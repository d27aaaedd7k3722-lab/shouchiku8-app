# -*- coding: utf-8 -*-
"""noncogni_candidates.py — survey.json の案件から「コグニ以外の書式」の工場見積を探し、検証する案件の一覧（_nc/cases.json）に足す。
書式の判定だけに 1〜2 ページ目の文字を見る（文字層、無ければ Windows OCR）。値は読まない・出さない。

コグニ印刷の見分け: 「部品価格適応日」「修理項目／部品名称」「ｺｰﾄﾞ 修理項目」の見出し。どれも無く、部品と工賃（技術料）の語がある PDF を候補にする。
速報/確報のある案件だけ（車両・保険の欄を header_auto で埋めるため）。新しい案件から順に見る。

    PYTHONIOENCODING=utf-8 python .claude/skills/pdf-to-neo/scripts/verify/noncogni_candidates.py --want 40            # 候補を 40 件探す（数十分）
    PYTHONIOENCODING=utf-8 python .claude/skills/pdf-to-neo/scripts/verify/noncogni_candidates.py --add 19 --max-pages 6  # 候補のうち未使用の 19 件を cases.json に足す
    PYTHONIOENCODING=utf-8 python .claude/skills/pdf-to-neo/scripts/verify/noncogni_candidates.py --want 30 --need-human-neo  # 人の NEO で答え合わせできる案件だけ

`--need-human-neo` は「部品コードの入った人の NEO（Claude 製でない）がある案件」だけを候補にする。
その案件は `verify/human_neo_accuracy.py` で**下書きと独立した**部品コードの答え合わせができる
（ふつうの `code_accuracy.py` の正解は担当が直した写しなので、担当が気づかなかった取り違えは正解に数えられる）。
"""
from __future__ import annotations

import argparse
import logging
import os
import re
import sys
import tempfile

sys.path.insert(0, os.path.dirname(os.path.realpath(__file__)))
from _common import NEO_CHECK, SCRIPTS, load_json, save_json  # noqa: E402

COGNI = re.compile(r'部品価格適応日|修理項目.{0,6}部品名称|ｺｰﾄﾞ.{0,4}修理項目|コード.{0,4}修理項目|コグニ|cognitive', re.I)
EST = re.compile(r'(部品|品番|品名|部品名).*(工賃|技術料|作業|金額)|(工賃|技術料).*(部品)', re.S)
CAND = os.path.join(NEO_CHECK, '_verify', 'noncogni_candidates.json')
CASES = os.path.join(NEO_CHECK, '_nc', 'cases.json')


def human_neo_rows(case: dict) -> int:
    """その案件にある**人の NEO**（Claude 製でない）のうち、部品コードの入った行がいちばん多い本数。
    ベタ打ちの NEO（部品コードが空）は 0。答え合わせに使えるかの目印"""
    sys.path.insert(0, SCRIPTS)
    import neo_compare  # noqa: PLC0415
    best = 0
    for n in (case.get('neo') or []):
        p = os.path.join(str(case.get('dir') or '').replace('/', os.sep), n)
        if not os.path.exists(p):
            continue
        try:
            rows = neo_compare.load(p)
        except Exception:  # noqa: BLE001
            continue
        best = max(best, sum(1 for r in rows if str(r.get('PartsCode') or '').strip() not in ('', '0', '-1')))
    return best


def first_text(pdf: str):
    """(文字層か OCR の文字, 'text' | 'image', ページ数)。開けない PDF は None"""
    import fitz  # noqa: PLC0415
    try:
        doc = fitz.open(pdf)
    except Exception:  # noqa: BLE001
        return None
    if len(doc) == 0:
        return None
    t = re.sub(r'\s+', '', ''.join(doc[i].get_text() for i in range(min(2, len(doc)))))
    if len(t) >= 80:
        return t, 'text', len(doc)
    sys.path.insert(0, SCRIPTS)
    import ocr_prefill  # noqa: PLC0415
    png = os.path.join(tempfile.mkdtemp(), 'p.png')
    try:
        doc[0].get_pixmap(matrix=fitz.Matrix(2.5, 2.5), colorspace=fitz.csGRAY).save(png)
        return re.sub(r'\s+', '', ''.join(w['text'] for w in ocr_prefill.run_ocr(png))), 'image', len(doc)
    except Exception:  # noqa: BLE001
        return None


def find(want: int, need_human: bool = False) -> list[dict]:
    logging.disable(logging.WARNING)
    sv = load_json(os.path.join(NEO_CHECK, '_verify', 'survey.json')) or load_json(os.path.join(NEO_CHECK, '_ocr_eval', '_survey.json')) or []
    if not sv:
        raise SystemExit('survey.json が無い。先に survey_cases.py を回す')
    out = load_json(CAND, []) or []
    seen = {x['pdf'] for x in out}
    cands = sorted((x for x in sv if x.get('est') and x.get('rep') and '99999' not in x['dir']), key=lambda x: x['dir'], reverse=True)
    for x in cands:
        if len(out) >= want:
            break
        # 同じ案件に複数あれば「最終」→ 新しい順
        ests = sorted(x['est'], key=lambda f: (('最終' in f), os.path.getmtime(os.path.join(x['dir'], f)) if os.path.exists(os.path.join(x['dir'], f)) else 0), reverse=True)
        pdf = os.path.join(x['dir'], ests[0]).replace('\\', '/')
        if pdf in seen:
            continue
        hn = human_neo_rows(x) if x.get('neo') else 0   # PDF を読むより先に見る（速い）
        if need_human and hn < 5:
            continue
        r = first_text(pdf)
        if r is None:
            continue
        t, kind, pages = r
        if COGNI.search(t) or ('修理項目' in t and '部品価格' in t) or not EST.search(t):
            continue
        out.append({'pdf': pdf, 'src': x['dir'], 'kind': kind, 'pages': pages,
                    'has_human_neo': bool(x.get('neo')), 'human_neo_rows': hn})
        seen.add(pdf)
        save_json(CAND, out)   # 途中で止まっても続きから
        print(len(out), kind, pages, f'人の NEO の部品コード {hn} 行' if hn else '-', flush=True)
    return out


def add_cases(n: int, max_pages: int, need_human: bool = False) -> None:
    cand = load_json(CAND, []) or []
    cases = load_json(CASES, []) or []
    used = {c['pdf'] for c in cases}
    nums = [int(m.group(1)) for c in cases for m in [re.match(r'nc(\d+)$', c.get('name', ''))] if m]
    k = max(nums) + 1 if nums else 1
    added = 0
    for x in cand:
        if added >= n:
            break
        if x['pdf'] in used or x.get('pages', 1) > max_pages:
            continue
        if need_human and int(x.get('human_neo_rows') or 0) < 5:
            continue
        cases.append({'name': f'nc{k:02d}', **x})
        print(f'nc{k:02d}', x['kind'], x.get('pages'))
        k += 1; added += 1
    save_json(CASES, cases)
    print(f'{added} 件を {CASES} に足した')


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('--want', type=int, default=0, help='候補をこの件数まで探す')
    ap.add_argument('--add', type=int, default=0, help='未使用の候補をこの件数だけ cases.json に足す')
    ap.add_argument('--max-pages', type=int, default=6, help='これより長い PDF は足さない（控えを重ねた束・見積以外の書類が多い）')
    ap.add_argument('--need-human-neo', action='store_true',
                    help='部品コードの入った人の NEO がある案件だけ（human_neo_accuracy.py で独立した答え合わせができる）')
    a = ap.parse_args()
    if a.want:
        print('候補', len(find(a.want, a.need_human_neo)), '件:', CAND)
    if a.add:
        add_cases(a.add, a.max_pages, a.need_human_neo)
    if not (a.want or a.add):
        ap.print_help()
    return 0


if __name__ == '__main__':
    sys.exit(main())
