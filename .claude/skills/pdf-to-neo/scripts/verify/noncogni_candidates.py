# -*- coding: utf-8 -*-
"""noncogni_candidates.py — survey.json の案件から「コグニ以外の書式」の工場見積を探し、検証する案件の一覧（_nc/cases.json）に足す。
書式の判定だけに 1〜2 ページ目の文字を見る（文字層、無ければ Windows OCR）。値は読まない・出さない。

コグニ印刷の見分け: 「部品価格適応日」「修理項目／部品名称」「ｺｰﾄﾞ 修理項目」の見出し。どれも無く、部品と工賃（技術料）の語がある PDF を候補にする。
速報/確報のある案件だけ（車両・保険の欄を header_auto で埋めるため）。新しい案件から順に見る。

    PYTHONIOENCODING=utf-8 python .claude/skills/pdf-to-neo/scripts/verify/noncogni_candidates.py --want 40            # 候補を 40 件探す（数十分）
    PYTHONIOENCODING=utf-8 python .claude/skills/pdf-to-neo/scripts/verify/noncogni_candidates.py --add 19 --max-pages 6  # 候補のうち未使用の 19 件を cases.json に足す
    PYTHONIOENCODING=utf-8 python .claude/skills/pdf-to-neo/scripts/verify/noncogni_candidates.py --want 30 --need-human-neo  # 人の NEO で答え合わせできる案件だけ

`--need-human-neo` は「部品コードの入った人の NEO（Claude 製でない）がある案件」だけを候補にする
（既定は 5 行以上。`--need-human-neo 1` なら 1 行でも。行数は**写しを作る手間に見合うか**の線引きで、
答え合わせ自体は 1 行でもできる）。
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


def human_neo_rows_dir(case_dir: str) -> int:
    """案件フォルダを直接見て、人の NEO（Claude 製でない .neo）の部品コード行の最大本数を返す"""
    d = str(case_dir or '').replace('/', os.sep)
    if not os.path.isdir(d):
        return 0
    return human_neo_rows({'dir': d, 'neo': [f for f in os.listdir(d)
                                            if f.lower().endswith('.neo') and 'claude' not in f.lower()]})


def human_neo_rows(case: dict) -> int:
    """その案件にある**人の NEO**（Claude 製でない）のうち、部品コードの入った行がいちばん多い本数。
    ベタ打ちの NEO（部品コードが空）は 0。答え合わせに使えるかの目印。
    `--need-human-neo` はこれが指定の行数（既定 5）以上の案件を選ぶ。**写しを作る手間に見合うか**の
    線引きであって、4 行以下の NEO が答えにならないという意味ではない（human_neo_accuracy は 1 行でも数える）"""
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


def find(want: int, need_human: int = 0) -> list[dict]:
    logging.disable(logging.WARNING)
    sv = load_json(os.path.join(NEO_CHECK, '_verify', 'survey.json')) or load_json(os.path.join(NEO_CHECK, '_ocr_eval', '_survey.json')) or []
    if not sv:
        raise SystemExit('survey.json が無い。先に survey_cases.py を回す')
    out = load_json(CAND, []) or []
    seen = {x['pdf'] for x in out}

    def enough(x):   # 行数の線引きは**前に貯めた候補にも**効かせる（古い候補で数が埋まると、線引きが素通りする。Codex 指摘）
        return (not need_human) or int(x.get('human_neo_rows') or 0) >= need_human
    cands = sorted((x for x in sv if x.get('est') and x.get('rep') and '99999' not in x['dir']), key=lambda x: x['dir'], reverse=True)
    by_pdf = {y['pdf']: y for y in out}
    for x in cands:
        if sum(1 for y in out if enough(y)) >= want:
            break
        # 同じ案件に複数あれば「最終」→ 新しい順
        ests = sorted(x['est'], key=lambda f: (('最終' in f), os.path.getmtime(os.path.join(x['dir'], f)) if os.path.exists(os.path.join(x['dir'], f)) else 0), reverse=True)
        pdf = os.path.join(x['dir'], ests[0]).replace('\\', '/')
        if pdf in seen:
            # 前に貯めた候補は、人の NEO の行数を数え直して覚え直す（あとから人の NEO が置かれた案件・
            # 行数を覚えていなかった頃の候補が、線引きに掛からないまま埋もれる。Codex 指摘）
            y = by_pdf.get(pdf)
            if need_human and y is not None and not enough(y):
                y['human_neo_rows'] = human_neo_rows(x)
                save_json(CAND, out)
            continue
        hn = human_neo_rows(x) if x.get('neo') else 0   # PDF を読むより先に見る（速い）
        if need_human and hn < need_human:
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
        save_json(CAND, out)   # 途中で止まっても続きから（貯めるのは全部。返すのは線引きに合うものだけ）
        print(sum(1 for y in out if enough(y)), kind, pages, f'人の NEO の部品コード {hn} 行' if hn else '-', flush=True)
    return [x for x in out if enough(x)]


def add_cases(n: int, max_pages: int, need_human: int = 0) -> None:
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
        if need_human:
            # 候補に覚えた行数は当てにせず、**足すときに毎回数え直す**（人の NEO が消えた・差し替わった・
            # 行数を覚えていなかった頃の候補。多い側にも少ない側にもずれる。Codex 指摘）
            x['human_neo_rows'] = human_neo_rows_dir(x.get('src') or '')
            if int(x.get('human_neo_rows') or 0) < need_human:
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
    ap.add_argument('--need-human-neo', nargs='?', type=int, const=5, default=0, metavar='行数',
                    help='人の NEO に部品コードがこの行数以上ある案件だけ（数を書かなければ 5）。'
                         'human_neo_accuracy.py は 1 行でも数えるので、これは「写しを作る手間に見合うか」の線引き。'
                         '小さい修理も入れたいなら --need-human-neo 1')
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
