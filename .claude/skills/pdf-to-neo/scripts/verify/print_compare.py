# -*- coding: utf-8 -*-
"""print_compare.py — コグニで刷った PDF（`<NEO_CHECK_ROOT>/_prints/<案件>.pdf`）を、見積書の写しと行ごとに突き合わせる（print_check.compare）。

- コグニ印刷（書式 A）: 写し（reading.json）と比べる（部品コード・名称・区分・品番・金額）
- コグニ以外の書式: 写しに部品コードが無いので、下書きの明細（estimate.json）と比べる。名称は比べない（部品コードのある行は ADDATA の名称で刷られるのが正しい）
- 合計: 写しの合計欄（印字）と印刷の合計

刷り方は reference/verification_workflow.md の「コグニで刷る」。PDF を刷った後に案件を作り直したら、刷り直してから比べる（古い NEO の印刷と新しい下書きを比べると差が大量に出る）。

    PYTHONIOENCODING=utf-8 python .claude/skills/pdf-to-neo/scripts/verify/print_compare.py [案件 …] [--base _nc] [--prints _prints]
"""
from __future__ import annotations

import argparse
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.realpath(__file__)))
from _common import case_names, load_json, save_json, work_dir  # noqa: E402
import print_check as pc  # noqa: E402


def compare_case(case_dir: str, pdf: str) -> tuple[list, dict]:
    rd = load_json(os.path.join(case_dir, 'reading.json')) or {}
    est = load_json(os.path.join(case_dir, 'estimate.json')) or {}
    _fmt_a = str(rd.get('format') or '').strip().upper()[:1] == 'A'
    if not rd or (not _fmt_a and not est.get('items')):
        return None, {'why': 'reading.json か estimate.json（明細）が無い。先に remake_cases.py で作る'}   # 空の写しと比べて「差なし」にしない（Codex 指摘）
    try:
        pr = pc.parse_print_pdf(pdf) or pc.parse_print(pc._text_pages(pdf))   # print_check の CLI と同じ（語の座標で読めなければ文字で）
    except (Exception, SystemExit):  # noqa: BLE001  壊れた・0 バイト・暗号化の PDF は「読めない」として数える（Codex 指摘）
        pr = None
    if pr is None or not (pr.get('rows') or pr.get('expenses') or pr.get('totals')):
        return None, {'why': '印刷 PDF を読めない（表の見出しも行も見つからない）'}   # 読めない PDF は「比べた」に数えない（呼び出し側が失敗にする。Codex 指摘）
    if (pr.get('totals') or {}).get('total') is None:
        return None, {'why': '印刷 PDF の合計（御見積額）を読めない。合計の突き合わせができないので比べた数に入れない'}   # Codex 指摘
    if _fmt_a:
        d = pc.compare(rd, pr, names=True)
    else:
        rde = pc.rows_from_estimate(est)
        rde['expenses'] = rd.get('expenses') or []
        rde['totals'] = rd.get('totals') or {}
        rde['tax_included'] = est.get('tax_included')
        d = pc.compare(rde, pr, names=False)
    info = {'rows_print': len(pr['rows']), 'rows_est': len(est.get('items') or []), 'expenses_print': len(pr['expenses']),
            'total_print': pr['totals'].get('total'), 'total_estimate': (rd.get('totals') or {}).get('total')}
    # 合計の違いは、下書きが理由付きで予告した額（3 点セットの neo_total。内税の費用の丸め 等）と印刷が同じなら説明済み
    # （make_neo --allow-neo-total と同じく 3 点そろったときだけ: neo_total・正の tolerance・理由。Codex 指摘）
    _t = est.get('totals') or {}
    _why = str(_t.get('tolerance_reason') or _t.get('neo_total_reason') or _t.get('note') or '').strip()
    try:
        _ok3 = _t.get('neo_total') is not None and int(_t.get('tolerance') or 0) > 0 and bool(_why) and info['total_print'] is not None \
            and int(_t['neo_total']) == int(info['total_print']) and info['total_estimate'] is not None \
            and abs(int(info['total_print']) - int(info['total_estimate'])) <= int(_t['tolerance'])   # 差が許容幅の中（run_case と同じ。Codex 指摘）
    except (TypeError, ValueError):
        _ok3 = False
    info['total_bad'] = any(x.startswith('合計') for x in d) and not _ok3
    return d, info


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('cases', nargs='*')
    ap.add_argument('--base', default='_nc')
    ap.add_argument('--prints', default='_prints')
    a = ap.parse_args()
    pdir = work_dir(a.prints)
    out = {}
    missing, unreadable, total_bad = [], [], []
    for c in a.cases or case_names(a.base):
        pdf = os.path.join(pdir, c + '.pdf')
        if not os.path.isfile(pdf):
            missing.append(c)   # 刷っていない・名前違い・cogni_open が消した後に刷れなかった: 「差 0」と見分けがつくように数える（Codex 指摘）
            continue
        d, info = compare_case(os.path.join(work_dir(a.base), c), pdf)
        if d is None:
            print(f"== {c}: 比べられない — {info.get('why', '')}")
            unreadable.append(c)
            continue
        print(f"== {c}: 印刷 {info.get('rows_print')} 行（コード付き）/ 下書き {info.get('rows_est')} 行 / 費用 {info.get('expenses_print')} / "
              f"合計 印刷 {info.get('total_print')} 写し {info.get('total_estimate')} / 差 {len(d)}")
        for x in d:
            print('   ', x)
        if info.get('total_bad'):
            total_bad.append(c)
        out[c] = d
    save_json(os.path.join(work_dir(a.base), 'print_compare.json'), out)
    print(f'計: 突き合わせた {len(out)} 件' + (f' / 印刷 PDF が無い {len(missing)} 件: {", ".join(missing)}' if missing else '')
          + (f' / 読めない {len(unreadable)} 件: {", ".join(unreadable)}' if unreadable else '')
          + (f' / **合計が違う {len(total_bad)} 件: {", ".join(total_bad)}**' if total_bad else ''))
    # 終了コード: 1 = 比べられなかった（名指しした案件の PDF が無い・読めない・1 件も比べていない）、2 = 合計が違う（下書きが予告した額でもない）。
    # 行の差（費用名の雛形・品番欄の '-' 等）は説明のつく差があるので終了コードにしない（手順書 §5 の表で 1 つずつ見る）
    if (a.cases and missing) or unreadable or not out:
        return 1
    return 2 if total_bad else 0


if __name__ == '__main__':
    sys.exit(main())
