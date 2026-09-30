# -*- coding: utf-8 -*-
"""code_accuracy.py — 部品コードの印字が無い書式（コグニ以外）で、下書きが部品コードをどれだけ当てるかを測る。

正解 = 担当が画像で確かめて直した reading.json（code を書いた行はその値、書かなかった行は下書きの結果を担当が認めたもの）。
試験 = 同じ reading から code を全部消したもの（見積書の印字そのもの）。両方を draft_estimate に通し、行を並びで揃えて部品コードを比べる。
コグニ印刷（書式 A）と汎用車種（部品コードが無い）の案件は数えない。

draft_estimate を直したら必ず回し、下がっていないことを確かめる（基準は reference/verification_workflow.md の「いまの数字」）。

    PYTHONIOENCODING=utf-8 python .claude/skills/pdf-to-neo/scripts/verify/code_accuracy.py [案件 …] [--base _nc] [-v] [--why]
      -v     外れた行を出す（正解 / 下書き / 名前 / 金額 / 下書きの理由）
      --why  外れを原因で分けて数える（名前の近似・未照合・同名の候補・部位ブロック・品番・別名辞書）と、単価で直せる行の数
"""
from __future__ import annotations

import argparse
import collections
import contextlib
import copy
import difflib
import io
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.realpath(__file__)))
from _common import case_names, load_json, work_dir  # noqa: E402
import draft_estimate as de  # noqa: E402


def strip_codes(rd: dict) -> dict:
    rd = copy.deepcopy(rd)
    for b in rd.get('blocks') or []:
        rows = []
        for r in b.get('rows') or []:
            if isinstance(r, str):
                p = r.split('|')
                p[0] = ''
                r = '|'.join(p)
            elif isinstance(r, dict):
                r = {k: v for k, v in r.items() if k != 'code'}
            rows.append(r)
        b['rows'] = rows
    return rd


def draft(rd: dict):
    with contextlib.redirect_stdout(io.StringIO()):
        d = de.Drafter(rd)
        return d, d.build()


def _key(it: dict):
    return (str(it.get('name') or '')[:10], it.get('price'), it.get('wage'))


def _cause(why: str, got, manual: bool) -> str:
    if manual or not got:
        return '未照合（手入力になった）'
    if '候補）' in why or why.startswith('名称一致'):
        return '同じ名前の候補が複数'
    if '別名辞書' in why:
        return '別名辞書の取り違え'
    if 'ブロック内' in why:
        return '部位ブロック内の照合で取り違え'
    if '品番一致' in why:
        return '品番一致だが別の部品コード'
    return '名前の近似で別部品'


def measure(case: str, base: str):
    rd = load_json(os.path.join(work_dir(base), case, 'reading.json'))
    if not rd or str(rd.get('format') or '').upper()[:1] == 'A' or (rd.get('vehicle') or {}).get('generic'):
        return None
    _, good = draft(rd)
    d, test = draft(strip_codes(rd))
    good, test = good['items'], test['items']
    sm = difflib.SequenceMatcher(a=[_key(x) for x in good], b=[_key(x) for x in test], autojunk=False)
    n = ok = 0
    bad = []
    for _tag, i1, i2, j1, j2 in sm.get_opcodes():
        for k in range(max(i2 - i1, j2 - j1)):
            g = good[i1 + k] if i1 + k < i2 else None
            t = test[j1 + k] if j1 + k < j2 else None
            if g is None or g.get('manual') or not g.get('code'):
                continue
            n += 1
            if t is not None and str(t.get('code')) == str(g.get('code')) and not t.get('manual'):
                ok += 1
                continue
            price = g.get('price') or 0
            qty = int(g.get('qty') or 1)
            unit = price // qty if price and qty and price % qty == 0 else 0

            def _std(c):
                try:
                    return d._std_unit(int(c)) if c else None
                except Exception:  # noqa: BLE001
                    return None
            bad.append({'right': g.get('code'), 'got': (t or {}).get('code'), 'manual': bool((t or {}).get('manual')),
                        'name': str(g.get('name'))[:20], 'price': g.get('price'), 'wage': g.get('wage'),
                        'why': str((t or {}).get('_ref_why') or ''),
                        'right_price_fits': bool(unit and _std(g.get('code')) == unit)})
    return n, ok, bad


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('cases', nargs='*')
    ap.add_argument('--base', default='_nc')
    ap.add_argument('-v', action='store_true')
    ap.add_argument('--why', action='store_true')
    a = ap.parse_args()
    tot_n = tot_ok = 0
    causes = collections.Counter()
    fits = 0
    errors = []
    for c in a.cases or case_names(a.base):
        try:
            r = measure(c, a.base)
        except Exception as e:  # noqa: BLE001
            print(c, 'ERROR', type(e).__name__, str(e)[:120])
            errors.append(c)
            continue
        if r is None:
            if a.cases:   # 名指しした案件が測れない（reading.json が無い・書式 A・汎用車種）: 打ち間違いを見逃さない（Codex 指摘）
                print(c, '測れない（reading.json が無い・コグニ印刷・汎用車種のどれか）')
                errors.append(c)
            continue
        n, ok, bad = r
        tot_n += n; tot_ok += ok
        print(f'{c}: 部品コード 正 {ok}/{n}' + (f'  外れ {len(bad)}' if bad else ''))
        for b in bad:
            causes[_cause(b['why'], b['got'], b['manual'])] += 1
            fits += b['right_price_fits']
            if a.v:
                print(f"    正 {b['right']} / 下書き {b['got'] or ''}{' M' if b['manual'] else ''}  {b['name']} {b['price']} {b['wage']} | {b['why'][:90]}")
    print(f'計: {tot_ok}/{tot_n}（{tot_ok * 100 / max(tot_n, 1):.1f}%）')
    if a.why and causes:
        for k, v in causes.most_common():
            print(f'  {v:3d} {k}')
        print(f'  うち正解の部品の標準単価が印字の単価と同じ（単価で直せるはずの）行: {fits}')
    if errors:
        print(f'測れなかった案件 {len(errors)}: {", ".join(errors)}')
    return 1 if (errors or tot_n == 0) else 0   # 落ちた案件がある・1 行も測れなかったら失敗（Codex 指摘）


if __name__ == '__main__':
    sys.exit(main())
