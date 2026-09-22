# -*- coding: utf-8 -*-
"""13/83.DB（色別・期間別部品）の行選び colored_part の不変条件（2026-09-22 差分 B の代替レビューで見つかった 3 つの穴を塞ぐ）。
ADDATA だけを読む（顧客データは使わない）。車種が無い PC では飛ばす。

  1. 車両カラーと違う色の行を返さない（カラー未設定・存在しないカラーの車に W19 などの色付き品番を当てない）
  2. 11.DB の品番（std_pn）と語幹が違う行を返さない（別の部品番号に置き換えない）
  3. 同じ色のグループが複数あり、初度登録の年月がちょうど 1 つの行の期間に入るなら、その行を返す
"""
import collections
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path[:] = [p for p in sys.path if 'scratchpad' not in p.replace(chr(92), '/')]
sys.path.insert(0, os.path.dirname(HERE))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.dirname(HERE)), '.claude', 'skills', 'pdf-to-neo', 'scripts'))
try:
    import skill_env
    skill_env.apply()
except Exception:  # noqa: BLE001  設定が無い PC は既定の ADDATA を使う
    pass
import estimate_to_neo as E  # noqa: E402

CARS = ['D82', 'D98', 'W66', 'W64', 'U52', 'J95']


def main() -> int:
    nb = E.NeoBuilder()
    bad = []
    n1 = n2 = n3 = 0
    for cc in CARS:
        if not os.path.exists(os.path.join(nb.engine.root, cc[0], cc, f'{cc}13.DB')) and not os.path.exists(os.path.join(nb.engine.root, cc[0], cc, f'{cc}83.DB')):
            continue
        p = E.AddataParts(nb.engine, cc)
        raw = p._load_83_raw()
        for ref, rows in raw.items():
            std = p._cogni_row(ref, 0, '', '', set(), '', '')
            std_pn = (std or {}).get('pn', '') or ''
            for col in ('', 'ZZZ') + tuple(sorted({r['color'] for r in rows if r['color']})[:2]):
                got = p.colored_part(ref, col, '', '', set(), std_pn, '', '', year='')
                if got is None:
                    continue
                n1 += 1
                if got['color'] and got['color'] != col:
                    bad.append(f'1: {cc} {ref} カラー {col!r} に色 {got["color"]} の行 {got["pn"]}')
                if std_pn:
                    n2 += 1
                    if not p._same_stem(got['pn'], std_pn):
                        bad.append(f'2: {cc} {ref} 11.DB {std_pn} と語幹の違う {got["pn"]}')
            bycol = collections.defaultdict(list)
            for r in rows:
                if r['color'] and not r['flags'].strip() and not r['grp'] and not r['body']:
                    bycol[r['color']].append(r)
            for col, rs in bycol.items():
                if len({r['group'] for r in rs}) < 2:
                    continue
                for r in rs:
                    ym = r.get('from') or ''
                    if len(ym) != 6 or not ym.isdigit() or r.get('period_invalid'):
                        continue
                    inside = [x for x in rs if not x.get('period_invalid') and (x.get('from') or x.get('to'))
                              and (not x.get('from') or x['from'] <= ym) and (not x.get('to') or ym <= x['to'])]
                    if len({x['group'] for x in inside}) != 1 or len({x['pn'] for x in inside}) != 1:
                        continue
                    got = p.colored_part(ref, col, '', '', set(), rs[0]['pn'], ym, '', year='')
                    n3 += 1
                    if not got or got['pn'] != inside[0]['pn']:
                        bad.append(f'3: {cc} {ref} {col} {ym} 期間の行 {inside[0]["pn"]} でなく {got and got["pn"]}')
    for b in bad[:20]:
        print('NG', b)
    print(f'color pick: 色 {n1} / 語幹 {n2} / 期間 {n3} 件を検査、NG {len(bad)}')
    if n1 == 0:
        print('（対象の車種が ADDATA に無いので飛ばした）')
    return 1 if bad else 0


if __name__ == '__main__':
    sys.exit(main())
