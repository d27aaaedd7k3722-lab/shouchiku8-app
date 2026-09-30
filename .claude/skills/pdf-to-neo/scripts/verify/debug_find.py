# -*- coding: utf-8 -*-
"""debug_find.py — 案件の車で、ある名前が ADDATA のどの部品に当たるかを出す（find_ref の結果・別名辞書・名前の近い候補 12 件と標準単価・部位ブロック）。
「なぜこの部品になったか / 正しい部品は候補に居るか」を調べる。単価を渡すと、その単価の部品も並べる。

    PYTHONIOENCODING=utf-8 python .claude/skills/pdf-to-neo/scripts/verify/debug_find.py <案件> <名前> [--side L|R] [--block A30] [--unit 1780] [--base _nc]
"""
from __future__ import annotations

import argparse
import contextlib
import io
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.realpath(__file__)))
from _common import load_json, work_dir  # noqa: E402
import draft_estimate as de  # noqa: E402


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('case')
    ap.add_argument('name')
    ap.add_argument('--side', default='')
    ap.add_argument('--block', default='')
    ap.add_argument('--unit', type=int, default=0)
    ap.add_argument('--base', default='_nc')
    a = ap.parse_args()
    rd = load_json(os.path.join(work_dir(a.base), a.case, 'reading.json'))
    if not rd:
        print('reading.json が無い'); return 1
    with contextlib.redirect_stdout(io.StringIO()):
        d = de.Drafter(rd)
        d.build()
    nm = de._clean_name(a.name)
    print('照合に使う名前:', nm, '| ホンダ式の読み替え:', de._honda_name(a.name))
    print('find_ref:', d.parts.find_ref('', '', nm, context_block=a.block, year=d.year))
    print('別名辞書:', d._alias_ref(a.name, a.side, a.block))

    def show(r, s=None):
        return (f"  {'' if s is None else f'{s:.2f} '}{r:04d} {sorted(x.strip() for x in d.parts.name20_by_ref.get(r, ()))} "
                f"標準 {d._std_unit(r)} 部位 {d.parts.block_of(r)}")
    print('名前の近い候補:')
    for s, r in sorted(((d._name_sim(nm, r, a.side), r) for r in d.parts.name20_by_ref), reverse=True)[:12]:
        print(show(r, s))
    if a.unit:
        print(f'標準単価 {a.unit:,} 円の部品:')
        for r in d._refs_by_price().get(a.unit, ()):
            if d._std_unit(r) == a.unit:
                print(show(r))
    return 0


if __name__ == '__main__':
    sys.exit(main())
