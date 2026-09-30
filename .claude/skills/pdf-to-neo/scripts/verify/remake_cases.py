# -*- coding: utf-8 -*-
"""remake_cases.py — 検証用の案件を今のコードで作り直す（reading.json はそのまま。納品しない・工場プロファイルに書かない）。
合否・見積書合計との一致・印刷の予測との差の数を 1 行ずつ出す。スクリプトを直したら、コグニ以外（_nc）とコグニ印刷（_batch）の両方で回す。

    PYTHONIOENCODING=utf-8 python .claude/skills/pdf-to-neo/scripts/verify/remake_cases.py [案件 …] [--base _nc] [--no-allow-neo-total]

--allow-neo-total（既定で付ける）: 下書きが書いた 3 点セット（neo_total / tolerance / 理由。工場の丸めや内税の費用で数円違う案件）を人が認めた扱いで通す。
納品の本番では人が理由を見てから付けるもの（make_neo の既定は付けない）。
"""
from __future__ import annotations

import argparse
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.realpath(__file__)))
from _common import case_list, run_make_neo, work_dir  # noqa: E402


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('cases', nargs='*')
    ap.add_argument('--base', default='_nc')
    ap.add_argument('--no-allow-neo-total', action='store_true')
    ap.add_argument('--skip-check', action='store_true', help='紙上検算（reading_check）の FAIL を承知で進む（既定は止める）')
    a = ap.parse_args()
    n = ok = 0
    ready, pending = case_list(a.base)
    missing = [] if a.cases else list(pending)   # 写し待ちの案件も失敗として数える（cases.json の "skip" で除ける）
    for c in missing:
        print(c, 'reading.json が無い（写し待ち。見積でないなら cases.json に "skip": 理由 を書く）')
    for c in a.cases or ready:
        d = os.path.join(work_dir(a.base), c)
        if not os.path.isfile(os.path.join(d, 'reading.json')):
            print(c, 'reading.json が無い')
            missing.append(c)
            continue
        _, s = run_make_neo(d, allow_neo_total=not a.no_allow_neo_total, skip_check=a.skip_check)
        n += 1; ok += s['ok']
        print(c, '合格' if s['ok'] else '不合格', s['total'], '予測差', s['pred_diff'], s['ng'], flush=True)
    print(f'計: 合格 {ok}/{n}' + (f'（reading.json の無い案件 {len(missing)}）' if missing else ''))
    return 0 if (n and ok == n and not missing) else 1   # 1 件でも落ちたら・1 件も回らなかったら失敗で返す（Codex 指摘）


if __name__ == '__main__':
    sys.exit(main())
