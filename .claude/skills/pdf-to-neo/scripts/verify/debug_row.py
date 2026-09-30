# -*- coding: utf-8 -*-
"""debug_row.py — 1 案件の reading.json を下書きに通し、名前に指定の文字を含む行の「写し」「下書きの結果」「下書きの注記」を並べて出す。
部品コードの外れを調べるときの最初の 1 手（code_accuracy.py -v で見つけた行をここで追う）。

    PYTHONIOENCODING=utf-8 python .claude/skills/pdf-to-neo/scripts/verify/debug_row.py <案件> <文字> [<文字> …] [--base _nc] [--strip]
      --strip  写しの部品コードを消してから下書きする（code_accuracy と同じ条件で再現する）
"""
from __future__ import annotations

import argparse
import contextlib
import io
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.realpath(__file__)))
from _common import load_json, work_dir  # noqa: E402
import draft_estimate as de  # noqa: E402
from code_accuracy import strip_codes  # noqa: E402


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('case')
    ap.add_argument('words', nargs='+')
    ap.add_argument('--base', default='_nc')
    ap.add_argument('--strip', action='store_true')
    a = ap.parse_args()
    rd = load_json(os.path.join(work_dir(a.base), a.case, 'reading.json'))
    if not rd:
        print('reading.json が無い'); return 1
    if a.strip:
        rd = strip_codes(rd)
    for b in rd.get('blocks') or []:
        for r in b.get('rows') or []:
            s = r if isinstance(r, str) else json.dumps(r, ensure_ascii=False)
            if any(w in s for w in a.words):
                print('写し  ', b.get('title') or '', '|', s[:200])
    with contextlib.redirect_stdout(io.StringIO()):
        d = de.Drafter(rd)
        e = d.build()
    for it in e['items']:
        if any(w in str(it.get('name')) or w in str(it.get('_name_raw', '')) for w in a.words):
            print('下書き', {k: it.get(k) for k in ('code', 'name', 'method', 'parts_no', 'qty', 'price', 'wage', 'manual')},
                  '|', str(it.get('_ref_why') or '')[:120])
    for n in d.notes:
        if any(w in n for w in a.words):
            print('注記  ', n[:300])
    return 0


if __name__ == '__main__':
    sys.exit(main())
