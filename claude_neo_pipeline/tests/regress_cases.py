# -*- coding: utf-8 -*-
"""案件回帰（開発機専用）: `<NEO_CHECK_ROOT>/_cases.json` の regression に載る案件を run_case で再生成し、
「見積書合計との一致」の行が期待どおりで、run_case の終了コードも 0 であることを確かめる。
（以前は verify_all.sh に案件フォルダ名を直書きしていた。損保名・顧客名をリポジトリに残さないため 2026-09-12 に移した）

usage: python claude_neo_pipeline/tests/regress_cases.py        # 全案件。1 件でも不合格なら exit 1
"""
from __future__ import annotations

import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from case_dirs import case_dir, regression_cases  # noqa: E402

ROOT = os.path.dirname(os.path.dirname(HERE))


def main() -> int:
    cases = regression_cases()
    if not cases:
        print('案件回帰: _cases.json に regression が無いので飛ばす（開発機では NEO_check/_cases.json を用意する）')
        return 0
    fail = 0
    for c in cases:
        d = case_dir(c['code'])
        est = os.path.join(d, 'estimate.json')
        if not os.path.exists(est):
            print(f"*** {c['code']}: estimate.json が無い（{d}）"); fail += 1
            continue
        out = os.path.join(HERE, f"reg_{c['code']}.neo")
        r = subprocess.run([sys.executable, os.path.join(ROOT, 'claude_neo_pipeline', 'run_case.py'), est, out],
                           capture_output=True, text=True, encoding='utf-8', errors='replace', cwd=ROOT,
                           env=dict(os.environ, PYTHONIOENCODING='utf-8'))
        text = (r.stdout or '') + (r.stderr or '')
        line = next((l.strip() for l in reversed(text.splitlines()) if '見積書合計との一致' in l), '')
        print(f"{c['code']} {line}")
        if r.returncode != 0:
            print(f"*** FAILED: {c['code']} (run_case exit {r.returncode})")
            for l in text.splitlines():
                if '★' in l or '合格条件 NG' in l:
                    print('   ', l.strip()[:160])
            fail += 1
        elif line != c['expect']:
            print(f"*** FAILED: {c['code']} (expected: {c['expect']})"); fail += 1
    print(f'案件回帰 {len(cases)} / 不合格 {fail}')
    return 1 if fail else 0


if __name__ == '__main__':
    sys.exit(main())
