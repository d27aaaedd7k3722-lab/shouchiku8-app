# -*- coding: utf-8 -*-
"""survey_cases.py — 元案件の置き場（既定 Z:/、環境変数 CASE_ROOT）の案件フォルダを走査し、工場見積 PDF・人の NEO・速報/確報の有無を一覧にする。
ファイル名と種類だけを見る（中身は読まない）。結果は `<NEO_CHECK_ROOT>/_verify/survey.json`（顧客名入りのパスなので git に入れない）。

置き場の形: <CASE_ROOT>/<YYYY年>/<MM月>/<DD日>/<損保>_<顧客>_<番号>_<車名>_<地域>/

    PYTHONIOENCODING=utf-8 python .claude/skills/pdf-to-neo/scripts/verify/survey_cases.py [--years 2025年 2026年]
"""
from __future__ import annotations

import argparse
import collections
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.realpath(__file__)))
from _common import CASE_ROOT, NEO_CHECK, save_json  # noqa: E402

# 工場見積らしいファイル名（'工場最終.pdf' '見積書.pdf'、FAX 受信名 '0938633113_20260916_172058.pdf'）
EST_RE = re.compile(r'見積|工場|最終|ソウシンモト|^\d{2,4}-\d{2,4}-\d{3,4}_|^\d{10,}_\d{8}', re.I)
NOT_EST_RE = re.compile(r'速報|確報|請求|車検証|claude|受注|依頼', re.I)
REP_RE = re.compile(r'速報|確報')


def survey(root: str, years: list[str]) -> list[dict]:
    cases = []
    for year in years:
        yd = os.path.join(root, year)
        if not os.path.isdir(yd):
            continue
        for mon in sorted(os.listdir(yd)):
            md = os.path.join(yd, mon)
            if not os.path.isdir(md):
                continue
            for day in sorted(os.listdir(md)):
                dd = os.path.join(md, day)
                if not os.path.isdir(dd):
                    continue
                for case in os.listdir(dd):
                    cd = os.path.join(dd, case)
                    if not os.path.isdir(cd):
                        continue
                    try:
                        fs = os.listdir(cd)
                    except OSError:
                        continue
                    pdfs = [f for f in fs if f.lower().endswith('.pdf')]
                    neos = [f for f in fs if f.lower().endswith('.neo')]
                    cases.append({'dir': cd.replace('\\', '/'),
                                  'est': [f for f in pdfs if EST_RE.search(f) and not NOT_EST_RE.search(f)],
                                  'rep': [f for f in pdfs if REP_RE.search(f)],
                                  'neo': [n for n in neos if 'claude' not in n.lower()],   # 人がコグニで作った NEO（答え合わせに使える）
                                  'claude_neo': [n for n in neos if 'claude' in n.lower()],
                                  'insurer': case.split('_')[0]})
    return cases


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('--root', default=CASE_ROOT)
    ap.add_argument('--years', nargs='*', default=['2025年', '2026年'])
    a = ap.parse_args()
    cases = survey(a.root, a.years)
    out = os.path.join(NEO_CHECK, '_verify', 'survey.json')
    save_json(out, cases)
    c = collections.Counter()
    for x in cases:
        c['案件'] += 1
        c['工場見積あり'] += bool(x['est'])
        c['人の NEO あり'] += bool(x['neo'])
        c['速報/確報あり'] += bool(x['rep'])
        c['見積＋人の NEO（答え合わせできる）'] += bool(x['est'] and x['neo'])
    print(dict(c))
    print('保存:', out)
    return 0


if __name__ == '__main__':
    sys.exit(main())
