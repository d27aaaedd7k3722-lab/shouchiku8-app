# -*- coding: utf-8 -*-
"""ocr_eval.py — OCR ＋ ADDATA 照合（ocr_anchor.py）の評価。人が写した正解（NEO_check の案件の pages/page_N.json・reading.json）と行ごとに比べる。

合格条件は **見逃しゼロ**: comment に「OCR未確認」の付かない行（確定行）の 品番・部品価格・工賃・数量・修理方法・印 が正解と違う行（bad_sure）が 0。
ocr_anchor.py を直したら必ず回す（2026-09-28 の基準: 4 案件 291 行で 確定 262・bad_sure 0。ハイエース（東海日動）の 4800 の 1 件は正解側が協定で直した値）。

案件の一覧は リポジトリの外 `<NEO_CHECK_ROOT>/_ocr_eval/cases.json`（元案件フォルダの場所に顧客名が入るので git に入れない）:
    [{"name": "t_jimny", "truth": "Chubb_C25_ジムニー", "pdf": "Z:/…/最終工場見積書.pdf"}, …]
    正解側を印字と違う値に直した行（協定で工賃を直した 等）は "ignore_codes": ["4800"] で除く
試験の作業フォルダも `<NEO_CHECK_ROOT>/_ocr_eval/<name>/`（見積書の画像・header に個人情報があるので scratchpad に置かない）。

使い方（files ディレクトリで）:
    PYTHONIOENCODING=utf-8 python .claude/skills/pdf-to-neo/scripts/ocr_eval.py [--only t_jimny] [--verbose]
"""
from __future__ import annotations

import argparse
import io
import json
import os
import re
import shutil
import subprocess
import sys
import unicodedata

HERE = os.path.dirname(os.path.realpath(__file__))
sys.path.insert(0, HERE)
import skill_env  # noqa: E402
ENV = skill_env.apply()
K = ('code', 'name', 'method', 'parts_no', 'index', 'qty', 'price', 'wage', 'flags', 'comment')


def conv(x) -> dict:
    if isinstance(x, str):
        r = dict(zip(K, (x.split('|') + [''] * 10)[:10]))
    else:
        r = {k: x.get(k) for k in K}
        r['flags'] = x.get('flags') or x.get('mark') or ''
    return {k: ('' if v is None else str(v)) for k, v in r.items()}


def page_rows(case: str) -> list[dict]:
    pdir = os.path.join(case, 'pages')
    out = []
    if os.path.isdir(pdir):
        for f in sorted(os.listdir(pdir), key=lambda f: int(re.sub(r'\D', '', f) or 0)):
            if re.match(r'page_\d+\.json$', f):
                d = json.load(io.open(os.path.join(pdir, f), encoding='utf-8'))
                out += [conv(x) for b in d.get('blocks') or [] for x in b.get('rows') or []]
    return out


def truth_rows(case: str) -> list[dict]:
    rows = page_rows(case)
    if rows:
        return rows
    rd = json.load(io.open(os.path.join(case, 'reading.json'), encoding='utf-8'))
    return [conv(x) for b in rd.get('blocks') or [] for x in b.get('rows') or []]


def n(s) -> str:
    return re.sub(r'[\s,]', '', unicodedata.normalize('NFKC', str(s or '')))


def pn(s) -> str:
    return re.sub(r'[^0-9A-Z]', '', unicodedata.normalize('NFKC', str(s or '')).upper())


def compare(T: list[dict], R: list[dict], verbose: bool, ignore=()) -> dict:
    tot = {'rows': len(R), 'ocr_rows': len(T), 'sure': 0, 'check': 0, 'miss_rows': 0, 'bad_sure': 0, 'bad_extra': 0}
    used = set()
    for r in R:
        j = next((j for j, t in enumerate(T) if j not in used and t['code'] and t['code'] == r['code']), None)
        if j is None:
            j = next((j for j, t in enumerate(T) if j not in used and not t['code'] and not r['code'] and pn(t['parts_no']) == pn(r['parts_no'])
                      and (n(t['price']) or '0') == (n(r['price']) or '0')), None)
        if j is None:
            tot['miss_rows'] += 1
            print(f'   行が無い: {r["code"]} {r["method"]}')
            continue
        used.add(j)
        t = T[j]
        diffs = []
        if pn(t['parts_no']) != pn(r['parts_no']) and pn(r['parts_no']):
            diffs.append(f'品番 {t["parts_no"]} / 正 {r["parts_no"]}')
        for k in ('price', 'wage'):
            if (n(t[k]) or '0') != (n(r[k]) or '0'):
                diffs.append(f'{k} {t[k]} / 正 {r[k]}')
        if (n(t['qty']) or '1') != (n(r['qty']) or '1'):
            diffs.append(f'数量 {t["qty"]} / 正 {r["qty"]}')
        if n(t['method']) != n(r['method']):
            diffs.append(f'方法 {t["method"]} / 正 {r["method"]}')
        if ''.join(sorted(t['flags'])) != ''.join(sorted(r['flags'])):
            diffs.append(f'印 {t["flags"]!r} / 正 {r["flags"]!r}')
        sure = not t['comment'].startswith('OCR未確認')
        tot['sure' if sure else 'check'] += 1
        if diffs and sure and r['code'] in ignore:
            print(f'   （既知の例外 {r["code"]}: 正解側を印字と違う値に直した行）')
        elif diffs and sure:
            tot['bad_sure'] += 1
            print(f'   ★確定なのに違う {r["code"]}: ' + ' / '.join(diffs))
        elif diffs and verbose:
            print(f'   要確認 {r["code"]}: ' + ' / '.join(diffs))
    for j, t in enumerate(T):  # OCR が余分に作った行: 確定（OCR未確認 なし）なら見逃しと同じ（明細・合計を壊す。Codex 指摘）
        if j in used:
            continue
        if not t['comment'].startswith('OCR未確認'):
            tot['bad_extra'] += 1
            print('   ★余分な確定行:', t['code'], t['method'], t['price'], t['wage'])
        elif verbose:
            print('   余分な行（要確認つき）:', t['code'], t['price'], t['wage'])
    return tot


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('--only', default='')
    ap.add_argument('--verbose', action='store_true')
    a = ap.parse_args()
    root = ENV.get('NEO_CHECK_ROOT') or os.path.join(os.path.expanduser('~'), 'Documents', 'NEO_check')
    ev = os.path.join(root, '_ocr_eval')
    cfg = os.path.join(ev, 'cases.json')
    if not os.path.exists(cfg):
        print(f'評価の案件一覧が無い: {cfg}（[{{"name", "truth", "pdf"}}] の形で書く）'); return 2
    cases = json.load(io.open(cfg, encoding='utf-8'))
    allt = {'rows': 0, 'sure': 0, 'check': 0, 'miss_rows': 0, 'bad_sure': 0, 'bad_extra': 0}
    for c in cases:
        if a.only and a.only != c['name']:
            continue
        truth = os.path.join(root, c['truth'])
        work = os.path.join(ev, c['name'])
        shutil.rmtree(work, ignore_errors=True)
        os.makedirs(os.path.join(work, 'pages'))
        hp = os.path.join(truth, 'pages', 'header.json')
        h = json.load(io.open(hp if os.path.exists(hp) else os.path.join(truth, 'reading.json'), encoding='utf-8'))
        json.dump({k: h[k] for k in ('vehicle', 'hints', 'labor_rate', 'format') if k in h}, io.open(os.path.join(work, 'pages', 'header.json'), 'w', encoding='utf-8'), ensure_ascii=False)
        p = subprocess.run([sys.executable, os.path.join(HERE, 'ocr_anchor.py'), c['pdf'], work], capture_output=True, text=True, encoding='utf-8', errors='replace',
                           env=dict(os.environ, PYTHONIOENCODING='utf-8'))
        io.open(work + '.log', 'w', encoding='utf-8').write(p.stdout + p.stderr)
        print(f"== {c['name']}")
        t = compare(page_rows(work), truth_rows(truth), a.verbose, set(c.get('ignore_codes') or []))
        print('  ', t)
        for k in allt:
            allt[k] += t.get(k, 0)
    print(f"計: 正解 {allt['rows']} 行 / 確定 {allt['sure']} / 要確認 {allt['check']} / 行が無い {allt['miss_rows']} / 確定なのに違う {allt['bad_sure']} / 余分な確定行 {allt['bad_extra']}")
    return 1 if allt['bad_sure'] or allt['miss_rows'] or allt['bad_extra'] else 0


if __name__ == '__main__':
    sys.exit(main())
