# -*- coding: utf-8 -*-
"""内板骨格の「基本内」と、build ごとの控えの初期化（2026-09-28）

  基本内 = 基本修正作業に含まれる部位。Frame の DamageRank 1 / Time・Wage* すべて -1 / 内骨計に入らない
           （実案件 NEO 2,500 本の Frame 行の実測。NEO_FILE_SPEC_COMPLETE.md §Frame）
  控え   = stats['renamed'] / ['name_diff'] は案件ごとに空から始まる（同じ NeoBuilder を使い回す corpus_scan・audit 用）

    cd files && PYTHONIOENCODING=utf-8 python claude_neo_pipeline/tests/unit_frame_basic.py
"""
from __future__ import annotations

import os
import sys

HERE = os.path.dirname(os.path.realpath(__file__))
sys.path.insert(0, os.path.dirname(HERE)); sys.path.insert(0, HERE)
from estimate_to_neo import NeoBuilder  # noqa: E402
import neo_diff  # noqa: E402

VEH = {'model_code': 'JF1', 'serial_no': 'JF1-0000001', 'desig': '17075', 'category': '0061', 'reg_date': 'H28.10', 'color_code': ''}
ok = True


def chk(cond, msg):
    global ok
    if not cond:
        ok = False
        print('  NG', msg)
    return cond


def build(nb, frame, items=None, name=''):
    est = {'source': 'unit_frame_basic', 'issuer': '', 'est_date': '20260928', 'vehicle': VEH, 'customer': {}, 'insurance': {},
           'labor_rate': 8000, 'items': items or [{'code': '0100', 'name': 'Fﾊﾞﾝﾊﾟ', 'method': '脱着', 'qty': 1}],
           'paint': {}, 'expenses': [], 'totals': {}, 'hints': {}, 'frame': frame}
    neo, rep = nb.build(est, VEH, hints={}, labor_rate=8000, est_date='20260928', insurance={})
    tmp = os.path.join(os.environ.get('TEMP', HERE), f'unit_frame_basic{name}.neo')
    open(tmp, 'wb').write(neo)
    em = neo_diff.load(tmp)['AnSvEm0001.sld']
    rows = [dict(r) for r in em.execute('select LineNo,PartsCode,DamageRank,Time,TimeStandard,WageOutTax from Frame')]
    tot = dict(zip([c[1] for c in em.execute('pragma table_info(Total)')], em.execute('select * from Total').fetchone()))
    return rows, tot, rep


nb = NeoBuilder()
FR = {'basic': True, 'basic_index': 3.5, 'basic_wage': 28000,
      'items': [{'code': '1372', 'name': 'ﾗｼﾞｴｰﾀｻﾎﾟｰﾄ', 'rank': 'A'},
                {'code': '1374', 'name': '左ﾌﾛﾝﾄﾌｪﾝﾀﾞｴﾌﾟﾛﾝ', 'rank': '基本内'}]}
rows, tot, rep = build(nb, FR, name='1')
print('-- 基本内の行 --')
bi = [r for r in rows if r['PartsCode'] == '1374']
chk(len(bi) == 1, f'基本内の行が 1 行で入っていない: {rows}')
if bi:
    r = bi[0]
    chk(r['DamageRank'] == 1, f"DamageRank が {r['DamageRank']}（1 のはず）")
    chk(r['Time'] == -1 and r['TimeStandard'] == -1 and r['WageOutTax'] == -1, f'指数・工賃が -1 でない: {r}')
a = [r for r in rows if r['PartsCode'] == '1372']
chk(a and a[0]['DamageRank'] == 2 and (a[0]['WageOutTax'] or 0) > 0, f'ランク A の行が壊れた: {a}')
chk(tot['nk_TotalOutTax'] == 28000 + (a[0]['WageOutTax'] if a else 0), f"内骨計に基本内の工賃が入っている: {tot['nk_TotalOutTax']}")

print('-- 基本内なのに工賃がある reading は止める --')
try:
    build(nb, {'basic': True, 'items': [{'code': '1374', 'name': 'x', 'rank': '基本内', 'wage': 12000}]}, name='2')
    chk(False, '工賃付きの「基本内」を黙って受けた')
except ValueError:
    pass

print('-- 控えは案件ごとに空から始まる --')
IT = [{'code': '0100', 'name': 'Fﾊﾞﾝﾊﾟ', 'method': '脱着', 'qty': 1, 'neo_name': 'Fﾊﾞﾝﾊﾟ 一部脱着'}]
n1 = len(build(nb, FR, items=IT, name='3')[2]['stats']['renamed'])
n2 = len(build(nb, FR, items=IT, name='4')[2]['stats']['renamed'])
chk(n1 == 1 and n2 == 1, f'名称の控えが積み上がっている: 1 回目 {n1} / 2 回目 {n2}')

print('unit_frame_basic:', 'all ok' if ok else 'NG')
sys.exit(0 if ok else 1)
