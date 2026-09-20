# -*- coding: utf-8 -*-
"""塗装画面の単体テスト。根拠 = コグニ実機で塗装の全機能を入れて保存した NEO（2026-09-20、J87 N-BOX、レート 80,000、
２Ｋ・メタリック・高機能なし。操作ごとの差分は .claude/skills/pdf-to-neo/reference/experiments/2026-09-20_塗装画面.md）。
実機 NEO そのものは配らないので、期待値は**実機から写した数値**として直に書く（ADDATA さえあれば配布先でも動く）。

    cd files && PYTHONIOENCODING=utf-8 python claude_neo_pipeline/tests/unit_paint_screen.py
"""
from __future__ import annotations

import os
import sys

HERE = os.path.dirname(os.path.realpath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
import neo_diff  # noqa: E402
from estimate_to_neo import NeoBuilder  # noqa: E402

VEH = {'model_code': 'JF1', 'serial_no': 'JF1-0000001', 'desig': '17075', 'category': '0061', 'reg_date': 'H28.10', 'color_code': ''}
RATE = 80000
ITEMS = [
    {'code': '0600', 'name': '  ﾎﾞﾝﾈﾂﾄ', 'method': '取替', 'qty': 1, 'price': 40400, 'wage': 64000, 'index': 0.8},
    {'code': '2300', 'name': '左Frﾄﾞｱﾊﾟﾈﾙ', 'method': '板金', 'qty': 1, 'wage': 104000, 'index': 1.3, 'bankin': {'area': 10, 'yes': [1, 1, 1]}},
    {'code': '3100', 'name': '右Frﾄﾞｱﾊﾟﾈﾙ', 'method': '修理', 'qty': 1, 'wage': 96000, 'index': 1.2, 'bankin': {'area': 8, 'yes': [1, 1, 1]}},
]
PAINT = {
    'paint': '２Ｋ', 'coat': 'メタリック', 'hf': 'しない',
    'panels': [
        {'code': '0600', 'name': '  ﾎﾞﾝﾈﾂﾄ', 'method': '取替'},
        {'code': '2300', 'name': '左Frﾄﾞｱﾊﾟﾈﾙ', 'method': '修理', 'ratio': '1/3'},
        {'code': '3100', 'name': '右Frﾄﾞｱﾊﾟﾈﾙ', 'method': '修理', 'ratio': '1/2'},
        {'code': '0800', 'name': '左Fﾌｪﾝﾀﾞﾊﾟﾈﾙ', 'method': '修理', 'ratio': '1/1'},   # コグニの「パネル追加」（明細に無い）
        {'manual': True, 'name': 'RSIDE', 'index': 1.5},                              # 「行追加」（20.DB に無い部位）
    ],
    'booth': {'index': 0.5},
    'bumper_front': {'method': '新品', 'color': '一色'},
    'frame': {'engine_room': {'option': 2}, 'rear_floor': {'option': 1}},
    'door_sash': {'count': 2}, 'sealing': {'m': 3}, 'wax': {'count': 2},
    'other': [{'name': 'UNDERCOAT', 'index': 0.5}],
    'material_rate': 14,
}
# 実機 NEO の PaintingPanel（この順で並ぶ: 連動 3 行が部品コード昇順 → パネル追加 → 手入力の塗装行）
# PartsCode, DisposalCode, PaintingAreaName, Time, PanelArea, PrepareArea, AddedFrom, WageByManual, WageOutTax
PANELS = [
    ('0600', 0, '',    1.0, 45, -1, 0, '',  80000),
    ('2300', 6, '1/3', 1.7, 94, 11, 0, '',  136000),
    ('3100', 2, '1/2', 1.9, 94, 16, 0, '',  152000),
    ('0800', 2, '1/1', 1.6, 28, 10, 1, '*', 128000),
    ('',     9, '',    1.5, -1, -1, 1, '#', 120000),
]
PLAN = {'InputType': 1, 'Paint': 3, 'Coat': 2, 'HFPainting': 0, 'MaterialRateType': 1, 'MaterialRate': 14,
        'BoothFlag': 1, 'BoothTime': 0.5, 'BoothWageOutTax': 40000, 'BaseTime': 3.0, 'BaseWageOutTax': 240000,
        'BumperBaseTime': -1}   # 外板パネルがあるのでバンパ加算基礎は付かない
PTOTAL = {'WageTotalPanelOutTax': 616000, 'WageTotalBumperOutTax': 136000, 'WageTotalFrameOutTax': 184000,
          'WageTotalEtceteraOutTax': 88000, 'WageTotalOtherOutTax': 40000,
          'WageTotalOutTax': 1304000, 'MaterialTotalOutTax': 182560, 'TotalOutTax': 1526560}
ETC = {'DSBlackTime': 0.6, 'BSealingTime': 0.3, 'ARWaxTime': 0.2}              # fukaetc.DB / 0.1×数量
FRAME = {'er_Disposal': 2, 'er_Time': 1.4, 'rp_Disposal': 1, 'rp_Time': 0.9}   # NAIKOKUA.DB 車形 7 の 02・08
BUMPER = {'fb_Time': 1.7, 'fb_WageOutTax': 136000}                             # J8723.DB
TOTALS = {'parts': 40400, 'wage': 264000, 'paint': 1526560, 'paint_material': 182560,
          'paint_other': 40000, 'subtotal': 1830960, 'tax': 183096, 'total': 2014056}


def _row(em, table):
    cols = [c[1] for c in em.execute(f'pragma table_info({table})')]
    r = em.execute(f'SELECT * FROM {table}').fetchone()
    return dict(zip(cols, r)) if r else {}


def _cmp(label, got, exp, fails):
    ok = ((abs(float(got) - float(exp)) < 1e-6) if isinstance(exp, (int, float)) and isinstance(got, (int, float))
          else (str(got).strip() == str(exp).strip()))
    if not ok:
        print(f'FAIL {label}: got {got!r} expected {exp!r}')
    return fails + (0 if ok else 1)


def main() -> int:
    nb = NeoBuilder()
    est = {'source': 'unit_paint_screen', 'issuer': '', 'est_date': '20260920', 'vehicle': VEH, 'customer': {}, 'insurance': {},
           'labor_rate': RATE, 'items': ITEMS, 'paint': PAINT, 'expenses': [], 'totals': {}, 'hints': {}}
    neo, rep = nb.build(est, VEH, hints={}, labor_rate=RATE, est_date='20260920', insurance={})
    tmp = os.path.join(os.environ.get('TEMP', HERE), f'unit_paint_screen_{os.getpid()}.neo')  # 同時に走る別セッションとぶつからない名前
    open(tmp, 'wb').write(neo)
    d = neo_diff.load(tmp)
    em = next(v for k, v in d.items() if k.endswith('AnSvEm0001.sld'))
    fails = 0

    cols = [c[1] for c in em.execute('pragma table_info(PaintingPanel)')]
    rows = [dict(zip(cols, r)) for r in em.execute('SELECT * FROM PaintingPanel ORDER BY RecordNo')]
    if len(rows) != len(PANELS):
        print(f'FAIL 塗装パネルの行数: got {len(rows)} expected {len(PANELS)}')
        fails += 1
    for i, (code, disp, area_name, t, p_area, prep, added, mark, wage) in enumerate(PANELS):
        if i >= len(rows):
            break
        r = rows[i]
        for k, v in (('PartsCode', code), ('DisposalCode', disp), ('PaintingAreaName', area_name), ('Time', t),
                     ('PanelArea', p_area), ('PrepareArea', prep), ('AddedFrom', added),
                     ('WageByManual', mark), ('WageOutTax', wage)):
            fails = _cmp(f'パネル[{i}] {code or "(手入力)"} {k}', r.get(k), v, fails)

    for table, exp in (('PaintingPlan', PLAN), ('PaintingTotal', PTOTAL), ('PaintingEtcetera', ETC),
                       ('PaintingFrame', FRAME), ('PaintingBumper', BUMPER)):
        got = _row(em, table)
        for k, v in exp.items():
            fails = _cmp(f'{table} {k}', got.get(k), v, fails)

    ocols = [c[1] for c in em.execute('pragma table_info(PaintingOther)')]
    used = [o for o in (dict(zip(ocols, r)) for r in em.execute('SELECT * FROM PaintingOther'))
            if (o.get('WageOutTax') or -1) > 0]
    if len(used) != 1 or used[0].get('Time') != 0.5 or used[0].get('WageOutTax') != 40000 or used[0].get('WageByManual') != '#':
        print(f'FAIL 追加項目: {[(o.get("Name"), o.get("Time"), o.get("WageOutTax"), o.get("WageByManual")) for o in used]}')
        fails += 1
    for k, v in TOTALS.items():
        fails = _cmp(f'totals {k}', int(rep['totals'].get(k) or 0), v, fails)
    try:
        os.remove(tmp)
    except OSError:
        pass

    # 塗装工賃計の食い違い警告: 内板骨格塗装・ボデーシーリングを足したあとの値で比べること。
    # 足す前の値で比べると、合っている見積に「差がある」と出てしまう（実機 A10 で 208,000 の誤警告）
    def _paint_notes(total):
        b2 = NeoBuilder()
        p2 = dict(PAINT); p2['total'] = total
        e2 = dict(est); e2['paint'] = p2
        b2.build(e2, VEH, hints={}, labor_rate=RATE, est_date='20260920', insurance={})
        return [n for n in (getattr(b2, '_paint_notes', None) or []) if '塗装工賃計' in n]
    if _paint_notes(1304000):
        print(f'FAIL 合っている塗装工賃計に警告が出た: {_paint_notes(1304000)}')
        fails += 1
    if not _paint_notes(1300000):
        print('FAIL 塗装工賃計が違うのに警告が出ない')
        fails += 1
    print('unit_paint_screen:', 'all ok' if not fails else f'{fails} failed')
    return 1 if fails else 0


if __name__ == '__main__':
    sys.exit(main())
