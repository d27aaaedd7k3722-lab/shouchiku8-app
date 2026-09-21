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

    # 内板骨格塗装の標準指数は 溶剤（NAIKOKUA.DB）と 水性（WNAIKOKUA.DB）で違う。
    # 車形 7: ラジエータサポート 両側新品 1.40 / 1.70、リヤフロア 1台小修正 0.90 / 1.10
    b3 = NeoBuilder()
    p3 = dict(PAINT)
    p3['paint'] = '水性'      # 塗料だけ水性に替える（パネル・バンパの水性指数は別の話。ここでは内板骨格だけ見る）
    p3.pop('total', None)
    e3 = dict(est)
    e3['paint'] = p3
    n3_, r3 = b3.build(e3, VEH, hints={}, labor_rate=RATE, est_date='20260920', insurance={})
    t3 = os.path.join(os.environ.get('TEMP', HERE), f'unit_paint_screen_w_{os.getpid()}.neo')
    open(t3, 'wb').write(n3_)
    fr3 = _row(next(v for k, v in neo_diff.load(t3).items() if k.endswith('AnSvEm0001.sld')), 'PaintingFrame')
    for k, v in (('er_Time', 1.7), ('rp_Time', 1.1)):
        fails = _cmp(f'水性の内板骨格 {k}', fr3.get(k), v, fails)
    try:
        os.remove(t3)
    except OSError:
        pass
    # 高機能塗装だけのパネル行（DisposalCode 7）: 明細は脱着でも、その部位に高機能塗装の加算だけ足せる。
    # 実案件 NEO 80 行 / 60 本の形（AddedFrom 1・SortNo 13・印 '*'・塗装面積なし・パネル計に入る・加算基礎の枚数には数えない）
    b4 = NeoBuilder()
    e4 = dict(est)
    e4['items'] = ITEMS + [{'code': '4300', 'name': 'ﾊﾞﾂｸﾄﾞｱﾊﾟﾈﾙ', 'method': '脱着', 'qty': 1}]
    p4 = dict(PAINT)
    p4['hf'] = '耐スリ傷'
    p4['panels'] = PAINT['panels'] + [{'code': '4300', 'name': 'ﾊﾞﾂｸﾄﾞｱﾊﾟﾈﾙ', 'method': '高機能'}]   # 通常パネルに無い部位（重なると二重計上になるので生成器が止める）
    p4.pop('total', None)
    e4['paint'] = p4
    n4, _r4 = b4.build(e4, VEH, hints={}, labor_rate=RATE, est_date='20260920', insurance={})
    t4 = os.path.join(os.environ.get('TEMP', HERE), f'unit_paint_screen_hf_{os.getpid()}.neo')
    open(t4, 'wb').write(n4)
    em4 = next(v for k, v in neo_diff.load(t4).items() if k.endswith('AnSvEm0001.sld'))
    c4 = [c[1] for c in em4.execute('pragma table_info(PaintingPanel)')]
    r7 = [dict(zip(c4, x)) for x in em4.execute('SELECT * FROM PaintingPanel') if dict(zip(c4, x))['DisposalCode'] == 7]
    if len(r7) != 1:
        print(f'FAIL 高機能塗装だけの行が {len(r7)} 行')
        fails += 1
    else:
        for k, v in (('PartsCode', '4300'), ('DisposalName', '耐スリ傷'), ('PaintingArea', -1), ('PrepareArea', -1),
                     ('AddedFrom', 1), ('SortNo', 13), ('WageByManual', '*'), ('Manual', 0)):
            fails = _cmp(f'高機能だけの行 {k}', r7[0].get(k), v, fails)
        if not (r7[0].get('Time') and abs(r7[0]['Time'] - (r7[0].get('TimeStandardHF') or 0)) < 1e-9):
            print(f"FAIL 高機能だけの行の指数が加算と違う: {r7[0].get('Time')} / {r7[0].get('TimeStandardHF')}")
            fails += 1
        if (r7[0].get('WageOutTax') or 0) != int(round((r7[0].get('Time') or 0) * RATE / 10) * 10):
            print(f"FAIL 高機能だけの行の工賃: {r7[0].get('WageOutTax')}")
            fails += 1
    try:
        os.remove(t4)
    except OSError:
        pass

    # 塗装条件の注記欄（印刷に出る自由入力。実案件 600 本中 12 本が 'ｱﾝﾀﾞｰｺｰﾄ含み'）
    b5 = NeoBuilder()
    p5 = dict(PAINT)
    p5['type_note'] = 'アンダーコート含み'
    p5['paint_note'] = '水性'
    p5.pop('total', None)
    e5 = dict(est)
    e5['paint'] = p5
    n5, _r5 = b5.build(e5, VEH, hints={}, labor_rate=RATE, est_date='20260921', insurance={})
    t5 = os.path.join(os.environ.get('TEMP', HERE), f'unit_paint_screen_note_{os.getpid()}.neo')
    open(t5, 'wb').write(n5)
    em5 = next(v for k, v in neo_diff.load(t5).items() if k.endswith('AnSvEm0001.sld'))
    pl5 = _row(em5, 'PaintingPlan')
    for k, v in (('PaintingTypeName', 'ｱﾝﾀﾞｰｺｰﾄ含み'), ('PaintingTypeNameAdded', 'ｱﾝﾀﾞｰｺｰﾄ含み'), ('PaintNameAdded', '水性'),
                 ('PaintName', '２Ｋ'), ('CoatName', 'メタリック')):
        fails = _cmp(f'塗装条件の注記 {k}', pl5.get(k), v, fails)
    try:
        os.remove(t5)
    except OSError:
        pass

    # パネル別塗り数値の表（77/87/97/99.DB）: 装備（EVA）別の行を選べること。
    # J57 のテールゲート 4300 は 無条件 2.5 / EVA 'Z'（4WD）2.3（ADDATA 2026/08。実案件 NEO とも一致）
    import paint_index as _pi
    _root = NeoBuilder().engine.root
    try:
        _p0 = _pi.PaintIndex(_root, 'J57')
        _p1 = _pi.PaintIndex(_root, 'J57')
        _p1.eva = {'Z'}
        _r0, _r1 = _p0.panel87('4300', 3, 0), _p1.panel87('4300', 3, 0)
    except Exception:
        _r0 = _r1 = None
    if _r0 is None or _r1 is None:
        print('     （この PC の ADDATA に J57 の 77.DB が無いので飛ばす）')
    else:
        fails = _cmp('77.DB 無条件の行', _r0.get('new_multi'), 2.5, fails)
        fails = _cmp('77.DB 4WD(Z) の行', _r1.get('new_multi'), 2.3, fails)
        fails = _cmp('77.DB の出どころ', _r0.get('src'), '77.DB', fails)
    # 装備が複数条件の行（M89 4500 ボディ 20: 無条件 5.3 / R 3.5 / W 5.7 / WR 4.0）は**具体的な行**を採る
    try:
        _m = {}
        for _e in (frozenset(), frozenset('R'), frozenset('W'), frozenset('WR')):
            _p = _pi.PaintIndex(_root, 'M89', body='20')
            _p.eva = set(_e)
            _m[_e] = (_p.panel87('4500', 3, 0) or {}).get('new_multi')
    except Exception:
        _m = {}
    if not _m or _m.get(frozenset()) is None:
        print('     （この PC の ADDATA に M89 の 77.DB が無いので飛ばす）')
    else:
        for _e, _v in ((frozenset(), 5.3), (frozenset('R'), 3.5), (frozenset('W'), 5.7), (frozenset('WR'), 4.0)):
            fails = _cmp(f'77.DB 装備 {sorted(_e) or "なし"}', _m.get(_e), _v, fails)

    # 2コートソリッド: 基本 0.10 ＋ 0.10 × ルーフ以外 ＋ 0.30 × ルーフ
    # （実機 2K: ルーフのみ 0.4 / +1 枚 0.5 / +5 枚 0.9 / +7 枚 1.1、水性: 1 枚 0.2 / 2 枚 0.3 / ルーフ+2 枚 0.6。
    #  実案件 153 本すべて一致。2026-09-21 に溶剤でルーフが無いときの 0.10 が抜けていたのを直した）
    import estimate_to_neo as _E
    for _args, _want in (((1, 0, 3), 0.4), ((1, 1, 3), 0.5), ((1, 5, 3), 0.9), ((1, 7, 3), 1.1),
                         ((0, 1, 3), 0.2), ((0, 4, 3), 0.5), ((0, 8, 3), 0.9),
                         ((0, 1, 4), 0.2), ((0, 2, 4), 0.3), ((1, 2, 4), 0.6)):
        fails = _cmp(f'2コートソリッド {_args}', _E.two_coat_solid_time(*_args), _want, fails)

    # バンパ 23.DB は 年式群・ボディ・グレード・装備でも行が分かれる（2026-09-21。実案件 127/127 一致）。
    # D62: 無条件 / グレード A / B / H。F メタリック取替一色 = 無条件 2.5、グレード A 2.2
    from paint_index import PaintIndex as _PI
    _root = os.environ.get('ADDATA_ROOT') or r'C:\Addata'
    _d = _PI(_root, 'D62')
    fails = _cmp('23.DB グレード無し', _d.bumper_time(True, 2, '取替'), 2.5, fails)
    _d.grade = 'A'
    fails = _cmp('23.DB グレード A', _d.bumper_time(True, 2, '取替'), 2.2, fails)
    _d.grade = 'B'
    fails = _cmp('23.DB グレード B', _d.bumper_time(True, 2, '取替'), 2.2, fails)
    _d.grade = 'X'  # どの条件行にも当たらないグレード → 無条件行
    fails = _cmp('23.DB 該当しないグレード', _d.bumper_time(True, 2, '取替'), 2.5, fails)

    # 66/96.DB の色別の塗装条件（2026-09-21 に解読）。塗膜の候補・高機能塗装・注記が読めること
    from addata_vehicle_resolver import AddataVehicleResolver as _R
    _r = _R(os.environ.get('ADDATA_ROOT') or r'C:\Addata')
    _i = _r.color_paint_info('W66', '2SK')
    fails = _cmp('66.DB 塗膜の候補（2 通りある色）', _i['coats'], [2, 3], fails)
    fails = _cmp('66.DB 行数', _i['rows'], 2, fails)
    fails = _cmp('66.DB 高機能（なし）', _i['hf'], ['B'], fails)
    fails = _cmp('66.DB 注記あり', bool(_i['notes']), True, fails)
    _i2 = _r.color_paint_info('W66', '070')
    fails = _cmp('66.DB 塗膜 1 通りの色', _i2['coats'], [4], fails)
    _i3 = _r.color_paint_info('W82', '4X1')
    fails = _cmp('66.DB 高機能（耐スリ傷の色）', _i3['hf'], ['T'], fails)
    fails = _cmp('66.DB 無い色は行 0', _r.color_paint_info('W66', 'ZZZZ')['rows'], 0, fails)

    # 25.DB は 13 バイトのレコードで、ボディで車形が変わる（2026-09-21）
    _w66 = _PI(_root, 'W66')
    fails = _cmp('25.DB 車形（ボディなし）', ''.join(_w66.form_codes()), ''.join(_PI(_root, 'W66').form_codes()), fails)
    for _car, _b1, _b2 in (('C34', '00', '10'), ('D88', '00', '20')):
        _p1 = _PI(_root, _car, body=_b1)._chm_path() or ''
        _p2 = _PI(_root, _car, body=_b2)._chm_path() or ''
        fails = _cmp(f'{_car} はボディで CHM が変わる', _p1 != _p2 and bool(_p1) and bool(_p2), True, fails)

    # 暫定指数の車種（S_Est の 1 桁目が 2）は塗装パネルの印が `$`
    fails = _cmp('S_Est 1 桁目（W66）', _PI(_root, 'W66').car_paint_kind(), 1, fails)
    fails = _cmp('S_Est 1 桁目（C10）', _PI(_root, 'C10').car_paint_kind(), 5, fails)
    fails = _cmp('汎用車種は塗装指数なし', _PI(_root, 'Z10').car_paint_kind(), 0, fails)
    fails = _cmp('暫定でない車は False', _PI(_root, 'W66').car_paint_provisional(), False, fails)

    print('unit_paint_screen:', 'all ok' if not fails else f'{fails} failed')
    return 1 if fails else 0


if __name__ == '__main__':
    sys.exit(main())
