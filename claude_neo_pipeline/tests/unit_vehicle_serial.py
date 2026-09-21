# -*- coding: utf-8 -*-
"""車両特定: 車台番号で（車種・年式）が決まったら初度登録は見ない（コグニ本体 AxCarSrcUIProof.bpl
SearchCarFromCarSerialNo 0x410D74 と同じ。2026-09-21）

在庫期間のある車（生産終了後に登録）は、初度登録が KA81 の生産期間の外になる。点数で比べていたころは
「車台番号の年式（+5, 期間外 −2 = 3）」が「隣の年式（車種だけ一致 +2, 期間内 +4 = 6）」に負け、しかも確度 confirmed で外していた
（実案件 1,169 本で 14 本）。KA81・KA06 の検索結果は作り物で与え、採点と絞り込みの規則だけを確かめる

    cd files && PYTHONIOENCODING=utf-8 python claude_neo_pipeline/tests/unit_vehicle_serial.py
"""
from __future__ import annotations

import os
import sys

HERE = os.path.dirname(os.path.realpath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
from addata_vehicle_resolver import AddataVehicleResolver  # noqa: E402

ok = True


def chk(cond, msg):
    global ok
    if not cond:
        ok = False
        print('  NG', msg)


CAR = 'J87'   # 自己テストと同じ N BOX（年式名などの付随情報を ADDATA から引けるように実在の車種を使う）
ym = lambda y, m: (y - 1900) * 12 + m  # noqa: E731  KA81 の生産期間の値


def ka81(year, grade, start, end):
    return {'car_code': CAR, 'year_code': year, 'body_code': '10', 'grade_code': grade, 'fva_code': 'T',
            'four_wd': False, 'categories': [61], 'period': (start, end)}


def run(by_desig, by_serial, reg):
    r = AddataVehicleResolver()
    r.lookup_by_designation = lambda d, c: list(by_desig)       # noqa: E731
    r.lookup_by_model_serial = lambda m, s: list(by_serial)     # noqa: E731
    return r.resolve(model_code='JF1', serial_no='JF1-0000001', desig='17075', category='0061', reg_date=reg)


def got(res):
    c = res['neo_car']
    return c.get('YearCode'), c.get('GradeCode'), res['confidence']


print('-- 車台番号の年式が、初度登録の生産期間の外でも勝つ --')
old = ka81('01', 'A', ym(2016, 1), ym(2017, 8))   # 車台番号が指す年式（生産は 2017/8 まで）
new = ka81('02', 'A', ym(2017, 9), 0)              # 隣の年式（初度登録 2018/2 はこちらの期間内）
res = run([old, new], [{'car_code': CAR, 'year_code': '01', 'model': 'JF1', 'range': (1, 9)}], '2018/2')
chk(got(res)[:2] == ('01', 'A'), f'車台番号の年式 01 のはずが {got(res)}')
chk(got(res)[2] == 'confirmed', f'1 台に決まったので confirmed のはずが {got(res)[2]}')

print('-- 車台番号で決まった年式の中に複数残ったら、ヒントで選んでも confirmed にしない --')
res = run([ka81('01', 'A', ym(2016, 1), ym(2017, 8)), ka81('01', 'B', ym(2016, 1), ym(2017, 8)), new],
          [{'car_code': CAR, 'year_code': '01', 'model': 'JF1', 'range': (1, 9)}], '2018/2')
chk(got(res)[0] == '01', f'年式は 01 のはずが {got(res)}')
chk(got(res)[2] != 'confirmed', f'グレード A/B が残っているのに confirmed になった {got(res)}')

print('-- 車台番号で決まらないときは、初度登録で生産期間を絞る --')
res = run([old, new], [], '2018/2')
chk(got(res)[0] == '02', f'初度登録 2018/2 の期間内の 02 のはずが {got(res)}')
res = run([old, new], [], '2016/5')
chk(got(res)[0] == '01', f'初度登録 2016/5 の期間内の 01 のはずが {got(res)}')

print('-- どの期間にも入らなければ絞らない（候補を全部落とさない）--')
res = run([ka81('01', 'A', ym(2016, 1), ym(2016, 6)), ka81('02', 'A', ym(2016, 7), ym(2016, 12))], [], '2020/1')
chk(res['neo_car'].get('CarCode') == CAR, f'候補が消えた {res.get("confidence")}')

print('-- 車台番号の車種・年式が KA81 に無ければ、今までどおり KA81 から選ぶ --')
res = run([old, new], [{'car_code': 'J99', 'year_code': '05', 'model': 'JF1', 'range': (1, 9)}], '2018/2')
chk(got(res)[0] == '02', f'KA81 の期間で選ぶはずが {got(res)}')

print('unit_vehicle_serial: all ok' if ok else 'unit_vehicle_serial: NG')
sys.exit(0 if ok else 1)
