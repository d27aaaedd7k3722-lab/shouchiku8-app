# -*- coding: utf-8 -*-
"""境界値の試験（2026-09-29 バグハント）: 空・None・0・負の金額・全角・カンマ付きの数字・紛らわしい名前で、
その日に足した関数が落ちないこと・変な値を返さないことを確かめる。ADDATA は使わない。

    PYTHONIOENCODING=utf-8 python .claude/skills/pdf-to-neo/scripts/tests/test_edge_values.py
"""
from __future__ import annotations

import copy
import os
import sys

HERE = os.path.dirname(os.path.realpath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
import skill_env  # noqa: E402
skill_env.apply()
import draft_estimate as de  # noqa: E402
import header_auto as ha  # noqa: E402
import print_check as pc  # noqa: E402
import reading_check as rc  # noqa: E402
import estimate_to_neo as en  # noqa: E402

FAILS: list[str] = []


def t(label, fn, *a, expect=None, check=None):
    try:
        r = fn(*a)
    except Exception as e:  # noqa: BLE001
        FAILS.append(f'{label}: 例外 {type(e).__name__}: {e}')
        return None
    if expect is not None and r != expect:
        FAILS.append(f'{label}: {r!r}（期待 {expect!r}）')
    if check is not None and not check(r):
        FAILS.append(f'{label}: {r!r} が条件を満たさない')
    return r


def test_name_helpers():
    for n in ['', None, ',', ',,', 'A,B,C', 'L,R', 'FR', '1234,5678', 'ﾌﾛﾝﾄ,', ',ﾌﾛﾝﾄ', 'HOOD', 'hood comp', 'ＨＯＯＤ　ＣＯＭＰ', 'PANEL,L',
              'CLIP,L.', 'ASSY', 'COMP,ASSY', 'LED', 'R/F BUMPER']:
        t(f'_honda_name({n!r})', de._honda_name, n)
    t('_honda_name(COMP,ASSY) は読み替えない', de._honda_name, 'COMP,ASSY', expect=None)
    for n in ['', '1/1', '(1/2)', '取替 単体', '2P 塗装', 'ﾘﾔﾋﾞｭｰ', '(5dm²)', '左', 'RH']:
        t(f'_clean_panel_line({n!r})', de._clean_panel_line, n)
        t(f'_fr_of({n!r})', de._fr_of, n)
        t(f'_clean_name({n!r})', de._clean_name, n)


def test_tax_excluded_odd_quantities():
    for qty, price in [('0', '1000'), ('abc', '1000'), ('2.0', '1368'), ('-2', '1368'), ('2', '-1368'), ('', '1368'), ('3', '0'), ('10', '')]:
        rd = {'blocks': [{'title': '', 'rows': [f'|ｸﾘｯﾌﾟ|取替|||{qty}|{price}|||', {'name': 'x', 'qty': qty, 'price': price}]}], 'totals': {}}
        t(f'to_tax_excluded(qty={qty!r}, price={price!r})', rc.to_tax_excluded, rd, 10)
    rd = {'blocks': [{'title': '', 'rows': [{'name': 'x', 'qty': 2, 'price': -1368}]}], 'totals': {}}
    rc.to_tax_excluded(rd, 10)
    if rd['blocks'][0]['rows'][0]['price'] not in (-1244, -1243):
        FAILS.append(f"値引きの数量行の割り戻し: {rd['blocks'][0]['rows'][0]['price']}")


def test_explicit_zero_and_money():
    for v, want in [(None, False), ('', False), (' ', False), (0, True), (0.0, True), ('0', True), ('0.0', True), ('0円', True), ('¥0', True),
                    ('０', True), (False, False), (True, False), ('abc', False), ('1', False), ('-0', True), ('0%', False)]:
        t(f'_explicit_zero({v!r})', en._explicit_zero, v, expect=want)
    t("_int_or_none('1,364')", en._int_or_none, '1,364', expect=1364)
    t('_int_or_none(None)', en._int_or_none, None, expect=None)
    t("_tax_excluded_printed('1,100')", en._tax_excluded_printed, '1,100', expect=1000)


def test_format_and_header():
    for rd in [{}, {'blocks': []}, {'format': 'G'}, {'format': 'g', 'tax_included': '10'}, {'format': '', 'blocks': [{'title': '', 'rows': []}]}]:
        def _f(rd=rd):
            ck = rc.Checker(copy.deepcopy(rd)); ck.load_rows(); ck.check_format(); return ck.detect_format()
        t(f'detect_format({rd})', _f)
    for f in [{}, {'使用者': None, '所有者': None}, {'使用者': '同上'}, {'使用者': '＊＊＊', '所有者': '山田'}, {'所有者': '不明'},
              {'使用者': '確認不可'}, {'型式': None}]:
        t(f'header_auto.build({f})', ha.build, f, '')
    t('「不明商事」は名前のまま', ha.build, {'使用者': '不明商事'}, '', check=lambda r: (r.get('customer') or {}).get('name') == '不明商事')


def test_print_check_empty():
    pr = {'rows': [], 'expenses': [], 'frame': [], 'totals': {}, 'name_only': ['ｽﾃｯﾌﾟｶﾊﾞｰ']}
    rd = {'blocks': [{'title': '', 'rows': [{'code': '', 'name': 'ｽﾃｯﾌﾟｶﾊﾞｰ', 'method': ''}]}]}
    t('金額の無い手入力行', pc.compare, rd, pr, False, check=lambda r: r == [])
    t('name_only の無い pr', pc.compare, rd, {'rows': [], 'expenses': [], 'frame': [], 'totals': {}}, False)
    t('空の写し', pc.compare, {}, {'rows': [], 'expenses': [], 'frame': [], 'totals': {}}, False)
    t('空の下書き', pc.rows_from_estimate, {})
    t('税込の印', pc.read_rows, {'blocks': [{'rows': ['|ｸﾘｯﾌﾟ|取替|||2|1240|||[税込 部品=1368 工賃=]']}]},
      check=lambda r: bool(r) and r[0].get('price_in') == 1368)
    t('負の税込の印', pc.read_rows, {'blocks': [{'rows': ['|値引|取替|||1|-1000|||[税込 部品=-1100 工賃=]']}]})


if __name__ == '__main__':
    for name, fn in sorted(globals().items()):
        if name.startswith('test_') and callable(fn):
            fn()
    print('\n'.join(FAILS) if FAILS else 'edge_values tests: all ok')
    sys.exit(1 if FAILS else 0)
