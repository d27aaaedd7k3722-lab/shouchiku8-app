# -*- coding: utf-8 -*-
"""印刷 PDF と見積書の写しの突き合わせ（print_check.py）の単体テスト。
PDF は使わず、コグニ帳票の文字層と同じ形の文字列を渡す（ADDATA も要らない）。

    PYTHONIOENCODING=utf-8 python .claude/skills/pdf-to-neo/scripts/tests/test_print_check.py
"""
from __future__ import annotations

import os
import sys

HERE = os.path.dirname(os.path.realpath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
import print_check as pc  # noqa: E402

PAGE = """1 / 2
ｺｰﾄﾞ 修理項目／部品名称／塗装項目 修理方法／部品番号／塗装面積 部品価格(円) 工賃(円)
0100     Fﾊﾞﾝﾊﾟｶﾊﾞ- 取替 52119-B2G40 45,000 8,000
0140 左  Fﾌｴﾝﾀﾞ 脱着 1,600
3800 Rrﾗｲｾﾝｽﾌﾟﾚｰﾄ脱着修正 脱着修理 再封印 12,000 *
6350 ﾙｰﾌﾍｯﾄﾞﾗｲﾆﾝｸﾞ一部脱着 脱着 6,400
6347 左ｻｰﾄﾞｼｰﾄ(脱着･修理) 脱着 2,400
0170     ｸﾘﾂﾌﾟ 取替 90467-08186       (04) 520
【内板骨格修正】
1371 基本修正作業 28,000 n
1388 左リヤフロアサイドメンバ 修正 ﾗﾝｸ B 12,000 n
1396 リヤフロアクロスメンバ 修正 基本内 n
【塗装明細】
塗装費用計 120,000
0100 Fﾊﾞﾝﾊﾟｶﾊﾞ- 塗装 1/1 2.5 20,000
【費用】
配線修理 240 4,000
写真代他 2,000
ページ小計 240 6,000
小      計 45,000 30,400
課 税 額 計 195,400
消  費  税 19,540
合      計 214,940
G0141016 部品価格適応日 08年 9月 1日
"""

READING = {
    'blocks': [{'title': '', 'rows': [
        '0100|Fﾊﾞﾝﾊﾟｶﾊﾞｰ|取替|52119-B2G40|||45000|8000||',
        '0140|左 Fﾌｪﾝﾀﾞ|脱着|||||1600||',
        {'code': '3800', 'name': 'Rrﾗｲｾﾝｽﾌﾟﾚｰﾄ脱着修正', 'method': '脱着修理', 'parts_no': '再封印', 'wage': 12000},
        '6350|ﾙｰﾌﾍｯﾄﾞﾗｲﾆﾝｸﾞ一部脱着|脱着|||||6400||',
        '6347|左ｻｰﾄﾞｼｰﾄ(脱着･修理)|脱着|||||2400||',
        '0170|ｸﾘｯﾌﾟ|取替|90467-08186||4|520|||',
    ]}],
    'expenses': [{'name': '配線修理', 'amount': 240, 'in': '部品計'}, {'name': '配線修理', 'amount': 4000, 'in': '作業計'},
                 {'name': '写真代他', 'amount': 2000, 'in': '作業計'}],
    'frame': {'basic': True, 'items': [{'code': '1388', 'rank': 'B', 'wage': 12000}, {'code': '1396', 'rank': '基本内'}]},
    'totals': {'taxable': 195400, 'tax': 19540, 'total': 214940},
}

ok = True


def chk(cond, msg):
    global ok
    if not cond:
        ok = False
        print('  NG', msg)


def test_parse_and_compare():
    pr = pc.parse_print([PAGE])
    codes = [r['code'] for r in pr['rows']]
    chk(codes == ['0100', '0140', '3800', '6350', '6347', '0170'], f'明細の拾い方が違う: {codes}')   # 塗装明細の 0100 を明細にしない
    chk([r['code'] for r in pr['frame']] == ['1371', '1388', '1396'], f"内板骨格: {[r['code'] for r in pr['frame']]}")
    chk([e['name'] for e in pr['expenses']] == ['配線修理', '写真代他'], f'費用: {pr["expenses"]}')   # 合計欄・ページ小計を費用にしない
    chk(pr['totals'].get('taxable') == 195400 and pr['totals'].get('total') == 214940, f'合計: {pr["totals"]}')
    chk(pr['price_date'] == '080901', f'部品価格適応日: {pr["price_date"]}')
    by = {r['code']: r for r in pr['rows']}
    chk(by['3800']['name'] == 'Rrﾗｲｾﾝｽﾌﾟﾚｰﾄ脱着修正' and by['3800']['method'] == '脱着修理', f'名称/区分の切り分け: {by["3800"]}')
    chk(by['3800'].get('pn_text') == '再封印', f'品番欄の文字: {by["3800"]}')
    chk(by['6350']['name'] == 'ﾙｰﾌﾍｯﾄﾞﾗｲﾆﾝｸﾞ一部脱着', f'名称に区分の語が入る行: {by["6350"]}')
    chk(by['6347']['name'] == '左ｻｰﾄﾞｼｰﾄ(脱着･修理)', f'括弧の中の区分語で切っている: {by["6347"]}')
    chk(not by['0140'].get('pn_text'), f'指数・金額を品番欄の文字にしている: {by["0140"]}')
    diffs = pc.compare(READING, pr)
    chk(not diffs, f'差が無いはずなのに出た: {diffs}')


def test_finds_the_four_kinds_of_difference():
    """2026-09-28 シエンタで実際に出た 4 種（名称・費用名・骨格の行落ち・品番欄）を見つける"""
    pr = pc.parse_print([PAGE])
    import copy
    rd = copy.deepcopy(READING)
    rd['blocks'][0]['rows'][3] = '6350|ﾙｰﾌﾍｯﾄﾞﾗｲﾆﾝｸﾞ|脱着|||||6400||'          # 名称（印刷にだけ「一部脱着」）
    rd['expenses'][0]['name'] = '配線・配管費用'                                  # 費用名
    rd['frame']['items'].append({'code': '1389', 'rank': 'A', 'wage': 5600})      # 骨格の行が印刷に無い
    rd['blocks'][0]['rows'][2] = {'code': '3800', 'name': 'Rrﾗｲｾﾝｽﾌﾟﾚｰﾄ脱着修正', 'method': '脱着修理', 'wage': 12000}   # 品番欄
    d = ' / '.join(pc.compare(rd, pr))
    for w in ('名称', '費用名', '内板骨格の行', '品番欄'):
        chk(w in d, f'{w} の差を見つけていない: {d}')


def test_parse_print_pdf_reads_by_word_position():
    """コグニの「PDF(通常)」出力は名称と区分が 1 語にくっつき、文字列の並びも崩れる。語の座標で欄を読む（2026-09-28）。
    PyMuPDF が無い PC では飛ばす"""
    try:
        import fitz  # type: ignore  # noqa: PLC0415
    except ImportError:
        print('   skip test_parse_print_pdf_reads_by_word_position（PyMuPDF が無い）')
        return
    import tempfile
    doc = fitz.open()
    pg = doc.new_page(width=595, height=842)
    def put(x, y, t):
        pg.insert_text((x, y), t + ' ', fontname='japan', fontsize=8)   # コグニの PDF も欄の間に空白がある（語が分かれる）
    for x, t in ((31, 'ｺｰﾄﾞ'), (87, '修理項目／部品名称'), (266, '修理方法／部品番号'), (419, '部品価格(円)'), (496, '工賃(円)')):
        put(x, 300, t)
    put(27, 330, '0030'); put(54, 330, '左Frﾊﾞﾝﾊﾟｻｲﾄﾞｽﾍﾟ-ｻ取替'); put(253, 330, '71280-3M0-003'); put(463, 330, '640')
    put(27, 346, '0186'); put(54, 346, 'ｽｸﾘﾕｸﾞﾛﾒﾂﾄ'); put(202, 346, '取替'); put(253, 346, '90682-SDA-A01'); put(343, 346, '(02)'); put(465, 346, '250')
    put(54, 362, '配線修理'); put(470, 362, '240'); put(521, 362, '4,000')
    put(54, 378, '合計'); put(521, 378, '1,102,977'); put(560, 378, '*')
    path = os.path.join(tempfile.mkdtemp(), 'p.pdf')
    doc.save(path)
    pr = pc.parse_print_pdf(path)
    chk(pr is not None, 'PDF を読めない')
    rows = {r['code']: r for r in pr['rows']}
    chk(rows.get('0030', {}).get('method') == '取替' and rows['0030']['name'].endswith('ｽﾍﾟ-ｻ') and rows['0030']['pn'] == '71280-3M0-003',
        f"名称と区分のくっついた語を分ける {rows.get('0030')}")
    chk(rows.get('0186', {}).get('qty') == '2' and rows['0186']['money'] == [250], f"数量と金額 {rows.get('0186')}")
    chk([(e['name'], e['money']) for e in pr['expenses']] == [('配線修理', [240, 4000])], f"費用名は区分で切らない {pr['expenses']}")
    chk(pr['totals'].get('total') == 1102977, f"合計 {pr['totals']}")


for _n, _f in sorted((k, v) for k, v in dict(globals()).items() if k.startswith('test_')):
    _f()
    print('ok  ', _n)
print('print_check tests: all ok' if ok else 'print_check tests: NG')
sys.exit(0 if ok else 1)
