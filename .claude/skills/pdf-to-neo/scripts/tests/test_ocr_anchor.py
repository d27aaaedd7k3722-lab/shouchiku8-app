# -*- coding: utf-8 -*-
"""OCR ＋ ADDATA 照合（ocr_anchor.py）の単体テスト。PDF・OCR・ADDATA は使わない（判定の部品だけを確かめる）。
例はすべて 2026-09-28 に実案件の FAX で実際に起きた読み違い（名称・番号は部品の一般名だけ）。

    PYTHONIOENCODING=utf-8 python .claude/skills/pdf-to-neo/scripts/tests/test_ocr_anchor.py
"""
from __future__ import annotations

import os
import sys

HERE = os.path.dirname(os.path.realpath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
import ocr_anchor as oa  # noqa: E402

FAILS: list[str] = []


def check(cond, msg):
    if not cond:
        FAILS.append(msg)
        print('NG', msg)


# ---- 修理方法・品番の欄
m = oa.parse_mid('取替71811ー77R10ー5PK(02)')
check(m['method'] == '取替' and m['parts_no'] == '71811-77R10-5PK' and m['qty'] == 2, f'parse_mid 基本 {m}')
m = oa.parse_mid('政替43211ー101303,80')   # 取替の「取」が崩れ、指数 3.80 が品番に続けて読まれた
check(m['method'] == '取替' and m['index'] == '3.80' and m['parts_no'] == '43211-10130', f'parse_mid 指数（カンマ）{m}')
m = oa.parse_mid('42611ー103600.50')
check(m['index'] == '0.50' and m['parts_no'] == '42611-10360', f'parse_mid 指数（品番に続く）{m}')
m = oa.parse_mid('取替48530ー80A312-70')   # 小数点が '-' に化けた
check(m['index'] == '2.70' and m['parts_no'] == '48530-80A31', f'parse_mid 指数（-）{m}')
m = oa.parse_mid('取替12345-67890-01')     # 枝番 -01 は指数ではない（残りが 5-5 にならない）
check(m['index'] == '' and m['parts_no'] == '12345-67890-01', f'parse_mid 枝番を指数にしない {m}')
m = oa.parse_mid('取替195/80R15107/105ー')
check('/' in m['parts_no'], f'parse_mid タイヤの品番の / {m}')
check(oa.parse_mid('点検')['method'] == '点検', '点検を読む')
check(oa.parse_mid('鈑金')['method'] == '鈑金', '鈑金は印字どおり（板金に変えない）')
check(oa.parse_mid('2.80')['method'] == '' and oa.parse_mid('2.80')['index'] == '2.80', '修理方法の字が無い行')

# ---- 品番の読み違い
check(oa.pn_ocr_confusable('90189-O6OO6', '90189-06006'), 'O と 0 は読み違い')
check(oa.pn_ocr_confusable('90189CC006', '9018906006'), 'C は 0 にも 6 にも化ける（C-HR 90189-06006）')
check(not oa.pn_ocr_confusable('90189-09006', '90189-06006'), '9 と 6 は読み違いの組ではない')
check(oa.pn_ocr_confusable('7571G10090', '7571010090'), 'G と 0 は読み違い')
check(not oa.pn_ocr_confusable('64716-52180-C0', '64716-52180-A0'), '色違いの末尾 C0 / A0 は読み違いではない')

check(oa.pn_ocr_noise('893433220-C7', '89341-33220-C7'), 'FAX の字落ち・ハイフンずれ（枝番 C7 は同じ）')
check(not oa.pn_ocr_noise('64716-52180-C0', '64716-52180-A0'), '枝番（色）が違えば崩れではない')
check(oa.pn_ocr_noise('84840-58010', '84840-58011'), '1 字違い（呼び出し側が価格の一致を条件にする）')
check(oa.edit_distance('abc', 'abd') == 1 and oa.edit_distance('abc', 'ac') == 1, '編集距離')

# ---- 工場の名称の書き換え
check(oa.renamed_hint('ルーハッドライニンク。部脱着', 'ﾙ-ﾌﾍﾂﾄﾞﾗｲﾆﾝｸﾞ') != '', '一部脱着を足した名称')
check(oa.renamed_hint('ルー7ハ-ネルヒンシ。取付け部', 'ﾙ-ﾌﾊﾟﾈﾙ') != '', '取付け部を足した名称')
check(oa.renamed_hint('左サードシート', 'ｻｰﾄﾞｼｰﾄ(脱着･修理)') != '', '(脱着･修理) を消した名称')
check(oa.renamed_hint('Rr工ンガレム(シ。ムニ', 'Rrｴﾝﾌﾞﾚﾑ(ｼﾞﾑﾆ-)') == '', 'OCR の崩れ（工）は書き換えではない')
check(oa.renamed_hint('がラスセッ幵舛。イ', 'ｶﾞﾗｽｾﾂﾁﾔｸｻﾞｲ') == '', 'OCR の崩れ（幵舛）は書き換えではない')

# ---- 金額: 読み・多数決・桁数
check(oa.split_mark('21,880S') == ('21,880', '$') and oa.split_mark('2,630#') == ('2,630', '#') and oa.split_mark('5,500') == ('5,500', ''), '金額の後ろの印（S は $）')
check(oa._money_text('1町000') == (None, False), '字の混じった金額は読めない扱い')
check(oa._money_text('34200') == (34200, True), 'カンマの落ちた金額は読める')
check(oa.vote_money(['町000', '8,000', '8,000', '町000'])[:2] == (8000, 2), '多数決（カンマの位置が正しい読みだけ）')
check(oa.vote_money(['2000', '2000', '20,000', '20,000', '20,000'])[0] == 20000, "カンマの無い '2000' は数えない")
check(oa.vote_money(['1,600', '7,600'])[0] is None, '同票は決めない')
check(not oa.money_len_ok(300, 5.0), "'3,000' を '300' と読んだ桁落ちを捨てる")
check(oa.money_len_ok(3000, 5.0), '字数が合う読みは採る')
check(oa.money_len_ok(0, None), '字の幅が分からなければ採る')


# ---- 行の種類
def slot(code='', name='', mid='', price='', wage='', mark=''):
    return {'code': code, 'name': name, 'mid': mid, 'price': price, 'wage': wage, 'mark': mark, 'y': 0, 'pitch': 86}


sl = [slot('4300', 'ﾊﾞｯｸﾄﾞｱﾊﾟﾈﾙ', '取替69100-77R34', '50,200'), slot('保留', 'ｴｷｿﾞｰｽﾄﾊﾟｲﾌﾟ', '取替17410-21D40'),
      slot('', '配線修理', '', '240', '4,000', '*#'), slot('7460', 'ﾊﾞｯﾃﾘ', '脱着'),
      slot('1371', '基本修正作業', '', '', '28,000', 'n'), slot('1388', '左リヤフロアサイドメンバー', '修正ランクB', '', '12,000', 'n'),
      slot('1396', 'リヤフロアクロスメンバー', '修正基本内', '', '', 'n')]
oa.classify(sl)
check([s['kind'] for s in sl] == ['part', 'reserve', 'expense', 'part', 'frame', 'frame', 'frame'], f"classify {[s['kind'] for s in sl]}")
sl = [slot('4300', 'ﾊﾞｯｸﾄﾞｱﾊﾟﾈﾙ', '取替'), slot('', '【奘明細】'), slot('4300', 'ﾊﾞｯｸﾄﾞｱﾊﾟﾈﾙ', '取替89dm')]
oa.classify(sl)
check([s['kind'] for s in sl] == ['part', 'paint', 'paint'], f"塗装明細の見出しが崩れても塗装欄 {[s['kind'] for s in sl]}")

frame, cells = oa.build_frame([slot('1371', '基本修正作業', '', '', '28,000', 'n'), slot('1388', 'x', '修正ランクB', '', '12,000', 'n'),
                               slot('1396', 'y', '修正基本内', '', '', 'n')], 8000)
check(frame.get('basic') and frame.get('basic_wage') == 28000 and frame.get('basic_index') == 3.5, f'骨格の基本 {frame}')
check([(i['code'], i['rank'], i.get('wage')) for i in frame['items']] == [('1388', 'B', 12000), ('1396', '基本内', None)], f"骨格の部位 {frame['items']}")


# ---- 小計でまとめて確かめる
def row(price=None, wage=None, unread_w=False, code='1000'):
    return {'code': code, 'flags': '', 'price': price, 'wage': wage, '_unread': {'price': False, 'wage': unread_w},
            '_sure': {'price': price is not None, 'wage': False}, '_why': [], '_ocr': {'wage': ''}, 'comment': ''}


rows = [row(100, 13500), row(200, None, True), row(300, 2700)]
oa.confirm_by_subtotal(rows, [], {'wage': 34200, 'parts': 600})
check(rows[1]['wage'] == 18000 and rows[1]['comment'].startswith('OCR未確認') and not rows[0]['comment'] and not rows[2]['comment'],
      f"読めない工賃 1 つを小計から逆算 {[r['wage'] for r in rows]} {[r['comment'][:30] for r in rows]}")
rows = [row(100, 12000), row(200, 6400)]
oa.confirm_by_subtotal(rows, [], {'wage': 13400, '_cands': {'wage': {13400, 18400}}})
check(all(not r['comment'] for r in rows), '小計の読みの候補に行の合計があれば確定（3/8 の取り違え）')
rows = [row(100, 12000), row(200, 6400)]
oa.confirm_by_subtotal(rows, [], {'wage': 13400})
check(all(r['comment'].startswith('OCR未確認') for r in rows), '小計と合わなければ工賃は要確認')


# ---- 部品コードを直す（ADDATA の代わりの小さな表）
class FakeAnchor:
    ok = True

    def __init__(self, valid, names, pns=None, prices=None):
        self.valid = set(valid)
        self._names = names
        self._pns = pns or {}
        self._prices = prices or {}

    code_candidates = oa.Anchor.code_candidates

    def std_name(self, c):
        return self._names.get(c, '')

    def pns(self, c):
        return set(self._pns.get(c, ()))

    def unit_prices(self, c):
        return set(self._prices.get(c, ()))


an = FakeAnchor({4312, 4342, 4343, 3620, 5000, 5001, 6000, 3810, 3830},
                {4342: 'ｶﾞﾗｽﾌｱｽﾅﾒ-ﾙ', 4343: 'ｶﾞﾗｽﾌｱｽﾅﾒ-ﾙ', 5000: 'ｸｵ-ﾀﾊﾟﾈﾙ', 5001: 'ｸｵ-ﾀﾊﾟﾈﾙ(ｺｳﾁﾝ)', 6000: 'ｳｲﾝﾄﾞｼ-ﾙﾄﾞｶﾞﾗｽ',
                 3810: 'Rrﾊﾞﾝﾊﾟｶﾊﾞ-', 3830: 'Rrﾊﾞﾝﾊﾟｻｲﾄﾞｻﾎﾟ-ﾄ', 3620: 'Rrﾄﾞｱｱｳﾄｻｲﾄﾞﾊﾝﾄﾞﾙ', 4312: 'ﾊﾞﾂｸﾄﾞｱﾋﾝｼﾞ'},
                pns={4342: ['84513-76F00']}, prices={4342: [100]})
sl = [slot('4312', 'x', '取替'), slot('342', 'ガラスファスナメール', '取替84513ー76F00', '100'), slot('4343', 'ガラスファスナメール', '取替')]
for s in sl:
    s['kind'] = 'part'
oa.decide_codes(sl, an)
check(sl[1]['code4'] == '4342' and not sl[1]['code_why'], f"先頭の桁落ち 342 → 4342（品番で裏が取れる）{sl[1]['code4']} {sl[1]['code_why']}")
sl = [slot('3620', 'x', '脱着'), slot('3訂0', 'ハ。ンハ。カハ。', '0.60', '', '5,250'), slot('6000', '右クオータハ-ネル', ''), slot('5001', 'クオータパネル(コウチン)', '')]
for s in sl:
    s['kind'] = 'part'
oa.decide_codes(sl, an)
check(sl[1]['code4'] == '3810', f"2 桁しか読めない 30 → 並びと名称で 3810 {sl[1]['code4']}")
check(sl[2]['code4'] == '5000' and sl[2]['code_why'], f"並びも名称も合わない 6000 → 5000（要確認つき）{sl[2]['code4']} {sl[2]['code_why']}")

# ---- 仮の値（読みの決まらない欄）: 入れた合計が小計と合うときだけ採る
check(oa.tentative('?3000') == 3000 and oa.tentative('3印00') == 300 and oa.tentative('') is None, '仮の値は読めた数字')
rows = [row(100, 13500), row(200, None, True)]
rows[1]['_tent'] = {'wage': 3000}
oa.confirm_by_subtotal(rows, [], {'wage': 16500})
check(rows[1]['wage'] == 3000 and not rows[1]['comment'] and not rows[0]['comment'], f"仮の値で小計と一致 → 確定 {rows[1]['wage']} {rows[1]['comment']}")
rows = [row(100, 13500), row(200, None, True)]
rows[1]['_tent'] = {'wage': 300}
oa.confirm_by_subtotal(rows, [], {'wage': 16500})
check(rows[1]['wage'] == 3000 and rows[1]['comment'].startswith('OCR未確認'), '仮の値が合わなければ小計から逆算して要確認')
rows = [row(100, 7180)]
oa.confirm_by_subtotal(rows, [], {'_cands': {'wage': {17180}}, '_nest': {'wage': 7.2}})
check(rows[0]['comment'].startswith('OCR未確認'), '先頭の桁落ちの読みでも、行の合計と桁数・下の桁が合わなければ確定しない')
rows = [row(100, 117180)]
oa.confirm_by_subtotal(rows, [], {'_cands': {'wage': {17180}}, '_nest': {'wage': 7.2}})
check(not rows[0]['comment'], '先頭の 1 桁だけ落ちた小計の読み（17,180）と、字の幅で 7 字 → 117,180 と一致')


# ---- 塗装明細の区画（コグニ印刷の並び。項目名は OCR で崩れる）
def ps(code='', name='', mid='', price='', wage='', mark=''):
    return slot(code, name, mid, price, wage, mark)


sec = oa.parse_sections([ps('', '【塗装明細】'), ps('', '', '110,680円'), ps('', 'く内訳>塗装一計', '66,600円'), ps('', '塗装材料代計', '32,380'),
                         ps('', '追加塗装費計', '11,700工'), ps('', '塗料', 'R-MDIAMONT'), ps('', '', '2コートノヾーノレ'),
                         ps('4300', 'ﾊﾞｯｸﾄﾞｱﾊﾟﾈﾙ', '取替89dm', '', '17,100', '#'), ps('5000', '右 ｸｵｰﾀﾊﾟﾈﾙ', '修理90dm(1/3)', '', '15,300', '#'),
                         ps('', '', 'ブース有n(0,5の', '', '4,500', '#'), ps('', '', '加礎数値(2.9の', '', '26,100', '#'), ps('', 'ボデーシーリング', '4.00m', '', '3,600'),
                         ps('', ';オ料代', '', '', '32,380'), ps('', 'サ代割合', '38.0%'), ps('', 'す代単価', '9,500円'), ps('', '材料代係数', '1.30'),
                         ps('', '塩害ガード', '', '', '4,500', '#'), ps('', '新品パネル/プライマ塗布', '', '', '7,200', '#'),
                         ps('', 'ー質用】'), ps('', 'ショートパーツ', '', '1,500'), ps('', '写真代他', '', '', '1,500')],
                        None, {'other': ['塩害ガード', '新品パネル/プライマ塗布'], 'lines': []})
pa = sec['paint']
check(pa and pa['total'] == 66600 and pa['material'] == 32380 and pa['material_rate'] == 38 and pa['material_unit'] == 9500 and pa['material_coefficient'] == 1.3,
      f'塗装明細の頭と材料代 {pa}')
check(pa['coat'] == '2コートパール' and pa['paint'] == '2K' and pa['hf'] == 'しない', f"塗膜 {pa.get('coat')}")
check([(ln['name'].split()[-1] if ln.get('code') else ln['name'], ln.get('index'), ln['wage']) for ln in pa['lines']] ==
      [('取替', 1.9, 17100), ('1/3', 1.7, 15300), ('ブース加算', 0.5, 4500), ('加算基礎数値', 2.9, 26100), ('ボデーシーリング 4.00m', None, 3600)], f"塗装行 {pa['lines']}")
check([o['name'] for o in pa['other']] == ['塩害ガード', '新品パネル/プライマ塗布'] and sum(o['wage'] for o in pa['other']) == 11700, f"追加項目 {pa.get('other')}")
check(sec['labor'] == 9000 and not sec['why'], f"レートは 指数 と 工賃 から、検算は全部合う {sec['labor']} {sec['why']}")
check([x['name'] for x in sec['exp_slots']] == ['ショートパーツ', '写真代他'], '【費用】より下は費用')
_sl = [ps('', '【費用】'), ps('', '写真代他', '', '', '2,000'), ps('', 'よろしく')]
sec = oa.parse_sections(_sl, None, {})
check(sec['paint'] is None and [x['name'] for x in sec['exp_slots']] == ['写真代他'] and _sl[0].get('kind') == 'heading' and _sl[2].get('kind') == 'noise',
      f"費用だけの区画: 見出し・金額の無い行は塗装の行に数えない {[x.get('kind') for x in _sl]}")
sec = oa.parse_sections([ps('', '塗装費用', '', '', '191,360')], None, {})
check(sec['paint'] == {'total': 191360, 'material': 0, 'paint': '2K', 'hf': 'しない'} and sec['why'], f"塗装一式だけ {sec['paint']}")

check(not oa._filled({'parts': None, 'taxable': None}) and not oa._filled({}) and oa._filled({'taxable': 1}), 'reading_pages init の雛形（値が全部 None）は空とみなす')

# ---- 罫線（Pillow があるときだけ）
try:
    from PIL import Image, ImageDraw  # type: ignore
except ImportError:
    Image = None
if Image is not None:
    W, H = 3456, 4400
    im = Image.new('L', (W, H), 255)
    d = ImageDraw.Draw(im)
    for x in (200, 350, 1190, 2370, 2755, 3140):
        d.line((x, 1500, x + 15, 4300), fill=0, width=12)   # 少し傾いた縦線
    d.text((230, 1700), '3810', fill=0)
    clean, vert = oa.remove_rules(im)
    L = oa.layout_a(oa.long_vlines(vert, H), W)
    check(L is not None and len(L) == 6, f'書式 A の縦線 6 本を見つける {None if L is None else [round(x["x"]) for x in L]}')
    if L is not None:
        check(oa.col_of(L, 2500, 2000) == 'price' and oa.col_of(L, 3000, 2000) == 'wage' and oa.col_of(L, 260, 2000) == 'code', '列の振り分け')
        check(clean.getpixel((205, 2500)) == 255, '縦線を白で消す')

print('OK' if not FAILS else f'NG {len(FAILS)} 件')
sys.exit(1 if FAILS else 0)
