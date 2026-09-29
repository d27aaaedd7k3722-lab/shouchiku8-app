# -*- coding: utf-8 -*-
"""技術料だけの書式（指数もレートも印字なし）で、技術料が 10 円の倍数でない工場（コグニの工賃丸め 1 円）のレート逆算。
2026-09-15 スペーシア（S89）の FAX 見積: 13,716 / 3,048 / 762 / 3,810 / 15,240 / 23,622 / 7,620 → 7,620 円。
10 円 / 100 円丸めしか試さないと決まらず、生成器が 100 円刻みの推定（7,600）で標準工賃を作っていた。

    PYTHONIOENCODING=utf-8 python .claude/skills/pdf-to-neo/scripts/tests/test_labor_from_wages.py
"""
from __future__ import annotations

import os
import sys

HERE = os.path.dirname(os.path.realpath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
import skill_env  # noqa: E402

skill_env.apply()
import draft_estimate as de  # noqa: E402

# 型式指定・類別は車種の識別（個人情報ではない）。車台番号は架空
S89 = {'model_code': '5AA-MK94S', 'serial_no': 'MK94S-300001', 'desig': '20824', 'category': '0001', 'reg_date': 'R7.12', 'color_code': 'WBW'}
READING = {'source': 't', 'issuer': 't', 'est_date': '20260823', 'format': 'F', 'vehicle': dict(S89), 'customer': {}, 'insurance': {},
           'paint': {}, 'expenses': [], 'totals': {}}
ROWS_1YEN = ['|ﾊﾞﾝﾊﾟ ﾌﾛﾝﾄ|取替|||1|40700|13716||', '|LH ﾍｯﾄﾞﾗﾝﾌﾟｱｯｼ|取替|||1|70000|3048||',
             '|RH ﾌﾛﾝﾄﾌｰﾄﾞ ﾋﾝｼﾞ|取替|||1|2950|762||', '|LH ﾌﾛﾝﾄﾌｪﾝﾀﾞ ﾊﾟﾈﾙ|取替|||1|23000|3810||',
             '|ｺﾝﾃﾞﾝｻｱｯｼ|取替|||1|29000|7620||', '|ｳｲﾝﾄﾞｼｰﾙﾄﾞｶﾞﾗｽ|取替|||1|187600|23622||']
ROWS_10YEN = ['|ﾊﾞﾝﾊﾟ ﾌﾛﾝﾄ|取替|||1|40700|13720||', '|LH ﾍｯﾄﾞﾗﾝﾌﾟｱｯｼ|取替|||1|70000|3050||',
              '|RH ﾌﾛﾝﾄﾌｰﾄﾞ ﾋﾝｼﾞ|取替|||1|2950|760||', '|LH ﾌﾛﾝﾄﾌｪﾝﾀﾞ ﾊﾟﾈﾙ|取替|||1|23000|3810||',
              '|ｺﾝﾃﾞﾝｻｱｯｼ|取替|||1|29000|7620||', '|ｳｲﾝﾄﾞｼｰﾙﾄﾞｶﾞﾗｽ|取替|||1|187600|23620||']


def _s89_available() -> bool:
    try:
        return de.Drafter(dict(READING, blocks=[])).car.get('CarCode') == 'S89'
    except Exception:  # noqa: BLE001  ADDATA に車種が無い・読めない
        return False


def _draft(rows: list) -> dict:
    return de.Drafter(dict(READING, blocks=[{'title': '鈑金・塗装', 'rows': rows}])).build()


def test_one_yen_wages_give_rate_and_round_1():
    """10 円の倍数でない技術料 → 1 円丸めで逆算して 7,620 円、estimate.wage_round は 1"""
    if not _s89_available():
        print('   skip test_one_yen_wages_give_rate_and_round_1（この ADDATA に S89 が無い）')
        return
    e = _draft(ROWS_1YEN)
    assert e.get('labor_rate') == 7620, f"レートが 7,620 にならない（{e.get('labor_rate')}）"
    assert e.get('wage_round') == 1, f"工賃の丸め単位が 1 円にならない（{e.get('wage_round')}）"
    revs = [r for r in e.get('_review', []) if r.get('kind') == 'レバーレート']
    assert revs and all(r.get('level') == '判断' for r in revs), f'1 円単位で説明できるのにレートの要確認が出ている（{revs}）'


def test_ten_yen_wages_keep_default_units():
    """技術料が全部 10 円の倍数なら従来どおり 10 円 → 100 円丸めで試す（1 円丸めは持ち出さない）"""
    if not _s89_available():
        print('   skip test_ten_yen_wages_keep_default_units（この ADDATA に S89 が無い）')
        return
    e = _draft(ROWS_10YEN)
    assert e.get('labor_rate') == 7620, f"レートが 7,620 にならない（{e.get('labor_rate')}）"
    assert e.get('wage_round', 10) == 10, f"10 円丸めのまま決まるべき（{e.get('wage_round')}）"


def test_declared_round_10_yields_to_one_yen_evidence():
    """reading.wage_round: 10（既定と同じ値）と書いてあっても、10 円の倍数でない技術料は 10 円丸めでは説明できないので
    1 円丸めで逆算する（印字の技術料が証拠。従来も明示の 10 は既定と同じ扱いだった）。100 円の明示はその単位だけで試す"""
    if not _s89_available():
        print('   skip test_declared_round_10_yields_to_one_yen_evidence（この ADDATA に S89 が無い）')
        return
    e = de.Drafter(dict(READING, wage_round=10, blocks=[{'title': '鈑金・塗装', 'rows': ROWS_1YEN}])).build()
    assert e.get('labor_rate') == 7620 and e.get('wage_round') == 1, (e.get('labor_rate'), e.get('wage_round'))
    e = de.Drafter(dict(READING, wage_round=100, blocks=[{'title': '鈑金・塗装', 'rows': ROWS_1YEN}])).build()
    assert not e.get('labor_rate'), f"100 円丸めの明示で 1 円単位の技術料からレートを決めてはいけない（{e.get('labor_rate')}）"
    assert [r for r in e.get('_review', []) if r.get('level') == '要確認' and r.get('kind') == 'レバーレート'], 'レートの要確認が出ていない'


def test_manual_wage_rows_do_not_block_the_rate():
    """印 * （手入力工賃）の行の技術料はレート × 指数でなくてよい。全部では決まらないとき * の行を除いて探す
    （2026-09-28 t12・k03: 2,500 / 10,000 / 2,204 の * 行があるだけでレートが決まらず、# 行の指数を起こせなかった）"""
    if not _s89_available():
        print('   skip test_manual_wage_rows_do_not_block_the_rate（この ADDATA に S89 が無い）')
        return
    rows = ROWS_10YEN + ['|ﾌﾛｱﾏｯﾄ|取替|||1|5000|2204|*|']
    e = _draft(rows)
    assert e.get('labor_rate') == 7620, f"* の行を除けば 7,620 に決まる（{e.get('labor_rate')}）"
    assert e.get('wage_round', 10) == 10, f"丸め単位は * の無い行で決める（{e.get('wage_round')}）"


def test_low_cover_lines_become_paint_low_cover():
    """低隠蔽性塗色の印字 3 行（工賃つき 1 行 ＋ 枚数 2 行）は paint.low_cover 1 つにまとめる（2026-09-28 t09）"""
    if not _s89_available():
        print('   skip test_low_cover_lines_become_paint_low_cover（この ADDATA に S89 が無い）')
        return
    paint = {'paint': '2K', 'coat': 'ソリッド', 'total': 9460,
             'lines': [{'name': '低隠蔽性塗色 ﾙｰﾌ なし', 'wage': 9460}, {'name': 'ﾙｰﾌ以外 取替 2枚', 'wage': None}, {'name': 'ﾙｰﾌ以外 修理 3枚', 'wage': None}]}
    e = de.Drafter(dict(READING, labor_rate=7620, paint=paint, blocks=[{'title': 'x', 'rows': ROWS_10YEN[:1]}])).build()
    lc = (e.get('paint') or {}).get('low_cover') or {}
    assert lc.get('roof') == 'なし' and lc.get('change') == 2 and lc.get('repair') == 3 and lc.get('wage') == 9460, f'low_cover {lc}'
    assert not (e.get('paint') or {}).get('other'), f"枚数の行を追加項目にしない {(e.get('paint') or {}).get('other')}"


def test_method_word_at_end_of_name():
    """区分の列の無い書式で名前の末尾に作業の語（'…交換' '…脱着'）: 切り出して区分にする。部品に当たらない行（手入力の作業行）は印字どおりに戻す（2026-09-29 nc17）"""
    if not _s89_available():
        print('   skip test_method_word_at_end_of_name（この ADDATA に S89 が無い）')
        return
    rows = ['|ﾌﾛﾝﾄﾊﾞﾝﾊﾟ交換||||1|40700|13720||', '|配線修理||||||4000||']
    e = de.Drafter(dict(READING, labor_rate=7620, blocks=[{'title': 'x', 'rows': rows}])).build()
    it = e['items']
    assert it[0].get('method') == '取替' and it[0].get('code') and not it[0].get('manual'), f"'…交換' は取替で部品に当てる {it[0]}"
    assert it[1].get('manual') and '配線修理' in str(it[1].get('name')), f"部品に当たらない作業行は印字どおり {it[1]}"


def test_work_row_and_part_row_are_merged():
    """作業の行（工賃だけ）と部品の行（部品代だけ）が同じ部品コードの取替なら 1 行にまとめる（コグニ以外の書式。nc03・nc10・nc11）"""
    if not _s89_available():
        print('   skip test_work_row_and_part_row_are_merged（この ADDATA に S89 が無い）')
        return
    code = _draft([ROWS_10YEN[0]])['items'][0].get('code')   # この車のフロントバンパの部品コード
    rows = [f'{code}|ﾌﾛﾝﾄﾊﾞﾝﾊﾟ|取替|||||13720||', f'{code}|ﾌﾛﾝﾄﾊﾞﾝﾊﾟｶﾊﾞｰ|取替|||1|40700|||']
    e = de.Drafter(dict(READING, labor_rate=7620, blocks=[{'title': 'x', 'rows': rows}])).build()
    its = [x for x in e['items'] if x.get('code') == code]
    assert len(its) == 1 and its[0].get('price') == 40700 and its[0].get('wage') == 13720, f'1 行にまとまっていない {its}'
    e2 = de.Drafter(dict(READING, format='A', labor_rate=7620, blocks=[{'title': 'x', 'rows': rows}])).build()
    assert len([x for x in e2['items'] if x.get('code') == code]) == 2, 'コグニ印刷（書式 A）はまとめない'


def test_tax_round_without_printed_taxable():
    """課税小計の印字が無い見積でも、総合計 − 消費税 から切り捨ての工場を判定する（2026-09-15 アプリのバグハント O11。
    判定しないと 1 円差で不合格になり、逃げ道のベタ打ちでも切り捨ては作れない）"""
    if not _s89_available():
        print('   skip test_tax_round_without_printed_taxable（この ADDATA に S89 が無い）')
        return
    rows = ['|部品|取替|||1|60005||M|', '|工賃|脱着|||||40000|M|']
    for totals, want in (({'parts': 60005, 'wage': 40000, 'tax': 10000, 'total': 110005}, '切り捨て'),
                         ({'parts': 60005, 'wage': 40000, 'tax': 10001, 'total': 110006}, None),
                         ({'parts': 60005, 'wage': 40000, 'taxable': 100005, 'tax': 10000, 'total': 110005}, '切り捨て')):
        e = de.Drafter(dict(READING, labor_rate=7620, totals=totals, blocks=[{'title': 'x', 'rows': rows}])).build()
        assert e.get('tax_round') == want, (totals, e.get('tax_round'))


def main() -> int:
    ng = 0
    for name, fn in sorted((k, v) for k, v in globals().items() if k.startswith('test_')):
        try:
            fn()
            print('ok  ', name)
        except AssertionError as e:
            print('FAIL', name, e)
            ng += 1
    print('labor_from_wages tests:', 'all ok' if not ng else f'{ng} 件 NG')
    return 1 if ng else 0


if __name__ == '__main__':
    sys.exit(main())
