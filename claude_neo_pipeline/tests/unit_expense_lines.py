# -*- coding: utf-8 -*-
"""費用 36 行の割付の単体テスト（実案件 800 本で確定した実機の構造。2026-09-21）

  行 1〜8  = NameFix=1 / Attribute=1〜8 の固定行。名前は全工場共通（AnDefine.ini [CostItem] が正本）
  行 9〜36 = NameFix=0 / Attribute=0 の自由行。名前は工場の雛形ごとに違い、行番号に意味は無い
            → 自由行をキーワードで決め打ちしてはいけない。載せた行の Name が見積書に刷られる
  レッカー  = **自由行**に載せる。帳票様式だけ見ると固定行 5/6 ＋ Total.hy_Wrecker1/2 が正しく見えるが、
            実機 NEO cogni_CXA は 'ﾚｯｶｰ' を自由行 36 に置き、実案件 800 本でも行 5/6 と hy_Wrecker は 0 本。
            行 5/6 は人が総合計画面のレッカー欄に直接入れたときの置き場で、費用欄から自動で流れない

    cd files && PYTHONIOENCODING=utf-8 python claude_neo_pipeline/tests/unit_expense_lines.py
"""
from __future__ import annotations

import os
import sys

HERE = os.path.dirname(os.path.realpath(__file__))
sys.path.insert(0, os.path.dirname(HERE)); sys.path.insert(0, HERE)
from estimate_to_neo import NeoBuilder, _exp_key, _pick_template_line  # noqa: E402
import neo_diff  # noqa: E402

VEH = {'model_code': 'JF1', 'serial_no': 'JF1-0000001', 'desig': '17075', 'category': '0061', 'reg_date': 'H28.10', 'color_code': ''}
ITEMS = [{'code': '0100', 'name': 'Fﾊﾞﾝﾊﾟ', 'method': '脱着', 'qty': 1}]

ok = True


def chk(cond, msg):
    global ok
    if not cond:
        ok = False
        print('  NG', msg)
    return cond


def build(expenses):
    nb = NeoBuilder()
    est = {'source': 'unit_expense_lines', 'issuer': '', 'est_date': '20260921', 'vehicle': VEH, 'customer': {}, 'insurance': {},
           'labor_rate': 8000, 'items': ITEMS, 'paint': {}, 'expenses': expenses, 'totals': {}, 'hints': {}}
    neo, rep = nb.build(est, VEH, hints={}, labor_rate=8000, est_date='20260921', insurance={})
    tmp = os.path.join(os.environ.get('TEMP', HERE), 'unit_expense_lines.neo')
    open(tmp, 'wb').write(neo)
    d = neo_diff.load(tmp)
    em = d['AnSvEm0001.sld']
    ec = [c[1] for c in em.execute('pragma table_info(Expense)')]
    exp = {r[ec.index('LineNo')]: dict(zip(ec, r)) for r in em.execute('select * from Expense')}
    tc = [c[1] for c in em.execute('pragma table_info(Total)')]
    tot = dict(zip(tc, em.execute('select * from Total').fetchone()))
    return exp, tot, rep


def used_lines(exp):
    return {ln: e for ln, e in exp.items() if e['PartsEnabled'] or e['WageEnabled']}


def amt(e):
    return (e['PartsPriceOutTax'] or 0) + (e['WageOutTax'] or 0)


print('-- 突き合わせ用のキー --')
chk(_exp_key('ｺｰﾃｨﾝｸﾞ') != _exp_key('コーティング'), '半角カナと全角を同じキーにしている（実機は区別する）')
chk(_exp_key('配線・配管費用') == _exp_key('配線配管費用'), '中黒のゆれを吸収しない')
chk(_exp_key('ｴｰﾐﾝｸﾞ費用') != _exp_key('ｴｰﾐﾝｸﾞ'), '別の名前が同じキーになっている')

print('-- 前方一致の向き（雛形の名前が費用名で始まるときだけ寄せる）--')
chk(_pick_template_line({9: 'ｴｰﾐﾝｸﾞ費用'}, 'ｴｰﾐﾝｸﾞ', set()) == 9, '短い費用名が長い雛形名に寄らない（実機 cogni_CXA の向き）')
chk(_pick_template_line({9: 'ｴｰﾐﾝｸﾞ'}, 'ｴｰﾐﾝｸﾞ作業', set()) is None,
    '長い費用名を短い雛形名に寄せている（PDF より情報の少ない名前が刷られる。Codex 指摘）')
chk(_pick_template_line({9: 'ｴｰﾐﾝｸﾞ'}, 'ｴｰﾐﾝｸﾞ', set()) == 9, '完全一致で寄らない')
chk(_pick_template_line({9: 'ｴｰﾐﾝｸﾞ費用'}, 'ｴｰﾐﾝｸﾞ', {(9, 'wage')}) is None, '使用中の行を選んでいる')
chk(_pick_template_line({9: '', 10: ''}, 'ｴｰﾐﾝｸﾞ', set()) is None, '空の雛形名に前方一致している')
chk(_pick_template_line({9: 'ｴｰﾐﾝｸﾞ費用'}, '', set()) is None, '空の費用名を寄せている')

print('-- 固定行 1〜8（全工場共通。名前は書き換えない）--')
exp, tot, _ = build([{'name': 'ショートパーツ', 'amount': 3000},
                     {'name': '写真代', 'amount': 1000},
                     {'name': '文字書き費用', 'amount': 2000}])
u = used_lines(exp)
chk(set(u) == {1, 4, 7}, f'固定行に載っていない: {sorted(u)}')
chk(exp[4]['Name'] == 'ショートパーツ' and exp[7]['Name'] == '写真代他' and exp[1]['Name'] == '文字書き費用',
    '固定行の名前を書き換えている（NameFix=1 の行は変更不可）')
chk(amt(u[4]) == 3000 and amt(u[7]) == 1000 and amt(u[1]) == 2000, '固定行の金額が違う')

print('-- レッカーは自由行（実機 cogni_CXA と同じ。固定行 5/6 へ自動で寄せない）--')
exp, tot, _ = build([{'name': 'レッカー代', 'amount': 22000}, {'name': 'ｼｮｰﾄﾊﾟｰﾂ', 'amount': 1500, 'kind': 'parts'}])
u = used_lines(exp)
chk(5 not in u and 6 not in u, f'レッカーを固定行 5/6 に寄せている: {sorted(u)}')
lek = [ln for ln in u if ln >= 9]
chk(len(lek) == 1, f'レッカーが自由行に 1 行で載っていない: {sorted(u)}')
chk(exp[lek[0]]['Name'] == 'ﾚｯｶｰ代',
    f"自由行の名前が '{exp[lek[0]]['Name']}'（ﾚｯｶｰ代 のはず。自由行の名前は半角カナで書く）")
# 実機・実案件 800 本とも hy_Wrecker は 0。費用欄から自動で流さない
chk(tot['hy_Wrecker1OutTax'] == 0 and tot['hy_Wrecker2OutTax'] == 0,
    'hy_Wrecker に費用欄のレッカーを流している（実機は総合計画面で人が入れたときだけ使う）')
chk(tot['hy_WageTaxTotalOutTax'] == 22000, f"レッカーが費用工賃計に入っていない（{tot['hy_WageTaxTotalOutTax']}）")
chk(tot['hy_PartsTaxTotalOutTax'] == 1500, 'ショートパーツが費用部品計に入っていない')

print('-- 自由行: 雛形に同じ名前があればその行に載せ、名前は変えない --')
exp, tot, _ = build([{'name': 'ｺｰﾃｨﾝｸﾞ', 'amount': 5000}])
u = used_lines(exp)
ln = next(iter(u))
chk(ln >= 9, f'自由行に載っていない（行 {ln}）')
chk(_exp_key(exp[ln]['Name']) == _exp_key('ｺｰﾃｨﾝｸﾞ'), f"載せた行の名前が '{exp[ln]['Name']}'（ｺｰﾃｨﾝｸﾞ のはず）")

print('-- 自由行: 半角カナと全角は別物（実機がそうしている）--')
# 雛形の行 12 は 'ｺｰﾃｨﾝｸﾞ'(半角)。'コーティング'(全角) は別の名前なので、そこへは寄せずに名前を書いて載せる
exp, tot, _ = build([{'name': 'コーティング', 'amount': 5000}])
u = used_lines(exp)
ln2 = next(iter(u))
chk(ln2 != ln, f'半角カナの行に全角の費用を寄せている（どちらも行 {ln}）')
chk(exp[ln2]['Name'] == 'ｺｰﾃｨﾝｸﾞ',
    f"載せた行の名前が '{exp[ln2]['Name']}'（ｺｰﾃｨﾝｸﾞ のはず。寄せは全角のまま判定し、書くときに半角カナへ直す）")

print('-- 自由行: 前方一致で雛形の行に寄せる（実機 cogni_CXA の ｴｰﾐﾝｸﾞ → ｴｰﾐﾝｸﾞ費用）--')
exp, tot, _ = build([{'name': 'ｴｰﾐﾝｸﾞ', 'amount': 15000}])
u = used_lines(exp)
ln3 = next(iter(u))
chk(exp[ln3]['Name'] == 'ｴｰﾐﾝｸﾞ費用', f"'ｴｰﾐﾝｸﾞ' が雛形の 'ｴｰﾐﾝｸﾞ費用' の行に寄っていない（'{exp[ln3]['Name']}'）")

print('-- 自由行: 前方一致の候補が複数なら寄せずに名前を書く --')
# 雛形には '室内清掃費'(行9) と 'ｴﾝｼﾞﾝﾙｰﾑ清掃'(行19) があり、'清掃' がどちらか決められない
exp, tot, _ = build([{'name': '清掃', 'amount': 3000}])
u = used_lines(exp)
ln4 = next(iter(u))
chk(_exp_key(exp[ln4]['Name']) == _exp_key('清掃'),
    f"曖昧なのに雛形の行へ寄せた（'{exp[ln4]['Name']}'）")

print('-- 自由行: 雛形に無い名前は空き行に載せ、**名前を書く** --')
exp, tot, _ = build([{'name': 'ﾎﾟﾘｯｼｬｰ仕上', 'amount': 4000}])
u = used_lines(exp)
ln = next(iter(u))
chk(ln >= 9, f'自由行に載っていない（行 {ln}）')
chk(_exp_key(exp[ln]['Name']) == _exp_key('ﾎﾟﾘｯｼｬｰ仕上'),
    f"名前を書いていない（'{exp[ln]['Name']}' のまま）。見積書に雛形の費用名が刷られてしまう")

print('-- 自由行: 雛形の名前と違えば、似ていても決め打ちしない --')
# 雛形の行 13 は 'ｴｰﾐﾝｸﾞ費用'。PDF が 'ｴｰﾐﾝｸﾞ作業' なら、行 13 に載せて名前を残してはいけない
exp, tot, _ = build([{'name': 'ｴｰﾐﾝｸﾞ作業', 'amount': 8000}])
u = used_lines(exp)
ln = next(iter(u))
chk(_exp_key(exp[ln]['Name']) == _exp_key('ｴｰﾐﾝｸﾞ作業'),
    f"載せた行の名前が '{exp[ln]['Name']}'（ｴｰﾐﾝｸﾞ作業 のはず）。雛形の名前が見積書に刷られる")

print('-- 部品費用と工賃費用が同じ名前なら同じ行に載る（従来どおり）--')
exp, tot, _ = build([{'name': 'ﾎﾟﾘｯｼｬｰ仕上', 'amount': 4000},
                     {'name': 'ﾎﾟﾘｯｼｬｰ仕上', 'amount': 2000, 'kind': 'parts'}])
u = used_lines(exp)
chk(len(u) == 1, f'同じ名前が別の行に分かれた: {sorted(u)}')
ln = next(iter(u))
chk(exp[ln]['WageOutTax'] == 4000 and exp[ln]['PartsPriceOutTax'] == 2000, '同じ行の部品側・工賃側に入っていない')

print('-- 前方一致で寄せた行も、同じ費用名の部品側・工賃側で共有する（Codex 指摘 2026-09-21）--')
# 'ｴｰﾐﾝｸﾞ' は雛形の 'ｴｰﾐﾝｸﾞ費用' の行に前方一致で寄る。行の名前は雛形のままなので
# 「行の名前と費用名が一致するか」では引き直せない。載せた費用名を覚えておく必要がある
exp, tot, _ = build([{'name': 'ｴｰﾐﾝｸﾞ', 'amount': 15000},
                     {'name': 'ｴｰﾐﾝｸﾞ', 'amount': 3000, 'kind': 'parts'}])
u = used_lines(exp)
chk(len(u) == 1, f'同じ費用名が別の行に分かれた: {sorted(u)}')
ln5 = next(iter(u))
chk(exp[ln5]['Name'] == 'ｴｰﾐﾝｸﾞ費用', f"雛形の行に寄っていない（'{exp[ln5]['Name']}'）")
chk(exp[ln5]['WageOutTax'] == 15000 and exp[ln5]['PartsPriceOutTax'] == 3000, '同じ行の部品側・工賃側に入っていない')

print('unit_expense_lines: all ok' if ok else 'unit_expense_lines: NG')
sys.exit(0 if ok else 1)
