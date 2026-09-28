# -*- coding: utf-8 -*-
"""速報・確報（自動車車両損害調査報告書）→ header.json（header_auto.py）の単体テスト。PDF は使わず、報告書の 1 ページ目と同じ形の文字列を渡す。
値はすべて架空。

    PYTHONIOENCODING=utf-8 python .claude/skills/pdf-to-neo/scripts/tests/test_header_auto.py
"""
from __future__ import annotations

import os
import sys

HERE = os.path.dirname(os.path.realpath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
import header_auto as ha  # noqa: E402

FAILS: list[str] = []


def check(cond, msg):
    if not cond:
        FAILS.append(msg)
        print('NG', msg)


PAGE = """自動車車両損害調査報告書 作成日 令和8年9月28日 受注日 令和8年9月1日
事故番号
X12345-1234567-01
事故日
令和8年8月3日
契約者名
ヤマダ タロウ
登録番号
品川 300 あ 1234
所有者
山田 太郎
車名
ｼﾞﾑﾆｰ JB64W XL
使用者
同上
型式
3BA-JB64W
グレード
XL/XC
車台No.
JB64W-100001
原動機型式
R06A型(4WD)
初度登録
令和7年5月
型式類別
18786 / 6
有効期限
令和10年5月20日
走行距離
12,345
km
カラーNo.
ZJ3 ｼﾞｬﾝｸﾞﾙｸﾞﾘｰﾝ
画像鑑定
"""

check(ha.is_report(PAGE), '報告書と見分ける')
check(ha.is_report(PAGE.replace('型式類別', '型式指定類別').replace('車台No.', '車台番号')), '項目名の別表記の報告書も見分ける')
f = ha.parse_report(PAGE)
check(f.get('型式') == '3BA-JB64W' and f.get('車台No.') == 'JB64W-100001' and f.get('使用者') == '同上', f'項目の次の行が値 {f}')
h = ha.build(f, 'chubb_ヤマダ_0001_ジムニー_画像鑑定')
v = h['vehicle']
check(v == {'model_code': 'JB64W', 'serial_no': 'JB64W-100001', 'desig': '18786', 'category': '0006', 'reg_date': 'R7.5', 'color_code': 'ZJ3', 'engine': 'R06A'}, f'車両 {v}')
check(h['hints'] == {'grade_name': 'XL'}, f"グレードは / の前 {h['hints']}")
c = h['customer']
check(c['name'] == '山田 太郎', '使用者が「同上」なら所有者が顧客名')
check(c['kilometer'] == '12345' and c['term_date'] == '20280520' and c['reg_no'] == '品川 300 あ 1234', f'顧客 {c}')
i = h['insurance']
check(i['company'] == 'Chubb損害保険' and i['accept_no'] == 'X12345-1234567-01' and i['policy_no'] == i['accept_no'], f'保険（証券番号が無いときは事故番号）{i}')
check(i['accident_date'] == '20260803' and i['presence_date'] == '写真鑑定', f'事故日・画像鑑定 {i}')
f2 = ha.parse_report(PAGE.replace('車台No.', '車台番号'))
check(f2.get('車台No.') == 'JB64W-100001', '項目名が「車台番号」の報告書でも車台番号を読む')
check(ha.strip_emission('6AANHP170G') == 'NHP170G' and ha.strip_emission('DBA-ZRR70W') == 'ZRR70W' and ha.strip_emission('JF3') == 'JF3', '排ガス記号を除く')
check(ha.wareki_ym('平成27年5月') == 'H27.5' and ha.wareki_ymd('令和元年5月1日') == '20190501', '和暦')
hdr = {'vehicle': {'desig': '99999'}}
wrote = ha.apply(hdr, h, overwrite=False)
check(hdr['vehicle']['desig'] == '99999' and 'vehicle.desig' not in wrote and 'vehicle.category' in wrote, '既にある値は上書きしない')
print('OK' if not FAILS else f'NG {len(FAILS)} 件')
sys.exit(1 if FAILS else 0)
