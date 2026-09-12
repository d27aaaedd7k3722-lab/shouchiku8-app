# -*- coding: utf-8 -*-
"""23.DB の無い車種（J69 パートナー）の樹脂バンパ塗装 = COM/FBANPA.DB: 生成器とコグニ保存 NEO（FBANPA_J69.neo、3コートパール、
Fバンパ 外傷修正 標準 黒ライン 4.4 / Rバンパ 新品 大型 黒ライン 3.0）の PaintingBumper を比較。単体値（画面読取 16 値）も検証"""
import sys, os
SP = os.path.dirname(os.path.abspath(__file__))
F = os.path.dirname(os.path.dirname(SP)) if os.path.basename(SP) == 'tests' else os.path.dirname(SP)
sys.path.insert(0, SP); sys.path.insert(0, os.path.join(F, 'claude_neo_pipeline')); sys.path.insert(0, F)
import neo_diff as nd, estimate_to_neo as e
from paint_index import PaintIndex
from case_dirs import case_dir
NC = os.environ.get('NEO_CHECK_ROOT') or os.path.join(os.path.expanduser('~'), 'Documents', 'NEO_check')
pi = PaintIndex(os.environ.get('ADDATA_ROOT') or r'C:\Addata', 'J69')
OBS = [((4, '新品', 0, 0), 2.6), ((4, '新品', 0, 1), 3.0), ((4, '新品', 0, 2), 3.3), ((4, '新品', 1, 1), 2.9), ((4, '新品', 1, 2), 3.2),
       ((2, '新品', 0, 0), 2.2), ((2, '新品', 0, 1), 2.5), ((2, '新品', 0, 2), 2.6), ((2, '新品', 1, 0), 2.1), ((2, '新品', 1, 1), 2.4), ((2, '新品', 1, 2), 2.5),
       ((2, '変形修正', 0, 1), 4.6), ((2, '変形修正', 1, 0), 3.8), ((2, '外傷修正', 0, 1), 4.0), ((2, '外傷修正', 1, 0), 3.2),
       ((4, '変形修正', 0, 1), 5.0), ((4, '変形修正', 1, 1), 4.9), ((4, '外傷修正', 0, 1), 4.5), ((4, '外傷修正', 1, 1), 4.4)]
ok = 0
for (coat, kind, form, col), exp in OBS:
    got = pi.bumper_time_generic(coat, kind, form, col)
    ok += (got is not None and abs(got - exp) < 0.001) or print('NG', coat, kind, form, col, got, exp) is not None
print('FBANPA unit', ok, '/', len(OBS))
nb = e.NeoBuilder()
est = {'labor_rate': 10000, 'index_policy': 'auto', 'items': [{'code': '0600', 'name': '', 'method': '取替', 'qty': 1}], 'expenses': [], 'totals': {},
       'paint': {'paint': 3, 'coat': '３コートパール', 'material_rate': 15, 'panels': [{'code': '0600', 'method': '取替'}],
                 'bumper_front': {'method': '外傷修正', 'form': '標準', 'color': '黒ライン', 'draft': '無し'}, 'bumper_rear': {'method': '新品', 'form': '大型', 'color': '黒ライン'}}}
veh = {'model_code': 'GJ3', 'serial_no': 'GJ3-1200001', 'desig': '', 'category': '', 'reg_date': '2007/1', 'color_code': ''}
neo, rep = nb.build(est, veh, hints={'grade_name': 'EL'}, labor_rate=10000)
out = os.path.join(SP, 'gen_FBANPA_J69.neo'); open(out, 'wb').write(neo)
G = nd.load(out)['AnSvEm0001.sld']; C = nd.load(os.path.join(case_dir('NONE'), 'FBANPA_J69.neo'))['AnSvEm0001.sld']
cols = ['fb_Disposal', 'fb_Name', 'fb_Form', 'fb_FormName', 'fb_Color', 'fb_ColorName', 'fb_Draft', 'fb_DraftName', 'fb_Time', 'fb_TimeStandard', 'fb_WageOutTax', 'fb_WageByManual',
        'rb_Disposal', 'rb_Form', 'rb_FormName', 'rb_Color', 'rb_Time', 'rb_TimeStandard', 'rb_WageOutTax']
q = f"select {','.join(cols)} from PaintingBumper"
g = tuple(G.execute(q).fetchone()); c = tuple(C.execute(q).fetchone())
ng = 0
for k, a, b in zip(cols, g, c):
    if a != b:
        ng += 1; print('NG', k, a, b)
print('FBANPA bumper cells NG', ng, '/', len(cols))
