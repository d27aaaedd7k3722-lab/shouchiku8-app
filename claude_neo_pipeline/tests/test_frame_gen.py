# -*- coding: utf-8 -*-
"""骨格組合せ: 生成器 NEO とコグニ保存 NEO（FRAME_p7 / FRAME_p8）の ERParts を行単位で比較"""
import sys, os, json, copy
SP = os.path.dirname(os.path.abspath(__file__))
F = os.path.dirname(os.path.dirname(SP))  # tests → claude_neo_pipeline → files
sys.path.insert(0, SP); sys.path.insert(0, os.path.join(F, 'claude_neo_pipeline')); sys.path.insert(0, F)
import neo_diff as nd
import estimate_to_neo as e
from case_dirs import case_dir  # noqa: E402
NC = case_dir('NONE')
base = json.load(open(os.path.join(NC, 'estimate.json'), encoding='utf-8'))
COLS = ['PartsCode', 'DisposalCode', 'Time', 'TimeStandard', 'WageOutTax', 'WageStandardOutTax', 'WageByManual', 'ChangeTotalOutTax', 'ConstructGroup', 'WorkCode', 'Provisional', 'WageFileTime', 'PartsPriceOutTax', 'PartsNo', 'PartsNoStandard', 'PartsPriceStandardOutTax', 'PartsPriceByManual', 'PartsName', 'PartsNameStandard']
CASES = {'FRAME_p7': ['1410', '1420', '1430', '1434', '1500', '1511', '1600'], 'FRAME_p8': ['1904', '1950'], 'FRAME_p9': ['1400', '1442', '1503', '1510', '1511', '1517']}
nb = e.NeoBuilder()
tot_ok = tot_all = 0
for tag, codes in CASES.items():
    est = copy.deepcopy(base)
    est['labor_rate'] = 86100; est['index_policy'] = 'auto'; est['paint'] = {}; est['expenses'] = []; est['totals'] = {}
    est['items'] = [{'code': c, 'name': '', 'method': '取替', 'qty': 1} for c in codes]
    neo, rep = nb.build(est, est['vehicle'], hints=est.get('hints'), labor_rate=86100)
    out = os.path.join(SP, f'gen_{tag}.neo'); open(out, 'wb').write(neo)
    G = nd.load(out)['AnSvEm0001.sld']; C = nd.load(os.path.join(NC, tag + '.neo'))['AnSvEm0001.sld']
    q = f"select {','.join(COLS)} from ERParts order by PartsCode"
    g = {str(r[0]).strip(): tuple(r) for r in G.execute(q)}; c = {str(r[0]).strip(): tuple(r) for r in C.execute(q)}
    print('==', tag)
    for code in codes:
        gr, cr = g.get(code), c.get(code)
        for i, col in enumerate(COLS):
            if gr is None or cr is None or gr[i] != cr[i]:
                print(f'  NG {code} {col}: gen={gr[i] if gr else None!r} cogni={cr[i] if cr else None!r}')
            else:
                tot_ok += 1
            tot_all += 1
print('cells', tot_ok, '/', tot_all)
