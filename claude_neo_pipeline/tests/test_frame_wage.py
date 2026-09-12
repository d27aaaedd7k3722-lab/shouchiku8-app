# -*- coding: utf-8 -*-
"""工賃だけ印字（指数なし）／工賃 0 の骨格行: 生成器が FRAME_p7 と同じ標準欄・WorkCode になるか"""
import sys, os, json, copy
SP = os.path.dirname(os.path.abspath(__file__))
F = os.path.dirname(os.path.dirname(SP))  # tests → claude_neo_pipeline → files
sys.path.insert(0, SP); sys.path.insert(0, os.path.join(F, 'claude_neo_pipeline')); sys.path.insert(0, F)
import neo_diff as nd, estimate_to_neo as e
from case_dirs import case_dir  # noqa: E402
NC = case_dir('NONE')
base = json.load(open(os.path.join(NC, 'estimate.json'), encoding='utf-8'))
est = copy.deepcopy(base); est['labor_rate'] = 86100; est['index_policy'] = 'auto'; est['paint'] = {}; est['expenses'] = []; est['totals'] = {}
codes = ['1410', '1420', '1430', '1434', '1500', '1511', '1600']
wages = {'1410': 792120, '1420': 439110}
est['items'] = [{'code': c, 'name': '', 'method': '取替', 'qty': 1, 'wage': wages.get(c, 0)} for c in codes]
nb = e.NeoBuilder(); neo, rep = nb.build(est, est['vehicle'], hints=est.get('hints'), labor_rate=86100)
out = os.path.join(SP, 'gen_FRAME_wage.neo'); open(out, 'wb').write(neo)
G = nd.load(out)['AnSvEm0001.sld']; C = nd.load(os.path.join(NC, 'FRAME_p7.neo'))['AnSvEm0001.sld']
COLS = ['PartsCode', 'Time', 'TimeStandard', 'WageOutTax', 'WageStandardOutTax', 'WageByManual', 'ChangeTotalOutTax', 'WorkCode', 'ConstructGroup']
q = f"select {','.join(COLS)} from ERParts order by PartsCode"
g = {str(r[0]).strip(): tuple(r) for r in G.execute(q)}; c = {str(r[0]).strip(): tuple(r) for r in C.execute(q)}
ng = 0
for code in codes:
    for i, col in enumerate(COLS):
        if g[code][i] != c[code][i]:
            ng += 1; print('NG', code, col, g[code][i], c[code][i])
print('wage-only test NG cells', ng, '/', len(codes) * len(COLS))
