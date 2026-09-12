# -*- coding: utf-8 -*-
"""他工場のコグニ生成 NEO 10 本の骨格行 ChangeTotal を「標準部品代 + 単独取替標準工賃」で検算（単価は標準行から逆算、±10 円）"""
import sys, os, collections
SP = os.path.dirname(os.path.abspath(__file__))
F = os.path.dirname(os.path.dirname(SP))  # tests → claude_neo_pipeline → files
sys.path.insert(0, SP); sys.path.insert(0, os.path.join(F, 'claude_neo_pipeline')); sys.path.insert(0, F)
import roundtrip as rt, estimate_to_neo as e
nb = e.NeoBuilder(); ok = ng = 0; miss = []
for path in rt.NEOS:
    car, cs, eva, st, rows = rt.load(path); ap = e.AddataParts(nb.engine, car['CarCode'])
    rates = [round(r['WageStandardOutTax'] / r['TimeStandard']) for r in rows if (r.get('TimeStandard') or 0) > 0 and (r.get('WageStandardOutTax') or 0) > 0]
    rate = collections.Counter(rates).most_common(1)[0][0] if rates else 0
    present = [(int(r['PartsCode']), int(r['DisposalCode'])) for r in rows if (r.get('PartsCode') or '').isdigit()]
    for r in rows:
        code = r.get('PartsCode') or ''
        if not code.isdigit() or ap.block_of(int(code)) not in ap.FRAME_BLOCKS:
            continue
        ps = int(r.get('PartsPriceStandardOutTax') or 0); ct = r.get('ChangeTotalOutTax')
        if ct is None or ct < 0:
            continue
        std = ap.cogni_standard(int(code), 0, car.get('GradeCode', ''), (car.get('FVACode', '') or '')[-1:], set(eva), car.get('YearCode', ''), present, car.get('BodyCode', ''))
        base = (std or {}).get('base', 0) or 0
        pred = (ps if ps > 0 else 0) + e.r10_even(base * rate)
        if abs(pred - ct) <= 10:
            ok += 1
        else:
            ng += 1; miss.append((os.path.basename(path)[:8], code, 'ct', ct, 'pred', pred, 'base', base, (r.get('WorkCode') or '').strip()))
print('ChangeTotal(骨格, ±10) ok', ok, 'ng', ng)
for m in miss[:10]:
    print('  ', m)
