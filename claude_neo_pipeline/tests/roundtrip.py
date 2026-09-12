# -*- coding: utf-8 -*-
"""コグニ生成 NEO を正解として、resolver / 部品照合 / 標準指数 の再現率を測る（ラウンドトリップ・ハーネス）
usage: python roundtrip.py [--mode a|b|c|all] [--json out.json]
  a: 名称+品番+価格  b: 名称+価格（品番なし = FAX 概算書式）  c: 名称のみ"""
import sys, os, json, re, collections, argparse
sys.path.insert(0, os.path.dirname(__file__))
_HERE = os.path.dirname(os.path.abspath(__file__))
PIPE = os.environ.get('NEO_PIPELINE') or (os.path.dirname(_HERE) if os.path.basename(_HERE) == 'tests' else os.path.join(_HERE, '..', 'claude_neo_pipeline'))  # tests/ に置いたときは親が pipeline
if not os.path.isdir(PIPE):
    PIPE = os.path.dirname(_HERE)  # tests の親 = claude_neo_pipeline
sys.path.insert(0, PIPE)
import neo_diff
import estimate_to_neo as e
from case_dirs import case_dir  # 案件フォルダ名は NEO_check/_cases.json
from addata_vehicle_resolver import AddataVehicleResolver

F = os.environ.get('NEO_FILES_ROOT') or os.path.normpath(os.path.join(PIPE, '..'))
NC = os.environ.get('NEO_CHECK_ROOT') or os.path.join(os.path.expanduser('~'), 'Documents', 'NEO_check')
NEOS = [
    F + r'\サンプル見積PDF\04011103.neo', F + r'\サンプル見積PDF\04011141.neo',
    F + r'\_開発資料\テスト要　車検証・見積PDF\04-12 テスト見積.neo', F + r'\_開発資料\テスト要　車検証・見積PDF\テスト①\11261526.neo',
    # 工場 NEO の見本 5 本（旧ハーネス v10 samples → NEO_check\_fixtures に移設 2026-09-08。リポジトリ外・顧客情報あり）
    os.path.join(NC, '_fixtures', '12051345.neo'), os.path.join(NC, '_fixtures', '12081431.neo'),
    os.path.join(NC, '_fixtures', '12121650.neo'), os.path.join(NC, '_fixtures', '12151249.neo'),
    os.path.join(NC, '_fixtures', '12241720.neo'),
    os.path.join(case_dir('NONE'), 'NEW4.neo'),
]


def load(path):
    d = neo_diff.load(path)
    em, ifc = d['AnSvEm0001.sld'], d['AnSvIf0001.sld']
    car = dict(ifc.execute('select * from Car').fetchone())
    cs = dict(ifc.execute('select * from CarSearch').fetchone())
    eva = [r[1] for r in ifc.execute('select * from CarEVA') if r[1]]
    st = dict(ifc.execute('select * from Setting').fetchone())
    rows = [dict(r) for r in em.execute('select * from ERParts order by LineNo')]
    return car, cs, eva, st, rows


def vehicle_test(res, car, cs, eva):
    reg = cs.get('ps_CarRegDate') or ''
    reg_s = f'{reg[:4]}/{int(reg[4:6])}' if len(reg) >= 6 and reg[:4].isdigit() and int(reg[4:6]) else ''
    inp = dict(model_code=cs.get('ps_CarSerialNoHead') or '', serial_no=cs.get('ps_CarSerialNo') or '',
               desig=cs.get('ps_CarMouldNo') or '', category=cs.get('ps_CarKindNo') or '', reg_date=reg_s, color_code=car.get('ColorCode') or '')
    try:
        r = res.resolve(**inp)
    except Exception as ex:
        return {'input': inp, 'error': str(ex)[:200]}
    nc = r.get('neo_car') or {}
    keys = ('CarCode', 'YearCode', 'BodyCode', 'GradeCode', 'FVACode', 'WorkCodeUpdateDate')
    got = {k: nc.get(k) for k in keys}; exp = {k: car.get(k) for k in keys}
    got['WorkCodeUpdateDate'] = e.NeoBuilder().dataup_date(nc.get('CarCode', ''))
    got_eva = sorted(x for x in (nc.get('eva') or nc.get('EVA') or []) if x) if isinstance(nc.get('eva') or nc.get('EVA'), (list, tuple, set)) else None
    return {'input': inp, 'confidence': r.get('confidence'), 'expected': exp, 'got': got, 'ok': got == exp,
            'eva_expected': sorted(eva), 'eva_got': got_eva, 'candidates': len(r.get('candidates') or [])}


def equivalent(parts, a, b):
    """別 ref でも 11.DB 名称欄・品番・価格・12.DB 数量・部位が同じなら NEO として同値（0170/0176 の Fﾊﾞﾝﾊﾟｸﾘﾂﾌﾟ）"""
    ra = parts.by_ref.get(a) or []; rb = parts.by_ref.get(b) or []
    if not ra or not rb:
        return False
    ka = {(str(x.get('parts_no')), int(x.get('price') or 0)) for x in ra}; kb = {(str(x.get('parts_no')), int(x.get('price') or 0)) for x in rb}
    return bool(ka & kb) and (parts.name20_by_ref.get(a) == parts.name20_by_ref.get(b)) and parts.qty_by_ref.get(a, 1) == parts.qty_by_ref.get(b, 1) and parts.block_of(a) == parts.block_of(b)


def parts_test(parts, rows, mode, year=''):
    out = collections.Counter(); miss = []
    prev_block = ''
    for r in rows:
        code = r.get('PartsCode') or ''
        if not code or not code.isdigit() or int(code) >= 9900:
            continue
        truth = int(code)
        if truth not in parts.by_ref and truth not in parts.p12 and truth not in parts.block_by_ref:
            out['skip_not_in_addata'] += 1
            continue
        name = r.get('PartsName') or ''
        pn = r.get('PartsNo') or '' if mode == 'a' else ''
        price = r.get('PartsUnitPriceOutTax') if (r.get('PartsCount') or 0) > 1 else r.get('PartsPriceOutTax')
        price = int(price) if price and price > 0 and mode in ('a', 'b') else None
        qty = int(r.get('PartsCount') or 1) if (r.get('PartsCount') or 0) > 1 else None
        try:
            ref, why = parts.find_ref('', pn, name, context_block=prev_block, price=price, qty=qty, year=year)
        except Exception as ex:
            ref, why = None, 'ERR ' + str(ex)[:80]
        ok = ref == truth or (ref is not None and equivalent(parts, ref, truth))
        if ok and ref != truth:
            out['equiv'] += 1
        out['ok' if ok else ('none' if ref is None else 'wrong')] += 1
        if not ok:
            miss.append({'truth': truth, 'name': name, 'pn': r.get('PartsNo'), 'price': price, 'disp': r.get('DisposalCode'), 'got': ref, 'why': why[:120]})
        if ref is not None:  # 本番と同じく、照合できた ref の部位を次行の文脈にする（正解の BlockCode は使わない）
            prev_block = parts.block_of(ref) or prev_block
    return out, miss


def std_test(parts, rows, car, eva):
    out = collections.Counter(); miss = []
    present = [(int(r['PartsCode']), int(r['DisposalCode'])) for r in rows if (r.get('PartsCode') or '').isdigit()]
    for r in rows:
        code = r.get('PartsCode') or ''
        if not code.isdigit() or r.get('WageByManual') not in ('', None) or not r.get('TimeStandard') or r['TimeStandard'] <= 0:
            continue
        d = int(r['DisposalCode'])
        if d not in (0, 1, 2, 3, 6):
            continue
        try:
            std = parts.cogni_standard(int(code), d, car.get('GradeCode', ''), (car.get('FVACode', '') or '')[-1:], set(eva), car.get('YearCode', ''), present, car.get('BodyCode', ''))
        except Exception as ex:
            std = {'time': None, 'secs': 'ERR ' + str(ex)[:60]}
        t = std['time'] if std else None
        ok = t is not None and abs(t - float(r['TimeStandard'])) < 0.005
        if not ok and t is not None and (r.get('Time') or -1) <= 0 and abs(t) < 0.005:
            ok = True; out['ok_blank'] += 1  # Time -1 で TimeStandard だけ残る行（骨格の抑止で古い標準が残る／利用者が工賃を消した）は空欄予測も可
        out['ok' if ok else ('none' if t is None else 'wrong')] += 1
        if not ok:
            miss.append({'code': code, 'disp': d, 'name': r.get('PartsName'), 'expected': r['TimeStandard'], 'wc': (r.get('WorkCode') or '').strip(), 'got': t, 'secs': (std or {}).get('secs')})
    return out, miss


def paint_test(path, car, root):
    """PaintingPanel（標準扱いの行）と PaintingPlan.BaseTime を paint_index で再現"""
    from paint_index import PaintIndex
    d = neo_diff.load(path); em = d['AnSvEm0001.sld']
    pp = dict(em.execute('select * from PaintingPlan').fetchone())
    panels = [dict(r) for r in em.execute('select * from PaintingPanel order by RecordNo')]
    out = collections.Counter(); miss = []
    if not panels:
        return out, miss
    n = len(panels); hf = int(pp.get('HFPainting') or 0); paint = int(pp.get('Paint') or 3); coat = int(pp.get('Coat') or 1)
    try:
        pi = PaintIndex(root, car['CarCode'])
    except Exception as ex:
        return collections.Counter({'error': 1}), [str(ex)[:100]]
    form = pi.form_codes()[0]
    bt = pi.base_time(form, paint, coat, hf, n) if form else None
    if pp.get('BaseTime') is not None and pp['BaseTime'] > 0:
        out['base_ok' if (bt is not None and abs(bt - pp['BaseTime']) < 0.05) else 'base_ng'] += 1
    for p in panels:
        if p.get('WageByManual') not in ('', None):
            continue
        std = pi.standard_times(p.get('PartsCode'), hf, n, paint)
        key = 'new' if p.get('DisposalCode') == 0 else {1: 's1', 2: 's2', 3: 's3'}.get(p.get('PaintingArea') or 1, 's1')
        got = (std or {}).get(key)
        ok = got is not None and abs(got - float(p.get('Time') or 0)) < 0.05
        out['ok' if ok else 'ng'] += 1
        if not ok:
            miss.append({'code': p.get('PartsCode'), 'disp': p.get('DisposalCode'), 'area': p.get('PaintingArea'), 'expected': p.get('Time'), 'got': got})
    return out, miss


def main():
    ap = argparse.ArgumentParser(); ap.add_argument('--mode', default='all'); ap.add_argument('--json', default=''); ap.add_argument('--only', default='')
    a = ap.parse_args()
    modes = ['a', 'b', 'c'] if a.mode == 'all' else [a.mode]
    nb = e.NeoBuilder(); res = AddataVehicleResolver()
    report = {}
    tot = collections.Counter()
    for path in NEOS:
        if a.only and a.only not in path:
            continue
        name = os.path.basename(path)
        try:
            car, cs, eva, st, rows = load(path)
        except Exception as ex:
            print(name, 'LOAD ERR', ex); continue
        cc = car.get('CarCode')
        rep = {'car': cc, 'grade': car.get('GradeCode'), 'fva': car.get('FVACode'), 'rows': len(rows)}
        rep['vehicle'] = vehicle_test(res, car, cs, eva)
        try:
            parts = e.AddataParts(nb.engine, cc)
        except Exception as ex:
            rep['parts_error'] = str(ex)[:120]; report[name] = rep; print(name, rep['vehicle'].get('ok'), 'parts ERR'); continue
        for m in modes:
            c, miss = parts_test(parts, rows, m, car.get('YearCode', ''))
            rep[f'parts_{m}'] = {'count': dict(c), 'miss': miss}
            tot[f'{m}_ok'] += c['ok']; tot[f'{m}_all'] += c['ok'] + c['none'] + c['wrong']
        c, miss = std_test(parts, rows, car, eva)
        rep['std'] = {'count': dict(c), 'miss': miss}
        pc, pm = paint_test(path, car, nb.engine.root)
        rep['paint'] = {'count': dict(pc), 'miss': pm}
        tot['paint_ok'] += pc['ok'] + pc['base_ok']; tot['paint_all'] += pc['ok'] + pc['ng'] + pc['base_ok'] + pc['base_ng']
        tot['std_ok'] += c['ok']; tot['std_all'] += c['ok'] + c['none'] + c['wrong']
        report[name] = rep
        v = rep['vehicle']
        print(f"{name} {cc} vehicle={'OK' if v.get('ok') else 'NG'}({v.get('confidence')}) " + ' '.join(f"{m}={rep[f'parts_{m}']['count']}" for m in modes) + f" std={rep['std']['count']}")
    for m in modes:
        print(f"parts mode {m}: {tot[f'{m}_ok']}/{tot[f'{m}_all']}")
    print(f"std: {tot['std_ok']}/{tot['std_all']}")
    print(f"paint: {tot['paint_ok']}/{tot['paint_all']}")
    if a.json:
        json.dump(report, open(a.json, 'w', encoding='utf-8'), ensure_ascii=False, indent=1, default=str)


if __name__ == '__main__':
    main()
