# -*- coding: utf-8 -*-
"""品番からの車両・装備の逆引き（parts_vehicle_infer.py）の単体テスト。この PC の ADDATA だけで完結する（案件データは見ない）。
    cd files && python claude_neo_pipeline/tests/unit_parts_infer.py

ADDATA から「ある車・装備で本体が選ぶ品番」を作って見積に見立て、逆引きがその車・装備に戻るかを確かめる。
品番の具体値は ADDATA の版で変わるので、テストの中で表から探す。"""
from __future__ import annotations

import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE)); sys.path.insert(0, os.path.dirname(os.path.dirname(HERE)))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.dirname(HERE)), '.claude', 'skills', 'pdf-to-neo', 'scripts'))
try:
    import skill_env
    skill_env.apply()
except Exception:  # noqa: BLE001
    pass
from estimate_to_neo import AddataParts, NeoBuilder  # noqa: E402
from parts_vehicle_infer import PartsVehicleInference, pick, vehicle_cv  # noqa: E402

NB = NeoBuilder()
# N-BOX（JF1）。型式指定・類別があるので車検証だけで 1 台に決まる（test_pick_grade と同じ車）
VEH = {'model_code': 'JF1', 'serial_no': 'JF1-0000001', 'desig': '17075', 'category': '0061', 'reg_date': 'H28.10', 'color_code': 'YR586P'}


def _car():
    v = NB.resolve_vehicle(VEH, {})
    return v['neo_car']


def _pvi(car_code):
    return PartsVehicleInference(AddataParts(NB.engine, car_code), NB.resolver)


def _cv(car, eva=()):
    return vehicle_cv(car['YearCode'], car['BodyCode'], car['GradeCode'], car['FVACode'], car.get('SBaseCode', ''), eva=set(eva))


def _decisive(pvi, car):
    """装備 L を足すと本体の選ぶ品番が変わり、しかもその品番は L 以外の 1 文字では選ばれない部品 (ref, L, 装備ありの品番, なしの品番)"""
    base = _cv(car)
    for ref, rows in sorted(pvi.k.items()):
        b0 = pick(rows, base)
        if not b0:
            continue
        for L in pvi.options:
            b1 = pick(rows, _cv(car, {L}))
            if not b1 or b1['pn'] == b0['pn']:
                continue
            others = [M for M in pvi.options if M != L and (pick(rows, _cv(car, {M})) or {}).get('pn') == b1['pn']]
            if not others:
                return ref, L, b1['pn'], b0['pn']
    return None


def test_rule_group_is_at_most():
    """年式群は「車の群以下」の行が当てはまり、大きい方が優先（一致ではない）"""
    rows = [{'grp': ' ', 'body': 0, 'flags': ' ' * 7, 'pn': 'A'}, {'grp': '1', 'body': 0, 'flags': ' ' * 7, 'pn': 'B'},
            {'grp': '3', 'body': 0, 'flags': ' ' * 7, 'pn': 'C'}]
    assert pick(rows, vehicle_cv('02', '10', 'A', 'A'))['pn'] == 'B'
    assert pick(rows, vehicle_cv('00', '10', 'A', 'A'))['pn'] == 'A'
    assert pick(rows, vehicle_cv('05', '10', 'A', 'A'))['pn'] == 'C'


def test_rule_body_beats_grade_and_equipment():
    """ボディ専用の行は、グレード・装備が一致する共通行より優先"""
    rows = [{'grp': ' ', 'body': 0, 'flags': 'B    X ', 'pn': 'G'}, {'grp': ' ', 'body': 20, 'flags': ' ' * 7, 'pn': 'BODY'}]
    assert pick(rows, vehicle_cv('01', '20', 'B', 'A', eva={'X'}))['pn'] == 'BODY'
    assert pick(rows, vehicle_cv('01', '10', 'B', 'A', eva={'X'}))['pn'] == 'G'


def test_rule_fva_letters_count_as_equipment():
    """[5:7] の文字は FVA（エンジン区分・4WD の Z）でも満たされる。すべての文字が要る"""
    rows = [{'grp': ' ', 'body': 0, 'flags': ' ' * 7, 'pn': 'N'}, {'grp': ' ', 'body': 0, 'flags': '     Z ', 'pn': '4WD'},
            {'grp': ' ', 'body': 0, 'flags': '     ZX', 'pn': '4WDX'}]
    assert pick(rows, vehicle_cv('01', '10', 'A', 'ZA'))['pn'] == '4WD'
    assert pick(rows, vehicle_cv('01', '10', 'A', 'ZA', eva={'X'}))['pn'] == '4WDX'
    assert pick(rows, vehicle_cv('01', '10', 'A', 'A', eva={'X'}))['pn'] == 'N'


def test_equipment_round_trip():
    """本体が装備 L ありで選ぶ品番を見積に書けば L が「有」、なしで選ぶ品番なら「無」に戻る"""
    car = _car(); pvi = _pvi(car['CarCode'])
    hit = _decisive(pvi, car)
    if not hit:
        print('  （この ADDATA の N-BOX に、装備 1 文字で品番が決まる部品が無いので省略）'); return
    ref, L, pn_on, pn_off = hit
    for pn, want_on in ((pn_on, True), (pn_off, False)):
        evs = pvi.evidence([{'code': f'{ref:04d}', 'parts_no': pn, 'method': '取替', 'qty': 1}])
        assert evs, f'{ref:04d} {pn} を証拠にできていない'
        r = pvi.score(evs, car['YearCode'], car['BodyCode'], car['GradeCode'], car['FVACode'], car.get('SBaseCode', ''))
        assert (L in r['eva_on']) == want_on, f'{ref:04d} {pn}: 装備 {L} の有無 {r}'
        if not want_on:
            assert L in r['eva_off'], f'{ref:04d} {pn}: 装備 {L} が「無」と決まっていない {r}'


def test_generator_uses_inferred_equipment():
    """生成器は品番で「有」と決まった装備を CarEVA に書き、人の指定が無ければ旧方式の多数決は使わない"""
    car = _car(); pvi = _pvi(car['CarCode'])
    hit = _decisive(pvi, car)
    if not hit:
        return
    ref, L, pn_on, pn_off = hit
    est = {'source': 'unit_parts_infer', 'issuer': '', 'est_date': '20260922', 'vehicle': VEH, 'customer': {}, 'insurance': {}, 'labor_rate': 8000,
           'paint': {}, 'expenses': [], 'totals': {},
           'items': [{'code': f'{ref:04d}', 'name': 'ﾃｽﾄ', 'method': '取替', 'qty': 1, 'parts_no': pn_on, 'price': 1000}]}
    _neo, rep = NeoBuilder().build(est, VEH, hints={}, labor_rate=8000, est_date='20260922', insurance={})
    assert L in (rep.get('eva_write') or []), f'品番 {pn_on} で装備 {L} が付いていない（{rep.get("eva_write")}, {rep.get("parts_infer")}）'
    est['items'][0]['parts_no'] = pn_off
    _neo, rep = NeoBuilder().build(est, VEH, hints={}, labor_rate=8000, est_date='20260922', insurance={})
    assert L not in (rep.get('eva_write') or []), f'品番 {pn_off} なのに装備 {L} が付いた'
    # 人の除外指定は逆引きより強い
    est['items'][0]['parts_no'] = pn_on
    _neo, rep = NeoBuilder().build(est, VEH, hints={'eva_exclude': [L]}, labor_rate=8000, est_date='20260922', insurance={})
    assert L not in (rep.get('eva_write') or []), 'eva_exclude が逆引きに負けている'


def test_vehicle_ranking_keeps_truth_on_top():
    """ある候補で本体が選ぶ品番を並べた見積なら、その候補は必ず最高点に残る（同じ品番になる別の候補が並ぶことはある）"""
    car = _car(); pvi = _pvi(car['CarCode'])
    cv = _cv(car)
    items = []
    for ref, rows in sorted(pvi.k.items()):
        if len({x['pn'] for x in rows}) < 2:
            continue
        b = pick(rows, cv)
        if b and b['pn']:
            items.append({'code': f'{ref:04d}', 'parts_no': b['pn'], 'method': '取替', 'qty': 1})
        if len(items) >= 40:
            break
    evs = pvi.evidence(items)
    assert evs, '証拠が作れていない'
    cands = [{'car_code': car['CarCode'], 'year_code': y, 'body_code': b, 'grade_code': g, 'fva_code': f2.strip()[-1:], 'four_wd': f2.startswith('Z')}
             for (y, b, g, f2) in (NB.resolver.header_db(car['CarCode']).get('records') or {})]
    rk = pvi.rank(evs, cands, fixed_eva=set())
    top = {(cands[i]['year_code'], cands[i]['body_code'], cands[i]['grade_code'], cands[i]['fva_code'], cands[i]['four_wd']) for i in rk['top']}
    me = (car['YearCode'], car['BodyCode'], car['GradeCode'], car['FVACode'][-1:], car['FVACode'].startswith('Z'))
    assert me in top, f'正解の車が最高点に居ない（{len(top)} 台）'
    assert len(top) < len(cands), '品番で 1 台も絞れていない'


def test_unknown_part_number_is_not_evidence():
    """ADDATA に無い品番（版違い・社外品）と手入力行は証拠にしない"""
    car = _car(); pvi = _pvi(car['CarCode'])
    ref = next(iter(sorted(pvi.k)))
    assert not pvi.evidence([{'code': f'{ref:04d}', 'parts_no': 'ZZZZZ-99999', 'method': '取替', 'qty': 1}])
    assert not pvi.evidence([{'code': '', 'parts_no': pvi.k[ref][0]['pn'], 'name': 'x', 'manual': True}])


def _est(items):
    return {'source': 't', 'issuer': '', 'est_date': '20260922', 'vehicle': VEH, 'customer': {}, 'insurance': {}, 'labor_rate': 8000,
            'paint': {}, 'expenses': [], 'totals': {}, 'items': items}


def test_human_equipment_is_not_doubled():
    """品番が「P か Q のどちらか」としか決まらないとき、人が hints.eva_codes で Q を選んだら、仮に採る P を足さない（Q だけ）"""
    car = _car(); pvi = _pvi(car['CarCode'])
    found = None
    for ref, rows in sorted(pvi.k.items()):
        b0 = pick(rows, _cv(car))
        by = {}
        for L in pvi.options:
            b = pick(rows, _cv(car, {L}))
            if b and b0 and b['pn'] != b0['pn']:
                by.setdefault(b['pn'], []).append(L)
        found = next(((ref, pn, Ls) for pn, Ls in by.items() if len(Ls) >= 2), None)
        if found:
            break
    if not found:
        print('   （この版の ADDATA に「どれかの装備で同じ品番」の部品が無いので飛ばす）')
        return
    ref, pn, Ls = found
    evs = pvi.evidence([{'code': f'{ref:04d}', 'parts_no': pn, 'qty': 1}])
    r = pvi.score(evs, car['YearCode'], car['BodyCode'], car['GradeCode'], car['FVACode'], car.get('SBaseCode', ''))
    other = [L for L in Ls if L not in r['eva_on']][0]
    _n, rep = NeoBuilder().build(_est([{'code': f'{ref:04d}', 'name': 'x', 'method': '取替', 'qty': 1, 'parts_no': pn, 'price': 1000}]), VEH,
                                 hints={'eva_codes': [other]}, labor_rate=8000, est_date='20260922', insurance={})
    got = set(rep.get('eva_write') or [])
    assert other in got and not (set(Ls) - {other}) & got, (other, sorted(got))


def test_vehicle_hint_is_not_overridden():
    """型式指定の無い車で人がグレード名のヒントを書いたら、品番の点数が別のグレードを推しても車を替えない（★ で知らせる）"""
    veh = {'model_code': 'JF1', 'serial_no': 'JF1-2000000', 'reg_date': 'H28.10', 'color_code': 'YR586P'}
    allv = NB.resolve_vehicle(veh, {'candidate_limit': 0})
    cands = [c for c in allv['candidates'] if c.get('grade_code')]
    if allv.get('confidence') in ('confirmed', 'high') or len(cands) < 2:
        print('   （この版の ADDATA では車台番号だけで決まるので飛ばす）')
        return
    pvi = _pvi(cands[0]['car_code'])

    def cvof(c):
        return vehicle_cv(c['year_code'], c['body_code'], c['grade_code'], ('Z' if c['four_wd'] else '') + c['fva_code'])
    pair = None
    for A in cands:
        if sum(1 for c in cands if c['grade_name'] == A['grade_name']) != sum(1 for c in cands if c['grade_code'] == A['grade_code']):
            continue
        for B in cands:
            if B['grade_code'] == A['grade_code']:
                continue
            items = []
            for ref, rows in sorted(pvi.k.items()):
                pa, pb = pick(rows, cvof(A)), pick(rows, cvof(B))
                if pa and pb and pa['pn'] != pb['pn']:
                    items.append({'code': f'{ref:04d}', 'name': 'x', 'method': '取替', 'qty': 1, 'parts_no': pb['pn'], 'price': 1000})
                if len(items) >= 3:
                    break
            if len(items) >= 3:
                pair = (A, B, items); break
        if pair:
            break
    if not pair:
        print('   （グレードで品番の割れる部品が無いので飛ばす）')
        return
    A, B, items = pair
    h = {'grade_name': A['grade_name']}
    want = NB.resolve_vehicle(veh, h)['neo_car']['GradeCode']
    e = _est(items); e['vehicle'] = veh
    _n, rep = NeoBuilder().build(e, veh, hints=h, labor_rate=8000, est_date='20260922', insurance={})
    b = rep['vehicle']
    assert (b.get('best') or {}).get('grade_code') == want, ((b.get('best') or {}).get('grade_code'), want)
    assert any(x.startswith('★ 品番の逆引き') for x in b.get('evidence') or []), b.get('evidence')


def test_pick_agrees_with_generator():
    """逆引きの行選び pick と、生成器の AddataParts._cogni_pick が同じ行を選ぶ（年式群・ボディ・グレード・装備を振る）"""
    car = _car(); ap = AddataParts(NB.engine, car['CarCode']); pvi = _pvi(car['CarCode'])
    from estimate_to_neo import _bparse
    n = bad = 0
    for ref in sorted(pvi.k)[:400]:
        rows11 = [r for r in ap._load_11_raw().get(ref, []) if r['disp'] == 'K']
        for y in ('', '01', '03'):
            for g in ('', car['GradeCode']):
                for eva in ((), tuple(pvi.options[:1])):
                    a = pick(pvi.k[ref], vehicle_cv(y, car['BodyCode'], g, car['FVACode'], car.get('SBaseCode', ''), eva=set(eva)))
                    grp = y[-1] if y.isdigit() and int(y) else ''
                    b = ap._cogni_pick(rows11, g, car['FVACode'], set(eva), grp, _bparse(str(car['BodyCode']), str(car.get('SBaseCode', '') or '')))
                    n += 1
                    if (a or {}).get('pn') != (b or {}).get('pn') and ap.norm_pn((a or {}).get('pn')) != ap.norm_pn((b or {}).get('pn')):
                        bad += 1
    assert n and bad == 0, (n, bad)


def test_human_equipment_clash_is_reported():
    """人が hints.eva_codes に書いた装備が、見積の品番では「無」と決まるなら ★ で知らせる"""
    car = _car(); pvi = _pvi(car['CarCode'])
    found = None
    for ref, rows in sorted(pvi.k.items()):
        b0 = pick(rows, _cv(car))
        for L in pvi.options:
            b = pick(rows, _cv(car, {L}))
            if b and b0 and b['pn'] != b0['pn']:
                found = (ref, b0['pn'], L); break
        if found:
            break
    if not found:
        print('   （装備で品番の割れる部品が無いので飛ばす）')
        return
    ref, pn, L = found
    _n, rep = NeoBuilder().build(_est([{'code': f'{ref:04d}', 'name': 'x', 'method': '取替', 'qty': 1, 'parts_no': pn, 'price': 1000}]), VEH,
                                 hints={'eva_codes': [L]}, labor_rate=8000, est_date='20260922', insurance={})
    ev = rep['vehicle'].get('evidence') or []
    assert any('hints.eva_codes にあるが' in x for x in ev), ev


def main() -> int:
    ng = 0
    for name, fn in sorted((k, v) for k, v in globals().items() if k.startswith('test_')):
        try:
            fn()
            print('ok  ', name)
        except AssertionError as e:
            print('FAIL', name, e)
            ng += 1
    print('unit_parts_infer:', 'all ok' if not ng else f'{ng} 件 NG')
    return 1 if ng else 0


if __name__ == '__main__':
    sys.exit(main())
