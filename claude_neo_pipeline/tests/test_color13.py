# -*- coding: utf-8 -*-
"""色別部品（83.DB / 13.DB）の品番予測を実 NEO の取替行と突き合わせる。
13.DB 車種（D88 / U52 / D98 / W64）と 83.DB 車種（S64 / J95）の ERParts 取替行のうち、11.DB の変種に色別フラグ（[70] & 1）が立つ部品について
生成器 colored_part(ref, ColorCode, grade, fva, eva, 11.DB 変種の品番) の品番・価格が NEO の PartsNo / PartsPriceStandardOutTax と一致するか。
usage: python test_color13.py"""
import os, sys, collections
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import neo_diff, roundtrip
import estimate_to_neo as e

SP = os.path.dirname(os.path.abspath(__file__))
F = os.path.dirname(os.path.dirname(SP))  # tests → claude_neo_pipeline → files


def run():
    nb = e.NeoBuilder() if hasattr(e, 'NeoBuilder') else None
    tot = collections.Counter(); miss = []
    for p in roundtrip.NEOS + [os.path.join(roundtrip.NC, "COLOR_D98.neo")]:
        if not os.path.exists(p):
            print('MISSING', os.path.basename(p)); continue
        tot['files'] += 1
        d = neo_diff.load(p)
        car = dict(d['AnSvIf0001.sld'].execute('select * from Car').fetchone())
        cc = car['CarCode']; color = (car.get('ColorCode') or '').strip()
        try:
            eva = [r[0] for r in d['AnSvIf0001.sld'].execute('select EVACode from CarEVA')] if any(t[0] == 'CarEVA' for t in d['AnSvIf0001.sld'].execute("select name from sqlite_master where type='table'")) else []
        except Exception:
            eva = []
        parts = e.AddataParts(nb.engine, cc)
        r11 = parts._load_11_raw()
        src = 'none'
        for s_ in ('83', '13'):
            if os.path.exists(os.path.join(nb.engine.root, cc[0], cc, f'{cc}{s_}.DB')):
                src = s_
        try:
            reg = (d['AnSvIf0001.sld'].execute('select ps_CarRegDate from CarSearch').fetchone() or [''])[0] or ''
        except Exception:
            reg = ''
        ctx = {'grade': car.get('GradeCode', ''), 'fva': (car.get('FVACode', '') or '')[-1:], 'eva': set(eva), 'color': color, 'year': car.get('YearCode', ''), 'body': str(car.get('BodyCode', '') or ''), 'reg_ym': str(reg)[:6]}
        parts.vehicle_body = ctx['body']
        rows = [dict(r) for r in d['AnSvEm0001.sld'].execute('select PartsCode, PartsNo, PartsNoStandard, PartsPriceStandardOutTax, DisposalCode from ERParts')]
        n_ok = n_ng = n_skip = 0
        for r in rows:
            code = r.get('PartsCode') or ''
            if r.get('DisposalCode') != 0 or not code.isdigit() or int(code) >= 9000:
                continue
            ref = int(code)
            if not any((int(x.get('color_flag') or 0) & 1) and x.get('disp') == 'K' for x in r11.get(ref, [])):
                continue
            var, _ = parts.variant(ref, '', ctx, 0)
            std_pn = str(var['parts_no']) if var else ''
            cp = parts.colored_part(ref, color, ctx['grade'], ctx['fva'], ctx['eva'], std_pn, ctx['reg_ym']) if parts.variant_color_flag(ref, std_pn, ctx['body'], ctx) else None
            truth_pn = (r.get('PartsNoStandard') or r.get('PartsNo') or '').replace('*', '').strip()
            truth_price = int(r.get('PartsPriceStandardOutTax') or 0)
            if not truth_pn:  # 品番の無い行（保留・手入力）は比較しない
                continue
            got_pn = cp['pn'] if cp else std_pn  # 色別行が無ければ 11.DB の変種のまま（コグニも同じ）
            got_price = int(cp['price']) if cp else int((var or {}).get('price') or 0)
            if parts.norm_pn(got_pn) == parts.norm_pn(truth_pn):
                n_ok += 1
                if truth_price > 0 and got_price != truth_price:
                    tot['price_diff'] += 1; miss.append((os.path.basename(p), cc, src, code, 'price', got_price, truth_price, got_pn))
            else:
                n_ng += 1; miss.append((os.path.basename(p), cc, src, code, got_pn, got_price, truth_pn, truth_price, 'std', std_pn, 'cp' if cp else 'no-cp'))
        print(f"{os.path.basename(p)} {cc} color={color!r} reg={ctx['reg_ym']!r} src={src} ok={n_ok} ng={n_ng}")
        tot['ok'] += n_ok; tot['ng'] += n_ng; tot['none'] += n_skip
    for m in miss:
        print('  MISS', m)
    print(f"color parts: pn ok {tot['ok']} / ng {tot['ng']} (price diff {tot['price_diff']})")
    tot['miss_list'] = miss
    return tot


# 既知の不一致（担当者がダイアログで 2 行目以降を選んだ例と、旧データ版の '*' 付き品番。NEO 名, 部品コード → 正解品番）
KNOWN = {
    ('04011141.neo', '0645'): '53105-B2290',   # ﾒﾂｷ（仕様違い、ダイアログ）
    ('04011141.neo', '2310'): '68102-B2681',   # ｽ-ﾊﾟ-UV&IRｶﾂﾄｶﾞﾗｽ（仕様違い）
    ('04-12 テスト見積.neo', '0010'): '52119-B5100-A1',  # 素材色/塗装済み（ダイアログ）
    ('04-12 テスト見積.neo', '1200'): '67002-B5060',     # ﾄﾞｱﾎﾟｹﾂﾄ付車（仕様違い）
    ('12051345.neo', '4300'): '67005-52E60',   # ﾊﾞﾂｸｶﾒﾗ付車（仕様違い）
    ('12151249.neo', '0010'): '52119-B2G40-C0',  # 旧データ版（2025.12）の '*' 付き品番
    ('12151249.neo', '0094'): '52722-B2121-C0',  # 同上
    ('COLOR_D98.neo', '0182'): '52561-B2030',  # ダイアログで 1 行目を選んだ実験（生成器は初度登録 2025.01 を含む B2031）
}


# 期待値（2026-09-06 夜の確定状態。NEO 11 本すべてが揃っていること、pn 94/102、既知 8 例外、価格差 42 = 旧データ版の価格改定分）
EXPECTED = {'files': 11, 'ok': 94, 'ng': 8, 'price_diff': 42}


if __name__ == '__main__':
    t = run()
    unknown = [m for m in t.get('miss_list', []) if m[4] != 'price' and KNOWN.get((m[0], m[3])) != m[6]]
    for m in unknown:
        print('  UNEXPECTED', m)
    got = {'files': t.get('files', 0), 'ok': t['ok'], 'ng': t['ng'], 'price_diff': t['price_diff']}
    print(f"known exceptions {len(KNOWN)}, unexpected mismatches {len(unknown)}, got {got}, expected {EXPECTED}")
    sys.exit(0 if (not unknown and got == EXPECTED) else 1)
