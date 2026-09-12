# -*- coding: utf-8 -*-
"""実案件 NEO の山（亮平さんがコグニで作った NEO。既定 Z:\\ドキュメント の月別フォルダ、約 7,000 本）で生成器を確かめる開発用ツール。

    python claude_neo_pipeline/tests/corpus_scan.py inventory            # 全 NEO の統計（金額・コード・フラグだけ）→ <NEO_CHECK_ROOT>/_zdocs/inventory.jsonl
    python claude_neo_pipeline/tests/corpus_scan.py roundtrip [月] [本数]  # この PC の ADDATA と同じ月（例 080801）の NEO で 車両・部品・標準指数・塗装の再現率

顧客名・住所・登録番号・車台番号・工場名は書き出さない（工場はディーラーかどうかの真偽だけ）。NEO のファイルは id（パスのハッシュ）で呼び、
id → パスの対応（ファイル名に車名・顧客名が入っていることがある）はファイルに残さず、実行のたびに走査し直してメモリ上で作る。結果は NEO_check（git の外）
NEO の山の場所は環境変数 NEO_CORPUS_ROOT（既定 Z:\\ドキュメント）。ADDATA は毎月更新されるので、roundtrip は同じ月の NEO だけを比べる
（Car.PartsPriceDate が '080801' = 令和 8 年 8 月版）。2026-09-12 の結果は HANDOFF §8 と README §4
"""
import os, sys, json, sqlite3, time, random, collections
from concurrent.futures import ProcessPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))
FILES = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, os.path.join(FILES, 'claude_neo_pipeline')); sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(FILES, '.claude', 'skills', 'pdf-to-neo', 'scripts'))
import neo_container as nc  # noqa: E402
from case_dirs import neo_check_root  # noqa: E402

SRC = os.environ.get('NEO_CORPUS_ROOT') or r'Z:\ドキュメント'
NC = neo_check_root()
OUT = os.path.join(NC, '_zdocs')

DEALER_WORDS = ('トヨタ', 'トヨペット', 'カローラ', 'ネッツ', 'レクサス', 'ホンダ', 'Honda', 'HONDA', '日産', 'ニッサン', 'マツダ', 'スバル', 'SUBARU', 'スズキ', 'ダイハツ', '三菱',
                'ヤマハ', 'いすゞ', 'BMW', 'ベンツ', 'Mercedes', 'アウディ', 'Audi', 'ボルボ', 'VOLVO', 'フォルクスワーゲン', 'ポルシェ', 'BYD', 'プジョー', 'ジープ', 'レンタ')


def dbs(path):
    neo = open(path, 'rb').read()
    ck = nc.find_real_cks(neo)
    dec = nc.decompress_neo(neo, ck)
    _m, entries = nc.parse_entries(neo, ck[0])
    files = nc.extract_files(dec, entries)
    out = {}
    for k in ('AnSvIf0001.sld', 'AnSvEm0001.sld'):
        con = sqlite3.connect(':memory:')
        con.deserialize(files[k])
        out[k] = con
    return out, files


_MONTH = __import__('re').compile(r'^(?:\d{4}-)?[0-9０-９]{1,2}月(?:-[0-9０-９]{1,2}月)?$')  # 月の置き場だけ（顧客名のフォルダは書き出さない）


def _err(e) -> str:
    """例外は種類の名前だけを残す（本文にはファイルのパス＝顧客名が入ることがあるので書き出さない。Codex 指摘）"""
    return type(e).__name__


def _id(rel):
    import hashlib
    return hashlib.sha1(rel.encode('utf-8')).hexdigest()[:12]


def one(path):
    rel = os.path.relpath(path, SRC)
    try:
        d, files = dbs(path)
    except Exception as e:
        return {'id': _id(rel), 'error': _err(e)}
    cif, em = d['AnSvIf0001.sld'], d['AnSvEm0001.sld']
    top = rel.split(os.sep)[0]
    r = {'id': _id(rel), 'folder': top if _MONTH.match(top) else '', 'size': os.path.getsize(path)}  # 月のフォルダ名（１月・2026-7月-12月 など）だけ残す
    try:
        g = lambda db, sql: db.execute(sql).fetchone()  # noqa: E731
        r['est_date'] = g(cif, 'SELECT EstimatedDate FROM FileInfo')[0]
        c = g(cif, 'SELECT CarCode, YearCode, BodyCode, GradeCode, FVACode, ColorCode, CarFormCode, PartsPriceDate, WorkCodeUpdateDate FROM Car')
        r.update(dict(zip(('car', 'year', 'body', 'grade', 'fva', 'color', 'form', 'price_date', 'wc_date'), c)))
        r['eva'] = sorted({x[0] for x in cif.execute('SELECT EVACode FROM CarEVA') if x[0] and str(x[0]).strip()})
        s = g(cif, 'SELECT wb_PriceBase, wb_Round, tx_CalculateFlag, tx_ArrangeFlag FROM Setting')
        r.update(dict(zip(('rate', 'wb_round', 'tx_calc', 'tx_arrange'), s)))
        fac = str((g(cif, 'SELECT ConsultantFactory FROM Insurance') or [''])[0] or '')
        r['factory_is_dealer'] = any(w in fac for w in DEALER_WORDS) if fac.strip() else None  # 工場名そのものは残さない
        er = list(em.execute('SELECT PartsCode, DisposalCode, WageByManual, Provisional, OrderFlag, ReserveFlag, 0, Time, WageOutTax, PartsPriceOutTax, PartsPriceByManual FROM ERParts'))
        r['n_rows'] = len(er)
        r['disp'] = dict(collections.Counter(int(x[1] if x[1] is not None else -9) for x in er))
        r['wbm'] = dict(collections.Counter(str(x[2] or '') for x in er))
        r['n_manual_code'] = sum(1 for x in er if not str(x[0] or '').strip())
        r['n_prov'] = sum(1 for x in er if str(x[3] or '').strip() == '$')
        r['order'] = dict(collections.Counter(str(x[4] or '') for x in er))
        r['n_reserve'] = sum(1 for x in er if int(x[5] or 0) == 1)
        r['ppm'] = dict(collections.Counter(str(x[10] or '') for x in er))
        r['wage_sum'] = sum(int(x[8]) for x in er if x[8] and int(x[8]) > 0)
        r['parts_sum'] = sum(int(x[9]) for x in er if x[9] and int(x[9]) > 0)
        pp = g(em, 'SELECT Paint, Coat, HFPainting, MaterialRateType, MaterialRate, BaseTime, BaseWageByManual, BoothFlag, BumperBaseTime, BumperBaseWageByManual, InputType FROM PaintingPlan')
        r['paint'] = dict(zip(('paint', 'coat', 'hf', 'mat_type', 'mat_rate', 'base', 'base_wbm', 'booth', 'bumper_base', 'bumper_base_wbm', 'input_type'), pp)) if pp else None
        pn = list(em.execute('SELECT PartsCode, DisposalCode, PanelArea, PaintingAreaName, Time, WageByManual, Manual, AddedFrom FROM PaintingPanel'))
        r['n_panel'] = len(pn)
        r['panel_disp'] = dict(collections.Counter(int(x[1] or 0) for x in pn))
        r['panel_ratio'] = dict(collections.Counter(str(x[3] or '') for x in pn))
        r['panel_added'] = sum(1 for x in pn if int(x[7] or 0) == 1)
        r['panel_manual'] = sum(1 for x in pn if int(x[6] or 0) == 1)
        r['panel_wbm'] = dict(collections.Counter(str(x[5] or '') for x in pn))
        fb = g(em, 'SELECT fb_Disposal, rb_Disposal FROM PaintingBumper')
        r['bumper'] = list(fb) if fb else None
        pt = g(em, 'SELECT WageTotalOutTax, MaterialTotalOutTax, MaterialTotalbyManual, TotalOutTax, TimeTotal FROM PaintingTotal')
        r['ptotal'] = dict(zip(('wage', 'material', 'mat_manual', 'total', 'time'), pt)) if pt else None
        tt = g(em, 'SELECT SubTotal, Total, pt_ExtraTotalOutTax, pt_ExtraFlag, wg_ExtraTotalOutTax, wg_ExtraFlag, wg_IncludeMaterial, pt_IncludeRecycle FROM Total')
        r['total'] = dict(zip(('subtotal', 'total', 'pt_extra', 'pt_extra_flag', 'wg_extra', 'wg_extra_flag', 'wg_incl_material', 'pt_incl_recycle'), tt)) if tt else None
        r['n_adas'] = g(em, 'SELECT COUNT(*) FROM ReserveERParts')[0]
        r['n_recycle'] = g(em, "SELECT COUNT(*) FROM RCParts")[0] if em.execute("SELECT name FROM sqlite_master WHERE name='RCParts'").fetchone() else 0
        fr = em.execute("SELECT name FROM sqlite_master WHERE name='FrameParts'").fetchone()
        r['n_frame'] = g(em, 'SELECT COUNT(*) FROM FrameParts')[0] if fr else None
        ex = list(em.execute('SELECT Name, WageOutTax, PartsPriceOutTax FROM Expense'))
        r['n_expense_used'] = sum(1 for x in ex if (x[1] and int(x[1]) > 0) or (x[2] and int(x[2]) > 0))
    except Exception as e:
        r['error'] = _err(e)
    finally:
        for con in d.values():
            con.close()
    return r



_W = {}


def _init():
    import skill_env; skill_env.apply()
    import roundtrip as rt, estimate_to_neo as e
    from addata_vehicle_resolver import AddataVehicleResolver
    _W['rt'] = rt; _W['e'] = e; _W['nb'] = e.NeoBuilder(); _W['res'] = AddataVehicleResolver()


def _clean_miss(lst):
    """外れの一覧から例外の本文を消す（roundtrip の検査関数は 'ERR ' + 例外文 を入れることがある。パスが入りうるので書き出さない）"""
    out = []
    for m in lst or []:
        if isinstance(m, dict):
            out.append({k: ('ERR' if isinstance(v, str) and v.startswith('ERR') else v) for k, v in m.items()})
        else:
            out.append('error')
    return out


def rt_one(item):
    rid, rel = item
    rt, e, nb, res = _W['rt'], _W['e'], _W['nb'], _W['res']
    path = os.path.join(SRC, rel)
    out = {'id': rid}
    try:
        car, cs, eva, st, rows = rt.load(path)
    except Exception as ex:
        out['error'] = 'load ' + _err(ex); return out
    out['car'] = car.get('CarCode')
    v = rt.vehicle_test(res, car, cs, eva)
    out['vehicle'] = {k: v.get(k) for k in ('ok', 'confidence', 'expected', 'got', 'candidates')}
    out['vehicle']['has_desig'] = bool((v.get('input') or {}).get('desig'))
    try:
        parts = e.AddataParts(nb.engine, car['CarCode'])
    except Exception as ex:
        out['error'] = 'parts ' + _err(ex); return out
    for m in ('a', 'b', 'c'):
        try:
            c, miss = rt.parts_test(parts, rows, m, car.get('YearCode', ''))
            out[f'parts_{m}'] = dict(c); out[f'miss_{m}'] = _clean_miss(miss[:15])
        except Exception as ex:
            out[f'parts_{m}'] = {'error': 1}; out[f'miss_{m}'] = [_err(ex)]
    try:
        c, miss = rt.std_test(parts, rows, car, eva); out['std'] = dict(c); out['miss_std'] = _clean_miss(miss[:20])
    except Exception as ex:
        out['std'] = {'error': 1}; out['miss_std'] = [_err(ex)]
    try:
        c, miss = rt.paint_test(path, car, os.environ.get('ADDATA_ROOT') or r'C:\Addata'); out['paint'] = dict(c); out['miss_paint'] = _clean_miss(miss[:15])
    except Exception as ex:
        out['paint'] = {'error': 1}; out['miss_paint'] = [_err(ex)]
    return out



def inventory():
    os.makedirs(OUT, exist_ok=True)
    paths = sorted(os.path.join(r, f) for r, _d, fs in os.walk(SRC) for f in fs if f.lower().endswith('.neo'))
    print('NEO', len(paths), flush=True)
    t0 = time.time(); n = 0
    with open(os.path.join(OUT, 'inventory.jsonl'), 'w', encoding='utf-8') as fh, ProcessPoolExecutor(max_workers=6) as pool:
        for r in pool.map(one, paths, chunksize=8):
            fh.write(json.dumps(r, ensure_ascii=False) + '\n'); n += 1
            if n % 500 == 0:
                print(f'{n}/{len(paths)} {time.time() - t0:.0f}s', flush=True)
    print('done', n, f'{time.time() - t0:.0f}s', flush=True)


def roundtrip(month='080801', n=700):
    inv_ = [json.loads(l) for l in open(os.path.join(OUT, 'inventory.jsonl'), encoding='utf-8')]
    idmap = {_id(os.path.relpath(os.path.join(r, f), SRC)): os.path.relpath(os.path.join(r, f), SRC)
             for r, _d, fs in os.walk(SRC) for f in fs if f.lower().endswith('.neo')}  # id → パスはファイルに残さない（Codex 指摘）
    cand = [r['id'] for r in inv_ if 'error' not in r and r.get('price_date') == month and not str(r.get('car') or '').startswith('Z') and r.get('n_rows', 0) >= 3 and r['id'] in idmap]
    random.seed(20260912); random.shuffle(cand); cand = [(i, idmap[i]) for i in sorted(cand[:n])]
    print('対象', len(cand), '本（ADDATA 月', month, '）', flush=True)
    t0 = time.time(); res = []
    with ProcessPoolExecutor(max_workers=5, initializer=_init) as pool:
        for r in pool.map(rt_one, cand, chunksize=2):
            res.append(r)
    json.dump(res, open(os.path.join(OUT, f'roundtrip_{month}.json'), 'w', encoding='utf-8'), ensure_ascii=False, indent=0)
    T = collections.Counter()
    for r in res:
        if 'error' in r:
            T['error'] += 1; continue
        T['veh_all'] += 1; T['veh_ok'] += bool(r['vehicle'].get('ok'))
        for m in ('a', 'b', 'c'):
            p = r.get(f'parts_{m}') or {}
            T[f'{m}_ok'] += p.get('ok', 0); T[f'{m}_all'] += p.get('ok', 0) + p.get('wrong', 0) + p.get('none', 0)
        s = r.get('std') or {}; T['std_ok'] += s.get('ok', 0); T['std_all'] += s.get('ok', 0) + s.get('wrong', 0) + s.get('none', 0)
        p = r.get('paint') or {}; T['paint_ok'] += p.get('ok', 0); T['paint_all'] += p.get('ok', 0) + p.get('ng', 0)
        T['base_ok'] += p.get('base_ok', 0); T['base_all'] += p.get('base_ok', 0) + p.get('base_ng', 0)

    def pct(a, b):
        return f'{T[a]}/{T[b]} ({100.0 * T[a] / T[b]:.1f}%)' if T[b] else '-'
    print(f'done {time.time() - t0:.0f}s 車両 {pct("veh_ok", "veh_all")} / 部品(品番+名称+価格) {pct("a_ok", "a_all")} / (名称+価格) {pct("b_ok", "b_all")} / '
          f'(名称のみ) {pct("c_ok", "c_all")} / 標準指数 {pct("std_ok", "std_all")} / 塗装パネル {pct("paint_ok", "paint_all")} / 加算基礎 {pct("base_ok", "base_all")}', flush=True)


if __name__ == '__main__':
    cmd = sys.argv[1] if len(sys.argv) > 1 else ''
    if cmd == 'inventory':
        inventory()
    elif cmd == 'roundtrip':
        roundtrip(sys.argv[2] if len(sys.argv) > 2 else '080801', int(sys.argv[3]) if len(sys.argv) > 3 else 700)
    else:
        print(__doc__)
