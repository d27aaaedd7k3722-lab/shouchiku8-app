# -*- coding: utf-8 -*-
"""実機保存 NEO（NEO_check/_eva_exp/cogni_*.neo）と生成器の総当たり再検証（開発用。個人情報を含む NEO_check を参照するので配布 zip には入らない）。
各実験の estimate.json から NEO を作り直し、コグニ保存版と ERParts 全列・Total・Painting* を比較する。
既知の「再検索の副作用」だけを除外し、それ以外の差は BUG 候補として出す。
    cd files && PYTHONIOENCODING=utf-8 python <this> [tag ...]
"""
import io
import json
import os
import re
import sys

B = os.path.dirname(os.path.dirname(os.path.dirname(os.path.realpath(__file__))))  # <repo>/files（別フォルダに置いても自分のコードを見る）
sys.path.insert(0, os.path.join(B, 'claude_neo_pipeline')); sys.path.insert(0, os.path.join(B, 'claude_neo_pipeline', 'tests'))
import neo_diff  # noqa: E402
from estimate_to_neo import NeoBuilder  # noqa: E402

E = os.path.join(os.environ.get('NEO_CHECK_ROOT')  # 実機ファイルの置き場（PC ごとに違う）
                 or os.path.join(os.path.expanduser('~'), 'Documents', 'NEO_check'), '_eva_exp')
VEH = {'model_code': 'JF1', 'serial_no': 'JF1-0000001', 'desig': '17075', 'category': '0061', 'reg_date': 'H28.10', 'color_code': 'YR586P'}
EVA_ITEMS = [{'code': '0400', 'name': 'L ﾍｯﾄﾞﾗｲﾄ', 'method': '取替', 'qty': 1}, {'code': '0402', 'name': 'L ﾍｯﾄﾞﾗｲﾄﾕﾆｯﾄ', 'method': '取替', 'qty': 1},
             {'code': '0408', 'name': 'L ﾍｯﾄﾞﾗｲﾄﾊﾞﾙﾌﾞ', 'method': '取替', 'qty': 1}, {'code': '0140', 'name': 'LFﾌｫｸﾞﾗｲﾄ', 'method': '取替', 'qty': 1},
             {'code': '2700', 'name': 'L ｽﾗｲﾄﾞﾄﾞｱﾊﾟﾈﾙ', 'method': '取替', 'qty': 1}, {'code': '3500', 'name': 'R ｽﾗｲﾄﾞﾄﾞｱﾊﾟﾈﾙ', 'method': '取替', 'qty': 1},
             {'code': '6000', 'name': 'Fｳｲﾝﾄﾞｼｰﾙﾄﾞｶﾞﾗｽ', 'method': '取替', 'qty': 1}]
PAIR_ITEMS = EVA_ITEMS[:3] + EVA_ITEMS[4:6]
BASE_ITEMS = [{'code': '0010', 'name': 'Fﾊﾞﾝﾊﾟﾌｪｲｽ', 'method': '取替', 'qty': 1}, {'code': '0140', 'name': 'LFﾌｫｸﾞﾗｲﾄ', 'method': '取替', 'qty': 1},
              {'code': '0408', 'name': 'L ﾍｯﾄﾞﾗｲﾄﾊﾞﾙﾌﾞ', 'method': '取替', 'qty': 1}, {'code': '0400', 'name': 'L ﾍｯﾄﾞﾗｲﾄ', 'method': '取替', 'qty': 1},
              {'code': '2700', 'name': 'L ｽﾗｲﾄﾞﾄﾞｱﾊﾟﾈﾙ', 'method': '取替', 'qty': 1}, {'code': '2360', 'name': 'LFﾄﾞｱｱｳﾀﾊﾝﾄﾞﾙ', 'method': '取替', 'qty': 1},
              {'code': '4300', 'name': 'ﾃｰﾙｹﾞｰﾄ', 'method': '取替', 'qty': 1}, {'code': '6000', 'name': 'Fｳｲﾝﾄﾞｼｰﾙﾄﾞｶﾞﾗｽ', 'method': '取替', 'qty': 1},
              {'code': '7480', 'name': 'ﾗｼﾞｴｰﾀ', 'method': '取替', 'qty': 1}]


# 実案件の estimate.json（NEO_check の案件フォルダ。顧客姓は匿名コード）を tag で引く
from case_dirs import case_dir  # noqa: E402  案件フォルダ名（損保名を含む）は NEO_check/_cases.json に置く
REAL_CASES = {'R1': case_dir('C05'), 'R2': case_dir('C04')}  # 実案件（オデッセイ・アルファード）をそのまま保存したもの


def est_of(tag: str):
    """tag → (estimate dict, ラベル)。ファイルがあればそれ、無ければ組み立て"""
    if tag in REAL_CASES:
        rp = os.path.join(REAL_CASES[tag], 'estimate.json')
        if os.path.exists(rp):
            return json.load(open(rp, encoding='utf-8-sig')), tag + '/estimate.json'
        return None, ''
    for cand in (f'nbox_{tag}_estimate.json', f'{tag}_estimate.json', f'exp_{tag}_estimate.json', f'frame_{tag}_estimate.json'):
        p = os.path.join(E, cand)
        if os.path.exists(p):
            return json.load(open(p, encoding='utf-8-sig')), cand
    eva = {'none': [], 'T': ['T'], 'U': ['U'], 'TU': ['T', 'U'], 'TUPXV': ['T', 'U', 'P', 'X', 'V'],
           'pair_none': [], 'pair_U': ['U'], 'pair_P': ['P'], 'pair_Q': ['Q']}
    if tag in eva:
        items = PAIR_ITEMS if tag.startswith('pair') else BASE_ITEMS  # 装備実験: base 系 9 行 / pair 系 5 行
        return ({'source': f'audit_{tag}', 'issuer': '', 'est_date': '20260908', 'vehicle': VEH, 'customer': {}, 'insurance': {}, 'labor_rate': 8000,
                 'items': items, 'paint': {}, 'expenses': [], 'totals': {}, 'hints': ({'eva_codes': eva[tag]} if eva[tag] else {})}, 'built-in')
    return None, ''


# 比較しない列。税込・税額は税抜から機械的に決まる（実機も「税抜が -1 の行は税込も -1」で例外なし。
# 実験 67 ファイル 398 行で確認）ので、税抜側を見れば足りる。
# 名称・品番・OrderFlag は 2026-09-10 に比較対象へ戻した（脱着行で左右が消える不具合を見逃していたため）。
# 実機由来の差（固定長の空白詰めなど）は known_side_effect で 1 つずつ理由を付けて許す
SKIP_COLS = {'RecordNo',
             'PartsPriceStandardInTax', 'PartsPriceStandardTax', 'ChangeTotalInTax', 'ChangeTotalTax',
             'WageInTax', 'WageTax', 'WageStandardInTax', 'WageStandardTax', 'PartsPriceInTax', 'PartsPriceTax',
             'PartsUnitPriceInTax', 'PartsUnitPriceTax'}
NAME_COLS = ('PartsName', 'PartsNameStandard', 'PartsNo', 'PartsNoStandard', 'DisposalName', 'DisposalNameStandard')

# 生成 NEO をコグニで開いて「そのまま保存」した実験（再検索・画面編集を通していない）。
# ここは ERParts だけでなく全テーブル・AnSMB.txt・AnSvEm0001Ex.db・AnNote.ini まで完全一致であるべき。
STRAIGHT_SAVE = ('M1', 'M2', 'M3', 'CW66', 'CD98', 'CL10', 'CS64', 'CJ52',
                 'CX1', 'CX2', 'CX3', 'CX4', 'CX5', 'CX6', 'CX7', 'CX8', 'CX9', 'CXA', 'CXB', 'CXC', 'CXD', 'CXE', 'CXF',
                 'R1', 'R2')  # R1/R2 = 実案件（オデッセイ・アルファード）をそのまま保存したもの
EXTRA_FILES = ('AnSMB.txt', 'AnSvEm0001Ex.db', 'AnNote.ini')


KNOWN_DIFF = {  # 実機側の操作で入力と構造が変わった実験（生成器の退行ではない）: タグ → (説明, 期待する差の件数)
    'H24': ('同じ部品コード 2971 の 2 行目をコグニが捨て、数量・単価・加算基礎を画面で直した実験。'
            '加算基礎の工賃印は 見積 3.1 ≠ 標準 3.0 なので生成器は * を書くが、画面で直した保存版は 空（2026-09-12 に BaseWageByManual を比較対象へ戻した）',
            'KNOWN_H24'),  # 期待する差分そのもの（tests/known_diff_H24.txt）と 1 行ずつ照合する
    'W90': ('人が W90 ハイエース（ボディ 20）を最初から手入力: 2700 取替（品番ダイアログ 4 候補）・4800 取替・4801 パネル追加・装備未選択。'
            '残る差は 明細画面から入れた行の OrderFlag（0 / 複数候補は *）と品番末尾 *、SortNo、pt_ExtraFlag、車名末尾の全角空白（記録 .claude/skills/pdf-to-neo/reference/experiments/2026-09-12_W90_実機手入力.md）',
            'KNOWN_W90'),  # 期待する差分そのもの（tests/known_diff_W90.txt）と 1 行ずつ照合する
    'W90b': ('W90 に 4600 Rrﾌﾛｱｱｳﾀｸﾛｽﾒﾝﾊﾞ 取替 を足した版。実機は 4800 が居ると 4600 の指数が 4.0 → 11.7（+7.7h の連動加算。ChangeTotal は 4.0 のまま。4800 の ChangeTotal 985,800 = ボディ 20 行 9.7h は 2026-09-12 に再現）。'
             '生成器はこの連動を再現できていない（未解決 2026-09-12）。W90 と同じ状態依存の差も含む',
             'KNOWN_W90b'),
    'W66x': ('人が W66 シエンタに 4802 修理(2) だけ（工賃未入力）を入れて塗装ページを開き保存: 塗装パネルは 1/2 で自動連動。'
             '残る差は 明細画面から入れた行の OrderFlag 0 と SortNo（記録 reference/experiments/2026-09-12_W90_実機手入力.md の W66 節）',
             'KNOWN_W66x'),
    'W66y': ('W66x に 0600/2300/5800/4600 の修理(2) を足した版（5 枚とも 1/2 で連動、指数は連動減算）。'
             '残る差は OrderFlag 0・SortNo・float の足し算の癖・ルーフ 287 の下処理面積（近似式 50 / 実機 48。W66 のルーフだけ合わない、未解決）',
             'KNOWN_W66y'),
    'W66z': ('W66y に 2602 L ロッカパネルアウタ 修理(2) を足した版: CHM に 1/2・1/3 列の無いパネルは 1/1 固定（指数 1.3、下処理面積 9）。'
             '実機は後から足した 2602 を塗装パネルの末尾に置く（LineNo/SortNo は操作順）ので並びの差が出る。ほかは OrderFlag 0・float の癖・ルーフの下処理面積',
             'KNOWN_W66z'),
    'H11': ('板金行の加算基礎に 0 を明示入力した実験（品番欄に「付加 0.00」が残る。加算が無ければ書かないのが実機の既定で、他 19 件はそちら）', 'KNOWN_H11'),
}


def known_diff_lines(tag: str) -> list:
    """既知差の期待メッセージ（tests/known_diff_<tag>.txt）。無ければ空 = 必ず失敗させる"""
    p = os.path.join(os.path.dirname(os.path.realpath(__file__)), f'known_diff_{tag}.txt')
    if not os.path.exists(p):
        return []
    return sorted(l.rstrip(chr(10)) for l in io.open(p, encoding='utf-8') if l.strip())


def _same_float(gen, cog) -> bool:
    """実機の指数は 0.1 を足し込むので 0.30000000000000004 のような尾を持つ。印字も入力も同じ値なので一致とみなす——小数同士で 1e-9 未満の差だけ）"""
    if isinstance(gen, float) and isinstance(cog, float):
        return abs(gen - cog) < 1e-9
    return False


# 実機の操作履歴で付いたり消えたりする語尾。ここに挙げたものだけ差を許す。
# 「(修理)」「(片側)」などは 12.DB の作業項目そのものの名前なので、消えたら退行として落とす
PAREN_OK = ('(ﾄｿｳｽﾞﾐ)',)


def _same_but_paren(a: str, b: str) -> bool:
    """末尾が PAREN_OK の語尾だけ違うか（'ﾊﾞﾝﾊﾟﾌｴｲｽ' と 'ﾊﾞﾝﾊﾟﾌｴｲｽ(ﾄｿｳｽﾞﾐ)'）。
    前置き（左右・前後）が違うものや、ほかの括弧書きが消えたものは別物として弾く"""
    x, y = a.rstrip(), b.rstrip()
    if not x or not y:
        return False
    return any(x == y + suf or y == x + suf for suf in PAREN_OK)


def ws_origin(cog_rows: list) -> bool:
    """工場から届いた NEO（W/S 経路）をコグニで開いて保存したファイルか。
    元データの固定長（名称・品番の右空白詰め）が残っているかで見分ける。
    コグニで新規作成した見積は詰めが無いので、そちらでは名称・品番を厳密に比べる"""
    return any(isinstance(r.get(c), str) and r[c] != r[c].rstrip()
               for r in cog_rows for c in ('PartsNameStandard', 'PartsNo', 'PartsNoStandard'))


def known_side_effect(dc: int, col: str, gen, cog, ws: bool = False, cog_row: dict = None) -> bool:
    """再検索の副作用（生成器は W/S 経路の工場 NEO を正とする）。
    ws=True は工場 NEO 由来のファイル。由来差の許可はそのファイルだけに限る"""
    if dc in (1, 2, 3, 6) and col in ('PartsPriceStandardOutTax', 'PartsCount', 'ChangeTotalOutTax'):
        return True
    if col in ('WageFileTime', 'PartsFileTime') and str(cog) == '0' and str(gen) != '0':
        return True  # 再検索は WageFileTime / PartsFileTime を '0' にする
    if col == 'PartsPriceFlag' and dc in (2, 6) and cog == 1:
        return True  # 再検索は板金/修理の '#' 行に価格フラグを立てる
    if dc == 4 and col in ('DisposalName', 'DisposalNameStandard', 'BlockCode', 'PartsCount', 'WorkCode'):
        return True
    g, c = (gen if isinstance(gen, str) else ''), (cog if isinstance(cog, str) else '')
    star = str((cog_row or {}).get('PartsNo') or '').rstrip().endswith('*')  # 品番候補が複数ある部品の印
    if col in NAME_COLS and isinstance(gen, str) and isinstance(cog, str):
        if ws and g.rstrip() == c.rstrip():
            return True  # 工場 NEO 由来のファイルは元データの固定長（右空白詰め）が残る
        if col == 'PartsNo' and star and c.rstrip().rstrip('*').strip() == g.strip():
            return True  # 実機はその印を品番欄に足す（条件は未特定。ADDATA の暫定フラグとは無関係）
        if ws and col == 'PartsNoStandard' and dc != 0 and not c.strip():
            return True  # コグニは取替以外の行に標準品番を持たない（工場 NEO 由来の estimate は品番を持つので差が出る）
        if col in ('PartsName', 'PartsNameStandard') and _same_but_paren(g, c):
            return True  # 名称はコグニが部品を入れた時点の修理方法で決まり、後で変えても残る
            # （同じ 0010 の修理行でも cogni_M1/R1 は取替名 'ﾊﾞﾝﾊﾟﾌｴｲｽ(ﾄｿｳｽﾞﾐ)'、cogni_H6/H11 は脱着名 'ﾊﾞﾝﾊﾟﾌｴｲｽ'）
    if col == 'OrderFlag' and str(gen) == '':
        if ws and str(cog) == '0':
            return True  # 工場 NEO 由来のファイルは元データの '0' が残る
        if star and str(cog) == '1':
            return True  # 品番欄に '*' が付いた行と対で立つ
    return False


def load(path):
    d = neo_diff.load(path); em = d['AnSvEm0001.sld']; ifc = d['AnSvIf0001.sld']
    cols = [c[1] for c in em.execute('pragma table_info(ERParts)')]
    rows = [dict(zip(cols, r)) for r in em.execute('select * from ERParts order by RecordNo')]
    tabs = {}
    for t in ('Total', 'PaintingPlan', 'PaintingTotal', 'PaintingPanel'):
        try:
            tc = [c[1] for c in em.execute(f'pragma table_info({t})')]
            tabs[t] = [dict(zip(tc, r)) for r in em.execute(f'select * from {t}')]
        except Exception:
            tabs[t] = []
    st = [c[1] for c in ifc.execute('pragma table_info(Setting)')]
    tabs['Setting'] = [dict(zip(st, ifc.execute('select * from Setting').fetchone()))]
    return rows, tabs


def main() -> int:
    args = [a for a in sys.argv[1:] if not a.startswith('-')]  # --full などのフラグはタグではない
    tags = args or [f[len('cogni_'):-len('.neo')] for f in sorted(os.listdir(E)) if f.startswith('cogni_') and f.endswith('.neo')]
    nb = NeoBuilder()
    bad = 0
    for tag in tags:
        cog_p = os.path.join(E, f'cogni_{tag}.neo')
        if not os.path.exists(cog_p):
            print(f'-- {tag}: cogni NEO なし'); continue
        est, label = est_of(tag)
        if est is None:
            print(f'-- {tag}: estimate 不明（スキップ）'); continue
        try:
            neo, rep = nb.build(est, est['vehicle'], hints=est.get('hints'), labor_rate=est.get('labor_rate') or 8000,
                                est_date=est.get('est_date') or '20260908', insurance={})
        except Exception as e:  # noqa: BLE001
            print(f'** {tag}: 生成失敗 {e}'); bad += 1; continue
        tmp = os.path.join(os.environ.get('TEMP', '.'), f'audit_{tag}.neo')
        open(tmp, 'wb').write(neo)
        g_rows, g_tabs = load(tmp); c_rows, c_tabs = load(cog_p)
        ws = ws_origin(c_rows)   # 工場 NEO 由来のファイルだけ、元データの固定長・OrderFlag の差を許す
        msgs = []
        if len(g_rows) != len(c_rows):
            msgs.append(f'行数 {len(g_rows)} vs {len(c_rows)}')
        gt, ct = g_tabs['Total'][0], c_tabs['Total'][0]
        mat_reset0 = (g_tabs['PaintingPlan'] and c_tabs['PaintingPlan'] and g_tabs['PaintingPlan'][0].get('MaterialRate') != c_tabs['PaintingPlan'][0].get('MaterialRate'))
        if gt.get('Total') != ct.get('Total') and not mat_reset0:
            msgs.append(f"合計 {gt.get('Total')} vs {ct.get('Total')}")
        gi: dict = {}
        for r in sorted(g_rows, key=lambda x: int(x.get('LineNo') or 0)):
            gi.setdefault((r['PartsCode'], int(r.get('DisposalCode') or 0)), []).append(r)
        for c in sorted(c_rows, key=lambda x: int(x.get('LineNo') or 0)):
            dc = int(c.get('DisposalCode') or 0)
            _q = gi.get((c['PartsCode'], dc)) or []
            g = _q.pop(0) if _q else None
            if g is None:
                msgs.append(f"行なし {c['PartsCode']} d{dc}"); continue
            for col in c:
                if col in SKIP_COLS or g.get(col) == c.get(col) or _same_float(g.get(col), c.get(col)):
                    continue
                if known_side_effect(dc, col, g.get(col), c.get(col), ws=ws, cog_row=c):
                    continue
                msgs.append(f"{c['PartsCode']} d{dc} {col}: {g.get(col)!r} vs {c.get(col)!r}")
        for (_c, _d), _left in gi.items():  # 実機に無い行を生成側が作っている（対応づけで余った分）
            for _r in _left:
                msgs.append(f'実機に無い行 {_c} d{_d} LineNo {_r.get("LineNo")}')
        for t in ('PaintingPlan', 'PaintingTotal', 'Setting'):
            if g_tabs[t] and c_tabs[t]:
                for col in c_tabs[t][0]:
                    a, b = g_tabs[t][0].get(col), c_tabs[t][0].get(col)
                    mat_reset = (g_tabs['PaintingPlan'] and c_tabs['PaintingPlan'] and g_tabs['PaintingPlan'][0].get('MaterialRate') != c_tabs['PaintingPlan'][0].get('MaterialRate'))  # 再検索は材料代割合を既定に戻す
                    if a != b and not (t == 'PaintingTotal' and 'MaterialTotal' in col and b == -1 and a == 0) and not (t == 'PaintingPlan' and col == 'MaterialRate') and not (t == 'PaintingTotal' and mat_reset and ('Material' in col or col.startswith('Total'))):
                        msgs.append(f'{t}.{col}: {a!r} vs {b!r}')
        gp = {r['PartsCode']: r for r in g_tabs['PaintingPanel']}
        for c in c_tabs['PaintingPanel']:
            g = gp.get(c['PartsCode'])
            if g is None:
                msgs.append(f"塗装パネルなし {c['PartsCode']}"); continue
            for col in c:
                if g.get(col) != c.get(col) and col not in ('RecordNo',):
                    msgs.append(f"PP {c['PartsCode']}.{col}: {g.get(col)!r} vs {c.get(col)!r}")
        if tag in KNOWN_DIFF and sorted(msgs) == known_diff_lines(tag):
            print(f'--  {tag} ({label}) 差 {len(msgs)}（既知の差と完全に一致: {KNOWN_DIFF[tag][0]}）')
        elif tag in KNOWN_DIFF:
            bad += 1
            exp = known_diff_lines(tag)
            print(f'** {tag} ({label}) 差 {len(msgs)} —— 既知の差（{len(exp)} 件）と違うので退行の疑い:')
            for m in (sorted(set(msgs) - set(exp)) if '--full' in sys.argv else sorted(set(msgs) - set(exp))[:8]):
                print('    新しい差', m[:170])
            for m in (sorted(set(exp) - set(msgs)) if '--full' in sys.argv else sorted(set(exp) - set(msgs))[:8]):
                print('    消えた差', m[:170])
        elif msgs:
            bad += 1
            print(f'** {tag} ({label}) 差 {len(msgs)}:')
            for m in (msgs if '--full' in sys.argv else msgs[:12]):  # --full: 既知差ファイルを作り直すとき
                print('   ', m[:180])
        else:
            print(f'ok  {tag} ({label}) 全列一致 rows={len(c_rows)} total={ct.get("Total")}')
    print(f'--- 差のある実験 {bad} / {len(tags)}')
    return 1 if bad else 0


if __name__ == '__main__' and '--ansmb' not in sys.argv and '--full-files' not in sys.argv:
    sys.exit(main())


def check_ansmb(tag: str = 'M1') -> int:
    """AnSMB.txt が実機保存版と 142 桁一致するか。基準は M1（生成 NEO をコグニで開いてそのまま保存したもの）。
    K1 は明細を編集した後の保存版なので OrderFlag（100 桁）が変わっている
    cd files && python claude_neo_pipeline/tests/audit_cogni_files.py --ansmb"""
    import json as _json
    import neo_container as _nc
    cog_p = os.path.join(E, f'cogni_{tag}.neo')
    est, _label = est_of(tag)
    if est is None or not os.path.exists(cog_p):
        print(f'AnSMB: {tag} の estimate / cogni NEO が無い'); return 0

    def _smb(p):
        raw = open(p, 'rb').read(); ck = _nc.find_real_cks(raw); dec = _nc.decompress_neo(raw, ck)
        mgmt, entries = _nc.parse_entries(raw, ck[0]); files = _nc.extract_files(dec, entries)
        return [l for l in files.get('AnSMB.txt', b'').split(b'\r\n') if l]
    neo, _ = NeoBuilder().build(est, est['vehicle'], hints=est.get('hints'), labor_rate=est.get('labor_rate') or 8000, est_date=est.get('est_date') or '20260908', insurance={})
    tmp = os.path.join(os.environ.get('TEMP', '.'), f'ansmb_{tag}.neo'); open(tmp, 'wb').write(neo)
    g, c = _smb(tmp), _smb(cog_p)
    same = (g == c)
    print(f'AnSMB {tag}: 行 {len(g)}/{len(c)} ' + ('142 桁すべて一致' if same else '差あり'))
    return 0 if same else 1


def check_ansmb_all() -> int:
    """estimate と実機 NEO が揃う実験すべてで AnSMB.txt を突き合わせる（既知差の実験は除く）"""
    import glob
    tags = sorted(f[len('cogni_'):-len('.neo')] for f in os.listdir(E) if f.startswith('cogni_') and f.endswith('.neo'))
    base = STRAIGHT_SAVE  # 生成 NEO を開いてそのまま保存したもの。ここは完全一致であるべき（実案件 R1/R2 を含む）
    ng = ok = other_ng = other_ok = 0
    for t in tags:
        if t in KNOWN_DIFF or est_of(t)[0] is None:
            continue
        r = check_ansmb(t)
        if t in base:
            ng += 1 if r else 0
            ok += 0 if r else 1
        else:
            other_ng += 1 if r else 0
            other_ok += 0 if r else 1
    print(f'--- AnSMB 基準（そのまま保存）一致 {ok} / 差あり {ng}')
    print(f'--- 参考: 再検索・編集を通した保存版 一致 {other_ok} / 差あり {other_ng}'
          '（100 桁の OrderFlag と標準品番が変わるので差が出るのが正常）')
    return 1 if ng else 0


def check_ansmb_base() -> int:
    """生成 NEO をコグニで開いてそのまま保存したファイル（STRAIGHT_SAVE。実案件 R1/R2 を含む）で 142 桁一致を見る。
    2026-09-10 に M1/M2/M3 の 3 本から 25 本へ広げた（印刷用の明細一覧が崩れる退行を捕まえるため）"""
    ng = 0
    for t in STRAIGHT_SAVE:
        cog_p = os.path.join(E, f'cogni_{t}.neo')
        if not os.path.isdir(E):
            # 実機ファイルは個人領域（NEO_check）にあり配布物には入らない。無い PC では検査できないので、
            # 「行わなかった」ことが分かる形で終える（PDF_TO_NEO_REQUIRE_FIXTURES=1 なら失敗にする）
            msg = '** AnSMB: 実機ファイル（NEO_check/_eva_exp）が無いので 142 桁の比較を行っていない **'
            print(msg)
            return 1 if os.environ.get('PDF_TO_NEO_REQUIRE_FIXTURES', '') == '1' else 0
        # estimate は実験ごとに置き場が違う（実験ファイル・実案件フォルダ・組み立て）ので est_of で引く
        if est_of(t)[0] is None or not os.path.exists(cog_p):  # 基準の欠落は失敗（検証ゲートが空回りしないように）
            print(f'** AnSMB の基準 {t} が無い（estimate か cogni_{t}.neo）')
            ng += 1
            continue
        ng += check_ansmb(t)
    return 1 if ng else 0


if __name__ == '__main__' and '--ansmb' in sys.argv:
    sys.exit(check_ansmb_all() if '--all' in sys.argv else check_ansmb_base())

def _full_diff(gen_path: str, cog_path: str) -> list:
    """neo_diff と同じ範囲（両 SQLite の全テーブル + 付随ファイル）を比べ、差分メッセージを返す"""
    A = neo_diff.load(gen_path); B = neo_diff.load(cog_path)
    out = []
    for k in ('AnSvEm0001.sld', 'AnSvIf0001.sld'):
        ca, cb = A[k], B[k]
        ta = [r[0] for r in ca.execute("select name from sqlite_master where type='table'")]
        tb = [r[0] for r in cb.execute("select name from sqlite_master where type='table'")]
        for t in sorted(set(tb) - set(ta)):
            out.append('%s: 実機にある表が生成側に無い (%s)' % (t, k))
        for t in sorted(set(ta) - set(tb)):
            out.append('%s: 生成側にだけある表 (%s)' % (t, k))
        for t in ta:
            if t not in tb:
                continue
            ia = [tuple(c) for c in ca.execute('pragma table_info(%s)' % t)]
            ib = [tuple(c) for c in cb.execute('pragma table_info(%s)' % t)]
            ca_cols = [c[1] for c in ia]; cb_cols = [c[1] for c in ib]
            if ia != ib:  # 列名だけでなく型・NOT NULL・既定値・PK まで見る
                out.append('%s: 列定義が違う %r vs %r' % (t, ia, ib))
            sa = ca.execute("select sql from sqlite_master where type='table' and name=?", (t,)).fetchone()
            sb = cb.execute("select sql from sqlite_master where type='table' and name=?", (t,)).fetchone()
            if (sa and sa[0]) != (sb and sb[0]):
                out.append('%s: CREATE TABLE 文が違う' % t)
            ra = ca.execute('select * from ' + t).fetchall(); rb = cb.execute('select * from ' + t).fetchall()
            if len(ra) != len(rb):
                out.append('%s: 行数 %d vs %d' % (t, len(ra), len(rb)))
            common = [c for c in ca_cols if c in cb_cols]
            for i, (x, y) in enumerate(zip(ra, rb)):
                for kk in common:
                    if x[kk] != y[kk] and not _same_float(x[kk], y[kk]):
                        out.append('%s[%d].%s: %r vs %r' % (t, i, kk, x[kk], y[kk]))
    for fn in EXTRA_FILES:
        fa = A['files'].get(fn, b''); fb = B['files'].get(fn, b'')
        if fa == fb:
            continue
        # 行単位の差を出す前に、まず「バイトが違う」ことを必ず記録する。
        # splitlines() は CRLF/LF の違いや末尾の改行有無を消すので、これが無いと完全一致ゲートが空回りする
        out.append('%s: バイト一致しない (%d B vs %d B)' % (fn, len(fa), len(fb)))
        la = fa.decode('cp932', 'replace').splitlines(); lb = fb.decode('cp932', 'replace').splitlines()
        if len(la) != len(lb):
            out.append('%s: 行数 %d vs %d' % (fn, len(la), len(lb)))
        for i, (x, y) in enumerate(zip(la, lb)):
            if x != y:
                out.append('%s[%d]: %r vs %r' % (fn, i, x, y))
    return out


def check_full() -> int:
    """そのまま保存の実験で、生成 NEO と実機保存版が全テーブル・付随ファイルまで一致するか
        cd files && python claude_neo_pipeline/tests/audit_cogni_files.py --full-files"""
    if not os.path.isdir(E):
        print('** 全ファイル比較: 実機ファイル（NEO_check/_eva_exp）が無いので行っていない **')
        return 1 if os.environ.get('PDF_TO_NEO_REQUIRE_FIXTURES', '') == '1' else 0
    require = os.environ.get('PDF_TO_NEO_REQUIRE_FIXTURES', '') == '1'
    nb = NeoBuilder(); ng = 0; done = 0; missing = []
    for tag in STRAIGHT_SAVE:
        cog_p = os.path.join(E, 'cogni_%s.neo' % tag)
        est, _label = est_of(tag)
        if est is None or not os.path.exists(cog_p):
            # 実機ファイルは個人領域（NEO_check）にあり、一部しか無い PC もある。
            # 揃っている分だけ比べ、欠けを別途報告する（PDF_TO_NEO_REQUIRE_FIXTURES=1 のときだけ失敗）
            missing.append(tag); continue
        neo, _rep = nb.build(est, est['vehicle'], hints=est.get('hints'), labor_rate=est.get('labor_rate') or 8000,
                             est_date=est.get('est_date') or '20260908', insurance=est.get('insurance') or {})
        tmp = os.path.join(os.environ.get('TEMP', '.'), 'full_%s.neo' % tag)
        open(tmp, 'wb').write(neo)
        msgs = _full_diff(tmp, cog_p)
        done += 1
        if msgs:
            ng += 1
            print('** %s: 差 %d' % (tag, len(msgs)))
            for m in msgs[:10]:
                print('   ', m[:180])
    if missing:
        print('** 全ファイル比較: 実機ファイルが無くて比べられなかった: %s' % ', '.join(missing))
    if done == 0:
        print('** 全ファイル比較: 比べられる実機 NEO が 1 本も無いので行っていない **')
        return 1 if require else 0
    print('--- 全ファイル一致（そのまま保存） %d / %d 本' % (done - ng, done)
          + ('（実機ファイルの無い %d 本は未実施）' % len(missing) if missing else ''))
    return 1 if (ng or (missing and require)) else 0


if __name__ == '__main__' and '--full-files' in sys.argv:
    sys.exit(check_full())
