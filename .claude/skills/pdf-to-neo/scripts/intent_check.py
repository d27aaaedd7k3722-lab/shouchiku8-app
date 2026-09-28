# -*- coding: utf-8 -*-
"""intent_check.py — できあがった NEO を読み戻し、estimate.json（下書きが決めた「こう作るつもり」）と 1 行ずつ突き合わせる。

検算（run_case）は合計を見るが、合計が合っていても行の中身が意図と違うことがある
（2026-09-13 ベンツ: 手入力の作業名 13 行が名称欄 24 バイトで途中まで、英字の品名 'SPL. S' の S が 'ｽ' に化けていた。
 ランクル: 顧客名が 30 バイトの欄で「…株式」まで）。これを NEO の中身そのもので確かめる。

  hard（不合格にする）: 行数・部品コード・数量・金額・工賃・明細コメントの有無が意図と違う
  soft（確認箇所シートの 要確認）: 名称・コメント・顧客名・工場名・車名が欄の長さで切れた、表記が変わった

make_neo.py が生成の後に呼ぶ。単独でも `python intent_check.py <estimate.json> <neo>`。
"""
from __future__ import annotations

import json
import os
import sqlite3
import sys
import tempfile

HERE = os.path.dirname(os.path.realpath(__file__))
sys.path.insert(0, HERE)
import skill_env  # noqa: E402
skill_env.apply()
sys.path.insert(0, os.path.join(skill_env.FILES, 'claude_neo_pipeline'))
import neo_container as nc  # noqa: E402
from skill_env import flag  # noqa: E402
from estimate_to_neo import _code4, _fit, hw  # noqa: E402


def _open(neo_path: str) -> tuple[sqlite3.Connection, sqlite3.Connection, list]:
    data = open(neo_path, 'rb').read()
    ck = nc.find_real_cks(data)
    dec = nc.decompress_neo(data, ck)
    _m, entries = nc.parse_entries(data, ck[0])
    files = nc.extract_files(dec, entries)
    cons, tmps = [], []
    for k in ('AnSvEm0001.sld', 'AnSvIf0001.sld'):
        t = tempfile.NamedTemporaryFile(delete=False, suffix='.sld')
        t.write(files[k]); t.close(); tmps.append(t.name)
        c = sqlite3.connect(t.name); c.row_factory = sqlite3.Row
        cons.append(c)
    return cons[0], cons[1], tmps


def _e(level: str, kind: str, text: str, row='', name='', code='', page='') -> dict:
    return {'level': level, 'kind': kind, 'page': page, 'row': row, 'name': name, 'code': code, 'text': text}


def _int(v, default=None):
    """NEO の数値欄を int に（読めなければ default）"""
    try:
        return int(v)
    except (TypeError, ValueError):
        return default


class _Unreadable(ValueError):
    pass


def _amount(v):
    """estimate.json の金額・数量欄を int に。生成器と同じく '1,000' '¥1000' '1000円' 全角数字も読む。
    空・None は None（意図なし）。読めない値は _Unreadable（黙って比較を飛ばさない。Codex 指摘）"""
    if v is None or (isinstance(v, str) and not v.strip()):
        return None
    if isinstance(v, bool):
        raise _Unreadable(repr(v))
    if isinstance(v, float) and not v.is_integer():  # 生成器の _money と同じく円未満・指数表記は写し間違い（切り捨てて一致に見せない。Codex 指摘）
        raise _Unreadable(repr(v))
    if isinstance(v, (int, float)):
        return int(v)
    import re
    import unicodedata
    t = unicodedata.normalize('NFKC', str(v)).replace(',', '').replace('¥', '').replace('円', '').strip()
    if not re.fullmatch(r'[+-]?\d+(\.0*)?', t):
        raise _Unreadable(repr(v))
    return int(float(t))


def _code(v) -> str:
    """部品コードを生成器と同じ 4 桁にそろえる（10 / '10' / 10.0 → '0010'。Codex 指摘）。読めない値は _Unreadable"""
    try:
        return _code4(v)
    except ValueError as ex:
        raise _Unreadable(f'{v!r}（{ex}）') from None


def check(est: dict, neo_path: str) -> dict:
    """戻り値 {'hard': [...], 'soft': [...], 'rows': 突き合わせた行数}。各要素は確認箇所シートと同じ形の dict"""
    hard: list = []
    soft: list = []
    em, iff, tmps = _open(neo_path)
    try:
        rows = [dict(r) for r in em.execute('SELECT * FROM ERParts ORDER BY RecordNo')]
        items = list(est.get('items') or [])
        # リサイクル部品に置き換えた行は、生成器が明細の末尾へ動かす（品番欄 'リサイクル部品'）。それ以外の行は元の並びのまま残るので、
        # リサイクルでない行どうしを並び順で突き合わせ、リサイクルの行は件数だけ見る（Codex 指摘: 全部を飛ばすと関門が効かない）
        it_rc = [it for it in items if it.get('recycle')]
        it_n = [it for it in items if not it.get('recycle')]
        rw_rc = [r for r in rows if str(r.get('PartsNo') or '').strip() == 'リサイクル部品']
        rw_n = [r for r in rows if str(r.get('PartsNo') or '').strip() != 'リサイクル部品']
        if len(rows) != len(items) or len(rw_rc) != len(it_rc):
            hard.append(_e('要確認', '意図との突き合わせ', f'NEO の明細 {len(rows)} 行（うちリサイクル {len(rw_rc)}）/ 下書き {len(items)} 行（うちリサイクル {len(it_rc)}）。行が増えたか減った'))
            rows_cmp = []
        else:
            rows_cmp = list(zip(it_n, rw_n))
            links = [dict(x) for x in em.execute('SELECT * FROM RCLinkParts ORDER BY RecordNo')] if _has(em, 'RCLinkParts') else []
            for k_rc, (it, r) in enumerate(zip(it_rc, rw_rc)):  # リサイクルの行: 部品コード・数量 1・置き換え後の金額と名称（生成器は名称を 20 バイトに詰める）・元の行の退避
                rc = it.get('recycle') or {}
                rec = _int(r.get('RecordNo'))
                nm_rc = str(it.get('name') or '')
                try:
                    code_w = _code(it.get('code'))
                except _Unreadable as ex:
                    hard.append(_e('要確認', '意図との食い違い', f'リサイクルにした元の部品の部品コードが読めない: {ex}', rec, nm_rc, '', it.get('_page', '')))
                    code_w = ''
                if code_w and str(r.get('PartsCode') or '').strip() != code_w:
                    hard.append(_e('要確認', '意図との食い違い', f"リサイクル部品の部品コード: 意図 {code_w!r} / NEO {str(r.get('PartsCode') or '').strip()!r}", rec, nm_rc, '', it.get('_page', '')))
                if _int(r.get('PartsCount')) != 1:
                    hard.append(_e('要確認', '意図との食い違い', f"リサイクル部品の数量: NEO {r.get('PartsCount')!r}（リサイクル部品は 1）", rec, nm_rc, '', it.get('_page', '')))
                lk = links[k_rc] if k_rc < len(links) else {}
                try:
                    p_orig = _amount(it.get('parts_price') if it.get('parts_price') is not None else it.get('price'))
                except _Unreadable as ex:
                    hard.append(_e('要確認', '意図との食い違い', f'リサイクルにした元の部品の金額が読めない: {ex}', rec, str(it.get('name') or ''), '', it.get('_page', '')))
                    p_orig = None
                if not lk:
                    hard.append(_e('要確認', '意図との食い違い', '元の部品の行が RCLinkParts に退避されていない', rec, nm_rc, '', it.get('_page', '')))
                elif (code_w and str(lk.get('PartsCode') or '').strip() != code_w) or (p_orig is not None and _int(lk.get('PartsPriceOutTax')) != p_orig):
                    hard.append(_e('要確認', '意図との食い違い', f"退避した元の部品: 意図 {code_w} / {p_orig} 円 / NEO {str(lk.get('PartsCode') or '').strip()} / {lk.get('PartsPriceOutTax')} 円", rec, nm_rc, '', it.get('_page', '')))
                if it.get('comment'):
                    soft.append(_e('要確認', 'コメントが消えた', f"リサイクル部品に置き換えると明細コメント「{it['comment']}」は消える（コグニのリサイクル部品登録と同じ）", rec, nm_rc, '', it.get('_page', '')))
                try:
                    p_want = _amount(rc.get('price')) if isinstance(rc, dict) else None
                except _Unreadable as ex:
                    hard.append(_e('要確認', '意図との食い違い', f'リサイクル部品の金額が読めない: {ex}', rec, str(it.get('name') or ''), '', it.get('_page', '')))
                    p_want = None
                p_got = _int(r.get('PartsPriceOutTax'))
                if p_want is not None and p_got != p_want:
                    hard.append(_e('要確認', '意図との食い違い', f'リサイクル部品の金額: 意図 {p_want!r} / NEO {p_got!r}', rec, str(it.get('name') or ''), '', it.get('_page', '')))
                n_want = _fit(hw(str((rc.get('name') if isinstance(rc, dict) else '') or '')).strip(), 20).strip()  # 生成器と同じ半角カナ（判断規則 10-22b）
                n_got = str(r.get('PartsName') or '').strip()
                if n_want and n_got != n_want:
                    soft.append(_e('要確認', '名称が変わった', f'リサイクル部品の名称: 意図「{n_want}」/ NEO「{n_got}」', rec, str(it.get('name') or ''), '', it.get('_page', '')))
        generic = flag((est.get('vehicle') or {}).get('generic'), 'vehicle.generic')  # 汎用車種は全行が手入力（名称がそのまま NEO に出る）
        for i, (it, r) in enumerate(rows_cmp, start=1):
            rec = _int(r.get('RecordNo'), i)
            page = it.get('_page', '')
            nm = str(it.get('name') or '')
            try:
                code_want = _code(it.get('code'))
            except _Unreadable as ex:
                hard.append(_e('要確認', '意図との食い違い', f'部品コードが読めない: {ex}', rec, nm, '', page))
                code_want = ''
            code_got = str(r.get('PartsCode') or '').strip()
            manual = flag(it.get('manual'), 'items[].manual')  # 部品コードの無い行でも manual でなければ、生成器が名称・品番で照合して部品コードを付ける。文字列 "false" を真にしない（Codex 指摘）

            def bad(what, want, got):
                hard.append(_e('要確認', '意図との食い違い', f'{what}: 意図 {want!r} / NEO {got!r}', rec, nm, code_got, page))
            if manual and code_got:
                bad('部品コード（手入力のつもり）', '', code_got)
            elif code_want and code_got != code_want:
                bad('部品コード', code_want, code_got)
            try:
                price_want = _amount(it.get('parts_price') if it.get('parts_price') is not None else it.get('price'))  # 生成器と同じく parts_price を優先（Codex 指摘）
                qty_want = _amount(it.get('qty'))
                qty_want = 1 if qty_want is None else qty_want
                wage_want = _amount(it.get('wage'))
            except _Unreadable as ex:
                bad('金額・数量が読めない', str(ex), '')
                continue
            reserve = flag(it.get('reserve'), 'items[].reserve')
            if reserve != bool(_int(r.get('ReserveFlag'), 0)):  # 保留（見積書の「保留」行）の印が落ちた/付いた（合計には含めない行なので検算では見つからない。Codex 指摘）
                bad('保留の印', reserve, _int(r.get('ReserveFlag'), 0))
            qty_got = _int(r.get('PartsCount'))
            if qty_got != qty_want and not (qty_got == -1 and not price_want):  # 部品代の無い手入力行・作業行はコグニも数量 -1
                bad('数量', qty_want, qty_got)
            if price_want is not None and not reserve:
                p_got = _int(r.get('PartsPriceOutTax'))
                if p_got != price_want and not (price_want == 0 and p_got in (0, -1)):
                    bad('部品金額', price_want, p_got)
            if wage_want is not None and not reserve:  # 工賃 0 を意図した行（付属部品）も見る。NEO は 0 か -1（工賃なし）
                w_got = _int(r.get('WageOutTax'))
                if (w_got != wage_want) and not (wage_want == 0 and w_got in (0, -1)):
                    bad('工賃', wage_want, w_got)
            c_want = str(it.get('comment') or '')
            c_got = str(r.get('Comment1') or '').strip()
            if bool(c_want) != bool(_int(r.get('CommentFlag'), 0)):
                bad('明細コメントの有無', c_want, c_got)
            elif c_want and c_got != c_want.strip():
                soft.append(_e('要確認', '欄で切れた', f'明細コメント「{c_want}」が NEO では「{c_got}」（40 バイトの欄）', rec, nm, code_got, page))
            if manual or generic or it.get('neo_name'):  # 手入力行（汎用車種は全行）と、見積書の名称を指定した行（neo_name）は その名称が NEO に出るはず
                want_nm = hw(str(it.get('neo_name') or nm)).strip()
                got_nm = str(r.get('PartsName') or '').strip()
                if got_nm != want_nm:
                    soft.append(_e('要確認', '欄で切れた' if want_nm.startswith(got_nm) else '名称が変わった',
                                   f'名称: 意図「{want_nm}」/ NEO「{got_nm}」', rec, nm, '', page))
        # 費用（Expense）: 見積書に刷られる費用名は「載せた行の Name」。既定行に寄せると名前がコグニの文言に化けるので、
        # 名前と金額の両方を突き合わせる（2026-09-28 シエンタ: '配線修理' が '配線・配管費用' になっていた）
        if _has(em, 'Expense'):
            ex_rows = [dict(r) for r in em.execute('SELECT LineNo, Name, PartsEnabled, PartsPriceOutTax, WageEnabled, WageOutTax FROM Expense')]
            for ex in (est.get('expenses') or []):
                amt = _amount(ex.get('amount'))
                if not amt:
                    continue
                side = 'parts' if ex.get('kind') == 'parts' else 'wage'
                want = hw(str(ex.get('name') or '')).strip()
                hit = [r for r in ex_rows
                       if (_int(r.get('PartsPriceOutTax')) == amt if side == 'parts' else _int(r.get('WageOutTax')) == amt)
                       and (r.get('PartsEnabled') if side == 'parts' else r.get('WageEnabled'))]
                if not hit:
                    hard.append(_e('要確認', '意図との食い違い', f'費用「{want}」{amt:,} 円（{"部品側" if side == "parts" else "工賃側"}）が NEO の費用欄に無い'))
                    continue
                def _ok_name(got: str) -> bool:
                    # 生成器は「行の名前が費用名で始まる」ときだけ既定行・雛形行に寄せる（'写真代' → 行 7 '写真代他'）。
                    # その向きは意図どおりなので差にしない。逆向き（別の名前に化けた）は要確認
                    import unicodedata as _u
                    a_ = _u.normalize('NFKC', hw(got or '')).strip().replace(' ', '')
                    b_ = _u.normalize('NFKC', want).replace(' ', '')
                    return a_ == b_ or a_.startswith(b_)
                if want and not any(_ok_name(str(r.get('Name') or '')) for r in hit):
                    got = ' / '.join(sorted({str(r.get('Name') or '').strip() for r in hit}))
                    soft.append(_e('要確認', '費用名が変わった', f'費用名: 意図「{want}」/ NEO「{got}」（見積書に刷られるのは NEO の名前）'))
        # 内板骨格（Frame）: 行が落ちると明細が 1 行足りない見積書になる（金額に出ない。基本内の行は工賃を持たない）
        if _has(em, 'Frame'):
            fr_items = [x for x in ((est.get('frame') or {}).get('items') or [])]
            fr_rows = [dict(r) for r in em.execute('SELECT PartsCode, DamageRank, WageOutTax FROM Frame')]
            if len(fr_rows) != len(fr_items):
                hard.append(_e('要確認', '意図との食い違い', f'内板骨格の行: 意図 {len(fr_items)} 行 / NEO {len(fr_rows)} 行'))
            else:
                got_codes = {str(r.get('PartsCode') or '').strip() for r in fr_rows}
                want_codes = {str(x.get('code') or '').strip() for x in fr_items}
                if got_codes != want_codes:
                    hard.append(_e('要確認', '意図との食い違い', f'内板骨格の部位コード: 意図 {sorted(want_codes)} / NEO {sorted(got_codes)}'))
                for x in fr_items:
                    if str(x.get('rank', '')).strip() in ('基本内', '基本'):
                        r = next((r for r in fr_rows if str(r.get('PartsCode') or '').strip() == str(x.get('code') or '').strip()), None)
                        if r and (_int(r.get('DamageRank')) != 1 or _int(r.get('WageOutTax')) not in (-1, 0)):
                            hard.append(_e('要確認', '意図との食い違い', f"内板骨格 {x.get('code')}「基本内」が NEO でランク {r.get('DamageRank')} / 工賃 {r.get('WageOutTax')}"))
        cust = est.get('customer') or {}
        ins = est.get('insurance') or {}
        c_row = dict(iff.execute('SELECT * FROM Customer').fetchone() or {}) if _has(iff, 'Customer') else {}
        i_row = dict(iff.execute('SELECT * FROM Insurance').fetchone() or {}) if _has(iff, 'Insurance') else {}
        for label, want, got in (('顧客名', cust.get('name'), c_row.get('Name1')), ('工場（協定先）', ins.get('factory'), i_row.get('ConsultantFactory')),
                                 ('契約者', ins.get('contractor'), i_row.get('ContractorName'))):
            if want and str(got or '').strip() != str(want).strip():
                soft.append(_e('要確認', '欄で切れた', f'{label}: 意図「{want}」/ NEO「{str(got or "").strip()}」'))
        veh = est.get('vehicle') or {}
        if flag(veh.get('generic'), 'vehicle.generic') and veh.get('car_name'):  # 生成器と同じ読み方（'yes' 等も真。Codex 指摘）
            car = dict(iff.execute('SELECT * FROM Car').fetchone() or {}) if _has(iff, 'Car') else {}
            if str(car.get('CarNameByUser') or '').strip() != str(veh['car_name']).strip():
                soft.append(_e('要確認', '欄で切れた', f"車名: 意図「{veh['car_name']}」/ NEO「{str(car.get('CarNameByUser') or '').strip()}」"))
        return {'hard': hard, 'soft': soft, 'rows': len(rows_cmp)}
    finally:
        em.close(); iff.close()
        for t in tmps:
            try:
                os.unlink(t)
            except OSError:
                pass


def _has(con: sqlite3.Connection, table: str) -> bool:
    return con.execute("select 1 from sqlite_master where type='table' and name=?", (table,)).fetchone() is not None


def main(argv: list) -> int:
    if len(argv) < 2:
        print(__doc__ or '')
        print('使い方: python intent_check.py <estimate.json> <neo>')
        return 2
    est = json.load(open(argv[0], encoding='utf-8-sig'))
    res = check(est, argv[1])
    print(f"意図との突き合わせ: {res['rows']} 行 / 食い違い {len(res['hard'])} / 要確認 {len(res['soft'])}")
    for e in res['hard'] + res['soft']:
        print(f"  [{e['kind']}] 明細 {e['row']} {e['name']} {e['text']}")
    return 1 if res['hard'] else 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
