# -*- coding: utf-8 -*-
"""見積の品番（品番が無い行は単価）から、車両の年式・ボディ・グレード・駆動＋エンジン（FVA）と装備（CarEVA）を逆引きする。

本体 DBSEARCH.dll の部品の行選び（11.DB: SearchBuhin 100077A0 = 条件判定 10004BC0・優先順位 10004DA0、
13/83.DB: SearchKA13 / SearchKA83 も同じ条件と順位）を**候補の車両ごとにそのまま回し**、
「本体がこの車で選ぶ行の品番 = 見積に印字された品番」かを 1 行ずつ数える（2026-09-22）。

条件判定（行が車に当てはまるか）
  - 年式群（10001DB0）: 行の群が空欄か、車の群（YearCode の下 1 桁。年式 00 は 0）**以下**
  - ボディ（10001DF0）: 行のボディが 0 か、車の BodyCode・SBaseCode・LBaseCode のどれか
  - グレード（10001E20）: 行の [0:5] が空欄か、車の GradeCode を含む（いずれか一致）
  - 装備（10001E60）: 行の [5:7] の文字が**すべて**車の装備集合（CarEVA ＋ FVA の文字。4WD は 'Z' と区分文字）にある
優先順位（当てはまる行が複数あるとき）: 年式群の大きい方 → ボディの値の大きい方 → グレード一致 → [5] が数字 →
  [5] の文字コードの大きい方 → 一致した装備の数 → [6] の文字コードの大きい方 → ファイル上で先

逆向きに使うと、印字品番の行が選ばれるのは「その行が当てはまり、かつ**それより優先の行がどれも当てはまらない**」車だけ。
今の infer_from_parts（品番の行が持つグレード・年式群の文字を集めるだけ）と違い、
  1) 優先する行が当てはまらないこと（例: 無条件行の品番 → 装備 X の行が別品番なら「X なし」）
  2) 年式群は「以下」の関係（一致ではない）とボディの優先
  3) FVA（エンジン・4WD）も装備と同じ欄で効くこと
まで効くので、グレード・FVA・装備を同時に絞れる。

点数: 見積の品番が ADDATA のその部品にある行だけ使う。本体の選ぶ行と同じ品番なら +1、違えば −1。
ADDATA に無い品番（版違い・社外品・手入力）は 0（証拠にしない）。品番が無い行は単価で同じことをする（変種で価格が割れる部品だけ）。
装備は候補の車ごとに、見積の部品に関係するオプション装備（10.DB の区分 2）の組合せを全部試して最良点を取る
（10.DB の排他グループ（5 人乗り / 6 人乗り など）が同時に付く組合せは除く）。最良点の組合せが複数あれば
**すべてに共通する装備だけを「有」、どれにも無い関係装備を「無」、割れる装備は「決まらない」**とする。
共通の装備だけでは最良点にならない（P か Q のどちらかは付いている）ときだけ、最少の組合せのうちファイル上で先の行のものを仮に採る。

実案件 NEO（価格適応日 080801 の 638 本・080701 の 990 本）で測った結果は scratchpad/revgrade の報告を参照。
"""
from __future__ import annotations

import itertools
import os
import re
import struct
import unicodedata
from typing import Optional


def norm_pn(s) -> str:
    return re.sub(r'[^0-9A-Z]', '', unicodedata.normalize('NFKC', str(s or '')).upper())


# ------------------------------------------------------------------ 本体の条件判定と優先順位
def cond_ok(row: dict, cv: dict) -> bool:
    g = row['grp']
    if g != ' ':
        cg = cv['grp'] if cv['grp'] not in (' ', '') else '0'
        if not ('0' <= cg <= '9') or cg < g:
            return False
    if row['body'] not in cv['bodies']:
        return False
    fl = row['flags']
    if cv['grade'] not in (' ', '') and fl[0] != ' ' and cv['grade'] not in fl[0:5]:
        return False
    for ch in fl[5:7]:
        if ch != ' ' and ch not in cv['equip']:
            return False
    return True


def better(cand: dict, best: dict, cv: dict) -> bool:
    if cand['grp'] != best['grp']:
        return cand['grp'] > best['grp']
    if cand['body'] != best['body']:
        return cand['body'] > best['body']
    g = cv['grade']   # 車のグレードが空欄（' '）なら一致なし（AddataParts._cogni_pick と同じ）
    gb = g != ' ' and g in best['flags'][0:5]; gc = g != ' ' and g in cand['flags'][0:5]
    if gb != gc:
        return gc
    b0, c0 = best['flags'][5], cand['flags'][5]
    bd = '1' <= b0 <= '9'; cd = '1' <= c0 <= '9'
    if bd != cd:
        return cd
    if b0 != c0:
        return c0 > b0
    nb = sum(1 for ch in best['flags'][5:7] if ch != ' ' and ch in cv['equip'])
    nc = sum(1 for ch in cand['flags'][5:7] if ch != ' ' and ch in cv['equip'])
    if nb != nc:
        return nc > nb
    return cand['flags'][6] > best['flags'][6]


def pick(rows: list, cv: dict) -> Optional[dict]:
    best = None
    for r in rows:
        if cond_ok(r, cv) and (best is None or better(r, best, cv)):
            best = r
    return best


def vehicle_cv(year: str, body: str, grade: str, fva: str, sbase: str = '', lbase: str = '00', eva=()) -> dict:
    """fva は Car.FVACode の形（2WD 'A'、4WD 'ZA'）"""
    y = str(year or '').strip()
    bodies = {0}
    for v in (body, sbase, lbase):
        if str(v or '').strip().isdigit():
            bodies.add(int(v))
    return {'grp': y[-1] if y.isdigit() and int(y) else ' ', 'bodies': frozenset(bodies), 'grade': (str(grade or ' ') + ' ')[:1],
            'equip': frozenset(set(eva) | set(str(fva or '').strip()))}


# ------------------------------------------------------------------ 車種の表
class PartsVehicleInference:
    def __init__(self, parts, resolver=None):
        """parts = estimate_to_neo.AddataParts（その車種）、resolver = AddataVehicleResolver（10.DB の装備・SBase を引く）"""
        self.parts = parts
        self.car = parts.car
        self.resolver = resolver
        self.k: dict[int, list] = {}
        price = {}
        for r in parts.p11:
            price.setdefault((r['ref_no'], norm_pn(r['parts_no'])), int(r.get('price') or 0))
        for ref, xs in parts._load_11_raw().items():
            ks = [{'grp': (x.get('grp') or ' ')[:1] or ' ', 'body': int(x.get('body') or 0), 'flags': (str(x.get('flags') or '') + ' ' * 7)[:7],
                   'pn': norm_pn(x.get('pn'))} for x in xs if x.get('disp') == 'K']
            for x in ks:
                x['price'] = price.get((ref, x['pn']), 0)
            if ks:
                self.k[ref] = ks
        self.g = self._load_groups()
        self.k_by_pn: dict[str, list] = {}
        for ref, ks in self.k.items():
            for x in ks:
                if x['pn']:
                    self.k_by_pn.setdefault(x['pn'], [])
                    if ref not in self.k_by_pn[x['pn']]:
                        self.k_by_pn[x['pn']].append(ref)
        self.g_by_pn: dict[str, list] = {}
        for ref, gs in self.g.items():
            for g_ in gs:
                for b in g_['blocks']:
                    if b['pn']:
                        self.g_by_pn.setdefault(b['pn'], [])
                        if ref not in self.g_by_pn[b['pn']]:
                            self.g_by_pn[b['pn']].append(ref)
        self.kind: dict[str, int] = {}; self.overlap: dict[str, str] = {}; self.names: dict[str, str] = {}
        if resolver is not None:
            for l in resolver._vdb_bytes(self.car, '10'):
                t = l.decode('cp932', 'replace').rstrip()
                if len(t) < 7:
                    continue
                code = t[5]
                m = re.search(r'(\d\d)(\d\d|  )([0-9])(\d\d)\s*$', t)
                self.kind[code] = int(m.group(3)) if m else 2          # 1 = エンジン・駆動（FVA で決まる）、2 = オプション装備（人が選ぶ）
                self.overlap[code] = m.group(2).strip() if m else ''   # 同じ番号の装備は同時に付かない（5 人乗り / 6 人乗り）
                self.names[code] = re.split(r'\s{2,}|\d{3,4}cc', t[7:])[0].strip()
        self.options = sorted(c for c, k in self.kind.items() if k == 2)

    def _load_groups(self) -> dict:
        """13/83.DB を索引のグループ（ref, sub = 色群・枝番）ごとに。ブロック [4] 年式群、[5] ボディ、以降 CP932 のフラグ 7・名称 20・品番 17・価格 6"""
        e = self.parts.e; car = self.car
        p83 = os.path.join(e.root, car[0], car, f'{car}83.DB'); p13 = os.path.join(e.root, car[0], car, f'{car}13.DB')
        p, blen = (p83, 201) if os.path.exists(p83) else (p13, 189)
        out: dict = {}
        if not os.path.exists(p):
            return out
        from _addata_db_search import LCG
        raw = open(p, 'rb').read(); n = struct.unpack_from('<H', raw, 0)[0]; base = 2 + n * 8
        if base > len(raw) or (len(raw) - base) % blen:
            return out   # 長さの合わない表は使わない（生成器側の _load_83_raw が例外で知らせる）
        ks = LCG(e._read_seed(car)).keystream(blen)
        nb = (len(raw) - base) // blen
        for i in range(n):
            ref, sub, f, t = struct.unpack_from('<HHHH', raw, 2 + i * 8)
            blocks = []
            for k in range(f, min(t, nb - 1) + 1):
                dec = bytes(a ^ c for a, c in zip(raw[base + k * blen: base + (k + 1) * blen], ks))
                tt = dec[6:].decode('cp932', 'replace')
                pr = tt[44:50].strip()
                blocks.append({'grp': chr(dec[4]) if 0x20 <= dec[4] < 0x7f else ' ', 'body': dec[5], 'flags': (tt[0:7] + ' ' * 7)[:7],
                               'pn': norm_pn(tt[27:44]), 'price': int(pr) if pr.isdigit() else 0})
            out.setdefault(ref, []).append({'sub': sub, 'blocks': blocks})
        return out

    # -------------------------------------------------------------- 見積の行 → 証拠
    def evidence(self, items: list) -> list:
        """items = estimate.json の items（code / parts_no / price / qty / manual）。戻り値 [(kind, refs, value, 表示)]"""
        out = []
        for it in items or []:
            if it.get('manual') is True or str(it.get('manual')).strip().lower() in ('true', '1'):
                continue
            code = re.sub(r'\D', '', str(it.get('code') or ''))
            pn = norm_pn(re.sub(r'\s*\(\d+\)\s*$', '', str(it.get('parts_no') or '')))
            refs = [int(code)] if code else []
            if pn:
                kr = [r for r in (refs or self.k_by_pn.get(pn, [])) if any(x['pn'] == pn for x in self.k.get(r, []))]
                if kr:
                    out.append(('k', tuple(kr), pn, f'{kr[0]:04d} {pn}')); continue
                gr = [r for r in (refs or self.g_by_pn.get(pn, [])) if any(b['pn'] == pn for g_ in self.g.get(r, []) for b in g_['blocks'])]
                if gr:
                    out.append(('g', tuple(gr), pn, f'{gr[0]:04d} {pn}'))
                continue   # ADDATA のこの部品に無い品番（版違い・社外品）は証拠にしない
            if not refs:
                continue
            try:
                q = max(1, int(it.get('qty') or 1))
                pr = int(float(it.get('parts_price') if it.get('parts_price') is not None else (it.get('price') or 0)))
            except (TypeError, ValueError):
                continue
            unit = pr // q if pr > 0 and pr % q == 0 else 0
            ks = self.k.get(refs[0]) or []
            if unit and any(x['price'] == unit for x in ks) and len({x['price'] for x in ks}) > 1:
                out.append(('p', tuple(refs), unit, f'{refs[0]:04d} 単価 {unit}'))
        return out

    def _score1(self, ev, cv) -> int:
        kind, refs, v, _l = ev
        for ref in refs:   # 同じ品番が複数の部品にあるときは、どれかで本体が選べば整合
            if kind == 'k':
                b = pick(self.k.get(ref, []), cv)
                if b and b['pn'] == v:
                    return 1
            elif kind == 'p':
                b = pick(self.k.get(ref, []), cv)
                if b and b['price'] == v:
                    return 1
            else:
                for g_ in self.g.get(ref, []):
                    if any(b['pn'] == v for b in g_['blocks']):
                        b = pick(g_['blocks'], cv)
                        if b and b['pn'] == v:
                            return 1
        return -1

    def _letters(self, ev) -> set:
        kind, refs, _v, _l = ev
        s = set()
        for ref in refs:
            rows = self.k.get(ref, []) if kind in ('k', 'p') else [b for g_ in self.g.get(ref, []) for b in g_['blocks']]
            s |= {ch for r in rows for ch in r['flags'][5:7] if ch != ' '}
        return s

    def _excl_ok(self, E) -> bool:
        seen = set()
        for ch in E:
            o = self.overlap.get(ch, '')
            if o:
                if o in seen:
                    return False
                seen.add(o)
        return True

    def score(self, evs: list, year: str, body: str, grade: str, fva: str, sbase: str = '', fixed_eva=None, max_exh: int = 12,
              required=(), forbidden=()) -> dict:
        """1 台の点数。fixed_eva を渡せば装備はそれに固定（人が決めた装備）。
        required / forbidden は人が指定した装備（hints.eva_codes / eva_exclude）: 組合せは required を必ず含み、forbidden を含まないものだけ試す。
        戻り値 {'score', 'eva_on': 有と決まる装備（「どれかが付く」ときは仮に採った組合せを含む）, 'eva_off': 無と決まる装備,
                'eva_open': 決まらない装備, 'eva_alt': 「このどれかが付く」組合せ（有の装備だけでは最良点にならないとき）, 'bad': 整合しない証拠の表示}"""
        L = set()
        for ev in evs:
            L |= self._letters(ev)
        req = set(required or ()); forb = set(forbidden or ())
        L = sorted(ch for ch in L if ch in self.options and ch not in forb)
        base = frozenset(ch for ch in L if ch in req)   # 人が付けた装備（関係する分）は常に入れ、組合せは残りの文字だけで作る
        L = [ch for ch in L if ch not in base]
        if fixed_eva is not None:
            cv = vehicle_cv(year, body, grade, fva, sbase, eva=set(fixed_eva))
            sc = [self._score1(ev, cv) for ev in evs]
            return {'score': sum(sc), 'eva_on': set(fixed_eva) & (set(L) | base), 'eva_off': (set(L) | base) - set(fixed_eva), 'eva_open': set(), 'eva_alt': [],
                    'bad': [ev[3] for ev, s in zip(evs, sc) if s < 0]}
        if len(L) > max_exh:   # 関係する装備が多すぎるときは 1 文字ずつの山登り
            E: set = set(base)
            cur = sum(self._score1(ev, vehicle_cv(year, body, grade, fva, sbase, eva=E)) for ev in evs)
            while True:
                step = None
                for ch in L:
                    E2 = (E ^ {ch}) | base
                    if not self._excl_ok(E2):
                        continue
                    s2 = sum(self._score1(ev, vehicle_cv(year, body, grade, fva, sbase, eva=E2)) for ev in evs)
                    if s2 > cur and (step is None or s2 > step[0]):
                        step = (s2, E2)
                if not step:
                    break
                cur, E = step
            cv = vehicle_cv(year, body, grade, fva, sbase, eva=E)
            return {'score': cur, 'eva_on': set(E), 'eva_off': set(), 'eva_open': set(L) - set(E), 'eva_alt': [],   # 山登りでは「無」を決めない
                    'bad': [ev[3] for ev in evs if self._score1(ev, cv) < 0]}
        per = [(ev, sorted(self._letters(ev) & (set(L) | base)), {}) for ev in evs]   # 人が付けた装備（base）も採点の鍵に入れる
        best = None; sets = []
        for k in range(len(L) + 1):
            for E0 in itertools.combinations(L, k):
                E = tuple(E0) + tuple(base)
                if not self._excl_ok(E):
                    continue
                Es = set(E); tot = 0
                for ev, le, memo in per:
                    key = tuple(ch for ch in le if ch in Es)
                    if key not in memo:
                        memo[key] = self._score1(ev, vehicle_cv(year, body, grade, fva, sbase, eva=set(key)))
                    tot += memo[key]
                if best is None or tot > best:
                    best = tot; sets = [frozenset(Es)]
                elif tot == best:
                    sets.append(frozenset(Es))
        on = frozenset.intersection(*sets) if sets else frozenset()
        anyl = frozenset.union(*sets) if sets else frozenset()
        # 「有」と決まる装備だけでは最良点にならない（= P か Q のどれかは付いている、としか言えない）ときは、
        # 最少の組合せのうち、見積の品番と同じ品番の行がファイル上でいちばん先に来る組合せを仮に採り、候補も返す（人が確かめる）。
        # 実案件（正解の車両で）080801: 6 本で 正しく付く装備 +5・誤り +1、080701: 6 本で +4・+2（採らないと実機 H24 の 2700 の指数が 2.9 → 2.6 に外れる）
        alt = []; chosen = on
        if sets and on not in sets:
            m = min(len(E) for E in sets)
            mins = [E for E in sets if len(E) == m]
            alt = sorted(sorted(E - on) for E in mins)[:6]

            def _first(E):
                bi = 10 ** 9
                for kind, refs, v, _l in evs:
                    if kind != 'k':
                        continue
                    for ref in refs:
                        for i, r in enumerate(self.k.get(ref, [])):
                            le = {ch for ch in r['flags'][5:7] if ch != ' ' and ch in self.options}
                            if r['pn'] == v and le and le <= E:
                                bi = min(bi, i); break
                return (bi, sorted(E))
            chosen = min(mins, key=_first)
        cv = vehicle_cv(year, body, grade, fva, sbase, eva=chosen)
        return {'score': best or 0, 'eva_on': set(chosen), 'eva_off': (set(L) - set(anyl)) | (forb & set(self.options)), 'eva_open': set(anyl - chosen), 'eva_alt': alt,
                'bad': [ev[3] for ev in evs if self._score1(ev, cv) < 0]}

    def rank(self, evs: list, candidates: list, fixed_eva=None, required=(), forbidden=()) -> dict:
        """candidates = resolver の候補（dict: car_code, year_code, body_code, grade_code, fva_code, four_wd）。
        戻り値 {'scores': [...], 'top': [候補の番号（元の並び順）], 'n_ev': 証拠の行数}"""
        scores = []
        for c in candidates:
            if str(c.get('car_code') or '') != self.car or not c.get('grade_code'):
                scores.append(None); continue
            fva = ('Z' + c['fva_code']) if c.get('four_wd') else str(c.get('fva_code') or '')
            sb = ''
            if self.resolver is not None:
                try:
                    sb = self.resolver.sbase_code(self.car, c['year_code'], c['body_code'], c['grade_code'], self.resolver.fva2(bool(c.get('four_wd')), c['fva_code']))
                except Exception:  # noqa: BLE001
                    sb = ''
            scores.append(self.score(evs, c['year_code'], c['body_code'], c['grade_code'], fva, sb, fixed_eva=fixed_eva, required=required, forbidden=forbidden))
        vals = [s['score'] for s in scores if s is not None]
        top = [i for i, s in enumerate(scores) if s is not None and s['score'] == max(vals)] if vals else []
        return {'scores': scores, 'top': top, 'n_ev': len(evs)}
