# -*- coding: utf-8 -*-
"""print_check.py — コグニで印刷した NEO の PDF と、工場見積の写し（reading.json）を 1 行ずつ突き合わせる。

検算（run_case）と意図との突き合わせ（intent_check）は **金額と下書きの意図**を見る。
どちらも通っていても、**印刷すると見積書と違う**ことがある（2026-09-28 シエンタで 4 件）:

  - 明細の名称（工場がコグニの明細で書き換えた名称が ADDATA の名称になっていた）
  - 費用の名前（'配線修理' がコグニの既定名 '配線・配管費用' に化けていた）
  - 内板骨格の行落ち（'1396 リヤフロアクロスメンバー 修正 基本内' が読み取りから抜けていた）
  - 部品価格適応日（この PC の ADDATA の版。金額は見積書どおりでも日付は違う）

**reading.json は人（AI）の写しなので、印字そのものではない**。だから最後の砦として
「コグニが刷った PDF」と突き合わせる。文字層のある PDF（コグニ出力）ならそのまま読める。

このツールの限界（差が出ても誤りとは限らない）:
  - **税込で印字する見積書**（reading は税抜に直して書く規約）は、帳票が税込で並ぶので全行が差になる
  - **リサイクル部品の行**は印刷の品番欄が「リサイクル部品」なので、reading の元の品番とは必ず違う
  - **手入力行（部品コード無し）**は印刷に部品コードが出ないので、この突き合わせの対象外
  - 明細の並び・ページの切れ目・管理番号は帳票様式の話なので見ない

  cd files && PYTHONIOENCODING=utf-8 python .claude/skills/pdf-to-neo/scripts/print_check.py <案件フォルダ> <印刷した.pdf> [--json 出力先]

出す差: 行落ち / 余分な行 / 名称 / 修理方法 / 品番 / 数量 / 金額 / 費用（名前と金額）/ 内板骨格 / 合計。
表記のゆれ（長音・ハイフン・空白・小書きカナ・全半角）は同じものとみなす（生成器と同じ _name_key）。

印刷を待たずに（NEO の中身から コグニが刷る行を組み立てて）突き合わせる:
    PYTHONIOENCODING=utf-8 python .claude/skills/pdf-to-neo/scripts/print_check.py <案件フォルダ> - --neo <生成した NEO>
（make_neo が生成のあとに自動で回し、差を 確認箇所シートの 要確認 に出す）
"""
from __future__ import annotations

import io
import json
import os
import re
import sys
import unicodedata

HERE = os.path.dirname(os.path.realpath(__file__))
sys.path.insert(0, HERE)
import skill_env  # noqa: E402
skill_env.apply()
sys.path.insert(0, os.path.join(skill_env.FILES, 'claude_neo_pipeline'))
from estimate_to_neo import _name_key, hw  # noqa: E402

ROW_KEYS = ('code', 'name', 'method', 'parts_no', 'index', 'qty', 'price', 'wage', 'flags', 'comment')
METHODS = ('脱着修理', '脱着板金', '点検調整', '分解調整', '取替', '脱着', '修理', '調整', '点検', '板金', '修正', '分解')


def _text_pages(pdf: str) -> list:
    """PDF の文字層をページごとに返す（コグニ出力は文字層がある）"""
    try:
        from pypdf import PdfReader
    except ImportError:
        try:
            from PyPDF2 import PdfReader  # type: ignore
        except ImportError:
            print('pypdf が要る: pip install pypdf'); sys.exit(2)
    return [(p.extract_text() or '') for p in PdfReader(pdf).pages]


def _money(s):
    s = re.sub(r'[^\d]', '', str(s or ''))
    return int(s) if s else 0


def parse_print(pages: list) -> dict:
    """印刷 PDF から 明細行 / 費用 / 内板骨格 / 合計 / 部品価格適応日 を取り出す"""
    rows, expenses, frame, tot, pdate = [], [], [], {}, ''
    name_only: list = []
    sect = ''
    for txt in pages:
        sect = ''   # 区画はページごとに読み直す（帳票の下端に合計欄・作成日が入る）
        in_table = False   # 表の見出し（ｺｰﾄﾞ 修理項目 …）より下だけ金額の無い行を拾う（上は表題・顧客欄。Codex 指摘）
        for line in txt.splitlines():
            t = line.rstrip()
            if not t.strip():
                continue
            if 'ｺｰﾄﾞ' in t and '修理項目' in t:
                in_table = True
                continue
            m = re.search(r'部品価格適応日\s*(\d+)\s*年\s*(\d+)\s*月\s*(\d+)\s*日', t)
            if m:
                _y = int(m.group(1)) % 100   # 西暦 4 桁で刷る様式もある（令和 8 年 = 08）
                pdate = f'{_y:02d}{int(m.group(2)):02d}{int(m.group(3)):02d}'
            if '【内板骨格' in t:
                sect = 'frame'; continue
            if '【塗装' in t:
                sect = 'paint'; continue
            if '【費用' in t:
                sect = 'expense'; continue
            for lbl, key in (('小 計', 'sub'), ('小      計', 'sub'), ('課 税 額 計', 'taxable'), ('課 税 額計', 'taxable'),
                             ('消  費  税', 'tax'), ('消 費 税', 'tax'), ('合      計', 'total'), ('合 計', 'total')):
                if t.replace(' ', '').startswith(lbl.replace(' ', '')):
                    nums = [_money(x) for x in re.findall(r'[\d,]{3,}', t)]
                    if nums:
                        tot[key] = nums if key == 'sub' else nums[-1]
            m = re.match(r'^(\d{4}|保留)\s+(.*)$', t)
            if m and sect == 'paint':
                continue   # 【塗装明細】のパネル行は明細ではない（同じ部品コードが 2 行に見えてしまう）
            if m:
                code, rest = m.group(1), m.group(2)
                mk = ''.join(ch for ch in rest[-8:] if ch in '#*$@n')
                rest2 = rest.rstrip(' #*$@n')
                # 区分は「空白で区切られた語がちょうど区分語」のときだけ。名称に区分の語が入っていても切らない
                # （'Rrﾗｲｾﾝｽﾌﾟﾚｰﾄ脱着修正 脱着修理 …'・'ﾙｰﾌﾍｯﾄﾞﾗｲﾆﾝｸﾞ一部脱着 脱着 …'・'左ｻｰﾄﾞｼｰﾄ(脱着･修理) 脱着 …'）
                _toks = rest2.split()
                _im = next((i for i, w in enumerate(_toks) if w in METHODS), -1)
                meth = _toks[_im] if _im >= 0 else ''
                name = ' '.join(_toks[:_im]).strip() if _im >= 0 else rest2.strip()
                _after = _toks[_im + 1:] if _im >= 0 else []
                pn_text = next((w for w in _after if not re.fullmatch(r'[\d,]*[\d][\d,.]*|\(\d+\)|[#*$@n]+', w)), '')   # 品番欄の文字（品番 or '再封印' のような但し書き）。指数 '1.5' や金額は文字ではない
                pn = ''
                mp = re.search(r'([0-9A-Z]{5}-[0-9A-Z\-]+)', rest2)
                if mp:
                    pn = mp.group(1)
                qty = ''
                mq = re.search(r'\((\d\d)\)', rest2)
                if mq:
                    qty = str(int(mq.group(1)))
                money = [_money(x) for x in re.findall(r'[\d,]+', rest2.replace(pn, '')) if _money(x) >= 10]
                rec = {'code': code, 'name': name, 'method': meth, 'pn': pn, 'pn_text': pn_text, 'qty': qty, 'mark': mk, 'money': money, 'raw': t}
                (frame if sect == 'frame' else rows).append(rec)
                continue
            if sect == 'expense' and not re.search(r'(小\s*計|課\s*税\s*額\s*計|消\s*費\s*税|合\s*計|ページ|部品価格適応日|作成日|見\s*積\s*書|ｺｰﾄﾞ)', t):   # 費用は【費用】の区画だけ（合計欄・明細の行を費用にしない）
                nums = [_money(x) for x in re.findall(r'[\d,]+', t) if _money(x) >= 10]
                nm = re.split(r'\s{1,}[\d,]+', t)[0].strip()
                if nums and nm and 'ページ小計' not in nm and '小計' not in nm:
                    expenses.append({'name': nm, 'money': nums})
            elif in_table and not sect and not re.search(r'\d{1,3}(?:,\d{3})+|\d{3,}', t) and len(t.strip()) >= 2 and not _NOT_ROW_RE.search(t.strip()):   # 金額の無い行（'NO.2' のような短い数字は名前の一部。Codex 指摘）
                name_only.append(t.strip())   # 金額の無い明細の行（金額の無い写しの行と名前で組むときだけ使う。parse_print_pdf と同じ。Codex 指摘）
    return {'rows': rows, 'expenses': expenses, 'frame': frame, 'totals': tot, 'price_date': pdate, 'name_only': name_only}


# 金額の無い行のうち明細でないもの（欄外の受付番号・部品価格適応日、塗装条件の行）。余分な行として数えない（バグハント 2026-09-29）
_NOT_ROW_RE = re.compile(r'部品価格適応日|作成日|\d{5,}|ｺｰﾄﾞ|修理項目|^\d+\s*/\s*\d+$|^(塗料|塗膜|高機能塗装|材料代|加算基礎|ブース|塗装方法|見積書|ページ)')
_MONEY_W = re.compile(r'^([\d,]+)円?([#*$@n]*)$')
_TOTAL_LBL = (('小計', 'sub'), ('課税額計', 'taxable'), ('消費税', 'tax'), ('合計', 'total'))


def parse_print_pdf(pdf: str):
    """印刷 PDF を語の座標で読む（PyMuPDF）。parse_print と同じ形。PyMuPDF が無い・表の見出しが無ければ None。
    表の見出し（ｺｰﾄﾞ 修理項目 …）より上（顧客欄）は読まない。欄は語の中身で決める（帳票の版で x 位置が違う）"""
    try:
        import fitz  # type: ignore  # noqa: PLC0415
    except ImportError:
        return None
    rows, expenses, frame, tot, pdate = [], [], [], {}, ''
    name_only: list = []
    seen = False
    for page in fitz.open(pdf):
        ws = page.get_text('words')
        for w in ws:   # 部品価格適応日（見出しより下の欄外にある）
            pass
        m = re.search(r'部品価格適応日\s*(\d+)\s*年\s*(\d+)\s*月\s*(\d+)\s*日', page.get_text())
        if m:
            pdate = f'{int(m.group(1)) % 100:02d}{int(m.group(2)):02d}{int(m.group(3)):02d}'
        hd = {}
        for w in ws:
            for k, pat in (('code', 'ｺｰﾄﾞ'), ('name', '修理項目'), ('price', '部品価格'), ('wage', '工賃')):
                if k not in hd and w[4].startswith(pat):
                    hd[k] = w
        if len(hd) < 4:
            continue
        seen = True
        top = hd['code'][3]
        lines: dict = {}
        for w in ws:
            if w[1] > top + 1:
                lines.setdefault(round((w[1] + w[3]) / 2 / 3), []).append(w)
        sect = ''
        for y in sorted(lines):
            code, names, meth, after, money, mark, qty = '', [], '', [], [], '', ''
            for w in sorted(lines[y], key=lambda w: w[0]):
                t = w[4].replace('\u3000', ' ').strip()
                if not t:
                    continue
                cx = (w[0] + w[2]) / 2
                mm = _MONEY_W.match(t)
                if not code and not names and w[2] < hd['name'][0] and re.fullmatch(r'\d{4}|保留', t):
                    code = t
                elif re.fullmatch(r'[#*$@n]+', t):
                    mark += t
                elif mm and cx > hd['price'][0] - 20:
                    money.append(_money(mm.group(1))); mark += mm.group(2)
                elif re.fullmatch(r'\(\d\d\)', t):
                    qty = str(int(t[1:3]))
                elif not meth and names and t in METHODS:
                    meth = t
                elif meth:
                    after.append(t)
                else:
                    names.append(t)
            if not meth and code:   # 名称と区分がくっついた語（'…ｻｲﾄﾞｽﾍﾟ-ｻ取替'）。その後ろの語は品番欄。費用名（'配線修理'）は切らない
                for i_, t_ in enumerate(names):
                    m_ = next((m_ for m_ in METHODS if t_.endswith(m_) and len(t_) > len(m_)), None)
                    if m_:
                        after = names[i_ + 1:] + after
                        names = names[:i_] + [t_[:-len(m_)]]
                        meth = m_
                        break
            nm = ' '.join(names).strip()
            if not (nm or code or money):
                continue
            if re.search(r'ページ小計|前頁|次頁', nm):
                continue
            h = re.fullmatch(r'【(.+?)】', nm)   # 区画の見出しは【…】だけの行。名前の中の【本国在庫無】は見出しではない（2026-09-29 nc27）
            if h:
                sect = 'frame' if '内板骨格' in h.group(1) else 'paint' if '塗装' in h.group(1) else 'expense' if '費用' in h.group(1) else sect
                continue
            key = next((k for lbl, k in _TOTAL_LBL if nm.replace(' ', '') == lbl), None)
            if key and money:
                tot[key] = money if key == 'sub' else money[-1]
                continue
            if sect == 'paint' and not code:
                continue
            if code and sect != 'paint':
                pn_text = ' '.join(x for x in after if not re.fullmatch(r'[\d.,]+', x))
                mp = re.search(r'([0-9A-Z]{5}-[0-9A-Z\-]+)', pn_text)
                rec = {'code': code, 'name': nm, 'method': meth, 'pn': mp.group(1) if mp else '', 'pn_text': pn_text,
                       'qty': qty, 'mark': mark, 'money': [v for v in money if v >= 10], 'raw': ' '.join([code, nm, meth, pn_text])}
                (frame if sect == 'frame' else rows).append(rec)
            elif not code and meth and nm and sect not in ('paint', 'expense'):
                # 部品コードの無い手入力の明細行（区分が刷られる）。コードは空で拾う（Codex 指摘）
                pn_text = ' '.join(x for x in after if not re.fullmatch(r'[\d.,]+', x))
                mp = re.search(r'([0-9A-Z]{5}-[0-9A-Z\-]+)', pn_text)
                rows.append({'code': '', 'name': nm, 'method': meth, 'pn': mp.group(1) if mp else '', 'pn_text': pn_text,
                             'qty': qty, 'mark': mark, 'money': [v for v in money if v >= 10], 'raw': ' '.join([nm, meth, pn_text])})
            elif not code and not meth and money and sect != 'paint':
                expenses.append({'name': nm, 'money': [v for v in money if v >= 10]})
            elif not code and not meth and not money and nm and not sect and not _NOT_ROW_RE.search(nm):
                # 金額も区分も無い手入力の明細行（中括弧でまとめた技術料の 2 行目以降 等）。金額の無い行と組むときだけ使う（余分な行とは言わない。nc37）
                name_only.append(nm)
    if not seen:
        return None
    return {'rows': rows, 'expenses': expenses, 'frame': frame, 'totals': tot, 'price_date': pdate, 'name_only': name_only}


def print_from_neo(neo_path: str) -> dict:
    """NEO の中身から、コグニが印刷する 明細・費用・内板骨格・合計 を組み立てる（parse_print と同じ形）。
    印刷 PDF を待たずに compare() に掛けられる（2026-09-28: 印刷してから名称・費用名・骨格・品番欄の違いに気づく往復を無くす）。
    明細は親の行だけ（PartsCodeSub = -1）。名称は PartsName（見積書の名称で書いた行は neo_name）、品番欄は PartsNo、金額は 部品価格・工賃"""
    import intent_check  # noqa: PLC0415  NEO を開く処理を共有する
    em, iff, tmps = intent_check._open(neo_path)
    try:
        rows = []
        for r in em.execute('SELECT * FROM ERParts ORDER BY RecordNo'):
            if r['PartsCodeSub'] not in (-1, None) and int(r['RecycleFlag'] or 0) != 1:
                continue  # 子行は刷られない。リサイクル部品に置き換えた行（PartsCodeSub=1・RecycleFlag=1）は刷られる（Codex 指摘）
            pn = str(r['PartsNo'] or '').strip()
            cnt = int(r['PartsCount'] or 1) if str(r['PartsCount'] or '').lstrip('-').isdigit() else 1
            money = [int(v) for v in (r['PartsPriceOutTax'], r['WageOutTax']) if v not in (None, '') and int(v) >= 10]
            code = '保留' if int(r['ReserveFlag'] or 0) == 1 else str(r['PartsCode'] or '').strip()  # 保留の行はコードの代わりに「保留」と刷られる
            rows.append({'code': code, 'name': str(r['PartsName'] or '').strip(), 'method': str(r['DisposalName'] or '').strip(),
                         'pn': pn if re.search(r'[0-9A-Z]{3,}-[0-9A-Z]', pn) else '', 'pn_text': pn if pn not in ('-',) else '',
                         'qty': str(cnt) if cnt > 1 else '', 'mark': '', 'money': money, 'raw': ''})
        expenses = []
        for e in em.execute('SELECT * FROM Expense ORDER BY LineNo'):
            money = [int(v) for v in (e['PartsPriceOutTax'], e['WageOutTax']) if v not in (None, '') and int(v) >= 10]
            if money:
                expenses.append({'name': str(e['Name'] or '').strip(), 'money': money})
        frame = [{'code': str(f['PartsCode'] or '').strip(), 'name': str(f['PartsName'] or ''), 'rank': f['DamageRank']} for f in em.execute('SELECT * FROM Frame ORDER BY LineNo')]
        fp = em.execute('SELECT FrameFlag FROM FramePlan').fetchone()
        if fp is not None and int(fp['FrameFlag'] or 0) == 1:
            frame.insert(0, {'code': '1371', 'name': '基本修正作業', 'rank': None})
        t = em.execute('SELECT SubTotal, tx_TotalOutTax, Total FROM Total').fetchone()
        totals = {'taxable': int(t['SubTotal']), 'tax': int(t['tx_TotalOutTax']), 'total': int(t['Total'])} if t is not None else {}
    finally:
        em.close(); iff.close()
        for tf in tmps:
            try:
                os.unlink(tf)
            except OSError:
                pass
    return {'rows': rows, 'expenses': expenses, 'frame': frame, 'totals': totals, 'price_date': ''}


def read_rows(rd: dict) -> list:
    out = []
    for b in rd.get('blocks') or []:
        for x in b.get('rows') or []:
            d = dict(zip(ROW_KEYS, (str(x).split('|') + [''] * 10)[:10])) if isinstance(x, str) else dict(x)
            if not str(d.get('name') or '').strip() or 'N' in str(d.get('flags') or '').upper():
                continue   # 注記の行（N）は明細として刷られない（2026-09-29 コグニ以外の書式で「行落ち」と誤って出ていた）
            if d.get('neo_name'):
                d['name'] = d['neo_name']   # NEO の名称欄に入れた短い名前で刷られる（2026-09-29 nc12・nc13）
            _c = str(d.get('code') or '').strip()
            if re.fullmatch(r'\d{1,4}', _c):
                d['code'] = _c.zfill(4)     # '532' と写しても印刷は '0532'（nc15）
            if 'R' in str(d.get('flags') or '').upper() or d.get('reserve'):
                d['code'] = '保留'   # 保留の行は印刷でも部品コードの代わりに「保留」と出る
            _mt = re.search(r'\[税込 部品=(\d*) 工賃=(\d*)\]', str(d.get('comment') or ''))   # 税抜に直した見積の印字額（reading_check.tax_in_mark。Codex 指摘）
            if _mt:
                if _mt.group(1) and not d.get('price_in'):
                    d['price_in'] = int(_mt.group(1))
                if _mt.group(2) and not d.get('wage_in'):
                    d['wage_in'] = int(_mt.group(2))
            out.append(d)
    return out


def rows_from_estimate(est: dict) -> dict:
    """estimate.json の明細（下書きが部品コードを決めたもの）を、compare() に渡せる reading の形にする。
    部品コードの無い見積書（コグニ以外の書式）は写しにコードが無いので、写しと印刷の行を組めない（差 50〜160 件がすべて誤報だった。2026-09-29）"""
    rows = []
    for it in est.get('items') or []:
        rows.append({'code': '' if it.get('manual') else str(it.get('code') or ''), 'name': it.get('neo_name') or it.get('name') or '',
                     'method': it.get('method') or '', 'parts_no': it.get('parts_no') or '', 'qty': it.get('qty') or '',
                     'price': it.get('parts_price') if it.get('parts_price') is not None else it.get('price'),   # 生成器と同じ優先（バグハント）
                     'wage': it.get('wage'), 'flags': 'R' if it.get('reserve') else '',
                     'price_in': it.get('price_in'), 'wage_in': it.get('wage_in')})
    out = {k: v for k, v in est.items() if k not in ('items',)}
    out['blocks'] = [{'title': '', 'rows': rows}]
    return out


def _in(v: int, money: list, tax_rate: int = 0) -> bool:
    """印刷の金額の中に v があるか。内税で刷る見積（tax_rate）は税込の額（端数処理の違いで ±1 円）も同じとみる"""
    if v in money:
        return True
    if tax_rate:
        t = v * (100 + tax_rate) / 100
        return any(abs(m - t) <= 1 for m in money)
    return False


def compare(rd: dict, pr: dict, names: bool = True) -> list:
    """差の一覧（人が読む文字列）。表記のゆれは差にしない。names=False は名称を比べない（コグニ以外の書式: 部品コードのある行は ADDATA の名称で刷られるのが正しい）"""
    diffs = []
    rrows = read_rows(rd)
    _tr = int(rd.get('tax_included') or 0) if str(rd.get('tax_included') or '').isdigit() else (10 if rd.get('tax_included') else 0)   # 内税で刷る（2026-09-29 nc06・nc07・nc13）
    p_by = {}
    for r in pr['rows']:
        p_by.setdefault(r['code'], []).append(r)
    r_by = {}
    for r in rrows:
        r_by.setdefault(str(r.get('code') or '').strip(), []).append(r)
    for c in sorted(set(r_by) - set(p_by)):
        if c:
            for r in r_by[c]:
                diffs.append(f"行落ち: 見積書 {c} {r.get('name')} が印刷に無い")
    for c in sorted(set(p_by) - set(r_by)):
        for r in p_by[c]:
            diffs.append(f"余分な行: 印刷 {c} {r['name']} が見積書の写しに無い")
    for c in sorted(set(p_by) & set(r_by)):
        if c:
            if len(p_by[c]) != len(r_by[c]):
                diffs.append(f'行数: {c} 見積書 {len(r_by[c])} 行 / 印刷 {len(p_by[c])} 行')
            pairs = list(zip(r_by[c], p_by[c]))
        else:
            pairs = []
        for r, p in pairs:
            nm_r = re.sub(r'\s*[（(]\s*各?\s*\d+\s*個?\s*[)）]\s*$', '', hw(str(r.get('name') or '')))
            nm_p = str(p['name'])
            if names and _name_key(nm_r) != _name_key(nm_p):
                diffs.append(f'名称: {c} 見積書「{nm_r.strip()}」/ 印刷「{nm_p.strip()}」')
            m_r = hw(str(r.get('method') or '')).strip()
            if m_r and p['method'] and _name_key(m_r) != _name_key(p['method']):
                diffs.append(f"修理方法: {c} 見積書「{m_r}」/ 印刷「{p['method']}」")
            pn_r = str(r.get('parts_no') or '').strip()
            pn_p = p['pn'] or p.get('pn_text') or ''
            if pn_r and pn_r != '-' and pn_p and _name_key(pn_r) != _name_key(pn_p):
                diffs.append(f"品番欄: {c} 見積書「{pn_r}」/ 印刷「{pn_p}」")
            elif pn_r and pn_r != '-' and not pn_p:
                diffs.append(f"品番欄: {c} 見積書「{pn_r}」/ 印刷は空欄")
            elif not pn_r and p.get('pn_text') and not p['pn']:
                diffs.append(f"品番欄: {c} 見積書は空欄 / 印刷「{p['pn_text']}」")   # 生成器が要らない文字を入れていないか（今回の規則の逆向き）
            q_r = str(r.get('qty') or '').strip()
            if q_r not in ('', '1') and p['qty'] and q_r != p['qty']:
                diffs.append(f"数量: {c} 見積書 {q_r} / 印刷 {p['qty']}")
            for k, lbl in (('price', '部品価格'), ('wage', '工賃')):
                v = _money(r.get(k))
                _vin = _money(r.get(k + '_in'))   # 税込で印字された見積書の印字額（内税の NEO はこの額で刷られる。数量行は 税抜×1.1 と 1〜2 円違う。2026-09-29 nc30・nc38）
                if v > 0 and not _in(v, p['money'], _tr) and not (_vin > 0 and _vin in p['money']):
                    diffs.append(f"{lbl}: {c} 見積書 {v:,} / 印刷 {p['money']}")
    # 部品コードの無い手入力の行: 並びが揃わず、自由な区分（'施工'）の行は印刷で名称とくっつき費用の形にも見える。
    # 金額がすべて印刷の金額に含まれ、名称が前方一致する印刷の行（無ければ費用の形の行）と組む。組めなければ行落ち、印刷にだけある行は余分な行（Codex 指摘）
    _p_manual = list(p_by.get('', []))
    _p_exp = list(pr['expenses'])
    _p_name_only = list(pr.get('name_only') or [])   # 呼び出し元の pr を書き換えない（Codex 指摘）
    for r in r_by.get('', []):
        _nm = re.sub(r'\s*[（(]\s*各?\s*\d+\s*個?\s*[)）]\s*$', '', hw(str(r.get('name') or ''))).strip()
        _k = _name_key(_nm)
        _amts = [(_money(r.get(k_)), _money(r.get(k_ + '_in'))) for k_ in ('price', 'wage') if _money(r.get(k_)) > 0]   # (税抜, 税込の印字額)

        def _ok(p):
            pk = _name_key(str(p['name']))
            if not _amts and p.get('money'):   # 金額の無い行は金額のある印刷の行と組まない（組むと金額付きの余分な行を隠す。Codex 指摘）
                return False
            return bool(_k and pk) and (pk.startswith(_k) or _k.startswith(pk)) and all(
                _in(v, p['money'], _tr) or (vin > 0 and vin in p['money']) for v, vin in _amts)
        p = next((p for p in _p_manual if _ok(p)), None)
        if p is not None:
            _p_manual.remove(p)
            _mr, _mp = hw(str(r.get('method') or '')).strip(), str(p.get('method') or '')
            if _mr and _mp and _name_key(_mr) != _name_key(_mp):
                diffs.append(f"修理方法: 手入力の行 {_nm} 見積書「{_mr}」/ 印刷「{_mp}」")
            continue
        _mr = _name_key(hw(str(r.get('method') or '')).strip())
        # 費用の形の行は名称と区分の語がくっついている: 写しの区分（'施工'）が印刷の名称の後ろにあること（Codex 指摘）
        p = next((p for p in _p_exp if _ok(p) and (not _mr or _name_key(str(p['name'])).endswith(_mr))), None)
        if p is not None:
            _p_exp.remove(p)
            continue
        p = next((p for p in _p_exp if _ok(p)), None)
        if p is not None:
            _p_exp.remove(p)
            diffs.append(f"修理方法: 手入力の行 {_nm} 見積書「{hw(str(r.get('method') or '')).strip()}」が印刷に無い（印刷「{p['name']}」）")
            continue
        _no = _p_name_only
        _hit = next((x for x in _no if not _amts and _k and (_name_key(x).startswith(_k) or _k.startswith(_name_key(x)))), None)
        if _hit is not None:   # 金額の無い行は、金額の無い印刷の行と名前で組む
            _no.remove(_hit)
            continue
        diffs.append(f'行落ち: 見積書 手入力の行 {_nm} が印刷に無い')
    for p in _p_manual:
        diffs.append(f"余分な行: 印刷 手入力の行 {p['name']} が見積書の写しに無い")
    for x in _p_name_only:   # 金額の無い印刷の行が余った（注記の ※ / ＊ 行は写しでは N なので除く。バグハント）
        if not re.match(r'^[※＊*]', x):
            diffs.append(f"余分な行: 印刷 金額の無い行 {x} が見積書の写しに無い")
    # 費用
    for ex in rd.get('expenses') or []:
        amt = _money(ex.get('amount'))
        if not amt:
            continue
        hit = [e for e in _p_exp if _in(amt, e['money'], _tr)]   # 手入力の行と組んだ費用の形の行は使わない（二重に数えない。Codex 指摘）
        _named = [e for e in hit if _name_key(hw(str(ex.get('name') or ''))) == _name_key(e['name'])]
        hit = _named + [e for e in hit if e not in _named]   # 同じ額の費用が複数あるときは名前の合う方と組む（'写真代' と 'ｼｮｰﾄﾊﾟｰﾂ' が同額。nc02）
        if not hit:
            diffs.append(f"費用: 見積書「{ex.get('name')}」{amt:,} 円が印刷に無い")
        elif not any(_name_key(hw(str(ex.get('name') or ''))) == _name_key(e['name']) for e in hit):
            diffs.append(f"費用名: 見積書「{ex.get('name')}」/ 印刷「{hit[0]['name']}」")
    # 内板骨格
    fr = (rd.get('frame') or {})
    want = [x for x in (fr.get('items') or [])]
    got = [g for g in pr['frame'] if g['code'] not in ('1371',)]
    if fr and len(want) != len(got):
        diffs.append(f"内板骨格の行: 見積書 {len(want)} 行 {[x.get('code') for x in want]} / 印刷 {len(got)} 行 {[g['code'] for g in got]}")
    # 合計
    t = rd.get('totals') or {}
    for k, lbl in (('taxable', '課税額計'), ('tax', '消費税'), ('total', '合計')):
        if t.get(k) and pr['totals'].get(k) and _money(t[k]) != pr['totals'][k]:
            diffs.append(f"{lbl}: 見積書 {_money(t[k]):,} / 印刷 {pr['totals'][k]:,}")
    return list(dict.fromkeys(diffs))   # 同じ差（部品側・工賃側で 2 回出る費用など）は 1 回だけ


def main(argv: list) -> int:
    if len(argv) < 3:
        print(__doc__); return 2
    case, pdf = argv[1], argv[2]
    rd = json.load(io.open(os.path.join(case, 'reading.json'), encoding='utf-8'))
    pr = print_from_neo(argv[argv.index('--neo') + 1]) if '--neo' in argv else (parse_print_pdf(pdf) or parse_print(_text_pages(pdf)))
    if not pr['rows'] and not pr['expenses'] and not pr['totals']:   # 手入力の行だけの見積（汎用車種）は費用の形で読める
        print('この PDF から明細を読めなかった（コグニの印刷 PDF か、文字層のある PDF を渡す）'); return 2
    diffs = compare(rd, pr)
    print(f"印刷 {len(pr['rows'])} 行 / 見積書の写し {len(read_rows(rd))} 行 / 費用 {len(pr['expenses'])} / 内板骨格 {len(pr['frame'])}")
    if pr['price_date']:
        print(f"部品価格適応日（印刷）: {pr['price_date'][:2]}年{int(pr['price_date'][2:4])}月{int(pr['price_date'][4:6])}日"
              '  ← 工場の見積書と違うなら、この PC の ADDATA の版の違い（金額は見積書どおりでよい）')
    for d in diffs:
        print('  ★', d)
    print('差なし' if not diffs else f'差 {len(diffs)} 件')
    if '--json' in argv and argv.index('--json') + 1 < len(argv):
        out = argv[argv.index('--json') + 1]
        json.dump({'diffs': diffs, 'print': {k: v for k, v in pr.items() if k != 'rows'}}, io.open(out, 'w', encoding='utf-8'), ensure_ascii=False, indent=1)
        print('JSON:', out)
    return 1 if diffs else 0


if __name__ == '__main__':
    sys.exit(main(sys.argv))
