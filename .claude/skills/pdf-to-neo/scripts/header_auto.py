# -*- coding: utf-8 -*-
"""header_auto.py — 元案件フォルダの 速報・確報（自動車車両損害調査報告書。文字層のある PDF）から、
pages/header.json の 車両・顧客・保険・ヒント を自動で埋める（手順 4 の header.json の転記を無くす）。

報告書の 1 ページ目は「項目名の行の次の行に値」の決まった形（2026-09-28 のジムニー・シエンタで同じ）:
    事故番号 / 事故日 / 事故場所 / 契約者名 / 登録番号 / 所有者 / 車名 / 使用者 / 型式 / グレード / 車台No. /
    原動機型式 / 初度登録 / 登録日 / 型式類別（'18786 / 0006'）/ 有効期限 / 走行距離 / カラーNo. / 画像鑑定
写し先（estimate_schema.md・判断規則 10-28・保険欄の書き方の約束）:
    vehicle.model_code（排ガス記号 '3BA-' を除く）/ serial_no / desig / category / reg_date（'R7.5'）/ color_code（カラーNo. の最初の語）/ engine
    hints.grade_name ← グレード
    customer.name ← 使用者 / owner ← 所有者（NEO には書かれない控え）/ reg_no ← 登録番号 / kilometer ← 走行距離 / term_date ← 有効期限
    insurance.company ← 案件フォルダ名の頭（chubb → Chubb損害保険 …）/ accept_no・policy_no ← 事故番号（証券番号が無いときは事故番号を入れる約束）/
              contractor ← 契約者名 / accident_date ← 事故日 / presence_date ← 画像鑑定なら '写真鑑定'
既に書いてある値は上書きしない（--overwrite で上書き）。書いた項目は header.json の `_auto_from` に残す（merge は _ で始まるキーを持ち込まない）。
顧客・保険の値は画面に出さない（項目名だけ）。車両の値は出す（照合の確認に要る）。

使い方（files ディレクトリで）:
    PYTHONIOENCODING=utf-8 python .claude/skills/pdf-to-neo/scripts/header_auto.py <案件フォルダ(NEO_check)> <元案件フォルダ> [--report <報告書PDF>] [--overwrite]
"""
from __future__ import annotations

import argparse
import logging
import os
import re
import sys
import unicodedata
from typing import Optional

HERE = os.path.dirname(os.path.realpath(__file__))
sys.path.insert(0, HERE)
import reading_pages  # noqa: E402

LABELS = ('事故番号', '事故日', '事故場所', '契約者名', '登録番号', '所有者', '車名', '使用者', '型式', 'グレード', '車台No.', '原動機型式',
          '初度登録', '登録日', '型式類別', '有効期限', '走行距離', 'カラーNo.', '画像鑑定')
# 案件フォルダ名の頭 → 保険会社（NEO_check の既存案件の書き方）
INSURERS = (('chubb', 'Chubb損害保険'), ('三井住友', '三井住友海上火災保険'), ('東海日動', '東京海上日動火災保険'), ('東京海上', '東京海上日動火災保険'),
            ('coop', 'こくみん共済COOP'), ('楽天', '楽天損害保険'), ('損保ジャパン', '損害保険ジャパン'), ('あいおい', 'あいおいニッセイ同和損害保険'),
            ('ソニー', 'ソニー損害保険'), ('セゾン', 'SOMPOダイレクト損害保険'), ('イーデザイン', 'イーデザイン損害保険'), ('アクサ', 'アクサ損害保険'))
PERSONAL = {'customer', 'insurance'}
# 同じ項目の別の書き方（報告書の版・様式で違う）→ LABELS の名前にそろえる
LABEL_ALIASES = {'車台番号': '車台No.', '車体番号': '車台No.', 'カラー番号': 'カラーNo.', 'カラーコード': 'カラーNo.', '型式指定類別': '型式類別',
                 '型式指定・類別': '型式類別', '初度登録年月': '初度登録', '契約者': '契約者名', '有効期間満了日': '有効期限', '車検満了日': '有効期限'}


def nfkc(s) -> str:
    return unicodedata.normalize('NFKC', str(s or ''))


def text_pages(pdf: str, n: int = 1) -> list[str]:
    logging.disable(logging.WARNING)  # pypdf の「Advanced encoding … not implemented」を出さない
    try:
        import pypdf  # type: ignore
    except ImportError:
        return []
    try:
        r = pypdf.PdfReader(pdf)
        return [(p.extract_text() or '') for p in r.pages[:n]]
    except Exception:  # noqa: BLE001  壊れた PDF・JBIG2 の画像だけの PDF
        return []


def is_report(text: str) -> bool:
    """速報・確報の報告書か（項目名の別表記も見る: 型式指定類別 / 車体番号 …。Codex 指摘）"""
    t = nfkc(text).replace(' ', '').replace('　', '')
    has = lambda lb: nfkc(lb) in t or any(nfkc(al) in t for al, to in LABEL_ALIASES.items() if to == lb)  # noqa: E731
    return '事故番号' in t and has('型式類別') and has('車台No.')


def find_report(src_dir: str) -> Optional[str]:
    """元案件フォルダの報告書 PDF（確報 → 速報 → 名前に日付の新しいもの の順）"""
    cands = []
    for f in os.listdir(src_dir):
        if not f.lower().endswith('.pdf'):
            continue
        p = os.path.join(src_dir, f)
        pages = text_pages(p, 1)
        if pages and is_report(pages[0]):
            rank = 2 if '確報' in f else (1 if '速報' in f else 0)
            cands.append((rank, os.path.getmtime(p), p))
    return max(cands)[2] if cands else None


def parse_report(text: str) -> dict:
    """1 ページ目の文字層 → {項目名: 値}（項目名の行の次の行が値）"""
    lines = [ln.strip() for ln in text.splitlines() if ln.strip()]
    out: dict = {}
    keys = {nfkc(lb).replace(' ', ''): lb for lb in LABELS}
    keys.update({nfkc(al).replace(' ', ''): lb for al, lb in LABEL_ALIASES.items()})  # '車台番号' も '車台No.' として読む（Codex 指摘）
    for i, ln in enumerate(lines):
        k = nfkc(ln).replace(' ', '').replace('　', '')
        if k in keys and keys[k] not in out:
            val = lines[i + 1].strip() if i + 1 < len(lines) else ''
            nxt = nfkc(lines[i + 2]).strip() if i + 2 < len(lines) else ''
            if keys[k] == '登録番号' and re.fullmatch(r'[ぁ-んア-ン]\s*[\d・\-]{1,5}', nxt) and nfkc(nxt).replace(' ', '') not in keys:
                val = f'{val} {nxt}'   # 文字層で改行された登録番号（'品川 300' / 'あ 1234' のように 2 行に割れる。2026-09-29 nc12 で 2 行目が落ちた）
            out[keys[k]] = re.sub(r'[\x00-\x1f\x7f]', '', val).strip()   # NUL などの制御文字（確報のグレード名に混ざっていた。nc19）
    return out


def wareki_ym(s: str) -> str:
    """'令和7年5月' → 'R7.5'、'平成27年5月' → 'H27.5'"""
    m = re.search(r'(令和|平成|昭和|R|H|S)\s*(元|\d{1,2})\s*年\s*(\d{1,2})\s*月', nfkc(s))
    if not m:
        return ''
    era = {'令和': 'R', '平成': 'H', '昭和': 'S'}.get(m.group(1), m.group(1))
    y = 1 if m.group(2) == '元' else int(m.group(2))
    return f'{era}{y}.{int(m.group(3))}'


def wareki_ymd(s: str) -> str:
    """'令和8年5月14日' → '20260514'"""
    m = re.search(r'(令和|平成|R|H)\s*(元|\d{1,2})\s*年\s*(\d{1,2})\s*月\s*(\d{1,2})\s*日', nfkc(s))
    if not m:
        return ''
    y = 1 if m.group(2) == '元' else int(m.group(2))
    base = 2018 if m.group(1) in ('令和', 'R') else 1988
    return f'{base + y:04d}{int(m.group(3)):02d}{int(m.group(4)):02d}'


def strip_emission(model: str) -> str:
    """'3BA-JB64W' → 'JB64W'（排ガス記号を除く。estimate_schema の model_code）"""
    m = nfkc(model).strip().upper().replace(' ', '')
    m2 = re.match(r'^[0-9A-Z]{3}-(.+)$', m)
    if m2 and re.search(r'\d', m2.group(1)):
        return m2.group(1)
    m3 = re.match(r'^\d[A-Z]{2}([A-Z]{1,4}\d.*)$', m)  # ハイフンの無い印字 '6AANHP170G'（排ガス記号は 数字＋英字 2 つ）
    return m3.group(1) if m3 else m


def build(fields: dict, case_name: str) -> dict:
    """報告書の項目 → header の差分（{'vehicle': {...}, 'customer': {...}, 'insurance': {...}, 'hints': {...}}）"""
    v, c, ins, h = {}, {}, {}, {}
    if fields.get('型式') and not re.fullmatch(r'[\s*＊※\-－]*', nfkc(fields['型式'])):   # '＊＊＊'（型式の記載なし）は写さない（nc03。見積書の型式を人が写す）
        v['model_code'] = strip_emission(fields['型式'])
    if fields.get('車台No.'):
        v['serial_no'] = nfkc(fields['車台No.']).strip().upper().replace(' ', '')
    m = re.search(r'(\d{5})\s*[/／-]\s*(\d{1,4})', nfkc(fields.get('型式類別')))
    if m:
        v['desig'], v['category'] = m.group(1), m.group(2).zfill(4)
    if wareki_ym(fields.get('初度登録', '')):
        v['reg_date'] = wareki_ym(fields['初度登録'])
    col = nfkc(fields.get('カラーNo.')).strip().split()
    if col and re.fullmatch(r'[0-9A-Z]{2,6}', col[0].upper()):
        v['color_code'] = col[0].upper()
    m = re.match(r'[0-9A-Z]+', nfkc(fields.get('原動機型式')).strip().upper())
    if m:
        v['engine'] = m.group(0)  # 'S07A型(2WD)' → 'S07A'、'DLA-4450' → 'DLA'（既存案件の書き方）
    if nfkc(fields.get('グレード')).strip():
        h['grade_name'] = nfkc(fields['グレード']).split('/')[0].strip()  # 'G Cuero/FUNBASE G Cuero' → 'G Cuero'
    def _placeholder(x) -> bool:   # 報告書の「車検証確認できず」「書類確認出来ず」は名前ではない（2026-09-29 nc22・nc27・nc29 で顧客名に入った）
        return bool(re.search(r'確認(でき|出来)ず|確認不可|不明|記載なし', nfkc(x or '')))
    for _k in ('使用者', '所有者'):
        if _placeholder(fields.get(_k)):
            fields = dict(fields, **{_k: ''})
    user = (fields.get('使用者') or '').strip()
    if nfkc(user).replace(' ', '') in ('同上', '***', '＊＊＊') and fields.get('所有者'):
        user = fields['所有者'].strip()  # 使用者欄が「同上」: 所有者が使用者（シエンタ 2026-09-28。正解の顧客名は所有者だった）
    if nfkc(user).replace(' ', '') in ('同上', '***', '＊＊＊'):
        user = ''   # 「同上」なのに所有者が空（「車検証確認できず」を外した）: 印を名前にしない（Codex 指摘）
    if user:
        c['name'] = user
    if fields.get('所有者'):
        c['owner'] = fields['所有者'].strip()
    if fields.get('登録番号'):
        c['reg_no'] = fields['登録番号'].strip()
    km = re.sub(r'\D', '', nfkc(fields.get('走行距離')))
    if km:
        c['kilometer'] = km
    if wareki_ymd(fields.get('有効期限', '')):
        c['term_date'] = wareki_ymd(fields['有効期限'])
    low = nfkc(case_name).lower()
    comp = next((name for key, name in INSURERS if nfkc(key).lower() in low), '')
    if comp:
        ins['company'] = comp
    if fields.get('事故番号'):
        ins['accept_no'] = nfkc(fields['事故番号']).strip()
        ins['policy_no'] = ins['accept_no']  # 証券番号が読めないときは事故番号を入れる（2026-09-16 亮平さん指示）
    if fields.get('契約者名'):
        ins['contractor'] = fields['契約者名'].strip()
    if wareki_ymd(fields.get('事故日', '')):
        ins['accident_date'] = wareki_ymd(fields['事故日'])
    if '画像鑑定' in fields or '画像鑑定' in case_name:
        ins['presence_date'] = '写真鑑定'  # 画像鑑定（立会なし）は「写真鑑定」と書く約束
    return {k: d for k, d in (('vehicle', v), ('customer', c), ('insurance', ins), ('hints', h)) if d}


def apply(header: dict, add: dict, overwrite: bool) -> list[str]:
    """header に足す（既存の値は上書きしない）。書いた項目名の一覧を返す"""
    wrote = []
    for sec, d in add.items():
        cur = header.get(sec) if isinstance(header.get(sec), dict) else {}
        for k, val in d.items():
            if overwrite or cur.get(k) in (None, ''):
                if cur.get(k) != val:
                    cur[k] = val
                    wrote.append(f'{sec}.{k}')
        header[sec] = cur
    return wrote


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('case_dir')
    ap.add_argument('src_dir')
    ap.add_argument('--report', default='')
    ap.add_argument('--overwrite', action='store_true')
    a = ap.parse_args()
    rep = a.report or find_report(a.src_dir)
    if not rep:
        print('報告書（速報・確報の PDF。文字層に 事故番号・型式類別・車台No. がある）が見つからない。header.json は手で書く')
        return 1
    pages = text_pages(rep, 1)
    fields = parse_report(pages[0] if pages else '')
    add = build(fields, os.path.basename(os.path.normpath(a.src_dir)))
    pdir = reading_pages.pages_dir(a.case_dir)
    os.makedirs(pdir, exist_ok=True)
    hp = os.path.join(pdir, 'header.json')
    header = reading_pages.load_json(hp) if os.path.exists(hp) else {}
    wrote = apply(header, add, a.overwrite)
    header['_auto_from'] = {'report': os.path.basename(rep), 'fields': wrote}
    reading_pages.save_json(hp, header)
    print(f'報告書: {os.path.basename(rep)}')
    v = add.get('vehicle', {})
    print('車両: ' + ' / '.join(f'{k}={v[k]}' for k in ('model_code', 'desig', 'category', 'reg_date', 'color_code', 'engine') if k in v)
          + (f" / グレード {add.get('hints', {}).get('grade_name')}" if add.get('hints', {}).get('grade_name') else ''))
    print(f'header.json に書いた項目 {len(wrote)}: ' + ', '.join(wrote))
    missing = [lb for lb in ('型式', '車台No.', '型式類別', '初度登録') if lb not in fields]
    if missing:
        print(f'★ 報告書に無い項目: {missing}（車検証から写す）')
    print('書かない項目: issuer（工場名）・est_date（見積日）・insurance.factory（工場名 電話。corpus_lookup の過去の書き方）・labor_rate')
    return 0


if __name__ == '__main__':
    sys.exit(main())
