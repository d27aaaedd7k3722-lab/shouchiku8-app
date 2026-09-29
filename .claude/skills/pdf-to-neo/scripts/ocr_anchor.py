# -*- coding: utf-8 -*-
"""ocr_anchor.py — コグニ印刷（書式 A）の見積 PDF を「罫線を消した OCR ＋ ADDATA 照合」で page_N.json に起こす。

転記（画像から 1 行ずつ写す）が PDF → NEO の時間の大半と写し違いの大半を占めていた（2026-09-28 の 2 案件）。
コグニ印刷の見積は **部品コードさえ読めれば 名称・品番・標準価格が ADDATA で決まる** ので、人が見るのは ADDATA と
食い違う行だけにする。

  1. ページ画像の表の罫線（縦線・横線）を消してから Windows 標準 OCR にかける
     （罫線が数字に接して先頭の桁が落ちていた: 4342 → '342'。消すとジムニーの部品コードが 30/30 行読めた。従来は 25/30）
  2. 縦線の位置で列（コード / 名称 / 修理方法・品番 / 部品価格 / 工賃 / 印）を決め、行ごとに OCR の語を列に振り分ける
  3. 部品コードを ADDATA で確かめる。この車に無いコードは OCR の読み違い（先頭の桁落ち・3↔8 など）を直した候補のうち、
     品番・金額・前後のコードの並びと合うものに直す
  4. 生成器（build_rows）で標準の名称・品番・単価を引き、OCR の品番・金額と突き合わせる
       - 品番: OCR が部分的にしか読めなくても、標準品番と似ていれば標準品番を採る。まったく違う品番は 要確認
       - 部品価格: 印（$ = 価格の手入力）が無ければ 標準単価 × 数量。OCR がそれと違う額を読んだときだけ 要確認
       - ページ小計が読めて、行の合計と一致すれば、その列の金額はまとめて確定（OCR の値でも一致していればよい）
       - 工賃・$ 付きの価格・手入力の行（部品コードなし）は ADDATA で確かめられないので、小計で確定しなければ 要確認
       - 名称: OCR の名称が ADDATA の名称と大きく違う行は「工場が書き換えた」かもしれないので 要確認（印字どおりなら neo_name に写す）
  5. 確かめる必要のある行だけ comment を `OCR未確認: <理由>` にする（reading_pages validate はこの印が残る行を FAIL にする）。
     その行の拡大画像を 1 枚にまとめた `pages/ocr/check_page_N.png` を作るので、それを見て直す

書式 A でないページ（縦線の並びが違う）は従来の ocr_prefill の推定にまかせる。塗装明細・費用の欄はまだ読まない（header に写す）。

使い方（files ディレクトリで）:
    PYTHONIOENCODING=utf-8 python .claude/skills/pdf-to-neo/scripts/ocr_anchor.py <見積PDF> <案件フォルダ> [--src <元案件フォルダ>] [--pages 1,2] [--overwrite] [--labor 9000]
前提: ADDATA 照合に車両が要る。--src を渡すと元案件フォルダの速報・確報（文字層のある報告書）から header.json の
      車両・顧客・保険を先に埋める（header_auto.py）。渡さないときは <案件>/pages/header.json の vehicle を先に書いておく。
      車両が無ければ照合せずに OCR の値だけで下書きする（全行 要確認）。見積書の「作成日」は header の est_date に書く。
出力:
    <案件>/pages/ocr/page_N.png / page_N.clean.png   OCR にかけた画像（罫線を消したもの）
    <案件>/pages/page_N.anchor.json                  行ごとの OCR の生の値・ADDATA の標準値・判定（監査用）
    <案件>/pages/page_N.json                         下書き（無いときだけ作る。--overwrite で上書き）
    <案件>/pages/ocr/check_page_N.png                要確認の行だけを縦に並べた画像
"""
from __future__ import annotations

import argparse
import difflib
import json
import os
import re
import statistics
import sys
import unicodedata
from typing import Optional

HERE = os.path.dirname(os.path.realpath(__file__))
sys.path.insert(0, HERE)
import skill_env  # noqa: E402
skill_env.apply()
sys.path.insert(0, os.path.join(skill_env.FILES, 'claude_neo_pipeline'))
import ocr_prefill  # noqa: E402
import reading_pages  # noqa: E402

UNVERIFIED = 'OCR未確認'
METHODS = ('脱着修理', '脱着板金', '脱着鈑金', '鈑金修正', '点検調整', '分解調整', '取替', '交換', '取換', '脱着', '取外', '取付', '板金', '鈑金',
           '修理', '補修', '修正', '点検', '調整', '診断', '分解')  # 生成器の DISPOSAL の語（長い語から）。印字どおりに写す
END_RE = re.compile(r'塗装費用|塗装明細|【塗装|【費用|明細】|【[^使流転共兼汎専再]用】|ページ小計|頁小計|ジ小計|次頁|前頁繰越|課税額計|消費税|御見積額')  # 見出しは OCR で崩れる（'【奘明細】' '【豊用】'）
FRAME_RE = re.compile(r'ランク|ﾗﾝｸ|基本内|基本修正')
END2_RE = re.compile(r'ページ小計|頁小計|ジ小計|次頁|前頁繰越|課税額計|消費税|御見積額')  # 区画（塗装明細・費用）の下端
# 塗装明細の行（見出しの「塗装費用計」が OCR で崩れても、ここから下は部品の明細ではない）
PAINT_NAME_RE = re.compile(r'塗装費用|塗装工賃|塗装材料|塗料|塗膜|加算基礎|ブース加算|材料代割合|材料代単価|材料代係数|明細】|費用計|工賃計|内訳')  # 見出しの字が崩れても（'【奘明細】' '塰費用計'）
PAINT_MID_RE = re.compile(r'dm|新品または|片側|両側|\(1/\d\)')  # 内板骨格修正の行（コグニ印刷は明細の続きに刷り、右端に n）
# 費用の名称（コグニの既定行 1〜8 と、実案件でよく出るもの）。OCR の崩れた名称をこれに寄せる。NEO_check の reading の費用名も足す（expense_vocab）
EXP_NAMES = ('文字書き費用', '内張り費用', '配線・配管費用', 'ショートパーツ', 'レッカー代１', 'レッカー代２', '写真代他', 'その他控除',
             '配線修理', '電子部品点検再設定', '交換部品等廃棄費用', '産業廃棄物処理委託料', '防錆処理', '塩害ガード', '代車費用', '洗車',
             'エーミング', '部品運賃', '廃棄物処理費用', '車両搬送費用', 'コーティング')
SUBTOTAL_RE = re.compile(r'ジ小計|頁小計|ページ計')  # 'ページ小計' は OCR で '-ジ小計' になりやすい
HEADER_RE = re.compile(r'修理方法|部品番号|修理項目|部品名称|部品価格|塗装項目|塗装面積|\(円\)')  # 表の見出し行（'コード' は車両欄の「カラーコード」にもあるので使わない）
NOISE_RE = re.compile(r'^[。、,.・′゛゜"\'`~\-ー―‐|｜/\\:;()（）\[\]「」]+$')
DIGIT_FIX = str.maketrans({'O': '0', 'o': '0', 'Q': '0', 'D': '0', 'I': '1', 'l': '1', '|': '1', 'i': '1', 'Z': '2', 'S': '5', 's': '5', 'B': '8', 'g': '0', 'q': '0'})  # FAX の '0' は 'q'・'g' に崩れる（'134,20q' = 134,200、'3581g81' = 35810-81…）
# 数字の読み違い（Windows OCR・FAX で実際に見たもの）。部品コードを直すときの候補
CONFUSE = {'0': '689', '1': '47', '2': '7', '3': '85', '4': '19', '5': '63', '6': '508', '7': '12', '8': '3065', '9': '84'}


def nfkc(s) -> str:
    return unicodedata.normalize('NFKC', str(s or ''))


# ---------------------------------------------------------------------- 罫線
def find_rules(img, band: int = 120, thr: int = 100) -> tuple[list, list]:
    """縦線・横線の断片を返す。画像を帯（band 画素）ごとに平均して、帯の全体にわたって黒い列（行）を線とみなす
    （文字は帯の半分も埋まらないので平均が暗くならない）。FAX の傾き（ページ全体で 20 画素ほど）は帯ごとに追う"""
    from PIL import Image  # type: ignore
    g = img.convert('L')
    W, H = g.size
    nb = max(1, H // band)
    v = g.resize((W, nb), Image.BOX).load()
    vert = []  # (x0, x1, y0, y1)
    for b in range(nb):
        x = 0
        while x < W:
            if v[x, b] < thr:
                x0 = x
                while x < W and v[x, b] < thr:
                    x += 1
                if x - x0 < 40:
                    vert.append((x0, x - 1, b * H // nb, (b + 1) * H // nb))
            x += 1
    nbx = max(1, W // band)
    h = g.resize((nbx, H), Image.BOX).load()
    hor = []
    for b in range(nbx):
        y = 0
        while y < H:
            if h[b, y] < thr:
                y0 = y
                while y < H and h[b, y] < thr:
                    y += 1
                if y - y0 < 40:
                    hor.append((b * W // nbx, (b + 1) * W // nbx, y0, y - 1))
            y += 1
    return vert, hor


def remove_rules(img):
    """罫線を白で塗った画像と、縦線の断片を返す"""
    from PIL import ImageDraw  # type: ignore
    vert, hor = find_rules(img)
    c = img.convert('L').copy()
    d = ImageDraw.Draw(c)
    for x0, x1, y0, y1 in vert:
        d.rectangle((x0 - 3, y0, x1 + 3, y1), fill=255)
    for x0, x1, y0, y1 in hor:
        d.rectangle((x0, y0 - 3, x1, y1 + 3), fill=255)
    return c, vert


def long_vlines(vert: list, H: int, min_cover: float = 0.25) -> list[dict]:
    """縦線の断片を、傾きを許してつなぎ、ページ高さの min_cover 以上ある線だけを返す（x の小さい順）。
    各線は {'x': 代表 x, 'pts': [(y 中心, x 中心)]}（その高さの x は x_at で引く）"""
    segs = sorted(((x0 + x1) / 2, (y0 + y1) / 2, y1 - y0) for x0, x1, y0, y1 in vert)
    lines: list[dict] = []
    for xc, yc, hh in segs:
        for ln in lines:
            if abs(ln['x'] - xc) <= 30:
                ln['pts'].append((yc, xc)); ln['len'] += hh
                ln['x'] = statistics.median(p[1] for p in ln['pts'])
                break
        else:
            lines.append({'x': xc, 'pts': [(yc, xc)], 'len': hh})
    out = [ln for ln in lines if ln['len'] >= H * min_cover]
    for ln in out:
        ln['pts'].sort()
    return sorted(out, key=lambda ln: ln['x'])


def x_at(line: dict, y: float) -> float:
    pts = line['pts']
    best = min(pts, key=lambda p: abs(p[0] - y))
    return best[1]


def layout_a(lines: list[dict], W: int) -> Optional[list[dict]]:
    """コグニ印刷（書式 A）の縦線の並び: 左枠 | コード | 名称 | 修理方法・品番 | 部品価格 | 工賃 | 印。
    幅の比で確かめ、合わなければ None（書式 A ではない）"""
    if len(lines) < 6:
        return None
    import itertools  # noqa: PLC0415
    best = None
    # 並びを保ったまま 6 本を選ぶ（表の途中の短い縦線 = 見出しの枠などを飛ばす。ハイエース C14の PDF 出力で 1 本混じっていた）。
    # 比が合う組のうち、線の長さの合計がいちばん長いもの
    for L in itertools.combinations(lines[:16], 6):
        w = [(L[k + 1]['x'] - L[k]['x']) / W for k in range(5)]
        if 0.025 <= w[0] <= 0.08 and 0.15 <= w[1] <= 0.35 and 0.2 <= w[2] <= 0.45 and 0.06 <= w[3] <= 0.18 and 0.06 <= w[4] <= 0.18:
            tot = sum(ln['len'] for ln in L)
            if best is None or tot > best[0]:
                best = (tot, list(L))
    return best[1] if best else None


COLS = ('code', 'name', 'mid', 'price', 'wage', 'mark')


def col_of(L: list[dict], xc: float, yc: float) -> Optional[str]:
    xs = [x_at(ln, yc) for ln in L]
    if xc < xs[0] - 10:
        return None
    for k in range(5):
        if xc < xs[k + 1]:
            return COLS[k]
    return 'mark' if xc < xs[5] + (xs[5] - xs[4]) * 0.6 else None


# ---------------------------------------------------------------------- 行
def _substantial(t: str) -> bool:
    t = nfkc(t).strip()
    return bool(t) and not NOISE_RE.match(t)


def text_rows(words: list[dict]) -> list[dict]:
    """語を y でまとめた「行」（ページ全体。見出し・区切りの検出用）"""
    hs = [w['h'] for w in words if w['h'] > 0 and _substantial(w['text'])]
    tol = max(8, statistics.median(hs) * 0.6) if hs else 14
    rows: list[dict] = []
    for w in sorted(words, key=lambda w: w['y'] + w['h'] / 2):
        cy = w['y'] + w['h'] / 2
        if rows and abs(rows[-1]['y'] - cy) <= tol:
            rows[-1]['w'].append(w); rows[-1]['y'] = statistics.mean(v['y'] + v['h'] / 2 for v in rows[-1]['w'])
        else:
            rows.append({'y': cy, 'w': [w]})
    for r in rows:
        r['w'].sort(key=lambda w: w['x'])
        r['text'] = nfkc(''.join(w['text'] for w in r['w'])).replace(' ', '')
    return rows


def detail_region(trows: list[dict], L: list[dict], H: int) -> tuple[float, float, Optional[dict]]:
    """明細（部品の行）の上端・下端と、ページ小計の行"""
    top = None
    # 表の見出しの行 = 見出しの語が 2 つ以上ある行（注記「部品番号・価格再度確認」の '部品番号' 1 語で上の車両欄まで明細にしていた）。
    # 2 語の行が無ければ（FAX で崩れた）1 語の最初の行
    _hits = [(len(set(HEADER_RE.findall(r['text']))), r) for r in trows]
    _two = next((r for n_, r in _hits if n_ >= 2), None)
    _one = next((r for n_, r in _hits if n_ >= 1), None)
    if _two is not None or _one is not None:
        top = (_two if _two is not None else _one)['y'] + 20
    if top is None:
        top = min((p[0] for p in L[1]['pts']), default=0)
    # 表の下端 = 名称と修理方法の間の縦線の終わり（ページ小計の枠・部品価格適応日の行は表の外。'ページ小計' の字は OCR で崩れやすい）
    table_end = max((p[0] for p in L[2]['pts']), default=H) + 100  # 線の終わりは 120 画素の帯の中心なので最大 60 画素浅い（最後の行が切れていた: ハイエース C14）。ページ小計の行は END_RE で止まる
    bottom, sub = table_end, None
    for r in trows:
        if r['y'] <= top:
            continue
        if END_RE.search(r['text']):
            bottom = min(bottom, r['y'] - 20)
            break
    for r in trows:
        if r['y'] > top and SUBTOTAL_RE.search(r['text']):
            sub = r
            break
    if sub is None:  # 見出しの字が崩れていても、表のすぐ下で金額の欄に数字がある行は ページ小計
        for r in trows:
            if table_end - 60 < r['y'] < table_end + 200 and re.search(r'計|小|ジ|頁', r['text']) and any(
                    col_of(L, w['x'] + w['w'] / 2, r['y']) in ('price', 'wage') and re.search(r'\d', w['text']) for w in r['w']):
                sub = r
                break
    return top, bottom, sub


def slots_of(words: list[dict], L: list[dict], top: float, bottom: float) -> list[dict]:
    """明細の範囲の語を行（slot）にまとめ、列に振り分ける"""
    inreg = []
    for w in words:
        cy = w['y'] + w['h'] / 2
        if not (top < cy < bottom):
            continue
        c = col_of(L, w['x'] + w['w'] / 2, cy)
        if c:
            inreg.append(dict(w, cy=cy, col=c))
    code_y = sorted(w['cy'] for w in inreg if w['col'] == 'code' and re.search(r'\d', w['text']))
    diffs = [b - a for a, b in zip(code_y, code_y[1:]) if b - a > 20]
    hs = [w['h'] for w in inreg if _substantial(w['text'])]
    pitch = statistics.median(diffs) if diffs else (statistics.median(hs) * 2 if hs else 86)
    tol = pitch * 0.42
    slots: list[dict] = []
    for w in sorted((w for w in inreg if _substantial(w['text'])), key=lambda w: w['cy']):
        if slots and abs(slots[-1]['y'] - w['cy']) <= tol:
            s = slots[-1]; s['w'].append(w); s['y'] = statistics.mean(v['cy'] for v in s['w'])
        else:
            slots.append({'y': w['cy'], 'w': [w]})
    for w in inreg:  # 記号（。、）は近い行へ（名称の濁点・印の $ # * を落とさない）
        if _substantial(w['text']):
            continue
        near = min(slots, key=lambda s: abs(s['y'] - w['cy']), default=None)
        if near is not None and abs(near['y'] - w['cy']) <= tol:
            near['w'].append(w)
    for s in slots:
        s['pitch'] = pitch
        for c in COLS:
            ws = sorted((w for w in s['w'] if w['col'] == c), key=lambda w: w['x'])
            s[c] = nfkc(''.join(w['text'] for w in ws)).replace(' ', '')
    return slots


def _filled(d) -> bool:
    """header の欄に中身があるか（reading_pages init の雛形は totals の値が全部 None・paint が {}。雛形は空とみなす。Codex 指摘）"""
    if not isinstance(d, dict):
        return bool(d)
    return any(v not in (None, '', [], {}) for k, v in d.items() if not str(k).startswith('_'))


def split_mark(t: str) -> tuple[str, str]:
    """金額の欄の後ろにくっついた印（'21,880$' '21,880S'）を分ける。S は $ の読み違い（数字の後ろの S だけ）。戻り値 (金額の字, 印)"""
    m = re.search(r'(?<=[\d,])\s*([$S＄#*@]+)\s*$', nfkc(t))
    if not m:
        return t, ''
    return nfkc(t)[:m.start()], m.group(1).replace('S', '$').replace('＄', '$')


def tentative(t: str) -> Optional[int]:
    """読みの決まらない欄の「仮の値」: 欄の字から数字だけを拾う（'?3000' '3印00' → 3000 / 300 …）。
    仮の値は、それを入れた合計がページ小計と一致したときだけ採る（confirm_by_subtotal）"""
    d = re.sub(r'\D', '', nfkc(t).translate(DIGIT_FIX))
    return int(d) if 1 <= len(d) <= 8 else None


def _money_text(t: str) -> tuple[Optional[int], bool]:
    """OCR の金額欄 → (値, きれいに読めたか)。'1,800' '32,000' → 値。'1町000' のような混じり物は (None, False)"""
    t = nfkc(t).replace(' ', '')
    if not t:
        return None, True
    t2 = re.sub(r'[,.、，]', '', t.translate(DIGIT_FIX))
    if re.fullmatch(r'\d{1,8}', t2):
        clean = bool(re.fullmatch(r'[0-9,.、，]+', t))  # 数字と区切りだけ（カンマの落ち '34200' は構わない。'1町000' のような字の混じりは読み違い）
        return int(t2), clean
    return None, False


def parse_mid(t: str) -> dict:
    """修理方法・品番の欄: '取替71811ー77R10ー5PK(02)' → method / parts_no / qty"""
    t = nfkc(t)
    out = {'method': '', 'parts_no': '', 'qty': None, 'area': '', 'index': ''}
    for m in METHODS:
        if m in t:
            out['method'] = m
            t = t.replace(m, '', 1)
            break
    else:
        head = t[:3]
        if '替' in head or head.startswith('取'):
            out['method'] = '取替'
        elif '着' in head or '脱' in head:
            out['method'] = '脱着'
        elif '板' in head or '鈑' in head or head.startswith('金'):
            out['method'] = '板金'
        elif '修' in head:
            out['method'] = '修理'
    m = re.search(r'\((\d{1,3})\)', t)
    if m:
        out['qty'] = int(m.group(1)); t = t[:m.start()] + t[m.end():]
    m = re.search(r'(\d+(?:\.\d+)?)\s*dm', t)
    if m:
        out['area'] = m.group(1)
    # 指数は欄の右端に 'd.dd'（コグニ印刷の C-HR 書式）。品番に続けて読まれるので末尾から切る。
    # 区切りが '-' に化けた読み（'48530ー80A312-70'）は、残りが 5-5 の品番の形になるときだけ指数とみなす
    t2 = re.sub(r'\s+', '', t)
    m = None
    for k in (1, 2):  # 整数部 1 桁を先に（'101303,80' は 10130 + 3.80）。残りが品番の形にならなければ 2 桁（12.50）
        mk = re.search(r'(\d{%d})[.,](\d{2})$' % k, t2)
        rest = t2[:mk.start()] if mk else ''
        if mk and (not re.search(r'\d', rest) or re.search(r'[0-9A-Z]{5}[-ー―~][0-9A-Z]{5}([-ー―][0-9A-Z]{1,5})?$', rest)):
            m = mk
            break
        m = m or mk
    if not m:
        m2 = re.search(r'(\d)[-ー](\d{2})$', t2)
        if m2 and re.fullmatch(r'[0-9A-Z]{5}[-ー―][0-9A-Z]{5}', t2[:m2.start()]):
            m = m2
    if m:
        out['index'] = f'{int(m.group(1))}.{m.group(2)}'
        t = t2[:m.start()]
    s = re.sub(r'[ー―‐−~〜ｰ一_]', '-', t)
    s = re.sub(r'[^0-9A-Za-z\-/]', '', s).upper().strip('-')  # '/' はタイヤの品番（195/80R15 107/105）
    out['parts_no'] = s
    return out


def _kana_skel(s: str) -> str:
    """名称の骨格（濁点・小書き・記号・左右・Fr/Rr を落とす）。OCR の名称は濁点が落ちやすい"""
    t = nfkc(s)
    t = unicodedata.normalize('NFD', t)
    t = ''.join(ch for ch in t if ch not in '゙゚')
    t = t.translate(str.maketrans('ァィゥェォッャュョヮ', 'アイウエオツヤユヨワ'))
    t = re.sub(r'^(左|右)', '', t)
    t = re.sub(r'(?i)\b(fr|rr)', '', t)
    return re.sub(r'[^ア-ンA-Za-z0-9一-龥]', '', t).upper()


# 工場が名称に足す・消す語の漢字（2026-09-28 シエンタ: 'ﾙｰﾌﾍｯﾄﾞﾗｲﾆﾝｸﾞ一部脱着'・'ﾙｰﾌﾊﾟﾈﾙﾋﾝｼﾞ取付け部'・'ｻｰﾄﾞｼｰﾄ'（ADDATA は (脱着･修理)））。
# OCR が半角カナを崩して出す漢字（工・力・刀・加・叩・万 …）は入れない
RENAME_KANJI = set('一部脱着取付修理正交換塗装外内側込含調整分解点検補再使用中古品新純材料費代')


def renamed_hint(ocr_name: str, std_name: str) -> str:
    """OCR の名称と ADDATA の名称で、書き換えの語の漢字が 2 字以上違えば その字（足された字 / 消えた字）を返す。違わなければ ''"""
    a = {ch for ch in nfkc(ocr_name) if ch in RENAME_KANJI}
    b = {ch for ch in nfkc(std_name) if ch in RENAME_KANJI}
    add, gone = a - b, b - a
    if len(add) + len(gone) >= 2:
        return ('足された字 ' + ''.join(sorted(add)) if add else '') + (' / ' if add and gone else '') + ('消えた字 ' + ''.join(sorted(gone)) if gone else '')
    return ''


def name_similarity(ocr_name: str, std_name: str) -> float:
    a, b = _kana_skel(ocr_name), _kana_skel(std_name)
    if not a or not b:
        return 1.0
    return difflib.SequenceMatcher(None, a, b).ratio()


PN_CONFUSE = [set('0ODQCG'), set('1IL7'), set('5S6'), set('6CG'), set('8B3'), set('2Z')]  # FAX の '0'/'6' は 'C'・'G' にもなる（C-HR 90189-06006 → 90189CC006）


def pn_ocr_confusable(ocr_pn: str, std_pn: str) -> bool:
    """まるごと読めた品番と標準品番の違いが、OCR の読み違いの組（0/O/D、1/I/7、5/S/6、8/B/3、2/Z）だけで説明できるか。
    色違いの末尾（-A0 / -C0）のような違いは説明できない → 印字どおりを採るか人に見せる"""
    a = re.sub(r'[^0-9A-Z]', '', ocr_pn.upper()); b = re.sub(r'[^0-9A-Z]', '', std_pn.upper())
    if a == b:
        return True
    if len(a) != len(b):
        return False
    return all(x == y or any(x in g and y in g for g in PN_CONFUSE) for x, y in zip(a, b))


def edit_distance(a: str, b: str) -> int:
    """編集距離（字の置き換え・抜け・余りの数）"""
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(min(prev[j] + 1, cur[j - 1] + 1, prev[j - 1] + (ca != cb)))
        prev = cur
    return prev[-1]


def pn_ocr_noise(ocr_pn: str, std_pn: str) -> bool:
    """まるごと読めたように見える品番の違いが、FAX の OCR の崩れ（2 字以内の置き換え・抜け・ハイフンのずれ）で、
    末尾の枝番（3 つ以上に区切られた品番の最後。色・仕様: -C7 / -A0 / -5PK）は同じか。枝番が違えば別の部品（色違い）かもしれない"""
    a = re.sub(r'[^0-9A-Z]', '', ocr_pn.upper().translate(str.maketrans({'O': '0'})))
    b = re.sub(r'[^0-9A-Z]', '', std_pn.upper())
    segs = [x for x in std_pn.upper().split('-') if x]
    if len(segs) >= 3 and not a.endswith(segs[-1].replace('O', '0')):
        return False
    return edit_distance(a, b) <= 2


def pn_similarity(ocr_pn: str, std_pn: str) -> float:
    a = re.sub(r'[^0-9A-Z]', '', ocr_pn.upper().translate(str.maketrans({'O': '0', 'I': '1'})))
    b = re.sub(r'[^0-9A-Z]', '', std_pn.upper())
    if not a or not b:
        return 0.0
    if a == b:
        return 1.0
    sm = difflib.SequenceMatcher(None, a, b)
    return max(sm.ratio(), sum(bl.size for bl in sm.get_matching_blocks()) / max(len(a), 1) * (0.9 if len(a) >= 5 else 0.5))


# ---------------------------------------------------------------------- ADDATA
class Anchor:
    """車両を決めて、部品コードの妥当性と標準値（名称・品番・単価）を引く"""

    def __init__(self, header: dict, labor: Optional[int]):
        self.ok = False
        self.why = ''
        self.labor = labor
        v = header.get('vehicle') or {}
        if not isinstance(v, dict) or not any(v.get(k) for k in ('desig', 'serial_no', 'model_code', 'car_code')):
            self.why = 'header.json に vehicle（型式指定・類別・車台番号）が無い'
            return
        import estimate_to_neo as e  # noqa: PLC0415
        self.e = e
        self.nb = e.NeoBuilder()
        hints = e._norm_hint_flags(header.get('hints') or {})
        self.hints = hints
        try:
            veh = self.nb.resolve_vehicle(v, hints)
        except Exception as ex:  # noqa: BLE001
            self.why = f'車両特定に失敗（{type(ex).__name__}: {ex}）'
            return
        self.car = veh.get('neo_car') or {}
        self.confidence = veh.get('confidence')
        if not self.car.get('CarCode'):
            self.why = '車両特定で候補が無い'
            return
        self.parts = e.AddataParts(self.nb.engine, self.car['CarCode'])
        p = self.parts
        # 右の部品（左右ペアの右 ref）は 12.DB の行が左にしか無いことがある（ジムニー 3860・4310）。生成器の _find_ref_core と同じ範囲を有効にする
        self.valid = {int(k) for k in p.p12.keys()} | {int(k) for k in p.by_ref.keys()} | {int(k) for k in p.pair_left.keys()} | {int(v) for v in p.pair_right.values()}
        self.nb._row_ctx = self.nb.make_row_ctx(self.car, hints)
        self.ok = True

    def _recs(self, ref: int) -> list:
        return (self.parts.by_ref.get(ref) or []) + (self.parts.by_ref.get(self.parts.pair_left.get(ref, -1)) or [])  # 右 ref は左の行も見る

    def unit_prices(self, ref: int) -> set[int]:
        return {int(r.get('price') or 0) for r in self._recs(ref) if int(r.get('price') or 0) > 0}

    def variant_recs(self, ref: int) -> list[tuple[str, int]]:
        """この部品の品番の変種と単価（11.DB と 83/13.DB の色別部品）"""
        out = [(str(r.get('parts_no') or ''), int(r.get('price') or 0)) for r in self._recs(ref) if r.get('parts_no')]
        try:
            r83 = self.parts._load_83_raw()
            for k in (ref, self.parts.pair_left.get(ref, -1)):
                out += [(str(r.get('pn') or ''), int(r.get('price') or 0)) for r in (r83.get(k) or []) if r.get('pn')]
        except Exception:  # noqa: BLE001
            pass
        return out

    def std_name(self, ref: int) -> str:
        """この部品の ADDATA の名称（コグニの表示形。右の部品は左の名称で代用）"""
        n20s = self.parts.name20_by_ref.get(ref) or self.parts.name20_by_ref.get(self.parts.pair_left.get(ref, -1)) or set()
        return self.e.cogni_parts_names(sorted(n20s)[0])[0] if n20s else ''

    def pns(self, ref: int) -> set[str]:
        out = {str(r.get('parts_no') or '') for r in self._recs(ref) if r.get('parts_no')}
        try:  # 色別・期間別部品（83/13.DB）の品番も ADDATA にある品番として扱う（シエンタ 4730 64716-52180-C0: 11.DB は A0）
            r83 = self.parts._load_83_raw()
            for k in (ref, self.parts.pair_left.get(ref, -1)):
                out |= {str(r.get('pn') or '') for r in (r83.get(k) or []) if r.get('pn')}
        except Exception:  # noqa: BLE001
            pass
        return out

    def code_candidates(self, raw: str) -> list[int]:
        d = re.sub(r'\D', '', raw.translate(DIGIT_FIX))
        cands: list[str] = []
        if len(d) == 4:
            cands.append(d)
            for i, ch in enumerate(d):
                for alt in CONFUSE.get(ch, ''):
                    cands.append(d[:i] + alt + d[i + 1:])
        elif len(d) == 3:
            cands += [p + d for p in '123456789']
            cands += [d[:i] + x + d[i:] for i in (1, 2, 3) for x in '0123456789']
        elif len(d) == 5:
            cands += [d[:i] + d[i + 1:] for i in range(5)]
        seen, out = set(), []
        for c in cands:
            if len(c) == 4 and int(c) in self.valid and c not in seen:
                seen.add(c); out.append(int(c))
        return out

    def standards(self, items: list[dict]) -> list[Optional[dict]]:
        """build_rows で標準値を引く（items と同じ順・同じ長さ。引けない行は None）"""
        def run(its):
            gen, _st = self.nb.build_rows([dict(it) for it in its], self.car['CarCode'], self.labor or 8000)
            main = [g for g in gen if g.get('PartsCodeSub') in (-1, None)]
            out, k = [], 0
            for it in its:
                while k < len(main) and str(main[k].get('PartsCode') or '').strip() != it['code']:
                    k += 1
                out.append(main[k] if k < len(main) else None)
                k += 1
            return out
        try:
            return run(items)
        except Exception:  # noqa: BLE001  1 行の不整合で全体が引けないときは 1 行ずつ
            res = []
            for it in items:
                try:
                    res.append(run([it])[0])
                except Exception:  # noqa: BLE001
                    res.append(None)
            return res


def decide_codes(slots: list[dict], an: Optional[Anchor]) -> None:
    """各行の部品コードを決める（s['code4'] / s['code_why']）。
    OCR のコードがこの車に有り、並び（前後のコードの間）か名称が合えばそのまま。並びも名称も合わない（'5000' を '6000' と読んだ）、
    この車に無い（'342' = 4342）、2 桁しか読めない（'30' = 3810）ときは、候補を 品番・金額・名称・並び で採点して選ぶ"""
    raw = [re.sub(r'\D', '', nfkc(s['code']).translate(DIGIT_FIX)) if s.get('kind', 'part') == 'part' else '' for s in slots]
    for i, s in enumerate(slots):
        s['code4'], s['code_why'] = '', ''
        d = raw[i]
        if not d:
            continue
        if an is None or not an.ok:
            s['code4'] = d if len(d) == 4 else ''
            s['code_why'] = '' if len(d) == 4 else f'部品コードが 4 桁で読めない（{d}）'
            continue
        prev = next((int(slots[j]['code4']) for j in range(i - 1, -1, -1) if slots[j].get('code4')), None)
        nxt = next((int(raw[j]) for j in range(i + 1, len(slots)) if len(raw[j]) == 4 and int(raw[j]) in an.valid and (prev is None or int(raw[j]) > prev)), None)
        mid = s.get('_mid') or parse_mid(s['mid'])
        price, _ = _money_text(s['price'])
        qty = mid['qty'] or 1

        def in_order(c):
            return (prev is None or prev < c) and (nxt is None or c < nxt)

        def evidence(c):
            ev = 0.0
            if mid['parts_no'] and any(pn_similarity(mid['parts_no'], p) >= 0.8 for p in an.pns(c)):
                ev += 3
            if price and any(u * qty == price for u in an.unit_prices(c)):
                ev += 2
            return ev

        def nsim(c):
            return name_similarity(s['name'], an.std_name(c)) if _kana_skel(s['name']) else 0.0

        if len(d) == 4 and int(d) in an.valid:
            c0 = int(d)
            if evidence(c0) >= 2 or nsim(c0) >= 0.5:
                s['code4'] = d
                continue
            if in_order(c0) and not [c for c in an.code_candidates(d) if c != c0 and in_order(c) and (evidence(c) >= 2 or nsim(c) >= 0.5)]:
                s['code4'] = d  # 並びは合うが、品番・金額・名称の裏付けが無い（名称が読めない・品番も金額も無い行）: 人に回す（Codex 指摘）
                s['code_why'] = f'部品コード {d} は ADDATA にあり並びも合うが、品番・金額・名称で裏付けが取れない'
                continue
            alts = [c for c in an.code_candidates(d) if c != c0 and in_order(c)]
            best = max(alts, key=lambda c: evidence(c) + 2 * nsim(c), default=None)
            if best is not None and evidence(best) + 2 * nsim(best) >= evidence(c0) + 2 * nsim(c0) + 1 and nsim(best) >= 0.5:
                s['code4'] = f'{best:04d}'; s['code_fixed'] = d
                if evidence(best) < 2:
                    s['code_why'] = f'部品コードを OCR の {d} から {s["code4"]} に直した（並びと名称が根拠）'
            else:
                s['code4'] = d
            continue
        cands = an.code_candidates(d)
        if len(d) <= 2 and (prev is not None or nxt is not None):  # 2 桁しか読めない: 並びの範囲で、読めた数字を順に含むコード
            pat = re.compile('.*'.join(d))
            cands = [c for c in sorted(an.valid) if in_order(c) and pat.search(f'{c:04d}')]
        scored = []
        for c in cands:
            sc = evidence(c) + (1 if in_order(c) else 0) + (2 * nsim(c) if nsim(c) >= 0.5 else 0)
            scored.append((sc, c))
        scored.sort(reverse=True)
        if scored and scored[0][0] >= 1 and (len(scored) == 1 or scored[0][0] > scored[1][0] + 0.3):
            s['code4'] = f'{scored[0][1]:04d}'
            s['code_fixed'] = d
            if evidence(scored[0][1]) < 2:  # 品番か金額で裏が取れていない
                s['code_why'] = f'部品コードを OCR の {d} から {s["code4"]} に直した（並び・名称が根拠）'
        else:
            s['code4'] = d if len(d) == 4 else ''
            s['code_why'] = f'部品コード {d} がこの車の ADDATA に無い' + (f'（候補 {", ".join(f"{c:04d}" for _, c in scored[:4])}）' if scored else '')


# ---------------------------------------------------------------------- 1 ページ
STRICT_MONEY = re.compile(r'\d{1,3}(,\d{3})*')  # コグニ印刷の金額は 1,000 以上に必ずカンマ（'2000' は 1 桁落ちの読み: 4315 の 20,000）


def _strip_lines(tile):
    """切り出した欄の中の線（行・列の 6 割以上が黒）を白で塗る。ページ小計の小さな枠は表の罫線の検出（120 画素の帯）に掛からず残る"""
    from PIL import Image, ImageDraw  # type: ignore
    w, h = tile.size
    t = tile.copy()
    d = ImageDraw.Draw(t)
    rows = tile.resize((1, h), Image.BOX).load()
    for y in range(h):
        if rows[0, y] < 100:
            d.line((0, y, w, y), fill=255)
    cols = tile.resize((w, 1), Image.BOX).load()
    for x in range(w):
        if cols[x, 0] < 100:
            d.line((x, 0, x, h), fill=255)
    return t


def _variants(tile):
    """読み直しに使う前処理（拡大率 × 白黒化 / 太らせる）。2026-09-28 シエンタ FAX で、崩れた 5 欄すべてが多数決で正しく読めた組"""
    from PIL import Image, ImageFilter  # type: ignore
    out = []
    for z in (1.0, 1.5, 2.0, 3.0):
        t = tile.resize((max(1, int(tile.size[0] * z)), max(1, int(tile.size[1] * z))), Image.LANCZOS)
        if z != 1.0:
            out.append(t.point(lambda v: 0 if v < 170 else 255))
        if z != 3.0:
            out.append(t.filter(ImageFilter.MinFilter(3)))
    return out


def reocr_cells(img, boxes: list[tuple]) -> list[list[str]]:
    """欄（x0, y0, x1, y1）を切り出し、前処理を変えた数枚を縦に並べた画像で OCR し直す（高さ 4,000 画素ごとに 1 回の呼び出し）。
    戻り値 = 欄ごとの読みの一覧（前処理の数だけ）"""
    from PIL import Image  # type: ignore
    import tempfile  # noqa: PLC0415
    if not boxes:
        return []
    tiles = []  # (欄の番号, 画像)
    for k, (x0, y0, x1, y1) in enumerate(boxes):
        base = _strip_lines(img.crop((int(x0), int(y0), int(x1), int(y1))).convert('L'))
        tiles += [(k, v) for v in _variants(base)]
    gap = 80
    out: list[list[str]] = [[] for _ in boxes]
    chunk: list = []

    def flush(ch):
        if not ch:
            return
        W = max(t.size[0] for _, t in ch) + 160
        H = sum(t.size[1] + gap for _, t in ch) + gap
        comp = Image.new('L', (W, H), 255)
        spans, y = [], gap
        for k, t in ch:
            comp.paste(t, (80, y)); spans.append((k, y, y + t.size[1])); y += t.size[1] + gap
        fd, tmp = tempfile.mkstemp(suffix='.png'); os.close(fd)
        try:
            comp.save(tmp)
            words = ocr_prefill.run_ocr(tmp)
        finally:
            try:
                os.remove(tmp)
            except OSError:
                pass
        for k, y0, y1 in spans:
            ws = sorted((w for w in words if y0 - gap / 2 < w['y'] + w['h'] / 2 < y1 + gap / 2), key=lambda w: w['x'])
            out[k].append(nfkc(''.join(w['text'] for w in ws)).replace(' ', ''))

    h = 0
    for k, t in tiles:
        if chunk and h + t.size[1] + gap > 4000:
            flush(chunk); chunk, h = [], 0
        chunk.append((k, t)); h += t.size[1] + gap
    flush(chunk)
    return out


def ink_extent(img, box) -> float:
    """欄の中の字の左端から右端までの幅（画素）。字が無ければ 0"""
    from PIL import Image  # type: ignore
    x0, y0, x1, y1 = [int(v) for v in box]
    if x1 <= x0 or y1 <= y0:
        return 0.0
    col = img.crop((x0, y0, x1, y1)).convert('L').resize((x1 - x0, 1), Image.BOX).load()
    dark = [x for x in range(x1 - x0) if col[x, 0] < 235]
    return float(dark[-1] - dark[0] + 1) if dark else 0.0


def money_len_ok(v: Optional[int], n_est: Optional[float]) -> bool:
    """金額の字数（カンマ込み）が、インクの幅から見積もった字数と合うか（見積もりが無ければ合うとみなす）"""
    if v is None or not n_est:
        return True
    return abs(len(f'{v:,}') - n_est) <= 0.8


def money_votes(texts: list[str]) -> dict:
    """読みごとの票（カンマの位置が正しい読みだけ）"""
    votes: dict = {}
    for t in texts:
        t2 = re.sub(r'[$#*@nｎ\s]', '', t).translate(DIGIT_FIX).replace('.', ',').replace('、', ',').replace('，', ',')
        if STRICT_MONEY.fullmatch(t2):
            v = int(t2.replace(',', ''))
            votes[v] = votes.get(v, 0) + 1
    return votes


def vote_money(texts: list[str]) -> tuple[Optional[int], int, str]:
    """読みの多数決。カンマの位置が正しい読み（STRICT_MONEY）だけを数える。戻り値 = (値, 票数, 印の文字)"""
    marks = ''.join(ch for t in texts for ch in t if ch in '$#*@')
    votes = money_votes(texts)
    if not votes:
        return None, 0, marks
    best = sorted(votes.items(), key=lambda kv: -kv[1])
    if len(best) > 1 and best[1][1] == best[0][1]:
        return None, 0, marks  # 同票は決めない
    return best[0][0], best[0][1], marks


def second_pass(clean_img, L: list[dict], slots: list[dict], sub: Optional[dict], exact: bool = False) -> dict:
    """崩れた金額・印の欄と、ページ小計の欄を読み直す。読み直しで きれいな数字 になった欄だけ置き換える。戻り値 = ページ小計。
    exact（文字層の字）のときは読み直さず、小計は字のまま"""
    if exact:
        subtotal: dict = {'_cands': {}, '_nest': {}}
        if sub is not None:
            for c in ('price', 'wage'):
                ws = sorted((w for w in sub['w'] if col_of(L, w['x'] + w['w'] / 2, sub['y']) == c), key=lambda w: w['x'])
                v, _clean = _money_text(''.join(w['text'] for w in ws))
                if v is not None:
                    subtotal['parts' if c == 'price' else 'wage'] = v
        return subtotal
    boxes, where = [], []
    cells = []  # (slot, 列, 欄, 字の幅, OCR の字)
    for s in slots:
        yc, ph = s['y'], s['pitch']
        xs = [x_at(ln, yc) for ln in L]
        for col, a, b in (('price', 3, 4), ('wage', 4, 5)):
            raw = re.sub(r'[$#*@nｎ]', '', s[col])
            box = (xs[a] + 6, yc - ph * 0.45, xs[b] - 6, yc + ph * 0.45)
            tb = (box[0], yc - ph * 0.3, box[2], yc + ph * 0.3)
            cells.append((s, col, box, ink_extent(clean_img, tb) if ink(clean_img, tb, ph * 0.22) > 0 else 0.0, raw))
    extra = []  # (slot, 'method' | 'mark', 欄)
    for s in slots:
        yc, ph = s['y'], s['pitch']
        xs = [x_at(ln, yc) for ln in L]
        mbox = (xs[2] + 4, yc - ph * 0.45, xs[2] + (xs[3] - xs[2]) * 0.14, yc + ph * 0.45)
        if not parse_mid(s['mid'])['method'] and ink(clean_img, (mbox[0], yc - ph * 0.3, mbox[2], yc + ph * 0.3), ph * 0.22) > 0.004:
            extra.append((s, 'method', mbox))
        kbox = (xs[5] + 4, yc - ph * 0.45, xs[5] + (xs[5] - xs[4]) * 0.5, yc + ph * 0.45)
        if not re.search(r'[$#*@]', s['mark']) and ink(clean_img, (kbox[0], yc - ph * 0.3, kbox[2], yc + ph * 0.3), ph * 0.16) > 0.004:
            # 記号 1 字だけを切り出すと OCR は何も返さない。左の金額と続けて読ませる（C-HR で 9 行中 9 行の印の有無が正しく読めた）
            left = xs[4] + (xs[5] - xs[4]) * 0.35 if re.search(r'\d', s['wage']) else xs[3] + (xs[4] - xs[3]) * 0.35
            extra.append((s, 'mark', (left, kbox[1], kbox[2], kbox[3])))
    # 1 字の幅 = きれいに読めた金額（3 字以上）の「字の幅 ÷ 字数」の中央値（コグニ印刷は等幅。カンマも 1 字分）
    per = [w / len(nfkc(r)) for _s, _c, _b, w, r in cells if w > 0 and len(nfkc(r)) >= 3 and STRICT_MONEY.fullmatch(nfkc(r))]
    char_w = statistics.median(per) if len(per) >= 3 else None
    for s, col, box, w, raw in cells:
        v, clean = _money_text(raw)
        n_est = (w / char_w) if (char_w and w > 0) else None
        s.setdefault('_nest', {})[col] = round(n_est, 1) if n_est else None
        strict = bool(STRICT_MONEY.fullmatch(nfkc(raw).replace('.', ',')))
        if (v is not None and not (clean and strict and money_len_ok(v, n_est))) or (v is None and w > 0):
            boxes.append(box); where.append((s, col))
    sub_nest: dict = {}
    if sub is not None:
        xs = [x_at(ln, sub['y']) for ln in L]
        hh = statistics.median([w['h'] for w in sub['w'] if _substantial(w['text'])] or [40])
        for col, a, b in (('price', 3, 4), ('wage', 4, 5)):  # 上下は字の高さの 0.7 倍まで（すぐ下の「部品価格適応日」の行を入れない）
            box = (xs[a] + 6, sub['y'] - hh * 0.7, xs[b] - 6, sub['y'] + hh * 0.7)
            boxes.append(box); where.append((None, col))
            wpx = ink_extent(_strip_lines(clean_img.crop(tuple(int(v) for v in box)).convert('L')), (0, 0, int(box[2] - box[0]), int(box[3] - box[1])))
            if char_w and wpx:
                sub_nest['parts' if col == 'price' else 'wage'] = wpx / char_w
    texts = reocr_cells(clean_img, boxes + [b for _s, _k, b in extra])
    for (s, kind, _b), tt in zip(extra, texts[len(boxes):]):
        s.setdefault('_reocr', {})[kind] = tt
        if kind == 'method':
            from collections import Counter  # noqa: PLC0415
            top = Counter(g for g in (parse_mid(t)['method'] for t in tt) if g).most_common(2)
            best = top[0][0] if top and top[0][1] >= 2 and (len(top) == 1 or top[0][1] > top[1][1]) else ''
            if best:
                s['mid'] = best + s['mid']
        else:
            chars = {}
            for t in tt:
                for ch in set(nfkc(t).replace('S', '$').replace('＄', '$')):
                    if ch in '$#*@':
                        chars[ch] = chars.get(ch, 0) + 1
            got = ''.join(ch for ch in '$#*@' if chars.get(ch, 0) >= 2)
            if got:
                s['mark'] = s['mark'] + got
    texts = texts[:len(boxes)]
    subtotal: dict = {'_cands': {}, '_nest': sub_nest}
    for (s, col), tt in zip(where, texts):
        v, n, _m = vote_money(tt)
        if s is None:
            k = 'parts' if col == 'price' else 'wage'
            subtotal['_cands'][k] = set(money_votes(tt))  # 1 票でも出た読み。行の合計と一致すればその値を小計とみなす（3/8・5/6 の取り違え）
            if v is not None and n >= 2:
                subtotal[k] = v
            continue
        s.setdefault('_reocr', {})[col] = tt
        if v is not None and n >= 2 and not money_len_ok(v, (s.get('_nest') or {}).get(col)):
            s[col] = '?' + s[col]  # 多数決の値も字数が合わない（桁落ち）: 読めない欄として人に回す
            continue
        if v is not None and n >= 2:
            s[col] = f'{v:,}' + ''.join(ch for ch in s[col] if ch in '$#*@')  # 印は元の欄の文字として残す（judge が拾う）
            s.setdefault('_revoted', {})[col] = n
        elif _money_text(re.sub(r'[$#*@nｎ]', '', s[col]))[0] is not None:
            s[col] = '?' + s[col]  # 最初の読みは字数か形が合わず、読み直しでも決まらない: 最初の値を使わず読めない欄として人に回す
    if sub is not None and not ('parts' in subtotal and 'wage' in subtotal):  # 読み直しでも読めない列は、全体の OCR の値（崩れていなければ。Codex 指摘: _cands/_nest があるので件数では判定しない）
        for c in ('price', 'wage'):
            k = 'parts' if c == 'price' else 'wage'
            if k in subtotal:
                continue
            ws = sorted((w for w in sub['w'] if col_of(L, w['x'] + w['w'] / 2, sub['y']) == c), key=lambda w: w['x'])
            v, clean = _money_text(''.join(w['text'] for w in ws))
            if v is not None and clean:
                subtotal[k] = v
                subtotal['_cands'].setdefault(k, set()).add(v)
    return subtotal


def read_totals(clean_img, L: list[dict], trows: list[dict], sub: Optional[dict], exact: bool = False) -> dict:
    """合計欄（表の下: ページ小計 → 小計 → 課税額計 → 消費税 → 合計 → 部品価格適応日）→ {'taxable', 'tax', 'total'} と 検算の結果。
    数字は崩れやすい（'33,77' '371,48:'）ので、欄を読み直した票と、税（10%・四捨五入/切り捨て/切り上げ）と 合計 = 課税額計 + 消費税 の関係で
    辻褄の合う組を選ぶ。合う組が無ければ why に理由（header.totals.comment が OCR未確認 になる）"""
    table_end = max((p[0] for p in L[2]['pts']), default=0)
    below = [r for r in trows if r['y'] > (sub['y'] + 20 if sub is not None else table_end + 20)]  # 小計の見出しが崩れて見つからないときは表の下端から
    end = next((i for i, r in enumerate(below) if re.search(r'適応|適心|応日|G\d{5}', r['text'])), len(below))
    rows = below[:end]
    if len(rows) < 3:  # 合計欄の行が見つからない: 人に回す（空で返すと印の無いまま通る。Codex 指摘）
        return {'why': ['合計欄（課税額計・消費税・合計）の行が見つからない。最終ページの画像から写す']}
    tax_rows = rows[-3:]  # 課税額計・消費税・合計（その上に 小計・値引などがある）
    hh = statistics.median([w['h'] for r in tax_rows for w in r['w'] if _substantial(w['text'])] or [40])
    boxes = []
    for r in tax_rows:
        xs = [x_at(ln, r['y']) for ln in L]
        boxes.append((xs[3] + (xs[4] - xs[3]) * 0.3, r['y'] - hh * 0.7, xs[5] - 6, r['y'] + hh * 0.7))
    texts = [[''.join(w['text'] for w in r['w'] if col_of(L, w['x'] + w['w'] / 2, r['y']) in ('price', 'wage'))] * 2 for r in tax_rows] if exact else reocr_cells(clean_img, boxes)
    first = [tentative(''.join(w['text'] for w in r['w'] if col_of(L, w['x'] + w['w'] / 2, r['y']) in ('price', 'wage'))) for r in tax_rows]
    votes = [money_votes(tt) for tt in texts]

    def near(v: int, w: int) -> bool:  # 読み違いの組（3/8・5/6・0/8 …）で 1 字だけ違う
        a, b = str(v), str(w)
        return len(a) == len(b) and sum(x != y for x, y in zip(a, b)) == 1 and all(x == y or y in CONFUSE.get(x, '') for x, y in zip(a, b))

    def score(v, k):
        sc = votes[k].get(v, 0)
        if not sc and any(near(v, w) for w in votes[k]):
            sc = 0.5  # 票はあるが 1 字の読み違い（シエンタの合計 1,498,827 を '1,493,827' と読む）
        if first[k] is not None and str(v).startswith(str(first[k])[:max(3, len(str(first[k])) - 1)]):
            sc += 0.5  # 最初の読みの頭の数字と合う（'371,48:' → 371,481）
        return sc

    best = None
    for T in set(votes[0]) | ({first[0]} if first[0] else set()):
        for X in set(votes[1]) | {int(T * 0.1 + 0.5), int(T * 0.1), -(-T // 10)}:
            if X not in (int(T * 0.1 + 0.5), int(T * 0.1), -(-T // 10)):
                continue
            S = T + X
            sc = score(T, 0) + score(X, 1) + score(S, 2)
            if min(score(T, 0), score(X, 1), score(S, 2)) >= 0.5 and (best is None or sc > best[0]):  # 3 つとも何かしらの読みの裏付けがあり、税の関係が合う
                best = (sc, T, X, S)
    if best is None:
        return {'why': [f'合計欄（課税額計・消費税・合計）の読み {[t[:3] for t in texts]} から辻褄の合う組が見つからない']}
    return {'taxable': best[1], 'tax': best[2], 'total': best[3], 'why': []}


def fitz_text_pages(pdf: str, odir: str, pages) -> dict:
    """文字層のあるページ（コグニの PDF 出力）を PyMuPDF で読む: {ページ: (画像, 語)}。
    語は OCR と同じ形（x, y, w, h, text。画像の画素の座標）。PyMuPDF が無い・文字層の無いページは入れない（従来の OCR）。
    2026-09-28: Z: の直近の見積 PDF 約 1,180 件のうち 1,118 件が文字層つき（大半がコグニ印刷）だった"""
    try:
        import fitz  # type: ignore  # noqa: PLC0415
    except ImportError:
        return {}
    out = {}
    try:
        doc = fitz.open(pdf)
    except Exception:  # noqa: BLE001
        return {}
    for i, page in enumerate(doc, start=1):
        if pages and i not in pages:
            continue
        ws = page.get_text('words')
        try:   # スキャンした画像に OCR の文字層を重ねた PDF は「正確な字」ではない: ページの半分以上を覆う画像があれば従来の OCR にまかせる（Codex 指摘）
            _pa = abs(page.rect.width * page.rect.height) or 1
            # 画像の面積の合計で見る（帯・タイルに分けて埋め込んだスキャンもある。Codex 指摘）
            if sum(abs((b['bbox'][2] - b['bbox'][0]) * (b['bbox'][3] - b['bbox'][1])) for b in page.get_image_info()) > _pa * 0.5:
                continue
        except Exception:  # noqa: BLE001
            continue
        joined = ''.join(w[4] for w in ws)
        if len(ws) < 20 or not re.search(r'修理項目|部品価格|工賃', joined):
            continue
        zoom = 3456 / page.rect.width  # FAX の画像と同じくらいの大きさ（罫線の検出・欄の切り出しの閾値をそのまま使う）
        pix = page.get_pixmap(matrix=fitz.Matrix(zoom, zoom), colorspace=fitz.csGRAY)
        png = os.path.join(odir, f'page_{i}.text.png')   # ocr_prefill.extract_pages の page_N.png と別名（上書きされると語の座標と画像の縮尺がずれる。Codex 指摘）
        pix.save(png)
        words = [{'x': int(w[0] * zoom), 'y': int(w[1] * zoom), 'w': max(1, int((w[2] - w[0]) * zoom)), 'h': max(1, int((w[3] - w[1]) * zoom)),
                  'text': w[4], 'line': int(w[5]) * 1000 + int(w[6])} for w in ws]
        out[i] = (png, words)
    return out


def read_page_a(png: str, clean_img, L: list[dict], words: list[dict], H: int, exact: bool = False) -> dict:
    trows = text_rows(words)
    top, bottom, sub = detail_region(trows, L, H)
    slots = slots_of(words, L, top, bottom)
    subtotal = second_pass(clean_img, L, slots, sub, exact)
    tail = [r['text'] for r in trows if r['y'] > bottom]
    # 塗装明細・【費用】の区画: 明細の下端（区画の見出し）から、表の下端かページ小計・次頁まで
    table_end = max((p[0] for p in L[2]['pts']), default=H) + 100  # 線の終わりは 120 画素の帯の中心なので最大 60 画素浅い（最後の行が切れていた: ハイエース C14）。ページ小計の行は END_RE で止まる
    sec_end = table_end
    for r in trows:
        if r['y'] > bottom + 10 and END2_RE.search(r['text']):
            sec_end = min(sec_end, r['y'] - 20)
            break
    sec_slots = slots_of(words, L, bottom - 30, sec_end) if bottom < table_end - 60 else []
    if sec_slots and not exact:
        second_pass(clean_img, L, sec_slots, None)
    est_date = ''
    for r in trows[:40]:  # 帳票の上の「作成日 令和8年9月8日」
        m = re.search(r'作成日.*?(令和|R)\s*(元|\d{1,2})\s*年\s*(\d{1,2})\s*月\s*(\d{1,2})\s*日', r['text'])
        if m:
            y = 1 if m.group(2) == '元' else int(m.group(2))
            est_date = f'{2018 + y:04d}{int(m.group(3)):02d}{int(m.group(4)):02d}'
            break
    return {'top': top, 'bottom': bottom, 'slots': slots, 'subtotal': subtotal, 'est_date': est_date, 'sec_slots': sec_slots, '_trows': trows, '_sub': sub,
            'has_paint': any(re.search(r'塗装費用計|塗装明細|【塗装|塗料|塗膜', t) for t in tail),
            'has_expense': any('【費用' in t for t in tail)}


def ink(img, box, min_rows: float = 0.0) -> float:
    """枠の中の黒い画素の割合（罫線を消した画像で見る）。min_rows を渡すと、黒のある行が それだけの高さ（画素）に満たないときは 0
    （罫線の消し残り＝細い横棒 を字と取り違えない。ジムニー 5012 の工賃欄）"""
    from PIL import Image  # type: ignore
    x0, y0, x1, y1 = [int(v) for v in box]
    if x1 <= x0 or y1 <= y0:
        return 0.0
    c = img.crop((x0, y0, x1, y1)).convert('L')
    if min_rows:
        prof = c.resize((1, y1 - y0), Image.BOX).load()
        if sum(1 for y in range(y1 - y0) if prof[0, y] < 250) < min_rows:
            return 0.0
    hist = c.histogram()
    return sum(hist[:128]) / max(1, (x1 - x0) * (y1 - y0))


def judge(slots: list[dict], an: Optional[Anchor], page_sub: dict, clean_img, L: list[dict], others: Optional[list] = None, exact: bool = False) -> list[dict]:
    """行ごとに 出力する値 と 要確認の理由 を決める"""
    out = []
    items, idx = [], []
    for i, s in enumerate(slots):
        mid = s.get('_mid') or parse_mid(s['mid'])
        s['_mid'] = mid
        if an is not None and an.ok and s.get('code4'):
            items.append({'code': s['code4'], 'method': mid['method'] or '取替', 'qty': mid['qty'] or 1, 'name': ''})
            idx.append(i)
    std = [None] * len(slots)
    if items:
        for i, g in zip(idx, an.standards(items)):
            std[i] = g
    for i, s in enumerate(slots):
        mid = s['_mid']
        g = std[i]
        why: list[str] = []
        if s.get('code_why'):
            why.append(s['code_why'])
        # 印は 右端の欄（S は $ の読み違い）と、金額の欄の後ろにくっついたもの（先に S → $ にしてから拾う。Codex 指摘）
        marks = ''.join(ch for ch in nfkc(s['mark']).replace('S', '$').replace('＄', '$') if ch in '$#*@') + split_mark(s['wage'])[1] + split_mark(s['price'])[1]
        marks += ''.join(ch for ch in split_mark(s['wage'])[0] + split_mark(s['price'])[0] if ch in '$#*@')
        qty = mid['qty'] or 1
        row = {'code': s.get('code4') or '', 'name': s['name'], 'method': mid['method'], 'parts_no': mid['parts_no'], 'index': mid.get('index') or '',
               'qty': qty, 'price': None, 'wage': None, 'flags': ''.join(sorted(set(marks), key='$#*@'.index)), 'comment': ''}
        if s.get('_manual'):
            row['flags'] += 'M'
        if s.get('_free_method'):
            row['method'] = mid['method'] = s['_free_method']
        yc, ph = s['y'], s['pitch']
        xs = [x_at(ln, yc) for ln in L]
        ink_price = ink(clean_img, (xs[3] + 8, yc - ph * 0.3, xs[4] - 8, yc + ph * 0.3), ph * 0.22)  # ±0.3 行: 上の見出し（工賃(円)）の字を拾わない
        ink_wage = ink(clean_img, (xs[4] + 8, yc - ph * 0.3, xs[5] - 8, yc + ph * 0.3), ph * 0.22)
        price, price_clean = _money_text(re.sub(r'[$#*@]', '', split_mark(s['price'])[0]))  # 後ろの印（S を含む）は金額に混ぜない
        wage, wage_clean = _money_text(re.sub(r'[$#*@]', '', split_mark(s['wage'])[0]))
        row['_ocr'] = {'code': s['code'], 'name': s['name'], 'mid': s['mid'], 'price': s['price'], 'wage': s['wage'], 'mark': s['mark'],
                       'ink_price': round(ink_price, 4), 'ink_wage': round(ink_wage, 4)}
        row['_sure'] = {'price': False, 'wage': False}
        ink_mark = ink(clean_img, (xs[5] + 4, yc - ph * 0.3, xs[5] + (xs[5] - xs[4]) * 0.5, yc + ph * 0.3), ph * 0.16)
        row['_ocr']['ink_mark'] = round(ink_mark, 4)
        if ink_mark > 0.004 and not row['flags']:
            row['_mark_unread'] = True  # 判定は標準価格を引いてから（標準価格の無い部品に金額 → '*'）
        if not mid['method'] and (price is not None or ink_price > 0.004):
            mid['method'] = row['method'] = '取替'  # 部品価格があるのは取替の行だけ（修理方法の字を OCR が落とした）
            row['_ocr']['method_from_price'] = True
        if not mid['method']:
            why.append('修理方法が読めない')
        if g is not None:
            std_name = re.sub(r'\s+', ' ', str(g.get('PartsName') or '')).strip()
            std_pn = str(g.get('PartsNoStandard') or '').strip()
            unit = int(g.get('PartsPriceStandardOutTax') or 0) if str(g.get('PartsPriceStandardOutTax') or '').lstrip('-').isdigit() else 0
            row['_std'] = {'name': std_name, 'pn': std_pn, 'unit': unit}
            sim = name_similarity(s['name'], std_name)
            row['_ocr']['name_sim'] = round(sim, 2)
            row['name'] = std_name
            side_ocr = next((c for c in nfkc(s['name'])[:3] if c in '左右'), '')
            side_std = next((c for c in nfkc(std_name)[:3] if c in '左右'), '')
            if side_ocr and side_std and side_ocr != side_std:
                why.append(f'左右が違う（印字 {side_ocr} / 部品コード {row["code"]} は {side_std}）。部品コードを画像で確かめる')
            hint = renamed_hint(s['name'], std_name)
            if hint:
                row['_rename'] = True
                why.append(f'名称を工場が書き換えている（OCR「{s["name"]}」/ ADDATA「{std_name}」: {hint}）。印字どおりの名称を neo_name に写す')
            elif sim < 0.45 and len(_kana_skel(s['name'])) >= 4:
                why.append(f'名称が ADDATA（{std_name}）と大きく違う。工場が書き換えていれば印字どおり neo_name に写す')
            takes_part = mid['method'] in ('取替', '交換')  # 修理方法が読めない行は部品の行とみなさない（空の部品価格を標準で埋めない。C-HR 3500 板金）
            # 品番の変種: OCR の品番に一番近い変種が標準より明らかに近い（C-HR 0010: 印字 ﾐﾄｿｳ 52119-10919 / 標準 ﾄｿｳｽﾞﾐ 52119-10450-B1）
            if takes_part and std_pn and mid['parts_no'] and row['code']:
                vr = [(pn_similarity(mid['parts_no'], p), p, u) for p, u in an.variant_recs(int(row['code'])) if p]
                if vr:
                    bsim, bpn, bunit = max(vr)
                    if bsim >= 0.7 and an.parts.norm_pn(bpn) != an.parts.norm_pn(std_pn) and bsim >= pn_similarity(mid['parts_no'], std_pn) + 0.15:
                        std_pn = bpn
                        unit = bunit if bunit > 0 else unit
                        row['_pn_variant'] = True
                        row['_std']['variant'] = [bpn, bunit]
            # 品番
            if takes_part and std_pn:
                _n_ocr, _n_std = an.parts.norm_pn(mid['parts_no']), an.parts.norm_pn(std_pn)
                # まるごと読めた品番 = ハイフンで 2 つ以上に区切られ英数字 9 字以上（'52119-10919'）か、標準と同じ字数。
                # それ以外（'35650-770'・'524652020'・'Z0-77R00'）は OCR が字を落とした断片
                full = bool(re.fullmatch(r'[0-9A-Z]+(-[0-9A-Z]+)+', mid['parts_no'])) and len(_n_ocr) >= 9 or (len(_n_ocr) == len(_n_std) and len(_n_ocr) >= 8)
                variants = an.pns(int(row['code']))
                ocr_var = next((p for p in variants if an.parts.norm_pn(p) == an.parts.norm_pn(mid['parts_no'].replace('O', '0'))), None)
                if full and ocr_var and an.parts.norm_pn(ocr_var) != an.parts.norm_pn(std_pn):
                    row['parts_no'] = ocr_var  # 標準と違うが ADDATA にある品番（色違い・装備違い）。印字どおり（シエンタ 4730 -C0 / 標準 -A0）
                    row['_pn_variant'] = True
                elif full and not pn_ocr_confusable(mid['parts_no'], std_pn) and not (
                        '$' not in row['flags'] and unit > 0 and price is not None and price == unit * qty and pn_ocr_noise(mid['parts_no'], std_pn)):
                    # 読み違いの組でも、「価格が標準と一致 ＋ 2 字以内の崩れ ＋ 枝番が同じ」でもない: 別の品番かもしれない（価格の違う行 4527 は必ずここ）
                    why.append(f'品番 OCR {mid["parts_no"]} / 標準 {std_pn}（読み違いでは説明できない違い）')
                    row['parts_no'] = mid['parts_no']
                elif full or not mid['parts_no'] or pn_similarity(mid['parts_no'], std_pn) >= 0.7:
                    row['parts_no'] = std_pn  # まるごと読めて読み違いの組で説明できる / 読めない / 断片が標準と十分似ている
                elif not full:
                    row['parts_no'] = std_pn
                    why.append(f'品番の読めた部分 {mid["parts_no"]} が標準 {std_pn} と合わない（ほかの品番かもしれない）')
            elif not takes_part:
                row['parts_no'] = '' if not re.search(r'\d{4}', mid['parts_no']) else mid['parts_no']
            # 部品価格
            if takes_part and unit > 0 and '$' not in row['flags']:
                exp = unit * qty
                if row.get('_mark_unread') and price is not None and price_clean and price != exp:
                    row['price'] = price  # 右端の印が $（部品価格の手入力）かもしれない: 標準で埋めない
                    why.append(f'部品価格 OCR {price:,} / 標準 {unit:,}×{qty}（右端の印が $ なら手入力の価格）')
                elif price == exp:
                    row['price'] = exp; row['_sure']['price'] = True
                elif (price is None and ink_price > 0.004) or (price is not None and str(exp).endswith(str(price))) or (price_clean is False):
                    # OCR が桁を落とした・混じり物: 標準単価 × 数量 を下書きに入れる。確定はページ小計が合ったときだけ
                    # （ADDATA の版の違いで印字の価格が標準と違うことがある: シエンタ 2639 は 1,330 / 標準 1,600。Codex 指摘）
                    row['price'] = exp
                    row['_ocr']['price_from_std'] = True
                elif price is None:
                    row['price'] = 0  # 部品価格の欄が空（取替でも価格を入れない行がある: C-HR 7990 の *）。空のままだと下書きが標準価格を補うので 0（人の写しも 0）
                elif price and unit and price % unit == 0 and not mid['qty']:
                    row['price'] = price; row['qty'] = price // unit  # 数量の印字 (0N) を OCR が落とした（確定はページ小計で）
                    row['_ocr']['qty_from_price'] = True
                else:
                    row['price'] = price
                    why.append(f'部品価格 OCR {price:,} / 標準 {unit:,}×{qty}（ADDATA の版の違い？）')
            else:
                row['price'] = price
        elif s.get('kind') == 'reserve':
            row['flags'] = 'R'  # 保留（コード欄に「保留」。金額は計上しない）
            row['price'] = None; price = None
            hit = (an.parts.by_pn.get(an.parts.norm_pn(mid['parts_no'])) or []) if (an is not None and an.ok and mid['parts_no']) else []
            if hit:
                n20 = sorted(an.parts.name20_by_ref.get(hit[0]['ref_no']) or [''])[0]
                row['name'] = re.sub(r'\s+', ' ', an.e.cogni_parts_names(n20)[0]).strip() if n20 else s['name']
                row['_ocr']['reserve_pn_in_addata'] = True
            else:
                why.append('保留の行: 品番が ADDATA に無い。名称・品番を画像で写す')
        else:
            row['price'] = price
            if not row['code']:
                why.append('部品コードの無い行（手入力の行）: 名称・金額を画像で写す')
            else:  # 部品コードは読めたが ADDATA の標準値が引けない（車両未特定・引けない行）: 何も裏付けが無い（Codex 指摘）
                why.append('ADDATA の標準値が引けない（車両が決まらない・この行を引けない）。部品コード・名称・品番・金額を画像で確かめる')
        if row.pop('_mark_unread', None):
            if g is not None and not row.get('_std', {}).get('unit') and row['price']:
                row['flags'] = '*'  # 標準価格の無い部品に金額を入れた行の印（ジムニー 6029 ｶﾞﾗｽｾﾂﾁﾔｸｻﾞｲ）
                why.append('右端の印を * と読んだ（標準価格の無い部品。画像で確かめる）')
            else:
                why.append(f'右端に印（$ # * のどれか）があるが読めない（{s["mark"]}）')
        row['_unread'] = {'price': ink_price > 0.004 and row['price'] is None, 'wage': False}
        row['_tent'] = {'price': tentative(s['price']) if row['price'] is None else None, 'wage': tentative(s['wage']) if wage is None else None}
        if row['_unread']['price']:
            why.append('部品価格の欄に字があるが読めない')
        if not price_clean and row['price'] is None:
            why.append(f'部品価格が読めない（{s["price"]}）')
        row['wage'] = wage
        if wage is None and ink_wage <= 0.004 and not re.search(r'\d', s['wage']):
            row['wage'] = 0  # 工賃の欄が空 = 工賃なし（上の行に含む・吸収）。空のままだと下書きが標準の工賃を補う（シエンタ 4802/5002 で +104,000。人の写しも 0）
        if ink_wage > 0.004 and wage is None:
            row['_unread']['wage'] = True
            why.append(f'工賃の欄に字があるが読めない（{s["wage"]}）')
        elif wage is not None and not wage_clean:
            row['_wage_unclean'] = True
        row['_why'] = why
        out.append(row)
    if exact:
        # 文字層の字は正確: 名称は印字どおり（ADDATA の名称と違えば neo_name に。工場の書き換え）。読みの疑いの理由は付けない
        _nk = an.e._name_key if (an is not None and an.ok) else (lambda x: re.sub(r'\s+', '', nfkc(x)))
        for s, r in zip(slots, out):
            printed = ' '.join(w['text'] for w in sorted((w for w in s['w'] if w['col'] == 'name'), key=lambda w: w['x'])).strip()
            if printed and (not s['_mid']['method'] or (r.get('_ocr') or {}).get('method_from_price')):   # 部品価格から「取替」と補った行も
                # 名称と区分が 1 語にくっついた字（'…ｻｲﾄﾞｽﾍﾟ-ｻ取替'）: 区分の欄が空なら語尾の区分を切り出す（Codex 指摘）
                _pm = next((m_ for m_ in sorted(EXACT_METHODS, key=len, reverse=True) if nfkc(printed).endswith(m_) and len(nfkc(printed)) > len(m_)), None)
                if _pm:
                    printed = printed[:len(printed) - len(_pm)].strip()
                    r['method'] = s['_mid']['method'] = _pm
            if printed:
                std = (r.get('_std') or {}).get('name') or ''
                r['name'] = printed
                if std and _nk(printed) != _nk(std):
                    r['neo_name'] = printed
            if (r.get('_std') or {}).get('pn') and s['_mid']['parts_no']:
                r['parts_no'] = s['_mid']['parts_no']  # 品番も印字どおり
            elif (r.get('_std') or {}).get('pn') and not s['_mid']['parts_no']:
                # 品番欄に品番でない文字（'ﾓﾃﾞﾘｽﾀ' '再封印'）: 印字どおり（判断規則 10-29。t15 をコグニで刷って判明）
                _rest = re.sub(r'\(\d{1,3}\)|\d+(?:\.\d+)?', ' ', s['mid'])
                if s['_mid']['method']:
                    _rest = _rest.replace(s['_mid']['method'], ' ', 1)
                _rest = re.sub(r'\s+', ' ', _rest).strip()
                if _rest and not re.search(r'd[m㎡]|/', _rest):
                    r['parts_no'] = _rest
        # 字は正確でも、字の無いインク・空欄を 0 とした欄・ADDATA の補完は字では裏付けられない。
        # ページ小計（文字層の字）と明細＋費用＋骨格の合計が列ごとに一致したときだけ全部の理由を消す（Codex 指摘）
        _allc = out + list(others or [])
        _keys = [(c, k) for c, k in (('price', 'parts'), ('wage', 'wage')) if page_sub.get(k) is not None]
        _sub_match = bool(_keys) and all(sum(int(x.get(c) or 0) for x in _allc) == int(page_sub[k]) for c, k in _keys)
        # 文字層では意味の無い理由: 名称・金額は字のまま（区分の欄が空なら空）、工場の書き換えた名称は上で neo_name に・品番は印字どおりに写している
        _moot = re.compile(r'画像で写す|修理方法が読めない|名称を工場が書き換え|名称が ADDATA|^品番 OCR|^品番の読めた部分')
        _amount = re.compile(r'部品価格|工賃|金額|価格')
        for x in _allc:
            x['_why'] = [w for w in x.get('_why') or [] if not _moot.search(w) and not (_sub_match and _amount.search(w))]   # 小計が裏付けるのは金額だけ（印・コードの注意は残す。Codex 指摘）
            if _sub_match:
                for col, _k in _keys:   # confirm_by_subtotal と同じく、小計で裏付けた列は確定（塗装の行の検査が見る。Codex 指摘）
                    x.setdefault('_sure', {})[col] = True
            else:
                # 小計で裏付けられないときは、字で読んでいない金額（標準単価で埋めた・字の無いインク）に理由を必ず付ける（Codex 指摘）
                if (x.get('_ocr') or {}).get('price_from_std') and x.get('price'):
                    x['_why'].append(f"部品価格の欄に字が無いので標準単価×数量 {x['price']:,} を入れた（ページ小計なし・画像で確かめる）")
                for col, lbl in (('price', '部品価格'), ('wage', '工賃')):
                    if (x.get('_unread') or {}).get(col) and not any(lbl in w and '読めない' in w for w in x['_why']):
                        x['_why'].append(f'{lbl}の欄に字の無いインクがある（画像で確かめる）')
            x['comment'] = f'{UNVERIFIED}: ' + ' / '.join(dict.fromkeys(x['_why'])) if x['_why'] else ''
        return out
    confirm_by_subtotal(out, others or [], page_sub)
    return out


EXACT_METHODS = ('脱着修理', '脱着板金', '点検調整', '分解調整', '取替', '脱着', '修理', '調整', '点検', '板金')


def confirm_by_subtotal(rows: list[dict], others: list[dict], page_sub: dict) -> None:
    """ページ小計で列ごとにまとめて確かめる。others = 同じページの費用・内板骨格（同じ形の dict: price / wage / _unread / _sure / _why）。
    塗装明細が同じページにあると小計にそれも入るので使わない（page_sub は呼び出し側で空にする）"""
    allc = rows + others
    for col, key in (('price', 'parts'), ('wage', 'wage')):
        tot = sum(int(r[col] or 0) for r in allc)
        sub = page_sub.get(key)
        _c = (page_sub.get('_cands') or {}).get(key) or set()
        _n = (page_sub.get('_nest') or {}).get(key)

        def matches(x: int) -> bool:
            if not x:
                return False
            if x == sub or x in _c:  # 小計の読み（多数決の 1 位でなくても、1 票でも出た読み）と一致
                return True
            # 先頭の 1 桁だけ落ちた読み（'17,180' = 117,180）で、字の幅から見た桁数は合う（ジムニー 2 ページ目）
            return bool(_n and money_len_ok(x, _n) and any(len(str(c_)) >= 4 and len(str(x)) - len(str(c_)) == 1 and str(x).endswith(str(c_)) for c_ in _c))

        if matches(tot):
            sub = page_sub[key] = tot
        unread = [r for r in allc if r['_unread'][col]]
        tents = [(r, (r.get('_tent') or {}).get(col)) for r in unread]
        if unread and all(v is not None for _r, v in tents) and matches(tot + sum(v for _r, v in tents)):
            # 読みの決まらない欄の仮の値（読めた数字）を入れると小計と一致する（手書きの重なった費用欄: ジムニー 2 ページ目の 3000）
            for r1, v in tents:
                r1[col] = v
                r1['_unread'][col] = False
                _pre = ('部品価格', '費用の部品価格') if col == 'price' else ('工賃', '費用の工賃', '内板骨格の工賃', '塗装の行の工賃')
                r1['_why'] = [w for w in r1['_why'] if not ('読めない' in w and w.startswith(_pre))]  # その列の「読めない」だけを消す（右端の印などは残す）
                if 'amount' in r1:
                    r1['amount'] = v
            tot = tot + sum(v for _r, v in tents)
            sub = page_sub[key] = tot
            unread = []
        if sub is not None and len(unread) == 1 and sub - tot > 0:
            # 読めない欄が 1 つだけなら、小計から逆算した額を入れる（その行は画像で確かめる。ほかの行は小計と合うので確定）
            r1 = unread[0]
            r1[col] = sub - tot
            r1['_why'] = [w for w in r1['_why'] if 'の欄に字があるが読めない' not in w or ('工賃' if col == 'wage' else '部品価格') not in w]
            r1['_why'].append(f'{"工賃" if col == "wage" else "部品価格"}が読めないのでページ小計から逆算して {sub - tot:,} を入れた（画像で確かめる）')
            tot = sub
        if sub is not None and tot == sub:
            for r in allc:
                r['_sure'][col] = True
                if col == 'wage':
                    r.pop('_wage_unclean', None)
        for r in allc:
            if r['_sure'][col] or r[col] in (None, 0):
                continue
            tail = (f'（ページ小計 {sub:,} ≠ 行の合計 {tot:,}）' if sub is not None else '（ページ小計なし）')
            if col == 'price' and (r.get('_ocr') or {}).get('price_from_std'):
                r['_why'].append(f'部品価格が読めない（OCR「{r["_ocr"].get("price")}」）ので標準単価×数量 {r[col]:,} を入れた（画像で確かめる）' + tail)
            elif col == 'price' and ('$' in r.get('flags', '') or not r.get('code') or r.get('_std', {}).get('unit', 0) <= 0):
                r['_why'].append(f'部品価格 {r[col]:,} は ADDATA で確かめられない' + tail)
            elif col == 'price':  # 確定できない部品価格には必ず理由を付ける（理由の無い行は確定扱いになる）
                r['_why'].append(f'部品価格 {r[col]:,} を標準価格でもページ小計でも確かめられない' + ('（数量を価格から割り出した）' if (r.get('_ocr') or {}).get('qty_from_price') else '') + tail)
            elif col == 'wage':
                r['_why'].append(f'工賃 {r[col]:,} は ADDATA で確かめられない' + tail)
    for r in allc:
        if r.pop('_wage_unclean', None):
            r['_why'].append(f'工賃の読みに混じり物（{r["_ocr"]["wage"]}）')
        if r['_why']:
            r['comment'] = f'{UNVERIFIED}: ' + ' / '.join(dict.fromkeys(r['_why']))


# 塗膜の印字 → reading の coat。'2コートソリッド' はコグニの塗膜 ソリッド ＋ 付加塗装の 2コートソリッド加算（塗装条件で指定すると塗膜欄に
# '2コートソリッド' と刷られる）。'2コート' より先に見ないと 2コートパール になる（2026-09-28 生成 NEO をコグニで刷って判明: k02・t09）
COATS = ((r'2\s*コ[ー\-]?ト\s*ソリ', 'ソリッド'), (r'3\s*コ[ー\-]?ト', '3コートパール'), (r'2\s*コ[ー\-]?ト', '2コートパール'),
         ('メタリック', 'メタリック'), ('ソリ[ッツ]ド', 'ソリッド'))


def coat_of(text: str) -> str:
    t = nfkc(text or '')
    return next((full for pat, full in COATS if re.search(pat, t)), '')


def _money_any(t: str) -> Optional[int]:
    """'110,680円' '32,380' '11,700工' → 金額（円・後ろのごみを除く）。数字が無ければ None"""
    m = re.search(r'\d{1,3}(?:[,.]\d{3})+|\d+', nfkc(t).translate(DIGIT_FIX).replace(' ', ''))
    return int(re.sub(r'\D', '', m.group(0))) if m else None


def _mid_index(t: str) -> Optional[float]:
    """塗装行の指数（欄の右端 '1.70' '1,50' '1-70'）"""
    m = re.search(r'(\d{1,2})[.,\-](\d{2})\s*$', nfkc(t).replace(' ', ''))
    return float(f'{m.group(1)}.{m.group(2)}') if m else None


def _paren_index(t: str) -> Optional[float]:
    """'ブース加算 (0.50)' 'ブース有n(0,5の' → 0.5"""
    m = re.search(r'\(?\s*(\d{1,2})[.,](\d{1,2})', nfkc(t))
    return float(f'{m.group(1)}.{m.group(2)}') if m else None


# 塗装明細の「名称」「修理方法の欄」に出る決まった語（painting.md §6 の下書きが振り分ける形）
PAINT_BASES = ('フロント樹脂バンパ', 'リヤ樹脂バンパ', 'フロントバンパ', 'リヤバンパ', 'ラジエータサポート', 'フロントフェンダエプロン', 'フロントピラー',
               'センターピラー', 'リヤフロア', '防錆ワックス', 'ボデーシーリング')
PAINT_MID_WORDS = ('片側新品または修正', '両側新品または修正', '両側新品', '片側新品', '１台小修正', '大修正', '新品', '修正', '一色', '二色', '変形修正', '外傷修正小', '外傷修正大')


def reread_paint_mid(img, L: list[dict], slots: list[dict]) -> int:
    """塗装行（部品コードの無い行）の 修理方法の欄 を、元の画像（罫線を消す前）で線の右から読み直す。
    罫線を消すと線に接した頭の字が欠ける（C-HR: '両側新品 1.50' が '1.50' に）。読み直しの多数決（空でない読みの最頻値）で置き換える"""
    from collections import Counter  # noqa: PLC0415
    tgt = [x for x in slots if not re.sub(r'\D', '', x['code']) and (x['name'].strip() or x['mid'].strip())]
    if not tgt:
        return 0
    boxes = []
    for x in tgt:
        xs = [x_at(ln, x['y']) for ln in L]
        boxes.append((xs[2] + 9, x['y'] - x['pitch'] * 0.4, xs[3] - 10, x['y'] + x['pitch'] * 0.4))
    n = 0
    for x, tt in zip(tgt, reocr_cells(img, boxes)):
        c = Counter(t for t in tt if t)
        if not c:
            continue
        best, k = c.most_common(1)[0]
        if k >= 2 and len(best) >= len(nfkc(x['mid']).replace(' ', '')):
            x['_mid_orig'] = x['mid']
            x['mid'] = best
            n += 1
    return n


def paint_line_name(name: str, mid: str) -> tuple[str, bool, dict]:
    """塗装行の名称と欄の字 → ('ラジエータサポート 両側新品', 決まった語に寄せられたか, {'index': 1.5, 'count': 4})"""
    extra: dict = {}
    md = nfkc(mid).replace(' ', '')
    m = re.search(r'(\d{1,2})[.,\-](\d{2})\(?$', md)
    if m:
        extra['index'] = float(f'{m.group(1)}.{m.group(2)}'); md = md[:m.start()]
    m = re.search(r'(\d+)枚', md)
    if m:
        extra['count'] = int(m.group(1)); md = md.replace(m.group(0), '')
    base, ok = _snap(name, list(PAINT_BASES))
    words = []
    m = re.search(r'(\d+(?:\.\d+)?)m$', md)
    if m:
        words.append(f'{m.group(1)}m'); md = md[:m.start()]  # シーリングの長さ（'4.00m'）は名称に残す（下書きが長さから指数を出す）
    rest = md
    for w in sorted(PAINT_MID_WORDS, key=len, reverse=True):   # 長い語から（'外傷修正小' '変形修正' を汎用の '修正' より先に。Codex 指摘）
        w = nfkc(w)   # 欄の字は NFKC にしてある（'１台小修正' → '1台小修正'。そろえないと汎用の '修正' が先に当たる: Codex 指摘）
        if w in rest:
            words.append(w); rest = rest.replace(w, ' ')
    if base in ('フロント樹脂バンパ', 'リヤ樹脂バンパ', 'フロントバンパ', 'リヤバンパ') and not any(w in words for w in ('一色', '二色')):
        ok = False  # 一色 / 二色 で指数が変わる。読めなければ人に回す
    if base in ('ラジエータサポート', 'フロントフェンダエプロン', 'フロントピラー', 'センターピラー', 'リヤフロア') and not words:
        ok = False
    return (base + (' ' + ' '.join(words) if words else '')).strip(), ok, extra


def paint_vocab() -> dict:
    """塗装の追加項目・塗装行の名称の語彙（この PC の NEO_check の reading から）。OCR の崩れた名称をこれに寄せる"""
    out = {'other': ['塩害ガード', 'プライマー塗装', '新品パネル/プライマ塗布', '新品パネル/プライマー塗布', '防錆処理', 'アンダーコート'], 'lines': []}
    root = os.environ.get('NEO_CHECK_ROOT') or os.path.join(os.path.expanduser('~'), 'Documents', 'NEO_check')
    try:
        for d in os.listdir(root):
            for p in (os.path.join(root, d, 'reading.json'),):
                if os.path.exists(p):
                    pa = (reading_pages.load_json(p).get('paint') or {})
                    for k in ('other', 'lines'):
                        for x in pa.get(k) or []:
                            nm = nfkc((x or {}).get('name') or '').strip() if isinstance(x, dict) else ''
                            if nm and nm not in out[k]:
                                out[k].append(nm)
    except (OSError, ValueError):
        pass
    return out


def _snap(raw: str, vocab: list[str]) -> tuple[str, bool]:
    """OCR の崩れた名称を語彙の近いものに寄せる（0.6 以上、次点と 0.1 以上離れているとき）。戻り値 (名称, 寄せられたか)"""
    sk = _kana_skel(raw) or nfkc(raw)
    sc = sorted(((difflib.SequenceMatcher(None, sk, _kana_skel(v) or nfkc(v)).ratio(), v) for v in vocab), reverse=True)
    if sc and sc[0][0] >= 0.6 and (len(sc) == 1 or sc[0][0] - sc[1][0] >= 0.1 or _kana_skel(sc[0][1]) == _kana_skel(sc[1][1])):
        return sc[0][1], True
    return nfkc(raw).strip(), False


def is_expense_heading(nm: str) -> bool:
    """【費用】の見出し（OCR で '【豊用】' 'ー質用】' と崩れたものも）"""
    return bool(re.search(r'費用】|質用】|【費', nm) or (len(nm) <= 5 and re.search(r'.用】', nm)))


def parse_sections(slots: list[dict], labor: Optional[int], vocab: dict, an=None) -> dict:
    """【塗装明細】と【費用】の区画の行 → {'paint': reading の paint（無ければ None）, 'exp_slots': 費用の行, 'labor': 指数から逆算したレート, 'why': [...]}
    コグニ印刷の並び（2026-09-28 ジムニー・C-HR・ハイエース）:
        塗装費用計 / <内訳> 塗装工賃計 / 塗装材料代計 / 追加塗装費用計 / 塗料 / 塗膜 / パネルの行（コード 取替 89dm² / 修理 90dm² (1/3)）/
        ブース加算 (0.50) / 加算基礎数値 (2.90) / そのほかの塗装行（ボデーシーリング 4.00m・バンパ・内板骨格塗装）/
        塗装材料代 / 材料代割合 38.0% / 材料代単価 9,500円 / 材料代係数 1.30 / 追加項目（塩害ガード …）/ 【費用】 以下は費用
    項目名は OCR で崩れる（'サ代割合' 'く内訳>塗装一計'）ので、語の一部と値の形（円・%・(指数)）と並びで決める"""
    why: list[str] = []
    heads = {}           # paint_total / total / material_sum / other_total
    head_order = ['paint_total', 'total', 'material_sum', 'other_total']
    pa: dict = {'lines': [], 'other': []}
    exp_slots: list[dict] = []
    state = 'head'       # head → body（塗膜の後）→ material（塗装材料代の後）→ other（係数・割合の後）→ expense
    brand = coat = ''
    seen_any = False
    for s in slots:
        nm, md = nfkc(s['name']).replace(' ', ''), nfkc(s['mid']).replace(' ', '')
        wg = _money_text(re.sub(r'[$#*@nｎ]', '', s['wage']))[0]
        pr = _money_text(re.sub(r'[$#*@nｎ]', '', s['price']))[0]
        mark = ''.join(ch for ch in s['mark'] + s['wage'] if ch in '$#*@')
        txt = nm + md
        if not txt and wg is None and pr is None:
            continue
        if is_expense_heading(nm) or (state != 'expense' and re.fullmatch(r'【?費用】?', nm)):  # '【豊用】' 'ー質用】'も（ハイエース 2026-09-28）
            state = 'expense'
            s['kind'] = 'heading'  # 区画の見出し（塗装の行として数えない。Codex 指摘）
            s['_head'] = 'expense'
            continue
        if state == 'expense':
            if wg is not None or pr is not None or re.search(r'\d', s['wage'] + s['price']):
                exp_slots.append(s)  # 読みの決まらない欄（'?3000'）も費用の行として拾う（build_expenses が 仮の値・要確認 にする）
            else:
                s['kind'] = 'noise'  # 【費用】の区画の金額の無い行（手書きのメモ等）
            continue
        if re.search(r'塗装明細|明細】', nm):
            s['kind'] = 'heading'
            s['_head'] = 'paint'
            continue
        seen_any = True
        if state == 'head':
            if re.fullmatch(r'塗装費用計?', nm) and wg is not None and not heads:   # 「塗装費用計」と刷る様式も（バグハント）
                # 塗装が一式（'塗装費用 202,230' の 1 行だけ）。コグニはこの下に【費用】の見出しを付けずに費用を並べることがある（ハイエース C14）
                heads['paint_total'] = wg
                s['_paint_head'] = 'paint_total'
                s['_pv'] = wg  # 工賃の欄に刷られた額（ページ小計に入る）
                state = 'expense'
                continue
            if '塗料' in nm:
                brand = md; continue
            if re.match(r'塗装方法', nm):
                if md:
                    pa['type_note'] = md   # 塗装条件の注記（'ｱﾝﾀﾞｰｺｰﾄ含み'）。金額の行ではない（t07）
                continue
            if '塗膜' in nm or (re.search(r'コート|ソリッド|メタリック|パール', md) and wg is None):
                coat = md; state = 'body'; continue
            if '円' in md or (md and _money_any(md) is not None and not re.search(r'dm|\(', md)) or (wg is not None and not s['code'].strip()):
                v = _money_any(md) if md else wg
                key = ('other_total' if '追加' in nm else 'material_sum' if ('材料' in nm and '計' in nm) else
                       'total' if ('内訳' in nm or '工賃' in nm) else 'paint_total' if ('費用' in nm and '追加' not in nm) else None)
                key = key if key and key not in heads else next((k for k in head_order if k not in heads), None)
                if key and v is not None:
                    heads[key] = v
                    s['_paint_head'] = key
                continue
            state = 'body'   # 塗膜の行が読めないまま明細に入った
        if state in ('body', 'material', 'other'):
            if wg is not None:
                s['_pv'] = wg  # この行が工賃の欄に刷った額（ページ小計はこれの合計）
            elif re.search(r'\d', s['wage']):
                s['_pv_tent'] = tentative(s['wage'])  # 読みの決まらない工賃の欄（仮の値）
        if re.match(r'塗装方法', nm) and wg is None:
            if md:
                pa['type_note'] = md   # 塗膜の行の後に刷られる書式もある
            continue
        if state == 'body':
            if re.search(r'耐スリ|フッ素|セラミック|高機能', txt) and wg is None:
                pa['hf'] = '耐スリ傷' if '耐スリ' in txt else ('フッ素' if 'フッ素' in txt else pa.get('hf', 'しない'))
                continue
            if re.search(r'料代', nm) and not re.search(r'割合|単価|係数|計', nm) and wg is not None:
                pa['material'] = wg; state = 'material'
                if '*' in mark:
                    pa['_mat_manual'] = True   # 材料代を手入力（*）: 刷られた割合は材料代 ÷ 工賃計 と合わなくてよい（コグニは割合を刷ったまま。k02 25.0%・k05 23.0%）
                    if not s.get('_exact'):
                        pa['_mat_manual_ocr'] = True   # OCR の割合は裏付けが無い（'25.0%' を '250%' と読んでも通ってしまう。Codex 指摘）
                continue
            _both = txt + nfkc(s.get('_mid_orig') or '')  # 読み直す前の字も見る（読み直しで 'ブース' が崩れた: ジムニー 2026-09-28）
            if re.search(r'ブース', _both) or (re.search(r'加算|基礎|数値', _both) and (_paren_index(md) is not None or _paren_index(s.get('_mid_orig') or '') is not None)):
                idx = _paren_index(md) if _paren_index(md) is not None else _paren_index(s.get('_mid_orig') or '')
                name = '加算基礎数値' if (re.search(r'基礎|数値', _both) and not re.search(r'ブース', _both)) else ('ブース加算' if re.search(r'ブース|ブ', _both) else '加算基礎数値')
                ln = {'name': name, 'wage': wg}
                if idx is not None:
                    ln['index'] = idx
                if mark:
                    ln['mark'] = mark
                pa['lines'].append(ln); continue
            if wg is None and not md:
                continue
            code = re.sub(r'\D', '', nfkc(s['code']).translate(DIGIT_FIX))
            mid = parse_mid(s['mid'])
            if len(code) == 4 and (mid['method'] or mid['area']):
                ratio = re.search(r'\(?(\d)/(\d)\)?', md)
                base = an.std_name(int(code)) if (an is not None and getattr(an, 'ok', False) and int(code) in an.valid) else ''
                name = f"{base or s['name']} {mid['method'] or '取替'}" + (f' {ratio.group(1)}/{ratio.group(2)}' if ratio else '')
                ln = {'name': re.sub(r'\s+', ' ', name).strip(), 'wage': wg, 'code': code}  # draft は code で 20.DB のパネルを引く（名称が崩れても）
                if mid['index']:
                    ln['index'] = float(mid['index'])
                if mid['area']:
                    ln['comment'] = f"塗装面積 {mid['area']}d㎡"
                if mark:
                    ln['mark'] = mark
                pa['lines'].append(ln); continue
            nm2, ok, _ex = paint_line_name(s['name'], s['mid'])  # 決まった語（ラジエータサポート 両側新品 / 防錆ワックス 4 枚 …）に寄せる
            if not ok and vocab.get('lines'):
                nm3, ok3 = _snap(f"{s['name']} {s['mid']}".strip(), vocab.get('lines') or [])
                if ok3:
                    nm2, ok = nm3, True
            ln = {'name': nm2 if ok else re.sub(r'\s+', ' ', f"{nfkc(s['name'])} {nfkc(s['mid'])}").strip(), 'wage': wg}
            ln.update(_ex)
            if 'index' not in ln and _mid_index(md) is not None:
                ln['index'] = _mid_index(md)
            if mark:
                ln['mark'] = mark
            if not ok and not re.search(r'シーリング', nm):
                ln['_unsure'] = True
            pa['lines'].append(ln); continue
        if state in ('material', 'other'):
            if state == 'material' and (re.search(r'割合', nm) or '%' in md):
                m = re.search(r'(\d+(?:\.\d+)?)\s*%', md.translate(str.maketrans({'L': '1', 'l': '1', 'I': '1', 'O': '0'})))
                if m:
                    pa['material_rate'] = float(m.group(1)) if '.' in m.group(1) and not m.group(1).endswith('.0') else int(float(m.group(1)))
                continue
            if state == 'material' and (re.search(r'単価', nm) or ('円' in md and wg is None)):
                v = _money_any(md)
                if v:
                    pa['material_unit'] = v
                continue
            if state == 'material' and (re.search(r'係数', nm) or (re.fullmatch(r'\d\.\d{1,2}', md) and wg is None)):
                pa['material_coefficient'] = float(md) if re.fullmatch(r'\d+\.\d+', md) else _paren_index(md)
                state = 'other'; continue
            if wg is not None:
                state = 'other'
                nm2, ok = _snap(s['name'], vocab.get('other') or [])
                if s.get('_exact') and s['name'].strip():
                    nm2, ok = re.sub(r'\s+', ' ', s['name']).strip(), True   # 文字層の字は正確: 印字どおり（語彙に寄せると 'ｱﾝﾀﾞｰｺｰﾄ処理' が 'ｱﾝﾀﾞｰｺｰﾄ' に）
                o = {'name': nm2, 'wage': wg}
                if _mid_index(md) is not None:
                    o['index'] = _mid_index(md)
                if mark:
                    o['mark'] = mark
                if not ok:
                    o['_unsure'] = True
                pa['other'].append(o)
    if not seen_any:
        return {'paint': None, 'exp_slots': exp_slots, 'labor': None, 'why': []}
    # 一式だけ（塗装費用 191,360 の 1 行: シエンタ 5 ページ目）
    if not pa['lines'] and not pa['other'] and 'material' not in pa:
        v = heads.get('paint_total') if heads.get('paint_total') is not None else heads.get('total')
        if v is None:
            return {'paint': None, 'exp_slots': exp_slots, 'labor': None, 'why': []}
        _pa1 = {'total': v, 'material': 0, 'paint': '水性' if '水性' in brand else '2K', 'hf': pa.get('hf') or 'しない'}
        if coat_of(coat):
            _pa1['coat'] = coat_of(coat)   # 一式でも塗膜は刷られる（書かないとコグニの印刷が 塗膜 ソリッド になる: t04 2コートパール）
        return {'paint': _pa1, 'exp_slots': exp_slots, 'labor': None, 'paint_total': v,
                'why': [f'塗装は一式（{v:,} 円）だけ印字。明細から塗装パネルを起こすなら paint.auto_panels（手順 5）']}
    # レート: 指数が刷られた行（ブース加算・加算基礎数値）の 工賃 ÷ 指数
    rates = {round(ln['wage'] / ln['index'] / 10) * 10 for ln in pa['lines'] if ln.get('index') and ln.get('wage')}
    rate = labor or (rates.pop() if len(rates) == 1 else None)
    for ln in pa['lines']:
        if 'index' not in ln and ln.get('wage') and rate and ln.get('code'):  # シーリング（長さで決まる）などには付けない
            ln['index'] = round(ln['wage'] / rate, 2)
    pa['paint'] = '水性' if '水性' in brand else '2K'
    pa['coat'] = coat_of(coat) or coat
    pa['hf'] = pa.get('hf') or 'しない'
    if 'total' in heads:
        pa['total'] = heads['total']
    if 'material' not in pa and heads.get('material_sum') is not None:
        pa['material'] = heads['material_sum']
    _mat_manual = pa.pop('_mat_manual', False)
    if pa.pop('_mat_manual_ocr', False) and pa.get('material_rate') is not None:
        why.append(f"材料代が手入力（*）なので割合 {pa['material_rate']}% を材料代から確かめられない。画像で割合を確かめる")
    if _mat_manual and pa.get('material_rate') is None:
        why.append('材料代が手入力（*）で、材料代割合の印字が読めない（割合を画像で写す。書かないと生成器の既定の割合になる）')
    if pa.get('material') and heads.get('total') and pa.get('material_rate') is not None and 'material_unit' not in pa and not _mat_manual:
        if abs(pa['material'] - heads['total'] * float(pa['material_rate']) / 100) > 10:
            pa.pop('material_rate')  # 読んだ割合が 材料代 ÷ 工賃計 と合わない（'400%' = 40.0%）: 下で計算し直す
    if 'material_rate' not in pa and pa.get('material') and heads.get('total') and not _mat_manual:  # 割合の字が崩れた（'3L0%'）: 材料代 ÷ 工賃計 が 0.1% 刻みなら割合
        r_ = pa['material'] / heads['total'] * 100
        if abs(round(r_, 1) - r_) < 0.005:
            pa['material_rate'] = round(r_, 1) if round(r_, 1) != int(round(r_, 1)) else int(round(r_, 1))
    # 検算（合えば確定）
    lsum = sum(int(ln.get('wage') or 0) for ln in pa['lines'])
    osum = sum(int(o.get('wage') or 0) for o in pa['other'])
    if any(o.get('wage') is None for o in pa['other']):
        why.append('追加項目に工賃の読めない行がある')
    if heads.get('total') is None or heads['total'] != lsum:
        why.append(f"塗装工賃計 {heads.get('total')} ≠ 塗装行の合計 {lsum:,}")
    if pa['other'] or heads.get('other_total'):
        if heads.get('other_total') != osum:
            why.append(f"追加塗装費用計 {heads.get('other_total')} ≠ 追加項目の合計 {osum:,}")
    if heads.get('material_sum') is not None and pa.get('material') is not None and heads['material_sum'] != pa['material']:
        why.append(f"塗装材料代計 {heads['material_sum']:,} ≠ 塗装材料代 {pa['material']:,}")
    if heads.get('paint_total') is not None and heads['paint_total'] != (heads.get('total') or 0) + (pa.get('material') or 0) + (heads.get('other_total') or 0):
        why.append(f"塗装費用計 {heads['paint_total']:,} ≠ 工賃計＋材料代計＋追加計")
    if any(ln.get('_unsure') for ln in pa['lines']) or any(o.get('_unsure') for o in pa['other']):
        why.append('塗装行・追加項目の名称が読み切れない行がある（' + ' / '.join(x['name'] for x in pa['lines'] + pa['other'] if x.get('_unsure')) + '）')
    if not pa['coat']:
        why.append('塗膜が読めない')
    for _nm in ('ブース加算', '加算基礎数値'):
        if sum(1 for ln in pa['lines'] if ln.get('name') == _nm) > 1:
            why.append(f'{_nm} が 2 行ある（ブース加算と加算基礎数値の取り違え？）')
    for x in pa['lines'] + pa['other']:
        x.pop('_unsure', None)
    if not pa['other']:
        pa.pop('other')
    return {'paint': pa, 'exp_slots': exp_slots, 'labor': rate if not labor else None, 'paint_total': heads.get('paint_total'), 'why': why}


def method_glyph(img, L: list[dict], s: dict):
    """修理方法の欄の字の形（白黒・字の外枠で切って 64×32 にそろえる）。字が無ければ None。元の画像で見る（罫線を消すと線に接した字の端が欠ける）"""
    xs = [x_at(ln, s['y']) for ln in L]
    ph = s['pitch']
    t = img.crop((int(xs[2] + 10), int(s['y'] - ph * 0.35), int(xs[2] + (xs[3] - xs[2]) * 0.13), int(s['y'] + ph * 0.35))).convert('L').point(lambda v: 0 if v < 160 else 255)
    bb = t.point(lambda v: 255 - v).getbbox()
    if not bb or (bb[2] - bb[0]) < 20:
        return None
    return t.crop(bb).resize((64, 32))


def glyph_diff(a, b) -> float:
    pa, pb = a.load(), b.load()
    return sum(1 for x in range(64) for y in range(32) if (pa[x, y] < 128) != (pb[x, y] < 128)) / (64 * 32)


def methods_by_shape(items: list) -> int:
    """items = [(slot, 字の形)]。OCR で読めた修理方法の字の形を手本にして、読めなかった欄を形で決める。
    1 位の違いが 0.2 以下で、2 位と 0.15 以上離れているときだけ採る（C-HR で 13 欄すべて正しく、2 位との差は 0.2 以上だった）。戻り値 = 決めた欄の数"""
    tpl: dict = {}
    for s, g in items:
        m = parse_mid(s['mid'])['method']
        if m and g is not None:
            tpl.setdefault(m, []).append(g)
    n = 0
    for s, g in items:
        if g is None or parse_mid(s['mid'])['method'] or len(tpl) < 2:
            continue
        sc = sorted((min(glyph_diff(g, t) for t in ts), k) for k, ts in tpl.items())
        if sc[0][0] <= 0.2 and (len(sc) == 1 or sc[1][0] - sc[0][0] >= 0.15):
            s['mid'] = sc[0][1] + s['mid']
            s['_mid'] = parse_mid(s['mid'])
            s['_method_shape'] = round(sc[0][0], 3)
            n += 1
    return n


def classify(slots: list[dict], paint_open: bool = False) -> None:
    """行の種類: part（部品の明細）/ reserve（保留）/ expense（費用: コードも修理方法も無く金額だけ）/ frame（内板骨格修正）。
    コグニ印刷は 明細 → 手入力の費用 → 内板骨格 の順に同じ表へ刷る（2026-09 シエンタ 4 ページ目）"""
    frame_on, paint_on = False, paint_open  # paint_open: 前のページの塗装明細が【費用】の前で終わっている（C-HR 3 ページ目）
    for s in slots:
        s['_mid'] = parse_mid(s['mid'])
        ctext = nfkc(s['code'])
        if re.fullmatch(r'0000', re.sub(r'\s', '', ctext)):
            s['code'] = ctext = ''  # 部品コード 0000 = コグニの手入力の行（ホンダ系の工場: t12）。コードの無い行として扱う
            s['_manual'] = True  # 工場がコグニで手入力した行: 名称の近い別の部品コードを下書きに当てさせない（M）
        _fm = re.sub(r'\s+', '', nfkc(s['mid']))
        if (s.get('_exact') and not re.search(r'\d', ctext) and not s['_mid']['method'] and _fm and not re.search(r'\d', _fm)
                and 1 <= len(_fm) <= 8 and (re.search(r'\d', s['price']) or re.search(r'\d', s['wage']))):
            s['_manual'] = True
            s['_free_method'] = re.sub(r'\s+', '', s['mid'])   # 手入力の作業行の区分（コグニに無い語でも印字どおり。生成器が区分コード -1 で書く）
        txt = nfkc(s['mid'] + s['name'])
        if paint_on or PAINT_NAME_RE.search(nfkc(s['name'])) or (PAINT_MID_RE.search(nfkc(s['mid'])) and not re.search(r'鈑金|板金|付加', nfkc(s['mid']))):  # 板金の行の損傷面積（2dm2 B 付加）は塗装面積ではない
            s['kind'] = 'paint'; paint_on = True  # ③ で読む。いまは header に写す
        elif re.search(r'保|留', ctext):
            s['kind'] = 'reserve'
        elif frame_on or FRAME_RE.search(txt) or (re.search(r'[nｎ]', s['mark']) and not re.search(r'\d{4}-', s['_mid']['parts_no'])):
            s['kind'] = 'frame'; frame_on = True
        elif not re.search(r'\d', ctext) and not s['_mid']['method'] and (re.search(r'\d', s['price']) or re.search(r'\d', s['wage'])) and not s.get('_manual'):
            s['kind'] = 'expense'   # 部品コード 0000 の行（工場がコグニの明細に手入力した作業・費用）は明細の行のまま（コグニ印刷どおり。t12）
        elif not re.search(r'\d', ctext) and not s['_mid']['method'] and not re.search(r'\d', s['price'] + s['wage']) and not s['_mid']['parts_no']:
            s['kind'] = 'note'  # コードも修理方法も金額も無い = 注記の行（'※一部脱着※'）。明細の行数に数えない
        else:
            s['kind'] = 'part'


def expense_vocab() -> list[str]:
    """費用名の語彙: 既定の名称 ＋ この PC の NEO_check にある reading の費用名（案件が増えるほど寄せやすくなる）"""
    names = [nfkc(x) for x in EXP_NAMES]
    root = os.environ.get('NEO_CHECK_ROOT') or os.path.join(os.path.expanduser('~'), 'Documents', 'NEO_check')
    try:
        for d in os.listdir(root):
            p = os.path.join(root, d, 'reading.json')
            if os.path.exists(p):
                rd = reading_pages.load_json(p)
                for e in (rd.get('expenses') or []):
                    nm = nfkc(str((e or {}).get('name') or '')).strip() if isinstance(e, dict) else ''
                    if nm and nm not in names:
                        names.append(nm)
    except (OSError, ValueError):
        pass
    return names


def _cell(val, unread: bool, raw: str, clean: bool) -> dict:
    return {'price': None, 'wage': None, '_unread': {'price': False, 'wage': False}, '_sure': {'price': False, 'wage': False}, '_why': [],
            '_ocr': {'wage': raw}, 'comment': '', **({'_wage_unclean': True} if (val is not None and not clean) else {})}


def build_expenses(slots: list[dict], clean_img, L: list[dict], vocab: list[str], exact: bool = False) -> list[dict]:
    """費用の行 → reading の expenses（{name, amount, in}）。部品価格の欄 = 部品計、工賃の欄 = 作業計。
    名称は語彙の近いものに寄せ（OCR の '与具代他' → '写真代他'）、寄せきれない名称は 要確認"""
    out = []
    for s in slots:
        raw = nfkc(s['name'])
        scored = sorted(((difflib.SequenceMatcher(None, _kana_skel(raw), _kana_skel(v)).ratio(), -k, v) for k, v in enumerate(vocab)), reverse=True)
        top1 = scored[0] if scored else (0, 0, '')
        second = next((x for x in scored[1:] if _kana_skel(x[2]) != _kana_skel(top1[2])), (0, 0, ''))
        ok_name = exact or top1[0] >= 0.6 or (top1[0] >= 0.5 and top1[0] - second[0] >= 0.15)
        best = (top1[0] if ok_name else 0.0, top1[2])
        name = raw.strip() if exact else (top1[2] if ok_name else raw)
        yc, ph = s['y'], s['pitch']
        xs = [x_at(ln, yc) for ln in L]
        for col, where, x0, x1 in (('price', '部品計', xs[3], xs[4]), ('wage', '作業計', xs[4], xs[5])):
            v, clean = _money_text(re.sub(r'[$#*@nｎ]', '', s[col]))
            has_ink = ink(clean_img, (x0 + 8, yc - ph * 0.3, x1 - 8, yc + ph * 0.3), ph * 0.22) > 0.004
            if v is None and not has_ink and not re.search(r'\d', s[col]):
                continue
            e = _cell(v, has_ink and v is None, s[col], clean)
            e.update({'name': name, 'amount': v, 'in': where, col: v, '_col': col, '_slot': s})
            e['_unread'][col] = v is None
            e['_tent'] = {col: tentative(s[col]) if v is None else None}
            if not ok_name:
                e['_why'].append(f'費用名 OCR「{raw}」を寄せる名称が無い。印字どおりに直す')
            elif best[0] < 0.85:
                e['_ocr']['name'] = raw  # 寄せた（'与具代他' → '写真代他'）。金額が小計で合えば確定
            if v is None:
                e['_why'].append(f'費用の{"部品価格" if col == "price" else "工賃"}の欄に字があるが読めない（{s[col]}）')
            out.append(e)
    return out


def build_frame(slots: list[dict], labor: Optional[int]) -> tuple[dict, list[dict]]:
    """内板骨格修正の行 → reading の frame（{basic, basic_wage, basic_index, items[{code, name, rank, wage, index}]}）と、小計の確かめに使う行"""
    frame: dict = {'items': []}
    cells = []
    for s in slots:
        wage, clean = _money_text(re.sub(r'[$#*@nｎ]', '', s['wage']))
        txt = nfkc(s['mid'] + s['name'])
        c = _cell(wage, False, s['wage'], clean)
        c['wage'] = wage
        c['_tent'] = {'wage': tentative(s['wage']) if wage is None else None}
        c['_unread']['wage'] = wage is None and bool(re.search(r'\d', s['wage']))
        if wage is None and '基本内' not in txt:  # 基本修正作業・ランク A/B/C の行に工賃が読めない（丸ごと落ちた）: 人に回す（Codex 指摘）
            c['_unread']['wage'] = True
            c['_why'].append(f'内板骨格の工賃の欄に字があるが読めない（{s["wage"]}）')
        if '基本修正' in txt or ('基本' in txt and '基本内' not in txt):
            frame['basic'] = True
            frame['basic_wage'] = wage
            if wage and labor:
                frame['basic_index'] = round(wage / labor, 2)
            c['_where'] = 'basic'
        else:
            code = re.sub(r'\D', '', nfkc(s['code']).translate(DIGIT_FIX))
            m = re.search(r'(?:ランク|ﾗﾝｸ)\s*([A-CＡ-Ｃa-c])', txt)
            rank = '基本内' if '基本内' in txt else (nfkc(m.group(1)).upper() if m else '')
            it = {'code': code, 'name': nfkc(s['name']), 'rank': rank}
            if rank != '基本内':
                it['wage'] = wage
                if wage and labor:
                    it['index'] = round(wage / labor, 2)
            if len(code) != 4:
                c['_why'].append(f'内板骨格の部位コードが読めない（{s["code"]}）')
            if not rank:
                c['_why'].append(f'内板骨格のランクが読めない（{s["mid"]}）')
            frame['items'].append(it)
            c['_where'] = it
        cells.append(c)
    return frame, cells


def exps_rowish(exps: list[dict], slots: list[dict]) -> list[dict]:
    """費用の行（1 つの印字行が 部品計・作業計 の 2 件になることがある）を、確認シート用に印字行ごと 1 件にまとめる"""
    out = []
    for s in [x for x in slots if x['kind'] == 'expense']:
        mine = [e for e in exps if e.get('_slot') is s]
        out.append({'comment': ' '.join(e['comment'] for e in mine if e['comment'])})
    return out


def short_row(r: dict):
    def f(v):
        return '' if v in (None, '') else str(v)
    if r.get('neo_name'):  # 印字の名称（工場の書き換え）は dict の行の neo_name に
        d = {k: r.get(k) for k in ('code', 'name', 'neo_name', 'method', 'parts_no', 'index', 'qty', 'price', 'wage', 'flags', 'comment')}
        return {k: v for k, v in d.items() if v not in (None, '')}
    name = f(r['name']).replace('|', '/')
    qty = '' if r['qty'] in (None, 1) else str(r['qty'])
    return '|'.join([f(r['code']), name, f(r['method']), f(r['parts_no']), f(r['index']), qty, f(r['price']), f(r['wage']), f(r['flags']), f(r['comment']).replace('|', '/')])


def check_sheet(img, slots: list[dict], rows: list[dict], dst: str) -> int:
    """要確認の行だけを縦に並べた画像（元画像の行を切り出す。左に行番号）"""
    from PIL import Image, ImageDraw  # type: ignore
    picks = [(i, s) for i, (s, r) in enumerate(zip(slots, rows)) if r['comment'].startswith(UNVERIFIED)]
    if not picks:
        if os.path.exists(dst):
            os.remove(dst)
        return 0
    W = img.size[0]
    ph = int(slots[0]['pitch'])
    tiles = []
    for i, s in picks:
        y0 = max(0, int(s['y'] - ph * 0.6)); y1 = int(s['y'] + ph * 0.6)
        tiles.append((i, img.crop((0, y0, W, y1)).convert('L')))
    lab = 120
    out = Image.new('L', (W + lab, sum(t.size[1] + 6 for _, t in tiles)), 255)
    d = ImageDraw.Draw(out)
    y = 0
    for i, t in tiles:
        out.paste(t, (lab, y))
        d.text((8, y + t.size[1] // 3), f'r{i + 1}', fill=0)
        d.line((0, y + t.size[1] + 3, W + lab, y + t.size[1] + 3), fill=160)
        y += t.size[1] + 6
    out = out.resize((out.size[0] // 2, out.size[1] // 2))
    out.save(dst)
    return len(picks)


# ---------------------------------------------------------------------- メイン
def anchor_pdf(pdf: str, case: str, pages: Optional[set[int]], overwrite: bool, labor: Optional[int], scale: float = 2.0, src: str = '') -> dict:
    from PIL import Image  # type: ignore
    pdir = reading_pages.pages_dir(case)
    odir = os.path.join(pdir, 'ocr')
    os.makedirs(odir, exist_ok=True)
    hdr_path = os.path.join(pdir, 'header.json')
    if src:  # 元案件フォルダの速報・確報から header の車両・顧客・保険を先に埋める（header_auto。既にある値は上書きしない）
        import header_auto  # noqa: PLC0415
        rep = header_auto.find_report(src)
        if rep:
            _h = reading_pages.load_json(hdr_path) if os.path.exists(hdr_path) else {}
            _pages = header_auto.text_pages(rep, 1)
            _wrote = header_auto.apply(_h, header_auto.build(header_auto.parse_report(_pages[0] if _pages else ''), os.path.basename(os.path.normpath(src))), False)
            _h['_auto_from'] = {'report': os.path.basename(rep), 'fields': _wrote}
            reading_pages.save_json(hdr_path, _h)
            print(f'速報・確報から header.json に {len(_wrote)} 項目を書いた（車両・顧客・保険）')
        else:
            print('元案件フォルダに速報・確報（文字層のある報告書）が無い。header.json の車両は手で書く')
    header = reading_pages.load_json(hdr_path) if os.path.exists(hdr_path) else {}
    labor = labor or (int(header['labor_rate']) if str(header.get('labor_rate') or '').isdigit() else None)
    ftx = fitz_text_pages(pdf, odir, pages)  # 文字層のページ（コグニの PDF 出力）は OCR せず字をそのまま使う
    if ftx:
        print(f'文字層のあるページ {sorted(ftx)}: OCR の代わりに PDF の文字を使う（読み違いは起きない）')
    imgs = ocr_prefill.extract_pages(pdf, odir, pages, scale) if len(ftx) < (len(pages) if pages else 10 ** 6) else []
    _have = {pg for pg, _p, _t in imgs}
    imgs = [(pg, ftx[pg][0] if pg in ftx else png, t) for pg, png, t in imgs] + [(pg, ftx[pg][0], '') for pg in sorted(ftx) if pg not in _have]
    imgs.sort(key=lambda x: x[0])
    an = Anchor(header, labor)
    if not an.ok:
        print(f'ADDATA 照合なし: {an.why}。OCR の値だけで下書きする（全行 要確認）')
    else:
        print(f"車両 {an.car.get('CarCode')}（確度 {an.confidence}）で ADDATA 照合する")
    summary = {'pages': [], 'anchor': an.ok}
    vocab = expense_vocab()
    pvocab = paint_vocab()
    fallback = []
    # 1) 全ページを OCR し、行の種類を決める（塗装明細は前のページから続くことがある）
    pdata = []
    paint_open = False
    for pg, png, _text in imgs:
        if not png:
            continue
        img = Image.open(png)
        W, H = img.size
        clean, vert = remove_rules(img)
        L = layout_a(long_vlines(vert, H), W)
        if L is None:
            # 表の見出し（部品価格・工賃・修理方法 …）の字が無いページだけ「表の無いページ」（送り状・再封印申請書: シエンタ 6 ページ目で番号から余計な行ができていた）。
            # 縦線の数だけでは決めない（線のかすれた見積のページを捨てないため。Codex 指摘）
            if pg in ftx:
                _words = ftx[pg][1]
            else:
                _cp = os.path.join(odir, f'page_{pg}.clean.png')
                clean.save(_cp)
                _words = ocr_prefill.run_ocr(_cp)
            _txt = nfkc(''.join(w['text'] for w in _words)).replace(' ', '')
            _no_table = not re.search(r'部品価格|工賃|技術料|修理方法|部品番号|品番|数量|単価|金額', _txt)
            if _no_table:
                print(f'ページ {pg}: 見積の表の無いページ（送り状・申請書など）→ 明細なしとして扱う')
                _dst = os.path.join(pdir, f'page_{pg}.json')
                if overwrite or not os.path.exists(_dst):
                    reading_pages.save_json(_dst, {'page': pg, 'rows_printed': 0, 'blocks': [{'title': '', 'rows': []}], 'note': '表の無いページ（送り状など）。明細なし'})
                continue
            print(f'ページ {pg}: 書式 A の罫線の並びではない → 従来の OCR 先読み（ocr_prefill）にまかせる')
            fallback.append(pg)
            continue
        cpng = os.path.join(odir, f'page_{pg}.clean.png')
        clean.save(cpng)
        exact = pg in ftx
        words = ftx[pg][1] if exact else ocr_prefill.run_ocr(cpng)
        pr = read_page_a(png, clean, L, words, H, exact)
        if not header.get('format'):
            header['format'] = 'A'   # コグニ印刷の表を読んだ（下書きの「分解」を印字どおりにする判定などに使う）
            reading_pages.save_json(hdr_path, header)
        if pr.get('est_date') and not header.get('est_date'):
            header['est_date'] = pr['est_date']  # 見積書の作成日
            reading_pages.save_json(hdr_path, header)
            print(f"見積日（作成日）{pr['est_date']} を header.json の est_date に書いた")
        for x in pr['slots']:
            x['_exact'] = exact
        classify(pr['slots'], paint_open)
        if any(x['kind'] == 'paint' for x in pr['slots']):
            pr['has_paint'] = True
        psl = [x for x in pr['slots'] if x['kind'] == 'paint'] + pr.get('sec_slots', [])
        if not exact:
            reread_paint_mid(img, L, psl)
        if psl:
            paint_open = not any(is_expense_heading(nfkc(x['name'])) for x in psl)   # parse_sections と同じ判定（崩れた '【豊用】' も。Codex 指摘）
        pdata.append({'pg': pg, 'png': png, 'img': img, 'clean': clean, 'cpng': cpng, 'L': L, 'pr': pr, 'psl': psl, 'exact': exact})
    # 修理方法の欄の字の形で、読めなかった欄を決める（見積全体の読めた欄が手本）
    _items = [(x, method_glyph(d['img'], d['L'], x)) for d in pdata for x in d['pr']['slots'] if x.get('kind') in ('part', 'reserve')]
    _nm = methods_by_shape(_items)
    if _nm:
        print(f'修理方法を字の形で {_nm} 欄決めた（同じ見積の中で読めた欄が手本）')
    # 2) 塗装明細はページをまたいでまとめて解釈する
    for d in pdata:
        for x in d['psl']:
            x['_exact'] = bool(d.get('exact'))
    sec = parse_sections([x for d in pdata for x in d['psl']], labor, pvocab, an if an.ok else None)
    for x in sec['exp_slots']:
        x['kind'] = 'expense'
    if sec.get('labor') and not labor and not header.get('labor_rate'):
        labor = sec['labor']
        header['labor_rate'] = labor
        reading_pages.save_json(hdr_path, header)
        print(f'レバーレート {labor:,}（塗装明細の 指数 と 工賃 から）を header.json の labor_rate に書いた')
    paint_unsure_pages = []
    # 3) ページごとに 部品の明細・費用・内板骨格 を確かめて書く（ページ小計 = そのページの工賃の欄に刷られた額の合計。塗装行も含む）
    for d in pdata:
        pg, png, img, clean, cpng, L, pr = d['pg'], d['png'], d['img'], d['clean'], d['cpng'], d['L'], d['pr']
        slots = [x for x in pr['slots'] if x['kind'] in ('part', 'reserve')]
        exp_sl = [x for x in pr['slots'] if x['kind'] == 'expense'] + [x for x in d['psl'] if x.get('kind') == 'expense']
        exps = build_expenses(exp_sl, clean, L, vocab, d.get('exact', False))
        pcells = []
        for x in d['psl']:
            if x.get('kind') == 'expense':
                continue
            if x.get('_pv') is not None:
                c = _cell(x['_pv'], False, str(x['_pv']), True)
                c['wage'] = x['_pv']
                pcells.append(c)
            elif '_pv_tent' in x:
                c = _cell(None, True, x['wage'], False)
                c['_unread']['wage'] = True
                c['_tent'] = {'wage': x['_pv_tent']}
                c['_why'].append(f"塗装の行の工賃の欄に字があるが読めない（{x['wage']}）")
                c['_slot'] = x
                pcells.append(c)
        frame, fcells = build_frame([x for x in pr['slots'] if x['kind'] == 'frame'], labor)
        decide_codes(slots, an if an.ok else None)
        # 塗装明細の区画はあるのに行を読めていないページ（塗装欄が読めない）では小計を使わない
        _sub_ok = not d['psl'] or bool(pcells) or all(x.get('kind') == 'expense' or x.get('_paint_head') for x in d['psl'] if (x.get('wage') or '').strip())
        rows = judge(slots, an if an.ok else None, pr['subtotal'] if _sub_ok else {}, clean, L, exps + fcells + pcells, d.get('exact', False))
        if pcells and not all(c['_sure']['wage'] for c in pcells):
            paint_unsure_pages.append(pg)
        for c in fcells:  # 小計から逆算した工賃を骨格にも戻す
            w = c['_where']
            if w == 'basic':
                frame['basic_wage'] = c['wage']
                if c['wage'] and labor:
                    frame['basic_index'] = round(c['wage'] / labor, 2)
            elif w.get('rank') != '基本内':
                w['wage'] = c['wage']
                if c['wage'] and labor:
                    w['index'] = round(c['wage'] / labor, 2)
        n_chk = check_sheet(img, slots + [x for x in exp_sl] + [x for x in pr['slots'] if x['kind'] == 'frame'],
                            rows + [dict(e) for e in exps_rowish(exps, exp_sl)] + fcells, os.path.join(odir, f'check_page_{pg}.png'))
        marks: dict = {}
        for r in rows:
            for ch in r['flags']:
                if ch in '$#*@':   # 印字の印だけ数える（M 手入力 / R 保留 は転記の印で、印字の右端には無い）
                    marks[ch] = marks.get(ch, 0) + 1
        page_json = {'page': pg, 'rows_printed': len(rows), 'marks': marks, 'blocks': [{'title': '', 'rows': [short_row(r) for r in rows]}]}
        if exps:
            page_json['expenses'] = [{'name': e['name'], 'amount': e[e['_col']], 'in': e['in']} | ({'comment': e['comment']} if e['comment'] else {}) for e in exps]
        if frame.get('items') or frame.get('basic'):
            frame['page'] = pg
            fr_why = [w for c in fcells for w in c['_why']]
            if fr_why:
                frame['comment'] = f'{UNVERIFIED}: ' + ' / '.join(dict.fromkeys(fr_why))
            if not _filled(header.get('frame')):
                header['frame'] = frame
                reading_pages.save_json(hdr_path, header)
                print(f'   内板骨格 {len(frame["items"])} 部位' + (f'・基本 {frame.get("basic_wage")}' if frame.get('basic') else '') + ' を header.json の frame に写した'
                      + (f'（{frame["comment"]}）' if frame.get('comment') else ''))
            else:
                print('   内板骨格は header.json に既にあるので書かない（OCR の読み: ' + json.dumps(frame, ensure_ascii=False)[:200] + '）')
        sub_out = {k: v for k, v in pr['subtotal'].items() if not k.startswith('_')}
        _paint_here = pr['has_paint'] or any(x.get('kind') not in ('expense', 'heading', 'noise') for x in d['psl'])
        if sub_out and not _paint_here:
            page_json['subtotal'] = sub_out  # 費用だけのページは書く（reading_pages が 明細＋費用 の別解で検算する。Codex 指摘）
        elif sub_out:
            page_json['note'] = (f"ページ小計（OCR）{sub_out} は塗装明細の行も含むので subtotal に書かない（塗装明細は header.paint）")
        # 塗装明細・【費用】の区画を読めていない（区画は見えたが行が拾えない / 拾えたが塗装明細として解釈できない）: 人に回す（Codex 指摘）
        _paint_rows_here = [x for x in d['psl'] if x.get('kind') not in ('expense', 'heading', 'noise') and (x['name'] + x['mid'] + x['wage'] + x['price']).strip()]
        _unparsed = (pr['has_paint'] or pr['has_expense']) and not d['psl'] and not exps
        _unparsed = _unparsed or (bool(_paint_rows_here) and sec['paint'] is None)
        # 見出しだけ読めて中身が拾えない区画（【塗装明細】なのに塗装明細が無い・【費用】なのに費用の行が無い）も人に回す（Codex 指摘）
        _unparsed = _unparsed or (any(x.get('_head') == 'paint' for x in d['psl']) and sec['paint'] is None)
        _unparsed = _unparsed or (any(x.get('_head') == 'expense' for x in d['psl']) and not any(x.get('kind') == 'expense' for x in d['psl']))
        if _unparsed:
            page_json['_todo'] = (f'{UNVERIFIED}: このページの塗装明細・【費用】の区画は OCR で読んでいない。画像を見て header.json の paint / expenses に写し、'
                                  'この _todo を消す（残っていると validate / merge が止める）')
        dbg = {'page': pg, 'image': png, 'clean': cpng, 'region': [pr['top'], pr['bottom']], 'subtotal_ocr': sub_out,
               'vlines': [round(ln['x']) for ln in L], 'rows': [{k: v for k, v in r.items()} for r in rows]}
        reading_pages.save_json(os.path.join(pdir, f'page_{pg}.anchor.json'), dbg)
        dst = os.path.join(pdir, f'page_{pg}.json')
        wrote = False
        if overwrite or not os.path.exists(dst):
            reading_pages.save_json(dst, page_json); wrote = True
        for e in exps:
            print(f'   費用 {e["name"]} {e[e["_col"]] if e[e["_col"]] is not None else "?"}（{e["in"]}）' + (f': {e["comment"][len(UNVERIFIED) + 2:]}' if e['comment'] else ''))
        sure = sum(1 for r in rows if not r['comment'])
        print(f'ページ {pg}: 明細 {len(rows)} 行 / ADDATA・小計で確定 {sure} 行 / 要確認 {n_chk} 行'
              + (f'（画像 pages/ocr/check_page_{pg}.png）' if n_chk else '') + ('' if wrote else f'  ※ page_{pg}.json は既にあるので書かない（--overwrite で上書き）'))
        for i, r in enumerate(rows):
            if r['comment']:
                print(f'   r{i + 1} {r["code"] or "----"} {r["name"][:18]}: {r["comment"][len(UNVERIFIED) + 2:]}')
        if page_json.get('_todo'):
            print('   ' + page_json['_todo'])
        summary['pages'].append({'page': pg, 'rows': len(rows), 'sure': sure, 'check': n_chk})
    # 合計欄・塗装明細は PDF の全ページを読んだときだけ header に書く（--pages の一部だけ・最終ページが書式 A でないときに途中の読みを固定しない。Codex 指摘）
    _all_pages = [pg_ for pg_, _png, _t in imgs]
    last_is_a = bool(pdata) and pdata[-1]['pg'] == max(_all_pages)  # 最終ページまで書式 A として読めた
    whole = pages is None and bool(pdata)                            # --pages で一部だけ回していない
    totals_found = False
    # 合計欄（最終ページ）: 課税額計・消費税・合計 を header.totals に（既にあれば書かない）
    if whole and not _filled(header.get('totals')):
        d = pdata[-1]
        tt = read_totals(d['clean'], d['L'], d['pr']['_trows'], d['pr']['_sub'], d.get('exact', False))
        if not last_is_a and not tt.get('taxable'):
            # 最後の書式 A のページに合計欄が無く、その後ろに読めないページがある: 合計欄はそちらかもしれない。値は書かず、止める印だけ残す（Codex 指摘）
            tt = {'why': ['合計欄を読めなかった（最終ページが書式 A でない）。最終ページの画像から header の totals に写す']}
            d = {'pg': max(_all_pages)}
        totals_found = bool(tt.get('taxable'))
        if tt.get('taxable') or tt.get('why'):
            tot_ = {k: tt[k] for k in ('taxable', 'tax', 'total') if tt.get(k)}
            tot_['page'] = d['pg']  # 合計欄が刷られたページ（validate がそのページで OCR未確認 を止める）
            if tt.get('why'):
                tot_['comment'] = f'{UNVERIFIED}: ' + ' / '.join(tt['why'])
            header['totals'] = tot_
            reading_pages.save_json(hdr_path, header)
            print('合計欄: ' + (f"課税額計 {tt['taxable']:,} / 消費税 {tt['tax']:,} / 合計 {tt['total']:,} を header.json の totals に写した（税と合計の関係で確定）"
                                if tt.get('taxable') else tot_.get('comment', '')))
    # 塗装明細（header.paint）: 区画の中の検算（工賃計・追加計・費用計）と、ページ小計での確かめ
    # 塗装明細は、区画が【費用】の見出しで閉じている（＝全部読んだ）か、最終ページまで読めたときだけ書く（途中の読みを固定しない。Codex 指摘）
    paint_closed = any(x.get('_head') == 'expense' for d_ in pdata for x in d_['psl']) or totals_found  # 合計欄が読めた = 表はそこで終わっている（シエンタの塗装一式）
    if sec['paint'] is not None and not (whole and (paint_closed or last_is_a)):
        print('※ 塗装明細の区画を最後まで読めていない（--pages 指定か、区画の終わりが見えない）ので header に書かない。全ページで回すか画像から写す')
        _fp = next((d_['pg'] for d_ in pdata if any(x.get('kind') not in ('expense', 'heading', 'noise') for x in d_['psl'])), None)
        _fpath = os.path.join(pdir, f'page_{_fp}.json') if _fp else ''
        if _fpath and os.path.exists(_fpath):  # そのページに印を残す（header に塗装が無いまま merge まで進まないように）
            _pj = reading_pages.load_json(_fpath)
            if not _pj.get('_todo'):
                _pj['_todo'] = (f'{UNVERIFIED}: このページからの塗装明細を header.json の paint に書いていない（区画の終わりが見えない）。'
                                f'OCR の読み {json.dumps(sec["paint"], ensure_ascii=False)[:200]} を画像で確かめて header の paint に写し、この _todo を消す')
                reading_pages.save_json(_fpath, _pj)
    if whole and (paint_closed or last_is_a) and sec['paint'] is not None:
        pw = list(sec['why'])
        if all(d.get('exact') for d in pdata if d['psl']):
            pw = [w for w in pw if '読み切れない' not in w]
        if paint_unsure_pages:
            pw.append(f'ページ {paint_unsure_pages} の小計で塗装行の額を確かめられない')
        first = next((d['pg'] for d in pdata if d['psl']), None)
        if first is not None:
            sec['paint']['page'] = first
        if pw:
            sec['paint']['comment'] = f'{UNVERIFIED}: ' + ' / '.join(dict.fromkeys(pw))
        if not _filled(header.get('paint')):
            header['paint'] = sec['paint']
            reading_pages.save_json(hdr_path, header)
            p_ = sec['paint']
            print(f"塗装明細: 工賃計 {p_.get('total')} / 材料代 {p_.get('material')} / 塗装行 {len(p_.get('lines') or [])} / 追加 {len(p_.get('other') or [])} を header.json の paint に写した"
                  + (f"（{p_['comment']}）" if p_.get('comment') else '（検算とページ小計で確定）'))
        else:
            print('塗装は header.json に既にあるので書かない（OCR の読み: ' + json.dumps(sec['paint'], ensure_ascii=False)[:300] + '）')
    if fallback:
        ocr_prefill.prefill(pdf, case, set(fallback), scale, overwrite)
    return summary


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('pdf')
    ap.add_argument('case_dir')
    ap.add_argument('--pages', default='')
    ap.add_argument('--overwrite', action='store_true')
    ap.add_argument('--labor', type=int, default=None)
    ap.add_argument('--src', default='', help='元案件フォルダ。速報・確報から header の車両・顧客・保険を先に埋める（header_auto）')
    a = ap.parse_args()
    if sys.platform != 'win32':
        print('Windows 専用（Windows.Media.Ocr）'); return 1
    pages = {int(x) for x in a.pages.split(',') if x.strip()} if a.pages else None
    anchor_pdf(os.path.abspath(a.pdf), os.path.abspath(a.case_dir), pages, a.overwrite, a.labor, src=a.src)
    return 0


if __name__ == '__main__':
    sys.exit(main())
