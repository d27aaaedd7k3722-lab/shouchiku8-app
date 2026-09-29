# -*- coding: utf-8 -*-
"""pdf_pages.py — 見積 PDF を「読みやすい画像」に切り分ける（転記の下ごしらえ。時間短縮用）。

FAX・スキャンの見積 PDF はページ全体を 1 枚で読むと細かい数字（品番・単価）を読み違えやすい。
ページごとに画像にし、明細の帯を上下に分けて拡大した画像を作る。文字層がある PDF は文字も書き出す。

    python .claude/skills/pdf-to-neo/scripts/pdf_pages.py <見積.pdf> <出力フォルダ> [--parts 2] [--width 1650] [--no-rotate]

出力: page_N.png（ページ全体）/ page_N_1.png, page_N_2.png …（上から順に分けて拡大）/ page_N.txt（文字層があるときだけ）
その後 Read ツールで page_N_k.png を順に開いて写す（2026-09-13 ランクル・ベンツで手作業していた切り出しを 1 コマンドにした）。

**PyMuPDF（fitz）があればページを描画する**（2026-09-29 コグニ以外の書式 17 件で直した）:
  - ページの回転（/Rotate 90）をそのまま反映する（埋め込み画像を取り出すと横倒しになっていた）
  - 1 ページに画像が 2 枚以上（上下 2 枚に分けて埋め込んだ FAX）でも全部描く（一番大きい 1 枚だけ出して下半分が消えていた。明細の後半と合計欄が見えない）
  - 文字だけの PDF（ディーラーの概算見積）も画像にする
  - 上下逆さ・横倒しで届いた FAX（回転の指定なし）は、Windows OCR で読める字の数が一番多い向きに回す（--no-rotate で止める）
PyMuPDF が無い PC は従来どおり pypdf で埋め込み画像（一番大きい 1 枚）を取り出す（要 pypdf と Pillow）。
"""
from __future__ import annotations

import argparse
import io
import os
import re
import sys

HERE = os.path.dirname(os.path.realpath(__file__))


def _ocr_score(img, tmp_png: str) -> int:
    """その向きで Windows OCR が読めた日本語・数字の字数（向きの判定用。OCR が使えなければ -1）"""
    try:
        sys.path.insert(0, HERE)
        import ocr_prefill  # noqa: PLC0415
        img.save(tmp_png)
        words = ocr_prefill.run_ocr(tmp_png)
    except Exception:  # noqa: BLE001  OCR が使えない PC
        return -1
    return len(re.findall(r'[぀-ヿ一-鿿0-9]', ''.join(w.get('text', '') for w in words)))


def _upright(img, out_dir: str, text_len: int):
    """画像だけのページ（文字層なし）の向きを OCR の読める字数で決める。戻り値 (画像, 回した角度)"""
    if text_len > 50:
        return img, 0   # 文字層のある PDF は描画の向きが正しい
    tmp = os.path.join(out_dir, '_orient.png')
    small = img.copy()
    small.thumbnail((1600, 1600))
    best = (_ocr_score(small, tmp), 0)
    if best[0] < 0:
        return img, 0
    cands = [180]
    if best[0] < 60:
        cands += [90, 270]
    for ang in cands:
        sc = _ocr_score(small.rotate(ang, expand=True), tmp)
        if sc > best[0] * 1.5 + 10:
            best = (sc, ang)
    try:
        os.remove(tmp)
    except OSError:
        pass
    return (img.rotate(best[1], expand=True) if best[1] else img), best[1]


def _pages_fitz(pdf: str, out_dir: str, rotate: bool):
    """[(ページ番号, PIL 画像, 文字層の文字, 回した角度)]。PyMuPDF が無ければ None"""
    try:
        import fitz  # type: ignore  # noqa: PLC0415
        from PIL import Image  # noqa: PLC0415
    except ImportError:
        return None
    out = []
    doc = fitz.open(pdf)
    for i, page in enumerate(doc, start=1):
        try:
            txt = page.get_text() or ''
        except Exception:  # noqa: BLE001
            txt = ''
        # 長い辺が 3,000 px 前後になる倍率（FAX 200dpi の元画像と同じくらい）
        zoom = max(1.0, 3000 / max(page.rect.width, page.rect.height))
        pix = page.get_pixmap(matrix=fitz.Matrix(zoom, zoom), colorspace=fitz.csRGB)
        img = Image.open(io.BytesIO(pix.tobytes('png'))).convert('RGB')
        ang = 0
        if rotate:
            img, ang = _upright(img, out_dir, len(txt.strip()))
        out.append((i, img, txt, ang))
    return out


def _pages_pypdf(pdf: str):
    try:
        import pypdf
        from PIL import Image
    except ImportError:
        raise SystemExit('PyMuPDF か、pypdf と Pillow が要る（pip install pymupdf / pip install pypdf pillow）。無ければ PDF を Read ツールで直接読む')
    out = []
    for i, pg in enumerate(pypdf.PdfReader(pdf).pages, start=1):
        try:
            txt = pg.extract_text() or ''
        except Exception:  # noqa: BLE001  壊れた文字層は無いものとして扱う
            txt = ''
        imgs = list(pg.images)
        img = max((Image.open(io.BytesIO(x.data)) for x in imgs), key=lambda im: im.size[0] * im.size[1]).convert('RGB') if imgs else None
        out.append((i, img, txt, 0))
    return out


def split_pages(pdf: str, out_dir: str, parts: int = 2, width: int = 1650, top: float = 0.0, bottom: float = 1.0, overlap: float = 0.03,
                rotate: bool = True) -> list[dict]:
    """戻り値: ページごとの {'page', 'full', 'parts': [...], 'text': 文字数, 'rotated': 回した角度}"""
    os.makedirs(out_dir, exist_ok=True)
    pages = _pages_fitz(pdf, out_dir, rotate)
    if pages is None:
        pages = _pages_pypdf(pdf)
    res = []
    for i, img, txt, ang in pages:
        info = {'page': i, 'full': '', 'parts': [], 'text': 0, 'rotated': ang}
        if txt.strip():
            p = os.path.join(out_dir, f'page_{i}.txt')
            open(p, 'w', encoding='utf-8').write(txt)
            info['text'] = len(txt)
        if img is not None:
            full = os.path.join(out_dir, f'page_{i}.png')
            img.save(full)
            info['full'] = full
            w, h = img.size
            y0, y1 = int(h * top), int(h * bottom)
            step = (y1 - y0) / max(1, parts)
            for k in range(parts):
                a = max(y0, int(y0 + step * k - h * overlap)); b = min(y1, int(y0 + step * (k + 1) + h * overlap))  # 境目の行が切れないよう少し重ねる
                crop = img.crop((0, a, w, b))
                if w > width:
                    crop = crop.resize((width, max(1, int(crop.size[1] * width / w))))
                p = os.path.join(out_dir, f'page_{i}_{k + 1}.png')
                crop.save(p)
                info['parts'].append(p)
        res.append(info)
    return res


def main(argv: list) -> int:
    ap = argparse.ArgumentParser(description='見積 PDF をページごとの拡大画像に切り分ける')
    ap.add_argument('pdf')
    ap.add_argument('out_dir')
    ap.add_argument('--parts', type=int, default=2, help='1 ページを上下いくつに分けるか（既定 2。明細が細かいときは 3）')
    ap.add_argument('--width', type=int, default=1650, help='切り出した画像の幅（px）')
    ap.add_argument('--top', type=float, default=0.0, help='明細の帯の上端（ページの高さに対する割合。ヘッダを飛ばすなら 0.2 など）')
    ap.add_argument('--bottom', type=float, default=1.0, help='明細の帯の下端（割合）')
    ap.add_argument('--no-rotate', action='store_true', help='上下逆さ・横倒しの FAX を OCR で起こさない')
    a = ap.parse_args(argv)
    res = split_pages(a.pdf, a.out_dir, a.parts, a.width, a.top, a.bottom, rotate=not a.no_rotate)
    for r in res:
        print(f"page {r['page']}: 画像 {'あり' if r['full'] else 'なし'} / 切り出し {len(r['parts'])} 枚 / 文字層 {r['text']} 字"
              + (f" / {r['rotated']} 度回した（上下逆さ・横倒しの FAX）" if r.get('rotated') else ''))
    print(f'{len(res)} ページ → {a.out_dir}（page_N_k.png を順に Read で開いて写す）')
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
