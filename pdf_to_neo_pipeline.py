#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
pdf_to_neo_pipeline.py  (v2-Iter2)

工場見積PDF → コグニセブン互換 NEO ファイル変換パイプライン。

Iter2 追加要件:
  - classify_pdf_source: 正規表現 (Audatex|アウダテックス|コグニ|Cogni\\s*7?|AUDADAMS|車両見積システム|自動車補修見積システム|Cognitive\\s*Seven) に強化
  - identify_vehicle_in_addata: AddataSearchEngine + difflib fuzzy
  - build_neo_mode_b/c: マッチ→マーカー→generate_neo_file で bytes 生成
  - verify_neo_against_pdf: ERParts SELECT し件数・総額比較
  - process_pdf_to_neo: vehicle_info/items 未提供かつ skip_ocr=False かつ GEMINI_API_KEY あり → OCR
  - 後方互換: Iter1 のシグネチャ維持
"""
from __future__ import annotations

import logging
import os
import re
import sqlite3
import tempfile
from typing import Any, Dict, List, Literal, Optional, TypedDict

logger = logging.getLogger(__name__)
if not logger.handlers:
    _h = logging.StreamHandler()
    _h.setFormatter(logging.Formatter("[pdf_to_neo_pipeline] %(levelname)s %(message)s"))
    logger.addHandler(_h)
    logger.setLevel(logging.INFO)

# ============================================================
# 型定義
# ============================================================
PdfSource = Literal["cogni", "other", "unknown"]
GenerationMode = Literal["A", "B", "C"]

# Iter9: パイプライン全体結果キャッシュ (md5 → process_pdf_to_neo result)
_PIPELINE_CACHE: Dict[str, Dict[str, Any]] = {}
_PIPELINE_CACHE_MAX = 32


def _pdf_md5(b: bytes) -> str:
    import hashlib
    return hashlib.md5(b).hexdigest() if b else ""


def clear_pipeline_cache() -> None:
    _PIPELINE_CACHE.clear()


class VehicleInfo(TypedDict, total=False):
    maker: str
    model_code: str
    model_designation: str
    category_number: str
    color_code: str
    first_reg: str
    type_no: str
    classification: str


class IdentifyResult(TypedDict, total=False):
    found: bool
    vehicle_code: Optional[str]
    confidence: float
    method: str
    notes: str


# 判定キーワード（cogni/Audatex 系） - 後方互換用
_COGNI_KEYWORDS = (
    "Audatex", "AUDATEX", "audatex",
    "Cogni7", "Cogni 7", "COGNI7", "コグニセブン", "コグニ7",
    "アウダテックス", "アウダテッスク",
)

# Iter2: 正規表現（大文字小文字無視）
_COGNI_REGEX = re.compile(
    # Iter R4: キーワード拡張 - 富士通ピットイン/MOTOR EYE/EDER等の他社見積システムも識別
    r"(Audatex|アウダテックス|コグニ|Cogni\s*7?|AUDADAMS|"
    r"車両見積システム|自動車補修見積システム|Cognitive\s*Seven|"
    r"見積\s*書\s*No|見積番号|データ№|データ番号|"
    r"DCS|FUJITSU|富士通)",
    re.IGNORECASE,
)


# ============================================================
# 1. PDFソース分類
# ============================================================
def _extract_pdf_text_layer(pdf_path: str) -> str:
    """PyMuPDF→pypdfium2 順で全ページのテキスト層を連結。失敗時は空文字 (Iter R10)"""
    # PyMuPDF を試す
    try:
        import fitz  # type: ignore
        doc = fitz.open(pdf_path)
        chunks = []
        for page in doc:
            try:
                chunks.append(page.get_text() or "")
            except Exception:
                continue
        doc.close()
        return "\n".join(chunks)
    except Exception as e_fitz:
        logger.debug("fitz失敗→pypdfium2 fallback: %s", e_fitz)
    # pypdfium2 fallback
    try:
        import pypdfium2 as pdfium  # type: ignore
        pdf = pdfium.PdfDocument(pdf_path)
        chunks = []
        for page in pdf:
            try:
                tp = page.get_textpage()
                chunks.append(tp.get_text_range() or "")
            except Exception:
                continue
        return "\n".join(chunks)
    except Exception as e:
        logger.warning("PDFテキスト抽出失敗 %s: %s", pdf_path, e)
        return ""


def _extract_pdf_text_from_bytes(pdf_bytes: bytes) -> str:
    """bytes から PyMuPDF→pypdfium2 fallback でテキスト抽出 (Iter R10)"""
    try:
        import fitz  # type: ignore
        doc = fitz.open(stream=pdf_bytes, filetype="pdf")
        chunks = []
        for page in doc:
            try:
                chunks.append(page.get_text() or "")
            except Exception:
                continue
        doc.close()
        return "\n".join(chunks)
    except Exception:
        pass
    try:
        import pypdfium2 as pdfium  # type: ignore
        import io
        pdf = pdfium.PdfDocument(io.BytesIO(pdf_bytes))
        chunks = []
        for page in pdf:
            try:
                tp = page.get_textpage()
                chunks.append(tp.get_text_range() or "")
            except Exception:
                continue
        return "\n".join(chunks)
    except Exception as e:
        logger.warning("PDFテキスト抽出(bytes)失敗: %s", e)
        return ""


def classify_pdf_source(pdf_path_or_bytes, ocr_text: Optional[str] = "") -> PdfSource:
    """PDFソース判定 (cogni/other/unknown)。

    pdf_path_or_bytes: ファイルパス(str) または bytes（Iter2 仕様兼用）。
    ocr_text: OCR後テキスト（任意）。
    """
    try:
        embedded = ""
        if isinstance(pdf_path_or_bytes, (bytes, bytearray)):
            embedded = _extract_pdf_text_from_bytes(bytes(pdf_path_or_bytes))
        elif isinstance(pdf_path_or_bytes, str):
            if pdf_path_or_bytes and os.path.exists(pdf_path_or_bytes):
                embedded = _extract_pdf_text_layer(pdf_path_or_bytes)
        # 正規表現判定
        for txt in (embedded, ocr_text or ""):
            if txt and _COGNI_REGEX.search(txt):
                return "cogni"
        # キーワード文字列フォールバック
        for txt in (embedded, ocr_text or ""):
            if not txt:
                continue
            for kw in _COGNI_KEYWORDS:
                if kw in txt:
                    return "cogni"
        if (embedded and embedded.strip()) or (ocr_text and ocr_text.strip()):
            return "other"
        return "unknown"
    except Exception as e:
        logger.warning("classify_pdf_source 失敗: %s", e)
        return "unknown"


# ============================================================
# 2. 車種特定
# ============================================================
def identify_vehicle_in_addata(vehicle_info: Dict[str, Any],
                               addata_root: str = r"C:\Addata") -> IdentifyResult:
    """ADDATA で車両を特定する。

    1. AddataSearchEngine 生成
    2. model_code を _vehicle_folder() で存在チェック → exact
    3. 失敗時: ルート下の各メーカーフォルダ(A-Z)配下の vehicle_code 一覧と
       difflib.get_close_matches で fuzzy
    4. addata_root が存在しない → {found:False, vehicle_code:None, confidence:0.0, method:"no_db"}
    """
    result: IdentifyResult = {
        "found": False,
        "vehicle_code": None,
        "confidence": 0.0,
        "method": "none",
        "notes": "",
    }
    try:
        if not vehicle_info:
            result["notes"] = "vehicle_info empty"
            return result
        if not addata_root or not os.path.isdir(addata_root):
            result["method"] = "no_db"
            result["notes"] = f"addata_root not found: {addata_root}"
            return result

        # AddataSearchEngine をインスタンス化（lazy import）
        try:
            from _addata_db_search import AddataSearchEngine  # type: ignore
        except Exception as e:
            result["method"] = "no_db"
            result["notes"] = f"AddataSearchEngine import失敗: {e}"
            return result

        engine = AddataSearchEngine(addata_root)

        model_code = (vehicle_info.get("model_code")
                      or vehicle_info.get("car_model")
                      or "").strip().upper()

        # 1) exact: model_code から _vehicle_folder のフォルダが存在するか
        if model_code:
            try:
                folder = engine._vehicle_folder(model_code)
                if os.path.isdir(folder):
                    result["found"] = True
                    result["vehicle_code"] = model_code
                    result["confidence"] = 1.0
                    result["method"] = "exact"
                    result["notes"] = f"folder={folder}"
                    return result
            except Exception as e:
                logger.debug("exact check skip: %s", e)

        # 2) fuzzy: ルート下のメーカーフォルダ(A-Z)配下の vehicle_code 一覧収集
        candidates: List[str] = []
        try:
            for entry in os.listdir(addata_root):
                p = os.path.join(addata_root, entry)
                if not os.path.isdir(p):
                    continue
                # A-Z 1文字フォルダ想定
                if len(entry) != 1 or not entry.isalpha():
                    continue
                try:
                    for sub in os.listdir(p):
                        if os.path.isdir(os.path.join(p, sub)):
                            candidates.append(sub)
                except OSError:
                    continue
        except OSError as e:
            result["notes"] = f"listdir失敗: {e}"
            return result

        if model_code and candidates:
            import difflib
            close = difflib.get_close_matches(model_code, candidates, n=1, cutoff=0.7)
            if close:
                # SequenceMatcher で score 算出
                ratio = difflib.SequenceMatcher(None, model_code, close[0]).ratio()
                result["found"] = True
                result["vehicle_code"] = close[0]
                result["confidence"] = float(ratio)
                result["method"] = "fuzzy"
                result["notes"] = f"matched={close[0]} ratio={ratio:.2f}"
                return result

        result["notes"] = "no match"
        return result
    except Exception as e:
        logger.warning("identify_vehicle_in_addata 失敗: %s", e)
        result["notes"] = f"error: {e}"
        return result


_GRADE_CACHE: Dict[str, Dict[str, Any]] = {}


def identify_grade_from_items(vehicle_code: str,
                              items: List[Dict[str, Any]],
                              addata_root: str = r"C:\Addata",
                              body_code: int = 0) -> Dict[str, Any]:
    """Iter15: PDFGradeIdentifier で部品名/価格からグレードを推定。
    戻り値: {grade_code, grade_name, confidence, option_codes, source}
    """
    out = {"grade_code": None, "grade_name": None, "confidence": 0.0,
           "option_codes": [], "source": "none"}
    if not vehicle_code or not items or not addata_root or not os.path.isdir(addata_root):
        return out
    # Iter R5: grade キャッシュ (vcode + body_code + items件数で簡易キー)
    cache_key = f"{vehicle_code}:{body_code}:{len(items)}"
    if cache_key in _GRADE_CACHE:
        return dict(_GRADE_CACHE[cache_key])
    try:
        from _addata_db_search import AddataSearchEngine  # type: ignore
        from _grade_identifier import PDFGradeIdentifier  # type: ignore
        engine = AddataSearchEngine(addata_root)
        ident = PDFGradeIdentifier(engine, vehicle_code, body_code=body_code)
        # PDFGradeIdentifier.identify() は内部で items を受け取る形を期待 → 呼び出し方を確認
        try:
            r = ident.identify(items)  # type: ignore
        except TypeError:
            # 古い API: 引数なし → instance に items を渡す
            try:
                ident.items = items  # type: ignore
                r = ident.identify()
            except Exception:
                r = {}
        if isinstance(r, dict):
            out["grade_code"] = r.get("grade_code") or r.get("grade")
            out["grade_name"] = r.get("grade_name")
            out["confidence"] = float(r.get("confidence") or r.get("score") or 0)
            out["option_codes"] = r.get("option_codes") or []
            out["source"] = "PDFGradeIdentifier"
    except Exception as e:
        logger.debug("identify_grade_from_items skip: %s", e)
        out["source"] = f"err:{e}"
    # Iter R5: 結果キャッシュ
    if len(_GRADE_CACHE) > 64:
        _GRADE_CACHE.pop(next(iter(_GRADE_CACHE)))
    _GRADE_CACHE[cache_key] = dict(out)
    return out


# ============================================================
# 3. モード判定
# ============================================================
def decide_mode(found_or_source, source_or_addata=None) -> GenerationMode:
    """found / source からモード A/B/C を決定。

    後方互換: decide_mode(found: bool, source: str)
    Iter2 仕様: decide_mode(source_kind: str, addata_hit: dict)
    """
    # 引数パターンを判別
    if isinstance(found_or_source, str) and isinstance(source_or_addata, dict):
        # Iter2: (source_kind, addata_hit)
        source = found_or_source
        found = bool(source_or_addata.get("found"))
    else:
        # Iter1: (found, source)
        found = bool(found_or_source)
        source = source_or_addata if isinstance(source_or_addata, str) else "unknown"

    if not found:
        return "A"
    if source == "cogni":
        return "B"
    return "C"


# ============================================================
# 4. 品番マーカー
# ============================================================
_PRICE_MISMATCH_MARK = "※部品価格不一致"
_DB_MISS_MARK = "※DB不一致"


def _decorate_part_no(orig: Any, marker: str) -> str:
    base = str(orig or "").strip()[:25]
    if not base:
        return marker
    return f"{base}　{marker}"  # 全角スペース区切り


def _append_remark(item: Dict[str, Any], marker: str):
    """remarks 末尾にマーカー追記（既存 remarks 保持）。"""
    cur = str(item.get("remarks", "") or "")
    if marker in cur:
        return
    item["remarks"] = (cur + " " + marker).strip()


PRICE_MISMATCH_TOL_RATIO = 0.02  # ±2% 以内なら一致とみなす (Iter3)
DB_MISS_SCORE_THRESHOLD = 0.6    # マッチスコア >= 0.6 なら DB不一致マーカー付けない (Iter3)


def _apply_price_mismatch_marker(items: List[Dict[str, Any]],
                                 tol_ratio: float = PRICE_MISMATCH_TOL_RATIO) -> List[Dict[str, Any]]:
    """db_price と unit_price の差を検出して品番にマーカー付与（Iter3: ±tol_ratio 許容）"""
    if not items:
        return items
    out = []
    for it in items:
        nit = dict(it)
        try:
            db_price = nit.get("db_price")
            unit_price = nit.get("unit_price") or nit.get("part_price") or 0
            try:
                db_p = float(db_price) if db_price not in (None, "") else 0.0
            except (TypeError, ValueError):
                db_p = 0.0
            try:
                up = float(unit_price) if unit_price not in (None, "") else 0.0
            except (TypeError, ValueError):
                up = 0.0
            tol_abs = max(db_p, up) * tol_ratio
            if db_p > 0 and up > 0 and abs(db_p - up) > max(tol_abs, 1):
                nit["parts_no"] = _decorate_part_no(nit.get("parts_no"), _PRICE_MISMATCH_MARK)
                nit["price_mismatch"] = True
                _append_remark(nit, _PRICE_MISMATCH_MARK)
        except Exception as e:
            logger.debug("price marker skip: %s", e)
        out.append(nit)
    return out


def _apply_db_miss_marker(items: List[Dict[str, Any]],
                          score_threshold: float = DB_MISS_SCORE_THRESHOLD) -> List[Dict[str, Any]]:
    """match_level == 'L4' か match_score < threshold の行に DB不一致マーカー付与（Iter3）"""
    if not items:
        return items
    out = []
    for it in items:
        nit = dict(it)
        try:
            ml = str(nit.get("match_level", "")).upper()
            score = nit.get("match_score")
            try:
                score_f = float(score) if score not in (None, "") else None
            except (TypeError, ValueError):
                score_f = None
            should_mark = (ml == "L4") or (score_f is not None and score_f < score_threshold)
            if should_mark:
                nit["parts_no"] = _decorate_part_no(nit.get("parts_no"), _DB_MISS_MARK)
                nit["db_miss"] = True
                _append_remark(nit, _DB_MISS_MARK)
        except Exception as e:
            logger.debug("db_miss marker skip: %s", e)
        out.append(nit)
    return out


# ============================================================
# 5. 内部ユーティリティ: テンプレートNEO読込 / generate_neo_file 呼出
# ============================================================
def _load_template_bytes(template_path: Optional[str]) -> bytes:
    if not template_path:
        here = os.path.dirname(os.path.abspath(__file__))
        cand = [
            os.path.join(here, "template_toyota.neo"),
            os.path.join(here, "テンプレート_トヨタ汎用_.neo"),
        ]
        for c in cand:
            if os.path.exists(c):
                template_path = c
                break
    if not template_path or not os.path.exists(template_path):
        raise FileNotFoundError(f"テンプレートNEOが見つかりません: {template_path}")
    with open(template_path, "rb") as f:
        return f.read()


def _fallback_parts_no_from_db(items: List[Dict[str, Any]],
                               vehicle_code: Optional[str],
                               addata_root: str) -> List[Dict[str, Any]]:
    """Iter13: 品番が空の行で、部品名から ADDATA を逆引きして補完。
    高コストなのでvehicle_code が確定している場合のみ実行。
    """
    if not items or not vehicle_code or not addata_root:
        return items
    if not os.path.exists(addata_root):
        return items
    try:
        from _addata_db_search import AddataSearchEngine  # type: ignore
        engine = AddataSearchEngine(addata_root)
        parts_master = engine.get_all_parts(vehicle_code)
        if not parts_master:
            return items
    except Exception as e:
        logger.debug("fallback_parts_no init失敗: %s", e)
        return items

    import difflib
    name_to_pno = {}
    for p in parts_master:
        nm = (p.get("name") or "").strip()
        pno = (p.get("parts_no") or "").strip()
        if nm and pno and nm not in name_to_pno:
            name_to_pno[nm] = pno
    names_list = list(name_to_pno.keys())

    out = []
    hit = 0
    for it in items:
        nit = dict(it) if isinstance(it, dict) else it
        if isinstance(nit, dict) and not (nit.get("parts_no") or nit.get("part_no")):
            nm = str(nit.get("name") or nit.get("parts_name") or "").strip()
            if nm:
                m = difflib.get_close_matches(nm, names_list, n=1, cutoff=0.7)
                if m:
                    nit["parts_no"] = name_to_pno[m[0]]
                    nit["parts_no_source"] = "db_fallback"
                    hit += 1
        out.append(nit)
    if hit:
        logger.info("fallback_parts_no: %d 件補完", hit)
    return out


def _final_dedup_items(items: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
    """Iter14: pipeline側 二重重複除去
    同名+同金額 (正規化name + parts_amount + wage) の連続行を統合。
    OCR内部の重複検知をすり抜けたケースを最終的に救う。
    """
    if not items or len(items) <= 1:
        return items
    seen = set()
    out = []
    for it in items:
        if not isinstance(it, dict):
            out.append(it)
            continue
        try:
            nm = str(it.get("name") or it.get("parts_name") or "").strip().lower()
            pa = int(float(it.get("parts_amount") or it.get("part_price") or 0))
            wg = int(float(it.get("wage") or it.get("labor_fee") or 0))
            ix = str(it.get("index_value") or "").strip()
            key = (nm, pa, wg, ix)
            if nm and key in seen:
                continue
            if nm:
                seen.add(key)
        except Exception:
            pass
        out.append(it)
    return out


def _enforce_grand_total_match(items: List[Dict[str, Any]],
                               pdf_grand_total: int,
                               is_tax_inclusive: bool = True,
                               tax_rate: float = 0.10,
                               tolerance: int = 0) -> List[Dict[str, Any]]:
    """v7.1: pdf_grand_total を真理値として、明細合算が一致するか最終チェック。
    乖離があれば末尾の調整行(なければ新規)に差分を加える。

    pdf_grand_total が税込なら、税抜合計 = grand_total / 1.1 で逆算。
    """
    if not items or pdf_grand_total <= 0:
        return items
    out = list(items)
    target_outtax = pdf_grand_total / (1 + tax_rate) if is_tax_inclusive else pdf_grand_total
    target_outtax = int(round(target_outtax))

    sum_outtax = 0
    for it in out:
        try:
            pa = it.get("parts_amount") or it.get("amount") or 0
            if pa:
                sum_outtax += int(float(pa))
            else:
                up = float(it.get("unit_price") or it.get("part_price") or 0)
                qty = max(int(float(it.get("quantity") or 1)), 1)
                if up > 0:
                    sum_outtax += int(up * qty)
        except Exception:
            pass
        try:
            wg = it.get("wage") or it.get("labor_fee") or 0
            if wg:
                sum_outtax += int(float(wg))
        except Exception:
            pass

    diff = target_outtax - sum_outtax
    if abs(diff) <= tolerance:
        return out

    # 既存の調整行があれば加算、なければ新規作成
    adj_idx = next((i for i, it in enumerate(out) if it.get("is_adjustment_row")), None)
    if adj_idx is not None:
        existing = out[adj_idx]
        cur_pa = int(float(existing.get("parts_amount") or 0))
        existing["parts_amount"] = cur_pa + diff
        existing["amount"] = cur_pa + diff
        existing["unit_price"] = cur_pa + diff
        logger.info("[grand_total_match] 調整行更新 +%d (target=%d sum=%d)", diff, target_outtax, sum_outtax)
    else:
        out.append({
            "name": "※金額調整 (PDF総額一致)",
            "parts_name": "※金額調整",
            "parts_no": "※金額調整",
            "part_no": "※金額調整",
            "quantity": 1,
            "parts_amount": int(diff),
            "amount": int(diff),
            "unit_price": int(diff),
            "wage": 0,
            "labor_fee": 0,
            "category": "",
            "work_code": "",
            "index_value": 0.0,
            "is_adjustment_row": True,
        })
        logger.info("[grand_total_match] 調整行新規 %+d (target=%d sum=%d)", diff, target_outtax, sum_outtax)
    return out


def _enforce_total_match(items: List[Dict[str, Any]],
                         pdf_parts_total: int,
                         pdf_wage_total: int,
                         tolerance: int = 0) -> List[Dict[str, Any]]:
    """v7: PDF表示の部品計/工賃計と明細合算の差分を「※金額調整」行で吸収。
    ADDATA配備時もベタ打ち時も最終合計を PDF表示金額に完全一致させる。

    入力:
      pdf_parts_total: PDF表示の部品計 (税抜)
      pdf_wage_total: PDF表示の工賃計 (税抜)
      tolerance: ±これ以下の差は無視

    動作:
      - sum(parts_amount or unit_price*qty) と pdf_parts_total を比較
      - 差分 > tolerance → 末尾に調整行追加
        * parts_amount = 部品差分
        * wage = 工賃差分
        * parts_no = "※金額調整"
        * name = "※金額調整 (PDF原本との差分吸収)"
    """
    if not items:
        return items
    if pdf_parts_total <= 0 and pdf_wage_total <= 0:
        return items  # PDF総額未取得 → 調整しない
    out = list(items)
    # 明細合算
    sum_parts = 0
    sum_wage = 0
    for it in out:
        try:
            pa = it.get("parts_amount") or it.get("amount") or 0
            if pa:
                sum_parts += int(float(pa))
            else:
                up = float(it.get("unit_price") or it.get("part_price") or 0)
                qty = max(int(float(it.get("quantity") or 1)), 1)
                if up > 0:
                    sum_parts += int(up * qty)
        except Exception:
            pass
        try:
            wg = it.get("wage") or it.get("labor_fee") or 0
            if wg:
                sum_wage += int(float(wg))
        except Exception:
            pass

    diff_parts = pdf_parts_total - sum_parts if pdf_parts_total else 0
    diff_wage = pdf_wage_total - sum_wage if pdf_wage_total else 0

    if abs(diff_parts) <= tolerance and abs(diff_wage) <= tolerance:
        return out  # 既に一致

    if diff_parts == 0 and diff_wage == 0:
        return out

    # 調整行を追加
    adj = {
        "name": "※金額調整 (PDF原本との差分吸収)",
        "parts_name": "※金額調整",
        "parts_no": "※金額調整",
        "part_no": "※金額調整",
        "quantity": 1,
        "parts_amount": int(diff_parts),
        "amount": int(diff_parts),
        "unit_price": int(diff_parts),
        "wage": int(diff_wage),
        "labor_fee": int(diff_wage),
        "category": "",
        "work_code": "",
        "index_value": 0.0,
        "is_adjustment_row": True,
    }
    out.append(adj)
    logger.info("[total_match] adj parts=%+d wage=%+d (PDF parts=%d wage=%d / 明細 parts=%d wage=%d)",
                diff_parts, diff_wage, pdf_parts_total, pdf_wage_total, sum_parts, sum_wage)
    return out


def _normalize_items_for_neo(items: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
    """OCR items を generate_neo_file 期待スキーマに正規化 (Iter6)
    OCR出力キー: name, part_no, quantity, parts_amount, wage, line_total, work_code, index_value
    NEO期待キー: name, parts_no, quantity, unit_price, wage, category
    """
    if not items:
        return items
    out = []
    for it in items:
        if not isinstance(it, dict):
            continue
        nit = dict(it)
        # 品番キー統一
        if not nit.get("parts_no"):
            nit["parts_no"] = nit.get("part_no") or nit.get("part_number") or ""
        # v4: app.generate_neo_file は part_no を読むため、parts_no を part_no にもコピー
        if nit.get("parts_no") and not nit.get("part_no"):
            nit["part_no"] = nit["parts_no"]
        # 数量
        try:
            qty = nit.get("quantity")
            qty_i = int(float(qty)) if qty not in (None, "", 0) else 1
            if qty_i < 1:
                qty_i = 1
        except (TypeError, ValueError):
            qty_i = 1
        nit["quantity"] = qty_i
        # 単価: unit_price 未設定なら parts_amount/qty で算出
        if not nit.get("unit_price"):
            try:
                pa = float(nit.get("parts_amount") or 0)
                if pa > 0 and qty_i > 0:
                    nit["unit_price"] = int(round(pa / qty_i))
                else:
                    nit["unit_price"] = int(float(nit.get("part_price") or 0))
            except (TypeError, ValueError):
                nit["unit_price"] = 0
        # 工賃
        try:
            nit["wage"] = int(float(nit.get("wage") or nit.get("labor_fee") or 0))
        except (TypeError, ValueError):
            nit["wage"] = 0
        # カテゴリ（取替/脱着/修理）
        if not nit.get("category"):
            nit["category"] = nit.get("work_code") or ""
        # 部品名
        if not nit.get("name"):
            nit["name"] = nit.get("parts_name") or nit.get("work_or_part_name") or ""
        out.append(nit)
    return out


def _call_generate_neo(template_bytes: bytes,
                       customer_info: Dict[str, Any],
                       items: List[Dict[str, Any]]) -> bytes:
    """app.generate_neo_file の薄ラッパ。lazy import + items正規化(Iter6)"""
    try:
        from app import generate_neo_file  # type: ignore
    except Exception as e:
        raise RuntimeError(f"app.generate_neo_file の import 失敗: {e}") from e
    deduped = _final_dedup_items(items or [])
    norm_items = _normalize_items_for_neo(deduped)
    neo_bytes, _tp, _tw, _gt = generate_neo_file(
        template_data=template_bytes,
        customer_info=customer_info or {},
        items=norm_items,
        short_parts_wage=0,
        insurance_info={},
        expenses=None,
        is_tax_inclusive=False,
        is_beta_mode=False,
        merge_mode=False,
    )
    return neo_bytes


def _normalize_jp_date(s: str) -> str:
    """v5: 和暦表記 ('R 2. 12. 16' / '令和6年9月' / 'H30.5.1') → YYYYMMDD 8桁文字列。
    変換不能なら "00000000"。既に8桁なら そのまま。"""
    if not s:
        return ""
    s = str(s).strip()
    if not s or s == "不明":
        return ""
    # 既に8桁数字
    if len(s) == 8 and s.isdigit():
        return s
    import re as _re
    # 和暦判定
    era_map = {"R": 2018, "令和": 2018, "H": 1988, "平成": 1988,
               "S": 1925, "昭和": 1925, "T": 1911, "大正": 1911}
    base = None
    rest = s
    for prefix, yr_off in era_map.items():
        if s.startswith(prefix):
            base = yr_off
            rest = s[len(prefix):]
            break
    if base is None:
        # 西暦4桁
        m = _re.search(r"(20\d{2})[\.\-/年]?\s*(\d{1,2})[\.\-/月]?\s*(\d{1,2})?", s)
        if m:
            yr = int(m.group(1))
            mo = int(m.group(2))
            da = int(m.group(3) or 1)
            return f"{yr:04d}{mo:02d}{da:02d}"
        return ""
    # 和暦数字抽出
    m = _re.search(r"(\d+)\D+(\d+)\D+(\d+)", rest)
    if m:
        wy, mo, da = int(m.group(1)), int(m.group(2)), int(m.group(3))
        yr = base + wy
        return f"{yr:04d}{mo:02d}{da:02d}"
    m = _re.search(r"(\d+)\D+(\d+)", rest)
    if m:
        wy, mo = int(m.group(1)), int(m.group(2))
        yr = base + wy
        return f"{yr:04d}{mo:02d}00"
    return ""


def _merge_vehicle_into_customer(vehicle_info: Dict[str, Any],
                                 customer_info: Optional[Dict[str, Any]]) -> Dict[str, Any]:
    cust = dict(customer_info or {})
    # Iter2 (v3): generate_neo_file の Car テーブル書込で使う全キーを伝搬
    keys = (
        "car_serial_no", "car_model_designation", "car_category_number",
        "car_reg_date", "term_date", "car_name", "car_model",
        "color_code", "body_color", "engine_model", "trim_code",
        "grade", "model_year", "mileage", "model_code",
        "customer_name", "owner_name", "postal_no",
        "prefecture", "municipality", "address_other",
        "car_reg_department", "car_reg_division", "car_reg_business", "car_reg_serial",
        "car_weight", "engine_displacement", "kilometer",
        "repair_shop_name",
    )
    for k in keys:
        if vehicle_info.get(k) and not cust.get(k):
            cust[k] = vehicle_info[k]
    # v5: 日付フィールドを YYYYMMDD に正規化
    for date_k in ("car_reg_date", "term_date", "first_reg_date"):
        v = cust.get(date_k)
        if v and not (str(v).isdigit() and len(str(v)) == 8):
            try:
                norm = _normalize_jp_date(str(v))
                if norm:
                    cust[date_k] = norm
                else:
                    # 変換不能なら空文字に倒して app.py の int 変換死を防ぐ
                    cust[date_k] = ""
            except Exception:
                cust[date_k] = ""
    return cust


# ============================================================
# 6. NEO生成 3系統
# ============================================================
def build_neo_mode_a(items: List[Dict[str, Any]],
                     vehicle_info: Dict[str, Any],
                     template_path: Optional[str] = None,
                     customer_info: Optional[Dict[str, Any]] = None) -> bytes:
    """モードA: ベタ打ち (収録外)。OCR項目をそのまま転写。"""
    tpl = _load_template_bytes(template_path)
    cust = _merge_vehicle_into_customer(vehicle_info or {}, customer_info)
    return _call_generate_neo(tpl, cust, items or [])


def build_neo_mode_b(items: List[Dict[str, Any]],
                     vehicle_info: Dict[str, Any],
                     template_path: Optional[str] = None,
                     addata_root: str = r"C:\Addata",
                     customer_info: Optional[Dict[str, Any]] = None) -> bytes:
    """モードB: 完全複製 (cogni判定)。価格不一致マーカー付与。"""
    matched = items or []
    # Iter13: 品番空 → DB逆引き補完
    vcode = (vehicle_info or {}).get("model_code") or (vehicle_info or {}).get("vehicle_code")
    matched = _fallback_parts_no_from_db(matched, vcode, addata_root)
    # v4: フルADDATAマッチング (parts_no_marked, db_price, db_work_index 付与)
    v4_done = False
    try:
        from auto_matching import _full_addata_match  # type: ignore
        matched = _full_addata_match(matched, vehicle_info or {}, addata_root)
        # parts_no を marked で上書き (NEOに反映)
        for it in matched:
            mk = it.get("parts_no_marked")
            if mk is not None:
                it["parts_no"] = mk
                it["part_no"] = mk  # v4: app.generate_neo_file 互換
            # v5-Iter6: DB WI を index_value に反映 (DB値があれば優先)
            db_wi = it.get("db_work_index")
            if db_wi and isinstance(db_wi, (int, float)) and db_wi > 0:
                try:
                    it["index_value"] = round(float(db_wi) / 100.0, 2)
                except Exception:
                    pass
        v4_done = True
    except Exception as e:
        logger.warning("modeB v4 full_match失敗: %s (既存ロジック継続)", e)
    if not v4_done:
        try:
            from auto_matching import match_pdf_items_to_addata  # type: ignore
            matched = match_pdf_items_to_addata(matched, vehicle_info or {}, addata_root)
            for it in matched:
                db_pno = it.get("db_parts_no")
                if db_pno and str(it.get("match_level", "")).upper() in ("L1", "L2"):
                    it.setdefault("orig_parts_no", it.get("parts_no", ""))
                    it["parts_no"] = db_pno
                try:
                    db_p = float(it.get("db_price") or 0)
                    up = float(it.get("unit_price") or 0)
                    if db_p > 0 and up > 0 and abs(db_p - up) >= 1:
                        it["parts_no"] = _decorate_part_no(it.get("parts_no"), _PRICE_MISMATCH_MARK)
                        it["price_mismatch"] = True
                        _append_remark(it, _PRICE_MISMATCH_MARK)
                except (TypeError, ValueError):
                    pass
        except Exception as e:
            logger.warning("modeB マッチング失敗: %s (素通し+価格マーカーのみ)", e)
            matched = _apply_price_mismatch_marker(items or [])

    tpl = _load_template_bytes(template_path)
    cust = _merge_vehicle_into_customer(vehicle_info or {}, customer_info)
    return _call_generate_neo(tpl, cust, matched)


def build_neo_mode_c(items: List[Dict[str, Any]],
                     vehicle_info: Dict[str, Any],
                     template_path: Optional[str] = None,
                     addata_root: str = r"C:\Addata",
                     customer_info: Optional[Dict[str, Any]] = None) -> bytes:
    """モードC: あいまい複製。L4 or db_parts_no 空 → ※ADDATA該当なし マーカー。"""
    matched = items or []
    vcode = (vehicle_info or {}).get("model_code") or (vehicle_info or {}).get("vehicle_code")
    matched = _fallback_parts_no_from_db(matched, vcode, addata_root)
    # v4: フルADDATAマッチング (parts_no_marked 付与) — 成功なら旧ロジックスキップ
    v4_done = False
    try:
        from auto_matching import _full_addata_match  # type: ignore
        matched = _full_addata_match(matched, vehicle_info or {}, addata_root)
        for it in matched:
            mk = it.get("parts_no_marked")
            if mk is not None:
                it["parts_no"] = mk
                it["part_no"] = mk  # v4: app.generate_neo_file 互換
            # v5-Iter6: DB WI を index_value に反映 (DB値があれば優先)
            db_wi = it.get("db_work_index")
            if db_wi and isinstance(db_wi, (int, float)) and db_wi > 0:
                try:
                    it["index_value"] = round(float(db_wi) / 100.0, 2)
                except Exception:
                    pass
        v4_done = True
    except Exception as e:
        logger.warning("modeC v4 full_match失敗: %s", e)
    if v4_done:
        # v4成功 → 旧ロジックはスキップして即返却
        tpl = _load_template_bytes(template_path)
        cust = _merge_vehicle_into_customer(vehicle_info or {}, customer_info)
        return _call_generate_neo(tpl, cust, matched)
    try:
        from auto_matching import match_pdf_items_to_addata  # type: ignore
        matched = match_pdf_items_to_addata(matched, vehicle_info or {}, addata_root)
        # 価格・部品番号は PDF 原文を採用 → parts_no は触らない
        # db_parts_no 空 の行も L4 と同等に扱う（mode_c 仕様）
        for it in matched:
            if not str(it.get("db_parts_no", "") or "").strip():
                it["match_level"] = "L4"
        matched = _apply_db_miss_marker(matched)
    except Exception as e:
        logger.warning("modeC マッチング失敗: %s (全行 L4 とみなしマーク)", e)
        for it in (matched or []):
            it["match_level"] = "L4"
        matched = _apply_db_miss_marker(matched or [])

    tpl = _load_template_bytes(template_path)
    cust = _merge_vehicle_into_customer(vehicle_info or {}, customer_info)
    return _call_generate_neo(tpl, cust, matched)


# ============================================================
# 7. verify_neo_against_pdf
# ============================================================
def verify_neo_against_pdf(neo_bytes: bytes, items: List[Dict[str, Any]]) -> Dict[str, Any]:
    """NEO bytes から AnSvEm0001.sld を取り出し、ERParts を SELECT。
    PDF items の件数と総額を比較する。
    """
    res = {
        "ok": False,
        "count_match": False,
        "total_match": False,
        "neo_count": 0,
        "pdf_count": len(items or []),
        "neo_total": 0,
        "pdf_total": 0,
        "mismatches": [],
    }
    try:
        # PDF total 計算
        pdf_total = 0
        for it in (items or []):
            try:
                up = float(it.get("unit_price") or it.get("part_price") or 0)
                qty = float(it.get("quantity") or 1)
                pdf_total += up * qty
            except (TypeError, ValueError):
                pass
        res["pdf_total"] = pdf_total

        if not neo_bytes:
            res["error"] = "neo_bytes empty"
            return res

        # NEO 展開 → AnSvEm0001.sld 取得
        try:
            from app import find_real_cks, decompress_neo, parse_entries, extract_files  # type: ignore
        except Exception as e:
            res["error"] = f"app helper import失敗: {e}"
            return res

        try:
            real_ck = find_real_cks(neo_bytes)
            full_raw = decompress_neo(neo_bytes, real_ck)
            _mgmt, entries = parse_entries(neo_bytes, real_ck[0])
            files = extract_files(full_raw, entries)
        except Exception as e:
            res["error"] = f"NEO展開失敗: {e}"
            return res

        sld_bytes = files.get("AnSvEm0001.sld")
        if not sld_bytes:
            res["error"] = "AnSvEm0001.sld not found in NEO"
            return res

        # sqlite3 で ERParts SELECT
        tf = tempfile.NamedTemporaryFile(suffix=".db", delete=False)
        tf_name = tf.name
        try:
            tf.write(sld_bytes)
            tf.close()
            conn = sqlite3.connect(tf_name)
            cur = conn.cursor()
            rows = cur.execute(
                "SELECT PartsNo, PartsUnitPriceOutTax, PartsUnitPriceInTax, "
                "PartsPriceOutTax, PartsPriceInTax, PartsCount FROM ERParts"
            ).fetchall()
            conn.close()
            neo_count = len(rows)
            neo_total = 0
            for r in rows:
                # PartsPriceInTax/OutTax のうち利用可能な値で総額算出
                try:
                    in_tax = float(r[4] or 0)
                    out_tax = float(r[3] or 0)
                    val = in_tax if in_tax > 0 else out_tax
                    if val <= 0:
                        # 単価×数量で代替
                        up = float(r[2] or r[1] or 0)
                        qty = float(r[5] or 1)
                        val = up * qty
                    neo_total += val
                except (TypeError, ValueError):
                    pass
            # name_match_pct (Iter4改良): PartsNo+PartsName両方で総合一致率
            try:
                import difflib
                pdf_keys = []
                for it in (items or []):
                    pno = str(it.get("parts_no") or "").strip()
                    pnm = str(it.get("parts_name") or "").strip()
                    if pno or pnm:
                        pdf_keys.append((pno, pnm))
                # NEO の PartsNo も読み出し
                try:
                    conn2 = sqlite3.connect(tf_name)
                    rows2 = conn2.execute("SELECT PartsNo, PartsName FROM ERParts").fetchall()
                    conn2.close()
                except Exception:
                    rows2 = [(r[0], "") for r in rows]
                neo_pnos = [str(r[0] or "").strip() for r in rows2]
                neo_pnms = [str(r[1] or "").strip() for r in rows2]
                if pdf_keys:
                    matched = 0
                    for pno, pnm in pdf_keys:
                        ok = False
                        if pno and (pno in neo_pnos or
                                    difflib.get_close_matches(pno, [n for n in neo_pnos if n], n=1, cutoff=0.7)):
                            ok = True
                        elif pnm and difflib.get_close_matches(pnm, [n for n in neo_pnms if n], n=1, cutoff=0.6):
                            ok = True
                        if ok:
                            matched += 1
                    res["name_match_pct"] = round(100.0 * matched / len(pdf_keys), 1)
                else:
                    res["name_match_pct"] = 0.0
            except Exception as e:
                logger.debug("name_match calc skip: %s", e)
                res["name_match_pct"] = None
            res["neo_count"] = neo_count
            res["neo_total"] = neo_total
            res["count_match"] = (neo_count == res["pdf_count"])
            res["total_match"] = abs(neo_total - pdf_total) < 1.0
            if not res["count_match"]:
                res["mismatches"].append(
                    {"type": "count", "neo": neo_count, "pdf": res["pdf_count"]}
                )
            if not res["total_match"]:
                res["mismatches"].append(
                    {"type": "total", "neo": neo_total, "pdf": pdf_total}
                )
            res["ok"] = bool(res["count_match"] and res["total_match"])
            return res
        finally:
            try:
                os.unlink(tf_name)
            except OSError:
                pass
    except Exception as e:
        logger.warning("verify_neo_against_pdf 例外: %s", e)
        res["error"] = str(e)
        return res


# ============================================================
# 8. ディスパッチャ
# ============================================================
def auto_find_addata() -> Optional[str]:
    """v6: ADDATA を OneDrive 含めて自動検索"""
    try:
        from addata_locator import find_addata
        return find_addata()
    except Exception:
        return None


def process_pdf_to_neo(pdf_path,
                       addata_root: str = r"C:\Addata",
                       template_path: Optional[str] = None,
                       vehicle_info: Optional[Dict[str, Any]] = None,
                       items: Optional[List[Dict[str, Any]]] = None,
                       ocr_text: str = "",
                       customer_info: Optional[Dict[str, Any]] = None,
                       skip_ocr: bool = False,
                       mode_override: Optional[str] = None) -> Dict[str, Any]:
    """E2E ディスパッチャ。

    - vehicle_info/items 未提供かつ skip_ocr=False かつ GEMINI_API_KEY あり → OCR
    - skip_ocr=True または API キー無し → 既存の挙動維持
    - 戻り値に verify 結果も含める
    """
    log: List[str] = []
    warnings: List[str] = []
    out: Dict[str, Any] = {
        "ok": False,
        "mode": None,
        "source": "unknown",
        "source_kind": "unknown",
        "addata": {"found": False, "vehicle_code": None, "confidence": 0.0,
                   "method": "none"},
        "identify": {"found": False, "vehicle_code": None, "confidence": 0.0,
                     "method": "none", "notes": ""},
        "ocr_used": False,
        "neo_bytes": None,
        "vehicle_info": vehicle_info or {},
        "items": items or [],
        "verify": {"ok": False, "count_match": False, "total_match": False,
                   "mismatches": [], "neo_count": 0, "pdf_count": 0},
        "warnings": warnings,
        "fallback": None,
        "log": log,
    }

    # PDF bytes 取得
    pdf_bytes = b""
    try:
        if isinstance(pdf_path, (bytes, bytearray)):
            pdf_bytes = bytes(pdf_path)
        elif isinstance(pdf_path, str) and os.path.exists(pdf_path):
            with open(pdf_path, "rb") as f:
                pdf_bytes = f.read()
    except Exception as e:
        warnings.append(f"PDF読込失敗: {e}")

    # Iter9: パイプライン結果キャッシュ確認
    cache_key = ""
    if pdf_bytes and not vehicle_info and not items and not skip_ocr:
        cache_key = _pdf_md5(pdf_bytes) + f":{mode_override}:{addata_root}"
        if cache_key in _PIPELINE_CACHE:
            cached = dict(_PIPELINE_CACHE[cache_key])
            cached["from_cache"] = True
            return cached

    # 1) OCR (必要時のみ)
    api_key = os.environ.get("GEMINI_API_KEY", "")
    need_vi = vehicle_info is None
    need_items = items is None
    if (need_vi or need_items) and (not skip_ocr) and api_key and pdf_bytes:
        try:
            # Iter11: 車検証OCRと見積書OCRを並列実行（pdf_bytes同一でも別関数なので重複しない）
            from concurrent.futures import ThreadPoolExecutor as _TPE
            _vi_future = None
            if need_vi:
                _ex = _TPE(max_workers=2)
                try:
                    from app import analyze_vehicle_registration  # type: ignore
                    _vi_future = _ex.submit(analyze_vehicle_registration, api_key, pdf_bytes, "application/pdf")
                except Exception as e:
                    vehicle_info = {}
                    warnings.append(f"vehicle OCR submit失敗: {e}")
            if need_vi and _vi_future is not None:
                try:
                    vi = _vi_future.result()
                    if isinstance(vi, dict):
                        vehicle_info = vi
                        out["ocr_used"] = True
                        log.append("OCR vehicle_info OK")
                    else:
                        vehicle_info = {}
                        warnings.append("vehicle OCR 戻り値不正")
                except Exception as e:
                    vehicle_info = {}
                    warnings.append(f"vehicle OCR 失敗: {e}")
            if need_items:
                try:
                    from app import analyze_estimate  # type: ignore
                    res = analyze_estimate(api_key, pdf_bytes, "application/pdf")
                    if isinstance(res, dict) and "items" in res:
                        items = res.get("items", [])
                        ocr_meta_first = res
                    elif isinstance(res, list):
                        items = res
                        ocr_meta_first = {"items": res}
                    else:
                        items = []
                        ocr_meta_first = {}
                    out["ocr_used"] = True
                    out["ocr_meta"] = ocr_meta_first
                    log.append(f"OCR estimate OK ({len(items)} items)")

                    # Iter5 (v3): car_name 正規化ヘルパ
                    def _clean_car_name(name: str, model: str = "") -> str:
                        if not name: return ""
                        name = str(name).strip()
                        # メーカー名のみは除去 (model から本当の車名を取る)
                        makers = {"トヨタ", "ホンダ", "日産", "ニッサン", "マツダ", "スバル",
                                  "スズキ", "ダイハツ", "三菱", "ミツビシ", "レクサス",
                                  "TOYOTA", "HONDA", "NISSAN", "MAZDA", "SUBARU",
                                  "SUZUKI", "DAIHATSU", "MITSUBISHI", "LEXUS"}
                        if name.upper() in {m.upper() for m in makers}:
                            # model から取り出し試行
                            if model:
                                # 例: "3DHB RPS13 TYPER 2000" → "TYPER" など
                                tokens = [t for t in str(model).split()
                                          if not t.isdigit() and len(t) >= 2
                                          and t.upper() not in {m.upper() for m in makers}
                                          and not (len(t) == 4 and t[0].isalpha() and t[1:].isdigit())]
                                if tokens:
                                    return tokens[0][:20]
                            return name  # フォールバック
                        # "不明" 含む等は除去
                        if "不明" in name or "C-IIR" in name:
                            return ""
                        return name
                    # Iter1 (v3): _vehicle_info を vehicle_info に統合
                    # analyze_estimate は見積書PDF内の車名・型式・車台番号を _vehicle_info に格納する
                    est_vi = ocr_meta_first.get("_vehicle_info") if isinstance(ocr_meta_first, dict) else None
                    if isinstance(est_vi, dict) and est_vi:
                        if not isinstance(vehicle_info, dict):
                            vehicle_info = {}
                        # キー名マッピング: OCR出力 → generate_neo_file 期待キー
                        _key_map = {
                            "car_name": "car_name",
                            "car_model": "car_model",  # 補助情報
                            "chassis_no": "car_serial_no",  # 車台番号
                            "color_code": "color_code",
                            "color_name": "body_color",
                            "engine_model": "engine_model",
                            "trim_code": "trim_code",
                            "grade": "grade",
                            "grade_code": "grade_code",   # v10.4: ADDATAマッチング補助
                            "body_code": "body_code",     # v10.4: ADDATAマッチング補助
                            "model_year": "model_year",
                            "mileage": "mileage",
                        }
                        merged = 0
                        for src_k, dst_k in _key_map.items():
                            v = est_vi.get(src_k)
                            if v and v != "不明" and not vehicle_info.get(dst_k):
                                vehicle_info[dst_k] = v
                                merged += 1
                        # car_name 正規化 (Iter5)
                        cn = vehicle_info.get("car_name") or ""
                        cm = vehicle_info.get("car_model") or ""
                        cn_clean = _clean_car_name(cn, cm)
                        if cn_clean and cn_clean != cn:
                            vehicle_info["car_name"] = cn_clean
                            log.append(f"car_name 正規化: {cn!r} → {cn_clean!r}")
                        # car_model から型式コード抽出 (例: "3DHB RPS13 TYPER 2000" → "RPS13")
                        if est_vi.get("car_model") and not vehicle_info.get("model_code"):
                            import re as _re
                            cm = str(est_vi.get("car_model"))
                            m = _re.search(r"\b([A-Z]{1,4}\d{1,4}[A-Z]?)\b", cm)
                            if m:
                                vehicle_info["model_code"] = m.group(1)
                                merged += 1
                        # 修理工場名・受付番号も入れておく
                        rs = ocr_meta_first.get("_repair_shop_name")
                        if rs and not vehicle_info.get("repair_shop_name"):
                            vehicle_info["repair_shop_name"] = rs
                            merged += 1
                        # Iter22-23: vehicle_info の追加フィールド
                        for ext_k in ("model_designation", "category_number",
                                      "first_reg_date", "term_date", "car_reg_no"):
                            ev = est_vi.get(ext_k)
                            if ev and ev != "不明":
                                _dst = {"model_designation": "car_model_designation",
                                        "category_number": "car_category_number",
                                        "first_reg_date": "car_reg_date",
                                        "term_date": "term_date",
                                        "car_reg_no": "car_reg_no"}.get(ext_k, ext_k)
                                if not vehicle_info.get(_dst):
                                    vehicle_info[_dst] = ev
                                    merged += 1
                        # Iter22: customer_info を vehicle_info にマージ
                        cust_info = ocr_meta_first.get("customer_info") or {}
                        if isinstance(cust_info, dict):
                            for c_k, c_v in cust_info.items():
                                if c_v and c_v != "不明" and not vehicle_info.get(c_k):
                                    vehicle_info[c_k] = c_v
                                    merged += 1
                        log.append(f"_vehicle_info マージ: +{merged} keys → {list(vehicle_info.keys())}")

                    # Iter13 v3 (Iter14で停止): リトライは Gemini非決定性で精度悪化リスクあり、
                    # かつ Iter6 thinking_budget=0 単独で十分な速度向上が得られたためコメントアウト

                    # Iter8: 金額誤差自動リカバリ
                    # OCR出力の合計と PDF表示総合計が ±5%超ずれてたら rasterize=ON で再OCR
                    try:
                        pdf_total = float(ocr_meta_first.get("grand_total") or
                                         ocr_meta_first.get("pdf_total") or 0)
                        items_sum = sum(float(it.get("line_total") or 0) for it in items)
                        diff_ratio = abs(items_sum - pdf_total) / pdf_total if pdf_total > 0 else 0
                        if diff_ratio > 0.05 and not skip_ocr:
                            log.append(f"⚠ 金額差{diff_ratio:.1%} → rasterize=ON で再OCR試行")
                            res2 = analyze_estimate(api_key, pdf_bytes, "application/pdf",
                                                    use_rasterize=True)
                            if isinstance(res2, dict) and "items" in res2:
                                items2 = res2.get("items", [])
                                items2_sum = sum(float(it.get("line_total") or 0) for it in items2)
                                diff2 = abs(items2_sum - pdf_total) / pdf_total if pdf_total > 0 else 1
                                if diff2 < diff_ratio:
                                    log.append(f"✅ 再OCR採用 ({diff2:.1%} < {diff_ratio:.1%})")
                                    items = items2
                                    out["ocr_meta"] = res2
                                    out["ocr_retry"] = True
                                else:
                                    log.append(f"× 再OCRも改善せず ({diff2:.1%}) - 元結果を採用")
                    except Exception as e:
                        log.append(f"金額リカバリ判定失敗: {e}")
                except Exception as e:
                    items = []
                    warnings.append(f"estimate OCR 失敗: {e}")
        except Exception as e:
            warnings.append(f"OCR 全体例外: {e}")
    else:
        if skip_ocr:
            log.append("skip_ocr=True (OCRバイパス)")
        elif not api_key:
            log.append("GEMINI_API_KEY 未設定 (OCRバイパス)")

    vehicle_info = vehicle_info or {}
    items = items or []

    # v7: PDF表示総額と明細合算の差分を「※金額調整」行で吸収 (完全一致保証)
    if items and out.get("ocr_meta"):
        try:
            _meta = out["ocr_meta"]
            pdf_p = int(_meta.get("pdf_parts_total") or 0)
            pdf_w = int(_meta.get("pdf_wage_total") or 0)
            pdf_g = int(_meta.get("pdf_grand_total") or 0)
            if pdf_p > 0 or pdf_w > 0:
                items = _enforce_total_match(items, pdf_p, pdf_w, tolerance=0)
                log.append(f"[total_match] parts={pdf_p} wage={pdf_w} 適用")
            # v7.1: grand_total で最終保証 (parts+wage の調整で足りない場合の差分)
            if pdf_g > 0:
                items = _enforce_grand_total_match(items, pdf_g, is_tax_inclusive=True)
                log.append(f"[grand_total_match] grand={pdf_g} 適用")
        except Exception as e:
            log.append(f"total_match 失敗: {e}")

    out["vehicle_info"] = vehicle_info
    out["items"] = items

    # 2) ソース判定 (Iter3: OCR完了後は raw_text 構築して再判定)
    try:
        ocr_combined = ocr_text or ""
        if items:
            try:
                parts = []
                for it in items[:200]:
                    for k in ("parts_name", "parts_no", "category", "remark"):
                        v = it.get(k)
                        if v:
                            parts.append(str(v))
                ocr_combined = (ocr_combined + "\n" + " ".join(parts)).strip()
            except Exception:
                pass
        if vehicle_info:
            try:
                ocr_combined += "\n" + " ".join(str(v) for v in vehicle_info.values() if v)
            except Exception:
                pass
        src = classify_pdf_source(pdf_path if isinstance(pdf_path, str) else pdf_bytes, ocr_combined)
        out["source"] = src
        out["source_kind"] = src
        log.append(f"classify_pdf_source={src} (ocr_len={len(ocr_combined)})")
    except Exception as e:
        warnings.append(f"classify失敗: {e}")
        out["source"] = "unknown"
        out["source_kind"] = "unknown"

    # 3) 車種特定 (v5-Iter2: identify 失敗 → 部品番号逆引き)
    ident = {"found": False, "vehicle_code": None, "confidence": 0.0, "method": "none"}
    try:
        ident = identify_vehicle_in_addata(vehicle_info, addata_root)
        if not ident.get("found") and items and addata_root and os.path.isdir(addata_root):
            try:
                from auto_matching import reverse_lookup_vehicle  # type: ignore
                rev = reverse_lookup_vehicle(items, addata_root, min_hits=2)
                if rev.get("found"):
                    ident["found"] = True
                    ident["vehicle_code"] = rev["vehicle_code"]
                    ident["confidence"] = rev["confidence"]
                    ident["method"] = "reverse_pno"
                    ident["notes"] = f"hits={rev['hits']}/{rev['total']}"
                    if isinstance(vehicle_info, dict) and not vehicle_info.get("model_code"):
                        vehicle_info["model_code"] = rev["vehicle_code"]
                    log.append(f"[reverse_pno] vcode={rev['vehicle_code']} conf={rev['confidence']}")
            except Exception as e:
                log.append(f"reverse_pno失敗: {e}")
        out["identify"] = ident
        out["addata"] = {
            "found": ident.get("found", False),
            "vehicle_code": ident.get("vehicle_code"),
            "confidence": ident.get("confidence", 0.0),
            "method": ident.get("method", "none"),
        }
        log.append(f"identify found={ident.get('found')} method={ident.get('method')}")
        # Iter15: グレード特定（任意・収録ありの時のみ）
        if ident.get("found") and ident.get("vehicle_code"):
            try:
                grade = identify_grade_from_items(
                    ident["vehicle_code"], items, addata_root,
                    body_code=int(vehicle_info.get("body_code") or 0)
                )
                out["grade"] = grade
                if grade.get("grade_code"):
                    if not vehicle_info.get("grade_code"):
                        vehicle_info["grade_code"] = grade["grade_code"]
                    log.append(f"grade={grade.get('grade_code')} conf={grade.get('confidence'):.2f}")
            except Exception as e:
                log.append(f"grade特定スキップ: {e}")
    except Exception as e:
        warnings.append(f"identify失敗: {e}")
        ident = {"found": False, "vehicle_code": None, "confidence": 0.0,
                 "method": "none", "notes": str(e)}
        out["identify"] = ident

    # 4) モード判定
    if mode_override in ("A", "B", "C"):
        mode = mode_override
        log.append(f"mode_override={mode}")
    else:
        mode = decide_mode(bool(ident.get("found")), out["source"])
    out["mode"] = mode
    log.append(f"mode={mode}")

    # 5) NEO生成
    if not (vehicle_info or items):
        log.append("vehicle_info/items 共に空のため NEO生成スキップ")
        out["ok"] = True
        return out

    try:
        if mode == "A":
            neo = build_neo_mode_a(items, vehicle_info, template_path, customer_info)
        elif mode == "B":
            neo = build_neo_mode_b(items, vehicle_info, template_path, addata_root, customer_info)
        else:
            neo = build_neo_mode_c(items, vehicle_info, template_path, addata_root, customer_info)
        out["neo_bytes"] = neo
        log.append(f"NEO生成成功 size={len(neo) if neo else 0}")
        # verify
        try:
            v = verify_neo_against_pdf(neo, items)
            out["verify"] = v
            log.append(f"verify ok={v.get('ok')} count={v.get('count_match')} total={v.get('total_match')}")
        except Exception as e:
            warnings.append(f"verify失敗: {e}")
        out["ok"] = True
    except Exception as e:
        warnings.append(f"NEO生成失敗: {e}")
        out["neo_bytes"] = None
        out["ok"] = False

    # Iter9: 成功結果をキャッシュ
    if cache_key and out.get("ok") and out.get("neo_bytes"):
        if len(_PIPELINE_CACHE) >= _PIPELINE_CACHE_MAX:
            _PIPELINE_CACHE.pop(next(iter(_PIPELINE_CACHE)))
        _PIPELINE_CACHE[cache_key] = {k: v for k, v in out.items()}

    # v10.4: items を CSV bytes 化（NEO 生成に成功している場合のみ。失敗時は付けない）
    try:
        if out.get("ok") and out.get("items"):
            out["csv_bytes"] = items_to_csv_bytes(
                out.get("items") or [],
                out.get("vehicle_info") or {},
                (out.get("vehicle_info") or {}).get("customer_info")
                if isinstance((out.get("vehicle_info") or {}).get("customer_info"), dict)
                else None,
            )
    except Exception as _csv_e:
        logger.debug("items_to_csv_bytes failed: %s", _csv_e)

    return out

# 後方互換 alias
run_pipeline = process_pdf_to_neo


# v10.4: CSV 中間表現エクスポート
def items_to_csv_bytes(items: List[Dict[str, Any]],
                       vehicle_info: Optional[Dict[str, Any]] = None,
                       customer_info: Optional[Dict[str, Any]] = None) -> bytes:
    """items list を CSV bytes（UTF-8 BOM 付き、Excel 対応）にエクスポート。

    列構成（NEO 生成前の可視チェック用）:
      行 / 部品名 / 部品番号(OCR) / DB部品番号 / 数量 / 単価 / DB単価 /
      部品計 / 工賃 / 作業区分 / 指数 / マッチレベル / マーカー / 備考
    """
    import io
    import csv
    buf = io.StringIO()
    buf.write('﻿')  # Excel が UTF-8 を判定する BOM
    writer = csv.writer(buf, quoting=csv.QUOTE_MINIMAL)
    if vehicle_info:
        writer.writerow(["# 車名", vehicle_info.get("car_name", "")])
        writer.writerow(["# 車台番号", vehicle_info.get("car_serial_no", "")])
        writer.writerow(["# 型式", vehicle_info.get("car_model", "")])
        writer.writerow(["# 色", str(vehicle_info.get("color_code", "")) + " " + str(vehicle_info.get("body_color", ""))])
        writer.writerow(["# グレード", vehicle_info.get("grade", "") or vehicle_info.get("grade_code", "")])
        writer.writerow(["# ボディコード", str(vehicle_info.get("body_code", 0))])
    if customer_info:
        writer.writerow(["# 顧客名", customer_info.get("customer_name", "")])
        writer.writerow(["# 受付番号", customer_info.get("receipt_no", "")])
        writer.writerow(["# 修理工場", customer_info.get("repair_shop_name", "")])
    writer.writerow([])
    writer.writerow([
        "行", "部品名", "部品番号(OCR)", "DB部品番号", "数量",
        "単価", "DB単価", "部品計", "工賃", "作業区分",
        "指数", "マッチ", "マーカー付", "備考",
    ])
    for i, it in enumerate(items, 1):
        if not isinstance(it, dict):
            continue
        writer.writerow([
            i,
            it.get("parts_name") or it.get("name", "") or it.get("work_or_part_name", ""),
            it.get("parts_no") or it.get("part_no", "") or it.get("part_number", ""),
            it.get("db_parts_no", ""),
            it.get("quantity", 1),
            it.get("unit_price") or it.get("part_price", 0),
            it.get("db_price") or "",
            it.get("parts_amount") or it.get("amount", 0),
            it.get("wage") or it.get("labor_fee", 0),
            it.get("category") or it.get("work_code", ""),
            it.get("index_value", 0),
            it.get("match_level", ""),
            it.get("parts_no_marked", "") or it.get("pno_marker", ""),
            it.get("match_note", "") or ("※金額調整" if it.get("is_adjustment_row") else ""),
        ])
    return buf.getvalue().encode("utf-8")


if __name__ == "__main__":
    import sys
    print("pdf_to_neo_pipeline v2-Iter2")
    if len(sys.argv) > 1:
        r = process_pdf_to_neo(sys.argv[1], skip_ocr=True)
        print({k: v for k, v in r.items() if k != "neo_bytes"})
