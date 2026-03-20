#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
AI-OCR連携 NEOファイル自動生成Webアプリ v3.2
コグニセブン用NEOファイルを車検証PDF＋見積書PDFから自動生成

【v3.2 追加・修正内容】
- google.generativeai → google.genai SDK移行（FutureWarning解消）
- 並列API呼び出しによる解析高速化（車検証＋見積書同時解析、マルチページ並列処理）
- NEO生成前の金額検証アラート（部品/工賃の差額チェック＋確認必須）
- 「**」工賃の0円処理（工賃欄の「**」は工賃なしとして読み取り）
- ショートパーツ二重計上防止（明細行→Expense自動移行）
- 預託/廃棄処分費用の非課税Expense自動振り分け（LineNo=5）

【v3.1 追加・修正内容】
- 画像前処理（コントラスト・シャープネス強化）によるFAX品質改善
- Gemini構造化JSON出力モード（response_mime_type: application/json）
- 明細行ごとの整合性チェック（数量×単価≠金額の検出・警告）
- 画像前処理のON/OFFオプション（サイドバー）

【v3.0 追加・修正内容】
- APIキーのハードコード除去（サイドバー入力のみ）
- FAXページ自動除外（ページ分類機能）
- 税込/税抜 自動判定（build_estimate_summary）
- 自己修復ループ（_self_correction_retry）
- 辞書ベースバリデーション（validate_and_correct_items）
- PDF→JPEG ラスタライズ（行ズレ防止オプション）
- プロンプト強化（_thought_process + discount_amount + amount_basis）
- 逆算一致時の誤警告抑制（reverse_match）
"""

import warnings
warnings.filterwarnings("ignore", message=".*use_container_width.*")

from dotenv import load_dotenv
load_dotenv()

import streamlit as st
import struct
import zlib
import sqlite3
import tempfile
import os
import datetime
import json
import base64
import io
import re
import math
import traceback
import pandas as pd
from concurrent.futures import ThreadPoolExecutor, as_completed

# PDF生成用 ReportLab
from reportlab.pdfgen import canvas
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
from reportlab.lib.pagesizes import A4
from reportlab.lib.units import mm

# ============================================================
# 定数・設定
# ============================================================
SCRIPT_DIR        = os.path.dirname(os.path.abspath(__file__))
TEMPLATE_FILENAME = "テンプレート_トヨタ汎用_.neo"
TEMPLATE_PATH     = os.path.join(SCRIPT_DIR, TEMPLATE_FILENAME)
TAX_RATE          = 0.10
# Streamlit Cloud の st.secrets にも対応（ローカルは .env を使用）
try:
    GEMINI_API_KEY = st.secrets.get('GEMINI_API_KEY', os.environ.get('GEMINI_API_KEY', ''))
except Exception:
    GEMINI_API_KEY = os.environ.get('GEMINI_API_KEY', '')
GEMINI_MODEL      = "gemini-2.5-flash"          # フォールバック（動的に上書きされる）
CONFIDENCE_THRESHOLD = 0.6

# 優先順位付きのモデル候補リスト（上位が最新・高精度）
_PREFERRED_MODELS = [
    "gemini-3.1-pro-preview",
    "gemini-3-pro-preview",
    "gemini-2.5-pro",
    "gemini-2.5-flash",
]
_FALLBACK_MODEL = "gemini-2.5-flash"


_model_availability_cache: dict = {}  # key: api_key_hash, value: list of model IDs

def get_available_gemini_models(api_key: str) -> list:
    """APIキーで利用可能なGeminiモデルを確認して返す（優先順位付き）。
    モジュールレベルキャッシュで結果を保持（サーバー再起動まで有効）。"""
    if not api_key:
        return [_FALLBACK_MODEL]
    cache_key = api_key[-8:]  # セキュリティのため末尾8文字をキーに使用
    if cache_key in _model_availability_cache:
        return _model_availability_cache[cache_key]
    try:
        import google.genai as genai
        client = genai.Client(api_key=api_key)
        available = []
        for model_id in _PREFERRED_MODELS:
            try:
                # 軽量テストリクエストで利用可否を確認（max_output_tokens=100で思考モデルも対応）
                client.models.generate_content(
                    model=model_id,
                    contents=["ping"],
                    config={"max_output_tokens": 100},
                )
                available.append(model_id)
            except Exception as e:
                err = str(e)
                # 404/利用不可 → スキップ、それ以外のエラー（レート制限等）→ 利用可能と仮定
                if '404' not in err and 'NOT_FOUND' not in err and 'no longer available' not in err:
                    available.append(model_id)
        result = available if available else [_FALLBACK_MODEL]
        _model_availability_cache[cache_key] = result
        return result
    except Exception:
        return [_FALLBACK_MODEL]


def get_default_gemini_model(api_key: str) -> str:
    """利用可能なモデルの中から最優先モデルを返す。"""
    models = get_available_gemini_models(api_key)
    return models[0] if models else _FALLBACK_MODEL
SELF_CORRECTION_THRESHOLD = 0   # 差額が1円でもあれば自己修復を試行（100%一致を目指す）

DOS_DBVER = bytes.fromhex('334cc198')   # AnDBVersion.ini 固定値
DOS_IMGE  = bytes.fromhex('2c365a67')   # AnSvImge.ini 固定値

# ============================================================
# 全角→半角カタカナ変換テーブル
# ============================================================
FULL_TO_HALF_KANA = {
    'ア': 'ｱ', 'イ': 'ｲ', 'ウ': 'ｳ', 'エ': 'ｴ', 'オ': 'ｵ',
    'カ': 'ｶ', 'キ': 'ｷ', 'ク': 'ｸ', 'ケ': 'ｹ', 'コ': 'ｺ',
    'サ': 'ｻ', 'シ': 'ｼ', 'ス': 'ｽ', 'セ': 'ｾ', 'ソ': 'ｿ',
    'タ': 'ﾀ', 'チ': 'ﾁ', 'ツ': 'ﾂ', 'テ': 'ﾃ', 'ト': 'ﾄ',
    'ナ': 'ﾅ', 'ニ': 'ﾆ', 'ヌ': 'ﾇ', 'ネ': 'ﾈ', 'ノ': 'ﾉ',
    'ハ': 'ﾊ', 'ヒ': 'ﾋ', 'フ': 'ﾌ', 'ヘ': 'ﾍ', 'ホ': 'ﾎ',
    'マ': 'ﾏ', 'ミ': 'ﾐ', 'ム': 'ﾑ', 'メ': 'ﾒ', 'モ': 'ﾓ',
    'ヤ': 'ﾔ', 'ユ': 'ﾕ', 'ヨ': 'ﾖ',
    'ラ': 'ﾗ', 'リ': 'ﾘ', 'ル': 'ﾙ', 'レ': 'ﾚ', 'ロ': 'ﾛ',
    'ワ': 'ﾜ', 'ヲ': 'ｦ', 'ン': 'ﾝ',
    'ァ': 'ｧ', 'ィ': 'ｨ', 'ゥ': 'ｩ', 'ェ': 'ｪ', 'ォ': 'ｫ',
    'ッ': 'ｯ', 'ャ': 'ｬ', 'ュ': 'ｭ', 'ョ': 'ｮ',
    'ガ': 'ｶﾞ', 'ギ': 'ｷﾞ', 'グ': 'ｸﾞ', 'ゲ': 'ｹﾞ', 'ゴ': 'ｺﾞ',
    'ザ': 'ｻﾞ', 'ジ': 'ｼﾞ', 'ズ': 'ｽﾞ', 'ゼ': 'ｾﾞ', 'ゾ': 'ｿﾞ',
    'ダ': 'ﾀﾞ', 'ヂ': 'ﾁﾞ', 'ヅ': 'ﾂﾞ', 'デ': 'ﾃﾞ', 'ド': 'ﾄﾞ',
    'バ': 'ﾊﾞ', 'ビ': 'ﾋﾞ', 'ブ': 'ﾌﾞ', 'ベ': 'ﾍﾞ', 'ボ': 'ﾎﾞ',
    'パ': 'ﾊﾟ', 'ピ': 'ﾋﾟ', 'プ': 'ﾌﾟ', 'ペ': 'ﾍﾟ', 'ポ': 'ﾎﾟ',
    'ヴ': 'ｳﾞ', 'ー': 'ｰ',
    '。': '｡', '「': '｢', '」': '｣', '、': '､', '・': '･',
}


# ============================================================
# ユーティリティ関数
# ============================================================

def to_halfwidth_katakana(text):
    """全角カタカナ・全角英数字・全角記号を半角に変換（部品名用）
    変換対象: カタカナ→半角カタカナ、英数字→半角英数字、一部記号→半角記号
    漢字など半角変換不可の文字はそのまま全角を維持する。
    """
    if not text:
        return text
    result = []
    for ch in text:
        # まずカタカナ変換テーブルをチェック
        if ch in FULL_TO_HALF_KANA:
            result.append(FULL_TO_HALF_KANA[ch])
        # 全角英大文字 Ａ-Ｚ → A-Z
        elif '\uff21' <= ch <= '\uff3a':
            result.append(chr(ord(ch) - 0xFEE0))
        # 全角英小文字 ａ-ｚ → a-z
        elif '\uff41' <= ch <= '\uff5a':
            result.append(chr(ord(ch) - 0xFEE0))
        # 全角数字 ０-９ → 0-9
        elif '\uff10' <= ch <= '\uff19':
            result.append(chr(ord(ch) - 0xFEE0))
        # 全角スペース → 半角スペース
        elif ch == '\u3000':
            result.append(' ')
        # 全角記号の一部 → 半角記号
        elif ch == '\uff08':  # （ → (
            result.append('(')
        elif ch == '\uff09':  # ） → )
            result.append(')')
        elif ch == '\uff0d':  # － → -
            result.append('-')
        elif ch == '\uff0f':  # ／ → /
            result.append('/')
        elif ch == '\uff0e':  # ． → .
            result.append('.')
        elif ch == '\uff0c':  # ， → ,
            result.append(',')
        else:
            result.append(ch)
    return ''.join(result)


def datetime_to_dos(dt):
    """Python datetime → DOS日時バイト列(4B)"""
    dos_date = ((dt.year - 1980) << 9) | (dt.month << 5) | dt.day
    dos_time = (dt.hour << 11) | (dt.minute << 5) | (dt.second // 2)
    return struct.pack('<HH', dos_date, dos_time)


def get_era_info(date_str):
    """YYYYMMDD文字列 → (和暦名, 和暦年4桁ゼロ埋め)"""
    if not date_str or len(date_str) < 4 or date_str == '00000000':
        return '令和', '0000'
    year = int(date_str[:4])
    if year >= 2019:
        return '令和', f'{year - 2018:04d}'
    elif year >= 1989:
        return '平成', f'{year - 1988:04d}'
    elif year >= 1926:
        return '昭和', f'{year - 1925:04d}'
    return '令和', '0000'


def repair_truncated_json(text):
    """途中で切れたJSONを修復して読み取り可能にする"""
    if not text:
        return text
    text = text.strip()
    # 配列が未閉じ
    open_brackets = text.count('[') - text.count(']')
    open_braces   = text.count('{') - text.count('}')
    for _ in range(open_brackets):
        text += ']'
    for _ in range(open_braces):
        text += '}'
    # 末尾のカンマ除去
    text = re.sub(r',\s*([}\]])', r'\1', text)
    return text


def extract_json_from_response(text):
    """GeminiレスポンスからJSONオブジェクトを抽出"""
    if not text:
        return {}
    # コードブロック除去
    cleaned = re.sub(r'```(?:json)?', '', text)
    cleaned = re.sub(r'```', '', cleaned).strip()
    # JSON部分を抽出
    match = re.search(r'\{.*\}', cleaned, re.DOTALL)
    if match:
        json_str = match.group(0)
        try:
            return json.loads(json_str)
        except json.JSONDecodeError:
            try:
                return json.loads(repair_truncated_json(json_str))
            except Exception:
                pass
    return {}


def get_mime_type(filename):
    """ファイル名からMIMEタイプを判定"""
    if not filename:
        return 'application/octet-stream'
    ext = filename.lower().rsplit('.', 1)[-1]
    mime_map = {
        'pdf':  'application/pdf',
        'jpg':  'image/jpeg',
        'jpeg': 'image/jpeg',
        'png':  'image/png',
        'webp': 'image/webp',
        'bmp':  'image/bmp',
        'tiff': 'image/tiff',
        'tif':  'image/tiff',
        'heic': 'image/heic',
        'heif': 'image/heif',
    }
    return mime_map.get(ext, 'application/octet-stream')


def safe_int(val, default=0):
    """OCR由来の「1個」「19,550円」「1.00」「8本」「**」なども整数化"""
    if val is None or val == '' or val == '*' or val == '**':
        return default
    if isinstance(val, str) and val.strip().replace('*', '') == '':
        return default
    if isinstance(val, int):
        return val
    if isinstance(val, float):
        return int(round(val))
    s = str(val).strip()
    # 単位除去
    s = re.sub(r'[個本枚セット台式時間]$', '', s)
    s = re.sub(r'[円¥,，\s]', '', s)
    s = re.sub(r'[^\d.\-]', '', s)
    if not s or s == '-':
        return default
    try:
        return int(round(float(s)))
    except (ValueError, OverflowError):
        return default


def safe_float(val, default=0.0):
    """安全な浮動小数変換"""
    if val is None:
        return default
    try:
        return float(val)
    except (ValueError, TypeError):
        return default


def safe_str(val, default=''):
    """安全な文字列変換"""
    if val is None:
        return default
    return str(val)


def replace_xml_tag(text, tag_name, value):
    """XMLタグの中身を現在値に関係なく置換"""
    pattern = rf'<{re.escape(tag_name)}>[^<]*</{re.escape(tag_name)}>'
    replacement = f'<{tag_name}>{value}</{tag_name}>'
    result = re.sub(pattern, replacement, text)
    # 空タグ形式も対応
    empty_pattern = rf'<{re.escape(tag_name)}/>'
    result = result.replace(empty_pattern, replacement)
    return result


def replace_ini_value(text, key, value):
    """INIキー値を確実に更新"""
    pattern = rf'^({re.escape(key)}\s*=).*$'
    replacement = rf'\g<1>{value}'
    return re.sub(pattern, replacement, text, flags=re.MULTILINE)


# ============================================================
# NEO バイナリ解析
# ============================================================

def find_real_cks(data, start=424):
    """comp_len連鎖法でCK位置を特定（偽CK除外）"""
    all_ck = []
    for i in range(start, len(data) - 1):
        if data[i] == 0x43 and data[i + 1] == 0x4B:
            all_ck.append(i)
    if not all_ck:
        return []
    real_ck = []
    idx = 0
    while idx < len(all_ck):
        ck = all_ck[idx]
        real_ck.append(ck)
        cl = struct.unpack('<H', data[ck - 4:ck - 2])[0]
        exp = ck + cl + 8
        found = False
        for j in range(idx + 1, len(all_ck)):
            if all_ck[j] == exp:
                idx = j
                found = True
                break
        if not found:
            break
    return real_ck


def decompress_neo(data, real_ck):
    """辞書連鎖展開でrawデータを復元"""
    full_raw = b''
    for i, ck in enumerate(real_ck):
        start = ck + 2
        end   = real_ck[i + 1] - 8 if i + 1 < len(real_ck) else len(data)
        chunk = data[start:end]
        if i == 0:
            raw = zlib.decompress(chunk, -15)
        else:
            dobj = zlib.decompressobj(-15, zdict=full_raw[-32768:])
            raw  = dobj.decompress(chunk)
        full_raw += raw
    return full_raw


def parse_entries(data, first_ck):
    """管理領域とファイルテーブルを解析"""
    table       = data[424:first_ck]
    first_entry = None
    for i in range(len(table) - 7):
        if table[i + 6] == 0x5C and struct.unpack_from('<H', table, i + 4)[0] == 0x0020:
            first_entry = i
            break
    if first_entry is None:
        raise ValueError("ファイルテーブルのエントリが見つかりません")
    mgmt    = table[:first_entry]
    entries = []
    pos     = first_entry
    while pos < len(table):
        if pos + 6 >= len(table):
            break
        if table[pos + 6] != 0x5C:
            pos += 1
            continue
        dos_bytes = table[pos:pos + 4]
        nul       = table.find(b'\x00', pos + 7)
        if nul == -1:
            break
        fn        = table[pos + 7:nul].decode('cp932', errors='replace')
        remaining = len(table) - (nul + 1)
        if remaining >= 10:
            sz       = struct.unpack_from('<I', table, nul + 1)[0]
            off      = struct.unpack_from('<I', table, nul + 5)[0]
            is_normal = sz < 10_000_000 and off < 10_000_000
        else:
            sz, off, is_normal = None, None, False
        if is_normal:
            entries.append({'name': fn, 'size': sz, 'offset': off, 'is_last': False, 'dos': dos_bytes})
            pos = nul + 11
        else:
            entries.append({'name': fn, 'size': None, 'offset': None, 'is_last': True, 'dos': dos_bytes})
            pos = len(table)
    return mgmt, entries


def extract_files(full_raw, entries):
    """rawデータから12ファイルを切り出し"""
    files        = {}
    normal_total = 0
    for e in entries:
        if not e['is_last']:
            files[e['name']] = full_raw[e['offset']:e['offset'] + e['size']]
            normal_total    += e['size']
    last_entry = [e for e in entries if e['is_last']]
    if not last_entry:
        raise ValueError("最後エントリ（hidden先頭ファイル）が見つかりません")
    last_name         = last_entry[0]['name']
    files[last_name]  = full_raw[0:len(full_raw) - normal_total]
    return files


# ============================================================
# 内部ファイル更新: AnSMB.txt（見積本体SQLite）
# ============================================================

def update_ansmb(db_bytes, items, short_parts_wage, expenses=None, is_tax_inclusive=False, is_beta_mode=False):
    """ERParts/Expense/Total を更新（値引き行の負工賃も対応）
    expenses: {
        'towing': レッカー費用,              # LineNo=1
        'rental_car': 代車費用,              # LineNo=2
        'short_parts': ショートパーツ,       # LineNo=4（short_parts_wageと同義）
        'tax_exempt': 非課税費用,            # LineNo=5（消費税なし）
    }
    is_tax_inclusive: True の場合、items の金額は税込値として扱い、
                     OutTax/InTax/Tax を正しく逆算する。
    is_beta_mode: True の場合、ベタ打ちモード（未マッチ部品に※を付与しない）
    """
    if expenses is None:
        expenses = {}
    tf = tempfile.NamedTemporaryFile(suffix='.db', delete=False)
    tf.write(db_bytes)
    tf.close()
    conn = sqlite3.connect(tf.name)
    cur  = conn.cursor()
    cur.execute('DELETE FROM ERParts')
    # 全Expense行をクリア（LineNo=1,2,3,4,5）
    for lno in (1, 2, 3, 4, 5):
        cur.execute("""UPDATE Expense SET
            WageEnabled=0, WageOutTax=0, WageInTax=0, WageTax=0
            WHERE LineNo=?""", (lno,))
    total_parts = 0
    total_wages = 0
    for i, item in enumerate(items):
        name   = item.get('name', '')
        
        # Addataのマスタと一致しており、ユーザーがUIで名前を意図的に上書き変更していない場合はマスタ名称と品番を採用
        parts_no = ''
        m_level = item.get('_match_level', 99)
        if m_level <= 3 and item.get('_master_name'):
            # ユーザーが編集画面でOCR名称をそのままにしていた場合のみマスタ名に置換
            # （手動で全く違う名前に直した場合はそちらを尊重する）
            if name == item.get('_original_name', name) or name == item.get('_master_name'):
                name = item.get('_master_name')
                parts_no = item.get('_master_part_no', '')
        
        # 未マッチ（またはそれに準ずる低マッチレベル）部品には先頭に「※」を付与
        # ベタ打ちモードではDB照合を行わないため※を付けない
        if not is_beta_mode and (m_level >= 4 or m_level == 0):
            if not name.startswith('※'):
                name = '※' + name
        
        method = item.get('method', '')
        qty    = safe_int(item.get('quantity', 1), 1)
        if qty < 1:
            qty = 1
        if 'parts_amount' in item:
            parts_total = safe_int(item.get('parts_amount', 0))
        else:
            unit_price  = safe_int(item.get('unit_price', 0))
            parts_total = unit_price * qty
            
        # (変更: 自動的に _master_price で上書きしないことで、OCRの合計額と常に一致させる運用とする)
                
        wage     = safe_int(item.get('wage', 0))
        rec_no   = i + 1
        line_no  = rec_no * 10
        wage_total  = wage
        if is_tax_inclusive:
            # 税込: 金額は既に税込値 → OutTax=税抜逆算, InTax=そのまま, Tax=差額
            if parts_total != 0:
                parts_outtax = round(parts_total / (1 + TAX_RATE))
                parts_intax  = parts_total
                parts_tax    = parts_total - parts_outtax
            else:
                parts_outtax = 0; parts_intax = 0; parts_tax = 0
            if wage_total != 0:
                wage_outtax  = round(abs(wage_total) / (1 + TAX_RATE))
                if wage_total < 0:
                    wage_outtax = -wage_outtax
                wage_intax   = wage_total
                wage_tax     = wage_total - wage_outtax
            else:
                wage_outtax = 0; wage_intax = 0; wage_tax = 0
        else:
            # 税抜: 従来通り
            parts_outtax = parts_total
            parts_tax    = round(parts_total * TAX_RATE) if parts_total != 0 else 0
            parts_intax  = parts_total + parts_tax if parts_total != 0 else 0
            wage_outtax  = wage_total
            wage_tax_abs = round(abs(wage_total) * TAX_RATE) if wage_total != 0 else 0
            wage_tax     = wage_tax_abs if wage_total >= 0 else -wage_tax_abs
            wage_intax   = wage_total + wage_tax if wage_total != 0 else 0
        total_parts += parts_outtax
        total_wages += wage_outtax
        # コグニセブンは -1 を空白として表示する（0やNULLは「0」と表示される）
        db_parts_total = parts_outtax if parts_total != 0 else -1
        db_parts_intax = parts_intax  if parts_total != 0 else -1
        db_parts_tax   = parts_tax    if parts_total != 0 else -1
        db_wage_total  = wage_outtax  if wage_total  != 0 else -1
        db_wage_intax  = wage_intax   if wage_total  != 0 else -1
        db_wage_tax    = wage_tax     if wage_total  != 0 else -1
        # 部品金額がある行のみ数量を設定。脱着など部品なし行は -1（空白）
        db_qty = qty if parts_total != 0 else -1
        # ── Addata マスタ照合結果から PartsCode / PartsCodeSub / DisposalCode を設定 ──
        _disposal_map = {'取替': 1, '脱着': 2, '修理': 3, '板金': 4}
        disposal_code = _disposal_map.get(method, -1)
        parts_code = item.get('_master_section_code', '')  # 部品コード大区分（例: '01'）
        _branch_raw = item.get('_master_branch_code', '')  # 枝番（例: '00101', '001AA'）
        # PartsCodeSub は SQLite integer 型。数値変換できる枝番のみ整数で保存
        try:
            parts_code_sub = int(_branch_raw) if _branch_raw and _branch_raw.isdigit() else -1
        except Exception:
            parts_code_sub = -1
        cur.execute("""INSERT INTO ERParts (
            RecordNo, LineNo, PartsCode, PartsCodeSub, DisposalCode,
            DisposalName, DisposalNameStandard, PartsName, PartsNameStandard,
            PartsNo, PartsNoStandard,
            PartsPriceOutTax, PartsPriceInTax, PartsPriceTax,
            PartsUnitPriceOutTax, PartsUnitPriceInTax, PartsUnitPriceTax,
            PartsPriceStandardOutTax, PartsPriceStandardInTax, PartsPriceStandardTax,
            PartsPriceByManual,
            Time, TimeStandard,
            WageOutTax, WageInTax, WageTax,
            WageStandardOutTax, WageStandardInTax, WageStandardTax,
            WageByManual, PartsCount,
            ChangeTotalOutTax, ChangeTotalInTax, ChangeTotalTax,
            PartsFileTime, WorkCode, ConstructGroup,
            OrderFlag, Provisional, PartsPriceFlag, DuplicateFlag,
            BlockCode, WageFileTime, ShapeModifyTime,
            DamageArea, DamageRank,
            DamageRankBtn1, DamageRankBtn2, DamageRankBtn3,
            SATime1, SATime1ByManual, SATime1Flag,
            SATime2, SATime2ByManual, SATime2Flag,
            SATime3, SATime3ByManual, SATime3Flag,
            SATime4, SATime4ByManual, SATime4Flag,
            SATime5, SATime5ByManual, SATime5Flag,
            BlockListFlag, RecycleFlag, RCRecordNo,
            ReserveFlag, ReserveRecordNo,
            CommentFlag, Comment1, Comment2, Comment3, RWLinkFlag
        ) VALUES (
            ?, ?, ?, ?, ?,
            ?, '', ?, '',
            ?, '',
            ?, ?, ?,
            -1, -1, -1,
            NULL, NULL, NULL,
            '*',
            -1, 0,
            ?, ?, ?,
            -1, -1, -1,
            '*', ?,
            -1, -1, -1,
            '', '', '',
            '9', '', 0, 0,
            '', '', '',
            '', '',
            0, 0, 0,
            -1, '', 0,
            -1, '', 0,
            -1, '', 0,
            -1, '', 0,
            -1, '', 0,
            0, 0, 0,
            0, 0,
            0, '', '', '', 0
        )""", (
            rec_no, line_no, parts_code, parts_code_sub, disposal_code,
            method, name,
            parts_no,
            db_parts_total, db_parts_intax, db_parts_tax,
            db_wage_total, db_wage_intax, db_wage_tax,
            db_qty
        ))
    # ── 税込/税抜に応じた費用計算ヘルパー ──
    def _calc_tax(amount, inclusive=False):
        """金額から OutTax, InTax, Tax を計算"""
        if amount == 0:
            return 0, 0, 0
        if inclusive:
            outtax = round(amount / (1 + TAX_RATE))
            intax  = amount
            tax    = amount - outtax
        else:
            outtax = amount
            tax    = round(amount * TAX_RATE)
            intax  = amount + tax
        return outtax, intax, tax

    # ── Expense各行を更新 ──
    # LineNo=4: ショートパーツ
    sp_wage = safe_int(short_parts_wage)
    sp_out, sp_intax, sp_tax = _calc_tax(sp_wage, is_tax_inclusive)
    cur.execute("""UPDATE Expense SET
        WageEnabled=?, WageOutTax=?, WageInTax=?, WageTax=?
        WHERE LineNo=4""", (1 if sp_wage > 0 else 0, sp_out, sp_intax, sp_tax))

    # LineNo=1: レッカー費用（課税）
    towing = safe_int(expenses.get('towing', 0))
    tow_out, tow_intax, tow_tax = _calc_tax(towing, is_tax_inclusive)
    cur.execute("""UPDATE Expense SET
        WageEnabled=?, WageOutTax=?, WageInTax=?, WageTax=?
        WHERE LineNo=1""", (1 if towing > 0 else 0, tow_out, tow_intax, tow_tax))

    # LineNo=2: 代車費用（課税）
    rental_car = safe_int(expenses.get('rental_car', 0))
    rent_out, rent_intax, rent_tax = _calc_tax(rental_car, is_tax_inclusive)
    cur.execute("""UPDATE Expense SET
        WageEnabled=?, WageOutTax=?, WageInTax=?, WageTax=?
        WHERE LineNo=2""", (1 if rental_car > 0 else 0, rent_out, rent_intax, rent_tax))

    # LineNo=5: 非課税費用（消費税なし）
    tax_exempt = safe_int(expenses.get('tax_exempt', 0))
    cur.execute("""UPDATE Expense SET
        WageEnabled=?, WageOutTax=?, WageInTax=?, WageTax=?
        WHERE LineNo=5""", (1 if tax_exempt > 0 else 0, tax_exempt, tax_exempt, 0))

    # ── Total計算 ──
    # total_parts / total_wages は既に税抜値（is_tax_inclusive時は逆算済み）
    taxable_expenses = sp_out + tow_out + rent_out
    sub_total         = total_parts + total_wages + taxable_expenses
    tax_total         = round(sub_total * TAX_RATE)
    grand_total       = sub_total + tax_total + tax_exempt  # 非課税は税計算後に加算
    parts_tax_total   = round(total_parts * TAX_RATE)
    wages_tax_total   = round(total_wages * TAX_RATE)
    sp_tax_total      = round(sp_out * TAX_RATE)
    cur.execute("""UPDATE Total SET
        ms_PartsTotalOutTax=?,
        ms_PartsTotalInTax=?,
        ms_PartsTotalTax=?,
        ms_WageTotalOutTax=?,
        ms_WageTotalInTax=?,
        ms_WageTotalTax=?,
        hy_WageTaxTotalOutTax=?,
        hy_WageTaxTotalInTax=?,
        hy_WageTaxTotalTax=?,
        tx_TotalOutTax=?,
        tx_TotalInTax=?,
        SubTotal=?,
        Total=?
    """, (
        total_parts, total_parts + parts_tax_total, parts_tax_total,
        total_wages, total_wages + wages_tax_total, wages_tax_total,
        taxable_expenses, taxable_expenses + round(taxable_expenses * TAX_RATE) if taxable_expenses > 0 else 0, round(taxable_expenses * TAX_RATE) if taxable_expenses > 0 else 0,
        tax_total,   tax_total,
        sub_total,   grand_total
    ))
    conn.commit()
    conn.close()
    with open(tf.name, 'rb') as f:
        result = f.read()
    os.unlink(tf.name)
    return result, total_parts, total_wages, grand_total


# ============================================================
# 内部ファイル更新: AnSvEm0001Ex.db（顧客・車両・保険）
# ============================================================

def update_em_db(db_bytes, cust, insurance_info, estimated_date, is_tax_inclusive=False, merge_mode=False):
    """Customer/FileInfo/Insurance/Setting テーブルを更新
    merge_mode=True の場合、OCRで取得した非空の値のみでテンプレートの既存値を上書きする。
    空値のフィールドはテンプレートNEOの値を保持する。
    """
    tf = tempfile.NamedTemporaryFile(suffix='.db', delete=False)
    tf.write(db_bytes)
    tf.close()
    conn = sqlite3.connect(tf.name)
    cur  = conn.cursor()
    customer_name = safe_str(cust.get('customer_name', ''))
    owner_name    = safe_str(cust.get('owner_name', ''))
    postal_no     = safe_str(cust.get('postal_no', ''))
    prefecture    = safe_str(cust.get('prefecture', ''))
    municipality  = safe_str(cust.get('municipality', ''))
    address_other = safe_str(cust.get('address_other', ''))
    car_dept      = safe_str(cust.get('car_reg_department', ''))
    car_div       = safe_str(cust.get('car_reg_division', ''))
    car_biz       = safe_str(cust.get('car_reg_business', ''))
    car_serial    = safe_str(cust.get('car_reg_serial', ''))
    car_serial_no = safe_str(cust.get('car_serial_no', ''))
    car_name       = safe_str(cust.get('car_name', ''))
    car_model      = safe_str(cust.get('car_model', ''))
    engine_model   = safe_str(cust.get('engine_model', ''))
    body_color     = safe_str(cust.get('body_color', ''))
    color_code     = safe_str(cust.get('color_code', ''))
    trim_code      = safe_str(cust.get('trim_code', ''))
    car_weight     = safe_int(cust.get('car_weight', 0))
    displacement   = safe_int(cust.get('engine_displacement', 0))
    model_desig    = safe_str(cust.get('car_model_designation', ''))
    category_num   = safe_str(cust.get('car_category_number', ''))
    kilometer      = safe_int(cust.get('kilometer', -1), -1)
    term_date      = safe_str(cust.get('term_date', '00000000'))
    car_reg_date   = safe_str(cust.get('car_reg_date', '00000000'))
    if not term_date    or len(term_date) < 8:    term_date    = '00000000'
    if not car_reg_date or len(car_reg_date) < 8: car_reg_date = '00000000'
    term_era, term_era_year = get_era_info(term_date)
    reg_era,  reg_era_year  = get_era_info(car_reg_date)

    if merge_mode:
        # マージモード: 非空の値のみでテンプレートの既存値を上書き
        _cust_updates = []
        _cust_values  = []
        _field_map = [
            ('Name1', customer_name), ('UserName', customer_name), ('OwnerName', owner_name),
            ('PostalNo', postal_no), ('Prefecture', prefecture),
            ('Municipality', municipality), ('AddressOther1', address_other),
            ('CarRegNoDepartment', car_dept), ('CarRegNoDivision', car_div),
            ('CarRegNoBusiness', car_biz), ('CarRegNoSerial', car_serial),
            ('CarSerialNo', car_serial_no), ('CarMouldNo', model_desig), ('CarKindNo', category_num),
        ]
        for col, val in _field_map:
            if val:  # 非空のみ上書き
                _cust_updates.append(f'{col}=?')
                _cust_values.append(val)
        # 日付系: 有効な日付（00000000以外）のみ上書き
        if term_date != '00000000':
            _cust_updates += ['TermDate=?', 'TermEra=?', 'TermEraYear=?']
            _cust_values  += [term_date, term_era, term_era_year]
        if car_reg_date != '00000000':
            _cust_updates += ['CarRegDate=?', 'CarRegEra=?', 'CarRegEraYear=?']
            _cust_values  += [car_reg_date, reg_era, reg_era_year]
        if kilometer >= 0:
            _cust_updates.append('Kilometer=?')
            _cust_values.append(kilometer)
        if _cust_updates:
            cur.execute(f"UPDATE Customer SET {', '.join(_cust_updates)}", _cust_values)
    else:
        # 通常モード: 全フィールドを上書き
        cur.execute('''UPDATE Customer SET
            Name1=?, UserName=?, OwnerName=?,
            PostalNo=?, Prefecture=?, Municipality=?, AddressOther1=?,
            CarRegNoDepartment=?, CarRegNoDivision=?,
            CarRegNoBusiness=?, CarRegNoSerial=?,
            CarSerialNo=?, CarMouldNo=?, CarKindNo=?,
            TermDate=?, TermEra=?, TermEraYear=?,
            CarRegDate=?, CarRegEra=?, CarRegEraYear=?,
            Kilometer=?
        ''', (
            customer_name, customer_name, owner_name,
            postal_no, prefecture, municipality, address_other,
            car_dept, car_div, car_biz, car_serial,
            car_serial_no, model_desig, category_num,
            term_date, term_era, term_era_year,
            car_reg_date, reg_era, reg_era_year,
            kilometer
        ))

    # Car テーブル更新（車名・カラーコード・トリムコード） — 非空の値のみ更新（通常・マージ共通）
    car_cols = {row[1] for row in cur.execute("PRAGMA table_info(Car)").fetchall()}
    car_update = [
        ('CarName', car_name), ('CarNameByUser', car_name),
        ('ColorCode', color_code), ('ColorName', body_color),
        ('TrimCode', trim_code),
    ]
    valid_car = [(col, val) for col, val in car_update if col in car_cols and val]
    if valid_car:
        set_clause = ', '.join(f'{col}=?' for col, _ in valid_car)
        values = [val for _, val in valid_car]
        cur.execute(f'UPDATE Car SET {set_clause}', values)
    est_era, est_era_year = get_era_info(estimated_date)
    cur.execute('''UPDATE FileInfo SET
        EstimatedDate=?, EstimatedEra=?, EstimatedEraYear=?
    ''', (estimated_date, est_era, est_era_year))
    policy_no  = safe_str(insurance_info.get('policy_no', ''))
    contractor = safe_str(insurance_info.get('contractor_name', ''))
    if merge_mode:
        # マージモード: 非空の保険情報のみ上書き
        _ins_updates = []
        _ins_values  = []
        if policy_no:
            _ins_updates.append('PolicyNo=?')
            _ins_values.append(policy_no)
        if contractor:
            _ins_updates.append('ContractorName=?')
            _ins_values.append(contractor)
        if _ins_updates:
            cur.execute(f"UPDATE Insurance SET {', '.join(_ins_updates)}", _ins_values)
    else:
        cur.execute('''UPDATE Insurance SET
            PolicyNo=?, ContractorName=?,
            AccidentDate='00000000', AccidentEra='令和'
        ''', (policy_no, contractor))
    conn.commit()

    # TaxKindFlag 更新 (1=内税, 0=外税)
    try:
        tax_flag = 1 if is_tax_inclusive else 0
        cur.execute('UPDATE Setting SET TaxKindFlag=?', (tax_flag,))
        conn.commit()
    except Exception as e:
        print("TaxKindFlag update failed:", e)

    conn.close()
    with open(tf.name, 'rb') as f:
        result = f.read()
    os.unlink(tf.name)
    return result


# ============================================================
# 内部ファイル更新: AnSvMail.ini（XML）
# ============================================================

def update_mail_ini(orig_bytes, cust, grand_total, merge_mode=False):
    """Shift_JIS XMLの顧客・車両情報を更新
    merge_mode=True の場合、非空の値のみ上書きする。
    """
    text         = orig_bytes.decode('cp932', errors='replace')
    customer_name = safe_str(cust.get('customer_name', ''))
    owner_name    = safe_str(cust.get('owner_name', ''))
    car_dept      = safe_str(cust.get('car_reg_department', ''))
    car_div       = safe_str(cust.get('car_reg_division', ''))
    car_biz       = safe_str(cust.get('car_reg_business', ''))
    car_serial    = safe_str(cust.get('car_reg_serial', ''))
    car_no_full   = f'{car_dept}{car_div}{car_biz}{car_serial}'
    car_name      = safe_str(cust.get('car_name', ''))
    car_serial_no = safe_str(cust.get('car_serial_no', ''))
    kilometer     = safe_str(cust.get('kilometer', ''))
    car_reg_date  = safe_str(cust.get('car_reg_date', ''))
    term_date     = safe_str(cust.get('term_date', ''))
    tag_values = {
        'CustomerName1': customer_name,
        'OwnerName':     owner_name,
        'UserName':      customer_name,
        'CarNo':         car_no_full,
        'CarName':       car_name,
        'CarSerialNo':   car_serial_no,
        'Kilometrage':   kilometer,
        'CarNoArea':     car_dept,
        'CarNoClass':    car_div,
        'CarNoKana':     car_biz,
        'CarNoSeries':   car_serial,
        'Total':         grand_total,
    }
    if term_date and term_date != '00000000':
        term_era, term_era_year = get_era_info(term_date)
        era_year_int = int(term_era_year)
        term_month = term_date[4:6] if len(term_date) >= 6 else ''
        term_day   = term_date[6:8] if len(term_date) >= 8 else ''
        tag_values['CarTermEraDate'] = (
            f'{term_era}{era_year_int}年{int(term_month)}月{int(term_day)}日'
            if term_month and term_day else ''
        )
    else:
        tag_values['CarTermEraDate'] = ''
    if car_reg_date and car_reg_date != '00000000':
        reg_era, reg_era_year = get_era_info(car_reg_date)
        reg_year_int = int(reg_era_year)
        reg_month    = car_reg_date[4:6] if len(car_reg_date) >= 6 else ''
        tag_values['CarRegistedDate'] = (
            f'{reg_era}{reg_year_int}年{int(reg_month)}月'
            if reg_month and reg_month != '00' else ''
        )
    else:
        tag_values['CarRegistedDate'] = ''
    for tag_name, value in tag_values.items():
        if merge_mode and not value:
            continue  # マージモード: 空値はスキップ（テンプレートの既存値を保持）
        text = replace_xml_tag(text, tag_name, value)
    return text.encode('cp932', errors='replace')


# ============================================================
# 内部ファイル更新: AnSvImge.ini（INI）
# ============================================================

def update_imge_ini(orig_bytes, cust, merge_mode=False):
    """INIファイルの顧客・車両情報を更新
    merge_mode=True の場合、非空の値のみ上書きする。
    """
    text      = orig_bytes.decode('cp932', errors='replace')
    ini_values = {
        'CustomerName':    safe_str(cust.get('customer_name', '')),
        'CarNoDepartment': safe_str(cust.get('car_reg_department', '')),
        'CarNoDivision':   safe_str(cust.get('car_reg_division', '')),
        'CarNoBusiness':   safe_str(cust.get('car_reg_business', '')),
        'CarNoSerial':     safe_str(cust.get('car_reg_serial', '')),
        'CarName':         safe_str(cust.get('car_name', '')),
    }
    for key, value in ini_values.items():
        if merge_mode and not value:
            continue  # マージモード: 空値はスキップ（テンプレートの既存値を保持）
        text = replace_ini_value(text, key, value)
    return text.encode('cp932', errors='replace')


# ============================================================
# 内部ファイル更新: AnNote.ini（明細簡易表現）
# ============================================================

def generate_annote(items):
    """142B固定長 × 行数 の AnNote.ini を生成"""
    if not items:
        return b''
    lines = []
    for i, item in enumerate(items):
        name    = item.get('name', '')
        qty     = safe_int(item.get('quantity', 1), 1)
        rec_no  = i + 1
        line_no = rec_no * 10
        line    = bytearray(142)
        for j in range(142):
            line[j] = 0x20
        ln_str = f'{line_no:08d}'
        for j, c in enumerate(ln_str):
            line[j] = ord(c)
        name_bytes = name.encode('cp932', errors='replace')[:30]
        for j, b in enumerate(name_bytes):
            line[14 + j] = b
        qty_str = f'{min(qty, 99):02d}'
        line[98] = ord(qty_str[0])
        line[99] = ord(qty_str[1])
        for j, c in enumerate('90000'):
            line[100 + j] = ord(c)
        for j, c in enumerate('F99999'):
            line[127 + j] = ord(c)
        lines.append(bytes(line) + b'\r\n')
    return b''.join(lines)


# ============================================================
# NEO リパッカー
# ============================================================

def repack_neo(orig_data, files, mgmt, entries):
    """更新済みファイルをNEOバイナリに再パック"""
    now     = datetime.datetime.now()
    now_dos = datetime_to_dos(now)
    entry_names  = [e['name'] for e in entries if e['name'] in files]
    missing_names = [name for name in files.keys() if name not in entry_names]
    ordered_names = entry_names + sorted(missing_names, key=lambda x: x.encode('cp932'))
    hidden_entries = [e for e in entries if e.get('is_last')]
    hidden_name    = hidden_entries[0]['name'] if hidden_entries else ordered_names[-1]
    normal_names   = [name for name in ordered_names if name != hidden_name]
    raw     = files[hidden_name]
    offsets = {}
    sizes   = {}
    for name in normal_names:
        offsets[name] = len(raw)
        sizes[name]   = len(files[name])
        raw += files[name]
    table_bytes = b''
    for name in ordered_names:
        if name == 'AnDBVersion.ini':
            dos = DOS_DBVER
        elif name == 'AnSvImge.ini':
            dos = DOS_IMGE
        else:
            dos = now_dos
        attr      = struct.pack('<H', 0x0020)
        name_enc  = ('\\' + name).encode('cp932') + b'\x00'
        if name == hidden_name:
            table_bytes += dos + attr + name_enc
        else:
            sz  = struct.pack('<I', sizes[name])
            off = struct.pack('<I', offsets[name])
            table_bytes += dos + attr + name_enc + sz + off + b'\x00\x00'
    CHUNK_SIZE      = 32768
    raw_chunks      = [raw[i:i + CHUNK_SIZE] for i in range(0, len(raw), CHUNK_SIZE)]
    num_chunks      = len(raw_chunks)
    compressed_chunks = []
    prev_raw        = b''
    for i, raw_chunk in enumerate(raw_chunks):
        if i == 0:
            c = zlib.compressobj(level=9, method=zlib.DEFLATED, wbits=-15)
        else:
            dict_data = prev_raw[-32768:]
            c = zlib.compressobj(level=9, method=zlib.DEFLATED, wbits=-15, zdict=dict_data)
        compressed = c.compress(raw_chunk) + c.flush()
        compressed_chunks.append(compressed)
        prev_raw += raw_chunk
    new_mgmt  = bytearray(mgmt)
    last_size = len(files[hidden_name])
    struct.pack_into('<H', new_mgmt, len(new_mgmt) - 14, num_chunks)
    struct.pack_into('<H', new_mgmt, len(new_mgmt) - 10, last_size)
    header  = orig_data[:424]
    ck_data = b''
    for i, comp in enumerate(compressed_chunks):
        comp_len  = len(comp) + 2
        decomp_len = len(raw_chunks[i])
        ck_data   += b'\x00\x00\x00\x00' + struct.pack('<HH', comp_len, decomp_len) + b'CK' + comp
    return header + bytes(new_mgmt) + table_bytes + ck_data


def generate_neo_file(template_data, customer_info, items, short_parts_wage, insurance_info, expenses=None, is_tax_inclusive=False, is_beta_mode=False, merge_mode=False):
    """テンプレートNEOから更新済みNEOを生成
    merge_mode=True の場合、ユーザーアップロードのテンプレートNEOをベースとし、
    車検証OCRで取得した値（非空のみ）でヘッダ情報を訂正し、明細欄はPDF解析結果で上書きする。
    テンプレートにのみ存在する情報（工場名・証券番号等）は保持される。
    """
    real_ck  = find_real_cks(template_data)
    if not real_ck:
        raise ValueError("テンプレートNEOのCKチャンクが見つかりません")
    full_raw     = decompress_neo(template_data, real_ck)
    mgmt, entries = parse_entries(template_data, real_ck[0])
    files        = extract_files(full_raw, entries)
    estimated_date = datetime.datetime.now().strftime('%Y%m%d')
    normalized_items = items or []
    files['AnSMB.txt'], total_parts, total_wages, grand_total = update_ansmb(
        files['AnSMB.txt'], normalized_items, short_parts_wage,
        expenses=expenses, is_tax_inclusive=is_tax_inclusive, is_beta_mode=is_beta_mode
    )
    files['AnNote.ini']       = generate_annote(normalized_items)
    files['AnSvEm0001Ex.db']  = update_em_db(
        files['AnSvEm0001Ex.db'], customer_info, insurance_info, estimated_date,
        is_tax_inclusive=is_tax_inclusive, merge_mode=merge_mode
    )
    files['AnSvMail.ini'] = update_mail_ini(files['AnSvMail.ini'], customer_info, grand_total, merge_mode=merge_mode)
    files['AnSvImge.ini'] = update_imge_ini(files['AnSvImge.ini'], customer_info, merge_mode=merge_mode)
    neo_data = repack_neo(template_data, files, mgmt, entries)
    return neo_data, total_parts, total_wages, grand_total


# ============================================================
# AI-OCR サポート関数
# ============================================================

def enhance_image_for_ocr(image_bytes):
    """
    OCR精度向上のための画像前処理。
    FAX品質の低画質画像に対して、コントラスト・シャープネスを強化する。
    """
    try:
        from PIL import Image, ImageEnhance, ImageFilter
        img = Image.open(io.BytesIO(image_bytes))
        # コントラスト強化（FAXのかすれた文字を読みやすくする）
        img = ImageEnhance.Contrast(img).enhance(1.5)
        # シャープネス強化（ぼやけた文字のエッジを明確にする）
        img = ImageEnhance.Sharpness(img).enhance(2.0)
        # 明るさ微調整（暗すぎる画像を補正）
        img = ImageEnhance.Brightness(img).enhance(1.1)
        buf = io.BytesIO()
        img.save(buf, format='JPEG', quality=92)
        return buf.getvalue()
    except Exception:
        return image_bytes


def rasterize_pdf_page(pdf_bytes, page_index, dpi=200, enhance=False):
    """
    PDFの指定ページをJPEG画像バイト列に変換。
    行ズレ防止のためGeminiに送る前に使用。
    enhance=True の場合、画像前処理（コントラスト・シャープネス強化）を適用。
    優先順位: pdf2image(poppler) → pypdfium2 → None
    """
    result = None

    # ── 方法1: pdf2image (poppler) ─────────────────────────
    try:
        from pdf2image import convert_from_bytes
        images = convert_from_bytes(
            pdf_bytes,
            dpi=dpi,
            first_page=page_index + 1,
            last_page=page_index + 1,
        )
        if images:
            buf = io.BytesIO()
            images[0].save(buf, format='JPEG', quality=90)
            result = buf.getvalue()
    except Exception:
        pass

    # ── 方法2: pypdfium2 (フォールバック) ──────────────────
    if result is None:
        try:
            import pypdfium2 as pdfium
            doc     = pdfium.PdfDocument(pdf_bytes)
            page    = doc[page_index]
            scale   = dpi / 72.0
            bitmap  = page.render(scale=scale)
            pil_img = bitmap.to_pil()
            buf     = io.BytesIO()
            pil_img.save(buf, format='JPEG', quality=90)
            doc.close()
            result = buf.getvalue()
        except Exception:
            pass

    # ── 画像前処理（FAX品質改善用） ──────────────────
    if result and enhance:
        result = enhance_image_for_ocr(result)

    return result


def try_fix_landscape_pdf(pdf_bytes):
    """横向きPDFを検出して縦向きに回転する"""
    try:
        from pypdf import PdfReader, PdfWriter
        reader       = PdfReader(io.BytesIO(pdf_bytes))
        needs_rotation = False
        for page in reader.pages:
            box = page.mediabox
            if float(box.width) > float(box.height) * 1.2:
                needs_rotation = True
                break
        if not needs_rotation:
            return pdf_bytes
        writer = PdfWriter()
        for page in reader.pages:
            box = page.mediabox
            if float(box.width) > float(box.height) * 1.2:
                page.rotate(270)
            writer.add_page(page)
        buf = io.BytesIO()
        writer.write(buf)
        return buf.getvalue()
    except Exception:
        return pdf_bytes


def try_split_pdf_pages(pdf_bytes):
    """PDFを個別ページに分割（2ページ以上の場合のみ）"""
    try:
        from pypdf import PdfReader, PdfWriter
        reader = PdfReader(io.BytesIO(pdf_bytes))
        if len(reader.pages) <= 1:
            return None
        pages = []
        for page in reader.pages:
            writer = PdfWriter()
            writer.add_page(page)
            buf = io.BytesIO()
            writer.write(buf)
            pages.append(buf.getvalue())
        return pages
    except Exception:
        return None


def detect_and_reorder_pages(pages):
    """
    PDFの各ページから「X/Y頁」「P.001/002」等のページ番号表記を検出し、
    正しい順序に並び替えて返す。
    【対応パターン】
      - FAXヘッダ形式: "P.001/002" → 1ページ目
      - 日本語形式: "1/2頁" "1／2頁" "1/2 頁"
      - 逆形式: "頁1/2"
    検出できない・全ページ揃わない場合は元の順序をそのまま返す。
    """
    import re
    try:
        from pypdf import PdfReader
    except ImportError:
        return pages

    page_numbers = []
    for idx, page_bytes in enumerate(pages):
        try:
            reader = PdfReader(io.BytesIO(page_bytes))
            text = reader.pages[0].extract_text() or ''
        except Exception:
            text = ''

        cur_page = None
        # パターン1: FAXヘッダ "P.001/002" 形式（大文字・小文字両対応）
        m = re.search(r'[Pp]\.(\d+)\s*/\s*(\d+)', text)
        if m:
            cur_page = int(m.group(1))
            page_numbers.append((idx, cur_page, int(m.group(2))))
            continue
        # パターン2: "1/2頁" "1／2頁" "1/2 頁" 形式
        m = re.search(r'(\d+)\s*[/／]\s*(\d+)\s*[頁ページ]', text)
        if m:
            cur_page = int(m.group(1))
            page_numbers.append((idx, cur_page, int(m.group(2))))
            continue
        # パターン3: "頁1/2" 逆形式
        m = re.search(r'[頁ページ]\s*(\d+)\s*[/／]\s*(\d+)', text)
        if m:
            cur_page = int(m.group(1))
            page_numbers.append((idx, cur_page, int(m.group(2))))
            continue
        # 検出できないページ
        page_numbers.append((idx, None, None))

    # 全ページでページ番号が検出できた場合のみ並び替え
    if page_numbers and all(pn[1] is not None for pn in page_numbers):
        original_order = [pn[0] for pn in page_numbers]
        page_numbers.sort(key=lambda x: x[1])
        new_order = [pn[0] for pn in page_numbers]
        if new_order != original_order:
            import sys
            print(f"[INFO] ページ順序を自動修正: {[p[1] for p in page_numbers]} "
                  f"(物理順 {original_order} → 文書順 {new_order})", file=sys.stderr)
        return [pages[pn[0]] for pn in page_numbers]

    return pages


def _get_genai_client(api_key):
    """google.genai クライアントを取得（キャッシュ付き）"""
    from google import genai
    return genai.Client(api_key=api_key)


def call_gemini(api_key, file_bytes, mime_type, prompt_text, model_name=None, use_json_mode=False):
    """Gemini APIにファイルを送信して解析結果テキストを取得（最大3回リトライ）
    use_json_mode=True の場合、構造化JSON出力モードを使用（解析精度向上）
    """
    from google.genai import types
    client = _get_genai_client(api_key)
    model = model_name or GEMINI_MODEL
    file_part = types.Part.from_bytes(data=file_bytes, mime_type=mime_type)
    config = {"temperature": 0.0, "max_output_tokens": 65536}
    if use_json_mode:
        config["response_mime_type"] = "application/json"
    last_error = None
    for attempt in range(3):
        try:
            response = client.models.generate_content(
                model=model,
                contents=[prompt_text, file_part],
                config=config,
            )
            if response.text and response.text.strip():
                return response.text
            if attempt < 2:
                import time; time.sleep(2)
                continue
            raise ValueError("Geminiから有効な応答が得られませんでした。")
        except ValueError:
            raise
        except Exception as e:
            last_error = e
            if attempt < 2:
                import time; time.sleep(2)
                continue
            raise ValueError(f"Gemini API呼び出しに失敗しました（{attempt+1}回試行）: {str(last_error)}")


def classify_first_page_as_fax(api_key, pdf_bytes, model_name):
    """
    PDFの1ページ目がFAX送付状かどうかをAIで判定する。
    True=FAX送付状 → 除外すべき、False=見積書・車検証などの本体ページ
    """
    try:
        img_bytes = rasterize_pdf_page(pdf_bytes, 0, dpi=120)
        if img_bytes is None:
            return False
        from google.genai import types
        client = _get_genai_client(api_key)
        prompt = """この画像はPDFの1ページ目です。
このページがFAX送付状・送信票・表紙（本文ではないカバーページ）かどうか判定してください。
{"is_fax_cover": true, "page_type": "fax_cover", "reason": "理由"}
または
{"is_fax_cover": false, "page_type": "estimate/vehicle/other", "reason": "理由"}
JSONのみ返してください。"""
        response = client.models.generate_content(
            model=model_name,
            contents=[prompt, types.Part.from_bytes(data=img_bytes, mime_type="image/jpeg")],
            config={"temperature": 0.0, "max_output_tokens": 256, "response_mime_type": "application/json"},
        )
        result = extract_json_from_response(response.text)
        return bool(result.get('is_fax_cover', False))
    except Exception:
        return False


def filter_fax_pages(api_key, pdf_bytes, model_name):
    """
    FAX送付状（1ページ目）を除去した新しいPDFバイト列を返す。
    2ページ以上かつ1ページ目がFAXと判定された場合のみ除去する。
    """
    try:
        from pypdf import PdfReader, PdfWriter
        reader = PdfReader(io.BytesIO(pdf_bytes))
        if len(reader.pages) <= 1:
            return pdf_bytes
        is_fax = classify_first_page_as_fax(api_key, pdf_bytes, model_name)
        if not is_fax:
            return pdf_bytes
        writer = PdfWriter()
        for i in range(1, len(reader.pages)):
            writer.add_page(reader.pages[i])
        buf = io.BytesIO()
        writer.write(buf)
        return buf.getvalue()
    except Exception:
        return pdf_bytes


def guess_manufacturer_from_vin(vin):
    """車台番号の先頭文字列からメーカー・車種を推定する"""
    if not vin:
        return '', ''
    vin = vin.upper().strip()
    # WMI（先頭3文字）ベースのメーカー判定テーブル
    WMI_MAP = {
        # ドイツ車
        'WUA': ('アウディ', ''), 'WAU': ('アウディ', ''), 'WA1': ('アウディ', ''),
        'WBA': ('BMW', ''), 'WBS': ('BMW', 'M'), 'WBY': ('BMW', 'i'),
        'WDB': ('メルセデス・ベンツ', ''), 'WDC': ('メルセデス・ベンツ', ''), 'WDD': ('メルセデス・ベンツ', ''),
        'W1K': ('メルセデス・ベンツ', ''), 'W1N': ('メルセデス・ベンツ', ''),
        'WVW': ('フォルクスワーゲン', ''), 'WV1': ('フォルクスワーゲン', ''), 'WV2': ('フォルクスワーゲン', ''),
        'WP0': ('ポルシェ', ''), 'WP1': ('ポルシェ', ''),
        # 日本車
        'JTD': ('トヨタ', ''), 'JTE': ('トヨタ', ''), 'JTN': ('トヨタ', ''),
        'JHM': ('ホンダ', ''), 'JHL': ('ホンダ', ''),
        'JN1': ('日産', ''), 'JN3': ('日産', ''),
        'JMA': ('マツダ', ''), 'JMZ': ('マツダ', ''),
        'JSA': ('スズキ', ''), 'JS1': ('スズキ', ''),
        'JF1': ('スバル', ''), 'JF2': ('スバル', ''),
        'JDA': ('ダイハツ', ''),
        'JMB': ('三菱', ''), 'JMY': ('三菱', ''),
        # 韓国車
        'KMH': ('ヒュンダイ', ''), 'KNA': ('キア', ''),
        # イタリア車
        'ZAR': ('アルファロメオ', ''), 'ZFF': ('フェラーリ', ''), 'ZHW': ('ランボルギーニ', ''),
        'ZFA': ('フィアット', ''), 'ZAM': ('マセラティ', ''),
        # イギリス車
        'SAL': ('ランドローバー', ''), 'SAJ': ('ジャガー', ''), 'SAR': ('ランドローバー', ''),
        'SCF': ('アストンマーティン', ''), 'SCC': ('ロータス', ''),
        # フランス車
        'VF1': ('ルノー', ''), 'VF3': ('プジョー', ''), 'VF7': ('シトロエン', ''),
        # アメリカ車
        '1FA': ('フォード', ''), '1FT': ('フォード', ''), '1G1': ('シボレー', ''),
        '1GC': ('シボレー', ''), '1GM': ('GM', ''), '2T1': ('トヨタ(北米)', ''),
        '3FA': ('フォード(メキシコ)', ''),
        # スウェーデン車
        'YV1': ('ボルボ', ''), 'YS3': ('サーブ', ''),
    }
    # 先頭3文字で判定
    wmi3 = vin[:3]
    if wmi3 in WMI_MAP:
        return WMI_MAP[wmi3]
    # 先頭2文字でフォールバック
    COUNTRY_PREFIX = {
        'WU': ('アウディ/VW系', ''), 'WB': ('BMW', ''), 'WD': ('メルセデス・ベンツ', ''),
        'WV': ('フォルクスワーゲン', ''), 'WP': ('ポルシェ', ''), 'WF': ('フォード(独)', ''),
        'JT': ('トヨタ', ''), 'JH': ('ホンダ', ''), 'JN': ('日産', ''),
        'JM': ('マツダ/三菱', ''), 'JS': ('スズキ', ''), 'JF': ('スバル', ''),
        'JD': ('ダイハツ', ''), 'ZA': ('イタリア車', ''), 'SA': ('イギリス車', ''),
        'VF': ('フランス車', ''), 'YV': ('ボルボ', ''),
    }
    wmi2 = vin[:2]
    if wmi2 in COUNTRY_PREFIX:
        return COUNTRY_PREFIX[wmi2]
    return '', ''


# ============================================================
# Addata / マスタ連携用関数群
# ============================================================

def read_addata_db(filepath):
    """
    Cogni7 (Addata) の独自DBファイル(Shift-JIS固定長/XOR0xFF難読化)を読む。
    後方互換用: テキスト行リストを返す（KA06_ALL.DB 等の照合用）

    KA06_ALL.DB は改行なしの固定長レコードファイルの場合がある。
    その場合は固定長スライス（27バイト/レコード）にフォールバックする。
    """
    if not os.path.exists(filepath):
        return []
    try:
        with open(filepath, 'rb') as f:
            data = f.read()
        dec = bytes(b ^ 0xFF for b in data)
        text = dec.decode('cp932', errors='replace').replace('\x00', ' ')
        # まず \r\n / \r / \n 全種の改行で分割を試みる
        normalized = text.replace('\r\n', '\n').replace('\r', '\n')
        lines = [line for line in normalized.split('\n') if line.strip()]
        if len(lines) > 1:
            return lines
        # 改行なし → 固定長レコードとして処理
        # KA06_ALL.DB: 27バイト/レコード (3,464,343 = 27 × 128,309)
        # フォーマット: [0:2]識別子 [2:5]車種コード [5:7]年式 [7:16]型式キー [16:20]類別 [20:25]型式指定 [25:27]予備
        for rec_len in [27, 29, 32, 33, 36, 40]:
            if len(text) % rec_len == 0:
                lines = [text[i:i+rec_len] for i in range(0, len(text), rec_len)
                         if text[i:i+rec_len].strip()]
                if lines:
                    return lines
        # 最終フォールバック: '06' マーカーを探してスライディングウィンドウ検索
        # → _ka06_raw_search() で処理するため、デコード済みテキストを1要素リストで返す
        return [text] if text.strip() else []
    except Exception as e:
        print(f"Error reading DB {filepath}: {e}")
        return []


def _ka06_raw_search(ka06_path, desig_plain, desig_with60, padded_cat):
    """
    KA06_ALL.DB のデコード済みテキストに対して、型式指定番号+類別区分番号の
    パターンをスライディングウィンドウで検索し、(v_code, n_code) を返す。
    改行なし固定長ファイルへの対応として使用。
    """
    try:
        with open(ka06_path, 'rb') as f:
            raw = f.read()
        dec = bytes(b ^ 0xFF for b in raw)
        text = dec.decode('cp932', errors='replace').replace('\x00', ' ')

        # 型式指定番号を含む位置を全て探索
        search_terms = [t for t in [desig_with60, desig_plain] if t]
        for term in search_terms:
            pos = 0
            while True:
                idx = text.find(term, pos)
                if idx == -1:
                    break
                # ±40文字のウィンドウ内に類別区分番号があるか確認
                start = max(0, idx - 40)
                end   = min(len(text), idx + 40)
                window = text[start:end]
                if padded_cat in window:
                    # '06' レコードマーカーをウィンドウ内で検索
                    rec_pos = window.find('06')
                    if rec_pos >= 0:
                        abs_rec = start + rec_pos
                        v_code = text[abs_rec+2:abs_rec+5].strip()
                        n_code = text[abs_rec+5:abs_rec+7].strip()
                        if v_code and v_code.isalnum():
                            return v_code, n_code
                pos = idx + 1
    except Exception as e:
        print(f"KA06 raw search error: {e}")
    return None, None


def read_addata_db_raw(filepath):
    """
    Cogni7 (Addata) の独自DBファイルをバイト列レコードのリストとして返す。
    XOR 0xFF 復号後に \\r\\n または \\n で分割。C1012.DB 等の部品マスタ解析用。
    """
    if not os.path.exists(filepath):
        return []
    try:
        with open(filepath, 'rb') as f:
            data = f.read()
        dec = bytes(b ^ 0xFF for b in data)
        # \r\n 区切りを優先、なければ \n 区切り
        if b'\r\n' in dec:
            records = dec.split(b'\r\n')
        else:
            records = dec.split(b'\n')
        return [r for r in records if len(r) >= 20]
    except Exception as e:
        print(f"Error reading DB raw {filepath}: {e}")
        return []


def find_addata_dir():
    """Addataフォルダを探索してパスを返す。
    KA06_ALL.DB は C:\\Addata\\COM\\ に直接置かれているか、
    COM.CAB を展開した C:\\Temp\\COM_extracted\\ にある場合もある。
    環境変数 ADDATA_PATH が設定されている場合は最優先で使用する。
    """
    # 環境変数による明示的なパス指定を最優先
    env_path = os.environ.get('ADDATA_PATH', '').strip()
    if env_path and os.path.isdir(env_path):
        return env_path

    search_paths = [
        r'C:\AdSeven\Addata',
        r'D:\Addata',
        r'C:\Addata',
    ]
    for p in search_paths:
        if not os.path.isdir(p):
            continue
        # KA06_ALL.DB が COM フォルダに直接ある場合
        if os.path.exists(os.path.join(p, 'COM', 'KA06_ALL.DB')):
            return p
        # KA06_ALL.DB がなくても COM フォルダと車種フォルダがあれば利用可能
        com_dir = os.path.join(p, 'COM')
        if os.path.isdir(com_dir) and any(os.path.isdir(os.path.join(p, d)) for d in ['T', 'U', 'W', 'N', 'H']):
            return p
    return None


def find_ka06_path(addata_base):
    """KA06_ALL.DB のパスを返す（COM直下 または Temp展開先にフォールバック）"""
    candidates = [
        os.path.join(addata_base, 'COM', 'KA06_ALL.DB'),
        r'C:\Temp\COM_extracted\KA06_ALL.DB',
    ]
    for c in candidates:
        if os.path.exists(c):
            return c
    return None


def identify_vehicle(addata_base, vehicle_data):
    """
    車検証の「型式指定番号」「類別区分番号」「型式」「車台番号」をもとに、
    Addata (COM/KA06_ALL.DB) と照合し、3層マッチングで最も適合する車種を特定する。
    """
    if not addata_base:
        return {'match_layer': 3, 'is_supported': False, 'reason': 'Addata path not found'}

    ka06_path = find_ka06_path(addata_base)
    if not ka06_path:
        return {'match_layer': 3, 'is_supported': False, 'reason': 'KA06_ALL.DB not found'}
    lines = read_addata_db(ka06_path)
    if not lines:
        return {'match_layer': 3, 'is_supported': False, 'reason': 'KA06_ALL.DB empty or unreadable'}

    model_desig = str(vehicle_data.get('car_model_designation', '')).strip()
    cat_num     = str(vehicle_data.get('car_category_number', '')).strip()
    car_model   = str(vehicle_data.get('car_model', '')).strip().upper()
    chassis_no  = str(vehicle_data.get('car_serial_no', '')).strip()

    def _try_resolve(v_code, n_code, layer):
        """車種コードからフォルダを特定して結果辞書を返す。フォルダが存在しなければ None。"""
        if not v_code:
            return None
        folder = os.path.join(addata_base, v_code[0], v_code)
        if os.path.isdir(folder):
            return {
                'match_layer':    layer,
                'vehicle_code':   v_code,
                'nenshi_code':    n_code,
                'addata_folder':  folder,
                'is_supported':   True,
            }
        return None

    # ── 第1層: 型式指定番号 ＋ 類別区分番号 完全一致 ───────────────────
    # KA06_ALL.DB の確認済みフォーマット例:
    #   "06W7100AVU65     0001000037601234"
    #   [0:2]  = "06"       レコード識別子
    #   [2:5]  = "W71"      Addataコード（車種グループ）
    #   [5:7]  = "00"       年式コード
    #   [7:16] = "AVU65    " 型式キー(9バイト、右スペース埋め)
    #   以降に類別区分番号(4桁)・型式指定番号(5桁)が連なる
    # 型式指定番号は "60" + 5桁 の形式でファイル内に格納される場合がある
    if model_desig and cat_num:
        padded_cat   = cat_num.zfill(4)
        # "60" プレフィックスを付けたパターンも試す（引継書仕様）
        desig_plain  = model_desig.zfill(5)
        desig_with60 = '60' + desig_plain

        # 通常の行分割で検索
        for line in lines:
            if not line.startswith('06'):
                continue
            if padded_cat in line and (desig_plain in line or desig_with60 in line):
                try:
                    v_code = line[2:5].strip()
                    n_code = line[5:7].strip()
                    result = _try_resolve(v_code, n_code, 1)
                    if result:
                        return result
                except Exception:
                    pass

        # 固定長/改行なしファイル用: スライディングウィンドウ検索
        if ka06_path:
            v_code, n_code = _ka06_raw_search(ka06_path, desig_plain, desig_with60, padded_cat)
            if v_code:
                result = _try_resolve(v_code, n_code, 1)
                if result:
                    result['match_via_raw_search'] = True
                    return result

    # ── 第1.5層: Katashiki.DB による型式コード直接マッピング ──────────
    # Katashiki.DB フォーマット: [Addataコード(5)] [バリアント(4)] [型式コード(10)]
    # 例: "U62  00AA ZVW30   " → Addataコード=U62, 型式=ZVW30
    if car_model:
        model_key = car_model.split('-')[-1].strip()  # "DBA-ZVW30" → "ZVW30"
        katashiki_path = os.path.join(addata_base, 'COM', 'Katashiki.DB')
        if model_key and os.path.exists(katashiki_path):
            try:
                with open(katashiki_path, 'r', encoding='cp932', errors='replace') as kf:
                    for kline in kf:
                        kline = kline.rstrip('\r\n')
                        if not kline.strip():
                            continue
                        parts = kline.split()
                        if len(parts) >= 3:
                            k_addata = parts[0].strip()   # 例: "U62"
                            k_model  = parts[2].strip()   # 例: "ZVW30"
                            # 完全一致 または 前方一致 (例: ZVW30W → ZVW30 にマッチ)
                            if k_model == model_key or model_key.startswith(k_model) or k_model.startswith(model_key):
                                result = _try_resolve(k_addata, '', 1)
                                if result:
                                    result['match_via_katashiki'] = True
                                    return result
            except Exception:
                pass

    # ── 第2層: 型式キー (DBA-AVU65W → 先頭5文字 AVU65) ──────────────
    if car_model:
        # ハイフンで分割して末尾トークンの先頭5文字を型式キーとする
        raw_key   = car_model.split('-')[-1]      # "AVU65W"
        model_key = raw_key[:5]                   # "AVU65"
        for line in lines:
            if not line.startswith('06'):
                continue
            if model_key in line[7:20]:           # 型式キー位置付近で検索
                try:
                    v_code = line[2:5].strip()
                    n_code = line[5:7].strip()
                    result = _try_resolve(v_code, n_code, 2)
                    if result:
                        return result
                except Exception:
                    pass
        # 型式キーが見つからない場合、ワイド検索（行全体）でも試みる
        for line in lines:
            if not line.startswith('06'):
                continue
            if model_key in line:
                try:
                    v_code = line[2:5].strip()
                    n_code = line[5:7].strip()
                    result = _try_resolve(v_code, n_code, 2)
                    if result:
                        return result
                except Exception:
                    pass

    # ── 第3層: 未マッチ → AIベタ打ちモード ──────────────────────────
    return {'match_layer': 3, 'is_supported': False, 'reason': 'No matching vehicle found in KA06_ALL'}


def match_parts_with_addata(items, addata_folder):
    """
    特定された車種フォルダ内の xx12.DB (部品マスタ) と、OCR見積明細(items)を照合し、
    一致した部品の「マスタ価格」「修理メソッド(K/D/S)」「セクション」「枝番」を返す。

    C1012.DB 確定フォーマット (79 bytes/record):
      [0:2]   '12'        レコード識別子
      [2:6]   'C10A'      車種グループ
      [6:8]   '01'        セクション番号 (部品コード大区分)
      [8:13]  '00101'     枝番 (entry/branch code)
      [13]    'F'/'R'     位置フラグ (Front/Rear)
      [14:44] 部品名称     30 bytes half-width kana
      [43]    '$'(0x24)   グレードバリアントフラグ (あれば)
      [44:48] '0010'      ref_a = 見積コード（D1911インデックス番号）
      [52:55] 'KDS'       利用可能修理メソッド (K=取替 D=脱着 S=修理)
      [60]    'G'/' '     グレード固有フラグ
      [48:52] '0050'      mirror_code = 右側部品の対応ref_a
    """
    if not addata_folder:
        return items, False

    import glob
    import struct as _struct
    db_files = glob.glob(os.path.join(addata_folder, '*.DB'))
    if not db_files:
        return items, False

    # ── *11.DB/*13.DB 価格連鎖を読み込む ──────────────────────────────
    def _load_price_chain(folder):
        """*11.DB (範囲インデックス) と *13.DB (実価格) を読み込む"""
        db11, db13 = None, None
        for f in glob.glob(os.path.join(folder, '*11.DB')):
            try:
                with open(f, 'rb') as fh:
                    db11 = fh.read()
                break
            except Exception:
                pass
        for f in glob.glob(os.path.join(folder, '*13.DB')):
            try:
                with open(f, 'rb') as fh:
                    db13 = fh.read()
                break
            except Exception:
                pass
        return db11, db13

    def _lookup_price(ref_no, db11, db13):
        """ref_no → *11.DB → *13.DB 連鎖でバリアント別価格一覧と代表価格を返す。

        *11.DB 構造: 先頭400バイト = 100組の (start, end) uint16 LE ペア
          → ref_no番目のペアが *13.DB インデックスレコード範囲を示す (end は inclusive)
        *13.DB 構造: [2バイト ヘッダ: レコード数] + [8バイト×N インデックス]
          インデックス各レコード: (price_div10, variant, blk_start, blk_end) uint16 LE×4
          price = price_div10 × 10 (円)

        Returns (representative_price_yen, [{'color_code': variant, 'price': p}, ...])
        見つからない場合は (None, []) を返す。
        """
        if db11 is None or db13 is None or ref_no < 0:
            return None, []
        # *11.DB ヘッダは100ペア (400バイト); ref_no >= 100 はデータ領域に溢れる
        if ref_no >= 100:
            return None, []
        offset = ref_no * 4
        if offset + 4 > len(db11):
            return None, []
        start, end = _struct.unpack_from('<HH', db11, offset)
        if start == 0xFFFF or end == 0xFFFF:
            return None, []
        # *13.DB 先頭2バイト = インデックスレコード総数
        if len(db13) < 2:
            return None, []
        idx_count = _struct.unpack_from('<H', db13, 0)[0]
        color_prices = []
        for i in range(start, end + 1):           # end は inclusive
            if i >= idx_count:
                break
            ep = 2 + i * 8                         # 2バイトヘッダをスキップ
            if ep + 8 > len(db13):
                break
            price_div10, variant, _bs, _be = _struct.unpack_from('<HHHH', db13, ep)
            price_yen = price_div10 * 10
            if price_yen > 0:
                color_prices.append({'color_code': variant, 'price': price_yen})
        if not color_prices:
            return None, []
        return color_prices[0]['price'], color_prices

    db11_data, db13_data = _load_price_chain(addata_folder)

    # ── 生バイト読み込みで部品マスタを構築 ──
    master_parts = []
    for db_path in db_files:
        records = read_addata_db_raw(db_path)
        for line_no, r in enumerate(records):
            # '12' で始まる部品マスタレコードのみ処理
            if len(r) < 66 or r[0:2] != b'12':
                continue
            try:
                def _s(b): return b.decode('cp932', errors='replace').strip()

                section_code    = _s(r[6:8])    # セクション番号 ('01', '05' …)
                branch_code     = _s(r[8:13])   # 枝番 ('00101', '001AA' …)
                pos_flag        = chr(r[13]) if 0x20 <= r[13] <= 0x7E else ''  # F/R

                # 部品名称 [14:44] — 旧コードの [13:43] はフラグバイトを含む誤りだった
                name = _s(r[14:44])

                # グレードバリアントフラグ: byte[43] == '$'(0x24)
                is_grade_variant = (r[43] == 0x24)

                # W6411インデックス = int(ref_a)
                # D1912の[44:48]に格納されたref_a（コグニセブン見積コードと同一）を
                # そのまま整数変換してW6411インデックスとして使用する。
                ref_str = _s(r[44:48])
                ref_no_val = int(ref_str) if ref_str.isdigit() else -1

                # ミラーコード: 右側部品の対応コード [48:52]（例: 左0030の鏡像が右0050）
                mirror_str = _s(r[48:52])

                # グレード固有フラグ: byte[59] == 'G'(0x47)
                grade_specific = (r[59] == 0x47)

                # 価格決定: まず *11/*13 連鎖を試みる
                price = 0
                color_prices = []
                if ref_no_val >= 0:
                    chain_price, color_prices = _lookup_price(ref_no_val, db11_data, db13_data)
                    if chain_price is not None:
                        price = chain_price
                # 連鎖で価格が取れなかった場合は price = 0 のまま（名前マッチングには使用する）

                # 利用可能修理メソッド: [52:55] に K / D / S が入る
                repair_methods = _s(r[52:55])   # 例: 'K', 'KDS', 'S', ''

                if name:
                    master_parts.append({
                        'name':             name,
                        'part_no':          '',          # C1012.DB には品番なし
                        'price':            price,
                        'color_prices':     color_prices,  # カラー別価格リスト
                        'ref_no':           ref_no_val,
                        'ref_a':            ref_str,      # コグニセブン見積コード（例: "0010"）
                        'mirror_code':      mirror_str,   # 右側部品の対応コード（例: "0050"）
                        'section_code':     section_code,
                        'branch_code':      branch_code,
                        'pos_flag':         pos_flag,
                        'repair_methods':   repair_methods,
                        'is_grade_variant': is_grade_variant,
                        'grade_specific':   grade_specific,
                        # 旧フィールド名を維持 (後方互換)
                        'repair_code':      section_code,
                        'part_code_r':      section_code,
                        'part_code_l':      branch_code,
                    })
            except Exception:
                pass

    # ref_a（コグニセブン見積コード）による高速引索インデックスを構築
    # 同じref_aが複数存在する場合は最初のものを採用（通常は一意）
    ref_a_index = {}
    for mp in master_parts:
        ra = mp.get('ref_a', '').strip()
        if ra and ra not in ref_a_index:
            ref_a_index[ra] = mp

    # ミラーインデックス: 右側部品コード → 左側部品レコード
    # D1912の[48:52]に格納された右側コード（例: "0050"）を左側レコードにマッピング
    mirror_index = {}
    for mp in master_parts:
        mc = mp.get('mirror_code', '').strip()
        if mc and mc.isdigit():
            mk = mc.zfill(4)
            # ref_a_indexに既存のコードは上書きしない
            if mk not in mirror_index and mk not in ref_a_index:
                mirror_index[mk] = mp

    # 英語カナ変換用（解析書 §5.2 の部品名称に基づく半角カタカナ表記に合わせる）
    EN_TO_KANA = {
        'BUMPER': 'バンパ', 'FENDER': 'フエンダ', 'HOOD': 'ボンネット', 'BONNET': 'ボンネット',
        'RADIATOR': 'ラジエータ', 'CONDENSER': 'コンデンサ', 'HEADLAMP': 'ヘッドランプ',
        'HEAD LAMP': 'ヘッドランプ', 'TAIL LAMP': 'テールランプ', 'WIPER': 'ワイパ',
        'PAD': 'パッド', 'SHOCK': 'シヨツク', 'ABSORBER': 'アブソーバ', 'DOOR': 'ドア',
        'PANEL': 'パネル', 'COVER': 'カバー', 'MIRROR': 'ミラー', 'GARNISH': 'ガーニッシュ',
        'BRACKET': 'ブラケット', 'SUPPORT': 'サポート', 'STABILIZER': 'スタビライザ',
        'GRILLE': 'グリル', 'GRILL': 'グリル', 'GLASS': 'ガラス', 'LAMP': 'ランプ',
        'LIGHT': 'ランプ', 'SPOILER': 'スポイラ', 'MOLDING': 'モール',
        'MOULDING': 'モール', 'CLIP': 'クリップ', 'BOLT': 'ボルト', 'NUT': 'ナット',
        'SENSOR': 'センサ', 'CAMERA': 'カメラ', 'HINGE': 'ヒンジ', 'SEAL': 'シール',
        'WEATHERSTRIP': 'ウエザーストリップ', 'EMBLEM': 'エンブレム',
        'LINER': 'ライナ', 'GUARD': 'ガード', 'RETAINER': 'リテーナ',
        'DEFLECTOR': 'デフレクタ', 'EXTENSION': 'エクステンション',
        'REINFORCEMENT': 'リインフォースメント', 'REINFORCE': 'リインフォース',
    }

    # 表記ゆれ正規化マップ（Addataの半角カタカナ表記に統一）
    # 解析書 §5.2: Addataは半角カタカナ・省略形が多い
    KANA_NORMALIZE = {
        'ヘッドライト': 'ヘッドランプ', 'ヘッドライ': 'ヘッドランプ',
        'テールライト': 'テールランプ', 'テールライ': 'テールランプ',
        'フォグランプ': 'フオグランプ', 'フォグ': 'フオグ',
        'フェンダ': 'フエンダ', 'フェンダー': 'フエンダ',
        'バンパー': 'バンパ', 'バンパカバー': 'バンパカバ',
        'ボンネット': 'ボンネツト',
        'ラジエーター': 'ラジエータ', 'ラジエーター': 'ラジエータ',
        'ワイパー': 'ワイパ', 'ミラー': 'ミラ',
        'スタビライザー': 'スタビライザ', 'スポイラー': 'スポイラ',
        'アブソーバー': 'アブソーバ', 'コンデンサー': 'コンデンサ',
        'センサー': 'センサ', 'ライナー': 'ライナ',
        'グリル': 'グリル', 'グリール': 'グリル',
        'モール': 'モール', 'モーディング': 'モール',
    }

    import jaconv
    try:
        from Levenshtein import distance
    except ImportError:
        def distance(a, b): return len(a) + len(b) # dummy

    def fuzzy_match_part(target_name, target_price, target_part_no=''):
        # 0. 品番 (part_no) による完全・前方マッチング（最も確実）
        norm_target_no = target_part_no.replace('-', '').replace(' ', '').upper()
        if norm_target_no:
            for mp in master_parts:
                norm_mp_no = mp.get('part_no', '').replace('-', '').replace(' ', '').upper()
                if norm_mp_no and (norm_mp_no == norm_target_no or norm_target_no.startswith(norm_mp_no)):
                    return mp, 0, False

        # 1. 正規化（解析書 §5.2: Addataは半角カタカナ・省略形）
        # まず全角→半角変換してから英字→カナ変換する
        norm_target = str(target_name)
        norm_target = jaconv.z2h(norm_target, ascii=True, digit=True, kana=True)
        norm_target = norm_target.upper()

        # KANA_NORMALIZE: Addata内の省略形表記に統一（長音省略など）
        for src, dst in KANA_NORMALIZE.items():
            src_h = jaconv.z2h(src, ascii=True, digit=True, kana=True)
            dst_h = jaconv.z2h(dst, ascii=True, digit=True, kana=True)
            norm_target = norm_target.replace(src_h.upper(), dst_h.upper())

        # 英単語→カナ変換
        for en, kana in EN_TO_KANA.items():
            kana_h = jaconv.z2h(kana, ascii=True, digit=True, kana=True)
            norm_target = norm_target.replace(en, kana_h.upper())

        # 代表的な位置プレフィックスを除去（"LH", "RH" 等）
        for prefix in ['LH ', 'RH ', '左 ', '右 ', 'L ', 'R ', '左', '右']:
            if norm_target.startswith(prefix):
                norm_target = norm_target[len(prefix):].strip()

        # ﾌﾛﾝﾄ / ﾘﾔ を F / R に変換（Addata pos_flag 形式）
        if norm_target.startswith('ﾌﾛﾝﾄ '):
            norm_target = 'F' + norm_target[4:].strip()
        elif norm_target.startswith('ﾌﾛﾝﾄ'):
            norm_target = 'F' + norm_target[4:].strip()
        elif norm_target.startswith('ﾘﾔ ') or norm_target.startswith('ﾘｱ '):
            norm_target = 'R' + norm_target[3:].strip()
        elif norm_target.startswith('ﾘﾔ') or norm_target.startswith('ﾘｱ'):
            norm_target = 'R' + norm_target[2:].strip()

        # アッシ / サブアッシ / COMP / ベース などノイズ語を除去
        norm_target = norm_target.replace('ｻﾌﾞｱｯｼ', '').replace('ｱｯｼ', '').replace('COMP', '').strip()
        norm_target = norm_target.replace('ﾍﾞｰｽ', '').replace('ｱｳﾃﾘｱ', 'ｱｳﾀ').replace('ｱｳﾄﾘﾔﾋﾞｭｰ', 'ｱｳﾄ').strip()
        norm_target = norm_target.replace(' ', '')

        # 小書き文字を大文字に変換するマップ（Addataは全て大文字カナが多い）
        KANA_SMALL_TO_LARGE = str.maketrans('ｧｨｩｪｫｯｬｭｮ', 'ｱｲｳｴｵﾂﾔﾕﾖ')
        norm_target = norm_target.translate(KANA_SMALL_TO_LARGE)

        # clean版: L/R位置フラグ・パネル・アッシ・ガードを除去した芯の文字列
        norm_target_clean = norm_target.replace('L', '').replace('R', '').replace('ﾊﾟﾈﾙ', '').replace('ｱｯｼ', '').replace('ｶﾞｰﾄﾞ', '').strip()

        candidates = []
        for mp in master_parts:
            m_name = jaconv.z2h(mp['name'], ascii=True, digit=True, kana=True).replace(' ', '')
            m_name = m_name.translate(KANA_SMALL_TO_LARGE)
            
            m_name_clean = m_name.replace('L','').replace('R','').replace('ﾊﾟﾈﾙ', '').replace('ｱｯｼ', '').replace('ｱｳﾀ', '').replace('ｲﾝﾅ', '').replace('ｶﾞｰﾄﾞ', '').strip()
            
            d = distance(m_name, norm_target)
            d_clean = distance(m_name_clean, norm_target_clean)
            
            if m_name == norm_target:
                candidates.append((mp, 1, 0))
            elif m_name_clean == norm_target_clean and len(norm_target_clean) >= 3:
                candidates.append((mp, 1, d)) # L/R等を除いた芯の部分が一致
            elif norm_target in m_name or m_name in norm_target:
                 # 相互包含。文字数が短すぎるものは汎用名詞の誤爆になるためレベルを下げる
                 if len(min(m_name, norm_target, key=len)) >= 6:
                     candidates.append((mp, 2, d))
                 else:
                     candidates.append((mp, 3, d))
            elif norm_target_clean in m_name_clean or m_name_clean in norm_target_clean:
                 if len(min(m_name_clean, norm_target_clean, key=len)) >= 5:
                     candidates.append((mp, 2, d_clean))
                 else:
                     candidates.append((mp, 3, d_clean))
            else:
                prefix_len = min(5, len(norm_target_clean))
                if m_name_clean.startswith(norm_target_clean[:prefix_len]) or norm_target_clean.startswith(m_name_clean[:min(5, len(m_name_clean))]):
                    candidates.append((mp, 3, d_clean))
                elif d_clean <= min(len(norm_target_clean), 4):
                    candidates.append((mp, 4 if d_clean <= 2 else 5, d_clean))

        if not candidates:
            return None, 6, False # 未マッチ

        # 2. 価格完全一致を探す (target_price > 0 の場合のみ)
        if target_price > 0:
            # カラー別価格リストも含めて一致チェック
            price_matches = []
            for c in candidates:
                mp = c[0]
                if mp['price'] == target_price:
                    price_matches.append(c)
                elif mp.get('color_prices'):
                    # カラーバリアント価格のいずれかが一致
                    if any(cp['price'] == target_price for cp in mp['color_prices']):
                        # マスタ価格をカラー一致価格に更新したコピーを作成
                        mp_copy = dict(mp)
                        mp_copy['price'] = target_price
                        price_matches.append((mp_copy, c[1], c[2]))
            if price_matches:
                # 価格一致の中で最もマッチレベルが良い（レベル数値が小さい）、次に距離が小さいものを選択
                price_matches.sort(key=lambda x: (x[1], x[2]))
                best = price_matches[0]
                return best[0], best[1], True  # True = 逆引き成功（価格一致補正）

        # 3. 価格一致がない場合は、通常の最良マッチ（文字列が最も近いもの）を返す
        candidates.sort(key=lambda x: (x[1], x[2]))
        best = candidates[0]
        return best[0], best[1], False

    # items 照合
    resolved_items = []
    has_reverse_match_global = False
    for item in items:
        new_item = dict(item)
        target_name = item.get('name', '')
        target_price = item.get('parts_amount', 0)
        target_part_no = str(item.get('part_no', '')).strip()

        # 画面表示・差額計算用に元の値を保持
        new_item['_original_name'] = target_name
        new_item['_original_parts_amount'] = target_price

        # ★ 最優先: work_code（コグニセブン見積コード）→ ref_a 完全一致
        # コグニセブンで作成された見積はコード列がD1912のref_aと1:1対応するため
        # 名前マッチより確実。コード "0010" → ref_a "0010" の部品レコードを直接特定。
        work_code_raw = str(item.get('work_code', '')).strip()
        matched_mp, match_level, is_reverse = None, 6, False
        if work_code_raw:
            # 数字のみ抽出して4桁ゼロ埋め（例: "10" → "0010", "0010" → "0010"）
            wc_digits = ''.join(filter(str.isdigit, work_code_raw))
            if wc_digits:
                wc_key = wc_digits.zfill(4)
                if wc_key in ref_a_index:
                    matched_mp, match_level, is_reverse = ref_a_index[wc_key], 0, False
                elif wc_key in mirror_index:
                    matched_mp, match_level, is_reverse = mirror_index[wc_key], 0, True

        # コード一致しなかった場合はファジーマッチにフォールバック
        if matched_mp is None:
            matched_mp, match_level, is_reverse = fuzzy_match_part(target_name, target_price, target_part_no)
        
        new_item['_match_level'] = match_level
        if matched_mp:
            new_item['_master_name'] = matched_mp['name']
            new_item['_master_price'] = matched_mp['price']
            new_item['_master_part_no'] = matched_mp.get('part_no', '')
            new_item['_master_repair_code'] = matched_mp.get('repair_code', '')
            new_item['_master_branch_code'] = matched_mp.get('branch_code', '')
            new_item['_master_part_code_r'] = matched_mp.get('part_code_r', '')
            new_item['_master_part_code_l'] = matched_mp.get('part_code_l', '')
            new_item['_master_section_code'] = matched_mp.get('section_code', '')
            new_item['_master_repair_methods'] = matched_mp.get('repair_methods', '')
            if is_reverse:
                new_item['_reverse_match'] = True
                has_reverse_match_global = True
            elif target_price > 0 and matched_mp['price'] > 0 and target_price != matched_mp['price']:
                new_item['_price_warning'] = True
        else:
            new_item['_match_level'] = 6
            new_item['_not_matched'] = True

        resolved_items.append(new_item)

    return resolved_items, has_reverse_match_global


def complement_vehicle_info_with_gemini(api_key, model_code, current_car_name, current_engine):
    """
    車両特定(KA06_ALL)に失敗した場合、型式(model_code)からGemini Web検索等で補完を試みる。
    Google Search Tool を有効化して正確な車種名とエンジン型式を取得する。
    """
    if not api_key or not model_code:
        return {}

    import json
    from google import genai
    from google.genai import types

    client = genai.Client(api_key=api_key)

    prompt = f'''あなたは日本の自動車の専門家です。
以下の型式（Model Code）を持つ自動車の「一般的な車種名（通称名）」と「エンジン型式」を特定し、厳密なJSON形式で出力してください。
型式: {model_code}
現在の情報（空欄の場合あり）:
- 車種名: {current_car_name}
- エンジン型式: {current_engine}

出力形式は必ず以下のJSONだけにしてください。マークダウンや説明は不要です。
{{
    "car_name": "車種名（例: プリウス, Ｎ－ＢＯＸ, アトレー など。メーカー名は含めない）",
    "engine_model": "エンジン型式（例: 2ZR-FXE, S07B など）"
}}
もし明確に不明な場合は、無理に嘘をつかず空文字列にしてください。'''

    try:
        _avail = get_available_gemini_models(api_key)
        _veh_model = _avail[0] if _avail else 'gemini-2.5-flash'
        response = client.models.generate_content(
            model=_veh_model,
            contents=prompt,
            config=types.GenerateContentConfig(
                temperature=0.0,
                max_output_tokens=512,
                response_mime_type='application/json',
            ),
        )
        text = response.text.strip()
        if text.startswith('```json'):
            text = text[7:]
        if text.endswith('```'):
            text = text[:-3]
        info = json.loads(text.strip())
        return info
    except Exception as e:
        print("Gemini Fallback Error:", e)
        return {}

def generate_discrepancy_report_pdf(discrepancies, total_diff, vehicle_info):
    """
    ReportLabを使用して部品価格の差額レポート(PDF)を生成する
    """
    from reportlab.platypus import SimpleDocTemplate, Paragraph, Spacer, Table, TableStyle
    from reportlab.lib.styles import getSampleStyleSheet, ParagraphStyle
    from reportlab.lib import colors
    from reportlab.pdfbase import pdfmetrics
    from reportlab.pdfbase.ttfonts import TTFont
    from reportlab.pdfbase.cidfonts import UnicodeCIDFont
    import io

    # 日本語フォントの登録 (Windows標準のメイリオを試行)
    try:
        pdfmetrics.registerFont(TTFont('Meiryo', 'meiryo.ttc'))
        font_name = 'Meiryo'
    except:
        try:
            pdfmetrics.registerFont(TTFont('MSGothic', 'msgothic.ttc'))
            font_name = 'MSGothic'
        except:
            # フォールバック (ビルトインの HeiseiKakuGo-W5)
            pdfmetrics.registerFont(UnicodeCIDFont('HeiseiKakuGo-W5'))
            font_name = 'HeiseiKakuGo-W5'

    buf = io.BytesIO()
    doc = SimpleDocTemplate(buf, pagesize=A4,
                            rightMargin=20 * mm, leftMargin=20 * mm,
                            topMargin=20 * mm, bottomMargin=20 * mm)

    styles = getSampleStyleSheet()
    styles.add(ParagraphStyle(name='JapaneseTitle', fontName=font_name, fontSize=18, alignment=1, spaceAfter=20))
    styles.add(ParagraphStyle(name='JapaneseNormal', fontName=font_name, fontSize=10, spaceAfter=10))
    styles.add(ParagraphStyle(name='JapaneseBold', fontName=font_name, fontSize=12, spaceAfter=10, textColor=colors.red))

    elements = []

    # タイトル
    elements.append(Paragraph("Addata マスタ連携 金額差分レポート", styles['JapaneseTitle']))

    # 車両情報
    if vehicle_info:
        v_str = f"対象車両: {vehicle_info.get('car_name', '')} {vehicle_info.get('car_model', '')} (車台番号: {vehicle_info.get('car_serial_no', '')})"
        elements.append(Paragraph(v_str, styles['JapaneseNormal']))

    date_str = f"出力日時: {datetime.datetime.now().strftime('%Y/%m/%d %H:%M:%S')}"
    elements.append(Paragraph(date_str, styles['JapaneseNormal']))
    elements.append(Spacer(1, 10 * mm))

    # テーブル構築
    # ヘッダ
    table_data = [['No.', '判定', 'OCR 部品名', 'OCR 価格', '=> マスタ正式名称', 'マスタ定価', '数量', '差額 (小計)']]

    for i, d in enumerate(discrepancies):
        no_str = str(i + 1)
        
        m_level = d.get('_match_level', 0)
        judgment = "未合致" if m_level >= 4 or m_level == 0 else "合致"
        
        ocr_name = d.get('_original_name', '')
        ocr_price = d.get('_original_parts_amount', 0)
        
        master_name = d.get('_master_name', '')
        master_price = d.get('_master_price', 0)
        
        qty = d.get('quantity', 1)
        diff = (master_price - ocr_price) * qty
        
        table_data.append([
            no_str,
            judgment,
            ocr_name,
            f"¥{ocr_price:,}",
            master_name,
            f"¥{master_price:,}",
            str(qty),
            f"¥{diff:,}"
        ])

    # テーブルスタイル
    t = Table(table_data, colWidths=[10*mm, 15*mm, 35*mm, 20*mm, 35*mm, 20*mm, 10*mm, 25*mm])
    t.setStyle(TableStyle([
        ('FONT', (0,0), (-1,-1), font_name, 9),
        ('ALIGN', (0,0), (-1,0), 'CENTER'),
        ('ALIGN', (3,1), (3,-1), 'RIGHT'),
        ('ALIGN', (5,1), (5,-1), 'RIGHT'),
        ('ALIGN', (6,1), (6,-1), 'CENTER'),
        ('ALIGN', (7,1), (7,-1), 'RIGHT'),
        ('BACKGROUND', (0,0), (-1,0), colors.lightgrey),
        ('TEXTCOLOR', (0,0), (-1,0), colors.black),
        ('GRID', (0,0), (-1,-1), 0.5, colors.black),
        ('VALIGN', (0,0), (-1,-1), 'MIDDLE'),
        ('PADDING', (0,0), (-1,-1), 4),
    ]))
    elements.append(t)
    elements.append(Spacer(1, 10 * mm))

    # 合計
    diff_color = 'red'
    if total_diff > 0:
        diff_str = f"マスタ適用による総額変動: +¥{total_diff:,}"
        diff_color = 'blue'
    elif total_diff < 0:
        diff_str = f"マスタ適用による総額変動: ¥{total_diff:,}"
    else:
        diff_str = "マスタ適用による総額変動: なし (¥0)"
        diff_color = 'black'

    # 赤・青など色付きスタイル
    styles.add(ParagraphStyle(name='DiffStyle', fontName=font_name, fontSize=14, alignment=2, textColor=diff_color))
    elements.append(Paragraph(diff_str, styles['DiffStyle']))

    doc.build(elements)
    pdf_bytes = buf.getvalue()
    buf.close()
    return pdf_bytes

def generate_beta_discrepancy_report_pdf(estimate_data, calc_parts, calc_wages, pdf_parts, pdf_wages, vehicle_info):
    """
    ReportLabを使用してベタ打ちモード用の金額ズレ検証レポート(PDF)を生成する
    """
    from reportlab.platypus import SimpleDocTemplate, Paragraph, Spacer, Table, TableStyle
    from reportlab.lib.styles import getSampleStyleSheet, ParagraphStyle
    from reportlab.lib import colors
    from reportlab.pdfbase import pdfmetrics
    from reportlab.pdfbase.ttfonts import TTFont
    from reportlab.pdfbase.cidfonts import UnicodeCIDFont
    import io

    # 日本語フォントの登録 (Windows標準のメイリオを試行)
    try:
        pdfmetrics.registerFont(TTFont('Meiryo', 'meiryo.ttc'))
        font_name = 'Meiryo'
    except:
        try:
            pdfmetrics.registerFont(TTFont('MSGothic', 'msgothic.ttc'))
            font_name = 'MSGothic'
        except:
            # フォールバック (ビルトイン)
            pdfmetrics.registerFont(UnicodeCIDFont('HeiseiKakuGo-W5'))
            font_name = 'HeiseiKakuGo-W5'

    buf = io.BytesIO()
    doc = SimpleDocTemplate(buf, pagesize=(595.27, 841.89), # A4
                            rightMargin=15 * 2.83, leftMargin=15 * 2.83,
                            topMargin=15 * 2.83, bottomMargin=15 * 2.83)

    styles = getSampleStyleSheet()
    styles.add(ParagraphStyle(name='JapaneseTitle', fontName=font_name, fontSize=16, alignment=1, spaceAfter=15))
    styles.add(ParagraphStyle(name='JapaneseNormal', fontName=font_name, fontSize=10, spaceAfter=8))
    styles.add(ParagraphStyle(name='JapaneseBold', fontName=font_name, fontSize=12, spaceAfter=8, textColor=colors.red))

    elements = []
    elements.append(Paragraph("ベタ打ちモード 金額ズレ検証レポート", styles['JapaneseTitle']))

    if vehicle_info:
        v_str = f"対象車両: {vehicle_info.get('car_name', '')} {vehicle_info.get('car_model', '')} (車台番号: {vehicle_info.get('car_serial_no', '')})"
        elements.append(Paragraph(v_str, styles['JapaneseNormal']))
    
    import datetime
    date_str = f"出力日時: {datetime.datetime.now().strftime('%Y/%m/%d %H:%M:%S')}"
    elements.append(Paragraph(date_str, styles['JapaneseNormal']))
    elements.append(Spacer(1, 5 * 2.83))

    parts_diff = calc_parts - pdf_parts
    wage_diff = calc_wages - pdf_wages

    sum_data = [
        ['項目', 'PDF原本 記載値', 'AI抽出 明細合算値', '差額'],
        ['部品合計', f"¥{pdf_parts:,}", f"¥{calc_parts:,}", f"{'+' if parts_diff>0 else ''}{parts_diff:,}円"],
        ['工賃合計', f"¥{pdf_wages:,}", f"¥{calc_wages:,}", f"{'+' if wage_diff>0 else ''}{wage_diff:,}円"]
    ]
    t_sum = Table(sum_data, colWidths=[30*2.83, 40*2.83, 40*2.83, 30*2.83])
    t_sum.setStyle(TableStyle([
        ('FONT', (0,0), (-1,-1), font_name, 10),
        ('ALIGN', (0,0), (-1,0), 'CENTER'),
        ('ALIGN', (1,1), (-1,-1), 'RIGHT'),
        ('BACKGROUND', (0,0), (-1,0), colors.lightgrey),
        ('GRID', (0,0), (-1,-1), 0.5, colors.black),
        ('TEXTCOLOR', (3,1), (3,1), colors.red if parts_diff != 0 else colors.black),
        ('TEXTCOLOR', (3,2), (3,2), colors.red if wage_diff != 0 else colors.black),
    ]))
    elements.append(t_sum)
    elements.append(Spacer(1, 10 * 2.83))

    elements.append(Paragraph("【AIが抽出した全明細行】（※ズレ箇所特定のためのリスト）", styles['JapaneseNormal']))
    table_data = [['No.', '部品/作業名', '区分', '数量', '部品金額', '工賃']]
    items = estimate_data.get('items', [])
    for i, it in enumerate(items):
        name = it.get('name', '')
        method = it.get('method', '')
        # quantity might be float in some edges
        try:
            qty = int(float(it.get('quantity', 1)))
        except:
            qty = 1
        
        try:
            p_amt = int(float(it.get('parts_amount', 0)))
        except:
            p_amt = getattr(it, '_original_parts_amount', 0)
            
        try:
            w_amt = int(float(it.get('wage', 0)))
        except:
            w_amt = 0

        table_data.append([
            str(i + 1), name, method, str(qty), f"¥{p_amt:,}", f"¥{w_amt:,}"
        ])
    
    t_items = Table(table_data, colWidths=[10*2.83, 75*2.83, 25*2.83, 15*2.83, 27*2.83, 27*2.83])
    t_items.setStyle(TableStyle([
        ('FONT', (0,0), (-1,-1), font_name, 8),
        ('ALIGN', (0,0), (-1,0), 'CENTER'),
        ('ALIGN', (3,1), (-1,-1), 'RIGHT'),
        ('BACKGROUND', (0,0), (-1,0), colors.lightgrey),
        ('GRID', (0,0), (-1,-1), 0.5, colors.black),
        ('VALIGN', (0,0), (-1,-1), 'MIDDLE'),
        ('PADDING', (0,0), (-1,-1), 3),
    ]))
    elements.append(t_items)
    doc.build(elements)
    pdf_bytes = buf.getvalue()
    buf.close()
    return pdf_bytes

def analyze_vehicle_registration(api_key, file_bytes, mime_type):
    """車検証をAI-OCRで解析"""
    prompt = """あなたは日本の車検証（自動車検査証）を読み取るOCRエキスパートです。
提供された画像またはPDFから以下の情報を正確に読み取ってください。

【重要な制約事項】
* 入力資料に記載されている文字を一言一句そのまま抽出すること。
* 推測での補完は絶対に行わないこと。
* 読み取り不能な箇所は空文字列""または数値0にすること。
* 勝手な情報の統合・省略は行わないこと。

**必ず有効なJSONのみを返してください。それ以外のテキストは一切不要です。**

返すべきJSON形式:
{
  "customer_name": "使用者の氏名又は名称（法人名含む）",
  "owner_name": "所有者の氏名又は名称",
  "postal_no": "使用者の住所の郵便番号（例: 339-0014）",
  "prefecture": "都道府県名",
  "municipality": "市区町村名",
  "address_other": "それ以降の住所",
  "car_reg_department": "登録番号の地名（例: 大宮）",
  "car_reg_division": "分類番号（例: １０２）※全角数字で",
  "car_reg_business": "用途かな文字（例: う）※全角で",
  "car_reg_serial": "一連番号（例: ８０００）※全角数字で",
  "car_serial_no": "車台番号（例: FD2AB-118821）",
  "car_name": "車名（メーカー名。例: トヨタ, 日産, アウディ）",
  "car_model": "型式（例: 3BA-FD2AB）",
  "car_model_designation": "型式指定番号（5桁の数字。例: 12345）",
  "car_category_number": "類別区分番号（4桁の数字。例: 0001）",
  "engine_model": "原動機の型式（エンジン型式。例: CZE, 2GR-FE, N20B20A）",
  "body_color": "車体の色（例: 白, 黒, シルバー）",
  "color_code": "カラーコード（車検証に記載がある場合。例: 040, 2T, LY9T）",
  "trim_code": "トリムコード（内装コード。車検証に記載がある場合。例: FK, QE）",
  "car_weight": 車両重量（kg単位の整数、不明なら0）,
  "engine_displacement": 総排気量（cc単位の整数、不明なら0）,
  "kilometer": 走行距離の数値（km単位の整数、不明なら0）,
  "term_date": "有効期間の満了日 YYYYMMDD形式（例: 20261125）",
  "car_reg_date": "初度登録年月 YYYYMM00形式（例: 20211100）",
  "confidence": 読み取り全体の信頼度を0.0から1.0で評価
}

注意事項:
- 和暦（令和/平成/昭和）は西暦に変換してください
  令和1年=2019年, 令和2年=2020年 ... 令和8年=2026年
  平成31年=2019年, 平成30年=2018年 ...
- 読み取れない項目は空文字列""または数値0にしてください
- 推測での補完は行わない
- 「車名」欄にはメーカー名のみが記載されていることが多い（例: トヨタ, ニッサン, アウディ）
- 「原動機の型式」はエンジン型式とも呼ばれる。必ず記載通りに正確に転記する
- 「型式指定番号」「類別区分番号」は車検証の右側に記載されていることが多い
- カラーコード・トリムコードは車検証の備考欄や車体の色の近くに記載されている場合がある
"""
    result_text = call_gemini(api_key, file_bytes, mime_type, prompt, use_json_mode=True)
    # JSON modeの場合は直接パース、フォールバックで従来のextract
    try:
        result = json.loads(result_text)
    except (json.JSONDecodeError, TypeError):
        result = extract_json_from_response(result_text)

    # 車名が空欄の場合、車台番号からメーカーを推定
    if not result.get('car_name') and result.get('car_serial_no'):
        maker, _ = guess_manufacturer_from_vin(result['car_serial_no'])
        if maker:
            result['car_name'] = maker

    return result


def analyze_estimate_totals(api_key, file_bytes, mime_type, model_name):
    """1パス目: 合計値・税込/税抜の判定 + 見積書ヘッダの車両情報読み取り"""
    prompt = """あなたは自動車修理見積書のデータ化を行う専門アシスタントです。
提供された見積書から以下の情報を一言一句そのまま抽出してください。

【重要な制約事項】
* 入力資料に記載されている文字を一言一句そのまま抽出すること。勝手な統合・省略・再計算は絶対にしないこと。
* 読み取り不能な箇所は空文字列""または0にすること（推測で補完しない）。
* アジャスターとしての査定や減額調整はこの段階では行わないこと。

**必ず有効なJSONのみを返してください。**

{
  "_thought_process": "判断の根拠を50字以内で",
  "repair_shop_name": "修理工場名・会社名（見積書の発行元。ヘッダや印鑑欄に記載。不明なら空文字）",
  "amount_basis": "明細・合計が税込か税抜かを自動判定: tax_inclusive(税込)/tax_exclusive(税抜)/unknown",
  "tax_reason": "「税込」または「税抜」と判定した根拠（例: 合計欄に消費税が別記されているため税抜）",
  "pdf_parts_total": 見積書に印刷されている部品合計/部品代/部品計の値（整数）,
  "pdf_wage_total": 見積書に印刷されている工賃合計/技術料/工賃計の値（整数）,
  "pdf_grand_total": 見積書に印刷されている最終合計金額（税込・整数）,
  "discount_amount": 値引き額（税込なら税込額、税抜なら税抜額、なければ0・整数）,
  "confidence": 読み取り信頼度 0.0〜1.0,

  "vehicle_info": {
    "car_name": "車名・車種名（記載があれば。なければ空文字）",
    "car_model": "型式（記載があれば。なければ空文字）",
    "engine_model": "エンジン型式（記載があれば。なければ空文字）",
    "color_code": "カラーコード（記載があれば。なければ空文字）",
    "color_name": "色名（記載があれば。なければ空文字）",
    "trim_code": "トリムコード/内装コード（記載があれば。なければ空文字）",
    "grade": "グレード名（記載があれば。なければ空文字）",
    "model_year": "年式（記載があれば。なければ空文字）",
    "chassis_no": "車台番号（記載があれば。なければ空文字）",
    "mileage": 走行距離（km、整数。記載があれば。なければ0）
  }
}

金額の注意:
- 一般的に左列が部品合計、右列が工賃合計
- 「部品計」「部品代」「部品合計額」「部品・油脂」等を探す
- 「工賃計」「技術料」「工賃合計額」等を探す
- 「合計」「税込合計」「総合計」が最終合計
- 金額はカンマを除去して整数で返す
- 読み取れない場合は0（nullではなく）
- 【重要】合計行がページ1ヘッダ上部のサマリーボックスに記載されている場合がある
  （例: Honda Cars系の見積書はページ1上部に合計値、最終ページに合計行なし）
  → 最終ページだけでなく、ページ1のヘッダ部分からも合計値を探すこと
- 【Honda Cars特有】「整備代①」欄の金額 = 部品+工賃の合計（税抜）。
  「整備代①」が合計欄の場合、その値をpdf_grand_totalとして採用する。
  ただし「内消費税10%」が別記されていれば tax_inclusive と判定する。
  「ページ小計」「整備代 小計」はページ内集計であり最終合計ではない。
- 「見積金額」「請求金額」「お見積り金額」等もpdf_grand_totalの候補
- amount_basis の判定ルール（重要）:
  * 「内消費税 ○○円」「うち消費税 ○○円」→ 合計に税が含まれている = tax_inclusive
  * 「(税込)」「税込合計」「税込金額」などの表記 → tax_inclusive
  * 「小計 ○○円 / 消費税 ○○円 / 合計 ○○円」と3行に分かれている → tax_exclusive
  * 合計の上に税抜小計と消費税の行が別々にある → tax_exclusive
  * 合計欄に「税込」の表記があれば → tax_inclusive
  * 判定できない場合のみ → unknown

修理工場名の探し方:
- 見積書の上部・ヘッダ・右上・左上に会社名・店舗名が記載されていることが多い
- 「○○自動車」「○○モータース」「○○板金」等の名称を探す
- FAX送信元の会社名もここに含まれる場合がある

車両情報の注意:
- 見積書のヘッダ部分（上部）に車名・型式・カラーコード等が記載されていることが多い
- 記載がない項目は空文字列""にする（推測しない）
- 「車名」「車種」「Car」等のラベルの横に書かれた値を読む
- 「E/G型式」「エンジン」「原動機」等のラベルの横がエンジン型式
- 「C/C」「カラー」「塗色」等のラベルの横がカラーコード
- 「T/C」「トリム」「内装」等のラベルの横がトリムコード
"""
    try:
        from google.genai import types
        client = _get_genai_client(api_key)
        file_part = types.Part.from_bytes(data=file_bytes, mime_type=mime_type)
        response = client.models.generate_content(
            model=model_name,
            contents=[prompt, file_part],
            config={
                "temperature": 0.0,
                "max_output_tokens": 4096,
                "response_mime_type": "application/json",
            },
        )
        if response.text:
            try:
                return json.loads(response.text)
            except (json.JSONDecodeError, TypeError):
                return extract_json_from_response(response.text)
    except Exception as e:
        err_msg = str(e)
        # モデル廃止エラーを呼び出し元に伝えるため例外を再送出
        if 'no longer available' in err_msg or '404' in err_msg or 'NOT_FOUND' in err_msg:
            raise RuntimeError(f"モデル '{model_name}' は利用できません。サイドバーで別のモデルを選択してください。\n詳細: {err_msg}") from e
    return None


def analyze_estimate_single(api_key, file_bytes, mime_type, model_name, page_num=1, total_pages=1):
    """2パス目: 見積書明細行を全フォーマット対応で読み取る"""
    page_instruction = ''
    if total_pages > 1:
        page_instruction = (
            f'\n\n★★★ これは全{total_pages}ページ中の{page_num}ページ目です。\n'
            'このページに記載されている明細行を全て読み取ってください。\n'
            '特に重要: ページの先頭行・末尾行を見落とさないでください。\n'
            'ページ上部や下部にある行も必ず含めてください。\n'
            '合計行・小計行・ページ小計行・整備代小計行はitemsに含めないでください。\n'
            '【列ズレ防止】各金額は必ずその行の品目にのみ属します。'
            '隣接行の金額を別の行に割り当てることは絶対に禁止です。'
            '列が空欄の場合はその種別の金額=0として扱ってください。\n'
            '【取消線除外】赤線・黒線の取消線が引かれた行は全て除外してください。 ★★★\n'
        )
    prompt = """あなたは自動車修理見積書のデータ化を行う専門アシスタントです。
提供された見積書の画像またはPDFから、すべての明細行を1行も漏らさず正確に読み取ってください。
**必ず有効なJSONのみを返してください。それ以外のテキストは一切不要です。**
**JSONは完結させてください。途中で切れないようにしてください。**

【最重要制約】
* 入力資料に記載されている文字を一言一句そのまま転記すること。
* 勝手な項目の統合、省略、金額の再計算は絶対にしないこと。
* 読み取り不能な箇所は必ず「不明」と記載すること（空欄で省略しない）。
* アジャスターとしての査定・減額調整はこの段階では行わないこと。
* 部品番号（part_no）・作業コード（work_code）が記載されている場合は絶対に省略せず転記すること。

━━━━━━━━━━━━━━━━━━━━━━━━━━
■ 見積書フォーマット自動判定ガイド
━━━━━━━━━━━━━━━━━━━━━━━━━━

見積書には主に10種類のフォーマットがあります。まず全体を見てフォーマットを判定してください。

【フォーマットA: コグニセブン系（部品価格列と工賃列が分離）】
特徴: 「コード | 修理項目/部品名称 | 修理方法/部品番号 | 部品価格(円) | 工賃(円)」
- 部品価格と工賃が別々の列に記載される
- 塗装明細が別セクション「【塗装明細】」にある場合がある
- 費用セクション「【費用】」にショートパーツ・内張り費用等がある
- 小計行に「部品計」「工賃計」「課税額計」「消費税」「合計」がある
→ 部品価格列の値をparts_amountに、工賃列の値をwageに入れる

【フォーマットB: 修理工場系（種別列で作業/部品を区分）】
特徴: 「作業内容/使用部品名 | 作業部位 | 種別 | 数量 | 単価 | 技術料/部品金額」
- 「種別」列に「作業」「部品」と明記されている
- 種別が「作業」→ 金額をwageに入れる（parts_amount=0）
- 種別が「部品」→ 金額をparts_amountに入れる（wage=0）
- 最下部に「技術料計」「部品計」「整備合計」がある

【フォーマットC: メルセデスベンツ系ディーラー（作業コード＋金額の1列）】
特徴: 「作業コード/部品番号 | 作業内容/部品名 | 時間/数量 | 金額」
- 作業と部品が混在し、金額が1列のみ
- 作業コードがBPで始まる → 作業行（wage=金額, parts_amount=0）
- 作業コードがMAまたはMNで始まる → 部品行（parts_amount=金額, wage=0）
- 作業名に「ペイント」「塗装」を含む → 作業行
- 作業名に「脱着」「交換」「修理」「板金」を含む → 作業行
- 最下部に「技術料」「部品代」「整備代合計」「消費税」「合計金額」がある

【フォーマットD: BMW系ディーラー（概算見積書・セクション分け＋作業CD）】
特徴: 「項目 | 作業CD/部品No. | 作業項目/部品名 | 工数/数量 | 単価 | 金額」
- セクション分け（A: 事故修理、B: 搬送費用 等）がある
- 作業CDが「MM99」で始まる行 → 工賃行（wage=金額, parts_amount=0）
- 作業CDが「UU99」で始まる行 → その他費用行（wage=金額, parts_amount=0）
- 作業CDが数字のみ（例: 0711 9904 207）→ 部品行（parts_amount=金額, wage=0）
- 工賃行のquantityは1にする（工数は時間なので数量ではない）
- 最下部に「工賃合計額」「部品合計額」「税込合計金額」がある

【フォーマットE: 町工場系（品名＋数量＋単価＋金額＋工賃の5列構成）】
特徴: 「品名 | 数量 | 単価 | 金額 | 工賃」の列構成
- 作業行: 「○○脱着組替」等、右端の「工賃」列に金額がある → wage=工賃列の値
- 部品行: 部品名＋数量＋単価＋金額 → parts_amount=金額列の値
- 最下部に「部品代」「工賃」「値引き」「小計」「消費税」「合計」がある

【フォーマットF: トヨタディーラー系（概算見積書・作業内容＋使用部品＋技術料）】
特徴: 「作業内容 | 使用部品 | 個数 | 部品・油脂 | 技術料 | 計」の列構成
- 作業行は「○○脱着」「○○修理」等 → 技術料列に金額がある（wage=技術料）
- 部品行は使用部品名＋個数＋部品金額 → parts_amount=部品・油脂列の値
- 「ショートパーツ」→ short_parts_wageに合算
- 最下部に「整備代金合計」が部品・技術料の内訳付きで記載される

【フォーマットL: Honda Cars / ホンダディーラー系（概算お見積書・2列金額）】
特徴: 「No | 整備内容（部品又は作業名） | 作業 | 数量 | 部品・油脂代 | 技術料」
識別方法: Honda Carsロゴ、「概算お見積書」「板金塗装」ヘッダ、"Honda Cars"または"ホンダカーズ"の記載
列の位置（左→右）: 品名列 → 作業列 → 数量列 → 【部品・油脂代列】 → 【技術料列】
- 【部品・油脂代列】（左側の金額列）の値 → parts_amount に入れる
- 【技術料列】（右側の金額列）の値 → wage に入れる
- 同一行に両列に値がある場合 → parts_amountとwageの両方に入れる
- セクション番号付き（例: "1 板金塗装修理"  "2 内装部品交換"）

★★★ Honda Cars形式で絶対に守るべき列ズレ防止ルール ★★★
【最頻出エラーパターン（必ず回避せよ）】
Honda Cars見積書では「部品のみの行」と「技術料のみの行」が交互に出現する。
このとき、ある行の技術料を次の行の技術料と誤って合算・置換することが頻発する。

NG例（絶対にしてはいけない）:
  見積書の実際のレイアウト:
  ├─ ガーニッシュASSY Rスライドドア  交換  1.0  【4,917】  【    】
  ├─ コーティング再施工             [作業] 1.0  【    】  【26,400】
  ├─ 諸費用                        [費用] 1.0  【4,675】  【    】
  └─ 材料費                        [費用] 1.0  【26,675】 【    】

  誤った読み取り（NG）:
  × ガーニッシュASSY: parts=4,917, wage=26,400  ← 下の行の技術料を取り込んでいる
  × コーティング再施工: parts=4,675, wage=0     ← さらに下の行の部品代を取り込んでいる
  × 諸費用: parts=26,675, wage=0                ← さらに下の行の値を取り込んでいる

  正しい読み取り（OK）:
  ○ ガーニッシュASSY: parts=4,917, wage=0       ← 技術料列が空なのでwage=0
  ○ コーティング再施工: parts=0, wage=26,400    ← 部品列が空なのでparts=0
  ○ 諸費用: parts=4,675, wage=0                 ← 技術料列が空なのでwage=0
  ○ 材料費: parts=26,675, wage=0                ← 技術料列が空なのでwage=0

【Honda Cars部品/技術料の判定基準】
  - 部品番号（英数字コード）が記載されている行: 部品代列(左)の値→parts_amount
  - 「清掃」「エーミング」「コーティング」「塗装費用」「洗車」等の作業名: 技術料列(右)の値→wage
  - 「諸費用」「材料費」「ショートパーツ」: 部品代列(左)の値→parts_amount
  - GARN ASSY R.FR ST 等の部品名で部品番号付き: 部品代列(左)の値→parts_amount（技術料列は空でwage=0）
  - 整備代 小計行・ページ小計行 → itemsに含めない（合計行のため）

【Honda Cars取消線（抹消行）の厳格処理】
  - 見積書上で赤線・黒線の取消線が引かれた行（例: GARN ASSY*NH900L* に2本の横線）
  - このような取消行は完全に除外すること
  - 同一部品番号が複数行に記載され、一方に取消線がある場合 → 取消線のない行のみ採用
  - 具体例: 「8412132R003ZA 3,850」が赤線付きで出現 → この行を除外、他の行のみ採用

【フォーマットG: 整備工場系（整備内容＋技術料＋部品単価＋部品小計の4列）】
特徴: 「整備内容 | 技術料(円) | 数量 | 部品単価(円) | 部品小計(円)」
- 1行に技術料と部品小計の両方が存在する場合がある
- 数量に単位が付く場合（「1個」「10個」「2本」）→ 数値部分のみ抽出
- 最下部に「A 技術料」「B 部品代」の合計が記載される

【フォーマットH: ヤナセ系（左右2カラム構成・作業と部品が左右に分離）】
特徴: 左側に「作業内容 | 金額」、右側に「使用部品 | 数量 | 金額」が並ぶ
- 左カラム: 作業内容と作業金額 → wageに入れる
- 右カラム: 使用部品名＋数量＋部品金額 → parts_amountに入れる
- 最下部に「定価合計:（作業）金額（部品）金額（全体）金額」がある

【フォーマットI: トラック整備系（部品列と工賃列が分離した一般的な4列）】
特徴: 「作業内容及び部品明細 | 数量 | 単価 | 部品 | 工賃」の5列
- 工賃列に値がある行 → wage=工賃列の値
- 部品列に値がある行 → parts_amount=部品列の値
- 「ショートパーツ」「材料費」は部品扱い（parts_amountに入れる）

【フォーマットJ: UDトラックス系（区コードで作業/部品を判別）】
特徴: 「区 | 作業コード(部品番号) | 作業内容(部品名称) | 数量 | 定価/単価 | 金額」
- 区=11 → 作業行（wage=金額, parts_amount=0, quantity=1）
- 区=1  → 部品行（parts_amount=金額, wage=0）
- 区=5  → セクションヘッダ → itemsに含めない
- 区=7  → その他費用行（wage=金額）

【フォーマットK: スズキ/ダイハツディーラー系（工数×単価方式）】
特徴: 「作業項目 | 修理方法 | 工数 | 工賃単価 | 数量 | 部品価格 | 部品番号」の7列構成
- 「工数」列（例: 0.70, 1.50, 2.30）と「工賃単価」列（例: 7,700, 25,300）が分離している
- 工賃 = 工賃単価列の値（工数は参考情報）→ wage=工賃単価列の値
- 部品価格 = 数量列の右隣の金額列 → parts_amount=部品価格列の値
- 同一行に工賃(wage)と部品価格(parts_amount)の両方が存在することがある
  例: 「LH フロントフェンダ パネル | 取替 | 0.70 | 7,700 | 1.00 | 21,300 | 57711-59S00」
      → name=LH フロントフェンダ パネル, method=取替, wage=7700, quantity=1, parts_amount=21300, part_no=57711-59S00
- 工数のみで部品価格列が空の行 → 作業行（wage=工賃単価, parts_amount=0）
  例: 「左 フロントフェンダー エプロン | 鈑金 | 0.80 | 8,800」→ wage=8800, parts_amount=0
- 部品価格のみで工賃列が空の行 → 部品行（parts_amount=部品価格, wage=0）
- 塗装セクション（2ページ目等）: 「作業項目 | 工数 | 工賃単価 | 係数 | 塗装工賃」の5列
  塗装工賃 = 工賃単価×係数（または直接記載値）→ wage=塗装工賃列の値
  例: 「左フロントフェンダパネル取替 | 1.50 | 16,500 | 0.45 | 7,425」→ wage=7425
- 「OBD点検」等の点検行: 「OBD点検 | 点検 | 1.00 | 11,000」→ wage=11000, parts_amount=0
- 最下部に「部品計」「工賃計」「塗装工賃計」「消費税」「合計」がある
→ 各列の値を正確に読み取り、工賃列と部品価格列を絶対に取り違えないこと

━━━━━━━━━━━━━━━━━━━━━━━━━━
■ 返すべきJSON形式
━━━━━━━━━━━━━━━━━━━━━━━━━━
{
  "_thought_process": "フォーマット判定の根拠と税込/税抜の判断理由を100字以内で",
  "amount_basis": "tax_inclusive(明細が税込) / tax_exclusive(明細が税抜) / unknown",
  "tax_reason": "「税込」または「税抜」と判定した根拠を簡潔に（例: 合計欄に消費税が別記されているため税抜と判定）",
  "items": [
    {
      "name": "部品名または作業名（見積書に記載のまま正確に転記）",
      "method": "区分（取替/脱着/修理/塗装/交換/調整/板金/部品 等）",
      "quantity": 数量（整数に丸める。1.00→1）,
      "parts_amount": その行の部品金額合計（整数。作業行は0。カンマ・¥記号を除去した純粋な整数）,
      "wage": その行の工賃/技術料（整数。部品行は0。カンマ・¥記号を除去した純粋な整数）,
      "part_no": "部品番号/品番【STEP2正規化】全角→半角英数字に変換・不要な空白削除・ハイフンは除去。なければ空文字列",
      "work_code": "作業コード/部品コード（見積書の『コード』列に記載された値をそのまま転記。なければ空文字列）"
    }
  ],
  "short_parts_wage": ショートパーツ・雑品代・小物部品代の合計（整数。なければ0。itemsには含めない）,
  "tax_exempt_amount": 預託金・廃棄処分費用等の非課税費用合計（整数。なければ0。itemsには含めない）,
  "discount_amount": 値引き額（整数。なければ0。items には含めない）,
  "pdf_parts_total": 見積書記載の「部品計」「部品代」の値（整数）,
  "pdf_wage_total": 見積書記載の「工賃計」「技術料」の値（整数）,
  "confidence": 読み取り信頼度 0.0〜1.0,
  "totals_verification": {
    "calculated_parts_total": itemsのparts_amount合計（整数）,
    "calculated_labor_total": itemsのwage合計（整数）,
    "document_parts_total": 見積書記載の部品合計（pdf_parts_totalと同値・整数）,
    "document_labor_total": 見積書記載の工賃合計（pdf_wage_totalと同値・整数）,
    "parts_diff": calculated_parts_total - document_parts_total（差額・整数）,
    "labor_diff": calculated_labor_total - document_labor_total（差額・整数）,
    "is_match": partsとlaborの差額が両方0ならtrue、1円でもズレがあればfalse,
    "validation_error": "差額がある場合は原因と推測箇所を記載。一致している場合はnull"
  }
}

━━━━━━━━━━━━━━━━━━━━━━━━━━
■ 【最最最重要】行と金額の一対一対応原則
━━━━━━━━━━━━━━━━━━━━━━━━━━
これは全てのフォーマットに共通する絶対原則です。

★ 各金額は必ずその行の品目にのみ属します ★
★ 隣接する行の金額を別の行に割り当てることは絶対に禁止です ★

【原則の適用方法】
1. テーブルの各行を上から順に1行ずつ処理する
2. その行の「部品列」に値がある → parts_amountに設定（wage=0）
3. その行の「技術料/工賃列」に値がある → wageに設定（parts_amount=0）
4. その行の両方の列に値がある → 両方に設定
5. その行の両方の列が空 → その行はitemsに含めない

【特に重要】列が空欄のときの扱い:
- 部品列が空欄 → parts_amount = 0（前後の行の値を借用しない）
- 技術料列が空欄 → wage = 0（前後の行の値を借用しない）
- 「空欄 = その行にその種別の金額なし = 0」これが絶対ルール

━━━━━━━━━━━━━━━━━━━━━━━━━━
■ 「取替（交換）」同一行パターンの部品代/工賃分離
━━━━━━━━━━━━━━━━━━━━━━━━━━
見積書には、部品項目と作業項目が同一行に記載されている形式が頻出する。
例: 「Fバンパー 取替  部品代21,300  工賃7,700」
この場合:
  → name="Fバンパー", method="取替", parts_amount=21300, wage=7700
ルール:
- 1行に「部品代（部品金額）」と「工賃（技術料）」の両方が存在する場合、必ず分離して記録
- 「取替」「交換」「脱着組替」等の作業名が部品名に付随している場合、それはmethodに入れる
- 金額が1列しかない場合でも、行の種別（部品行 or 作業行）を正確に判定する
- 部品名の横の金額 → parts_amount、作業名の横の金額 → wage
- 判定に迷う場合: 部品番号がある行の金額 → parts_amount、工数がある行の金額 → wage
- 品質基準: 部品代と工賃の分離精度は99%以上を目標とする

━━━━━━━━━━━━━━━━━━━━━━━━━━
■ 読み取りルール（厳守）
━━━━━━━━━━━━━━━━━━━━━━━━━━
【STEP 1: 完全抽出】
1. 明細テーブルの全行を1行ずつ正確に読み取る。行を絶対に飛ばさない。
2. 複数ページにまたがる場合、全ページの明細を必ず結合する。
3. 部品名は見積書に記載のとおり正確に転記する。
4. 勝手な査定（アジャスト）、減額、工法変更、項目の削除や統合は一切行わない。
5. 塗装明細の各パネル行は通常の明細行として含める（wage=塗装工賃）。
6. 費用セクションの扱い:
   - 「ショートパーツ」「小物部品」「雑品代」→ short_parts_wageに合算
   - 「内張り費用」「室内清掃費」「写真代」等 → 通常の明細行（wage）
7. parts_amountとwageの両方に値がある行もある。
8. 合計行・小計行・ページ小計行はitemsに含めない。
9. 「値引き」行はitemsに含めず discount_amount に記録する。
10. FAX受信で画質が悪い場合でも、読み取れる文字は最大限読み取る。
11. 「塗装に含む」「塗装費用」は工賃行として扱う（wage=金額）。
12. 「油脂代」は部品扱い（parts_amountに入れる）。
13. 数量が品名の後ろに「(数字」「（数字」形式で記載されている場合がある。
    例: 「ｸﾘｯﾌﾟﾅｯﾄ 取替 (14 1,960」→ 品名=ｸﾘｯﾌﾟﾅｯﾄ, method=取替, quantity=14, parts_amount=1960
    この「(数字」は数量であり、品名に含めない。先頭のゼロも除去して整数にする。
14. 工賃欄に「**」「＊＊」「***」等のアスタリスクのみが記載されている場合は工賃なし（wage=0）として扱う。
15. 「ショートパーツ」「雑品代」「小物部品代」はitemsに含めず、short_parts_wageに合算する。
16. 「預託金」「廃棄処分費用」「産業廃棄物処理代」「産廃費用」「リサイクル預託金」は非課税費用。
    itemsに含めず、必ず tax_exempt_amount に金額を記録する。
17. 【コード類の確実な抽出】見積書に「コード」列がある場合、その値を work_code フィールドに必ず転記。
    部品番号・品番がある場合は part_no フィールドに必ず転記すること。絶対に省略しない。
18. 【税区分の明記】amount_basis と tax_reason を必ず返すこと。
    tax_reason には「合計欄に消費税が別記されているため税抜」等、判定根拠を具体的に書く。
19. 金額0の行も含める（0は0として記録する）。
20. 【OBD点検・診断料の工賃抽出】「OBD点検」「OBD診断」「診断料」「システム診断」等の行は、
    隣接する金額列（例: 11,000）を必ず wage として抽出すること。絶対に0にしない。
    これらはスズキ・ダイハツ系フォーマットでは「工数×単価」方式で記載される。
21. 【スズキ系塗装工賃】塗装セクションで「工数 | 工賃単価 | 係数 | 塗装工賃」の形式がある場合、
    最右列の「塗装工賃」値（例: 7,425）をwageとして使う。中間の係数(0.45等)は無視してよい。
22. 【取消線・抹消行の絶対除外（Honda Cars形式で特に重要）】
    ★ 取消線のある行は存在しないものとして扱う ★
    - 赤線・黒線・斜線等の取消線（打ち消し線）が文字や行に引かれている行は除外
    - 取消線のある行の金額は絶対にparts_amount/wageに加算しない
    - 一部の文字だけに取消線がある場合でもその行全体を除外する
    【Honda Cars見積書での頻出パターン】
    同一部品番号が3行記載され、うち2行に取消線（修正の経緯）:
      行A: GARN ASSY*NH900L* 8412132R003ZA  3,850  ← 赤線あり → 除外
      行B: LNG ASSY*NH900L*  8311132R003ZA  1,342  ← 赤線なし → 採用
      行C: GARN ASSY*NH900L* 8420132R003ZA  1,702  ← 赤線あり → 除外
      行D: モジュールASSY,ドライバ           44,000 ← 赤線なし → 採用
      行E: LNG ASSY*NH900L*  8311132R003ZA  1,342  ← 赤線あり → 除外
    → 採用するのは行B(1,342)と行D(44,000)のみ。行A・C・Eは全て除外。
    - 取消線の色（赤・黒）にかかわらず、線が引かれている行は必ず除外すること

【STEP 2: DBマッチング用データ正規化】
20. 【部品番号の正規化】part_no フィールドの値:
    - 全角英数字 → 半角英数字に変換（例: 「７４０７５−０２０３０」→「74075-02030」）
    - 前後の不要な空白を削除
    - ハイフン（-）や全角文字が混在する場合も半角英数字に統一
21. 【金額・数値の正規化】parts_amount・wage:
    - カンマ（,）「¥」「円」は除去し、純粋な整数（Integer型）にする
    - 例: 「¥19,550」→ 19550、「1.00」→ 1
22. 【表記ゆれの正規化】部品名の全角・半角混在を内部的に認識:
    - 半角カタカナ（ｱｲｳ）と全角カタカナ（アイウ）を同一視してマッチング精度を上げる
    - ただし、part_noフィールドへの転記は必ず半角英数字で行う

【STEP 3: 総額完全合致バリデーション】
23. 【必須バリデーション】以下の計算を必ず内部実行し、totals_verificationに記録すること:
    - calculated_parts_total = items全行のparts_amountの合計
    - calculated_labor_total = items全行のwageの合計
    - parts_diff = calculated_parts_total - document_parts_total（0なら一致）
    - labor_diff = calculated_labor_total - document_labor_total（0なら一致）
24. 【不一致時の対応】差額が1円でもある場合:
    - is_match = false に設定する
    - validation_error に差額と推測される原因（行の見落とし・金額の誤読等）を記載する
    - 見積書を再精読して行の見落としがないか確認する
25. 【合計一致が最優先】最終的にitemsの合計が見積書記載値と一致するよう、全力で正確な抽出を行うこと。
"""
    if page_instruction:
        prompt = page_instruction + prompt
    from google.genai import types
    client = _get_genai_client(api_key)
    file_part = types.Part.from_bytes(data=file_bytes, mime_type=mime_type)
    last_error = None
    for attempt in range(3):
        try:
            response = client.models.generate_content(
                model=model_name,
                contents=[prompt, file_part],
                config={
                    "temperature": 0.0,
                    "max_output_tokens": 65536,
                    "response_mime_type": "application/json",
                },
            )
            if response.text and response.text.strip():
                result_text = response.text
                try:
                    return json.loads(result_text)
                except (json.JSONDecodeError, TypeError):
                    return extract_json_from_response(result_text)
            if attempt < 2:
                import time; time.sleep(2)
                continue
            raise ValueError("Geminiから有効な応答が得られませんでした。")
        except ValueError:
            raise
        except Exception as e:
            last_error = e
            err_msg = str(e)
            # モデル廃止エラーはリトライせずに即座に再送出
            if 'no longer available' in err_msg or 'NOT_FOUND' in err_msg:
                raise RuntimeError(
                    f"モデル '{model_name}' は利用できません。"
                    "サイドバーで「gemini-2.5-flash」または「gemini-2.5-pro」を選択してください。"
                ) from e
            if attempt < 2:
                import time; time.sleep(2)
                continue
            raise ValueError(f"Gemini API呼び出しに失敗しました: {str(last_error)}")


def validate_and_correct_items(items):
    """
    辞書ベースバリデーション: AIの誤分類を後処理で修正する。
    - 「脱着」「交換」等の作業系methodなのにparts_amountだけ入っている → wageへ移動
    - ただし「取替」「交換」で parts_amount と wage の両方が入っている行は正常（部品＋工賃同一行）
    """
    WAGE_METHODS  = {'脱着', '取外', '取付', '修理', '調整', '板金', '塗装',
                     'ペイント', '研磨', '清掃', '点検', '作業', '交換', '脱外組付',
                     '修正', '組付', '施工', '補修'}
    # 取替/交換は部品代＋工賃の両方が同一行に存在するパターンが多い
    BOTH_OK_METHODS = {'取替', '交換', '脱着組替', '取外組付'}
    corrected = []
    for item in items:
        item = dict(item)
        method    = str(item.get('method', ''))
        name      = str(item.get('name', ''))
        parts_amt = safe_int(item.get('parts_amount', 0))
        wage      = safe_int(item.get('wage', 0))
        # 取替/交換で部品金額と工賃の両方がある → 正常（分離済み）→ そのまま
        is_both_ok = any(kw in method for kw in BOTH_OK_METHODS) and parts_amt > 0 and wage > 0
        if is_both_ok:
            corrected.append(item)
            continue
        # 作業系キーワードがあるのに部品金額のみ → wageへ
        is_wage_method = any(kw in method for kw in WAGE_METHODS)
        is_wage_name   = any(kw in name   for kw in {'脱着', '板金', '塗装', 'ペイント', '修理', '研磨'})
        if (is_wage_method or is_wage_name) and parts_amt > 0 and wage == 0:
            item['wage']         = parts_amt
            item['parts_amount'] = 0
        corrected.append(item)
    return corrected


def extract_special_items(items, existing_sp=0, existing_exempt=0):
    """
    ショートパーツ・預託金等の特殊項目を明細行から抽出してExpense用に分離する。
    二重計上を防止するため、明細行からは除去してExpense値として返す。
    Returns: (filtered_items, short_parts_wage, tax_exempt_amount)
    """
    SP_KEYWORDS = {'ショートパーツ', 'ｼｮｰﾄﾊﾟｰﾂ', '雑品代', '小物部品代', '雑品', 'ショートパーツ代'}
    EXEMPT_KEYWORDS = {'預託金', '廃棄処分費用', '預託/廃棄処分費用', 'リサイクル預託金',
                       '預託/廃棄処分', '廃棄処分', 'ﾘｻｲｸﾙ預託金'}
    filtered = []
    sp_total = existing_sp
    exempt_total = existing_exempt
    for item in items:
        name = str(item.get('name', '')).strip()
        parts = safe_int(item.get('parts_amount', 0))
        wage = safe_int(item.get('wage', 0))
        amount = parts + wage
        # ショートパーツ判定
        if any(kw in name for kw in SP_KEYWORDS):
            sp_total += amount
            continue
        # 預託金・廃棄処分費用判定
        if any(kw in name for kw in EXEMPT_KEYWORDS):
            exempt_total += amount
            continue
        filtered.append(item)
    return filtered, sp_total, exempt_total


def deduplicate_page_items(all_items):
    """
    複数ページ分割時のページ境界での重複行を除去する。
    同一品名＋同一金額の行がページ境界付近で連続する場合、重複とみなして除去。
    """
    if len(all_items) <= 1:
        return all_items
    deduped = [all_items[0]]
    for i in range(1, len(all_items)):
        curr = all_items[i]
        prev = deduped[-1]
        # 品名・部品金額・工賃が全て一致する場合は重複と判定
        same_name  = str(curr.get('name', '')).strip() == str(prev.get('name', '')).strip()
        same_parts = safe_int(curr.get('parts_amount', 0)) == safe_int(prev.get('parts_amount', 0))
        same_wage  = safe_int(curr.get('wage', 0)) == safe_int(prev.get('wage', 0))
        if same_name and same_parts and same_wage and str(curr.get('name', '')).strip():
            continue  # 重複 → スキップ
        deduped.append(curr)
    return deduped


def validate_row_consistency(items):
    """
    明細行ごとの整合性チェック。
    数量 × 単価 ≠ 部品金額 の不整合を検出し、可能な限り自動修正する。
    Returns: (corrected_items, warnings_list)
    """
    corrected = []
    warnings = []
    for i, item in enumerate(items):
        item = dict(item)
        qty   = safe_int(item.get('quantity', 1), 1)
        parts = safe_int(item.get('parts_amount', 0))
        wage  = safe_int(item.get('wage', 0))
        name  = str(item.get('name', ''))

        if parts > 0 and qty > 1:
            # 単価を逆算して整合性チェック
            unit_price = parts / qty
            # 単価が整数でなければ不整合の可能性
            if abs(unit_price - round(unit_price)) > 0.01:
                # 数量=1として全額を部品金額とみなす方が正しいか判定
                # 例: parts_amount=1960, qty=14 → 140円/個 → 整合（OK）
                # 例: parts_amount=5000, qty=3 → 1666.67円/個 → 不整合
                warnings.append(
                    f"行{i+1}「{name}」: 数量{qty} × 単価{unit_price:.1f} ≠ 部品金額¥{parts:,}（端数あり）"
                )
            # 単価が極端に小さい場合（1円未満）も警告
            elif round(unit_price) < 1:
                warnings.append(
                    f"行{i+1}「{name}」: 単価が極端に小さい（¥{unit_price:.0f}/個）、数量{qty}を確認してください"
                )

        # 部品金額も工賃もゼロの行は警告（0円行が意図的でない可能性）
        if parts == 0 and wage == 0 and name and name != '値引き':
            # ただし method が「脱着」「取外」「組付」など工賃0円が妥当な作業は除外
            method = str(item.get('method', ''))
            zero_ok_methods = {'脱着', '取外', '取付', '組付', '点検', '調整', '清掃'}
            if not any(kw in method for kw in zero_ok_methods) and not any(kw in name for kw in zero_ok_methods):
                warnings.append(
                    f"行{i+1}「{name}」: 部品金額・工賃ともに0円です"
                )

        corrected.append(item)
    return corrected, warnings


def build_estimate_summary(items, short_parts_wage, pdf_parts_total,
                           pdf_wage_total, pdf_grand_total, discount_amount=0,
                           gemini_amount_basis=''):
    """
    税込/税抜を自動判定してNEO書込み用正規化サマリーを返す。
    Returns: {
      'basis': 'tax_inclusive' / 'tax_exclusive' / 'unknown',
      'norm_parts': 税抜部品合計,
      'norm_wage':  税抜工賃合計,
      'norm_sp':    税抜ショートパーツ,
      'norm_disc':  税抜値引き,
      'grand':      税込総合計,
      'reverse_match': bool  ← 逆算で総合計が一致するか
    }
    """
    calc_parts = sum(safe_int(it.get('parts_amount', 0)) for it in items)
    calc_wage  = sum(safe_int(it.get('wage', 0))         for it in items)
    sp    = safe_int(short_parts_wage)
    disc  = safe_int(discount_amount)
    grand = safe_int(pdf_grand_total)

    if grand <= 0:
        return {
            'basis': 'tax_exclusive',
            'norm_parts': calc_parts, 'norm_wage': calc_wage,
            'norm_sp': sp, 'norm_disc': disc,
            'grand': 0, 'reverse_match': False,
        }

    TOLERANCE = 50  # 円
    items_sum = calc_parts + calc_wage + sp - disc
    # 税込判定: (items_sum) ≈ grand (既に税込)
    tax_incl = abs(items_sum - grand) <= TOLERANCE
    # 税抜判定: round((sum) * 1.1) ≈ grand
    tax_excl = abs(round(items_sum * (1 + TAX_RATE)) - grand) <= TOLERANCE

    if tax_incl and not tax_excl:
        basis = 'tax_inclusive'
    elif tax_excl:
        basis = 'tax_exclusive'
    else:
        # どちらにも合わない場合: PDFの列合計と grand を比較
        # ① sp が pdf_parts_total に既に含まれている場合（多くのフォーマット）
        #    pdf_parts_total + pdf_wage_total ≈ grand → tax_inclusive
        # ② sp が列合計に含まれていない場合（コグニセブン等）
        #    pdf_parts_total + pdf_wage_total + sp ≈ grand → tax_inclusive
        # ※ 旧実装では sp を常に加算していたため、フォーマット①で二重計上となりバグ発生
        pdf_parts = safe_int(pdf_parts_total)
        pdf_wage  = safe_int(pdf_wage_total)
        # ①: sp込みの列合計（フォーマットF等、spが部品列に含まれる場合）
        pdf_sum_sp_in  = pdf_parts + pdf_wage - disc
        # ②: sp別立ての列合計（フォーマットA等、spが費用セクションに別途記載の場合）
        pdf_sum_sp_out = pdf_parts + pdf_wage + sp - disc
        if abs(pdf_sum_sp_in - grand) <= TOLERANCE or abs(pdf_sum_sp_out - grand) <= TOLERANCE:
            basis = 'tax_inclusive'
        else:
            basis = 'unknown'

    # Geminiの明示的な判定で unknown を上書き
    # 数値判定が不確定な場合に限り、AIの判断を補助シグナルとして採用
    if basis == 'unknown' and gemini_amount_basis in ('tax_inclusive', 'tax_exclusive'):
        basis = gemini_amount_basis
    # 数値判定とGemini判定が一致する場合はそのまま採用（補強）
    # 数値判定とGemini判定が矛盾する場合はGeminiを優先（数値だけでは曖昧なケースが多い）
    elif basis != 'unknown' and gemini_amount_basis in ('tax_inclusive', 'tax_exclusive') and basis != gemini_amount_basis:
        # 数値判定が曖昧（tax_inclとtax_exclの両方が合致する場合等）
        if tax_incl and tax_excl:
            basis = gemini_amount_basis  # 両方合致 → Geminiの文脈判定を優先

    if basis == 'tax_inclusive':
        norm_parts = round(calc_parts / (1 + TAX_RATE))
        norm_wage  = round(calc_wage  / (1 + TAX_RATE))
        norm_sp    = round(sp         / (1 + TAX_RATE))
        norm_disc  = round(disc       / (1 + TAX_RATE))
    else:
        norm_parts = calc_parts
        norm_wage  = calc_wage
        norm_sp    = sp
        norm_disc  = disc

    reverse_grand = round((norm_parts + norm_wage + norm_sp - norm_disc) * (1 + TAX_RATE))
    reverse_match = abs(reverse_grand - grand) <= TOLERANCE

    return {
        'basis':       basis,
        'norm_parts':  norm_parts,
        'norm_wage':   norm_wage,
        'norm_sp':     norm_sp,
        'norm_disc':   norm_disc,
        'grand':       grand,
        'reverse_match': reverse_match,
    }


def _self_correction_retry(api_key, file_bytes, mime_type, model_name,
                           original_items, target_parts, target_wage):
    """
    合計値との差額をフィードバックして再抽出し、改善された場合のみ採用する。
    Returns: 改善後の result dict、または None（改善なし）
    """
    calc_parts = sum(safe_int(it.get('parts_amount', 0)) for it in original_items)
    calc_wage  = sum(safe_int(it.get('wage', 0))         for it in original_items)
    parts_diff = calc_parts - target_parts
    wage_diff  = calc_wage  - target_wage

    if (abs(parts_diff) <= SELF_CORRECTION_THRESHOLD and
            abs(wage_diff) <= SELF_CORRECTION_THRESHOLD):
        return None  # 差額が閾値以下 → 修正不要

    correction_prompt = f"""【STEP 3 バリデーション失敗 - 自己修復モード】

前回の読み取り結果に以下の金額誤差が検出されました。
これは1円の狂いも許されません。見積書を最初から再精読して完全に正確な抽出を行ってください。

■ 検出された誤差:
- 部品合計: 計算値 ¥{calc_parts:,} ≠ PDF記載 ¥{target_parts:,} （差額 {parts_diff:+,}円）
- 工賃合計: 計算値 ¥{calc_wage:,} ≠ PDF記載 ¥{target_wage:,} （差額 {wage_diff:+,}円）

■ よくある誤差原因（必ずチェックしてください）:
1. 行の見落とし → 見積書の全明細行を先頭から末尾まで1行ずつ数え直す
2. 部品と工賃の取り違え → wageに入れるべきものがparts_amountに入っている（またはその逆）
3. 数量の誤読 → 「10」を「1」と読んでいる、小数点のずれ等
4. ショートパーツをitemsに含めている → short_parts_wageに分離すること
5. 金額の読み取りミス → カンマ区切りの桁ずれ（19,550を1,955と読む等）
6. 複数行を1行に合算している → 必ず1行ずつ個別に記録すること

■ 修復指示:
- parts_diffが{parts_diff:+,}円 → 部品金額を合計{abs(parts_diff):,}円分{'追加' if parts_diff < 0 else '削減'}すること
- labor_diffが{wage_diff:+,}円 → 工賃を合計{abs(wage_diff):,}円分{'追加' if wage_diff < 0 else '削減'}すること

【絶対要件】
・勝手な査定（アジャスト）、減額、工法変更、項目削除は行わないこと
・見積書に記載されている金額を一言一句正確に読み取ること
・totals_verificationのis_matchがtrueになるまで再抽出を続けること

正しいJSONで再度出力してください（形式は前回と同じ）。
**必ず有効なJSONのみを返してください。**
"""
    try:
        from google.genai import types
        client = _get_genai_client(api_key)
        file_part = types.Part.from_bytes(data=file_bytes, mime_type=mime_type)
        response = client.models.generate_content(
            model=model_name,
            contents=[correction_prompt, file_part],
            config={"temperature": 0.0, "max_output_tokens": 65536, "response_mime_type": "application/json"},
        )
        if not response.text:
            return None
        try:
            new_result = json.loads(response.text)
        except (json.JSONDecodeError, TypeError):
            new_result = extract_json_from_response(response.text)
        new_items  = new_result.get('items', [])
        if not new_items:
            return None
        new_parts  = sum(safe_int(it.get('parts_amount', 0)) for it in new_items)
        new_wage   = sum(safe_int(it.get('wage', 0))         for it in new_items)
        old_error  = abs(parts_diff) + abs(wage_diff)
        new_error  = abs(new_parts - target_parts) + abs(new_wage - target_wage)
        if new_error < old_error:
            return new_result  # 改善された → 採用
        return None  # 改善なし
    except Exception as e:
        import sys
        print(f"[WARN] _self_correction_retry 例外: {e}", file=sys.stderr)
        return None


def analyze_estimate(api_key, file_bytes, mime_type, model_name=None,
                     use_fax_filter=False, use_rasterize=False, use_enhance=True):
    """
    見積書をAI-OCRで解析するメイン関数。
    新機能:
      use_fax_filter: FAXページを自動除外する（追加APIコール1回）
      use_rasterize: PDF→JPEG変換してから送信（行ズレ防止）
    """
    used_model = model_name or GEMINI_MODEL

    # ① FAXページフィルタリング（オプション）
    filtered_count = 0
    if use_fax_filter and mime_type == 'application/pdf':
        original_size = len(file_bytes)
        file_bytes    = filter_fax_pages(api_key, file_bytes, used_model)
        if len(file_bytes) < original_size:
            filtered_count = 1

    # ② 横向きPDF補正
    if mime_type == 'application/pdf':
        file_bytes = try_fix_landscape_pdf(file_bytes)

    # ③ ページ分割
    pages = try_split_pdf_pages(file_bytes) if mime_type == 'application/pdf' else None
    # ③-a ページ順序自動補正（FAXヘッダ等で逆順になっている場合を修正）
    if pages and len(pages) > 1:
        pages = detect_and_reorder_pages(pages)

    # ③-b ラスタライズ: PDF→JPEG変換（行ズレ防止）
    # 1パス目用: 合計欄が最終ページにある場合を考慮し、最終ページをラスタライズ
    raster_bytes = file_bytes
    raster_mime  = mime_type
    if use_rasterize and mime_type == 'application/pdf':
        try:
            from pypdf import PdfReader
            num_pages = len(PdfReader(io.BytesIO(file_bytes)).pages)
        except Exception:
            num_pages = 1
        # 最終ページをラスタライズ（合計欄は通常最終ページにある）
        last_page_idx = max(0, num_pages - 1)
        img = rasterize_pdf_page(file_bytes, last_page_idx, dpi=250, enhance=use_enhance)
        if img:
            raster_bytes = img
            raster_mime  = 'image/jpeg'

    # ③-c 1ページ目もラスタライズ（車両情報ヘッダ読み取り用）
    first_raster_bytes = file_bytes
    first_raster_mime  = mime_type
    if use_rasterize and mime_type == 'application/pdf':
        img1 = rasterize_pdf_page(file_bytes, 0, dpi=250, enhance=use_enhance)
        if img1:
            first_raster_bytes = img1
            first_raster_mime  = 'image/jpeg'

    # ④ 1パス目: 合計値＋車両情報抽出
    # 合計欄は最終ページ、車両情報は1ページ目にあることが多い
    # 単一ページ or 1ページ目=最終ページ の場合はそのまま
    totals_data = analyze_estimate_totals(api_key, raster_bytes, raster_mime, used_model) or {}
    # 複数ページで1ページ目≠最終ページの場合、1ページ目から車両情報を別途取得
    if pages and len(pages) > 1 and first_raster_bytes != raster_bytes:
        first_page_data = analyze_estimate_totals(api_key, first_raster_bytes, first_raster_mime, used_model) or {}
        # 車両情報は1ページ目の結果を優先
        vinfo_first = first_page_data.get('vehicle_info', {})
        vinfo_last  = totals_data.get('vehicle_info', {})
        merged_vinfo = {k: (vinfo_first.get(k) or vinfo_last.get(k, '')) for k in
                        set(list(vinfo_first.keys()) + list(vinfo_last.keys()))}
        totals_data['vehicle_info'] = merged_vinfo
        # 税区分判定: 最終ページ不明の場合、1ページ目の判定を優先採用
        # 例: 「内消費税」「(税込)」表記は1ページ目にある場合が多い
        last_basis  = totals_data.get('amount_basis', 'unknown')
        first_basis = first_page_data.get('amount_basis', 'unknown')
        if last_basis not in ('tax_inclusive', 'tax_exclusive') and first_basis in ('tax_inclusive', 'tax_exclusive'):
            totals_data['amount_basis'] = first_basis
            totals_data['tax_reason']   = first_page_data.get('tax_reason', totals_data.get('tax_reason', ''))
        # 合計値の補完: 最終ページに合計がない場合（pdf_grand_total=0）、1ページ目の値を使用
        # 例: Honda Cars系フォーマット（合計がページ1ヘッダのサマリーボックスに記載）
        last_grand = safe_int(totals_data.get('pdf_grand_total', 0))
        if last_grand == 0:
            first_grand = safe_int(first_page_data.get('pdf_grand_total', 0))
            if first_grand > 0:
                totals_data['pdf_grand_total'] = first_grand
                # 部品合計・工賃合計・値引きも1ページ目から補完（最終ページに0の場合のみ）
                if safe_int(totals_data.get('pdf_parts_total', 0)) == 0:
                    totals_data['pdf_parts_total'] = first_page_data.get('pdf_parts_total', 0)
                if safe_int(totals_data.get('pdf_wage_total', 0)) == 0:
                    totals_data['pdf_wage_total'] = first_page_data.get('pdf_wage_total', 0)
                if safe_int(totals_data.get('discount_amount', 0)) == 0:
                    totals_data['discount_amount'] = first_page_data.get('discount_amount', 0)
    target_parts = safe_int(totals_data.get('pdf_parts_total', 0))
    target_wage  = safe_int(totals_data.get('pdf_wage_total', 0))
    pdf_grand    = safe_int(totals_data.get('pdf_grand_total', 0))
    discount     = safe_int(totals_data.get('discount_amount', 0))

    # ⑤ 2パス目: 明細抽出
    if pages and len(pages) > 1:
        all_items   = []
        total_sp    = 0
        confidences = []
        # 各ページのラスタライズ前処理
        page_data = []
        for idx, page_bytes in enumerate(pages):
            send_bytes = page_bytes
            send_mime  = 'application/pdf'
            if use_rasterize:
                img = rasterize_pdf_page(page_bytes, 0, dpi=250, enhance=use_enhance)
                if img:
                    send_bytes = img
                    send_mime  = 'image/jpeg'
            page_data.append((idx, send_bytes, send_mime))
        # 全ページを並列でAPI呼び出し（高速化）
        def _analyze_page(args):
            idx, sb, sm = args
            try:
                return idx, analyze_estimate_single(
                    api_key, sb, sm, used_model, idx + 1, len(pages)
                ) or {}
            except Exception as e:
                # モデル廃止エラーは再送出して呼び出し元でエラー表示できるようにする
                err_msg = str(e)
                if 'no longer available' in err_msg or 'NOT_FOUND' in err_msg or 'モデル' in err_msg:
                    raise
                import sys
                print(f"[WARN] ページ{idx+1}の解析失敗: {err_msg}", file=sys.stderr)
                return idx, {'_error': err_msg}
        with ThreadPoolExecutor(max_workers=min(4, len(page_data))) as executor:
            results = list(executor.map(_analyze_page, page_data))
        # ページ順に結合
        results.sort(key=lambda x: x[0])
        page_amount_bases = []  # 各ページのGemini税区分判定を収集
        for idx, res in results:
            all_items.extend(res.get('items', []))
            total_sp += safe_int(res.get('short_parts_wage', 0))
            confidences.append(safe_float(res.get('confidence', 0.0)))
            ab = res.get('amount_basis', '')
            if ab in ('tax_inclusive', 'tax_exclusive'):
                page_amount_bases.append(ab)
        # ページ境界の重複行を除去
        all_items = deduplicate_page_items(all_items)
        # 各ページのGemini税判定を集約（tax_inclusiveが1つでもあれば採用）
        gemini_amount_basis = ''
        if page_amount_bases:
            if 'tax_inclusive' in page_amount_bases:
                gemini_amount_basis = 'tax_inclusive'
            else:
                from collections import Counter
                gemini_amount_basis = Counter(page_amount_bases).most_common(1)[0][0]
        # 1パス目の税判定も収集
        if not gemini_amount_basis:
            gemini_amount_basis = totals_data.get('amount_basis', '')
        result = {
            'items':                all_items,
            'short_parts_wage':     total_sp,
            'pdf_parts_total':      target_parts,
            'pdf_wage_total':       target_wage,
            'pdf_grand_total':      pdf_grand,
            'discount_amount':      discount,
            'confidence':           (sum(confidences) / len(confidences)) if confidences else 0.5,
            '_fax_filtered':        filtered_count,
            '_page_count':          len(pages),
            '_vehicle_info':        totals_data.get('vehicle_info', {}),
            '_repair_shop_name':    totals_data.get('repair_shop_name', ''),
            '_tax_reason':          totals_data.get('tax_reason', ''),
            '_gemini_amount_basis': gemini_amount_basis,
        }
    else:
        # 単一ページ: ラスタライズ済みがあればそちらを使用
        result = analyze_estimate_single(
            api_key, raster_bytes, raster_mime, used_model, 1, 1
        ) or {}
        result.setdefault('items', [])
        result.setdefault('short_parts_wage', 0)
        result['pdf_parts_total'] = target_parts or safe_int(result.get('pdf_parts_total', 0))
        result['pdf_wage_total']  = target_wage  or safe_int(result.get('pdf_wage_total', 0))
        result['pdf_grand_total'] = pdf_grand    or safe_int(result.get('pdf_grand_total', 0))
        result['discount_amount'] = discount     or safe_int(result.get('discount_amount', 0))
        result['confidence']      = safe_float(result.get('confidence', 0.5))
        result['_fax_filtered']   = filtered_count
        result['_vehicle_info']   = totals_data.get('vehicle_info', {})
        result['_repair_shop_name'] = totals_data.get('repair_shop_name', '')
        result['_tax_reason']     = totals_data.get('tax_reason', '')

    # ⑥ 辞書ベースバリデーション
    result['items'] = validate_and_correct_items(result['items'])

    # ⑥-b 明細行ごとの整合性チェック
    result['items'], row_warnings = validate_row_consistency(result['items'])
    if row_warnings:
        result['_row_warnings'] = row_warnings

    # ⑥-c ショートパーツ・預託金の明細行からの分離（二重計上防止）
    existing_sp = safe_int(result.get('short_parts_wage', 0))
    existing_exempt = safe_int(result.get('tax_exempt_amount', 0))
    result['items'], sp_total, exempt_total = extract_special_items(
        result['items'], existing_sp, existing_exempt
    )
    result['short_parts_wage'] = sp_total
    result['tax_exempt_amount'] = exempt_total

    # ⑦ 自己修復ループ（合計値が取得できた場合のみ、最大2回）
    if (result['pdf_parts_total'] > 0 or result['pdf_wage_total'] > 0):
        _correction_rounds = 0
        for _sc_round in range(2):
            _cur_items = result['items']
            _cur_parts = sum(safe_int(it.get('parts_amount', 0)) for it in _cur_items)
            _cur_wage  = sum(safe_int(it.get('wage', 0))         for it in _cur_items)
            _p_diff = abs(_cur_parts - result['pdf_parts_total'])
            _w_diff = abs(_cur_wage  - result['pdf_wage_total'])
            if _p_diff == 0 and _w_diff == 0:
                break  # 完全一致 → 修正不要
            retry = _self_correction_retry(
                api_key, raster_bytes, raster_mime, used_model,
                result['items'],
                result['pdf_parts_total'],
                result['pdf_wage_total'],
            )
            if retry and retry.get('items'):
                result['items']            = validate_and_correct_items(retry['items'])
                result['short_parts_wage'] = safe_int(retry.get('short_parts_wage', result.get('short_parts_wage', 0)))
                _correction_rounds += 1
            else:
                break  # 改善なし → 終了
        if _correction_rounds > 0:
            result['_self_corrected'] = True
            result['_correction_rounds'] = _correction_rounds

    # ⑧ 税込/税抜 自動判定
    summary = build_estimate_summary(
        result['items'],
        result.get('short_parts_wage', 0),
        result.get('pdf_parts_total', 0),
        result.get('pdf_wage_total', 0),
        result.get('pdf_grand_total', 0),
        result.get('discount_amount', 0),
        gemini_amount_basis=result.get('_gemini_amount_basis', ''),
    )
    result['_tax_basis']     = summary['basis']
    result['_reverse_match'] = summary['reverse_match']
    # tax_reason: Geminiが返した判定根拠を保持（UI表示用）
    if 'tax_reason' not in result or not result.get('tax_reason'):
        result['tax_reason'] = result.get('_thought_process', '')

    # ⑨ 税込明細の場合でもそのままの金額を維持する仕様に変更（TaxKindFlagで制御するため）
    # (以前は自動的に税抜変換していたが削除)
    if summary['basis'] == 'tax_inclusive':
        result['_tax_converted'] = False
        result['_is_tax_inclusive'] = True


    # ⑩ 値引きを負の工賃行として items に追加
    disc_outtax = summary.get('norm_disc', 0)
    if disc_outtax > 0:
        result['items'].append({
            'name':         '値引き',
            'method':       '値引き',
            'quantity':     1,
            'parts_amount': 0,
            'wage':         -disc_outtax,
        })

    # ⑪ STEP 3 最終バリデーション結果の生成（APIが返したものを優先、なければ再計算）
    final_items = [it for it in result['items'] if it.get('name') != '値引き']
    calc_p = sum(safe_int(it.get('parts_amount', 0)) for it in final_items)
    calc_w = sum(safe_int(it.get('wage', 0))         for it in final_items)
    doc_p  = safe_int(result.get('pdf_parts_total', 0))
    doc_w  = safe_int(result.get('pdf_wage_total', 0))
    p_diff = calc_p - doc_p
    w_diff = calc_w - doc_w
    is_match = (p_diff == 0 and w_diff == 0) or (doc_p == 0 and doc_w == 0)
    # Geminiが返したtotals_verificationがある場合はそちらを優先
    if not result.get('totals_verification'):
        result['totals_verification'] = {
            'calculated_parts_total': calc_p,
            'calculated_labor_total': calc_w,
            'document_parts_total':   doc_p,
            'document_labor_total':   doc_w,
            'parts_diff':             p_diff,
            'labor_diff':             w_diff,
            'is_match':               is_match,
            'validation_error':       None if is_match else f'部品差額{p_diff:+,}円・工賃差額{w_diff:+,}円',
        }

    return result


# ============================================================
# ファイル名生成
# ============================================================

def generate_filename(cust, calc_parts, calc_wages, pdf_parts, pdf_wages,
                      has_estimate, reverse_match=False, short_parts_wage=0):
    """
    登録番号から出力ファイル名を生成。
    reverse_match=True の場合は部品・工賃相違を抑制する。
    ショートパーツがPDF側の部品合計に含まれているケースも考慮して比較する。
    """
    dept   = safe_str(cust.get('car_reg_department', ''))
    div    = safe_str(cust.get('car_reg_division', ''))
    biz    = safe_str(cust.get('car_reg_business', ''))
    serial = safe_str(cust.get('car_reg_serial', ''))
    base   = f'{dept}{div}{biz}{serial}'
    if not base.strip():
        base = '新規見積'
    sp = safe_int(short_parts_wage)
    discrepancies = []
    if not reverse_match and has_estimate:
        # ショートパーツがPDF部品合計に含まれている場合も一致とみなす
        parts_match = (calc_parts == pdf_parts) or (calc_parts + sp == pdf_parts)
        if pdf_parts is not None and pdf_parts > 0 and not parts_match:
            discrepancies.append('部品相違')
        if pdf_wages is not None and pdf_wages > 0 and calc_wages != pdf_wages:
            discrepancies.append('工賃相違')
    if discrepancies:
        suffix = '（' + '・'.join(discrepancies) + '）'
    else:
        suffix = ''
    return f'{base}_見積{suffix}.neo'


# ============================================================
# Streamlit UI
# ============================================================

def main():
    st.set_page_config(
        page_title="NEO自動生成アプリ",
        page_icon="🚗",
        layout="wide",
        initial_sidebar_state="expanded"
    )
    st.markdown("""
    <style>
    *, *::before, *::after { box-sizing: border-box; }
    body { font-family: 'Segoe UI', 'Hiragino Sans', 'Meiryo', sans-serif; }

    /* Topbar */
    .topbar { background: #1a2744; color: #fff; padding: 0 24px; height: 52px;
              display: flex; align-items: center; justify-content: space-between;
              box-shadow: 0 2px 8px rgba(0,0,0,.25); border-radius: 8px; margin-bottom: 20px; }
    .topbar-title { font-size: 16px; font-weight: 700; letter-spacing: .04em;
                    display: flex; align-items: center; gap: 10px; }
    .topbar-badge { background: #3b82f6; font-size: 10px; padding: 2px 7px;
                    border-radius: 10px; font-weight: 600; }
    .topbar-right { display: flex; align-items: center; gap: 16px; font-size: 12px; color: #94a3b8; }
    .api-dot { width: 8px; height: 8px; border-radius: 50%; display: inline-block; margin-right: 4px; vertical-align: middle; }

    /* Step bar */
    .step-bar { display: flex; align-items: center; background: #fff; border-radius: 10px;
                padding: 16px 24px; margin-bottom: 20px; box-shadow: 0 1px 4px rgba(0,0,0,.07); }
    .step-item { display: flex; align-items: center; gap: 10px; }
    .step-circle { width: 32px; height: 32px; border-radius: 50%; display: inline-flex;
                   align-items: center; justify-content: center; font-weight: 700; font-size: 13px; flex-shrink: 0; }
    .step-circle-done { background: #22c55e; color: #fff; }
    .step-circle-active { background: #1d4ed8; color: #fff; box-shadow: 0 0 0 4px #bfdbfe; }
    .step-circle-pending { background: #e2e8f0; color: #94a3b8; }
    .step-label-active { font-size: 12px; font-weight: 600; color: #1d4ed8; }
    .step-label-done { font-size: 12px; font-weight: 600; color: #15803d; }
    .step-label-pending { font-size: 12px; font-weight: 600; color: #94a3b8; }
    .step-connector { flex: 1; height: 2px; background: #e2e8f0; margin: 0 8px; min-width: 20px; }
    .step-connector-done { background: #22c55e; }

    /* Mode selector */
    .mode-selector { display: flex; gap: 8px; margin-bottom: 16px; }
    .mode-btn { flex: 1; padding: 12px 16px; border: 2px solid #e2e8f0; border-radius: 8px;
                background: #fff; text-align: center; }
    .mode-btn-active { border-color: #1d4ed8; background: #eff6ff; }
    .mode-icon { font-size: 22px; display: block; margin-bottom: 4px; }
    .mode-label { font-size: 13px; font-weight: 700; color: #1e293b; }
    .mode-label-active { color: #1d4ed8; }
    .mode-desc { font-size: 11px; color: #94a3b8; margin-top: 2px; }

    /* Vehicle strip */
    .vehicle-strip { background: linear-gradient(135deg, #1a2744 0%, #1e3a5f 100%); color: #fff;
                     border-radius: 10px; padding: 16px 20px; margin-bottom: 16px;
                     display: flex; align-items: flex-start; gap: 16px; }
    .vehicle-strip-name { font-size: 18px; font-weight: 700; }
    .vehicle-strip-detail { font-size: 12px; color: #94a3b8; margin-top: 2px; }
    .vehicle-strip-badges { display: flex; gap: 6px; margin-top: 6px; flex-wrap: wrap; }

    /* Total strip */
    .total-strip { background: #1a2744; color: #fff; border-radius: 10px; padding: 16px 24px;
                   display: flex; align-items: center; gap: 20px; margin-top: 16px; flex-wrap: wrap; }
    .total-item { text-align: center; }
    .total-label { font-size: 10px; color: #94a3b8; font-weight: 600; letter-spacing: .05em; }
    .total-value { font-size: 18px; font-weight: 700; }
    .total-value-highlight { font-size: 22px; font-weight: 700; color: #fbbf24; }
    .total-sep { color: #334155; font-size: 18px; }

    /* Badges */
    .badge-green  { background: #dcfce7; color: #15803d; padding: 2px 8px; border-radius: 10px; font-size: 11px; font-weight: 600; }
    .badge-blue   { background: #dbeafe; color: #1d4ed8; padding: 2px 8px; border-radius: 10px; font-size: 11px; font-weight: 600; }
    .badge-orange { background: #ffedd5; color: #c2410c; padding: 2px 8px; border-radius: 10px; font-size: 11px; font-weight: 600; }
    .badge-red    { background: #fee2e2; color: #b91c1c; padding: 2px 8px; border-radius: 10px; font-size: 11px; font-weight: 600; }
    .badge-gray   { background: #f1f5f9; color: #475569; padding: 2px 8px; border-radius: 10px; font-size: 11px; font-weight: 600; }
    .badge-purple { background: #f3e8ff; color: #7e22ce; padding: 2px 8px; border-radius: 10px; font-size: 11px; font-weight: 600; }

    /* Alert boxes */
    .alert { border-radius: 8px; padding: 12px 16px; margin-bottom: 12px; font-size: 13px; }
    .alert-info    { background: #eff6ff; border: 1px solid #bfdbfe; color: #1d4ed8; }
    .alert-warn    { background: #fffbeb; border: 1px solid #fde68a; color: #92400e; }
    .alert-success { background: #f0fdf4; border: 1px solid #bbf7d0; color: #15803d; }
    .alert-error   { background: #fef2f2; border: 1px solid #fca5a5; color: #991b1b; }

    /* Mismatch banner */
    .mismatch-banner { background: #fef2f2; border: 1px solid #fca5a5; border-radius: 10px; padding: 16px; margin-bottom: 16px; }
    .mismatch-title  { font-weight: 700; color: #991b1b; font-size: 14px; margin-bottom: 4px; }
    .mismatch-body   { font-size: 12px; color: #7f1d1d; line-height: 1.6; margin-bottom: 8px; }

    /* DB status */
    .db-status-item { font-size: 11px; color: #475569; line-height: 1.8; }
    .db-dot-green { color: #22c55e; }
    .db-dot-yellow { color: #f59e0b; }

    /* Section title */
    .section-title { font-size: 13px; font-weight: 700; color: #334155; margin-bottom: 12px;
                     padding-bottom: 8px; border-bottom: 1px solid #f1f5f9; display: flex; align-items: center; gap: 8px; }

    /* Legacy classes (keep for backward compat) */
    .main-title   { font-size: 1.8rem; font-weight: bold; color: #1a5276; margin-bottom: 0.5rem; }
    .step-header  { font-size: 1.3rem; font-weight: bold; color: #2c3e50; padding: 0.5rem 0; border-bottom: 2px solid #3498db; margin-bottom: 1rem; }
    .success-box  { background: #d4edda; border: 1px solid #c3e6cb; border-radius: 8px; padding: 1rem; margin: 0.5rem 0; }
    .warning-box  { background: #fff3cd; border: 1px solid #ffeaa7; border-radius: 8px; padding: 1rem; margin: 0.5rem 0; }
    .error-box    { background: #f8d7da; border: 1px solid #f5c6cb; border-radius: 8px; padding: 1rem; margin: 0.5rem 0; }
    .info-box     { background: #d1ecf1; border: 1px solid #bee5eb; border-radius: 8px; padding: 1rem; margin: 0.5rem 0; }
    .tax-box      { background: #e8f5e9; border: 1px solid #a5d6a7; border-radius: 8px; padding: 0.8rem; margin: 0.5rem 0; font-size: 0.9rem; }

    /* File uploader */
    [data-testid="stFileUploader"] {
        border: 2px dashed #cbd5e1 !important;
        border-radius: 10px !important;
        padding: 12px !important;
        background-color: #f8fafc !important;
    }
    [data-testid="stFileUploader"]:hover {
        border-color: #3b82f6 !important;
        background-color: #eff6ff !important;
    }
    </style>
    """, unsafe_allow_html=True)

    # テンプレートチェック
    if not os.path.exists(TEMPLATE_PATH):
        st.error(
            f"⚠️ テンプレートファイルが見つかりません: {TEMPLATE_FILENAME}\n\n"
            f"app.py と同じフォルダに「{TEMPLATE_FILENAME}」を配置してください。"
        )
        st.stop()
    with open(TEMPLATE_PATH, 'rb') as f:
        template_data = f.read()

    # ─── サイドバー ───────────────────────────────────
    with st.sidebar:
        # ── メニュー ──
        st.markdown('<div style="font-size:10px;font-weight:700;color:#94a3b8;letter-spacing:.08em;text-transform:uppercase;padding:8px 0 4px">メニュー</div>', unsafe_allow_html=True)
        st.markdown('🏠 **ホーム**')
        st.markdown('<div style="background:#eff6ff;color:#1d4ed8;padding:6px 10px;border-radius:6px;font-size:13px;font-weight:600;margin-bottom:2px">📝 新規作成</div>', unsafe_allow_html=True)
        st.markdown('📂 作成履歴（準備中）')
        st.markdown("---")

        # ── 設定 ──
        st.markdown('<div style="font-size:10px;font-weight:700;color:#94a3b8;letter-spacing:.08em;text-transform:uppercase;padding:4px 0">設定</div>', unsafe_allow_html=True)
        st.header("🔑 APIキー設定")
        if GEMINI_API_KEY:
            api_key = GEMINI_API_KEY
            st.success("APIキー: 設定済み (.env)")
        else:
            api_key = st.text_input(
                "Gemini APIキー",
                type="password",
                help=".envファイルの GEMINI_API_KEY にキーを設定すれば毎回入力不要"
            )
        # 利用可能なモデルをAPIで動的取得（APIキーがある場合のみ）
        if api_key:
            with st.spinner("利用可能なモデルを確認中..."):
                _avail_models = get_available_gemini_models(api_key)
        else:
            _avail_models = [_FALLBACK_MODEL]
        selected_model = st.selectbox(
            "🤖 AIモデル",
            options=_avail_models,
            index=0,
            key="model_selector_v2",
            help="APIで利用可能なモデルを自動検出。3.1 Pro=最高精度、2.5 Flash=高速・コスパ良好"
        )
        st.markdown("---")
        st.markdown("**🗂 DBパス設定**")
        addata_status = find_addata_dir()
        if addata_status:
            st.success(f"Addata検出済み")
            st.caption(addata_status)
        else:
            st.warning("Addataフォルダ未検出")
        st.markdown("---")
        st.header("🔬 精度オプション")
        use_fax_filter = st.checkbox(
            "FAXページ自動除外",
            value=False,
            help="FAX送付状が混在するPDFの1ページ目を自動検出・除外します。APIコールが1回増えます。"
        )
        use_rasterize = st.checkbox(
            "PDF→画像変換（行ズレ防止）",
            value=True,
            help="PDFをJPEG画像に変換してからAIに送ります。テキストレイヤーの行ズレ問題を防ぎます。デフォルト有効。"
        )
        use_enhance = st.checkbox(
            "画像前処理（FAX品質改善）",
            value=True,
            help="コントラスト・シャープネスを強化してFAX品質の画像を読みやすくします。ラスタライズ有効時のみ機能します。"
        )
        st.markdown("---")
        st.header("🛡️ 保険情報")
        policy_no       = st.text_input("証券番号",  value=st.session_state.get('policy_no', ''))
        contractor_name = st.text_input("契約者名", value=st.session_state.get('contractor_name', ''))
        st.session_state['policy_no']       = policy_no
        st.session_state['contractor_name'] = contractor_name
        st.markdown("---")
        st.header("💰 費用（Expense）")
        exp_towing    = st.number_input("レッカー費用（税抜）",  value=st.session_state.get('exp_towing', 0),    min_value=0, step=1000, key='exp_towing_input')
        exp_rental    = st.number_input("代車費用（税抜）",      value=st.session_state.get('exp_rental', 0),    min_value=0, step=1000, key='exp_rental_input')
        exp_exempt    = st.number_input("非課税費用",            value=st.session_state.get('exp_exempt', 0),    min_value=0, step=1000, key='exp_exempt_input')
        st.session_state['exp_towing'] = exp_towing
        st.session_state['exp_rental'] = exp_rental
        st.session_state['exp_exempt'] = exp_exempt
        st.markdown("---")
        st.markdown('<div style="font-size:10px;font-weight:700;color:#94a3b8;letter-spacing:.08em;text-transform:uppercase;padding:4px 0">DB状態</div>', unsafe_allow_html=True)
        _addata_dir_check = find_addata_dir()
        _ka06_exists = False
        _parts_count_approx = "—"
        if _addata_dir_check:
            _ka06_path = find_ka06_path(_addata_dir_check)
            _ka06_exists = _ka06_path is not None and os.path.exists(_ka06_path)
            if _ka06_exists:
                try:
                    _ka06_size = os.path.getsize(_ka06_path)
                    _vehicle_count = _ka06_size // 32  # 概算
                    _parts_count_approx = f"〜{_vehicle_count:,}件"
                except Exception:
                    pass
        dot_g = '<span style="color:#22c55e">●</span>'
        dot_y = '<span style="color:#f59e0b">●</span>'
        ka06_dot = dot_g if _ka06_exists else dot_y
        addata_dot = dot_g if _addata_dir_check else dot_y
        st.markdown(f"""
        <div style="font-size:11px;color:#475569;line-height:2">
            {ka06_dot} vehicle_index (KA06)<br>
            {addata_dot} Addataフォルダ<br>
            {dot_y} grade_codes: —<br>
        </div>
        """, unsafe_allow_html=True)
        st.markdown("---")
        st.caption(f"消費税率: {int(TAX_RATE * 100)}%（固定）")
        st.caption(f"見積日: {datetime.datetime.now().strftime('%Y/%m/%d')}（自動）")

    # セッション状態初期化
    for key, default in [
        ('step', 1), ('vehicle_data', None), ('estimate_data', None),
        ('neo_bytes', None), ('neo_filename', None)
    ]:
        if key not in st.session_state:
            st.session_state[key] = default

    current_step = st.session_state['step']

    # ── Topbar ──
    api_dot_color = "#22c55e" if api_key else "#ef4444"
    api_status_text = "接続中" if api_key else "未設定"
    st.markdown(f"""
    <div class="topbar">
        <div class="topbar-title">
            🚗 SHOUCHIKU8 — NEO自動生成
            <span class="topbar-badge">v4.0</span>
        </div>
        <div class="topbar-right">
            <span><span class="api-dot" style="background:{api_dot_color}"></span>Gemini API {api_status_text}</span>
            <span>|</span>
            <span>モデル: {selected_model}</span>
        </div>
    </div>
    """, unsafe_allow_html=True)

    # ── Step progress bar ──
    step_labels = ["① アップロード", "② AI解析", "③ プレビュー・修正", "④ NEO生成"]
    step_html = '<div class="step-bar">'
    for i, label in enumerate(step_labels):
        sn = i + 1
        if sn < current_step:
            c_cls = "step-circle step-circle-done"
            c_txt = "✓"
            l_cls = "step-label-done"
        elif sn == current_step:
            c_cls = "step-circle step-circle-active"
            c_txt = str(sn)
            l_cls = "step-label-active"
        else:
            c_cls = "step-circle step-circle-pending"
            c_txt = str(sn)
            l_cls = "step-label-pending"
        step_html += f'<div class="step-item"><div class="{c_cls}">{c_txt}</div><span class="{l_cls}" style="font-size:12px;font-weight:600;margin-left:8px">{label}</span></div>'
        if i < len(step_labels) - 1:
            conn_cls = "step-connector step-connector-done" if sn < current_step else "step-connector"
            step_html += f'<div class="{conn_cls}"></div>'
    step_html += '</div>'
    st.markdown(step_html, unsafe_allow_html=True)

    # =========================================
    # STEP 1: アップロード
    # =========================================
    if current_step == 1:
        # ── モード選択（st.radio で実装） ──
        st.markdown("""
        <style>
        div[data-testid="stRadio"] > label { display: none; }
        div[data-testid="stRadio"] > div { display: flex; gap: 12px; }
        div[data-testid="stRadio"] > div > label {
            flex: 1; border: 2px solid #e2e8f0; border-radius: 8px;
            padding: 14px 16px; background: #fff; cursor: pointer;
            display: flex; flex-direction: column; align-items: center; text-align: center;
        }
        div[data-testid="stRadio"] > div > label:has(input:checked) {
            border-color: #1d4ed8; background: #eff6ff;
        }
        /* DBマッチングモードをグレーアウト（現在エラーにより使用停止中） */
        div[data-testid="stRadio"] > div > label:first-child {
            opacity: 0.35;
            pointer-events: none;
            cursor: not-allowed !important;
            background: #f8fafc !important;
            border-color: #cbd5e1 !important;
            color: #94a3b8 !important;
        }
        </style>
        """, unsafe_allow_html=True)
        mode = st.radio(
            "動作モード",
            options=["🤖 DBマッチングモード（コグニセブンDBと照合して部品コード・作業コードを確定）",
                     "✏️ ベタ打ちモード（見積内容をそのままNEOファイルに転記）"],
            index=1,
            horizontal=True,
            label_visibility="collapsed",
            key="mode_radio"
        )
        # DBマッチングモードは現在停止中 → 常にベタ打ちモードを使用
        st.session_state['selected_mode'] = 'beta'
        mode_val = 'beta'

        # モード状態バッジ
        st.markdown('<div style="background:#f1f5f9;border:1px solid #e2e8f0;border-radius:8px;padding:10px 14px;font-size:13px;margin-bottom:12px">✏️ <b>ベタ打ちモード選択中</b> — 見積内容をそのままNEOファイルに転記します</div>', unsafe_allow_html=True)

        # ── アップロードカード ──
        col1, col2 = st.columns(2)
        with col1:
            st.markdown('<div class="section-title">📋 車検証</div>', unsafe_allow_html=True)
            vehicle_file = st.file_uploader(
                "車検証をアップロード（PDF・JPG・PNG 対応）",
                type=['pdf', 'jpg', 'jpeg', 'png', 'webp', 'bmp', 'tiff', 'tif', 'heic', 'heif'],
                key='vehicle_upload',
            )
            if vehicle_file:
                st.success(f"✅ {vehicle_file.name} ({vehicle_file.size:,} bytes)")
                st.caption("🔍 OCR対象: 型式・型式指定番号・類別区分番号・エンジン型式・使用者情報")
        with col2:
            st.markdown('<div class="section-title">🧾 見積書</div>', unsafe_allow_html=True)
            estimate_file = st.file_uploader(
                "見積書をアップロード（PDF・JPG・PNG 対応、FAX品質可）",
                type=['pdf', 'jpg', 'jpeg', 'png', 'webp', 'bmp', 'tiff', 'tif', 'heic', 'heif'],
                key='estimate_upload',
            )
            if estimate_file:
                st.success(f"✅ {estimate_file.name} ({estimate_file.size:,} bytes)")
                st.caption("🔍 OCR対象: 部品名・部品番号・単価・工賃・塗装・その他費用 全明細")
            else:
                st.info("💡 見積書なしの場合、車両情報のみのNEOを作成します")

        # ── テンプレートNEOアップロード（任意） ──
        with st.expander("📁 テンプレートNEOファイル（任意）", expanded=False):
            st.markdown(
                '<div style="background:#fffbeb;border:1px solid #fbbf24;border-radius:8px;padding:10px 14px;font-size:13px;margin-bottom:10px">'
                '💡 <b>証券番号・工場名・車両情報など</b>が入力済みのNEOファイルをテンプレートとして使用できます。<br>'
                '車検証OCRで取得した情報と照合し、<b>誤記入を自動訂正</b>した上で<b>明細欄をPDF解析結果でベタ打ち</b>します。<br>'
                'テンプレートにしか存在しない情報（工場名・証券番号など）はそのまま保持されます。'
                '</div>',
                unsafe_allow_html=True
            )
            custom_neo_file = st.file_uploader(
                "テンプレートNEOファイルをアップロード",
                type=['neo'],
                key='custom_neo_upload',
                help="コグニセブンで作成した.neoファイル。証券番号・工場名・車両情報等が入力済みのものを使用してください。"
            )
            if custom_neo_file:
                st.success(f"✅ {custom_neo_file.name} ({custom_neo_file.size:,} bytes)")
                st.caption("📋 車検証OCRで誤記入を訂正し、テンプレートの工場名・証券番号等はそのまま引き継ぎます")
            else:
                st.info(f"未選択の場合はデフォルトテンプレート（{TEMPLATE_FILENAME}）を使用します")

        # ── オプション設定 ──
        with st.expander("⚙️ オプション設定", expanded=False):
            opt_col1, opt_col2, opt_col3 = st.columns(3)
            with opt_col1:
                policy_no_step1 = st.text_input("保険会社", placeholder="例: 東京海上日動", key="ins_company_step1")
            with opt_col2:
                policy_no_step1b = st.text_input("証券番号", placeholder="例: TK-12345678", key="ins_policy_step1")
            with opt_col3:
                assignee_step1 = st.text_input("担当者名", placeholder="例: 田中 花子", key="assignee_step1")

        st.markdown("")
        if vehicle_file:
            if st.button("🚀 AI解析を開始 →", type="primary", use_container_width=True):
                if not api_key:
                    st.error("⚠️ APIキーが未設定です。サイドバーで入力するか、app.py冒頭の GEMINI_API_KEY に貼り付けてください。")
                else:
                    st.session_state['vehicle_file_bytes'] = vehicle_file.read()
                    st.session_state['vehicle_file_name']  = vehicle_file.name
                    if estimate_file:
                        st.session_state['estimate_file_bytes'] = estimate_file.read()
                        st.session_state['estimate_file_name']  = estimate_file.name
                    else:
                        st.session_state['estimate_file_bytes'] = None
                        st.session_state['estimate_file_name']  = None
                    st.session_state['use_fax_filter'] = use_fax_filter
                    st.session_state['use_rasterize']  = use_rasterize
                    st.session_state['use_enhance']    = use_enhance
                    st.session_state['selected_model'] = selected_model
                    st.session_state['step'] = 2
                    st.rerun()
        else:
            st.warning("車検証ファイルをアップロードしてください")

    # =========================================
    # STEP 2: AI解析
    # =========================================
    elif current_step == 2:
        st.markdown('<div class="step-header">② AI解析中...</div>', unsafe_allow_html=True)
        vehicle_bytes  = st.session_state.get('vehicle_file_bytes')
        vehicle_name   = st.session_state.get('vehicle_file_name', '')
        estimate_bytes = st.session_state.get('estimate_file_bytes')
        estimate_name  = st.session_state.get('estimate_file_name', '')
        _use_fax       = st.session_state.get('use_fax_filter', False)
        _use_raster    = st.session_state.get('use_rasterize', True)   # デフォルトTrue（UIと一致）
        _use_enhance   = st.session_state.get('use_enhance', True)
        _model         = st.session_state.get('selected_model', GEMINI_MODEL)

        if vehicle_bytes is None:
            st.error("車検証データが見つかりません。ステップ①に戻ってください。")
            if st.button("← ステップ①に戻る"):
                st.session_state['step'] = 1
                st.rerun()
            st.stop()

        progress = st.progress(0, text="AI解析を開始しています...")
        try:
            vehicle_mime  = get_mime_type(vehicle_name)
            estimate_mime = get_mime_type(estimate_name) if estimate_bytes else None

            # 車検証＋見積書を並列で解析（高速化）
            if estimate_bytes:
                progress.progress(10, text="🔍 車検証＋見積書を同時解析中...")
                with ThreadPoolExecutor(max_workers=2) as executor:
                    fut_vehicle = executor.submit(
                        analyze_vehicle_registration, api_key, vehicle_bytes, vehicle_mime
                    )
                    fut_estimate = executor.submit(
                        analyze_estimate, api_key, estimate_bytes, estimate_mime, _model,
                        _use_fax, _use_raster, _use_enhance
                    )
                    vehicle_data  = fut_vehicle.result()
                    progress.progress(50, text="✅ 車検証の解析完了、見積書を処理中...")
                    estimate_data = fut_estimate.result() or {}
            else:
                progress.progress(10, text="🔍 車検証を解析中...")
                vehicle_data  = analyze_vehicle_registration(api_key, vehicle_bytes, vehicle_mime)
                estimate_data = None

            st.session_state['vehicle_data'] = vehicle_data
            progress.progress(60, text="✅ 解析完了")

            v_conf = safe_float(vehicle_data.get('confidence', 1.0), 1.0)
            if v_conf < CONFIDENCE_THRESHOLD:
                st.warning(f"⚠️ 車検証の読み取り信頼度が低いです（{v_conf:.0%}）。プレビュー画面で内容をご確認ください。")

            # 見積書の後処理
            if estimate_data:
                # 部品名を半角カタカナに変換
                for item in estimate_data.get('items', []):
                    if item.get('name'):
                        item['name'] = to_halfwidth_katakana(item['name'])

                # 見積書ヘッダの車両情報で車検証データの空欄を補完
                est_vinfo = estimate_data.get('_vehicle_info', {})
                if est_vinfo and vehicle_data:
                    MERGE_MAP = {
                        'car_name':      'car_name',
                        'car_model':     'car_model',
                        'engine_model':  'engine_model',
                        'color_code':    'color_code',
                        'color_name':    'body_color',
                        'trim_code':     'trim_code',
                        'grade':         'grade',
                        'chassis_no':    'car_serial_no',
                        'mileage':       'kilometer',
                    }
                    supplemented = []
                    for est_key, veh_key in MERGE_MAP.items():
                        est_val = est_vinfo.get(est_key, '')
                        if est_val and not vehicle_data.get(veh_key):
                            vehicle_data[veh_key] = est_val
                            supplemented.append(veh_key)
                    if supplemented:
                        st.session_state['vehicle_data'] = vehicle_data
                        st.info(f"📋 見積書から車両情報を補完: {', '.join(supplemented)}")

                st.session_state['estimate_data'] = estimate_data
                progress.progress(90, text="✅ 見積書の解析完了")

                e_conf = safe_float(estimate_data.get('confidence', 1.0), 1.0)
                if e_conf < CONFIDENCE_THRESHOLD:
                    st.warning(f"⚠️ 見積書の読み取り信頼度が低いです（{e_conf:.0%}）。プレビュー画面で内容をご確認ください。")

                # --- 11. Addata 連携 (車両特定 & 部品マッチング) ---
                _current_mode = st.session_state.get('selected_mode', 'db')
                addata_dir = find_addata_dir()
                if _current_mode == 'db' and addata_dir and vehicle_data:
                    progress.progress(92, text="Addata マスタとの照合を実行中...")
                    veh_match_result = identify_vehicle(addata_dir, vehicle_data)
                    estimate_data['_veh_match_result'] = veh_match_result

                    if veh_match_result.get('is_supported'):
                        a_folder = veh_match_result.get('addata_folder')
                        if 'items' in estimate_data and estimate_data['items']:
                            matched_items, has_rev = match_parts_with_addata(estimate_data['items'], a_folder)
                            estimate_data['items'] = matched_items
                            estimate_data['_reverse_match'] = has_rev
                elif _current_mode == 'beta':
                    # ベタ打ちモード: Addata照合をスキップし、PDF見積の内容をそのまま転記
                    estimate_data['_veh_match_result'] = {'match_layer': 3, 'is_supported': False, 'reason': 'ベタ打ちモード（DB照合スキップ）'}
                    progress.progress(92, text="✏️ ベタ打ちモード — PDF見積をそのまま転記...")
                
                # --- セッションステートへの保存 ---
                st.session_state['estimate_data'] = estimate_data

                # 精度処理の結果を表示
                info_msgs = []
                if _current_mode == 'beta':
                    info_msgs.append("✏️ ベタ打ちモード: PDF見積の全明細をそのままNEOファイルに転記します（DB照合なし）")
                elif estimate_data.get('_veh_match_result', {}).get('is_supported'):
                    v_res = estimate_data['_veh_match_result']
                    info_msgs.append(f"🚙 Addata マスタ連携成功: レイヤー{v_res['match_layer']} 一致 (車種コード: {v_res.get('vehicle_code')})")
                else:
                    info_msgs.append("⚠️ Addata マスタ連携: 該当車種が見つかりませんでした (手動入力モード)")
                    # フォールバック処理 (Geminiで車種名とエンジン型式を推測)
                    if vehicle_data.get('car_model'):
                        c_name = vehicle_data.get('car_name', '')
                        e_model = vehicle_data.get('engine_model', '')
                        if not c_name or not e_model:
                            progress.progress(95, text="🌐 Gemini: 不明な車両情報を検索補完中...")
                            comp = complement_vehicle_info_with_gemini(
                                api_key,
                                vehicle_data['car_model'],
                                c_name,
                                e_model
                            )
                            if comp.get('car_name'):
                                vehicle_data['car_name'] = comp['car_name']
                                info_msgs.append(f"🌐 車種名をWebから補完: {comp['car_name']}")
                            if comp.get('engine_model'):
                                vehicle_data['engine_model'] = comp['engine_model']
                                info_msgs.append(f"🌐 エンジン型式をWebから補完: {comp['engine_model']}")
                            st.session_state['vehicle_data'] = vehicle_data

                # 修理工場名の表示
                shop_name = estimate_data.get('_repair_shop_name', '')
                if shop_name:
                    info_msgs.append(f"🏭 修理工場: {shop_name}")
                # 税判定理由の表示
                tax_reason = estimate_data.get('_tax_reason', '')
                if tax_reason:
                    info_msgs.append(f"💱 税区分判定根拠: {tax_reason}")
                if estimate_data.get('_fax_filtered', 0) > 0:
                    info_msgs.append("🗑️ FAX送付状を自動除外しました")
                if estimate_data.get('_self_corrected'):
                    info_msgs.append("🔧 自己修復ループが有効になりました")
                page_count = estimate_data.get('_page_count', 1)
                if page_count > 1:
                    info_msgs.append(f"📄 {page_count}ページ分割処理（重複除去済み）")
                tax_basis = estimate_data.get('_tax_basis', 'unknown')
                if _current_mode == 'beta':
                    if tax_basis == 'tax_inclusive':
                        info_msgs.append("💱 税込明細を検出 → NEOファイルも税込モードで生成します")
                    elif tax_basis == 'tax_exclusive':
                        info_msgs.append("✅ 税抜明細を検出 → NEOファイルも税抜モードで生成します")
                else:
                    if tax_basis == 'tax_inclusive':
                        info_msgs.append("💱 税込明細を検出 → 税抜に自動変換しました")
                    elif tax_basis == 'tax_exclusive':
                        info_msgs.append("✅ 税抜明細を検出")
                # 明細行整合性チェックの警告表示
                row_warnings = estimate_data.get('_row_warnings', [])
                if row_warnings:
                    info_msgs.append(f"🔍 明細行整合性チェック: {len(row_warnings)}件の注意事項")
                if info_msgs:
                    for msg in info_msgs:
                        st.info(msg)
                if row_warnings:
                    with st.expander(f"⚠️ 整合性チェック詳細（{len(row_warnings)}件）", expanded=False):
                        for w in row_warnings:
                            st.warning(w)
            else:
                st.session_state['estimate_data'] = None
                progress.progress(90, text="（見積書なし）")

            progress.progress(100, text="✅ 解析完了！")
            st.session_state['step'] = 3
            st.rerun()
        except Exception as e:
            progress.empty()
            st.error(f"⚠️ AI解析中にエラーが発生しました:\n\n{str(e)}")
            st.code(traceback.format_exc())
            if st.button("← ステップ①に戻る"):
                st.session_state['step'] = 1
                st.rerun()

    # =========================================
    # STEP 3: プレビュー・修正
    # =========================================
    elif current_step == 3:
        vehicle_data  = st.session_state.get('vehicle_data', {})
        estimate_data = st.session_state.get('estimate_data')

        if not vehicle_data:
            st.error("解析データがありません。ステップ①に戻ってください。")
            if st.button("← ステップ①に戻る"):
                st.session_state['step'] = 1
                st.rerun()
            st.stop()

        # ── 車両ストリップ ──
        veh_match_result = estimate_data.get('_veh_match_result', {}) if estimate_data else {}
        match_is_db = veh_match_result.get('is_supported', False)
        car_name_strip = safe_str(vehicle_data.get('car_name', ''))
        car_model_strip = safe_str(vehicle_data.get('car_model', ''))
        engine_strip = safe_str(vehicle_data.get('engine_model', ''))
        reg_date_strip = safe_str(vehicle_data.get('car_reg_date', ''))
        reg_date_display = reg_date_strip[:7] if len(reg_date_strip) >= 6 else reg_date_strip
        km_strip = safe_int(vehicle_data.get('kilometer', 0))
        type_desig = safe_str(vehicle_data.get('car_model_designation', ''))
        cat_num = safe_str(vehicle_data.get('car_category_number', ''))
        v_code = veh_match_result.get('vehicle_code', '')
        match_mode_html = f'<span class="badge-blue">🗂 DBモード</span>' if match_is_db else '<span class="badge-gray">✏️ ベタ打ち</span>'
        items_count = len(estimate_data.get('items', [])) if estimate_data else 0
        match_ok_count = sum(1 for it in (estimate_data.get('items', []) if estimate_data else []) if it.get('_match_level', 99) <= 3)
        st.markdown(f"""
        <div class="vehicle-strip">
            <span style="font-size:32px">🚗</span>
            <div style="flex:1">
                <div class="vehicle-strip-name">{car_name_strip} <span style="font-size:14px;font-weight:400">{car_model_strip}</span></div>
                <div class="vehicle-strip-detail">{engine_strip} ／ {reg_date_display}登録 ／ {km_strip:,}km</div>
                <div class="vehicle-strip-badges">
                    {'<span class="badge-blue">型式指定 ' + type_desig + '</span>' if type_desig else ''}
                    {'<span class="badge-blue">類別 ' + cat_num + '</span>' if cat_num else ''}
                    {'<span class="badge-green">DBマッチ ✓ ' + v_code + '</span>' if match_is_db and v_code else ''}
                </div>
            </div>
            <div style="text-align:right">
                {match_mode_html}
                {'<div style="font-size:11px;color:#94a3b8;margin-top:4px">マッチ率 ' + str(match_ok_count) + '/' + str(items_count) + '件</div>' if items_count > 0 else ''}
            </div>
        </div>
        """, unsafe_allow_html=True)

        # 信頼度・税区分の警告
        v_conf = safe_float(vehicle_data.get('confidence', 1.0), 1.0)
        if v_conf < CONFIDENCE_THRESHOLD:
            st.markdown(f'<div class="alert alert-warn">⚠️ 車検証の読み取り信頼度: <b>{v_conf:.0%}</b> — 内容をよくご確認ください。</div>', unsafe_allow_html=True)
        if estimate_data:
            e_conf = safe_float(estimate_data.get('confidence', 1.0), 1.0)
            if e_conf < CONFIDENCE_THRESHOLD:
                st.markdown(f'<div class="alert alert-warn">⚠️ 見積書の読み取り信頼度: <b>{e_conf:.0%}</b> — 内容をよくご確認ください。</div>', unsafe_allow_html=True)
            tax_basis = estimate_data.get('_tax_basis', 'unknown')
            rev_match = estimate_data.get('_reverse_match', False)
            tax_reason = estimate_data.get('_tax_reason', '') or estimate_data.get('tax_reason', '')
            shop_name  = estimate_data.get('_repair_shop_name', '')
            # コグニセブン設定用 税モード（大きく明示）
            if tax_basis == 'tax_inclusive':
                cogni_tax_mode = '税込'
                cogni_tax_color = '#1e40af'
                cogni_tax_bg = '#dbeafe'
                cogni_tax_border = '#3b82f6'
                cogni_tax_icon = '🔵'
                basis_label = '税込明細（税抜に自動変換済み）'
            elif tax_basis == 'tax_exclusive':
                cogni_tax_mode = '税抜'
                cogni_tax_color = '#14532d'
                cogni_tax_bg = '#dcfce7'
                cogni_tax_border = '#22c55e'
                cogni_tax_icon = '🟢'
                basis_label = '税抜明細'
            else:
                cogni_tax_mode = '判定不能'
                cogni_tax_color = '#92400e'
                cogni_tax_bg = '#fef3c7'
                cogni_tax_border = '#f59e0b'
                cogni_tax_icon = '🟡'
                basis_label = '判定不能（手動確認推奨）'
            rev_icon = '✅ 逆算一致' if rev_match else '⚠️ 逆算不一致（金額を確認してください）'
            reason_html = f'<div style="font-size:12px;color:{cogni_tax_color};margin-top:4px">判定根拠: {tax_reason}</div>' if tax_reason else ''
            shop_html   = f'<div style="font-size:13px;color:#374151;margin-bottom:10px">🏭 修理工場: <b>{shop_name}</b></div>' if shop_name else ''
            st.markdown(f'''
<div style="border:2px solid {cogni_tax_border};border-radius:8px;background:{cogni_tax_bg};padding:14px 18px;margin-bottom:12px">
  {shop_html}
  <div style="font-size:13px;color:{cogni_tax_color};font-weight:600;margin-bottom:6px">■ コグニセブン設定用 税区分</div>
  <div style="font-size:22px;font-weight:700;color:{cogni_tax_color}">{cogni_tax_icon} コグニセブンを <u>{cogni_tax_mode}モード</u> に設定してください</div>
  <div style="font-size:13px;color:{cogni_tax_color};margin-top:4px">（{basis_label} ／ {rev_icon}）</div>
  {reason_html}
</div>
''', unsafe_allow_html=True)

        # ── タブ ──
        tab_vehicle, tab_estimate, tab_totals = st.tabs(["🚗 車両情報", "📊 見積明細", "💰 合計・費用"])

        with tab_vehicle:
            st.markdown('<div class="section-title">📋 車検証情報</div>', unsafe_allow_html=True)
            # 車両情報（修正可能なフォーム）
            col1, col2 = st.columns(2)
            with col1:
                v_customer = st.text_input("使用者名",    value=safe_str(vehicle_data.get('customer_name', '')),    key='v_customer')
                v_owner    = st.text_input("所有者名",    value=safe_str(vehicle_data.get('owner_name', '')),       key='v_owner')
                v_postal   = st.text_input("郵便番号",    value=safe_str(vehicle_data.get('postal_no', '')),        key='v_postal')
                v_pref     = st.text_input("都道府県",    value=safe_str(vehicle_data.get('prefecture', '')),       key='v_pref')
                v_muni     = st.text_input("市区町村",    value=safe_str(vehicle_data.get('municipality', '')),     key='v_muni')
                v_addr     = st.text_input("その他住所",  value=safe_str(vehicle_data.get('address_other', '')),    key='v_addr')
            with col2:
                v_dept   = st.text_input("登録番号 地名",   value=safe_str(vehicle_data.get('car_reg_department', '')), key='v_dept')
                v_div    = st.text_input("登録番号 分類番号", value=safe_str(vehicle_data.get('car_reg_division', '')),   key='v_div')
                v_biz    = st.text_input("登録番号 かな",   value=safe_str(vehicle_data.get('car_reg_business', '')),   key='v_biz')
                v_serial = st.text_input("登録番号 一連番号", value=safe_str(vehicle_data.get('car_reg_serial', '')),    key='v_serial')
                v_csn    = st.text_input("車台番号",       value=safe_str(vehicle_data.get('car_serial_no', '')),       key='v_csn')
                v_carname = st.text_input("車名",          value=safe_str(vehicle_data.get('car_name', '')),             key='v_carname')
            col3, col4, col5 = st.columns(3)
            with col3:
                v_km      = st.number_input("走行距離 (km)", value=safe_int(vehicle_data.get('kilometer', 0)), min_value=0, step=1000, key='v_km')
            with col4:
                v_term    = st.text_input("有効期限 (YYYYMMDD)",   value=safe_str(vehicle_data.get('term_date', '')),    key='v_term')
            with col5:
                v_regdate = st.text_input("初度登録年月 (YYYYMM00)", value=safe_str(vehicle_data.get('car_reg_date', '')), key='v_regdate')

            # 車両詳細情報
            st.markdown('<div class="section-title" style="margin-top:16px">🔧 車両詳細</div>', unsafe_allow_html=True)
            dc1, dc2, dc3 = st.columns(3)
            with dc1:
                v_model     = st.text_input("型式",         value=safe_str(vehicle_data.get('car_model', '')),              key='v_model')
                v_engine    = st.text_input("エンジン型式", value=safe_str(vehicle_data.get('engine_model', '')),           key='v_engine')
            with dc2:
                v_color     = st.text_input("車体の色",     value=safe_str(vehicle_data.get('body_color', '')),             key='v_color')
                v_colorcode = st.text_input("カラーコード", value=safe_str(vehicle_data.get('color_code', '')),             key='v_colorcode')
            with dc3:
                v_trimcode  = st.text_input("トリムコード", value=safe_str(vehicle_data.get('trim_code', '')),              key='v_trimcode')
                v_modeldesig = st.text_input("型式指定番号", value=safe_str(vehicle_data.get('car_model_designation', '')), key='v_modeldesig')
            dc4, dc5, dc6 = st.columns(3)
            with dc4:
                v_catnum    = st.text_input("類別区分番号", value=safe_str(vehicle_data.get('car_category_number', '')),    key='v_catnum')
            with dc5:
                v_weight    = st.number_input("車両重量 (kg)",  value=safe_int(vehicle_data.get('car_weight', 0)),          min_value=0, step=10, key='v_weight')
            with dc6:
                v_displace  = st.number_input("排気量 (cc)",    value=safe_int(vehicle_data.get('engine_displacement', 0)), min_value=0, step=100, key='v_displace')

        updated_vehicle = {
            'customer_name':      v_customer,
            'owner_name':         v_owner,
            'postal_no':          v_postal,
            'prefecture':         v_pref,
            'municipality':       v_muni,
            'address_other':      v_addr,
            'car_reg_department': v_dept,
            'car_reg_division':   v_div,
            'car_reg_business':   v_biz,
            'car_reg_serial':     v_serial,
            'car_serial_no':      v_csn,
            'car_name':           v_carname,
            'car_model':          v_model,
            'engine_model':       v_engine,
            'body_color':         v_color,
            'color_code':         v_colorcode,
            'trim_code':          v_trimcode,
            'car_model_designation': v_modeldesig,
            'car_category_number':   v_catnum,
            'car_weight':         v_weight,
            'engine_displacement': v_displace,
            'kilometer':          v_km,
            'term_date':          v_term,
            'car_reg_date':       v_regdate,
        }

        # 見積明細
        calc_parts = 0
        calc_wages = 0
        pdf_parts  = 0
        pdf_wages  = 0

        with tab_estimate:
          if estimate_data and estimate_data.get('items'):
            items = estimate_data['items']
            edit_rows = []
            for i, item in enumerate(items):
                m_level = item.get('_match_level', 0)
                m_text = ""
                if m_level == 1: m_text = "🟢 カタカナ完全"
                elif m_level == 2: m_text = "🟢 部分"
                elif m_level == 3: m_text = "🟢 前方"
                elif m_level == 4: m_text = "🟡 あいまい"
                elif m_level == 5: m_text = "🟡 類似"
                elif m_level == 6: m_text = "🔴 未マッチ"

                if item.get('_price_warning'):
                    m_text += " (価格⚠️)"

                if item.get('_reverse_match'):
                    m_text = "✅ 逆引一致 (" + m_text.split(" ")[0] + ")"

                # 部品コード: 見積書記載のpart_no → なければDBマッチ結果の_master_part_no
                part_code_disp = str(item.get('part_no', '') or item.get('_master_part_no', '') or '')
                # 作業コード: 見積書記載のwork_code → なければDBマッチ結果のsection+branchコード
                work_code_raw = str(item.get('work_code', '') or '')
                if not work_code_raw:
                    sc = str(item.get('_master_section_code', '') or item.get('_master_repair_code', '') or '')
                    bc = str(item.get('_master_branch_code', '') or '')
                    work_code_raw = (sc + bc).strip() if (sc or bc) else ''
                edit_rows.append({
                    'No': i + 1,
                    '品名': str(item.get('name', '')),
                    '作業': str(item.get('method', '')),
                    '数量': safe_int(item.get('quantity', 1), 1),
                    '部品金額': safe_int(item.get('parts_amount', 0)),
                    '工賃': safe_int(item.get('wage', 0)),
                    '部品コード': part_code_disp,
                    '作業コード': work_code_raw,
                    'マスタ照合': m_text,
                    '_master_name': item.get('_master_name', ''),
                    '_master_price': item.get('_master_price', 0),
                    '_master_part_no': item.get('_master_part_no', ''),
                    '_master_repair_code': item.get('_master_repair_code', ''),
                    '_master_branch_code': item.get('_master_branch_code', ''),
                    '_master_part_code_r': item.get('_master_part_code_r', ''),
                    '_master_part_code_l': item.get('_master_part_code_l', ''),
                    '_match_level': m_level,
                    '_original_name': item.get('name', ''),
                    '_original_parts_amount': item.get('parts_amount', 0),
                })
            df = pd.DataFrame(edit_rows)
            edited_df = st.data_editor(
                df,
                use_container_width=True,
                hide_index=True,
                num_rows="dynamic",
                column_config={
                    'No': st.column_config.NumberColumn('No', disabled=True, width='small'),
                    '品名': st.column_config.TextColumn('品名', width='large'),
                    '作業': st.column_config.TextColumn('作業'),
                    '数量': st.column_config.NumberColumn('数量', min_value=1, step=1),
                    '部品金額': st.column_config.NumberColumn('部品金額', step=1, format="¥%d"),
                    '工賃': st.column_config.NumberColumn('工賃', step=1, format="¥%d"),
                    '部品コード': st.column_config.TextColumn('部品コード', help='見積書記載の部品番号またはDBマッチ結果'),
                    '作業コード': st.column_config.TextColumn('作業コード', help='見積書記載の作業コードまたはDBマッチ結果'),
                    'マスタ照合': st.column_config.TextColumn('マスタ照合', disabled=True),
                    '_master_name': None,  # 非表示
                    '_master_price': None, # 非表示
                    '_master_part_no': None, # 非表示
                    '_master_repair_code': None, # 非表示
                    '_master_branch_code': None, # 非表示
                    '_master_part_code_r': None, # 非表示
                    '_master_part_code_l': None, # 非表示
                    '_match_level': None,  # 非表示
                    '_original_name': None, # 非表示
                    '_original_parts_amount': None, # 非表示
                },
                key='items_editor',
            )
            # 編集後データを反映（No列を自動採番）
            edited_df['No'] = range(1, len(edited_df) + 1)
            edited_items = []
            for _, row in edited_df.iterrows():
                name_val = row.get('品名', '')
                if pd.isna(name_val):
                    name_val = ''
                method_val = row.get('作業', '')
                if pd.isna(method_val):
                    method_val = ''
                edited_items.append({
                    'name': str(name_val),
                    'method': str(method_val),
                    'quantity': safe_int(row.get('数量', 1), 1),
                    'parts_amount': safe_int(row.get('部品金額', 0)),
                    'wage': safe_int(row.get('工賃', 0)),
                    'part_no': str(row.get('部品コード', '') or ''),
                    'work_code': str(row.get('作業コード', '') or ''),
                    '_master_name': row.get('_master_name', ''),
                    '_master_price': row.get('_master_price', 0),
                    '_master_part_no': row.get('_master_part_no', ''),
                    '_master_repair_code': row.get('_master_repair_code', ''),
                    '_master_branch_code': row.get('_master_branch_code', ''),
                    '_master_part_code_r': row.get('_master_part_code_r', ''),
                    '_master_part_code_l': row.get('_master_part_code_l', ''),
                    '_match_level': row.get('_match_level', 0),
                    '_original_name': str(row.get('_original_name', '')),
                    '_original_parts_amount': safe_int(row.get('_original_parts_amount', 0)),
                })
            estimate_data['items'] = edited_items
            st.session_state['estimate_data'] = estimate_data
            for it in edited_items:
                calc_parts += safe_int(it.get('parts_amount', 0))
                calc_wages += safe_int(it.get('wage', 0))
            sp = safe_int(estimate_data.get('short_parts_wage', 0))
            est_exempt = safe_int(estimate_data.get('tax_exempt_amount', 0))
            if sp > 0:
                st.markdown(f'<div class="alert alert-info">🔧 ショートパーツ（雑品代）: ¥{sp:,}（Expense自動振り分け済み）</div>', unsafe_allow_html=True)
            if est_exempt > 0:
                st.markdown(f'<div class="alert alert-info">🏷️ 非課税費用（預託/廃棄処分等）: ¥{est_exempt:,}（Expense自動振り分け済み）</div>', unsafe_allow_html=True)
                current_exempt = st.session_state.get('exp_exempt', 0)
                if current_exempt == 0:
                    st.session_state['exp_exempt'] = est_exempt
            pdf_parts = safe_int(estimate_data.get('pdf_parts_total', 0))
            pdf_wages = safe_int(estimate_data.get('pdf_wage_total', 0))
          else:
            with tab_estimate:
              st.info("見積書が読み込まれていません")

        with tab_totals:
          if estimate_data and estimate_data.get('items'):
            st.markdown('<div class="section-title">💰 金額サマリー</div>', unsafe_allow_html=True)
            scol1, scol2, scol3 = st.columns(3)
            rev_match = estimate_data.get('_reverse_match', False)

            # 金額差額の計算
            parts_diff = calc_parts - pdf_parts if pdf_parts > 0 else 0
            # SP込みでも一致チェック
            parts_match_sp = (calc_parts + sp == pdf_parts) if pdf_parts > 0 else False
            parts_match = (calc_parts == pdf_parts) or parts_match_sp
            wage_diff = calc_wages - pdf_wages if pdf_wages > 0 else 0
            wage_match = (calc_wages == pdf_wages)
            has_discrepancy = False

            with scol1:
                st.metric("部品合計（税抜）", f"¥{calc_parts:,}")
                if pdf_parts > 0 and not parts_match and not rev_match:
                    has_discrepancy = True
                    st.markdown(
                        f'<div class="error-box">⚠️ <b>部品相違</b>: PDF ¥{pdf_parts:,} ≠ 計算 ¥{calc_parts:,}（差額: {parts_diff:+,}円）</div>',
                        unsafe_allow_html=True
                    )
                elif pdf_parts > 0:
                    st.markdown('<div class="success-box">✅ PDF金額と一致</div>', unsafe_allow_html=True)
            with scol2:
                st.metric("工賃合計（税抜）", f"¥{calc_wages:,}")
                if pdf_wages > 0 and not wage_match and not rev_match:
                    has_discrepancy = True
                    st.markdown(
                        f'<div class="error-box">⚠️ <b>工賃相違</b>: PDF ¥{pdf_wages:,} ≠ 計算 ¥{calc_wages:,}（差額: {wage_diff:+,}円）</div>',
                        unsafe_allow_html=True
                    )
                elif pdf_wages > 0:
                    st.markdown('<div class="success-box">✅ PDF金額と一致</div>', unsafe_allow_html=True)
            with scol3:
                exp_tow = st.session_state.get('exp_towing', 0)
                exp_ren = st.session_state.get('exp_rental', 0)
                exp_exm = st.session_state.get('exp_exempt', 0)
                sub   = calc_parts + calc_wages + sp + exp_tow + exp_ren
                tax   = round(sub * TAX_RATE)
                total = sub + tax + exp_exm
                st.metric("合計（税込）", f"¥{total:,}")
                if rev_match:
                    st.markdown('<div class="success-box">✅ 逆算一致</div>', unsafe_allow_html=True)

            # ── STEP 3 バリデーション結果パネル ──
            tv = estimate_data.get('totals_verification', {})
            if tv:
                tv_match = tv.get('is_match', True)
                tv_p_diff = safe_int(tv.get('parts_diff', 0))
                tv_l_diff = safe_int(tv.get('labor_diff', 0))
                tv_err    = tv.get('validation_error', None)
                if tv_match:
                    st.markdown(
                        '<div class="success-box" style="padding:10px 16px;margin-bottom:12px">'
                        '✅ <b>【STEP 3 バリデーション: 合格】</b> 見積書記載の合計値と1円の誤差もなく一致しています。'
                        '</div>', unsafe_allow_html=True)
                else:
                    err_text = f'<br>推定原因: {tv_err}' if tv_err else ''
                    st.markdown(
                        f'<div class="error-box" style="padding:10px 16px;margin-bottom:12px">'
                        f'🚨 <b>【STEP 3 バリデーション: 不合格】</b> 金額の不一致が検出されています。<br>'
                        f'部品差額: {tv_p_diff:+,}円 ／ 工賃差額: {tv_l_diff:+,}円{err_text}'
                        f'</div>', unsafe_allow_html=True)

            # ── ベタ打ちモード専用: 包括的金額一致検証パネル ──
            _step3_mode = st.session_state.get('selected_mode', 'db')
            if _step3_mode == 'beta':
                st.markdown('<div class="section-title">📋 ベタ打ちモード — 金額一致検証レポート</div>', unsafe_allow_html=True)
                pdf_grand = safe_int(estimate_data.get('pdf_grand_total', 0))
                tax_basis_s3 = estimate_data.get('_tax_basis', 'unknown')
                _beta_verification_rows = []
                _beta_all_ok = True

                # 各行ごとの部品価格・工賃の記録
                for idx_b, item_b in enumerate(edited_items):
                    row_name = item_b.get('name', f'行{idx_b+1}')
                    row_parts = safe_int(item_b.get('parts_amount', 0))
                    row_wage = safe_int(item_b.get('wage', 0))
                    _beta_verification_rows.append({
                        'No': idx_b + 1,
                        '品名': row_name,
                        '部品価格': f"¥{row_parts:,}" if row_parts != 0 else '-',
                        '工賃': f"¥{row_wage:,}" if row_wage != 0 else '-',
                    })

                with st.expander("📊 明細行一覧（全項目）", expanded=False):
                    st.table(pd.DataFrame(_beta_verification_rows))

                # 合算値の一致確認
                _verify_items = []
                # ① 部品合計
                parts_ok = parts_match or rev_match
                _verify_items.append(('部品合計', pdf_parts, calc_parts, parts_ok))
                if not parts_ok and pdf_parts > 0:
                    _beta_all_ok = False
                # ② 工賃合計
                wage_ok = wage_match or rev_match
                _verify_items.append(('工賃合計', pdf_wages, calc_wages, wage_ok))
                if not wage_ok and pdf_wages > 0:
                    _beta_all_ok = False
                # ③ 見積合計（税込or税抜）
                if pdf_grand > 0:
                    grand_label = '見積合計（税込）' if tax_basis_s3 == 'tax_inclusive' else '見積合計（税抜→税込算出）'
                    # 丸め誤差の許容: 明細行数 × 1円 + 基本許容10円（最大50円）
                    _n_items = len(edited_items)
                    _grand_tolerance = min(_n_items + 10, 50)
                    grand_ok = abs(total - pdf_grand) <= _grand_tolerance
                    _verify_items.append((grand_label, pdf_grand, total, grand_ok))
                    if not grand_ok:
                        _beta_all_ok = False

                verify_html = '<table style="width:100%;border-collapse:collapse;font-size:13px;margin:8px 0">'
                verify_html += '<tr style="background:#f1f5f9;font-weight:600"><td style="padding:6px 10px">検証項目</td><td style="padding:6px 10px;text-align:right">PDF記載</td><td style="padding:6px 10px;text-align:right">計算値</td><td style="padding:6px 10px;text-align:center">結果</td></tr>'
                for v_label, v_pdf, v_calc, v_ok in _verify_items:
                    v_icon = '✅' if v_ok else '❌'
                    v_color = '#16a34a' if v_ok else '#dc2626'
                    v_diff = v_calc - v_pdf
                    v_diff_text = f' ({v_diff:+,}円)' if not v_ok and v_pdf > 0 else ''
                    verify_html += f'<tr style="border-bottom:1px solid #e2e8f0"><td style="padding:6px 10px">{v_label}</td><td style="padding:6px 10px;text-align:right">¥{v_pdf:,}</td><td style="padding:6px 10px;text-align:right">¥{v_calc:,}{v_diff_text}</td><td style="padding:6px 10px;text-align:center;color:{v_color};font-weight:600">{v_icon}</td></tr>'

                # ④ 逆算チェック: 合計から逆算して個別金額との不整合チェック
                if pdf_grand > 0 and (pdf_parts > 0 or pdf_wages > 0):
                    reverse_sub = calc_parts + calc_wages + sp
                    reverse_tax = round(reverse_sub * TAX_RATE)
                    reverse_grand = reverse_sub + reverse_tax + st.session_state.get('exp_exempt', 0)
                    _rev_tolerance = min(_n_items + 10, 50)
                    reverse_ok = abs(reverse_grand - pdf_grand) <= _rev_tolerance
                    reverse_icon = '✅' if reverse_ok else '⚠️'
                    reverse_color = '#16a34a' if reverse_ok else '#d97706'
                    if not reverse_ok:
                        _beta_all_ok = False
                    verify_html += f'<tr style="border-bottom:1px solid #e2e8f0;background:#fefce8"><td style="padding:6px 10px">逆算検証（税込総額）</td><td style="padding:6px 10px;text-align:right">¥{pdf_grand:,}</td><td style="padding:6px 10px;text-align:right">¥{reverse_grand:,}</td><td style="padding:6px 10px;text-align:center;color:{reverse_color};font-weight:600">{reverse_icon}</td></tr>'

                verify_html += '</table>'
                st.markdown(verify_html, unsafe_allow_html=True)

                # 一致率の算出・表示
                total_checks = len(_verify_items) + (1 if pdf_grand > 0 and (pdf_parts > 0 or pdf_wages > 0) else 0)
                passed_checks = sum(1 for _, _, _, ok in _verify_items if ok)
                if pdf_grand > 0 and (pdf_parts > 0 or pdf_wages > 0) and reverse_ok:
                    passed_checks += 1
                match_rate = (passed_checks / total_checks * 100) if total_checks > 0 else 0
                if _beta_all_ok:
                    st.markdown(f'<div class="success-box" style="padding:10px 16px;margin:8px 0">✅ <b>ベタ打ち検証: 全項目一致（一致率 {match_rate:.0f}%）</b> — PDF原本とNEO転記内容が完全一致しています。</div>', unsafe_allow_html=True)
                else:
                    st.markdown(f'<div class="error-box" style="padding:10px 16px;margin:8px 0">⚠️ <b>ベタ打ち検証: 不一致あり（一致率 {match_rate:.0f}%）</b> — PDF原本との差異を確認してください。基準: 99%以上</div>', unsafe_allow_html=True)

            # マスタ連携の差額計算とレポート表示（DBモード時のみ）
            discrepancies = []
            total_diff = 0
            if _step3_mode == 'beta':
                pass  # ベタ打ちモードではマスタ差額レポートをスキップ
            for item in edited_items if _step3_mode != 'beta' else []:
                m_level = item.get('_match_level', 0)
                ocr_price = item.get('_original_parts_amount', 0)
                master_price = item.get('_master_price', 0)
                is_reverse = item.get('_reverse_match', False)
                qty = item.get('quantity', 1)

                # Check discrepancy if NOT reverse matched
                if not is_reverse and ocr_price > 0 and (m_level >= 4 or m_level == 0 or ocr_price != master_price):
                    d = (master_price - ocr_price) * qty
                    discrepancies.append(item)
                    total_diff += d

            if discrepancies:
                st.markdown('<div class="warning-box">⚠️ <b>マスタ適用による金額差分レポート</b><br>OCRで読み取った金額と、Addataマスタ側の定価にズレがある部品が検出されました。</div>', unsafe_allow_html=True)
                diff_data = []
                for idx, d in enumerate(discrepancies):
                    orig_p = d.get('_original_parts_amount', 0)
                    mast_p = d.get('_master_price', 0)
                    qty = d.get('quantity', 1)
                    diff = (mast_p - orig_p) * qty

                    code_r = str(d.get('_master_part_code_r', '')).strip()
                    code_l = str(d.get('_master_part_code_l', '')).strip()
                    p_code = f"R:{code_r} / L:{code_l}" if (code_r and code_l) else (code_r or code_l or '')

                    diff_data.append({
                        'No': idx + 1,
                        'OCR 品名': d.get('_original_name', ''),
                        'OCR 単価': f"¥{orig_p:,}",
                        'マスタ品名': d.get('_master_name', ''),
                        '部品コード': p_code,
                        '枝番': d.get('_master_branch_code', ''),
                        '修理': d.get('_master_repair_code', ''),
                        'マスタ単価': f"¥{mast_p:,}",
                        '数量': qty,
                        '差額小計': f"{diff:+,}円"
                    })
                st.table(pd.DataFrame(diff_data))
                if total_diff > 0:
                    st.markdown(f'<div style="color: blue; font-weight: bold;">マスタ適用による総額変動: +{total_diff:,}円</div>', unsafe_allow_html=True)
                elif total_diff < 0:
                    st.markdown(f'<div style="color: red; font-weight: bold;">マスタ適用による総額変動: {total_diff:,}円</div>', unsafe_allow_html=True)
                else:
                    st.markdown(f'<div style="font-weight: bold;">マスタ適用による総額変動: なし (0円)</div>', unsafe_allow_html=True)

            DISCREPANCY_THRESHOLD = 1000
            if has_discrepancy and (abs(parts_diff) >= DISCREPANCY_THRESHOLD or abs(wage_diff) >= DISCREPANCY_THRESHOLD):
                st.markdown(
                    '<div class="mismatch-banner">'
                    '<div class="mismatch-title">🚨 金額不一致警告</div>'
                    '<div class="mismatch-body">AI読み取り金額とPDF記載金額に大きな差があります。<br>'
                    '明細行の内容を確認・修正してから生成してください。</div>'
                    '</div>',
                    unsafe_allow_html=True
                )
                amount_confirmed = st.checkbox(
                    "金額の差異を確認しました。このまま生成を続行します。",
                    value=False,
                    key='amount_confirmed'
                )
            else:
                amount_confirmed = True

            # ── Total strip ──
            sub   = calc_parts + calc_wages + sp + st.session_state.get('exp_towing', 0) + st.session_state.get('exp_rental', 0)
            tax   = round(sub * TAX_RATE)
            total = sub + tax + st.session_state.get('exp_exempt', 0)
            st.markdown(f"""
            <div class="total-strip">
                <div class="total-item">
                    <div class="total-label">部品代</div>
                    <div class="total-value">¥{calc_parts:,}</div>
                </div>
                <div class="total-sep">+</div>
                <div class="total-item">
                    <div class="total-label">工賃</div>
                    <div class="total-value">¥{calc_wages:,}</div>
                </div>
                <div class="total-sep">+</div>
                <div class="total-item">
                    <div class="total-label">消費税</div>
                    <div class="total-value">¥{tax:,}</div>
                </div>
                <div class="total-sep">=</div>
                <div class="total-item">
                    <div class="total-label">合計（税込）</div>
                    <div class="total-value-highlight">¥{total:,}</div>
                </div>
            </div>
            """, unsafe_allow_html=True)
          else:
            amount_confirmed = True
            st.info("💡 見積書なし — 車両情報のみのNEOファイルを作成します")

        if 'amount_confirmed' not in dir():
            amount_confirmed = True

        # NEO生成ボタン
        st.markdown("---")
        bcol1, bcol2 = st.columns(2)
        with bcol1:
            if st.button("← ステップ①に戻る", use_container_width=True):
                st.session_state['step'] = 1
                st.session_state['vehicle_data']  = None
                st.session_state['estimate_data'] = None
                st.rerun()
        with bcol2:
            gen_disabled = not amount_confirmed
            if st.button("📦 NEOファイルを生成する →", type="primary", use_container_width=True, disabled=gen_disabled):
                st.session_state['updated_vehicle'] = updated_vehicle
                st.session_state['calc_parts']      = calc_parts
                st.session_state['calc_wages']      = calc_wages
                st.session_state['pdf_parts']       = pdf_parts if estimate_data else None
                st.session_state['pdf_wages']       = pdf_wages if estimate_data else None
                st.session_state['discrepancies']   = discrepancies
                st.session_state['total_diff']      = total_diff
                st.session_state['step'] = 4
                st.rerun()
            if gen_disabled:
                st.caption("⬆️ 金額差異を確認してチェックを入れてください")

    # =========================================
    # STEP 4: NEO生成・ダウンロード
    # =========================================
    elif current_step == 4:
        updated_vehicle = st.session_state.get('updated_vehicle', {})
        estimate_data   = st.session_state.get('estimate_data')
        calc_parts      = st.session_state.get('calc_parts', 0)
        calc_wages      = st.session_state.get('calc_wages', 0)
        pdf_parts       = st.session_state.get('pdf_parts')
        pdf_wages       = st.session_state.get('pdf_wages')
        insurance_info  = {
            'policy_no':        st.session_state.get('policy_no', ''),
            'contractor_name':  st.session_state.get('contractor_name', ''),
        }
        expense_info = {
            'towing':      st.session_state.get('exp_towing', 0),
            'rental_car':  st.session_state.get('exp_rental', 0),
            'tax_exempt':  st.session_state.get('exp_exempt', 0),
        }
        items            = []
        short_parts_wage = 0
        has_estimate     = False
        reverse_match    = False
        if estimate_data and estimate_data.get('items'):
            items            = estimate_data['items']
            short_parts_wage = safe_int(estimate_data.get('short_parts_wage', 0))
            has_estimate     = True
            reverse_match    = estimate_data.get('_reverse_match', False)

        progress = st.progress(0, text="NEOファイルを生成中...")
        try:
            progress.progress(30, text="📦 テンプレートを処理中...")
            is_tax_inclusive = estimate_data.get('_is_tax_inclusive', False) if estimate_data else False
            _step4_beta = st.session_state.get('selected_mode', 'db') == 'beta'
            # カスタムテンプレートNEOが指定されている場合はそちらを使用
            # Step4はStep1とは別のelifブランチのため、session_stateから取得する
            custom_neo_file = st.session_state.get('custom_neo_upload')
            _use_custom_neo = custom_neo_file is not None
            _active_template = custom_neo_file.read() if _use_custom_neo else template_data
            if _use_custom_neo:
                custom_neo_file.seek(0)  # 再読込に備えてシーク位置リセット
                progress.progress(40, text="📁 カスタムテンプレートNEOを読み込み中...")
            neo_data, total_parts, total_wages, grand_total = generate_neo_file(
                _active_template, updated_vehicle, items, short_parts_wage, insurance_info,
                expenses=expense_info, is_tax_inclusive=is_tax_inclusive, is_beta_mode=_step4_beta,
                merge_mode=_use_custom_neo
            )
            progress.progress(80, text="📝 ファイル名を生成中...")
            filename = generate_filename(
                updated_vehicle, calc_parts, calc_wages, pdf_parts, pdf_wages,
                has_estimate, reverse_match, short_parts_wage
            )
            st.session_state['neo_bytes']    = neo_data
            st.session_state['neo_filename'] = filename
            progress.progress(100, text="✅ 生成完了！")

            # 不一致チェック
            _discrepancies_step4 = []
            _total_diff_step4 = 0
            if has_estimate and not reverse_match:
                sp_val = safe_int(short_parts_wage)
                parts_match_s4 = (calc_parts == pdf_parts) or (calc_parts + sp_val == pdf_parts)
                if pdf_parts is not None and pdf_parts > 0 and not parts_match_s4:
                    _discrepancies_step4.append(f"部品相違（PDF: ¥{pdf_parts:,} / 計算: ¥{calc_parts:,}）")
                    _total_diff_step4 += calc_parts - pdf_parts
                if pdf_wages is not None and pdf_wages > 0 and calc_wages != pdf_wages:
                    _discrepancies_step4.append(f"工賃相違（PDF: ¥{pdf_wages:,} / 計算: ¥{calc_wages:,}）")
                    _total_diff_step4 += calc_wages - pdf_wages

            if _discrepancies_step4:
                diff_abs = abs(_total_diff_step4)
                st.markdown(f"""
                <div class="mismatch-banner">
                    <div class="mismatch-title">⚠️ 金額不一致が検出されました（差額 ▲¥{diff_abs:,}）</div>
                    <div class="mismatch-body">
                        元見積の合計額と本システムの算出額が一致しません。<br>
                        NEOファイルを生成する前に不一致レポートを確認・保存することを推奨します。
                    </div>
                </div>
                """, unsafe_allow_html=True)
                with st.expander("📄 不一致レポートを確認", expanded=False):
                    for d_item in _discrepancies_step4:
                        st.warning(d_item)

            # ── ベタ打ちモード: PDF原本との差異特定レポート ──
            if _step4_beta and _discrepancies_step4:
                st.markdown('<div class="section-title">📋 ベタ打ちモード — 差異特定レポート</div>', unsafe_allow_html=True)
                st.markdown('金額の不一致箇所を特定するための詳細レポートをPDF形式でダウンロードできます。')
                beta_pdf_bytes = generate_beta_discrepancy_report_pdf(estimate_data, calc_parts, calc_wages, pdf_parts or 0, pdf_wages or 0, updated_vehicle)
                st.download_button(
                    label="📄 差異レポートをダウンロード(PDF)",
                    data=beta_pdf_bytes,
                    file_name=filename.replace('.neo', '_ベタ打ち差異レポート.pdf'),
                    mime="application/pdf",
                    use_container_width=True,
                    type="primary",
                    key='beta_diff_report_dl'
                )

            st.markdown('<div class="alert alert-success">✅ NEOファイルの生成が完了しました！コグニセブンで開いて内容を確認してください。</div>', unsafe_allow_html=True)

            # 生成内容サマリー
            summary_items = [
                ("ファイル名", f"`{filename}`"),
                ("ファイルサイズ", f"{len(neo_data):,} bytes"),
            ]
            if has_estimate:
                summary_items += [
                    ("明細行数", f"{len(items)} 行"),
                    ("合計金額", f"¥{grand_total:,}（税込）"),
                ]
                if reverse_match:
                    summary_items.append(("金額検証", "✅ 逆算一致"))
            else:
                summary_items.append(("内容", "車両情報のみ（明細なし）"))
            for k, v in summary_items:
                st.markdown(f"**{k}:** {v}")

            st.markdown("---")
            dcol1, dcol2 = st.columns(2)
            with dcol1:
                st.download_button(
                    label="📥 NEOファイルをダウンロード",
                    data=neo_data,
                    file_name=filename,
                    mime="application/octet-stream",
                    type="primary",
                    use_container_width=True
                )
            with dcol2:
                discrepancies_list = st.session_state.get('discrepancies', [])
                total_diff_val = st.session_state.get('total_diff', 0)
                if discrepancies_list:
                    pdf_bytes = generate_discrepancy_report_pdf(discrepancies_list, total_diff_val, updated_vehicle)
                    pdf_filename = filename.replace('.neo', '_差額レポート.pdf')
                    st.download_button(
                        label="📄 差額レポートのダウンロード(PDF)",
                        data=pdf_bytes,
                        file_name=pdf_filename,
                        mime="application/pdf",
                        use_container_width=True
                    )
                else:
                    st.button("📄 差額なし (PDF生成不要)", disabled=True, use_container_width=True)
            
            st.markdown("")
            if st.button("🔄 新しい見積を作成する", use_container_width=True):
                for key in [
                    'step', 'vehicle_data', 'estimate_data', 'neo_bytes', 'neo_filename',
                    'vehicle_file_bytes', 'vehicle_file_name', 'estimate_file_bytes',
                    'estimate_file_name', 'updated_vehicle', 'calc_parts', 'calc_wages',
                    'pdf_parts', 'pdf_wages',
                    'policy_no', 'contractor_name',
                    'exp_towing', 'exp_rental', 'exp_exempt',
                ]:
                    if key in st.session_state:
                        del st.session_state[key]
                st.session_state['step'] = 1
                st.rerun()
        except Exception as e:
            progress.empty()
            st.error(f"⚠️ NEO生成中にエラーが発生しました:\n\n{str(e)}")
            st.code(traceback.format_exc())
            if st.button("← ステップ③に戻る"):
                st.session_state['step'] = 3
                st.rerun()


if __name__ == '__main__':
    main()
