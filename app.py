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
import io
import re
import traceback
import pandas as pd
from concurrent.futures import ThreadPoolExecutor

# ============================================================
# 定数・設定
# ============================================================
SCRIPT_DIR        = os.path.dirname(os.path.abspath(__file__))
TEMPLATE_FILENAME = "テンプレート_トヨタ汎用_.neo"
TEMPLATE_PATH     = os.path.join(SCRIPT_DIR, TEMPLATE_FILENAME)
ANALYSIS_LOG_PATH = os.path.join(SCRIPT_DIR, "analysis.log")
TAX_RATE          = 0.10
# Streamlit Cloud の st.secrets にも対応（ローカルは .env を使用）
try:
    GEMINI_API_KEY = st.secrets.get('GEMINI_API_KEY', os.environ.get('GEMINI_API_KEY', ''))
except Exception:
    GEMINI_API_KEY = os.environ.get('GEMINI_API_KEY', '')
GEMINI_MODEL      = "gemini-2.5-flash"          # フォールバック（動的に上書きされる）
CONFIDENCE_THRESHOLD = 0.6

# 優先順位付きのモデル候補リスト（上位が最優先）
# gemini-2.5-flashを最優先（安定・クォータ余裕あり）
# gemini-3.1-pro-previewはクォータ250回/日の制限があるため後方に配置
_PREFERRED_MODELS = [
    "gemini-2.5-flash",
    "gemini-2.5-pro",
    "gemini-3.1-pro-preview",
    "gemini-3-pro-preview",
]
_FALLBACK_MODEL = "gemini-2.5-flash"

# クォータ超過で利用不可になったモデルを記録（セッション内キャッシュ）
_quota_exhausted_models: set = set()

_model_availability_cache: dict = {}  # key: api_key_hash, value: list of model IDs

# 解析結果キャッシュ: 同一ファイル（md5）の再解析を防ぐ（セッション中に有効）
# key: md5_hex + "_" + model_name + "_" + str(use_rasterize) → value: 解析結果dict
_analyze_result_cache: dict = {}

def get_available_gemini_models(api_key: str) -> list:
    """利用可能なGeminiモデルを返す（優先順位付き）。
    API疎通テストなしで即返却（高速化）。クォータ超過モデルのみ除外。"""
    if not api_key:
        return [_FALLBACK_MODEL]
    cache_key = api_key[-8:]
    if cache_key in _model_availability_cache:
        return _model_availability_cache[cache_key]
    # API呼び出しなしで優先リストをそのまま返す（疎通テスト廃止で高速化）
    result = [m for m in _PREFERRED_MODELS if m not in _quota_exhausted_models]
    if not result:
        result = [_FALLBACK_MODEL]
    _model_availability_cache[cache_key] = result
    return result


def get_default_gemini_model(api_key: str) -> str:
    """利用可能なモデルの中から最優先モデルを返す。クォータ超過モデルは除外。"""
    models = get_available_gemini_models(api_key)
    # クォータ超過モデルを除外して最優先を返す
    for m in models:
        if m not in _quota_exhausted_models:
            return m
    # 全モデルがクォータ超過の場合はフォールバック
    return models[0] if models else _FALLBACK_MODEL
SELF_CORRECTION_THRESHOLD = 1000  # 差額が1000円以上の場合のみ自己修復を試行（高速化）

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
    # ── 塗装セクション・その他テーブルをリセット ──
    # PaintingPanel: 複数行テーブル（パネル塗装行）→ 全削除
    cur.execute('DELETE FROM PaintingPanel')
    # PaintingLinkParts: 塗装リンクパーツ → 全削除
    cur.execute('DELETE FROM PaintingLinkParts')
    # PaintingOther: 1行固定テーブル。行名・LineNoは保持し工賃・時間をリセット
    cur.execute("""UPDATE PaintingOther SET
        Time=-1, WageOutTax=-1, WageInTax=-1, WageTax=-1, WageByManual=''""")
    # PaintingTotal: 合計テーブルをゼロリセット
    cur.execute("""UPDATE PaintingTotal SET
        TimeTotalPanel=0, TimeTotalBumper=0, TimeTotalFrame=0,
        TimeTotalEtcetera=0, TimeTotalOther=0, TimeTotal=0,
        WageTotalPanelOutTax=0, WageTotalPanelInTax=0, WageTotalPanelTax=0,
        WageTotalBumperOutTax=0, WageTotalBumperInTax=0, WageTotalBumperTax=0,
        WageTotalFrameOutTax=0, WageTotalFrameInTax=0, WageTotalFrameTax=0,
        WageTotalEtceteraOutTax=0, WageTotalEtceteraInTax=0, WageTotalEtceteraTax=0,
        WageTotalOtherOutTax=0, WageTotalOtherInTax=0, WageTotalOtherTax=0,
        WageTotalOutTax=0, WageTotalInTax=0, WageTotalTax=0, WageTotalByManual='',
        MaterialTotalPanelOutTax=0, MaterialTotalPanelInTax=0, MaterialTotalPanelTax=0,
        MaterialTotalBumperOutTax=0, MaterialTotalBumperInTax=0, MaterialTotalBumperTax=0,
        MaterialTotalFrameOutTax=0, MaterialTotalFrameInTax=0, MaterialTotalFrameTax=0,
        MaterialTotalEtceteraOutTax=0, MaterialTotalEtceteraInTax=0, MaterialTotalEtceteraTax=0,
        MaterialTotalOutTax=0, MaterialTotalInTax=0, MaterialTotalTax=0, MaterialTotalbyManual='',
        TotalOutTax=0, TotalInTax=0, TotalTax=0""")
    # 全Expense行をクリア（LineNo=1〜8: 文字書き/内張り/配線/ショートパーツ/レッカー代１/レッカー代２/写真代他/その他控除）
    for lno in (1, 2, 3, 4, 5, 6, 7, 8):
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
        # DBマッチなし（CSV取り込み等）の場合はCSVの部品コードをPartsNoに使用
        if not parts_no:
            parts_no = str(item.get('part_no', '') or '')
        
        # 未マッチ（またはそれに準ずる低マッチレベル）部品には先頭に「※」を付与
        # ベタ打ちモードではDB照合を行わないため※を付けない
        if not is_beta_mode and m_level >= 4:
            if not name.startswith('※'):
                name = '※' + name
        
        # 区分: work_code（Markdownパーサー保存先）または method から取得
        method = item.get('method', '') or item.get('work_code', '')

        # 品名から作業種別を自動推定（区分が空白の場合）
        if not method:
            _name_for_detect = str(item.get('name', ''))
            _parts_amt = safe_int(item.get('parts_amount', 0))
            _wage_amt  = safe_int(item.get('wage', 0))
            # ルール7: 研磨・磨き・写真代・ショートパーツは空白のまま（最優先）
            if any(kw in _name_for_detect for kw in ('研磨', '磨き', '写真代', 'ショートパーツ')):
                method = ''
            # ルール1: 部品金額あり・工賃なし → 取替
            elif _parts_amt > 0 and _wage_amt == 0:
                method = '取替'
            elif any(kw in _name_for_detect for kw in ('取替', '交換', '取換', '取り替え')):
                method = '取替'
            elif any(kw in _name_for_detect for kw in ('脱着', '取外', '取付', '組付', '脱外')):
                method = '脱着'
            elif any(kw in _name_for_detect for kw in ('鈑金', '板金')):
                method = '鈑金'
            elif any(kw in _name_for_detect for kw in ('塗装', 'ペイント', 'ワックス', '加算', 'ブース')):
                method = '塗装'
            elif any(kw in _name_for_detect for kw in (
                '修理', '補修', '分解', '修正',
                '光軸', 'フィッティング', 'コーディング', '穴あけ',
                'シーリング', '点検', '消去', '設定', '調整',
            )):
                method = '修理'

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
        _disposal_map = {
            '取替': 1, '交換': 1, '取換': 1,
            '脱着': 2, '取外': 2, '取付': 2, '組付': 2, '脱外': 2,
            '修理': 3, '補修': 3, '分解': 3, '修正': 3, '調整': 3,
            '光軸': 3, 'フィッティング': 3, 'コーディング': 3, '穴あけ': 3,
            'シーリング': 3, '点検': 3, '消去': 3, '設定': 3,
            '鈑金': 4, '板金': 4, '塗装': 4, 'ペイント': 4, 'ワックス': 4, '加算': 4, 'ブース': 4,
        }
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
            # 住所欄はNEOに記載不要のため除外（PostalNo/Prefecture/Municipality/AddressOther1は書き込まない）
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
        # 通常モード: 全フィールドを上書き（住所欄はNEO不要のため除外）
        cur.execute('''UPDATE Customer SET
            Name1=?, UserName=?, OwnerName=?,
            CarRegNoDepartment=?, CarRegNoDivision=?,
            CarRegNoBusiness=?, CarRegNoSerial=?,
            CarSerialNo=?, CarMouldNo=?, CarKindNo=?,
            TermDate=?, TermEra=?, TermEraYear=?,
            CarRegDate=?, CarRegEra=?, CarRegEraYear=?,
            Kilometer=?
        ''', (
            customer_name, customer_name, owner_name,
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
    OCR精度向上のための画像前処理（300dpi FAX品質対応強化版）。
    グレースケール変換 → デスペックル → コントラスト補正 → アンシャープマスク の順で処理。
    """
    try:
        from PIL import Image, ImageEnhance, ImageFilter, ImageOps
        img = Image.open(io.BytesIO(image_bytes))
        # グレースケール変換（色ノイズを除去してOCR精度向上）
        if img.mode not in ('L', 'LA'):
            img = img.convert('L')
        # デスペックル（MedianFilter でノイズ除去）
        img = img.filter(ImageFilter.MedianFilter(size=3))
        # コントラスト強化（FAXのかすれた文字を読みやすくする）
        img = ImageEnhance.Contrast(img).enhance(1.8)
        # アンシャープマスク（エッジを鮮明化）
        img = img.filter(ImageFilter.UnsharpMask(radius=1, percent=150, threshold=2))
        # 明るさ微調整（暗すぎる画像を補正）
        img = ImageEnhance.Brightness(img).enhance(1.05)
        buf = io.BytesIO()
        img.save(buf, format='JPEG', quality=94)
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


def detect_table_region(image_bytes):
    """
    画像から明細テーブル領域を検出し、クロップされた画像バイトと位置比率を返す。
    OpenCV が利用可能な場合は水平線検出を使用。
    フォールバック: ヒューリスティック（上12%・下90%）。
    戻り値: (cropped_bytes, top_ratio, bottom_ratio)
    """
    # ── OpenCV による水平線ベース検出 ─────────────────────────
    try:
        import cv2
        import numpy as np
        nparr = np.frombuffer(image_bytes, np.uint8)
        img_cv = cv2.imdecode(nparr, cv2.IMREAD_GRAYSCALE)
        if img_cv is not None:
            h, w = img_cv.shape
            _, thresh = cv2.threshold(img_cv, 200, 255, cv2.THRESH_BINARY_INV)
            horiz_kernel = cv2.getStructuringElement(cv2.MORPH_RECT, (max(1, w // 5), 1))
            horiz = cv2.morphologyEx(thresh, cv2.MORPH_OPEN, horiz_kernel, iterations=2)
            coords = cv2.findNonZero(horiz)
            if coords is not None and len(coords) > 4:
                ys = coords[:, 0, 1]
                top_y = max(0, int(np.min(ys)) - 15)
                bot_y = min(h, int(np.max(ys)) + 15)
                top_ratio = top_y / h
                bot_ratio = bot_y / h
                if bot_ratio - top_ratio >= 0.3:
                    from PIL import Image
                    pil = Image.open(io.BytesIO(image_bytes))
                    cropped = pil.crop((0, top_y, pil.width, bot_y))
                    buf = io.BytesIO()
                    cropped.save(buf, format='JPEG', quality=93)
                    return buf.getvalue(), top_ratio, bot_ratio
    except ImportError:
        pass
    except Exception:
        pass

    # ── フォールバック: ヒューリスティック ──────────────────────
    try:
        from PIL import Image
        pil = Image.open(io.BytesIO(image_bytes))
        h = pil.height
        top_y = int(h * 0.12)
        bot_y = int(h * 0.90)
        cropped = pil.crop((0, top_y, pil.width, bot_y))
        buf = io.BytesIO()
        cropped.save(buf, format='JPEG', quality=93)
        return buf.getvalue(), 0.12, 0.90
    except Exception:
        return image_bytes, 0.0, 1.0


def split_into_vertical_chunks(image_bytes, n_chunks=3, overlap_ratio=0.08):
    """
    画像を縦方向に n_chunks 分割（オーバーラップあり）。
    戻り値: List of (chunk_bytes, y_start_ratio, y_end_ratio)
    ※ y比率はクロップ画像に対する 0-1 の値
    """
    try:
        from PIL import Image
        pil = Image.open(io.BytesIO(image_bytes))
        w, h = pil.width, pil.height
        if h < 200:
            return [(image_bytes, 0.0, 1.0)]
        chunk_h = h // n_chunks
        overlap_px = max(10, int(h * overlap_ratio))
        chunks = []
        for i in range(n_chunks):
            y_start = max(0, i * chunk_h - (overlap_px if i > 0 else 0))
            y_end   = min(h, (i + 1) * chunk_h + (overlap_px if i < n_chunks - 1 else 0))
            if y_end <= y_start:
                continue
            chunk = pil.crop((0, y_start, w, y_end))
            buf = io.BytesIO()
            chunk.save(buf, format='JPEG', quality=93)
            chunks.append((buf.getvalue(), y_start / h, y_end / h))
        return chunks if chunks else [(image_bytes, 0.0, 1.0)]
    except Exception:
        return [(image_bytes, 0.0, 1.0)]


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


@st.cache_resource
def _get_genai_client(api_key):
    """google.genai クライアントを取得（セッション間で再利用・タイムアウト付き）"""
    from google import genai
    return genai.Client(api_key=api_key, http_options={'timeout': 180})


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
                import time; time.sleep(1)
                continue
            raise ValueError("Geminiから有効な応答が得られませんでした。")
        except ValueError:
            raise
        except Exception as e:
            last_error = e
            if attempt < 2:
                import time; time.sleep(1)
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
        prompt = _build_prompt("estimate_cover_check")
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
        'ラジエーター': 'ラジエータ',
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

    # 部品名を事前正規化してキャッシュ（fuzzy_match_part内ループの高速化）
    _KANA_SMALL_TO_LARGE_PRE = str.maketrans('ｧｨｩｪｫｯｬｭｮ', 'ｱｲｳｴｵﾂﾔﾕﾖ')
    for _mp in master_parts:
        if '_norm_name' not in _mp:
            _mn = jaconv.z2h(_mp['name'], ascii=True, digit=True, kana=True).replace(' ', '')
            _mn = _mn.translate(_KANA_SMALL_TO_LARGE_PRE)
            _mp['_norm_name'] = _mn
            _mp['_norm_name_clean'] = _mn.replace('L', '').replace('R', '').replace('ﾊﾟﾈﾙ', '').replace('ｱｯｼ', '').replace('ｱｳﾀ', '').replace('ｲﾝﾅ', '').replace('ｶﾞｰﾄﾞ', '').strip()

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
        norm_target = norm_target.translate(_KANA_SMALL_TO_LARGE_PRE)

        # clean版: L/R位置フラグ・パネル・アッシ・ガードを除去した芯の文字列
        norm_target_clean = norm_target.replace('L', '').replace('R', '').replace('ﾊﾟﾈﾙ', '').replace('ｱｯｼ', '').replace('ｶﾞｰﾄﾞ', '').strip()

        candidates = []
        for mp in master_parts:
            m_name = mp['_norm_name']          # 事前正規化済み
            m_name_clean = mp['_norm_name_clean']  # 事前計算済み
            
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
    from reportlab.lib.pagesizes import A4
    from reportlab.lib.units import mm
    from reportlab.pdfbase import pdfmetrics
    from reportlab.pdfbase.ttfonts import TTFont
    from reportlab.pdfbase.cidfonts import UnicodeCIDFont
    import io

    # 日本語フォントの登録 (Windows標準のメイリオを試行)
    try:
        pdfmetrics.registerFont(TTFont('Meiryo', 'meiryo.ttc'))
        font_name = 'Meiryo'
    except Exception:
        try:
            pdfmetrics.registerFont(TTFont('MSGothic', 'msgothic.ttc'))
            font_name = 'MSGothic'
        except Exception:
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
    except Exception:
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
            p_amt = it.get('_original_parts_amount', 0)
            
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


# ============================================================
# Gemini 2.5 Flash 向け共通プロンプト定義
# 送信形式: CORE_PROMPT + "\n\n" + TASK_PROMPTS[task_type]
# ============================================================

CORE_PROMPT = """<system_instruction>
あなたは日本語の自動車関連業務帳票（自動車修理見積書、車検証、FAX表紙など）を解析し、後続のNEOシステム連携用に構造化データを抽出する高精度OCR・解析APIエンジンです。
入力された画像またはPDFを精読し、推測を一切排除して、指定された<output_format>の厳格なJSONのみを出力してください。
</system_instruction>

<golden_rules>
1. 【完全転写】入力画像に記載されているテキスト・数値をそのまま抽出すること。存在しない値の推測、補完、勝手な計算は絶対に行わない。
2. 【欠落防止】ページ跨ぎ、折り返し行、セクション区切り、ページ最下部の行などを絶対に漏らさないこと。
3. 【ノイズ排除】挨拶、説明文、Markdownの装飾（```json など）は一切出力しない。純粋なJSON文字列のみを返すこと。
4. 【数値の正規化】金額や数量は、カンマ(,)を除去した半角整数の数値型(Number)で出力すること。読み取れない数値は 0 とし、読み取れない文字は "不明" とする。
</golden_rules>

<extraction_logic>
- カンマと空白: 連続するカンマ（例: ,,,,,）は「空白セル」を意味する。列の右ズレを防ぐこと。
- 行の結合: 部品名などが不自然に改行されている場合は、文脈から1つのレコードに結合する。
- 金額の分離（単一列に混在している場合）:
  - 品番がある行、または「部品」「材料」の名称行 → 「部品金額」へ。
  - 「交換」「脱着」「調整」「修理」「鈑金」「塗装」「点検」「診断」「設定」等の作業名行 → 「技術料」へ。
- 外車ディーラー見積（BMW、ベンツ等）:
  - 「Labor」「工賃」に相当する金額 → 「技術料」へ。
  - 「Parts」「部品」に相当する金額 → 「部品金額」へ。
  - 英数字・ハイフン混じりの品番は必ず「部品品番」へ。
- 区分の判定ルール（作業内容から以下の優先順位で判定して文字列を割り当てる）:
  1. 【重要】部品名称および部品金額の計上があるが、技術料（工賃）の計上がない行 → "取替"
  2. 「取替」「交換」「取換」「取り替え」を含む → "取替"
  3. 「脱着」「取外」「取付」「組付」を含む → "脱着"
  4. 「鈑金」「板金」を含む → "鈑金"
  5. 「塗装」「ペイント」「ワックス」「加算」「ブース」を含む → "塗装"
  6. 「修理」「補修」「分解」「修正」「光軸」「フィッティング」「コーディング」「穴あけ」「シーリング」「点検」「消去」「設定」「調整」を含む → "修理"
  7. 「研磨」「磨き」「写真代」「ショートパーツ」を含む → ""（空白）
</extraction_logic>"""


TASK_PROMPTS = {}

TASK_PROMPTS["shaken_ocr"] = """あなたは日本の車検証（自動車検査証）を読み取るOCRエキスパートです。
提供された画像またはPDFから以下の情報を正確に読み取ってください。

ルール:
- 入力資料に記載されている文字を一言一句そのまま抽出する
- 推測での補完は絶対に行わない
- 読み取り不能な文字列は "" にする
- 読み取り不能な数値は 0 にする
- 勝手な情報の統合・省略は行わない
- 和暦は西暦へ変換する（令和1=2019, 令和6=2024, 令和8=2026 / 平成31=2019, 平成30=2018...）
- car_reg_division と car_reg_serial は全角数字
- car_reg_business は全角かな
- car_reg_date は YYYYMM00 形式
- term_date は YYYYMMDD 形式
- confidence は 0.0〜1.0

返却JSON:
{
  "customer_name": "",
  "owner_name": "",
  "postal_no": "",
  "prefecture": "",
  "municipality": "",
  "address_other": "",
  "car_reg_department": "",
  "car_reg_division": "",
  "car_reg_business": "",
  "car_reg_serial": "",
  "car_serial_no": "",
  "car_name": "",
  "car_model": "",
  "car_model_designation": "",
  "car_category_number": "",
  "engine_model": "",
  "body_color": "",
  "color_code": "",
  "trim_code": "",
  "car_weight": 0,
  "engine_displacement": 0,
  "kilometer": 0,
  "term_date": "",
  "car_reg_date": "",
  "confidence": 0.0
}"""


TASK_PROMPTS["estimate_cover_check"] = """<task_execution>
タスク名: fax_cover_check

このページが宛先・件名・枚数・メッセージのみのFAX送付状（カバーシート）であるかを判定します。見積明細や金額合計が含まれていればfalseです。

重要な判定基準:
- ページ上部に「送信日時」「FAX番号」等が印字されていても、見積書の明細・合計欄を含んでいれば is_fax_cover = false
- 「御見積書」「修理費用明細書」「部品代」「工賃」「合計」などが記載されていれば is_fax_cover = false

page_type の値: fax_cover / estimate / vehicle / other

<output_format>
{
  "step_by_step_reasoning": "見積明細や合計金額の有無を確認した結果",
  "is_fax_cover": false,
  "page_type": "estimate",
  "reason": ""
}
</output_format>
</task_execution>"""


TASK_PROMPTS["estimate_header_totals"] = """<task_execution>
タスク名: header_total_extraction

合計値・修理工場名・車両情報を抽出します。「ページ小計」は総合計に使用しないでください。
「部品計」「工賃計」の明示的な小計行が存在しない単列金額形式の場合は、部品計・工賃計を 0 とし、総合計のみを抽出してください。

金額探索ルール:
- 「部品計」「部品代」「部品合計」「部品・油脂」等の明示的な小計行 → pdf_parts_total
- 「工賃計」「技術料合計」「工賃合計」等の明示的な小計行 → pdf_wage_total
- 「合計」「総合計」「御見積合計金額」「御見積金額」「見積金額」「請求金額」等 → pdf_grand_total
- 値引き額 → discount_amount
- Honda Cars系はページ1上部サマリーボックスの合計値も確認する

<output_format>
{
  "step_by_step_reasoning": "金額がどこに記載されていたか、どのように数値を判定したかの簡潔な思考プロセス",
  "repair_shop_name": "不明",
  "car_name": "不明",
  "car_model": "不明",
  "color_code": "不明",
  "license_plate": "不明",
  "pdf_parts_total": 0,
  "pdf_wage_total": 0,
  "discount_amount": 0,
  "pdf_grand_total": 0
}
</output_format>
</task_execution>"""


TASK_PROMPTS["estimate_detail_page"] = """<task_execution>
タスク名: detail_extraction

文書上部から基本情報を抽出し、明細行を配列で抽出してください。合計行・小計行・消費税行は明細配列に含めないでください。

<output_format>
{
  "step_by_step_reasoning": "行のズレや欠落がないか、部品と工賃の分離をどう行ったかの簡潔な思考プロセス",
  "basic_info": {
    "estimate_date": "文字列",
    "customer_name": "文字列",
    "car_type": "文字列",
    "registration_number": "文字列",
    "model_code": "文字列"
  },
  "details": [
    {
      "work_or_part_name": "文字列",
      "category": "文字列 (区分判定ルールに従う)",
      "index_value": "文字列 (指数)",
      "labor_fee": 0,
      "quantity": 0,
      "part_price": 0,
      "part_number": "文字列"
    }
  ]
}
</output_format>
</task_execution>"""


TASK_PROMPTS["estimate_validation_repair"] = """あなたは、見積書抽出結果の金額検算エンジンです。
前回の読み取り結果に金額誤差が検出されたため、見積書を最初から再精読して完全に正確な抽出を行ってください。

原則:
- 1円の狂いも許されない
- 見積書記載額を一言一句正確に読む
- 勝手な査定、減額、工法変更、項目削除をしない
- 前回結果を盲信せず最初から読み直す
- 不一致原因を行単位で特定する

必須チェック:
1. 行の見落とし
2. 部品列と工賃列の取り違え
3. 数量の誤読
4. 金額の読み取りミス（桁ずれ）
5. 複数行を1行に合算している
6. ページ下端の取りこぼし
7. 小計/合計の誤加算
8. 行ずれによる列誤認
9. 値引き行を items に混入していないか
10. 明細行を誤って除外していないか

返却JSON形式は前回と同じ estimate_detail_page 形式で返すこと。
status フィールドを追加すること:
- "success": 期待合計と一致
- "failed": 不一致あり

成功条件:
- expected_totals と calculated_totals が完全一致
- ページ下端の取りこぼしなし
- 不確定数字なし"""


def _build_prompt(task_type: str, extra: str = "") -> str:
    """CORE_PROMPT + TASK_PROMPTS[task_type] + learned_hints + extra を結合して返す"""
    task_part = TASK_PROMPTS.get(task_type, "")
    learned   = _load_learned_hints(task_type)
    parts = [CORE_PROMPT, task_part, learned, extra]
    return "\n\n".join(p for p in parts if p)


# ============================================================
# フィードバック学習DB
# ============================================================
import uuid as _uuid

_FEEDBACK_DB_PATH = os.path.join(os.path.dirname(os.path.abspath(__file__)), "feedback.db")

# エラー種別の日本語ラベル
FEEDBACK_ERROR_TYPES = {
    "column_swap":    "部品↔工賃の取り違え",
    "missed_row":     "行の見落とし",
    "amount_misread": "金額の読み取りミス",
    "wrong_category": "分類誤り（合計行混入等）",
    "name_error":     "品名の誤読",
    "quantity_error": "数量の誤読",
    "extra_row":      "不要な行が追加されている",
    "other":          "その他",
}

# 積算しきい値（この件数を超えたらマスタ統合を推奨）
FEEDBACK_MERGE_THRESHOLD = 5


def _get_feedback_db():
    """フィードバックDB接続を返す（テーブルが存在しない場合は作成）"""
    conn = sqlite3.connect(_FEEDBACK_DB_PATH)
    cur  = conn.cursor()
    cur.execute("""
        CREATE TABLE IF NOT EXISTS corrections (
            id            TEXT PRIMARY KEY,
            timestamp     TEXT NOT NULL,
            document_type TEXT,
            error_type    TEXT,
            row_index     INTEGER,
            orig_name     TEXT,
            orig_parts    INTEGER,
            orig_wage     INTEGER,
            corr_name     TEXT,
            corr_parts    INTEGER,
            corr_wage     INTEGER,
            user_comment  TEXT,
            page_context  TEXT,
            status        TEXT DEFAULT 'pending'
        )
    """)
    cur.execute("""
        CREATE TABLE IF NOT EXISTS prompt_patches (
            id          TEXT PRIMARY KEY,
            task_type   TEXT NOT NULL,
            patch_text  TEXT NOT NULL,
            created_at  TEXT NOT NULL,
            is_active   INTEGER DEFAULT 1
        )
    """)
    conn.commit()
    return conn


def record_correction(corrections: list, user_comment: str, document_type: str = "不明"):
    """
    明細の訂正データをDBに記録する。
    corrections: [{"row_index": int, "error_type": str, "original": dict, "corrected": dict}]
    """
    if not corrections:
        return
    conn = _get_feedback_db()
    cur  = conn.cursor()
    ts   = datetime.datetime.now().isoformat()
    for c in corrections:
        orig = c.get("original", {})
        corr = c.get("corrected", {})
        cur.execute("""
            INSERT INTO corrections
            (id, timestamp, document_type, error_type, row_index,
             orig_name, orig_parts, orig_wage,
             corr_name, corr_parts, corr_wage,
             user_comment, page_context, status)
            VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?)
        """, (
            str(_uuid.uuid4()), ts, document_type,
            c.get("error_type", "other"),
            c.get("row_index", 0),
            str(orig.get("name", "")),
            safe_int(orig.get("parts_amount", 0)),
            safe_int(orig.get("wage", 0)),
            str(corr.get("name", "")),
            safe_int(corr.get("parts_amount", 0)),
            safe_int(corr.get("wage", 0)),
            user_comment,
            c.get("page_context", ""),
            "pending",
        ))
    conn.commit()
    conn.close()


def get_error_summary():
    """エラー種別ごとの件数・代表例をまとめて返す"""
    try:
        conn = _get_feedback_db()
        cur  = conn.cursor()
        cur.execute("""
            SELECT error_type, COUNT(*) as cnt,
                   GROUP_CONCAT(orig_name, '|') as names
            FROM corrections
            WHERE status = 'pending'
            GROUP BY error_type
            ORDER BY cnt DESC
        """)
        rows = cur.fetchall()
        conn.close()
        result = []
        for r in rows:
            names = list(set((r[2] or "").split("|")))[:5]
            result.append({
                "error_type": r[0],
                "label": FEEDBACK_ERROR_TYPES.get(r[0], r[0]),
                "count": r[1],
                "sample_names": [n for n in names if n],
            })
        return result
    except Exception:
        return []


def get_all_pending_corrections():
    """未統合の全訂正レコードを返す"""
    try:
        conn = _get_feedback_db()
        cur  = conn.cursor()
        cur.execute("""
            SELECT id, timestamp, document_type, error_type,
                   orig_name, orig_parts, orig_wage,
                   corr_name, corr_parts, corr_wage,
                   user_comment
            FROM corrections
            WHERE status = 'pending'
            ORDER BY timestamp DESC
        """)
        rows = cur.fetchall()
        conn.close()
        cols = ["id","timestamp","document_type","error_type",
                "orig_name","orig_parts","orig_wage",
                "corr_name","corr_parts","corr_wage","user_comment"]
        return [dict(zip(cols, r)) for r in rows]
    except Exception:
        return []


def generate_and_save_patch(patch_text: str, task_type: str = "estimate_detail_page"):
    """
    生成されたプロンプトパッチをDBに保存し、既存のアクティブパッチを無効化する。
    """
    conn = _get_feedback_db()
    cur  = conn.cursor()
    # 既存アクティブパッチを無効化
    cur.execute("UPDATE prompt_patches SET is_active = 0 WHERE task_type = ?", (task_type,))
    # 新パッチを挿入
    cur.execute("""
        INSERT INTO prompt_patches (id, task_type, patch_text, created_at, is_active)
        VALUES (?,?,?,?,1)
    """, (str(_uuid.uuid4()), task_type, patch_text,
          datetime.datetime.now().isoformat()))
    # 統合済みの pending レコードを merged に更新
    cur.execute("UPDATE corrections SET status = 'merged' WHERE status = 'pending'")
    conn.commit()
    conn.close()


def _load_learned_hints(task_type: str = "estimate_detail_page") -> str:
    """
    現在アクティブなプロンプトパッチを返す。なければ空文字列。
    _build_prompt() から呼ばれる。
    """
    try:
        conn = _get_feedback_db()
        cur  = conn.cursor()
        cur.execute("""
            SELECT patch_text FROM prompt_patches
            WHERE task_type = ? AND is_active = 1
            ORDER BY created_at DESC LIMIT 1
        """, (task_type,))
        row = cur.fetchone()
        conn.close()
        return row[0] if row else ""
    except Exception:
        return ""


def _detect_corrections(original_items: list, edited_items: list) -> list:
    """
    AIが出力したオリジナル明細とユーザー編集後を比較し、差分リストを返す。
    Returns: [{"row_index", "error_type", "original", "corrected", "page_context"}]
    """
    corrections = []
    max_len = max(len(original_items), len(edited_items))
    for i in range(max_len):
        if i >= len(original_items):
            # 行追加
            corr = edited_items[i]
            corrections.append({
                "row_index":    i + 1,
                "error_type":   "missed_row",
                "original":     {},
                "corrected":    corr,
                "page_context": f"{i+1}行目（追加）",
            })
            continue
        if i >= len(edited_items):
            # 行削除
            orig = original_items[i]
            corrections.append({
                "row_index":    i + 1,
                "error_type":   "extra_row",
                "original":     orig,
                "corrected":    {},
                "page_context": f"{i+1}行目（削除）",
            })
            continue

        orig = original_items[i]
        corr = edited_items[i]
        orig_p = safe_int(orig.get("parts_amount", 0))
        orig_w = safe_int(orig.get("wage", 0))
        corr_p = safe_int(corr.get("parts_amount", 0))
        corr_w = safe_int(corr.get("wage", 0))
        orig_n = str(orig.get("name", ""))
        corr_n = str(corr.get("name", ""))

        if orig_p == corr_p and orig_w == corr_w and orig_n == corr_n:
            continue  # 変更なし

        # エラー種別を自動推定
        error_type = "other"
        if orig_p == corr_w and orig_w == corr_p and orig_p != orig_w:
            error_type = "column_swap"
        elif orig_n != corr_n and orig_p == corr_p and orig_w == corr_w:
            error_type = "name_error"
        elif orig_p != corr_p and orig_w == corr_w:
            error_type = "amount_misread"
        elif orig_w != corr_w and orig_p == corr_p:
            error_type = "column_swap"
        elif orig_p != corr_p and orig_w != corr_w:
            error_type = "column_swap"

        corrections.append({
            "row_index":    i + 1,
            "error_type":   error_type,
            "original":     orig,
            "corrected":    corr,
            "page_context": f"{i+1}行目: {orig_n}",
        })
    return corrections


def analyze_vehicle_registration(api_key, file_bytes, mime_type):
    """車検証をAI-OCRで解析"""
    prompt = _build_prompt("shaken_ocr")
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
    """1パス目: 合計値 + 見積書ヘッダの修理工場名・車両情報読み取り"""
    _combined_prompt = _build_prompt("estimate_header_totals")
    # response schema: totals + vehicle_info のみ
    _schema_totals = {
        "type": "object",
        "properties": {
            "repair_shop_name": {"type": "string"},
            "pdf_parts_total":  {"type": "integer"},
            "pdf_wage_total":   {"type": "integer"},
            "pdf_grand_total":  {"type": "integer"},
            "discount_amount":  {"type": "integer"},
            "confidence":       {"type": "number"},
            "vehicle_info": {
                "type": "object",
                "properties": {
                    "car_name":    {"type": "string"},
                    "car_model":   {"type": "string"},
                    "engine_model":{"type": "string"},
                    "color_code":  {"type": "string"},
                    "color_name":  {"type": "string"},
                    "trim_code":   {"type": "string"},
                    "grade":       {"type": "string"},
                    "model_year":  {"type": "string"},
                    "chassis_no":  {"type": "string"},
                    "mileage":     {"type": "string"},
                },
            },
        },
    }
    try:
        from google.genai import types
        client = _get_genai_client(api_key)
        file_part = types.Part.from_bytes(data=file_bytes, mime_type=mime_type)
        response = client.models.generate_content(
            model=model_name,
            contents=[_combined_prompt, file_part],
            config={
                "temperature": 0.0,
                "max_output_tokens": 4096,
                "response_mime_type": "application/json",
                "response_schema": _schema_totals,
            },
        )
        if response.text:
            try:
                return json.loads(response.text)
            except (json.JSONDecodeError, TypeError):
                return extract_json_from_response(response.text)
    except Exception as e:
        err_msg = str(e)
        if 'no longer available' in err_msg or '404' in err_msg or 'NOT_FOUND' in err_msg:
            raise RuntimeError(f"モデル '{model_name}' は利用できません。サイドバーで別のモデルを選択してください。\n詳細: {err_msg}") from e
    return None


def parse_csv_to_items(csv_text: str) -> list:
    """Claude.ai / Gemini.ai 等から出力されたCSVテキストをitemsリストに変換する。
    期待フォーマット（ヘッダあり）:
        品名,区分,数量,部品金額,工賃,部品コード
    """
    import csv as _csv
    import io as _io

    # BOM除去・改行正規化
    text = csv_text.strip().lstrip('\ufeff').replace('\r\n', '\n').replace('\r', '\n')
    items = []
    try:
        reader = _csv.reader(_io.StringIO(text))
        rows = list(reader)
    except Exception:
        return items

    if not rows:
        return items

    # ヘッダ行を特定（"品名" を含む行を探す）
    header_idx = 0
    for i, row in enumerate(rows):
        if row and '品名' in row[0]:
            header_idx = i + 1  # 次行からデータ
            break

    row_idx = 0
    for row in rows[header_idx:]:
        if not row or not any(c.strip() for c in row):
            continue
        # 列数が足りない場合は右側を空文字で補完
        while len(row) < 6:
            row.append('')

        name      = row[0].strip()
        category  = row[1].strip() if len(row) > 1 else ''
        qty       = safe_int(row[2].strip(), 1) if len(row) > 2 else 1
        parts_amt = safe_int(row[3].strip()) if len(row) > 3 else 0
        wage_amt  = safe_int(row[4].strip()) if len(row) > 4 else 0
        part_no   = row[5].strip() if len(row) > 5 else ''

        if not name:
            continue
        # 合計・小計行を除外
        if any(kw in name for kw in ('合計', '小計', '消費税', '税額', '値引', '総額')):
            continue
        if qty < 1:
            qty = 1

        row_idx += 1
        items.append({
            'page':         1,
            'row_type':     'detail',
            'name':         to_halfwidth_katakana(name),
            'description':  '',
            'work_code':    category,
            'method':       category,
            'part_no':      part_no,
            'quantity':     qty,
            'parts_amount': parts_amt,
            'wage':         wage_amt,
            'line_total':   parts_amt + wage_amt,
            'index_value':  '',
            'raw_text':     ','.join(row),
            'row_id':       f'p1_r{row_idx:03d}',
            'row_bbox':     {'x1': 0, 'y1': 0, 'x2': 1000, 'y2': 50},
        })
    return items


def parse_detail_json_to_items(json_text: str, page_num: int = 1) -> list:
    """Geminiが出力したdetail_extraction JSONをitemsリスト（JSON互換）に変換する。
    失敗した場合は空リストを返す（呼び出し元でMarkdownフォールバック）。
    """
    import re, json as _json
    text = json_text.strip()
    # ```json ... ``` ブロックを除去
    text = re.sub(r'^```json\s*', '', text, flags=re.MULTILINE)
    text = re.sub(r'^```\s*$', '', text, flags=re.MULTILINE)
    # JSON部分を抽出
    m = re.search(r'\{.*\}', text, re.DOTALL)
    if not m:
        return []
    try:
        data = _json.loads(m.group(0))
    except Exception:
        try:
            data = _json.loads(repair_truncated_json(m.group(0)))
        except Exception:
            return []
    details = data.get('details', [])
    # 'details' キーが空なら 'items' キーもフォールバック確認
    if not details:
        details = data.get('items', [])
    if not isinstance(details, list):
        return []
    items = []
    for row_idx, detail in enumerate(details, 1):
        name        = str(detail.get('work_or_part_name', '') or '').strip()
        category    = str(detail.get('category', '') or '').strip()
        index_value = str(detail.get('index_value', '') or '').strip()
        wage_raw    = detail.get('labor_fee', 0)
        qty_raw     = detail.get('quantity', 1)
        parts_raw   = detail.get('part_price', 0)
        part_no     = str(detail.get('part_number', '') or '').strip()
        wage  = safe_int(wage_raw)
        qty   = safe_int(qty_raw, 1)
        parts = safe_int(parts_raw)
        if wage == 0 and parts == 0:
            continue
        if qty < 1:
            qty = 1
        items.append({
            'page':         page_num,
            'row_type':     'detail',
            'name':         name if name else '不明',
            'description':  '',
            'work_code':    category,
            'index_value':  index_value,
            'part_no':      part_no,
            'quantity':     qty,
            'parts_amount': parts,
            'wage':         wage,
            'line_total':   wage + parts,
            'raw_text':     str(detail),
            'row_id':       f'p{page_num}_r{row_idx:03d}',
            'row_bbox':     {'x1': 0, 'y1': 0, 'x2': 1000, 'y2': 50},
        })
    return items


def parse_markdown_to_items(md_text: str, page_num: int = 1) -> list:
    """Geminiが出力したMarkdown表をitemsリスト（JSON互換）に変換する"""
    import re
    items = []
    row_idx = 0

    def to_int(s):
        s = re.sub(r'[,，\s¥￥円△▲+\-]', '', str(s))
        try:
            return int(float(s))
        except Exception:
            return 0

    for line in md_text.splitlines():
        if not line.startswith('|'):
            continue
        cells = [c.strip() for c in line.split('|')[1:-1]]
        if len(cells) < 3:
            continue
        # ヘッダー行をスキップ
        if cells[0] in ('作業内容・使用部品名', '作業内容', '品名', '部品名'):
            continue
        # 区切り行（--- のみ）をスキップ
        if re.match(r'^[-: ]*$', cells[0]) and cells[0]:
            continue
        # 全セルが空または記号のみの行をスキップ
        if all(re.match(r'^[-:= ]*$', c) for c in cells):
            continue

        name        = cells[0] if cells[0] else '不明'
        method      = cells[1] if len(cells) > 1 else ''   # 区分
        index_value = cells[2].strip() if len(cells) > 2 else ''  # 指数（工数）
        wage        = to_int(cells[3]) if len(cells) > 3 else 0  # 技術料
        qty         = to_int(cells[4]) if len(cells) > 4 else 1  # 数量
        parts       = to_int(cells[5]) if len(cells) > 5 else 0  # 部品金額
        part_no     = cells[6].strip() if len(cells) > 6 else ''  # 部品品番

        if wage == 0 and parts == 0:
            continue  # 両方0は除外

        row_idx += 1
        items.append({
            'page':         page_num,
            'row_type':     'detail',
            'name':         name,
            'description':  '',
            'work_code':    method,
            'index_value':  index_value,
            'part_no':      part_no,
            'quantity':     qty if qty > 0 else 1,
            'parts_amount': parts,
            'wage':         wage,
            'line_total':   wage + parts,
            'raw_text':     line,
            'row_id':       f'p{page_num}_r{row_idx:03d}',
            'row_bbox':     {'x1': 0, 'y1': 0, 'x2': 1000, 'y2': 50},
        })
    return items


def analyze_estimate_single(api_key, file_bytes, mime_type, model_name, page_num=1, total_pages=1, tax_inclusive=False):
    """見積書明細行をJSON出力プロンプトで読み取り、itemsリストに変換して返す"""
    extra_notes = ''
    if tax_inclusive:
        extra_notes += '\n\n【税込表記】この見積書は税込表記です。記載されている金額はすべて税込金額として読み取り、そのまま転写してください。税抜きへの変換は不要です。'
    if total_pages > 1:
        extra_notes += f'\n\n【ページ指定】これは全{total_pages}ページ中の{page_num}ページ目です。このページの全明細行を漏れなく読み取ってください。'

    prompt = _build_prompt("estimate_detail_page", extra_notes)

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
                },
            )
            if response.text and response.text.strip():
                # まずJSONパーサーで試みる（新形式）
                items = parse_detail_json_to_items(response.text, page_num)
                # JSONパースが空ならMarkdownフォールバック
                if not items:
                    items = parse_markdown_to_items(response.text, page_num)
                return {
                    'items':           items,
                    'discount_amount': 0,
                    'confidence':      0.9,
                }
            if attempt < 2:
                import time; time.sleep(1)
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
            # クォータ超過エラー
            if '429' in err_msg or 'RESOURCE_EXHAUSTED' in err_msg:
                _quota_exhausted_models.add(model_name)
                cache_key = api_key[-8:] if api_key else ''
                if cache_key in _model_availability_cache:
                    del _model_availability_cache[cache_key]
                raise ValueError(
                    f"モデル '{model_name}' のクォータが上限に達しました。"
                    "自動的に代替モデルに切り替えます。"
                ) from e
            if attempt < 2:
                import time; time.sleep(1)
                continue
            raise ValueError(f"Gemini API呼び出しに失敗しました: {str(last_error)}")


# ============================================================
# チャンク分割解析: 表領域を縦に分割して各チャンクをAIで解析
# ============================================================

def analyze_estimate_chunk(api_key, chunk_bytes, mime_type, model_name,
                           page_num, chunk_idx, total_chunks,
                           y_start_ratio=0.0, y_end_ratio=1.0,
                           table_top_ratio=0.0, table_bot_ratio=1.0):
    """
    チャンク単位で明細行を解析する（analyze_estimate_single のチャンク版）。
    y_start_ratio / y_end_ratio : チャンクが表領域内の何%にあたるか（row_bbox補正用）
    """
    chunk_instruction = (
        f'【チャンク解析】ページ {page_num} の明細表を縦に {total_chunks} 分割した'
        f' {chunk_idx + 1}/{total_chunks} チャンク'
        f'（ページ上端から {y_start_ratio*100:.0f}%〜{y_end_ratio*100:.0f}% の範囲）。\n'
        'このチャンクに含まれる全明細行を漏れなく読み取ってください。\n'
        'row_bbox の y1/y2 はこのチャンク画像内の縦位置（0-1000スケール）で返してください。\n'
    )
    prompt = _build_prompt("estimate_detail_page", chunk_instruction)

    _schema_chunk = {
        "type": "object",
        "properties": {
            "items": {
                "type": "array",
                "items": {
                    "type": "object",
                    "properties": {
                        "name":          {"type": "string"},
                        "description":   {"type": "string"},
                        "method":        {"type": "string"},
                        "quantity":      {"type": "integer"},
                        "parts_amount":  {"type": "integer"},
                        "wage":          {"type": "integer"},
                        "line_total":    {"type": "integer"},
                        "part_no":       {"type": "string"},
                        "work_code":     {"type": "string"},
                        "raw_text":      {"type": "string"},
                        "row_id":        {"type": "string"},
                        "row_bbox": {
                            "type": "object",
                            "properties": {
                                "x1": {"type": "integer"},
                                "y1": {"type": "integer"},
                                "x2": {"type": "integer"},
                                "y2": {"type": "integer"},
                            },
                        },
                    },
                },
            },
            "discount_amount": {"type": "integer"},
        },
    }

    from google.genai import types
    client = _get_genai_client(api_key)
    file_part = types.Part.from_bytes(data=chunk_bytes, mime_type=mime_type)
    for attempt in range(3):
        try:
            response = client.models.generate_content(
                model=model_name,
                contents=[prompt, file_part],
                config={
                    "temperature": 0.0,
                    "max_output_tokens": 32768,
                    "response_mime_type": "application/json",
                    "response_schema": _schema_chunk,
                },
            )
            if response.text and response.text.strip():
                try:
                    res = json.loads(response.text)
                except Exception:
                    res = extract_json_from_response(response.text) or {}
                # row_bbox の y座標をページ全体座標系に変換（0-1000スケール）
                table_range = max(0.01, table_bot_ratio - table_top_ratio)
                chunk_range = max(0.01, y_end_ratio - y_start_ratio)
                for it in res.get('items', []):
                    it['_chunk_idx']    = chunk_idx
                    it['_chunk_y_start'] = y_start_ratio
                    it['_chunk_y_end']   = y_end_ratio
                    bbox = it.get('row_bbox')
                    if bbox and isinstance(bbox, dict):
                        # チャンク内y(0-1000) → ページ内y(0-1000)への変換
                        def _conv_y(vy):
                            # チャンク内相対位置 → 表領域内相対位置 → ページ全体相対位置
                            in_chunk  = vy / 1000.0           # 0-1
                            in_table  = y_start_ratio + in_chunk * chunk_range   # 0-1
                            in_page   = table_top_ratio + in_table * table_range # 0-1
                            return max(0, min(1000, int(in_page * 1000)))
                        it['row_bbox'] = {
                            'x1': bbox.get('x1', 0),
                            'y1': _conv_y(bbox.get('y1', 0)),
                            'x2': bbox.get('x2', 1000),
                            'y2': _conv_y(bbox.get('y2', 0)),
                        }
                return res
            if attempt < 2:
                import time; time.sleep(1)
        except Exception as e:
            err = str(e)
            if 'no longer available' in err or 'NOT_FOUND' in err:
                raise RuntimeError(f"モデル '{model_name}' は利用できません。") from e
            if '429' in err or 'RESOURCE_EXHAUSTED' in err:
                _quota_exhausted_models.add(model_name)
                raise ValueError(f"モデル '{model_name}' クォータ超過") from e
            if attempt < 2:
                import time; time.sleep(1)
    return {"items": [], "discount_amount": 0}


def merge_chunk_items(chunk_results, page_num):
    """
    複数チャンクの items を結合し、重複行を除去して page番号を付与して返す。
    重複判定（3段階）:
      1. raw_text 完全一致（OCR原文が同一 → 確実な重複）
      2. 正規化name(半角化) + (parts, wage) 一致（全角/半角表記ゆれを吸収）
      3. 絶対Y座標近傍 + 合計金額一致（チャンク境界部のOCR揺れを吸収）
    """
    all_items = []
    seen_raw  = set()       # raw_text ベース
    seen_norm = set()       # (normalized_name, parts, wage) ベース
    seen_abs_y = []         # (abs_y, amount_total) リスト（近傍チェック用）
    total_discount = 0
    Y_THRESHOLD = 0.05      # ページ高さの 5% 以内 = 同一行とみなす許容誤差

    for chunk_res in chunk_results:
        total_discount += safe_int(chunk_res.get('discount_amount', 0))
        for it in chunk_res.get('items', []):
            name  = str(it.get('name', '')).strip()
            parts = safe_int(it.get('parts_amount', 0))
            wage  = safe_int(it.get('wage', 0))
            # 完全空行はスキップ
            if not name and parts == 0 and wage == 0:
                continue
            has_amount = (parts > 0 or wage > 0)
            raw        = str(it.get('raw_text', '')).strip()
            norm_name  = to_halfwidth_katakana(name)

            # ── 重複チェック1: raw_text ──────────────────────────
            if raw and has_amount:
                if raw in seen_raw:
                    continue

            # ── 重複チェック2: 正規化name + (parts, wage) ────────
            norm_key = (norm_name, parts, wage)
            if has_amount and norm_key in seen_norm:
                continue

            # ── 重複チェック3: 絶対Y座標近傍 + 合計一致 ──────────
            # チャンクローカル座標(0-1000)→ページ絶対座標(0.0-1.0)に変換して比較
            bbox       = it.get('row_bbox', {})
            local_y1   = float(bbox.get('y1', -1))
            chunk_y_s  = float(it.get('_chunk_y_start', 0))
            chunk_y_e  = float(it.get('_chunk_y_end', 1))
            amt_total  = parts + wage
            is_y_dup   = False
            if local_y1 >= 0 and has_amount:
                abs_y = chunk_y_s + (local_y1 / 1000.0) * (chunk_y_e - chunk_y_s)
                for prev_y, prev_amt in seen_abs_y:
                    if abs(abs_y - prev_y) <= Y_THRESHOLD and prev_amt == amt_total:
                        is_y_dup = True
                        break
                if is_y_dup:
                    continue

            # ── 重複なし → 登録 ──────────────────────────────────
            if raw and has_amount:
                seen_raw.add(raw)
            if has_amount:
                seen_norm.add(norm_key)
            if local_y1 >= 0 and has_amount:
                seen_abs_y.append((abs_y, amt_total))

            it['page'] = page_num
            all_items.append(it)
    return all_items, total_discount


def analyze_page_with_chunks(api_key, page_bytes, mime_type, model_name,
                              page_num, total_pages, n_chunks=3):
    """
    1ページ分の画像を表領域検出 → チャンク分割 → 各チャンク解析 → マージ するパイプライン。
    JPEG画像でない場合は analyze_estimate_single にフォールバック。
    """
    # JPEG/PNG 画像でない場合はフォールバック
    if mime_type not in ('image/jpeg', 'image/png'):
        return analyze_estimate_single(api_key, page_bytes, mime_type, model_name, page_num, total_pages)

    # ① 表領域を検出してクロップ
    try:
        table_bytes, table_top, table_bot = detect_table_region(page_bytes)
    except Exception:
        table_bytes, table_top, table_bot = page_bytes, 0.0, 1.0

    # ② 縦分割（チャンク数は行数に応じて調整: 小さい画像は分割不要）
    try:
        from PIL import Image
        _pil = Image.open(io.BytesIO(table_bytes))
        _h = _pil.height
        actual_chunks = n_chunks if _h >= 600 else (2 if _h >= 300 else 1)
    except Exception:
        actual_chunks = n_chunks

    chunks = split_into_vertical_chunks(table_bytes, n_chunks=actual_chunks, overlap_ratio=0.02)

    # ③ 各チャンクをAPIで解析（並列処理）
    def _analyze_one_chunk(args):
        ci, (cb, y_start, y_end) = args
        try:
            return analyze_estimate_chunk(
                api_key, cb, 'image/jpeg', model_name,
                page_num, ci, actual_chunks,
                y_start_ratio=y_start, y_end_ratio=y_end,
                table_top_ratio=table_top, table_bot_ratio=table_bot,
            )
        except Exception as e:
            import sys
            print(f"[WARN] チャンク{ci+1}解析失敗 (page={page_num}): {e}", file=sys.stderr)
            return {"items": [], "discount_amount": 0}

    chunk_results = []
    if actual_chunks == 1:
        # チャンク分割不要: ページ全体画像（クロップなし）をシンプルプロンプトで解析
        chunk_results = [analyze_estimate_single(
            api_key, page_bytes, 'image/jpeg', model_name, page_num, total_pages
        )]
    else:
        with ThreadPoolExecutor(max_workers=min(actual_chunks, 3)) as _cx:
            chunk_results = list(_cx.map(_analyze_one_chunk, enumerate(chunks)))

    # ④ マージして重複除去
    merged_items, merged_discount = merge_chunk_items(chunk_results, page_num)

    # ⑤ 結果が空ならフォールバック
    if not merged_items:
        return analyze_estimate_single(api_key, page_bytes, mime_type, model_name, page_num, total_pages)

    return {
        "items":           merged_items,
        "discount_amount": merged_discount,
        "confidence":      0.85,
        "_chunked":        True,
        "_chunk_count":    actual_chunks,
    }




def validate_and_correct_items(items):
    """
    辞書ベースバリデーション: AIの誤分類を後処理で修正する。

    【部品価格計上の必須ルール】
    基本ルール: 部品価格を計上するのは、作業内容（method）が「取替」の場合のみ。
    例外ルール: 作業内容が空白でも、部品価格欄に金額がある場合は「取替」とみなし計上。
    それ以外（脱着・修理・板金等）の場合、parts_amount は強制的に 0 とする。
    これにより「脱着」行の空欄によって次行の金額がズレて取り込まれる連鎖エラーを防ぐ。

    【作業区分ごとの挙動】
    - 取替/交換系:    parts_amount 有効（工賃も同行にある場合はそのまま）
    - 脱着/取外系:    parts_amount = 0 強制（部品代なし）。工賃はそのまま保持。
    - 修理/板金等:    parts_amount = 0 強制。wage==0 のとき parts_amt を wage へ移動
                      （AIが工賃を parts 列に誤分類したケースを救済）
    - 空白method:     parts_amount > 0 ならそのまま（取替とみなす）
    """
    # 部品代計上が有効な作業区分
    PARTS_OK_METHODS = {'取替', '交換', '脱着組替', '取外組付'}

    # 脱着系: parts_amount を 0 に強制。工賃は保持。wage への移動も行わない。
    REMOVAL_METHODS  = {'脱着', '取外', '取付', '組付', '脱外'}

    # 修理・塗装系: parts_amount = 0 強制。wage==0 なら parts_amt を wage へ移動
    REPAIR_METHODS   = {'修理', '調整', '板金', '塗装', 'ペイント', '研磨',
                        '清掃', '点検', '作業', '修正', '施工', '補修'}

    corrected = []
    for item in items:
        item      = dict(item)
        method    = str(item.get('method', '')).strip()
        name      = str(item.get('name', ''))
        parts_amt = safe_int(item.get('parts_amount', 0))
        wage      = safe_int(item.get('wage', 0))

        # ケース1: 取替/交換系 → 部品代・工賃ともに有効（変更なし）
        if any(kw in method for kw in PARTS_OK_METHODS):
            corrected.append(item)
            continue

        # ケース2: 作業内容空白 + 部品価格あり → 「取替」とみなしそのまま計上
        if not method and parts_amt > 0:
            corrected.append(item)
            continue

        # ケース3: 脱着/取外系 → parts_amount を強制ゼロ（wage は触らない）
        is_removal = any(kw in method for kw in REMOVAL_METHODS)
        is_removal_name = any(kw in name for kw in {'脱着', '取外', '取付', '組付'})
        if is_removal or is_removal_name:
            item['parts_amount'] = 0
            corrected.append(item)
            continue

        # ケース4: 修理・塗装等 → parts_amount = 0 強制。wage==0 なら wage へ救済移動
        is_repair = any(kw in method for kw in REPAIR_METHODS)
        is_repair_name = any(kw in name for kw in {'板金', '塗装', 'ペイント', '修理', '研磨'})
        if (is_repair or is_repair_name) and parts_amt > 0:
            if wage == 0:
                # AIが工賃を parts 列に誤分類したとみなして wage へ移動
                item['wage']  = parts_amt
            item['parts_amount'] = 0

        corrected.append(item)
    return corrected


def check_parts_labor_classification(items):
    """
    部品/工賃区分の疑わしい行を検出する。
    AI抽出結果の parts_amount / wage の割り当てが不自然な行をフラグ付きで返す。

    検出パターン:
    1. 「脱着」「取外」系の行に parts_amount > 0 がある（脱着に部品代は不要）
    2. 「材料」「ウレタン」「シーリング」等の材料系名称なのに wage > 0, parts_amount = 0
       （材料費は部品・油脂列に入るべき）
    3. 両方ゼロの行（金額未読み取りの可能性）
    4. 「修理」「板金」「塗装」等の作業系なのに parts_amount > 0, wage = 0
       （作業費は技術料列に入るべき）

    Returns: list of dicts {
        'row_no': int,      # 1始まりの行番号
        'name': str,        # 品名
        'parts_amount': int,
        'wage': int,
        'flag': str,        # 'parts_in_labor' / 'labor_in_parts' / 'both_zero' / 'ambiguous'
        'message': str,     # 日本語の警告メッセージ
        'severity': str,    # 'error' / 'warning'
    }
    """
    # 脱着系キーワード（部品代なし）
    REMOVAL_KW = {'脱着', '取外', '取付', '組付', '脱外'}
    # 材料系キーワード（部品・油脂列に入るべき）
    MATERIAL_KW = {'ウレタン', 'シーリング', 'アンダーコート', '防錆', '塗料', '材料',
                   '充填', '発泡', '発砲', 'パネルボンド', '接着', '油脂', 'オイル'}
    # 作業・修理系キーワード（技術料列に入るべき）
    WORK_KW = {'修理', '板金', 'ペイント', '研磨', '塗装', '清掃', '点検', '作業', '施工', '補修'}

    alerts = []
    for i, item in enumerate(items):
        name      = str(item.get('name', '')).strip()
        method    = str(item.get('method', '')).strip()
        parts_amt = safe_int(item.get('parts_amount', 0))
        wage      = safe_int(item.get('wage', 0))
        row_no    = i + 1

        base = {'row_no': row_no, 'name': name, 'parts_amount': parts_amt, 'wage': wage}

        # パターン1: 脱着系で parts_amount > 0
        if any(kw in name or kw in method for kw in REMOVAL_KW) and parts_amt > 0:
            alerts.append({**base,
                'flag': 'parts_in_labor',
                'message': f'行{row_no}「{name}」: 脱着系作業なのに部品金額 ¥{parts_amt:,} が計上されています。'
                           '技術料欄の値が誤って部品欄に入った可能性があります。',
                'severity': 'error'
            })
            continue

        # パターン2: 材料系名称で wage > 0 かつ parts_amount = 0
        if any(kw in name for kw in MATERIAL_KW) and wage > 0 and parts_amt == 0:
            alerts.append({**base,
                'flag': 'labor_in_parts',
                'message': f'行{row_no}「{name}」: 材料系品名なのに工賃 ¥{wage:,} のみ計上されています。'
                           '部品・油脂列の値が誤って技術料欄に入った可能性があります。',
                'severity': 'error'
            })
            continue

        # パターン3: 作業系名称で parts_amount > 0 かつ wage = 0 （取替除く）
        if any(kw in name or kw in method for kw in WORK_KW):
            if parts_amt > 0 and wage == 0 and '取替' not in method and '交換' not in method:
                alerts.append({**base,
                    'flag': 'parts_in_labor',
                    'message': f'行{row_no}「{name}」: 作業系名称なのに部品金額 ¥{parts_amt:,} のみ計上されています。'
                               '技術料列の値が誤って部品欄に入った可能性があります。',
                    'severity': 'warning'
                })
                continue

        # パターン4: 両方ゼロ（品名があるのに金額なし）
        if parts_amt == 0 and wage == 0 and name:
            zero_ok = {'脱着', '取外', '取付', '組付', '点検', '調整', '清掃'}
            if not any(kw in name or kw in method for kw in zero_ok):
                alerts.append({**base,
                    'flag': 'both_zero',
                    'message': f'行{row_no}「{name}」: 部品金額・工賃ともに0円です。金額の読み取り漏れがないか確認してください。',
                    'severity': 'warning'
                })

    return alerts


def extract_special_items(items, existing_sp=0, existing_exempt=0):
    """
    【廃止済み: 特殊分離は行わない】
    明細欄に記載されている行はすべて items として通過させる。
    ショートパーツ・雑品代・預託金・廃棄処分費用も通常明細として扱う。
    Returns: (items, 0, 0)  ← 常に元のリストをそのまま返す
    """
    return list(items), 0, 0


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


def deduplicate_page_boundary_items(all_items, boundary_indices):
    """
    ページ境界付近でのみ重複行を除去する。
    同一ページ内の重複行はPDF原本通り全て保持する（ユーザー指定）。
    boundary_indices: 各ページの先頭インデックスのリスト
    """
    if len(all_items) <= 1:
        return all_items
    boundary_set = set(boundary_indices)
    result = []
    skip_next = False
    for i, item in enumerate(all_items):
        if skip_next:
            skip_next = False
            continue
        # このインデックスがページ境界（ページ先頭）かつ前の行と内容が同じなら除去
        if i in boundary_set and result:
            prev = result[-1]
            same_name  = str(item.get('name', '')).strip() == str(prev.get('name', '')).strip()
            same_parts = safe_int(item.get('parts_amount', 0)) == safe_int(prev.get('parts_amount', 0))
            same_wage  = safe_int(item.get('wage', 0))         == safe_int(prev.get('wage', 0))
            if same_name and same_parts and same_wage and str(item.get('name', '')).strip():
                continue  # ページ境界重複 → スキップ
        result.append(item)
    return result


def global_dedup_items(items):
    """
    全ページ横断の重複行除去。
    ページ境界に限らず、全 items の中で重複を検出して除去する。

    除去ルール:
      0. raw_text が完全一致 → 後出の行を除去（チャンク境界の重複対策）
      1. (normalized_name, parts_amount, wage) が一致 → 後出の行を除去
         ※ normalized_name は to_halfwidth_katakana で正規化（全角/半角の違いを吸収）
      2. name が「不明」または空欄 の行と、同一 (parts_amount, wage) を持つ
         名前付き行が存在する場合 → 「不明」側を除去（OCR誤読を優先排除）
    """
    # Pass0: raw_text ベースの重複除去（チャンク分割のオーバーラップ起因重複を除去）
    seen_raw = set()
    pass0 = []
    for it in items:
        raw   = str(it.get('raw_text', '')).strip()
        parts = safe_int(it.get('parts_amount', 0))
        wage  = safe_int(it.get('wage', 0))
        if parts == 0 and wage == 0:
            pass0.append(it)
            continue
        if raw:
            if raw in seen_raw:
                continue
            seen_raw.add(raw)
        pass0.append(it)

    # Pass1: 正規化name + (parts, wage) による重複除去（全角/半角の表記ゆれを吸収）
    seen_exact = set()
    pass1 = []
    for it in pass0:
        name  = to_halfwidth_katakana(str(it.get('name', ''))).strip()
        parts = safe_int(it.get('parts_amount', 0))
        wage  = safe_int(it.get('wage', 0))
        if parts == 0 and wage == 0:
            pass1.append(it)
            continue
        key = (name, parts, wage)
        if key in seen_exact:
            continue
        seen_exact.add(key)
        pass1.append(it)

    # Pass2: 「不明」行 vs 名前付き行の同一金額重複除去
    named_amount_keys = set()
    for it in pass1:
        name  = str(it.get('name', '')).strip()
        parts = safe_int(it.get('parts_amount', 0))
        wage  = safe_int(it.get('wage', 0))
        if name and name != '不明' and (parts > 0 or wage > 0):
            named_amount_keys.add((parts, wage))

    pass2 = []
    for it in pass1:
        name  = str(it.get('name', '')).strip()
        parts = safe_int(it.get('parts_amount', 0))
        wage  = safe_int(it.get('wage', 0))
        if name in ('不明', '') and (parts, wage) in named_amount_keys:
            continue  # 「不明」行と同額の名前付き行が存在 → 「不明」側を除去
        pass2.append(it)

    return pass2


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
                           user_tax_basis='tax_exclusive'):
    """
    税区分はUIユーザー選択値のみを使用してNEO書込み用正規化サマリーを返す。
    （AI自動判定は廃止。user_tax_basis='tax_inclusive' または 'tax_exclusive'）
    Returns: {
      'basis': 'tax_inclusive' / 'tax_exclusive',
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

    # 税区分はUIユーザー選択値のみを使用（AI判定廃止）
    basis = user_tax_basis if user_tax_basis in ('tax_inclusive', 'tax_exclusive') else 'tax_exclusive'

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

    TOLERANCE = 50  # 円
    reverse_grand = round((norm_parts + norm_wage + norm_sp - norm_disc) * (1 + TAX_RATE))
    reverse_match = abs(reverse_grand - grand) <= TOLERANCE if grand > 0 else False

    return {
        'basis':         basis,
        'norm_parts':    norm_parts,
        'norm_wage':     norm_wage,
        'norm_sp':       norm_sp,
        'norm_disc':     norm_disc,
        'grand':         grand,
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

    _extra = (
        f"【検出された誤差】\n"
        f"- 部品合計: 計算値 ¥{calc_parts:,} ≠ PDF記載 ¥{target_parts:,} （差額 {parts_diff:+,}円）\n"
        f"- 工賃合計: 計算値 ¥{calc_wage:,} ≠ PDF記載 ¥{target_wage:,} （差額 {wage_diff:+,}円）\n\n"
        f"【修復指示】\n"
        f"- 部品金額を合計{abs(parts_diff):,}円分{'追加' if parts_diff < 0 else '削減'}すること\n"
        f"- 工賃を合計{abs(wage_diff):,}円分{'追加' if wage_diff < 0 else '削減'}すること\n"
    )
    correction_prompt = _build_prompt("estimate_validation_repair", _extra)
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
        new_items  = new_result.get('items', []) or new_result.get('details', [])
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


def extract_honda_cars_subtotals(file_bytes):
    """
    Honda Cars形式PDFから pypdf テキスト解析で部品/工賃合計を確実に抽出する。
    Geminiが誤読するケースを防ぐため、pypdfのテキスト抽出結果を使用する。

    pypdf特有のパターン:
      - 「小      計 195,398 482,976」行 → 最終的な部品/工賃合計
      - 「ページ小計 140,547 175,246」行 → ページ別小計（全ページを加算）

    戻り値: (parts_total, wages_total) または None（Honda Cars形式でない場合）
    """
    import re
    try:
        from pypdf import PdfReader
        import io as _io
        reader = PdfReader(_io.BytesIO(file_bytes))
    except Exception:
        return None

    all_text = ''
    for page in reader.pages:
        try:
            t = page.extract_text() or ''
            all_text += t + '\n'
        except Exception:
            pass

    if not all_text.strip():
        return None

    # Honda Cars形式を識別: 「部品価格(税込)」列ヘッダが存在する
    if '部品価格(税込)' not in all_text and '部品価格（税込）' not in all_text:
        return None

    # パターン1: 「小      計 195,398 482,976」（最終合計行・スペース多め）
    m = re.search(r'小\s{2,}計\s+([\d,]+)\s+([\d,]+)', all_text)
    if m:
        parts = int(m.group(1).replace(',', ''))
        wages = int(m.group(2).replace(',', ''))
        if parts > 0 or wages > 0:
            return (parts, wages)

    # パターン2: 「小計 NNN NNN」（スペース少ない場合）
    m = re.search(r'小\s*計\s+([\d,]+)\s+([\d,]+)', all_text)
    if m:
        parts = int(m.group(1).replace(',', ''))
        wages = int(m.group(2).replace(',', ''))
        if parts > 0 or wages > 0:
            return (parts, wages)

    # パターン3: ページ小計を全ページ合算
    page_totals = re.findall(r'ページ小計\s+([\d,]+)\s+([\d,]+)', all_text)
    if page_totals:
        total_parts = sum(int(p.replace(',', '')) for p, w in page_totals)
        total_wages = sum(int(w.replace(',', '')) for p, w in page_totals)
        if total_parts > 0 or total_wages > 0:
            return (total_parts, total_wages)

    return None


def analyze_estimate(api_key, file_bytes, mime_type, model_name=None,
                     use_fax_filter=False, use_rasterize=False, use_enhance=True,
                     enable_self_correction=True, progress_cb=None):
    """
    見積書をAI-OCRで解析するメイン関数。
    progress_cb: (pct: int, text: str) -> None  進捗コールバック（Noneなら使用しない）
    新機能:
      use_fax_filter: FAXページを自動除外する（追加APIコール1回）
      use_rasterize: PDF→JPEG変換してから送信（行ズレ防止）
    """
    import hashlib, sys
    used_model = model_name or GEMINI_MODEL
    _log: list = []  # 解析ログ収集リスト

    def _logw(msg: str):
        """ログをリストと stderr 両方に出力する"""
        _log.append(msg)
        print(f"[ANALYZE] {msg}", file=sys.stderr)

    # ── ファイルハッシュキャッシュ: 同一ファイルの再解析を防ぐ ──────────────
    _cache_key = (hashlib.md5(file_bytes).hexdigest()
                  + f"_{used_model}_{use_rasterize}_{use_fax_filter}_{use_enhance}_{enable_self_correction}")
    def _cb(pct, text):
        """進捗コールバック呼び出し（Noneなら何もしない）"""
        if progress_cb:
            try:
                progress_cb(pct, text)
            except Exception:
                pass

    if _cache_key in _analyze_result_cache:
        print("[INFO] キャッシュヒット: 再解析をスキップします", file=sys.stderr)
        return _analyze_result_cache[_cache_key]
    # ──────────────────────────────────────────────────────────────────────────

    # クォータ超過モデルを除外して使用モデルを決定
    if used_model in _quota_exhausted_models:
        # 代替モデルを選択
        for alt_model in _PREFERRED_MODELS:
            if alt_model not in _quota_exhausted_models:
                print(f"[INFO] モデル '{used_model}' はクォータ超過のため '{alt_model}' に切り替えます", file=sys.stderr)
                used_model = alt_model
                break

    _logw(f"🤖 使用モデル: {used_model}")
    _logw(f"📂 ファイルサイズ: {len(file_bytes):,} bytes / MIMEタイプ: {mime_type}")
    _logw(f"⚙️ オプション: FAXフィルター={'ON' if use_fax_filter else 'OFF'} / ラスタライズ={'ON' if use_rasterize else 'OFF'} / 自己修復={'ON' if enable_self_correction else 'OFF'}")

    # ① FAXページフィルタリング（オプション）
    _cb(8, "① FAXページを確認中...")
    filtered_count = 0
    if use_fax_filter and mime_type == 'application/pdf':
        original_size = len(file_bytes)
        file_bytes    = filter_fax_pages(api_key, file_bytes, used_model)
        if len(file_bytes) < original_size:
            filtered_count = 1
    _logw(f"① FAXフィルター: {'1ページ除外' if filtered_count > 0 else '除外なし'}")

    # ② 横向きPDF補正
    _cb(12, "② ページ補正・分割中...")
    if mime_type == 'application/pdf':
        file_bytes = try_fix_landscape_pdf(file_bytes)

    # ③ ページ分割
    pages = try_split_pdf_pages(file_bytes) if mime_type == 'application/pdf' else None
    # ③-a ページ順序自動補正（FAXヘッダ等で逆順になっている場合を修正）
    if pages and len(pages) > 1:
        pages = detect_and_reorder_pages(pages)
    _logw(f"③ ページ分割: {len(pages) if pages else 1}ページ")

    # ③-b&c ラスタライズ: PDF→JPEG変換（行ズレ防止）
    # 最終ページ（合計欄）と1ページ目（車両情報）を並列でラスタライズ
    raster_bytes       = file_bytes
    raster_mime        = mime_type
    first_raster_bytes = file_bytes
    first_raster_mime  = mime_type
    if use_rasterize and mime_type == 'application/pdf':
        try:
            from pypdf import PdfReader
            num_pages = len(PdfReader(io.BytesIO(file_bytes)).pages)
        except Exception:
            num_pages = 1
        last_page_idx = max(0, num_pages - 1)
        # 最終ページと1ページ目を並列ラスタライズ（直列から並列化 → ~2s節約）
        def _raster_last(_):
            return rasterize_pdf_page(file_bytes, last_page_idx, dpi=300, enhance=use_enhance)
        def _raster_first(_):
            return rasterize_pdf_page(file_bytes, 0, dpi=300, enhance=use_enhance)
        with ThreadPoolExecutor(max_workers=2) as _ex:
            _fut_last  = _ex.submit(_raster_last, None)
            _fut_first = _ex.submit(_raster_first, None)
            img  = _fut_last.result()
            img1 = _fut_first.result()
        if img:
            raster_bytes = img
            raster_mime  = 'image/jpeg'
        if img1:
            first_raster_bytes = img1
            first_raster_mime  = 'image/jpeg'

    # ④ 1パス目: 合計値＋車両情報抽出
    _cb(20, "③ 合計金額・車両情報を読み取り中...（10〜20秒）")
    # 合計欄は最終ページ、車両情報は1ページ目にあることが多い
    # 複数ページの場合は最終ページと1ページ目を並列でAPI呼び出し（直列から並列化 → ~10s節約）
    _need_first_page = bool(pages and len(pages) > 1 and first_raster_bytes != raster_bytes)
    if _need_first_page:
        with ThreadPoolExecutor(max_workers=2) as _ex:
            _fut_totals = _ex.submit(
                analyze_estimate_totals, api_key, raster_bytes, raster_mime, used_model)
            _fut_first  = _ex.submit(
                analyze_estimate_totals, api_key, first_raster_bytes, first_raster_mime, used_model)
            totals_data     = _fut_totals.result() or {}
            first_page_data = _fut_first.result() or {}
    else:
        totals_data = analyze_estimate_totals(api_key, raster_bytes, raster_mime, used_model) or {}
    if _need_first_page:
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
    _logw(f"④ 合計抽出: 部品計={target_parts:,} / 工賃計={target_wage:,} / 総合計={pdf_grand:,} / 値引={discount:,}")

    # ④-a Honda Cars形式: pypdfで正確な合計値を取得（Gemini誤読を防ぐ）
    # Geminiは「小計 195,398 482,976」の数値を誤認することがある。
    # pypdf解析は列レイアウトに依存しないため確実。
    if mime_type == 'application/pdf':
        _pypdf_totals = extract_honda_cars_subtotals(file_bytes)
        if _pypdf_totals:
            _pypdf_parts, _pypdf_wages = _pypdf_totals
            import sys
            print(f"[INFO] Honda Cars pypdf合計: 部品={_pypdf_parts:,}, 工賃={_pypdf_wages:,} "
                  f"(Gemini推測: 部品={target_parts:,}, 工賃={target_wage:,})", file=sys.stderr)
            target_parts = _pypdf_parts
            target_wage  = _pypdf_wages
            totals_data['pdf_parts_total'] = _pypdf_parts
            totals_data['pdf_wage_total']  = _pypdf_wages

    # ⑤ 2パス目: 明細抽出（PDF全ページを一括送信 — ページ境界ズレを防ぐ）
    _cb(45, f"④ 明細行を解析中...（{len(pages) if pages else 1}ページ / 30秒〜2分かかる場合があります）")
    _page_count = len(pages) if pages else 1
    _logw(f"⑤ 全ページ一括解析開始 ({_page_count}ページ)")
    result = analyze_estimate_single(
        api_key, file_bytes, 'application/pdf', used_model, 1, _page_count
    ) or {}
    result.setdefault('items', [])
    result.setdefault('short_parts_wage', 0)
    result['pdf_parts_total']   = target_parts or safe_int(result.get('pdf_parts_total', 0))
    result['pdf_wage_total']    = target_wage  or safe_int(result.get('pdf_wage_total', 0))
    result['pdf_grand_total']   = pdf_grand    or safe_int(result.get('pdf_grand_total', 0))
    result['discount_amount']   = discount     or safe_int(result.get('discount_amount', 0))
    result['confidence']        = safe_float(result.get('confidence', 0.5))
    result['_fax_filtered']     = filtered_count
    result['_page_count']       = _page_count
    result['_vehicle_info']     = totals_data.get('vehicle_info', {})
    result['_repair_shop_name'] = totals_data.get('repair_shop_name', '')
    _p = sum(safe_int(it.get('parts_amount', 0)) for it in result['items'])
    _w = sum(safe_int(it.get('wage', 0)) for it in result['items'])
    _logw(f"  → {len(result['items'])}行 / 部品={_p:,} / 工賃={_w:,}")

    _cb(80, "⑤ データを整理中...")
    # ⑥ 全ページ横断重複除去（AI出力のページ先読み・同一行二重出力を除去）
    # ページ境界に限らず全行を対象にした重複除去。
    # ・Page1のAIがPage2の明細を合計額に合わせて先読み出力するケースを防止
    # ・同一ページ内で先頭数行を2回出力するAIの誤動作を防止
    _before_dedup = len(result['items'])
    result['items'] = global_dedup_items(result['items'])
    _after_dedup = len(result['items'])
    _logw(f"⑥ 全体重複除去: {_before_dedup}行 → {_after_dedup}行 ({_before_dedup - _after_dedup}件除去)")

    # ⑥-b 辞書ベースバリデーション
    result['items'] = validate_and_correct_items(result['items'])

    # ⑥-c 品名空白フォールバック（AIが名称を読み取れなかった行を保護）
    # work_code が非空なら品名の代替として使用し、それもなければ「不明」を設定
    for _it in result['items']:
        if not str(_it.get('name', '')).strip():
            _wc = str(_it.get('work_code', '')).strip()
            _it['name'] = _wc if _wc else '不明'

    # ⑥-d 明細行ごとの整合性チェック
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

    # ⑥-d スキャンPDF等でpypdf取得失敗時のクロスバリデーション
    # Geminiが誤った小計値を返した場合（スキャンPDF等）、明細合算＋grand_totalで検証して上書き
    _cv_items_nd = [it for it in result['items'] if it.get('name') != '値引き']
    _cv_calc_p   = sum(safe_int(it.get('parts_amount', 0)) for it in _cv_items_nd)
    _cv_calc_w   = sum(safe_int(it.get('wage', 0))         for it in _cv_items_nd)
    _cv_sp       = safe_int(result.get('short_parts_wage', 0))
    _cv_grand    = safe_int(result.get('pdf_grand_total', 0))
    _cv_p_stated = safe_int(result.get('pdf_parts_total', 0))
    _cv_w_stated = safe_int(result.get('pdf_wage_total', 0))
    if _cv_p_stated > 0 and _cv_w_stated > 0 and _cv_grand > 0 and _cv_calc_p > 0:
        _cv_item_total = _cv_calc_p + _cv_calc_w + _cv_sp
        # 明細合算＋sp が grand_total に近い（2%以内）か確認
        _cv_match_grand = abs(_cv_item_total - _cv_grand) / _cv_grand < 0.02
        # Geminiのstated totalsが明細合算と大きくずれているか（10%超）
        _cv_p_wrong = abs(_cv_calc_p - _cv_p_stated) / max(_cv_calc_p, 1) > 0.10
        _cv_w_wrong = abs(_cv_calc_w + _cv_sp - _cv_w_stated) / max(_cv_calc_w + _cv_sp, 1) > 0.10
        if _cv_match_grand and (_cv_p_wrong or _cv_w_wrong):
            import sys as _sys_cv
            print(f"[INFO] cross-validation: Gemini stated totals誤り検出 → 明細合算値で上書き", file=_sys_cv.stderr)
            print(f"  Gemini: 部品={_cv_p_stated:,}, 工賃={_cv_w_stated:,}", file=_sys_cv.stderr)
            print(f"  明細合算: 部品={_cv_calc_p:,}, 工賃={_cv_calc_w+_cv_sp:,} (sp={_cv_sp:,}), 合計={_cv_item_total:,}≈{_cv_grand:,}", file=_sys_cv.stderr)
            result['pdf_parts_total'] = _cv_calc_p
            result['pdf_wage_total']  = _cv_calc_w + _cv_sp

    # ⑦ 自己修復ループ（合計値が取得できた場合のみ、最大2回）
    # enable_self_correction=False（ベタ打ちモード等）の場合はスキップして高速化
    if enable_self_correction and (result['pdf_parts_total'] > 0 or result['pdf_wage_total'] > 0):
        _correction_rounds = 0
        for _sc_round in range(2):
            _cur_items = result['items']
            _cur_parts = sum(safe_int(it.get('parts_amount', 0)) for it in _cur_items)
            _cur_wage  = sum(safe_int(it.get('wage', 0))         for it in _cur_items)
            _sc_sp     = safe_int(result.get('short_parts_wage', 0))
            _p_diff = abs(_cur_parts - result['pdf_parts_total'])
            # 工賃比較はショートパーツを加味（Honda Cars等でspが工賃列に含まれるため）
            _w_diff = abs((_cur_wage + _sc_sp) - result['pdf_wage_total'])
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

    # ⑧ 税区分はUIユーザー選択値のみを使用（AI自動判定廃止）
    # 注: analyze_estimate 呼び出し後にセッションstate(tax_override)で上書きされる（line 4580付近）
    # ここでは仮に tax_exclusive を設定しておき、後段のUI処理で正式に上書きされる
    summary = build_estimate_summary(
        result['items'],
        result.get('short_parts_wage', 0),
        result.get('pdf_parts_total', 0),
        result.get('pdf_wage_total', 0),
        result.get('pdf_grand_total', 0),
        result.get('discount_amount', 0),
        user_tax_basis='tax_exclusive',  # 後段UIで上書きされる仮値
    )
    result['_tax_basis']     = summary['basis']
    result['_reverse_match'] = summary['reverse_match']
    # _is_tax_inclusive は後段のUIオーバーライドで設定されるため、ここでは設定しない

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
    # doc=0 は「PDF未記載」扱い → 不一致カウントしない
    p_mismatch = (doc_p > 0) and (p_diff != 0)
    w_mismatch = (doc_w > 0) and (w_diff != 0)
    is_match = (not p_mismatch and not w_mismatch)
    # Geminiが返したtotals_verificationがある場合はそちらを優先
    if not result.get('totals_verification'):
        _err_parts = []
        if p_mismatch: _err_parts.append(f'部品差額{p_diff:+,}円')
        if w_mismatch: _err_parts.append(f'工賃差額{w_diff:+,}円')
        result['totals_verification'] = {
            'calculated_parts_total': calc_p,
            'calculated_labor_total': calc_w,
            'document_parts_total':   doc_p,
            'document_labor_total':   doc_w,
            'parts_diff':             p_diff if doc_p > 0 else 0,
            'labor_diff':             w_diff if doc_w > 0 else 0,
            'is_match':               is_match,
            'validation_error':       '・'.join(_err_parts) if _err_parts else None,
        }
    else:
        # Gemini返却値がある場合も、PDF未記載(=0)の工賃・部品は不一致扱いしない
        _tv = result['totals_verification']
        _tv_doc_p = safe_int(_tv.get('document_parts_total', 0))
        _tv_doc_w = safe_int(_tv.get('document_labor_total', 0))
        _tv_p_diff = safe_int(_tv.get('parts_diff', 0))
        _tv_w_diff = safe_int(_tv.get('labor_diff', 0))
        if _tv_doc_w == 0 and _tv_w_diff != 0:
            _tv['labor_diff'] = 0
        if _tv_doc_p == 0 and _tv_p_diff != 0:
            _tv['parts_diff'] = 0
        _tv_p_mis = (_tv_doc_p > 0) and (_tv['parts_diff'] != 0)
        _tv_w_mis = (_tv_doc_w > 0) and (_tv['labor_diff'] != 0)
        _tv['is_match'] = not _tv_p_mis and not _tv_w_mis
        _err_parts = []
        if _tv_p_mis: _err_parts.append(f'部品差額{_tv["parts_diff"]:+,}円')
        if _tv_w_mis: _err_parts.append(f'工賃差額{_tv["labor_diff"]:+,}円')
        _tv['validation_error'] = '・'.join(_err_parts) if _err_parts else None
        result['totals_verification'] = _tv

    # 最終集計ログ
    _final_items = result.get('items', [])
    _final_p = sum(safe_int(it.get('parts_amount', 0)) for it in _final_items)
    _final_w = sum(safe_int(it.get('wage', 0)) for it in _final_items)
    _final_total = _final_p + _final_w
    _final_grand = safe_int(result.get('pdf_grand_total', 0))
    _diff = _final_total - _final_grand
    _match_str = "✅ 完全一致" if abs(_diff) <= 1 else f"⚠️ 差額 {_diff:+,}円"
    _logw(f"─────────────────────────────")
    _logw(f"📊 最終結果: {len(_final_items)}行 / 部品={_final_p:,} / 工賃={_final_w:,} / 計={_final_total:,}")
    _logw(f"  PDF総合計={_final_grand:,} → {_match_str}")
    result['_analysis_log'] = _log

    # ── 解析ログをファイルに書き出し ──────────────────────────────────────────
    try:
        _ts = datetime.datetime.now().strftime('%Y-%m-%d %H:%M:%S')
        with open(ANALYSIS_LOG_PATH, 'a', encoding='utf-8') as _lf:
            _lf.write(f"\n{'='*60}\n")
            _lf.write(f"[{_ts}] 解析開始\n")
            for _entry in _log:
                _lf.write(f"  {_entry}\n")
            _lf.write(f"[{_ts}] 解析終了\n")
    except Exception as _le:
        print(f"[WARN] analysis.log 書き込み失敗: {_le}", file=sys.stderr)
    # ──────────────────────────────────────────────────────────────────────────

    # ── キャッシュ保存 ──────────────────────────────────────────────────────────
    _analyze_result_cache[_cache_key] = result
    # キャッシュが大きくなりすぎないよう古いエントリを削除（最大20件）
    while len(_analyze_result_cache) > 20:
        oldest_key = next(iter(_analyze_result_cache))
        del _analyze_result_cache[oldest_key]
    # ──────────────────────────────────────────────────────────────────────────

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

    /* 上部の余白を完全に詰める */
    .block-container { padding-top: 0px !important; margin-top: 0px !important; }
    header[data-testid="stHeader"] { display: none !important; height: 0 !important; }
    #root > div:first-child { padding-top: 0 !important; }
    .stApp > header { display: none !important; }
    .stApp { margin-top: 0 !important; }
    section.main > div { padding-top: 0 !important; }

    /* file_uploader の「Drag and drop」「Limit」テキストを非表示（複数セレクタで対応） */
    [data-testid="stFileUploaderDropzoneInstructions"] { display: none !important; }
    [data-testid="stFileUploaderDropzone"] small,
    [data-testid="stFileUploaderDropzone"] span:not(.st-emotion-cache-9ycgxx),
    .uploadedFileName ~ small,
    section[data-testid="stFileUploaderDropzone"] div > small { display: none !important; }
    [data-testid="stFileUploaderDropzone"] { min-height: 56px !important; padding: 8px 12px !important; }
    /* アイコンとBrowseボタンだけ残す */
    [data-testid="stFileUploaderDropzone"] > div > div:first-child > span { display: none !important; }
    [data-testid="stFileUploaderDropzone"] > div > div:first-child > small { display: none !important; }

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

    # テンプレートチェック（キャッシュ付き — 毎リランで再読込しない）
    @st.cache_data(show_spinner=False)
    def _load_template(path: str) -> bytes:
        with open(path, 'rb') as f:
            return f.read()

    if not os.path.exists(TEMPLATE_PATH):
        st.error(
            f"⚠️ テンプレートファイルが見つかりません: {TEMPLATE_FILENAME}\n\n"
            f"app.py と同じフォルダに「{TEMPLATE_FILENAME}」を配置してください。"
        )
        st.stop()
    template_data = _load_template(TEMPLATE_PATH)

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
            _ck = api_key[-8:] if len(api_key) >= 8 else api_key
            if _ck in _model_availability_cache:
                _avail_models = _model_availability_cache[_ck]
            else:
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
            value=True,
            help="FAX送付状が混在するPDFの1ページ目を自動検出・除外します。APIコールが1回増えます。"
        )
        use_rasterize = st.checkbox(
            "PDF→画像変換（行ズレ防止）",
            value=False,
            help="PDFをJPEG画像に変換してからAIに送ります。通常はOFFのままで精度が高くなります。"
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

        # ── 🧠 学習データ管理 ──────────────────────────────────
        st.markdown("---")
        with st.expander("🧠 学習データ管理", expanded=False):
            _err_summary = get_error_summary()
            _total_pending = sum(s['count'] for s in _err_summary)

            if _total_pending == 0:
                st.info("訂正データはまだありません。\nSTEP③で明細を修正するとここに蓄積されます。")
            else:
                st.markdown(f"**未統合の訂正データ: {_total_pending}件**")
                for _es in _err_summary:
                    _names_str = "、".join(_es['sample_names'][:3]) if _es['sample_names'] else ""
                    st.markdown(
                        f"- **{_es['label']}**: {_es['count']}件"
                        + (f"（例: {_names_str}）" if _names_str else "")
                    )

                st.markdown("---")
                # 蓄積データ詳細
                with st.expander("📋 訂正データ詳細", expanded=False):
                    _all_corr = get_all_pending_corrections()
                    if _all_corr:
                        _corr_rows = []
                        for _cr in _all_corr:
                            _corr_rows.append({
                                "日時": _cr['timestamp'][:16],
                                "エラー種別": FEEDBACK_ERROR_TYPES.get(_cr['error_type'], _cr['error_type']),
                                "修正前": f"{_cr['orig_name']} 部品¥{_cr['orig_parts']:,}/工賃¥{_cr['orig_wage']:,}",
                                "修正後": f"{_cr['corr_name']} 部品¥{_cr['corr_parts']:,}/工賃¥{_cr['corr_wage']:,}",
                                "コメント": (_cr['user_comment'] or "")[:40],
                            })
                        st.dataframe(pd.DataFrame(_corr_rows), use_container_width=True, hide_index=True)

                st.markdown("---")
                # マスタ統合
                st.markdown("**プロンプトへのマスタ統合**")
                if _total_pending < FEEDBACK_MERGE_THRESHOLD:
                    st.caption(f"※ あと{FEEDBACK_MERGE_THRESHOLD - _total_pending}件蓄積されると統合推奨になります（現在{_total_pending}件）")

                # 統合用パッチテキストを自動生成
                _patch_lines = ["【学習済み訂正パターン（自動生成）】"]
                _seen_types = set()
                _all_corr2 = get_all_pending_corrections()
                for _cr2 in _all_corr2:
                    _et = _cr2['error_type']
                    _on = _cr2['orig_name']
                    _cp = _cr2['corr_parts']
                    _cw = _cr2['corr_wage']
                    _cm = _cr2['user_comment'] or ""
                    _key = (_et, _on)
                    if _key in _seen_types:
                        continue
                    _seen_types.add(_key)
                    if _et == "column_swap":
                        if _cp == 0 and _cw > 0:
                            _patch_lines.append(f"- 「{_on}」は部品列に記載されていても工賃（wage）として扱うこと")
                        elif _cp > 0 and _cw == 0:
                            _patch_lines.append(f"- 「{_on}」は工賃列に記載されていても部品（parts_amount）として扱うこと")
                    elif _et == "missed_row":
                        _patch_lines.append(f"- 「{_on}」のような行を見落とさないこと")
                    elif _et == "amount_misread":
                        _patch_lines.append(f"- 「{_on}」の金額を正確に読み取ること（桁ずれ注意）")
                    if _cm:
                        _patch_lines.append(f"  （補足: {_cm[:60]}）")

                _auto_patch = "\n".join(_patch_lines) if len(_patch_lines) > 1 else ""
                _patch_text = st.text_area(
                    "統合するプロンプトパッチ（編集可）",
                    value=_auto_patch,
                    height=200,
                    key="patch_text_input",
                )

                _mc1, _mc2 = st.columns(2)
                with _mc1:
                    if st.button("🔄 マスタ版に統合する", key="merge_patch_btn", type="primary",
                                 disabled=(_total_pending == 0)):
                        if _patch_text.strip():
                            generate_and_save_patch(_patch_text.strip(), "estimate_detail_page")
                            st.success("✅ プロンプトパッチを適用しました。次回解析から有効になります。")
                            st.rerun()
                        else:
                            st.warning("パッチテキストが空です。")
                with _mc2:
                    if st.button("🗑 パッチを無効化", key="deactivate_patch_btn"):
                        try:
                            _conn = _get_feedback_db()
                            _conn.execute("UPDATE prompt_patches SET is_active = 0")
                            _conn.commit(); _conn.close()
                            st.success("パッチを無効化しました。")
                            st.rerun()
                        except Exception as _pe:
                            st.error(f"エラー: {_pe}")

            # 現在適用中のパッチ表示
            _current_patch = _load_learned_hints("estimate_detail_page")
            if _current_patch:
                with st.expander("📌 現在適用中のパッチ", expanded=False):
                    st.code(_current_patch, language=None)

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
        # ベタ打ちモード固定
        st.session_state['selected_mode'] = 'beta'

        st.markdown('<div style="background:#eff6ff;border:1px solid #bfdbfe;border-radius:8px;padding:10px 14px;font-size:13px;margin-bottom:12px">✏️ <b>ベタ打ちモード</b> — 見積内容をそのままNEOファイルに転記します</div>', unsafe_allow_html=True)

        # ── アップロードカード ──
        col1, col2 = st.columns(2)
        with col1:
            st.markdown('<div class="section-title">📋 車検証（任意）</div>', unsafe_allow_html=True)
            vehicle_file = st.file_uploader(
                "車検証をアップロード（PDF・JPG・PNG 対応）※なくても見積書のみで作成可",
                type=['pdf', 'jpg', 'jpeg', 'png', 'webp', 'bmp', 'tiff', 'tif', 'heic', 'heif'],
                key='vehicle_upload',
            )
            if vehicle_file:
                st.success(f"✅ {vehicle_file.name} ({vehicle_file.size:,} bytes)")
                st.caption("🔍 OCR対象: 型式・型式指定番号・類別区分番号・エンジン型式・使用者情報")
            else:
                st.info("💡 車検証なしの場合、見積書から読み取れる車両情報のみでNEOを作成します")
        with col2:
            # 見積書アップロード ＋ 税区分を横並び
            _est_col, _tax_col = st.columns([3, 2])
            with _est_col:
                st.markdown('<div class="section-title">🧾 見積書</div>', unsafe_allow_html=True)
                estimate_file = st.file_uploader(
                    "見積書をアップロード（PDF・JPG・PNG 対応、FAX品質可）",
                    type=['pdf', 'jpg', 'jpeg', 'png', 'webp', 'bmp', 'tiff', 'tif', 'heic', 'heif'],
                    key='estimate_upload',
                )
                if estimate_file:
                    st.success(f"✅ {estimate_file.name}")
                    st.session_state.pop('csv_items', None)
                    st.session_state.pop('csv_mode', None)
                else:
                    st.caption("💡 見積書なしの場合、車両情報のみのNEOを作成します")
            with _tax_col:
                st.markdown('<div class="section-title">💴 税区分</div>', unsafe_allow_html=True)
                _tax_options = ['税抜き（外税）', '税込み（内税）']
                _saved_tax_override = st.session_state.get('tax_override', '税抜き（外税）')
                if _saved_tax_override not in _tax_options:
                    _saved_tax_override = '税抜き（外税）'
                _tax_sel = st.radio(
                    "税区分",
                    options=_tax_options,
                    index=_tax_options.index(_saved_tax_override),
                    horizontal=False,
                    key='tax_override_radio',
                    label_visibility='collapsed',
                    help="見積書の明細金額が税込みか税抜きかを選択してください。"
                )
                st.session_state['tax_override'] = _tax_sel
                st.caption(f"⚙️ {_tax_sel}")

        # ── CSV取り込みセクション ──
        _CSV_PROMPT = """添付の自動車修理見積書PDFを、以下のCSV形式で全明細行を転写してください。

【出力形式（ヘッダー行必須）】
品名,区分,数量,部品金額,工賃,部品コード

【各列の定義】
- 品名：部品名または作業名（そのまま転写）
- 区分：下記ルールで判定した1語のみ
- 数量：半角整数（不明な場合は 1）
- 部品金額：部品・材料費（半角整数・カンマなし）。工賃のみの行は 0
- 工賃：技術料・作業料（半角整数・カンマなし）。部品のみの行は 0
- 部品コード：見積書に記載の品番・部品番号（ない場合は空欄）

【区分の判定ルール（必ずいずれか1語を記入。該当なしは空欄）】
取替：「取替」「交換」「取換」を含む作業、または部品金額のみ（工賃0）の行
脱着：「脱着」「取外」「取付」「組付」を含む作業
鈑金：「鈑金」「板金」を含む作業
塗装：「塗装」「ペイント」「ワックス」「加算」「ブース」を含む作業
修理：「修理」「補修」「調整」「点検」「設定」「分解」「修正」を含む作業
空欄：「研磨」「磨き」「写真代」「ショートパーツ」など上記に当てはまらないもの

【重要ルール】
- 部品と工賃は必ず別行に分けて記載する（同一行に両方入れない）
- 部品金額と工賃が見積書で同一列の場合：品番付き行→部品金額列、作業名行→工賃列に振り分ける
- 合計行・小計行・消費税行は除外する
- 全ページ・全明細行を漏れなく抽出する

【合計額の確認】
明細抽出後、抽出した部品金額合計と工賃合計を計算し、見積書原本の合計額と照合してください。
不一致の場合のみ、CSVの末尾に改行して以下を記載してください（一致している場合は記載不要）。
部品相違○○○○円
工賃相違●●●●円

出力はCSVおよび相違確認結果のみ。説明文・コメント不要。"""

        _escaped = _CSV_PROMPT.replace('`', '\\`').replace('\\', '\\\\').replace('\n', '\\n')

        # CSV取り込みバー（テキスト＋コピーボタンを横並び）
        _csv_bar_col, _csv_btn_col = st.columns([5, 2])
        with _csv_bar_col:
            st.markdown(
                '<div style="background:#f0fdf4;border:1px solid #86efac;border-radius:8px;'
                'padding:10px 14px;font-size:13px;">'
                '📊 <b>CSV取り込み（AI解析をスキップ）</b><br>'
                '<span style="font-size:11px;color:#555;">Claude.ai / Gemini.ai にPDFと下のプロンプトを送信 → CSVをコピー → 下欄に貼り付け</span>'
                '</div>',
                unsafe_allow_html=True
            )
        with _csv_btn_col:
            st.components.v1.html(f"""
<button onclick="navigator.clipboard.writeText(`{_escaped}`).then(()=>{{
    this.textContent='✅ コピーしました！';
    this.style.background='#16a34a';
    setTimeout(()=>{{this.textContent='📋 AI用プロンプトをコピー';this.style.background='#2563eb';}},2000);
}})" style="
    background:#2563eb;color:white;border:none;border-radius:8px;
    padding:10px 14px;font-size:13px;cursor:pointer;font-weight:600;width:100%;height:52px;
">📋 AI用プロンプトをコピー</button>
""", height=56)

        with st.expander("📊 CSVを貼り付けて取り込む", expanded=st.session_state.get('csv_mode', False)):
            _escaped2 = _escaped  # 同じエスケープ済みプロンプトを再利用
            st.components.v1.html(f"""
<button onclick="navigator.clipboard.writeText(`{_escaped2}`).then(()=>{{
    this.textContent='✅ コピーしました！';
    this.style.background='#16a34a';
    setTimeout(()=>{{this.textContent='📋 AI用プロンプトをコピー';this.style.background='#2563eb';}},2000);
}})" style="
    background:#2563eb;color:white;border:none;border-radius:6px;
    padding:7px 18px;font-size:13px;cursor:pointer;font-weight:600;margin-bottom:10px;
">📋 AI用プロンプトをコピー</button>
""", height=44)
            st.divider()
            _csv_col1, _csv_col2 = st.columns([2, 1])
            with _csv_col1:
                _csv_paste = st.text_area(
                    "CSVテキストを貼り付け（ヘッダー行必須）",
                    height=160,
                    placeholder="品名,区分,数量,部品金額,工賃,部品コード\nフロントバンパー,取替,1,45000,0,\nバンパー交換工賃,取替,1,0,12000,",
                    key='csv_paste_area',
                    value=st.session_state.get('_csv_paste_saved', ''),
                )
            with _csv_col2:
                st.markdown("**CSVファイル（.csv/.txt）**")
                _csv_file = st.file_uploader(
                    "CSVファイル",
                    type=['csv', 'txt'],
                    key='csv_file_upload',
                    label_visibility='collapsed',
                )
                if st.session_state.get('csv_mode') and st.session_state.get('csv_items'):
                    _p = sum(safe_int(it.get('parts_amount', 0)) for it in st.session_state['csv_items'])
                    _w = sum(safe_int(it.get('wage', 0)) for it in st.session_state['csv_items'])
                    st.success(f"✅ {len(st.session_state['csv_items'])}行 取込済")
                    st.caption(f"部品: ¥{_p:,} / 工賃: ¥{_w:,}")
                    if st.button("🗑️ クリア", key='csv_clear_btn'):
                        st.session_state.pop('csv_items', None)
                        st.session_state.pop('csv_mode', None)
                        st.session_state.pop('_csv_paste_saved', None)
                        st.rerun()

            _csv_text = ''
            if _csv_file:
                try:
                    _raw = _csv_file.read()
                    for _enc in ('utf-8-sig', 'utf-8', 'shift-jis', 'cp932'):
                        try:
                            _csv_text = _raw.decode(_enc)
                            break
                        except Exception:
                            continue
                except Exception:
                    pass
            elif _csv_paste and _csv_paste.strip():
                _csv_text = _csv_paste.strip()

            if _csv_text:
                _preview_items = parse_csv_to_items(_csv_text)
                if _preview_items:
                    st.success(f"✅ {len(_preview_items)}行 読み込み完了 — 部品: ¥{sum(safe_int(it.get('parts_amount',0)) for it in _preview_items):,} / 工賃: ¥{sum(safe_int(it.get('wage',0)) for it in _preview_items):,}")
                    st.session_state['csv_items'] = _preview_items
                    st.session_state['csv_mode']  = True
                    st.session_state['_csv_paste_saved'] = _csv_text
                else:
                    st.error("❌ CSVの読み込みに失敗しました。1行目にヘッダー（品名,区分,数量,部品金額,工賃,部品コード）が必要です。")
                    st.session_state.pop('csv_items', None)
                    st.session_state.pop('csv_mode', None)

            # ── 税区分選択 ──
            # ※ STEP1上部の税区分ラジオと同じ値を共有（二重書き込み回避のため表示のみ）
            _current_tax = st.session_state.get('tax_override', '税抜き（外税）')
            st.caption(f"💴 税区分: {_current_tax}（上部の税区分で変更可能）")

        # ── テンプレートNEOアップロード（任意） ──
        st.markdown("**📁 テンプレートNEOファイル（任意）**")
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
            # Streamlitのfile_uploaderはステップ遷移でウィジェットが非表示になると
            # session_stateのキーがクリアされる。そのため、バイト列を別キーに保存して永続化する
            _neo_bytes_read = custom_neo_file.read()
            st.session_state['custom_neo_bytes'] = _neo_bytes_read
            st.session_state['custom_neo_name']  = custom_neo_file.name
            custom_neo_file.seek(0)
            st.success(f"✅ {custom_neo_file.name} ({len(_neo_bytes_read):,} bytes)")
            st.caption("📋 車検証OCRで誤記入を訂正し、テンプレートの工場名・証券番号等はそのまま引き継ぎます")
        elif st.session_state.get('custom_neo_bytes'):
            # 前回アップロード済みのファイルがある場合、その情報を表示
            _saved_name = st.session_state.get('custom_neo_name', 'テンプレートNEO')
            _saved_size = len(st.session_state['custom_neo_bytes'])
            st.success(f"✅ {_saved_name} ({_saved_size:,} bytes) — 前回アップロード済み")
            st.caption("📋 車検証OCRで誤記入を訂正し、テンプレートの工場名・証券番号等はそのまま引き継ぎます")
            if st.button("🗑️ テンプレートNEOをリセット", key='clear_custom_neo'):
                st.session_state.pop('custom_neo_bytes', None)
                st.session_state.pop('custom_neo_name', None)
                st.rerun()
        else:
            st.info(f"未選択の場合はデフォルトテンプレート（{TEMPLATE_FILENAME}）を使用します")

        # ── オプション設定 ──
        st.markdown("**⚙️ オプション設定**")
        opt_col1, opt_col2, opt_col3 = st.columns(3)
        with opt_col1:
            policy_no_step1 = st.text_input("保険会社", placeholder="例: 東京海上日動", key="ins_company_step1")
        with opt_col2:
            policy_no_step1b = st.text_input("証券番号", placeholder="例: TK-12345678", key="ins_policy_step1")
        with opt_col3:
            assignee_step1 = st.text_input("担当者名", placeholder="例: 田中 花子", key="assignee_step1")

        st.markdown("")
        _csv_mode_active = st.session_state.get('csv_mode') and st.session_state.get('csv_items')
        _has_input = vehicle_file or estimate_file or _csv_mode_active
        if _has_input:
            _btn_label = "📊 CSV取り込みを開始 →" if _csv_mode_active and not estimate_file else "🚀 AI解析を開始 →"
            if st.button(_btn_label, type="primary", use_container_width=True):
                if not _csv_mode_active and not api_key:
                    st.error("⚠️ APIキーが未設定です。サイドバーで入力するか、app.py冒頭の GEMINI_API_KEY に貼り付けてください。")
                else:
                    if vehicle_file:
                        st.session_state['vehicle_file_bytes'] = vehicle_file.read()
                        st.session_state['vehicle_file_name']  = vehicle_file.name
                    else:
                        st.session_state['vehicle_file_bytes'] = None
                        st.session_state['vehicle_file_name']  = None
                    if estimate_file:
                        st.session_state['estimate_file_bytes'] = estimate_file.read()
                        st.session_state['estimate_file_name']  = estimate_file.name
                        st.session_state.pop('csv_mode', None)   # PDFがある場合はCSVモード解除
                        st.session_state.pop('csv_items', None)
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
            st.warning("見積書・車検証のアップロード、またはCSVの取り込みを行ってください")

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
        _use_raster    = st.session_state.get('use_rasterize', False)  # デフォルトFalse（PDF直接送信）
        _use_enhance   = st.session_state.get('use_enhance', True)
        _model         = st.session_state.get('selected_model', GEMINI_MODEL)
        # ベタ打ちモードでは自己修復ループを無効化（DB照合不要のため高速化）
        _is_beta_s2    = st.session_state.get('selected_mode', 'db') == 'beta'
        _enable_sc     = not _is_beta_s2

        # ── CSV取り込みモード: 見積AI解析をスキップ ──
        _csv_mode_s2   = st.session_state.get('csv_mode', False)
        _csv_items_s2  = st.session_state.get('csv_items', [])
        if _csv_mode_s2 and _csv_items_s2 and estimate_bytes is None:
            st.info(f"📊 CSVモード: {len(_csv_items_s2)}行を取り込みます（AI解析をスキップ）")
            # 車検証のみAI解析（ある場合）
            vehicle_data = {}
            if vehicle_bytes:
                with st.spinner("🔍 車検証を解析中..."):
                    vehicle_mime = get_mime_type(vehicle_name) if vehicle_bytes else None
                    vehicle_data = analyze_vehicle_registration(api_key, vehicle_bytes, vehicle_mime) or {}
            st.session_state['vehicle_data'] = vehicle_data
            # CSVアイテムをestimate_dataとして格納
            _tax_s2 = st.session_state.get('tax_override', '税抜き（外税）')
            estimate_data = {
                'items':            _csv_items_s2,
                'discount_amount':  0,
                'short_parts_wage': 0,
                'confidence':       1.0,
                'pdf_parts_total':  sum(safe_int(it.get('parts_amount', 0)) for it in _csv_items_s2),
                'pdf_wage_total':   sum(safe_int(it.get('wage', 0)) for it in _csv_items_s2),
                'pdf_grand_total':  0,
                '_is_tax_inclusive': _tax_s2 == '税込み（内税）',
                '_page_count':      1,
                '_vehicle_info':    {},
                '_repair_shop_name': '',
                '_csv_import':      True,
            }
            st.session_state['estimate_data'] = estimate_data
            st.success(f"✅ CSV取り込み完了（{len(_csv_items_s2)}行）")
            st.session_state['step'] = 3
            st.rerun()

        if vehicle_bytes is None and estimate_bytes is None:
            st.error("ファイルデータが見つかりません。ステップ①に戻ってください。")
            if st.button("← ステップ①に戻る"):
                st.session_state['step'] = 1
                st.rerun()
            st.stop()

        progress = st.progress(0, text="AI解析を開始しています...")
        _wait_msg = st.info(
            "📡 GeminiにPDFを送信し解析中です。"
            "ページ数・ファイルサイズによって **30秒〜2分** かかる場合があります。"
            "このページから移動せずにお待ちください。"
        )

        def _progress_cb(pct: int, text: str):
            try:
                progress.progress(pct, text=text)
            except Exception:
                pass

        try:
            vehicle_mime  = get_mime_type(vehicle_name) if vehicle_bytes else None
            estimate_mime = get_mime_type(estimate_name) if estimate_bytes else None

            if vehicle_bytes and estimate_bytes:
                # 車検証＋見積書を並列で解析
                progress.progress(5, text="🔍 車検証＋見積書を同時解析中...")
                with ThreadPoolExecutor(max_workers=2) as executor:
                    fut_vehicle = executor.submit(
                        analyze_vehicle_registration, api_key, vehicle_bytes, vehicle_mime
                    )
                    fut_estimate = executor.submit(
                        analyze_estimate, api_key, estimate_bytes, estimate_mime, _model,
                        _use_fax, _use_raster, _use_enhance, _enable_sc
                    )
                    vehicle_data  = fut_vehicle.result()
                    progress.progress(40, text="✅ 車検証の解析完了、見積書を処理中...")
                    estimate_data = fut_estimate.result() or {}
            elif vehicle_bytes:
                # 車検証のみ
                progress.progress(10, text="🔍 車検証を解析中...")
                vehicle_data  = analyze_vehicle_registration(api_key, vehicle_bytes, vehicle_mime)
                estimate_data = None
            else:
                # 見積書のみ（車検証なし）— 逐次解析でプログレス更新可能
                progress.progress(5, text="🔍 見積書の解析を開始中...")
                vehicle_data  = {}
                estimate_data = analyze_estimate(
                    api_key, estimate_bytes, estimate_mime, _model,
                    _use_fax, _use_raster, _use_enhance, _enable_sc,
                    progress_cb=_progress_cb,
                ) or {}

            st.session_state['vehicle_data'] = vehicle_data
            progress.progress(90, text="✅ 解析完了")
            _wait_msg.empty()  # 「お待ちください」メッセージを非表示

            if vehicle_bytes:
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
                # （車検証なしの場合は見積書の車両情報が唯一の情報源となる）
                est_vinfo = estimate_data.get('_vehicle_info', {})
                if est_vinfo and vehicle_data is not None:
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
                
                # --- 税区分 ユーザー選択値を常に適用（AI自動判定廃止）---
                _tax_override = st.session_state.get('tax_override', '税抜き（外税）')
                if _tax_override == '税込み（内税）':
                    estimate_data['_is_tax_inclusive'] = True
                    estimate_data['_tax_basis']        = 'tax_inclusive'
                else:
                    # デフォルト: 税抜き（外税）
                    estimate_data['_is_tax_inclusive'] = False
                    estimate_data['_tax_basis']        = 'tax_exclusive'
                    estimate_data.pop('_tax_converted', None)

                # --- セッションステートへの保存 ---
                st.session_state['estimate_data'] = estimate_data

                # 精度処理の結果を表示
                info_msgs = []
                if not vehicle_bytes:
                    info_msgs.append("📋 車検証なしモード: 見積書から読み取れた車両情報のみでNEOを作成します。ステップ③で車両情報を確認・補完してください。")
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
                if estimate_data.get('_fax_filtered', 0) > 0:
                    info_msgs.append("🗑️ FAX送付状を自動除外しました")
                if estimate_data.get('_self_corrected'):
                    info_msgs.append("🔧 自己修復ループが有効になりました")
                page_count = estimate_data.get('_page_count', 1)
                if page_count > 1:
                    info_msgs.append(f"📄 {page_count}ページ分割処理（重複除去済み）")
                tax_basis = estimate_data.get('_tax_basis', 'tax_exclusive')
                if tax_basis == 'tax_inclusive':
                    info_msgs.append("💱 税込モード（ユーザー選択）— NEOファイルも税込で生成します")
                else:
                    info_msgs.append("✅ 税抜モード（ユーザー選択）")
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
            err_str = str(e)
            # クォータ超過エラーの場合、分かりやすいメッセージとリトライを促す
            if '429' in err_str or 'RESOURCE_EXHAUSTED' in err_str or 'クォータが上限' in err_str:
                _cur_model = st.session_state.get('selected_model', _model or 'gemini-2.5-flash')
                _quota_exhausted_models.add(_cur_model)
                # キャッシュクリア
                _api_key_for_err = api_key
                if _api_key_for_err:
                    _ck = _api_key_for_err[-8:]
                    if _ck in _model_availability_cache:
                        del _model_availability_cache[_ck]
                # 代替モデルを探す
                _alt = next((m for m in _PREFERRED_MODELS if m not in _quota_exhausted_models), None)
                if _alt:
                    st.warning(
                        f"⚠️ モデル「{_cur_model}」の1日クォータ（250回）が上限に達しました。\n\n"
                        f"**🔄 代替モデル「{_alt}」に自動切り替えます。「② AI解析」ボタンをもう一度押してください。**",
                        icon="⚠️"
                    )
                    # 自動的に代替モデルをセッションに設定
                    st.session_state['selected_model'] = _alt
                else:
                    st.error(
                        "⚠️ 全モデルのクォータが上限に達しました。\n\n"
                        "翌日（リセット後）か、Google AI StudioでAPIキーの課金を有効化してください。"
                    )
            else:
                st.error(f"⚠️ AI解析中にエラーが発生しました:\n\n{err_str}")
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

        if vehicle_data is None and not estimate_data:
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
        if len(reg_date_strip) >= 6:
            reg_date_display = f"{reg_date_strip[:4]}/{reg_date_strip[4:6]}"
        else:
            reg_date_display = reg_date_strip
        km_strip = safe_int(vehicle_data.get('kilometer', 0))
        type_desig = safe_str(vehicle_data.get('car_model_designation', ''))
        cat_num = safe_str(vehicle_data.get('car_category_number', ''))
        v_code = veh_match_result.get('vehicle_code', '')
        match_mode_html = f'<span class="badge-blue">🗂 DBモード</span>' if match_is_db else '<span class="badge-gray">✏️ ベタ打ち</span>'
        items_count = len(estimate_data.get('items', [])) if estimate_data else 0
        match_ok_count = sum(1 for it in (estimate_data.get('items', []) if estimate_data else []) if safe_int(it.get('_match_level', 99), 99) <= 3)
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

        # ── 解析ログ表示 ──────────────────────────────────────────────────────────
        if estimate_data:
            _analysis_log = estimate_data.get('_analysis_log', [])
            if _analysis_log:
                # 最終行から一致・不一致を判定してラベルを変える
                _log_label_ok = any('✅' in l for l in _analysis_log)
                _log_label_ng = any('⚠️ 差額' in l for l in _analysis_log)
                _log_icon = '✅' if _log_label_ok and not _log_label_ng else ('⚠️' if _log_label_ng else '🔍')
                with st.expander(f"{_log_icon} 解析ログ（詳細）", expanded=False):
                    st.code('\n'.join(_analysis_log), language=None)

        # 信頼度・税区分の警告
        v_conf = safe_float(vehicle_data.get('confidence', 1.0), 1.0)
        if v_conf < CONFIDENCE_THRESHOLD:
            st.markdown(f'<div class="alert alert-warn">⚠️ 車検証の読み取り信頼度: <b>{v_conf:.0%}</b> — 内容をよくご確認ください。</div>', unsafe_allow_html=True)
        if estimate_data:
            e_conf = safe_float(estimate_data.get('confidence', 1.0), 1.0)
            if e_conf < CONFIDENCE_THRESHOLD:
                st.markdown(f'<div class="alert alert-warn">⚠️ 見積書の読み取り信頼度: <b>{e_conf:.0%}</b> — 内容をよくご確認ください。</div>', unsafe_allow_html=True)
            tax_basis = estimate_data.get('_tax_basis', 'tax_exclusive')
            rev_match = estimate_data.get('_reverse_match', False)
            shop_name  = estimate_data.get('_repair_shop_name', '')
            # コグニセブン設定用 税モード（ユーザー選択値）
            if tax_basis == 'tax_inclusive':
                cogni_tax_mode = '税込'
                cogni_tax_color = '#1e40af'
                cogni_tax_bg = '#dbeafe'
                cogni_tax_border = '#3b82f6'
                cogni_tax_icon = '🔵'
                basis_label = '税込明細（ユーザー設定）'
            else:
                cogni_tax_mode = '税抜'
                cogni_tax_color = '#14532d'
                cogni_tax_bg = '#dcfce7'
                cogni_tax_border = '#22c55e'
                cogni_tax_icon = '🟢'
                basis_label = '税抜明細（ユーザー設定）'
            rev_icon = '✅ 逆算一致' if rev_match else '⚠️ 逆算不一致（金額を確認してください）'
            shop_html   = f'<div style="font-size:13px;color:#374151;margin-bottom:10px">🏭 修理工場: <b>{shop_name}</b></div>' if shop_name else ''
            st.markdown(f'''
<div style="border:2px solid {cogni_tax_border};border-radius:8px;background:{cogni_tax_bg};padding:14px 18px;margin-bottom:12px">
  {shop_html}
  <div style="font-size:13px;color:{cogni_tax_color};font-weight:600;margin-bottom:6px">■ コグニセブン設定用 税区分</div>
  <div style="font-size:22px;font-weight:700;color:{cogni_tax_color}">{cogni_tax_icon} コグニセブンを <u>{cogni_tax_mode}モード</u> に設定してください</div>
  <div style="font-size:13px;color:{cogni_tax_color};margin-top:4px">（{basis_label} ／ {rev_icon}）</div>
</div>
''', unsafe_allow_html=True)

        # ── タブ（見積明細タブ廃止・編集は合計・費用タブへ統合）──
        tab_vehicle, tab_totals = st.tabs(["🚗 車両情報", "💰 合計・費用"])

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

        # 見積明細（合計・費用タブ内で編集）
        calc_parts    = 0
        calc_wages    = 0
        pdf_parts     = 0
        pdf_wages     = 0
        sp            = 0
        wage_match_sp = False  # Step4でも参照するため初期化
        # tab_totals 内の条件分岐に依存する変数を安全のため事前初期化
        _step3_mode       = st.session_state.get('selected_mode', 'db')
        discrepancies     = []
        total_diff        = 0
        edited_items      = []

        with tab_totals:
          if estimate_data and estimate_data.get('items'):

            # ── 明細行一覧 (編集可) ──────────────────────────────
            st.markdown('<div class="section-title">📋 明細行一覧（全項目・編集可）</div>', unsafe_allow_html=True)

            # AI初期出力を _original_items として保存（初回のみ）
            if '_original_items' not in st.session_state:
                st.session_state['_original_items'] = [dict(it) for it in estimate_data.get('items', [])]

            _items_src = estimate_data['items']
            # ── 行操作ボタン（挿入・コピー・削除） ──────────────────────
            _op_col1, _op_col2, _op_col3, _op_col4 = st.columns([1, 1, 1, 5])
            with _op_col1:
                if st.button("➕ 行挿入", key="row_insert_btn", help="最終行に空白行を追加"):
                    _new_row = {
                        'name': '', 'method': '', 'work_code': '', 'index_value': '',
                        'quantity': 1, 'parts_amount': 0, 'wage': 0, 'part_no': '',
                        '_master_name': '', '_master_price': 0, '_master_part_no': '',
                        '_master_repair_code': '', '_master_branch_code': '',
                        '_master_part_code_r': '', '_master_part_code_l': '',
                        '_match_level': 0, '_original_name': '', '_original_parts_amount': 0,
                    }
                    estimate_data['items'].append(_new_row)
                    st.session_state['estimate_data'] = estimate_data
                    st.rerun()
            with _op_col2:
                _copy_no = st.number_input("コピーNo", min_value=1, max_value=max(len(_items_src), 1),
                                           value=1, step=1, key="row_copy_no", label_visibility="collapsed")
            with _op_col3:
                if st.button("📋 コピー", key="row_copy_btn", help="指定No行を複製して最終行に追加"):
                    _cidx = int(_copy_no) - 1
                    if 0 <= _cidx < len(_items_src):
                        import copy as _copy
                        _copied = _copy.deepcopy(_items_src[_cidx])
                        estimate_data['items'].append(_copied)
                        st.session_state['estimate_data'] = estimate_data
                        st.rerun()

            # 表示用DataFrame（7列）: No / 部品コード / 品名 / 数量 / 部品金額 / 工数 / 工賃
            _edit_rows = []
            for _i, _item in enumerate(_items_src):
                _part_code   = str(_item.get('part_no', '') or _item.get('_master_part_no', '') or '')
                _index_value = str(_item.get('index_value', '') or '')
                _edit_rows.append({
                    'No':     _i + 1,
                    '部品コード': _part_code,
                    '品名':   str(_item.get('name', '')),
                    '数量':   safe_int(_item.get('quantity', 1), 1),
                    '部品金額': safe_int(_item.get('parts_amount', 0)),
                    '工数':   _index_value,
                    '工賃':   safe_int(_item.get('wage', 0)),
                })
            _df_edit = pd.DataFrame(_edit_rows) if _edit_rows else pd.DataFrame(
                columns=['No', '部品コード', '品名', '数量', '部品金額', '工数', '工賃'])
            # キーを行数と連動させることで行挿入後に data_editor を強制再初期化する
            _editor_key = f'items_editor_{len(_items_src)}'
            # height を固定して描画行数を制限（全行フル展開すると100行超で重くなるため）
            _editor_height = min(600, max(200, len(_items_src) * 35 + 60))
            _edited_df = st.data_editor(
                _df_edit,
                use_container_width=True,
                hide_index=True,
                num_rows="dynamic",
                height=_editor_height,
                column_config={
                    'No':     st.column_config.NumberColumn('No', disabled=True, width='small'),
                    '部品コード': st.column_config.TextColumn('部品コード'),
                    '品名':   st.column_config.TextColumn('品名', width='large'),
                    '数量':   st.column_config.NumberColumn('数量', min_value=1, step=1, width='small'),
                    '部品金額': st.column_config.NumberColumn('部品金額', step=1, format="¥%d"),
                    '工数':   st.column_config.TextColumn('工数', width='small'),
                    '工賃':   st.column_config.NumberColumn('工賃', step=1, format="¥%d"),
                },
                key=_editor_key,
            )
            # 編集後データを反映（既存行の内部メタデータを保持、新規行はデフォルト値）
            _edited_df = _edited_df.reset_index(drop=True)
            _edited_df['No'] = range(1, len(_edited_df) + 1)
            edited_items = []
            for _i, _row in _edited_df.iterrows():
                _nv = _row.get('品名', '');     _nv = '' if pd.isna(_nv) else str(_nv)
                _pc = _row.get('部品コード', ''); _pc = '' if pd.isna(_pc) else str(_pc)
                _iv = _row.get('工数', '');     _iv = '' if pd.isna(_iv) else str(_iv)
                # 既存行のメタデータを引き継ぐ（新規追加行はデフォルト）
                _orig = _items_src[_i] if _i < len(_items_src) else {}
                _wk   = _orig.get('work_code', '') or _orig.get('method', '')
                edited_items.append({
                    'name': _nv, 'method': _wk, 'work_code': _wk,
                    'index_value': _iv,
                    'quantity': safe_int(_row.get('数量', 1), 1),
                    'parts_amount': safe_int(_row.get('部品金額', 0)),
                    'wage': safe_int(_row.get('工賃', 0)),
                    'part_no': _pc,
                    '_master_name': _orig.get('_master_name', ''),
                    '_master_price': _orig.get('_master_price', 0),
                    '_master_part_no': _orig.get('_master_part_no', ''),
                    '_master_repair_code': _orig.get('_master_repair_code', ''),
                    '_master_branch_code': _orig.get('_master_branch_code', ''),
                    '_master_part_code_r': _orig.get('_master_part_code_r', ''),
                    '_master_part_code_l': _orig.get('_master_part_code_l', ''),
                    '_match_level': _orig.get('_match_level', 0),
                    '_original_name': _orig.get('name', _nv),
                    '_original_parts_amount': _orig.get('parts_amount', safe_int(_row.get('部品金額', 0))),
                })
            estimate_data['items'] = edited_items
            st.session_state['estimate_data'] = estimate_data
            for _it in edited_items:
                calc_parts += safe_int(_it.get('parts_amount', 0))
                calc_wages += safe_int(_it.get('wage', 0))
            sp = 0
            pdf_parts = safe_int(estimate_data.get('pdf_parts_total', 0))
            pdf_wages = safe_int(estimate_data.get('pdf_wage_total', 0))

            # ── フィードバック: 差分検出（アイテムが変わった時だけ再計算）─────
            _orig_items_fb = st.session_state.get('_original_items', [])
            _fb_hash = hash(str([(it.get('name',''), it.get('parts_amount',0), it.get('wage',0)) for it in edited_items]))
            if st.session_state.get('_fb_hash') != _fb_hash:
                st.session_state['_fb_cache'] = _detect_corrections(_orig_items_fb, edited_items)
                st.session_state['_fb_hash']  = _fb_hash
            _fb_corrections = st.session_state.get('_fb_cache', [])
            if _fb_corrections:
                _fb_key = f"fb_open_{hash(str(_fb_corrections))}"
                with st.expander(f"📝 読み取り訂正レポート（{len(_fb_corrections)}件の変更を検出）", expanded=False):
                    st.markdown("**以下の行が修正されました。AIへのフィードバックとして記録できます。**")
                    _fb_rows = []
                    for _fc in _fb_corrections:
                        _orig = _fc.get("original", {})
                        _corr = _fc.get("corrected", {})
                        _fb_rows.append({
                            "行": _fc["row_index"],
                            "品名(修正前)": _orig.get("name", "-"),
                            "部品(修正前)": f"¥{safe_int(_orig.get('parts_amount',0)):,}" if _orig else "-",
                            "工賃(修正前)": f"¥{safe_int(_orig.get('wage',0)):,}" if _orig else "-",
                            "品名(修正後)": _corr.get("name", "-") if _corr else "（削除）",
                            "部品(修正後)": f"¥{safe_int(_corr.get('parts_amount',0)):,}" if _corr else "-",
                            "工賃(修正後)": f"¥{safe_int(_corr.get('wage',0)):,}" if _corr else "-",
                            "推定エラー種別": FEEDBACK_ERROR_TYPES.get(_fc.get("error_type","other"), _fc.get("error_type","")),
                        })
                    st.table(pd.DataFrame(_fb_rows).set_index("行"))

                    st.markdown("**エラーの原因を文章で教えてください（任意）:**")
                    _fb_comment = st.text_area(
                        "例: 工賃列に記載されているのに部品として読み取られた",
                        key="fb_comment_input", height=80, label_visibility="collapsed"
                    )
                    _fb_doc_type = estimate_data.get('_document_type', '不明')
                    _fbc1, _fbc2 = st.columns([1, 3])
                    with _fbc1:
                        if st.button("✅ フィードバックを記録する", key="fb_record_btn", type="primary"):
                            record_correction(_fb_corrections, _fb_comment, _fb_doc_type)
                            st.session_state['_original_items'] = [dict(it) for it in edited_items]
                            st.success(f"✅ {len(_fb_corrections)}件の訂正をDBに記録しました")
                            # 蓄積件数チェック
                            _summary = get_error_summary()
                            _total_pending = sum(s['count'] for s in _summary)
                            if _total_pending >= FEEDBACK_MERGE_THRESHOLD:
                                st.info(f"💡 訂正データが{_total_pending}件蓄積されました。サイドバーの「🧠 学習データ管理」からマスタ統合を実行できます。")
                    with _fbc2:
                        if st.button("⏭ スキップ", key="fb_skip_btn"):
                            st.session_state['_original_items'] = [dict(it) for it in edited_items]

            st.markdown("---")
            # ── 金額サマリー ────────────────────────────────────
            st.markdown('<div class="section-title">💰 金額サマリー</div>', unsafe_allow_html=True)
            scol1, scol2, scol3 = st.columns(3)
            rev_match = estimate_data.get('_reverse_match', False)

            # 税込/税抜モード判定
            is_tax_incl_s3 = estimate_data.get('_is_tax_inclusive', False)
            tax_label_sfx  = "税込" if is_tax_incl_s3 else "税抜"

            # 金額差額の計算
            parts_diff = calc_parts - pdf_parts if pdf_parts > 0 else 0
            # SP込みでも一致チェック（部品）
            parts_match_sp = (calc_parts + sp == pdf_parts) if pdf_parts > 0 else False
            # 税込モードでは明細合算とPDF記載値の小差（明細行数×1円以内）も一致とみなす
            _parts_tol = len(edited_items) if is_tax_incl_s3 else 0
            parts_match_tol = (abs(calc_parts - pdf_parts) <= _parts_tol) if pdf_parts > 0 else False
            parts_match_tol_sp = (abs(calc_parts + sp - pdf_parts) <= _parts_tol) if pdf_parts > 0 else False
            parts_match = (calc_parts == pdf_parts) or parts_match_sp or parts_match_tol or parts_match_tol_sp
            wage_diff = calc_wages - pdf_wages if pdf_wages > 0 else 0
            # SP込みでも一致チェック（工賃）: Honda Cars等でSPが工賃列に含まれる場合
            wage_match_sp = (calc_wages + sp == pdf_wages) if pdf_wages > 0 else False
            _wages_tol = len(edited_items) if is_tax_incl_s3 else 0
            wage_match_tol = (abs(calc_wages - pdf_wages) <= _wages_tol) if pdf_wages > 0 else False
            wage_match_tol_sp = (abs(calc_wages + sp - pdf_wages) <= _wages_tol) if pdf_wages > 0 else False
            wage_match = (calc_wages == pdf_wages) or wage_match_sp or wage_match_tol or wage_match_tol_sp
            has_discrepancy = False

            with scol1:
                st.metric(f"部品合計（{tax_label_sfx}）", f"¥{calc_parts:,}")
                if pdf_parts > 0 and not parts_match and not rev_match:
                    has_discrepancy = True
                    st.markdown(
                        f'<div class="error-box">⚠️ <b>部品相違</b>: PDF ¥{pdf_parts:,} ≠ 計算 ¥{calc_parts:,}（差額: {parts_diff:+,}円）</div>',
                        unsafe_allow_html=True
                    )
                elif pdf_parts > 0:
                    st.markdown('<div class="success-box">✅ PDF金額と一致</div>', unsafe_allow_html=True)
            with scol2:
                st.metric(f"工賃合計（{tax_label_sfx}）", f"¥{calc_wages:,}")
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
                sub = calc_parts + calc_wages + sp + exp_tow + exp_ren
                if is_tax_incl_s3:
                    # 税込モード: 明細金額は既に税込 → 消費税を加算しない
                    total = sub + exp_exm
                else:
                    tax   = round(sub * TAX_RATE)
                    total = sub + tax + exp_exm
                st.metric("合計（税込）", f"¥{total:,}")
                if rev_match:
                    st.markdown('<div class="success-box">✅ 逆算一致</div>', unsafe_allow_html=True)

            # ── STEP 3 バリデーション結果パネル ──
            # parts_match / wage_match はこの直上でリアルタイム再計算済みの値を使用する
            # (estimate_data['totals_verification'] は解析時の古い判定のため使わない)
            _tv_has_data = (pdf_parts > 0 or pdf_wages > 0)
            if _tv_has_data:
                _tv_p_mismatch = pdf_parts > 0 and not parts_match and not rev_match
                _tv_w_mismatch = pdf_wages > 0 and not wage_match and not rev_match
                if not _tv_p_mismatch and not _tv_w_mismatch:
                    st.markdown(
                        '<div class="success-box" style="padding:10px 16px;margin-bottom:12px">'
                        '✅ <b>【STEP 3 バリデーション: 合格】</b> 見積書記載の合計値と1円の誤差もなく一致しています。'
                        '</div>', unsafe_allow_html=True)
                else:
                    _disp_p_diff = parts_diff if _tv_p_mismatch else 0
                    _disp_w_diff = wage_diff  if _tv_w_mismatch else 0
                    _err_parts_list = []
                    if _disp_p_diff != 0: _err_parts_list.append(f'部品差額{_disp_p_diff:+,}円')
                    if _disp_w_diff != 0: _err_parts_list.append(f'工賃差額{_disp_w_diff:+,}円')
                    err_text = f'<br>推定原因: {"・".join(_err_parts_list)}' if _err_parts_list else ''
                    st.markdown(
                        f'<div class="error-box" style="padding:10px 16px;margin-bottom:12px">'
                        f'🚨 <b>【STEP 3 バリデーション: 不合格】</b> 金額の不一致が検出されています。<br>'
                        f'部品差額: {_disp_p_diff:+,}円 ／ 工賃差額: {_disp_w_diff:+,}円{err_text}'
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
                    st.table(pd.DataFrame(_beta_verification_rows).set_index('No'))

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
                reverse_ok = False  # ブロック外からの参照に備えて初期化
                if pdf_grand > 0 and (pdf_parts > 0 or pdf_wages > 0):
                    reverse_sub = calc_parts + calc_wages + sp
                    if is_tax_incl_s3:
                        # 税込モード: 金額は既に税込 → 消費税を加算しない
                        reverse_grand = reverse_sub + st.session_state.get('exp_exempt', 0)
                    else:
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

            # ── ベタ打ちモード専用: 部品・工賃区分確認パネル ──────────────────────────
            _classification_alerts = []
            _classification_confirmed = True
            _error_alerts = []
            if _step3_mode == 'beta':
                # アイテムが変わった時だけ再計算（session_stateでキャッシュ）
                _items_hash = hash(str([(it.get('name',''), it.get('parts_amount',0), it.get('wage',0)) for it in edited_items]))
                if st.session_state.get('_cls_hash') != _items_hash:
                    st.session_state['_cls_cache'] = check_parts_labor_classification(edited_items)
                    st.session_state['_cls_hash']  = _items_hash
                _classification_alerts = st.session_state.get('_cls_cache', [])
                _error_alerts   = [a for a in _classification_alerts if a['severity'] == 'error']
                _warning_alerts = [a for a in _classification_alerts if a['severity'] == 'warning']

                if _classification_alerts:
                    st.markdown(
                        '<div class="section-title">🔍 部品・工賃区分確認（NEO転記前の必須チェック）</div>',
                        unsafe_allow_html=True
                    )
                    # エラー（要確認）
                    if _error_alerts:
                        st.markdown(
                            f'<div class="error-box" style="padding:10px 16px;margin:6px 0">'
                            f'🚨 <b>要確認: 部品/工賃の区分に疑わしい行が {len(_error_alerts)} 件あります</b><br>'
                            f'以下の行を確認し、正しい列に金額が入っているかを確認してください。'
                            f'</div>',
                            unsafe_allow_html=True
                        )
                        for a in _error_alerts:
                            st.markdown(
                                f'<div style="background:#fef2f2;border-left:4px solid #dc2626;padding:8px 12px;margin:4px 0;font-size:13px">'
                                f'🔴 <b>行{a["row_no"]}「{a["name"]}」</b>: '
                                f'部品¥{a["parts_amount"]:,} / 工賃¥{a["wage"]:,}<br>'
                                f'⚠️ {a["message"]}'
                                f'</div>',
                                unsafe_allow_html=True
                            )
                    # 警告（参考情報）
                    if _warning_alerts:
                        with st.expander(f"⚠️ 参考警告 ({len(_warning_alerts)} 件) — 要確認の可能性あり", expanded=False):
                            for a in _warning_alerts:
                                st.markdown(
                                    f'<div style="background:#fffbeb;border-left:4px solid #d97706;padding:8px 12px;margin:4px 0;font-size:13px">'
                                    f'🟡 <b>行{a["row_no"]}「{a["name"]}」</b>: '
                                    f'部品¥{a["parts_amount"]:,} / 工賃¥{a["wage"]:,}<br>'
                                    f'{a["message"]}'
                                    f'</div>',
                                    unsafe_allow_html=True
                                )

                    # 確認チェックボックス（エラーがある場合のみ）
                    if _error_alerts:
                        _classification_confirmed = st.checkbox(
                            "⬆️ 上記の部品/工賃区分を確認しました。この内容でNEOファイルに転記します。",
                            value=False,
                            key='classification_confirmed'
                        )
                        if not _classification_confirmed:
                            st.info(
                                "💡 明細を修正するには、上の「✏️ 明細行を修正」エリアで各行の部品金額・工賃を直接編集できます。"
                                "区分が正しければチェックを入れてNEO生成に進んでください。"
                            )
                    else:
                        _classification_confirmed = True
                        st.markdown(
                            '<div class="success-box" style="padding:10px 16px;margin:8px 0">'
                            '✅ <b>部品・工賃区分チェック: 参考警告のみ</b> — 重大な区分エラーは検出されませんでした。</div>',
                            unsafe_allow_html=True
                        )
                else:
                    st.markdown(
                        '<div class="success-box" style="padding:10px 16px;margin:8px 0">'
                        '✅ <b>部品・工賃区分チェック: 問題なし</b> — 全明細行の区分が正常です。</div>',
                        unsafe_allow_html=True
                    )

            # セッションに保存（STEP4で参照）
            st.session_state['classification_alerts'] = _classification_alerts
            # classification_confirmed: 別キーで管理（ウィジェットキーとの衝突回避）
            if not _error_alerts:
                st.session_state['_cls_confirmed_value'] = _classification_confirmed
            else:
                st.session_state['_cls_confirmed_value'] = st.session_state.get('classification_confirmed', False)

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
                st.table(pd.DataFrame(diff_data).set_index('No'))
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
            _is_tax_incl_strip = (estimate_data.get('_is_tax_inclusive', False) if estimate_data else False)
            if _is_tax_incl_strip:
                tax   = 0
                total = sub + st.session_state.get('exp_exempt', 0)
            else:
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
                    <div class="total-label">{'消費税（税込済）' if _is_tax_incl_strip else '消費税'}</div>
                    <div class="total-value">{'—' if _is_tax_incl_strip else f'¥{tax:,}'}</div>
                </div>
                <div class="total-sep">=</div>
                <div class="total-item">
                    <div class="total-label">合計{'（税込）' if not _is_tax_incl_strip else ''}</div>
                    <div class="total-value-highlight">¥{total:,}</div>
                </div>
            </div>
            """, unsafe_allow_html=True)
          else:
            amount_confirmed = True
            st.info("💡 見積書なし — 車両情報のみのNEOファイルを作成します")

        if 'amount_confirmed' not in locals():
            amount_confirmed = True

        # ── 部品/工賃区分確認チェックの取得（ベタ打ちモード）──────────────────
        _cls_confirmed   = st.session_state.get('_cls_confirmed_value', True)
        _cls_alerts      = st.session_state.get('classification_alerts', [])
        _cls_errors      = [a for a in _cls_alerts if a['severity'] == 'error']
        # ベタ打ちモード以外は常にOK
        if _step3_mode != 'beta':
            _cls_confirmed = True

        # NEO生成ボタン
        st.markdown("---")

        # 区分エラーがあって未確認の場合、警告を再表示
        if _cls_errors and not _cls_confirmed and _step3_mode == 'beta':
            st.markdown(
                '<div class="mismatch-banner">'
                '<div class="mismatch-title">🚫 部品・工賃区分の確認が必要です</div>'
                '<div class="mismatch-body">'
                f'{len(_cls_errors)}件の区分エラーが未確認です。<br>'
                '上の「🔍 部品・工賃区分確認」パネルで内容を確認し、チェックボックスにチェックを入れてください。'
                '</div>'
                '</div>',
                unsafe_allow_html=True
            )

        bcol1, bcol2 = st.columns(2)
        with bcol1:
            if st.button("← ステップ①に戻る", use_container_width=True):
                st.session_state['step'] = 1
                st.session_state['vehicle_data']  = None
                st.session_state['estimate_data'] = None
                st.rerun()
        with bcol2:
            gen_disabled = not amount_confirmed or not _cls_confirmed
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
            if not amount_confirmed:
                st.caption("⬆️ 金額差異を確認してチェックを入れてください")
            elif not _cls_confirmed:
                st.caption("⬆️ 部品・工賃区分エラーを確認してチェックを入れてください")

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
        _neo_wait = st.info("📦 NEOファイルを生成しています。しばらくお待ちください...")
        try:
            progress.progress(20, text="📦 テンプレートを読み込み中...")
            is_tax_inclusive = estimate_data.get('_is_tax_inclusive', False) if estimate_data else False
            _step4_beta = st.session_state.get('selected_mode', 'db') == 'beta'
            # カスタムテンプレートNEOが指定されている場合はそちらを使用
            # session_stateに永続化したバイト列を優先使用（file_uploaderはステップ遷移でクリアされるため）
            _custom_neo_bytes = st.session_state.get('custom_neo_bytes')
            if not _custom_neo_bytes:
                # フォールバック: file_uploaderが同一セッション内でまだ生きている場合
                _fallback_neo = st.session_state.get('custom_neo_upload')
                if _fallback_neo:
                    _custom_neo_bytes = _fallback_neo.read()
                    _fallback_neo.seek(0)
            _use_custom_neo   = _custom_neo_bytes is not None
            _active_template  = _custom_neo_bytes if _use_custom_neo else template_data
            if _use_custom_neo:
                _custom_name = st.session_state.get('custom_neo_name', 'カスタムNEO')
                progress.progress(35, text=f"📁 テンプレートNEO ({_custom_name}) を読み込み中...")
            progress.progress(50, text="⚙️ 明細データをNEOに書き込み中...")
            neo_data, total_parts, total_wages, grand_total = generate_neo_file(
                _active_template, updated_vehicle, items, short_parts_wage, insurance_info,
                expenses=expense_info, is_tax_inclusive=is_tax_inclusive, is_beta_mode=_step4_beta,
                merge_mode=_use_custom_neo
            )
            progress.progress(85, text="📝 ファイル名を生成中...")
            filename = generate_filename(
                updated_vehicle, calc_parts, calc_wages, pdf_parts, pdf_wages,
                has_estimate, reverse_match, short_parts_wage
            )
            st.session_state['neo_bytes']    = neo_data
            st.session_state['neo_filename'] = filename
            progress.progress(100, text="✅ 生成完了！")
            _neo_wait.empty()  # 待機メッセージを消去

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

            # ── ベタ打ちモード: 部品・工賃区分確認済みサマリー表示 ──
            if _step4_beta:
                _cls_alerts_s4 = st.session_state.get('classification_alerts', [])
                _cls_errors_s4 = [a for a in _cls_alerts_s4 if a['severity'] == 'error']
                _cls_warnings_s4 = [a for a in _cls_alerts_s4 if a['severity'] == 'warning']
                if _cls_errors_s4:
                    st.markdown(
                        f'<div style="background:#fef9c3;border:1px solid #ca8a04;border-radius:6px;padding:10px 14px;margin:8px 0;font-size:13px">'
                        f'✅ <b>部品・工賃区分確認済み</b> — {len(_cls_errors_s4)} 件の要確認項目が確認・承認された上でNEOを生成しました。<br>'
                        + ''.join(f'<div style="margin-top:4px">⚠️ 行{a["row_no"]}「{a["name"]}」: 部品¥{a["parts_amount"]:,} / 工賃¥{a["wage"]:,}</div>' for a in _cls_errors_s4)
                        + '</div>',
                        unsafe_allow_html=True
                    )
                elif _cls_warnings_s4:
                    st.markdown(
                        f'<div style="background:#f0fdf4;border:1px solid #16a34a;border-radius:6px;padding:10px 14px;margin:8px 0;font-size:13px">'
                        f'✅ <b>部品・工賃区分チェック: 問題なし</b> — 参考警告 {len(_cls_warnings_s4)} 件のみ（重大エラーなし）</div>',
                        unsafe_allow_html=True
                    )
                else:
                    st.markdown(
                        '<div style="background:#f0fdf4;border:1px solid #16a34a;border-radius:6px;padding:10px 14px;margin:8px 0;font-size:13px">'
                        '✅ <b>部品・工賃区分チェック: 問題なし</b></div>',
                        unsafe_allow_html=True
                    )

            # ── ベタ打ちモード: PDF原本との差異特定レポート ──
            if _step4_beta and _discrepancies_step4:
                st.markdown('<div class="section-title">📋 ベタ打ちモード — 差異特定レポート</div>', unsafe_allow_html=True)
                st.markdown('金額の不一致箇所を特定するための詳細レポートをPDF形式でダウンロードできます。')
                # Step4はStep3とは別ブランチのため、wage_match_sp/spをStep4内で再計算する
                _sp_s4 = safe_int(short_parts_wage)
                _pdf_wages_s4 = safe_int(pdf_wages or 0)
                _wage_match_sp_s4 = (_pdf_wages_s4 > 0 and calc_wages + _sp_s4 == _pdf_wages_s4)
                # ショートパーツはHonda Cars等で工賃列に含まれるため、差異レポートの計算値に加算
                _calc_wages_report = calc_wages + _sp_s4 if _wage_match_sp_s4 else calc_wages
                beta_pdf_bytes = generate_beta_discrepancy_report_pdf(estimate_data, calc_parts, _calc_wages_report, pdf_parts or 0, pdf_wages or 0, updated_vehicle)
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
                    'custom_neo_bytes', 'custom_neo_name',
                    'tax_override',
                    'classification_confirmed', 'classification_alerts',
                    'discrepancies', 'total_diff',
                    'amount_confirmed',
                    '_original_items',
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
