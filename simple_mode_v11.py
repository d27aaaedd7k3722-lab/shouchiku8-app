#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""v11.0 シンプルモード UI

非エンジニアの社員さんが drag-and-drop だけで使えるよう、画面を以下に集約:
  ① 見積 PDF (必須)
  ② 車検証 PDF (任意)
  ③ 原本 NEO ファイル (任意)
  → [NEO ファイルを作成] ボタン
  → 結果カード (PDF/NEO 総額、ダウンロード)

すべて日本語表記。エラーは「何が起きたか / 次にどうするか」をペアで表示。
"""
from __future__ import annotations
import os, io, time, traceback
import streamlit as st


def _label_with_chip(text: str, chip_label: str, chip_color: str = '#0e7490') -> str:
    return (
        f'<div style="display:flex;align-items:center;gap:8px;margin:8px 0 4px;">'
        f'<span style="font-weight:700;font-size:1.05rem;color:#0f172a">{text}</span>'
        f'<span style="background:{chip_color};color:white;padding:2px 8px;'
        f'border-radius:10px;font-size:0.75rem;font-weight:600">{chip_label}</span>'
        f'</div>'
    )


def _humanize_error(exc: Exception) -> dict:
    """例外を「何が起きたか / 次にどうするか」のペアに翻訳する。"""
    msg = str(exc)
    cls = type(exc).__name__

    if 'GEMINI_API_KEY' in msg or 'api_key' in msg.lower():
        return {
            'title': '🔑 AIキーが設定されていません',
            'why': 'Gemini API キー (.env の GEMINI_API_KEY) が見つかりません。',
            'how': 'PCの管理者に「.env ファイルに GEMINI_API_KEY を入れて下さい」とお伝え下さい。',
        }
    if 'timeout' in msg.lower() or 'deadline' in msg.lower():
        return {
            'title': '⏱️ AI処理がタイムアウトしました',
            'why': 'PDFが大きすぎる、またはネット接続が遅い可能性があります。',
            'how': 'もう一度ボタンを押してみてください。何度も失敗する場合は PDF を分割してから投入して下さい。',
        }
    if 'quota' in msg.lower() or '429' in msg:
        return {
            'title': '📊 AI利用枠を使い切りました',
            'why': 'Gemini の今日の無料枠（約250件）を超過した可能性があります。',
            'how': '明日になると自動でリセットされます。緊急の場合は、サイドバーから AIモデルを「pro」に切り替えてください。',
        }
    if 'corrupt' in msg.lower() or 'damaged' in msg.lower() or 'invalid' in msg.lower():
        return {
            'title': '📄 PDF ファイルが壊れています',
            'why': 'PDF が正しく読み取れませんでした。',
            'how': 'もう一度 PDF を保存しなおして投入して下さい。',
        }
    if '(02)' in msg or 'could not convert string to float' in msg:
        return {
            'title': '🔢 数字の読取りで失敗しました',
            'why': '見積に括弧書きや特殊な数字表記が含まれていて変換できませんでした。',
            'how': '管理者に連絡して下さい。v11.0 で対策済みですが、未対応の表記がある可能性があります。',
        }
    if 'NEO' in msg and ('破損' in msg or 'broken' in msg.lower()):
        return {
            'title': '📦 原本 NEO ファイルが正しくありません',
            'why': '指定された .neo ファイルが破損しているか、コグニセブン形式ではない可能性があります。',
            'how': '原本 NEO ファイルを使わずにもう一度試して下さい（任意項目です）。',
        }
    return {
        'title': f'⚠️ 想定外のエラー ({cls})',
        'why': msg[:200] if msg else '詳細不明のエラーが発生しました。',
        'how': '管理者に画面のスクリーンショットを送って下さい。問題を調べます。',
    }


def _show_error(exc: Exception):
    """エラーを優しく表示。"""
    e = _humanize_error(exc)
    st.error(f"### {e['title']}\n\n**何が起きたか:** {e['why']}\n\n**次にどうするか:** {e['how']}")
    with st.expander('🔧 開発者向け詳細（管理者にコピペ送付して下さい）', expanded=False):
        st.code(f'{type(exc).__name__}: {exc}\n\n{traceback.format_exc()}')


def _process_with_progress(estimate_bytes: bytes, vehicle_bytes, original_neo_bytes,
                            api_key: str, model_name: str = 'gemini-2.5-flash') -> dict:
    """pipeline を呼びつつ進捗を表示。Returns: {ok, neo_bytes, csv_bytes, summary_text, ...}"""
    progress = st.progress(0, text='準備中...')
    log_area = st.empty()

    import tempfile
    with tempfile.NamedTemporaryFile(suffix='.pdf', delete=False) as tf:
        tf.write(estimate_bytes); est_path = tf.name
    try:
        progress.progress(10, text='① 見積 PDF を読込み中...')

        try:
            from addata_locator import find_addata
            addata_root = find_addata() or ''
        except Exception:
            addata_root = ''
        template = os.path.join(os.path.dirname(__file__), 'template_toyota.neo')
        if original_neo_bytes:
            with tempfile.NamedTemporaryFile(suffix='.neo', delete=False) as tf:
                tf.write(original_neo_bytes); template = tf.name
            progress.progress(20, text='② 原本 NEO を反映準備...')

        progress.progress(30, text='③ AI で OCR 解析中... (30秒〜2分)')
        log_area.caption('Gemini AI で見積内容を読取り中...')
        import pdf_to_neo_pipeline as P
        os.environ['GEMINI_MODEL'] = model_name
        vehicle_info = None
        if vehicle_bytes:
            try:
                from app import analyze_vehicle_registration
                progress.progress(40, text='④ 車検証 PDF も並行解析中...')
                vehicle_info = analyze_vehicle_registration(api_key, vehicle_bytes, 'application/pdf')
                if not isinstance(vehicle_info, dict):
                    vehicle_info = None
            except Exception as _ve:
                log_area.caption(f'車検証OCR失敗(無視可): {_ve}')
                vehicle_info = None

        progress.progress(60, text='⑤ 見積明細を NEO 形式に変換中...')
        kwargs = {
            'addata_root': addata_root,
            'template_path': template,
        }
        if vehicle_info:
            kwargs['vehicle_info'] = vehicle_info
        result = P.process_pdf_to_neo(est_path, **kwargs)
        progress.progress(90, text='⑥ NEO ファイルを書き出し中...')

        items = result.get('items') or []
        items_total = sum(
            ((it.get('parts_amount') or it.get('amount') or 0)
             + (it.get('wage') or it.get('labor_fee') or 0))
            for it in items if isinstance(it, dict)
        )
        meta = result.get('ocr_meta') or {}
        pdf_total = meta.get('pdf_grand_total') or 0
        if pdf_total:
            pdf_outtax = round(pdf_total / 1.1)
            tax_diff = items_total - pdf_outtax
        else:
            pdf_outtax = items_total
            tax_diff = 0

        progress.progress(100, text='✅ 完了！')
        time.sleep(0.3)
        progress.empty()
        log_area.empty()

        return {
            'ok': bool(result.get('neo_bytes')),
            'neo_bytes': result.get('neo_bytes'),
            'csv_bytes': result.get('csv_bytes'),
            'pdf_total': pdf_total,
            'items_total': items_total,
            'tax_diff': tax_diff,
            'mode': result.get('mode'),
            'items_count': len(items),
            'used_vehicle': vehicle_info is not None,
            'used_template': original_neo_bytes is not None,
            'warnings': result.get('warnings') or [],
            'pipeline_log': result.get('log') or [],
        }
    finally:
        try: os.unlink(est_path)
        except Exception: pass


def render(api_key: str, model_name: str = 'gemini-2.5-flash'):
    """シンプルモード本体。app.py:main() の冒頭から呼ばれる。"""

    st.markdown("""
    <div style="background:linear-gradient(135deg,#0e7490 0%,#06b6d4 100%);
                padding:24px;border-radius:12px;color:white;margin-bottom:24px;">
        <h1 style="margin:0;font-size:1.8rem;">🚗 SHOUCHIKU8 NEO ファイル自動作成</h1>
        <div style="margin-top:6px;opacity:.92;font-size:0.95rem;">
            見積 PDF を投げ込んで、ボタン1つでコグニセブン用 NEO ファイルが作れます。
        </div>
    </div>
    """, unsafe_allow_html=True)

    if not api_key:
        st.warning('⚠️ AIキー (GEMINI_API_KEY) が設定されていません。管理者に連絡して下さい。')
        return

    st.markdown(_label_with_chip('① 見積 PDF を入れて下さい', '必須', '#dc2626'),
                unsafe_allow_html=True)
    estimate_pdf = st.file_uploader(
        ' ',
        type=['pdf'],
        key='_v11_estimate_pdf',
        label_visibility='collapsed',
        help='ここに見積 PDF をドラッグ&ドロップして下さい',
    )

    col_a, col_b = st.columns(2)
    with col_a:
        st.markdown(_label_with_chip('② 車検証 PDF（あれば精度↑）', '任意', '#475569'),
                    unsafe_allow_html=True)
        vehicle_pdf = st.file_uploader(
            ' ',
            type=['pdf'],
            key='_v11_vehicle_pdf',
            label_visibility='collapsed',
            help='車検証 PDF があれば、車両情報を自動で反映します。なくてもOK。',
        )
    with col_b:
        st.markdown(_label_with_chip('③ 原本 NEO（あれば既存情報引継ぎ）', '任意', '#475569'),
                    unsafe_allow_html=True)
        original_neo = st.file_uploader(
            ' ',
            type=['neo'],
            key='_v11_original_neo',
            label_visibility='collapsed',
            help='以前作成済の .neo ファイルがあれば、そこに記入された保険情報を引継ぎます。',
        )

    st.markdown('---')

    btn_col_a, btn_col_b, btn_col_c = st.columns([1, 2, 1])
    with btn_col_b:
        run = st.button(
            '📥 NEO ファイルを作成',
            type='primary',
            use_container_width=True,
            disabled=(estimate_pdf is None),
            key='_v11_run_btn',
        )

    if estimate_pdf is None:
        st.caption('⬆ 見積 PDF を入れるとボタンが押せます')
        return

    if run:
        try:
            est_bytes = estimate_pdf.getvalue()
            veh_bytes = vehicle_pdf.getvalue() if vehicle_pdf else None
            tpl_bytes = original_neo.getvalue() if original_neo else None
            with st.spinner('処理中... (30秒〜2分かかります)'):
                t0 = time.time()
                result = _process_with_progress(
                    est_bytes, veh_bytes, tpl_bytes,
                    api_key=api_key, model_name=model_name,
                )
                elapsed = time.time() - t0
            st.session_state['_v11_last_result'] = result
            st.session_state['_v11_last_elapsed'] = elapsed
            st.session_state['_v11_last_filename'] = estimate_pdf.name
        except Exception as e:
            _show_error(e)
            return

    res = st.session_state.get('_v11_last_result')
    if res:
        elapsed = st.session_state.get('_v11_last_elapsed', 0)
        fname = st.session_state.get('_v11_last_filename', '見積.pdf')
        if res.get('ok'):
            badge = '✅ 完成しました'
            badge_color = '#16a34a'
        else:
            badge = '⚠️ 一部問題があります（詳細は下）'
            badge_color = '#f59e0b'

        st.markdown(f"""
        <div style="background:white;border:2px solid {badge_color};border-radius:12px;
                    padding:20px;margin-top:16px;">
          <div style="font-size:1.3rem;font-weight:700;color:{badge_color};">{badge}</div>
          <div style="margin-top:6px;color:#475569;font-size:0.9rem;">{fname} を {elapsed:.0f} 秒で処理</div>
        </div>
        """, unsafe_allow_html=True)

        c1, c2, c3 = st.columns(3)
        c1.metric('明細件数', f"{res.get('items_count', 0)} 件")
        if res.get('pdf_total'):
            c2.metric('PDF 総額（税込）', f"¥{res['pdf_total']:,}")
        c3.metric('処理モード', res.get('mode') or '-')

        chips = []
        if res.get('used_vehicle'):
            chips.append('🚗 車検証データ反映')
        if res.get('used_template'):
            chips.append('📦 原本NEO引継ぎ')
        if chips:
            st.caption(' / '.join(chips))

        if res.get('neo_bytes'):
            d1, d2 = st.columns(2)
            base = fname.replace('.pdf', '')
            with d1:
                st.download_button(
                    '📥 .neo ダウンロード',
                    data=res['neo_bytes'],
                    file_name=f'{base}.neo',
                    mime='application/octet-stream',
                    type='primary',
                    use_container_width=True,
                    key='_v11_dl_neo',
                )
            with d2:
                if res.get('csv_bytes'):
                    st.download_button(
                        '📋 明細 CSV',
                        data=res['csv_bytes'],
                        file_name=f'{base}_明細.csv',
                        mime='text/csv',
                        use_container_width=True,
                        key='_v11_dl_csv',
                    )

        if res.get('warnings'):
            with st.expander('⚠️ 警告', expanded=False):
                for w in res['warnings']:
                    st.write(f'- {w}')

        with st.expander('🔧 詳細ログ（管理者向け）', expanded=False):
            for line in res.get('pipeline_log', [])[:30]:
                st.code(line, language=None)
