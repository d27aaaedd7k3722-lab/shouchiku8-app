"""ハーネス本体: Planner→Generator→Evaluator を 20+回ループ。"""
from __future__ import annotations
import os, sys, json, time, importlib, argparse, traceback

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

from dotenv import load_dotenv
load_dotenv(os.path.join(HERE, '.env'))

import harness_planner   as PL
import harness_generator as GE
import harness_evaluator as EV

HARNESS_DIR = os.path.join(HERE, '_harness')
HISTORY_PATH = os.path.join(HARNESS_DIR, 'history.json')
GT_PATH      = os.path.join(HARNESS_DIR, 'ground_truth.json')

DEFAULT_PARAMS = {
    "use_fax_filter":          False,
    "use_rasterize":           False,
    "use_enhance":             True,
    "enable_self_correction":  True,
    "dpi":                     300,
    "thinking_budget":         0,
    "temperature":             0.0,
    "max_output_tokens":       65536,
    "self_correction_threshold": 100,
    "prompt_extra":            "",
}


def reload_app():
    """app.py を再読込して HARNESS_PARAMS を反映"""
    import app
    importlib.reload(app)
    import pdf_to_neo_pipeline
    importlib.reload(pdf_to_neo_pipeline)


def generate_ground_truth(pdfs: list, model: str) -> dict:
    """反復0: Claude or 高精度Geminiで GT を生成"""
    print(f"\n[Iter 0] Ground Truth 生成中 (model={model})...")
    GE.write_params(0, DEFAULT_PARAMS, [])
    reload_app()

    gt = {}
    for pdf in pdfs:
        fname = os.path.basename(pdf)
        print(f"  → {fname}", flush=True)
        actual = EV.run_pipeline(pdf, model_name=model)
        if actual.get('error'):
            print(f"    ERROR: {actual['error']}", flush=True)
            continue
        gt[fname] = {
            'items':       actual['items'],
            'item_count':  actual['item_count'],
            'items_total': actual['items_total'],
            'pdf_grand':   actual['pdf_grand'],
            'elapsed_s':   actual['elapsed_s'],
        }
        print(f"    OK: {actual['item_count']}行 / {actual['elapsed_s']}秒", flush=True)
    with open(GT_PATH, 'w', encoding='utf-8') as f:
        json.dump(gt, f, ensure_ascii=False, indent=2)
    print(f"[Iter 0] GT 保存: {GT_PATH} ({len(gt)} 件)\n")
    return gt


def load_history() -> list:
    if os.path.exists(HISTORY_PATH):
        with open(HISTORY_PATH, encoding='utf-8') as f:
            return json.load(f)
    return []


def save_history(h: list) -> None:
    with open(HISTORY_PATH, 'w', encoding='utf-8') as f:
        json.dump(h, f, ensure_ascii=False, indent=2)


def run_iteration(n: int, pdfs: list, gt: dict, history: list, model: str) -> dict:
    """1反復実行"""
    last_score = history[-1]['score'] if history else None
    current_params = history[-1]['params'] if history else DEFAULT_PARAMS

    # Planner
    proposed = PL.propose_next(n, history, current_params)
    print(f"\n[Iter {n}] Planner提案: {json.dumps(proposed, ensure_ascii=False)}")

    # Generator
    GE.write_params(n, proposed, history)
    reload_app()

    # Evaluator
    print(f"[Iter {n}] Evaluator 実行中 ({len(pdfs)}件)...", flush=True)
    t0 = time.perf_counter()
    score = EV.evaluate_all(pdfs, gt, model_name=model, parallel=2)
    iter_elapsed = time.perf_counter() - t0
    score['iter_elapsed'] = round(iter_elapsed, 1)

    # 履歴に追加
    entry = {
        'iteration': n,
        'params':    proposed,
        'score':     score,
        'timestamp': time.strftime('%Y-%m-%d %H:%M:%S'),
    }
    history.append(entry)
    save_history(history)

    # スコア保存
    with open(os.path.join(HARNESS_DIR, f'iter{n:02d}_scores.json'), 'w', encoding='utf-8') as f:
        json.dump(entry, f, ensure_ascii=False, indent=2)

    # 表示
    print(f"[Iter {n}] 総合={score['avg_total']} / 時間={score['avg_time']}秒 / 品番={score['avg_pn']*100:.1f}% / 金額={score['avg_amount']*100:.1f}%")
    print(f"          反復所要時間: {score['iter_elapsed']}秒")

    return entry


def write_final_report(history: list, gt: dict) -> None:
    """最終レポート"""
    if not history:
        return
    best = max(history, key=lambda h: h['score']['avg_total'])
    initial = history[0]
    final   = history[-1]

    lines = [
        '# PDF→CSV 精度・時間最適化 ハーネス 最終レポート',
        '',
        f'実行日時: {time.strftime("%Y-%m-%d %H:%M:%S")}',
        f'反復数: {len(history)}',
        f'対象PDF: {len(gt)} 件',
        '',
        '## 総合スコア推移',
        '',
        '| 反復 | 総合 | 時間(秒) | 品番% | 金額% | params概要 |',
        '|------|------|---------|------|------|-----------|',
    ]
    for h in history:
        s = h['score']
        p = h['params']
        psum = f"raster={p.get('use_rasterize')}/fax={p.get('use_fax_filter')}/dpi={p.get('dpi')}/think={p.get('thinking_budget')}"
        lines.append(f"| {h['iteration']} | {s['avg_total']} | {s['avg_time']} | {s['avg_pn']*100:.1f} | {s['avg_amount']*100:.1f} | {psum} |")

    lines += [
        '',
        '## ベスト構成',
        '',
        f"反復: **{best['iteration']}** / 総合スコア: **{best['score']['avg_total']}**",
        '',
        '```json',
        json.dumps(best['params'], ensure_ascii=False, indent=2),
        '```',
        '',
        '## 初期 vs 最終',
        '',
        f"- 総合: {initial['score']['avg_total']} → {final['score']['avg_total']} (改善: {final['score']['avg_total'] - initial['score']['avg_total']:+.2f})",
        f"- 平均時間: {initial['score']['avg_time']}秒 → {final['score']['avg_time']}秒 ({final['score']['avg_time'] - initial['score']['avg_time']:+.2f})",
        f"- 品番一致率: {initial['score']['avg_pn']*100:.1f}% → {final['score']['avg_pn']*100:.1f}%",
        f"- 金額一致率: {initial['score']['avg_amount']*100:.1f}% → {final['score']['avg_amount']*100:.1f}%",
    ]
    out = os.path.join(HARNESS_DIR, 'FINAL_REPORT.md')
    with open(out, 'w', encoding='utf-8') as f:
        f.write('\n'.join(lines))
    print(f"\n[FINAL] レポート保存: {out}")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--pdfs', nargs='+', required=True)
    ap.add_argument('--iterations', type=int, default=20)
    ap.add_argument('--gt-model', default='gemini-2.5-flash',
                    help="GT生成用モデル. ANTHROPIC_API_KEY設定時は claude-sonnet-4-6 推奨")
    ap.add_argument('--ocr-model', default='gemini-2.5-flash')
    ap.add_argument('--skip-gt', action='store_true', help="既存GTを再利用")
    ap.add_argument('--target-score', type=float, default=95.0)
    ap.add_argument('--target-time',  type=float, default=15.0)
    args = ap.parse_args()

    os.makedirs(HARNESS_DIR, exist_ok=True)

    # PDFs 検証
    pdfs = []
    for p in args.pdfs:
        if os.path.exists(p):
            pdfs.append(p)
        else:
            print(f"WARN: PDF not found: {p}")
    if not pdfs:
        print("ERROR: 有効な PDF が1件もありません")
        sys.exit(1)

    # GT
    if args.skip_gt and os.path.exists(GT_PATH):
        with open(GT_PATH, encoding='utf-8') as f:
            gt = json.load(f)
        print(f"[GT] 既存ファイル使用: {len(gt)} 件")
    else:
        gt = generate_ground_truth(pdfs, args.gt_model)
        if not gt:
            print("ERROR: GT 生成失敗")
            sys.exit(1)

    # 履歴復元
    history = load_history()
    start_iter = (history[-1]['iteration'] + 1) if history else 1

    # ループ
    for n in range(start_iter, args.iterations + 1):
        try:
            entry = run_iteration(n, pdfs, gt, history, args.ocr_model)
            s = entry['score']
            if s['avg_total'] >= args.target_score and s['avg_time'] <= args.target_time:
                print(f"\n🎯 目標達成 (反復 {n})!  総合={s['avg_total']} / 時間={s['avg_time']}秒")
                if n >= 20:  # 最低20回は実行
                    break
        except Exception as e:
            print(f"\n[Iter {n}] ERROR: {e}")
            traceback.print_exc()
            time.sleep(5)
            continue

    write_final_report(history, gt)


if __name__ == '__main__':
    main()
