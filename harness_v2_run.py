"""ハーネス v2 本体: Planner1 / Generator2 / Evaluator3 で 20+ 反復。

各反復:
  1. Planner: 履歴から戦略 A, B を提案
  2. Generator A, B: 並列で 5件PDFを処理
  3. Evaluator x3: 各結果を 車両/部品/工賃 で独立スコア化
  4. ベスト戦略を選んで params.json に書込み
"""
from __future__ import annotations
import os, sys, json, time, copy, importlib, traceback, io
# Windows cp932 対策: stdout/stderr を UTF-8 に
try:
    sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding='utf-8', errors='replace')
    sys.stderr = io.TextIOWrapper(sys.stderr.buffer, encoding='utf-8', errors='replace')
except Exception:
    pass
from concurrent.futures import ThreadPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

from dotenv import load_dotenv
load_dotenv(os.path.join(HERE, '.env'))

import harness_v2_planner    as PL
import harness_v2_evaluators as EV
import harness_generator     as GE
import harness_evaluator     as RUNNER

V2_DIR = os.path.join(HERE, '_harness_v2')
os.makedirs(V2_DIR, exist_ok=True)
HISTORY_PATH = os.path.join(V2_DIR, 'history.json')
GT_PATH      = os.path.join(V2_DIR, 'ground_truth.json')

PDFS = [
    r"C:\Users\竹下\Desktop\工場見積\工場見積書.pdf",
    r"C:\Users\竹下\Desktop\工場見積\工場最終見積.pdf",
    r"C:\Users\竹下\Desktop\工場見積\工場二次見積.pdf",
    r"C:\Users\竹下\Desktop\工場見積\工場一次見積.pdf",
    r"C:\Users\竹下\Desktop\工場見積\工場見積り.pdf",
]


def reload_app():
    import app, pdf_to_neo_pipeline
    importlib.reload(app)
    importlib.reload(pdf_to_neo_pipeline)


def run_pipeline_with_params(pdf_path: str, params: dict) -> dict:
    """params を適用して 1 PDF を処理。"""
    GE.write_params(0, params, [])
    reload_app()
    return RUNNER.run_pipeline(pdf_path, model_name='gemini-2.5-flash')


def evaluate_strategy(params: dict, gt: dict, label: str = '?') -> dict:
    """1 strategy で全 PDF を評価。"""
    GE.write_params(0, params, [])
    reload_app()

    results = []
    avg = {'total_score': 0, 'time_score': 0, 'vehicle_score': 0,
           'parts_score': 0, 'labor_score': 0, 'elapsed_s': 0}

    print(f"  [Gen-{label}] 5件PDF評価中...", flush=True)
    # 並列度2 で評価
    actuals = []
    with ThreadPoolExecutor(max_workers=2) as ex:
        actuals = list(ex.map(lambda p: RUNNER.run_pipeline(p, model_name='gemini-2.5-flash'), PDFS))

    for actual in actuals:
        fname = actual['file']
        g = gt.get(fname, {})
        # actualをEV.evaluate_3way 形式に整形
        actual_for_ev = {
            'items':         actual.get('items', []),
            'vehicle_info':  (actual.get('ocr_meta', {}) or {}).get('_vehicle_info', {}),
        }
        gt_for_ev = {
            'items':        g.get('items', []),
            'vehicle_info': g.get('vehicle_info', {}),
        }
        score = EV.evaluate_3way(actual_for_ev, gt_for_ev, actual['elapsed_s'])
        score['file'] = fname
        results.append(score)

    n = len(results)
    if n:
        avg['total_score']   = round(sum(r['total_score']   for r in results) / n, 2)
        avg['elapsed_s']     = round(sum(r['elapsed_s']     for r in results) / n, 2)
        avg['vehicle_score'] = round(sum(r['vehicle']['score'] for r in results) / n, 3)
        avg['parts_score']   = round(sum(r['parts']['score']   for r in results) / n, 3)
        avg['labor_score']   = round(sum(r['labor']['score']   for r in results) / n, 3)
        avg['time_score']    = round(sum(r['time_score']     for r in results) / n, 3)

    return {'avg': avg, 'per_file': results, 'params': params}


def aggregate_score(eval_result: dict) -> dict:
    """Generator結果を planner 用 score に変換 (代表は最低スコアファイル基準でなく avg)"""
    avg = eval_result['avg']
    return {
        'total_score': avg['total_score'],
        'elapsed_s':   avg['elapsed_s'],
        'time_score':  avg['time_score'],
        'vehicle': {'score': avg['vehicle_score'], 'matches': 0, 'total': 0},
        'parts':   {'score': avg['parts_score'],   'pn_match': 0, 'pn_total': 0, 'price_match': 0, 'name_match': 0},
        'labor':   {'score': avg['labor_score'],   'wage_diff_pct': 0, 'idx_match': 0, 'idx_total': 0},
    }


def generate_gt():
    """既存 _harness の GT を流用 (5 PDF 共通)"""
    src = os.path.join(HERE, '_harness', 'ground_truth.json')
    if not os.path.exists(src):
        print("ERROR: フェーズ1 GT がありません")
        sys.exit(1)
    with open(src, encoding='utf-8') as f:
        gt = json.load(f)
    # Add vehicle_info from same source if available
    with open(GT_PATH, 'w', encoding='utf-8') as f:
        json.dump(gt, f, ensure_ascii=False, indent=2)
    print(f"[GT] {len(gt)} 件 (流用)")
    return gt


def load_history() -> list:
    if os.path.exists(HISTORY_PATH):
        with open(HISTORY_PATH, encoding='utf-8') as f:
            return json.load(f)
    return []


def save_history(h: list):
    with open(HISTORY_PATH, 'w', encoding='utf-8') as f:
        json.dump(h, f, ensure_ascii=False, indent=2)


def run_iteration(n: int, history: list, gt: dict) -> dict:
    """1 反復: Planner → 2 Generator (parallel) → 3 Evaluator → ベスト選択"""
    current_params = history[-1]['winner']['params'] if history else {}
    strats = PL.propose_strategies(n, history, current_params)
    A_params, B_params = strats[0], strats[1]

    print(f"\n[Iter {n}] Strategy A: extra={A_params.get('prompt_extra','')[:30]!r} dpi={A_params.get('dpi')} unified={A_params.get('use_unified')} think={A_params.get('thinking_budget')}")
    print(f"[Iter {n}] Strategy B: extra={B_params.get('prompt_extra','')[:30]!r} dpi={B_params.get('dpi')} unified={B_params.get('use_unified')} think={B_params.get('thinking_budget')}")

    # Generator A 実行
    print(f"[Iter {n}] Generator A 実行...", flush=True)
    res_A = evaluate_strategy(A_params, gt, label='A')
    print(f"[Iter {n}] Gen-A 結果: 総合={res_A['avg']['total_score']:.2f} / 時間={res_A['avg']['elapsed_s']:.1f}s / 車両={res_A['avg']['vehicle_score']*100:.1f}% / 部品={res_A['avg']['parts_score']*100:.1f}% / 工賃={res_A['avg']['labor_score']*100:.1f}%")

    # Generator B 実行
    print(f"[Iter {n}] Generator B 実行...", flush=True)
    res_B = evaluate_strategy(B_params, gt, label='B')
    print(f"[Iter {n}] Gen-B 結果: 総合={res_B['avg']['total_score']:.2f} / 時間={res_B['avg']['elapsed_s']:.1f}s / 車両={res_B['avg']['vehicle_score']*100:.1f}% / 部品={res_B['avg']['parts_score']*100:.1f}% / 工賃={res_B['avg']['labor_score']*100:.1f}%")

    # 勝者選択
    if res_A['avg']['total_score'] >= res_B['avg']['total_score']:
        winner = res_A; loser = res_B; w_label = 'A'
    else:
        winner = res_B; loser = res_A; w_label = 'B'
    print(f"[Iter {n}] [WIN] Winner: Strategy {w_label}")

    entry = {
        'iteration': n,
        'A':         res_A,
        'B':         res_B,
        'winner':    {'label': w_label, 'params': winner['params'], 'avg': winner['avg']},
        'score':     aggregate_score(winner),
        'timestamp': time.strftime('%Y-%m-%d %H:%M:%S'),
    }
    history.append(entry)
    save_history(history)
    with open(os.path.join(V2_DIR, f'iter{n:02d}.json'), 'w', encoding='utf-8') as f:
        json.dump(entry, f, ensure_ascii=False, indent=2)
    return entry


def write_final_report(history: list):
    if not history: return
    best = max(history, key=lambda h: h['winner']['avg']['total_score'])
    initial = history[0]
    final   = history[-1]

    lines = [
        '# ハーネス v2 (1 Planner / 2 Generator / 3 Evaluator) 最終レポート',
        '',
        f"反復数: {len(history)} / 対象 PDF: 5件",
        f"実行日時: {time.strftime('%Y-%m-%d %H:%M:%S')}",
        '',
        '## 反復別スコア (winner)',
        '',
        '| 反復 | 勝者 | 総合 | 時間 | 車両% | 部品% | 工賃% |',
        '|-----|------|------|-----|------|------|------|',
    ]
    for h in history:
        w = h['winner']
        a = w['avg']
        lines.append(f"| {h['iteration']} | {w['label']} | {a['total_score']:.2f} | {a['elapsed_s']:.1f}s | {a['vehicle_score']*100:.1f} | {a['parts_score']*100:.1f} | {a['labor_score']*100:.1f} |")

    a = best['winner']['avg']
    lines += [
        '',
        '## ベスト構成',
        '',
        f"反復: **{best['iteration']}** / 勝者: **Strategy {best['winner']['label']}** / 総合: **{a['total_score']:.2f}**",
        '',
        '```json',
        json.dumps(best['winner']['params'], ensure_ascii=False, indent=2),
        '```',
        '',
        '## 初期 vs 最終',
        '',
        f"- 総合: {initial['winner']['avg']['total_score']:.2f} → {final['winner']['avg']['total_score']:.2f} ({final['winner']['avg']['total_score'] - initial['winner']['avg']['total_score']:+.2f})",
        f"- 時間: {initial['winner']['avg']['elapsed_s']:.1f}s → {final['winner']['avg']['elapsed_s']:.1f}s ({final['winner']['avg']['elapsed_s'] - initial['winner']['avg']['elapsed_s']:+.1f}s)",
        f"- 車両: {initial['winner']['avg']['vehicle_score']*100:.1f}% → {final['winner']['avg']['vehicle_score']*100:.1f}%",
        f"- 部品: {initial['winner']['avg']['parts_score']*100:.1f}% → {final['winner']['avg']['parts_score']*100:.1f}%",
        f"- 工賃: {initial['winner']['avg']['labor_score']*100:.1f}% → {final['winner']['avg']['labor_score']*100:.1f}%",
    ]
    out = os.path.join(V2_DIR, 'FINAL_REPORT_v2.md')
    with open(out, 'w', encoding='utf-8') as f:
        f.write('\n'.join(lines))
    print(f"[FINAL] {out}")


def main():
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument('--iterations', type=int, default=20)
    args = ap.parse_args()

    gt = generate_gt()
    history = load_history()
    start = (history[-1]['iteration'] + 1) if history else 1

    for n in range(start, args.iterations + 1):
        try:
            run_iteration(n, history, gt)
        except Exception as e:
            print(f"\n[Iter {n}] ERROR: {e}")
            traceback.print_exc()
            time.sleep(3)
            continue

    # 最終: ベスト構成を本番 params.json に書込み
    if history:
        best = max(history, key=lambda h: h['winner']['avg']['total_score'])
        GE.write_params(99, best['winner']['params'], [])
        print(f"\n[FINAL] ベスト構成を本番 params.json に保存 (Strategy {best['winner']['label']})")
    write_final_report(history)


if __name__ == '__main__':
    main()
