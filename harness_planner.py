"""ハーネス Planner: 前回スコアから次のパラメータ変異を決定する。

戦略:
  - 反復1〜5: 高速化方向 (ラスタライズOFF, FAXフィルタOFF, thinking=0)
  - 反復6〜10: 精度方向 (ラスタライズON, DPI増, FAXフィルタON, self_correction厳しく)
  - 反復11〜15: prompt_extra をローテーション (品番補強 / 指数補強 / 列構造)
  - 反復16〜20: 最良パラメータの周辺を探索 (Hill climbing)
"""
from __future__ import annotations
import os, json, copy

PROMPT_EXTRAS = [
    "",
    "\n【追加】部品番号(part_number)は必ずハイフン・スペース・スラッシュも含めて完全一致で転写すること。OCR誤読を避けるため、不確実な文字は空文字にすること。",
    "\n【追加】指数(index_value)は記載通り厳密抽出。0.1, 0.2, 0.3 等の小数点以下も省略しない。記載なしは空文字、ゼロではない。",
    "\n【追加】列の取り違えを避けるため、行の作業区分（取替/脱着/調整/塗装）を必ず確認し、それに応じた列マッピングで部品代と工賃を分離すること。",
    "\n【追加】合計行(小計/部品計/工賃計/塗装計/値引/総合計)は details に絶対に含めない。これらは verify_rows へ。",
    "\n【追加】1ページ目に車両情報(車名/型式/車台番号/型式指定/類別区分/初度登録)が記載されている。必ず抽出すること。",
]


def propose_next(iteration: int, history: list, current_params: dict) -> dict:
    """次の反復のパラメータを返す。

    history: 過去の {iteration, params, score} list
    """
    p = copy.deepcopy(current_params)
    # フェーズ2: 統合プロンプトを常時有効化
    p['use_unified'] = True

    # ベスト履歴
    best = max(history, key=lambda h: h.get('score', {}).get('avg_total', 0)) if history else None
    last = history[-1] if history else None

    # 失敗パターン分析
    failure = ''
    if last:
        s = last.get('score', {})
        if s.get('avg_time', 999) > 25:
            failure += 'slow '
        if s.get('avg_pn', 1) < 0.95:
            failure += 'pn_miss '
        if s.get('avg_amount', 1) < 0.95:
            failure += 'amount_miss '

    if iteration <= 5:
        # 高速化探索フェーズ
        configs = [
            {'use_fax_filter': False, 'use_rasterize': False, 'thinking_budget': 0, 'temperature': 0.0, 'dpi': 300},
            {'use_fax_filter': False, 'use_rasterize': False, 'thinking_budget': 0, 'temperature': 0.0, 'dpi': 250},
            {'use_fax_filter': False, 'use_rasterize': False, 'thinking_budget': 0, 'temperature': 0.1, 'dpi': 300},
            {'use_fax_filter': True,  'use_rasterize': False, 'thinking_budget': 0, 'temperature': 0.0, 'dpi': 300},
            {'use_fax_filter': False, 'use_rasterize': True,  'thinking_budget': 0, 'temperature': 0.0, 'dpi': 250},
        ]
        cfg = configs[(iteration - 1) % len(configs)]
        p.update(cfg)
        p['prompt_extra'] = ''
    elif iteration <= 10:
        # 精度方向探索
        configs = [
            {'use_fax_filter': True,  'use_rasterize': True, 'thinking_budget': 0,    'dpi': 300, 'self_correction_threshold': 100},
            {'use_fax_filter': True,  'use_rasterize': True, 'thinking_budget': 0,    'dpi': 350, 'self_correction_threshold': 100},
            {'use_fax_filter': True,  'use_rasterize': True, 'thinking_budget': 1000, 'dpi': 300, 'self_correction_threshold': 100},
            {'use_fax_filter': True,  'use_rasterize': True, 'thinking_budget': 0,    'dpi': 300, 'self_correction_threshold': 50},
            {'use_fax_filter': False, 'use_rasterize': True, 'thinking_budget': 0,    'dpi': 300, 'self_correction_threshold': 100},
        ]
        cfg = configs[(iteration - 6) % len(configs)]
        p.update(cfg)
        p['temperature'] = 0.0
        p['prompt_extra'] = ''
    elif iteration <= 15:
        # プロンプト探索フェーズ - ベース設定は best から
        if best:
            p.update(best['params'])
        idx = (iteration - 11) % len(PROMPT_EXTRAS)
        p['prompt_extra'] = PROMPT_EXTRAS[idx]
    else:
        # Hill climbing - ベスト周辺の微調整
        if best:
            p.update(best['params'])
        # ランダムな小変動
        if 'pn_miss' in failure:
            p['prompt_extra'] = PROMPT_EXTRAS[1]  # 品番強化
            p['temperature'] = 0.0
        elif 'amount_miss' in failure:
            p['prompt_extra'] = PROMPT_EXTRAS[4]  # 合計行除外
        elif 'slow' in failure:
            p['use_rasterize'] = False
            p['thinking_budget'] = 0
        else:
            # 既にバランス取れている → DPI微調整
            p['dpi'] = max(200, min(400, p.get('dpi', 300) + (10 if iteration % 2 == 0 else -10)))

    return p


def format_feedback(score: dict) -> str:
    """planner用のテキストフィードバック生成。"""
    lines = [
        f"前回スコア: 総合={score.get('avg_total', 0)} / 時間={score.get('avg_time', 0)}秒",
        f"  品番一致率={score.get('avg_pn', 0)*100:.1f}% / 金額一致率={score.get('avg_amount', 0)*100:.1f}%",
    ]
    for r in score.get('per_file', [])[:5]:
        lines.append(f"  - {r['file']}: 総合={r['total_score']}, 時間={r['elapsed_s']}秒, "
                     f"品番={r.get('pn_match', 0)}/{r.get('pn_total', 0)}, "
                     f"金額={'OK' if r.get('amount_match') else 'NG'}")
    return '\n'.join(lines)


if __name__ == '__main__':
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument('--iter', type=int, required=True)
    ap.add_argument('--history', default='')
    ap.add_argument('--current', default='')
    args = ap.parse_args()

    history = []
    if args.history and os.path.exists(args.history):
        with open(args.history, encoding='utf-8') as f:
            history = json.load(f)
    current = {}
    if args.current and os.path.exists(args.current):
        with open(args.current, encoding='utf-8') as f:
            current = json.load(f).get('params', {})

    proposed = propose_next(args.iter, history, current)
    print(json.dumps(proposed, ensure_ascii=False, indent=2))
