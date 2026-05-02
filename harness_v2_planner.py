"""ハーネス v2: Planner — 履歴+3 Evaluator から戦略 A/B を提案する。

戦略空間:
  - prompt_focus: vehicle / parts / labor / balanced
  - api_pattern:  unified / dedicated / hybrid
  - dpi:          250 / 300 / 350
  - thinking:     0 / 500 / 1500
  - shop_extra:   on / off
  - extra_pn:     強化PNプロンプト on / off
"""
from __future__ import annotations
import copy

# 強化プロンプト群
_PN_BOOST = ("\n【重点部品番号(part_number) 重点抽出】"
             "車両部品番号は5桁数字+ハイフン+英数字 (例: 62022-3GSOB, 04711-F4060-ZZ)。"
             "見積書の各部品行に必ず記載されている。一字も省略せず正確に書写する。"
             "見えない場合のみ\"\"。")
_LABOR_BOOST = ("\n【重点工賃・指数 重点抽出】"
                "labor_fee は工賃欄の数値。index_value は指数欄の数値（0.1, 0.5, 1.2 等）。"
                "両方とも記載通り厳密に。空欄は labor_fee=0, index_value=\"\"")
_VEHICLE_BOOST = ("\n【重点車両情報 重点抽出】"
                  "1ページ目ヘッダから maker(メーカー)/car_name(車名)/car_model(型式)/"
                  "car_serial_no(車体番号)/model_designation(型式指定)/category_number(類別区分) を抽出。"
                  "型式指定と類別区分は数字のみ（例: 12345 / 0001）。NEO生成必須。")


def propose_strategies(iteration: int, history: list, current: dict) -> list:
    """次反復用に2つの戦略 (A, B) を返す。

    Returns: [params_A, params_B]
    """
    base = copy.deepcopy(current)
    base.setdefault('use_unified', True)
    base.setdefault('dpi', 300)
    base.setdefault('thinking_budget', 0)
    base.setdefault('temperature', 0.0)
    base.setdefault('use_fax_filter', False)
    base.setdefault('use_rasterize', False)
    base.setdefault('prompt_extra', '')
    base.setdefault('use_enhance', True)
    base.setdefault('enable_self_correction', True)
    base.setdefault('max_output_tokens', 65536)
    base.setdefault('self_correction_threshold', 100)

    # ベスト履歴
    # history エントリ内の winner.params をベスト基準にする
    def _h_score(h):
        w = h.get('winner') or {}
        return (w.get('avg') or {}).get('total_score', 0)
    def _h_params(h):
        w = h.get('winner') or {}
        return w.get('params') or {}
    best = max(history, key=_h_score) if history else None
    last = history[-1] if history else None

    # 弱点分析: 直近の Evaluator スコアから不足分野を特定
    weak = []
    if last:
        s = last.get('score', {})
        if s.get('parts', {}).get('score', 1) < 0.95:
            weak.append('parts')
        if s.get('labor', {}).get('score', 1) < 0.95:
            weak.append('labor')
        if s.get('vehicle', {}).get('score', 1) < 0.95:
            weak.append('vehicle')

    A = copy.deepcopy(base)
    B = copy.deepcopy(base)

    if iteration <= 5:
        # 探索フェーズ: A=unified+PN強化、B=dedicated+標準
        A['use_unified'] = True
        A['prompt_extra'] = _PN_BOOST
        B['use_unified'] = False
        B['prompt_extra'] = ''
    elif iteration <= 10:
        # 強化フェーズ: A=unified+VEHICLE強化、B=unified+LABOR強化
        A['use_unified'] = True
        A['prompt_extra'] = _VEHICLE_BOOST
        B['use_unified'] = True
        B['prompt_extra'] = _LABOR_BOOST
    elif iteration <= 15:
        # 速度方向: A=unified+thinking=0、B=unified+thinking=500
        if best:
            A.update(_h_params(best))
            B.update(_h_params(best))
        A['thinking_budget'] = 0
        B['thinking_budget'] = 500
    else:
        # Hill climbing: A=ベスト+弱点強化、B=ベスト+別組合せ
        if best:
            A.update(_h_params(best))
            B.update(_h_params(best))
        if 'parts' in weak:
            A['prompt_extra'] = _PN_BOOST
        elif 'labor' in weak:
            A['prompt_extra'] = _LABOR_BOOST
        elif 'vehicle' in weak:
            A['prompt_extra'] = _VEHICLE_BOOST
        else:
            A['prompt_extra'] = ''
        # B はDPIや thinking を変える
        B['dpi'] = 300 if A.get('dpi') != 300 else 350
        B['thinking_budget'] = 0 if A.get('thinking_budget', 0) != 0 else 1000

    return [A, B]


def format_feedback(score: dict) -> str:
    """次反復planner用のフィードバック文字列。"""
    s = score
    lines = [
        f"前回 総合={s['total_score']:.2f} / 時間={s['elapsed_s']:.1f}s",
        f"  車両: {s['vehicle']['score']*100:.1f}% (matches={s['vehicle']['matches']}/{s['vehicle']['total']})",
        f"  部品: {s['parts']['score']*100:.1f}% (PN={s['parts']['pn_match']}/{s['parts']['pn_total']}, "
        f"price={s['parts']['price_match']}/{s['parts']['pn_total']}, name={s['parts']['name_match']}/{s['parts']['pn_total']})",
        f"  工賃: {s['labor']['score']*100:.1f}% (wage_diff={s['labor']['wage_diff_pct']:.1f}%, "
        f"idx={s['labor']['idx_match']}/{s['labor']['idx_total']})",
    ]
    return '\n'.join(lines)
