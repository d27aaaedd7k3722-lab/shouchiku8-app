"""ハーネス v2: 3人の Evaluator が独立にスコア化する。

  Evaluator 1: 車両情報 (メーカー/車名/型式/車体番号/型式指定/類別区分)
  Evaluator 2: 部品 (部品名称/部品番号/部品価格)
  Evaluator 3: 工賃 (作業内容/工賃/工数=指数)
"""
from __future__ import annotations
import os, sys, math, time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)


def _safe_int(v):
    try: return int(str(v).replace(',', ''))
    except: return 0

def _safe_float(v):
    try: return float(str(v).replace(',', ''))
    except: return 0.0

def _norm_pn(s: str) -> str:
    if not s: return ''
    return ''.join(str(s).upper().split()).replace('　', '').replace('-', '').replace('・', '')

def _norm_text(s: str) -> str:
    if not s: return ''
    return ''.join(str(s).split()).strip()


def _time_score(seconds: float) -> float:
    """sigmoid: 15s=1.0, 30s=0.5, 60s=0.1"""
    if seconds <= 0: return 0.0
    return 1.0 / (1.0 + math.exp((seconds - 22.5) / 7.5))


def evaluator_vehicle(actual: dict, gt: dict) -> dict:
    """車両情報 6 フィールドを評価。"""
    fields = ['maker', 'car_name', 'car_model', 'car_serial_no',
              'model_designation', 'category_number']
    a_vinfo = actual.get('vehicle_info', {}) or actual.get('_vehicle_info', {}) or {}
    g_vinfo = gt.get('vehicle_info', {}) or gt.get('_vehicle_info', {}) or {}
    # Aliases
    aliases = {
        'maker':              ['maker', 'car_maker'],
        'car_name':           ['car_name'],
        'car_model':          ['car_model'],
        'car_serial_no':      ['car_serial_no', 'chassis_no'],
        'model_designation':  ['model_designation', 'car_model_designation'],
        'category_number':    ['category_number', 'car_category_number'],
    }
    matches = 0
    total = 0
    detail = {}
    for f in fields:
        a_val = ''
        g_val = ''
        for k in aliases.get(f, [f]):
            if not a_val: a_val = str(a_vinfo.get(k, '') or '')
            if not g_val: g_val = str(g_vinfo.get(k, '') or '')
        an, gn = _norm_text(a_val), _norm_text(g_val)
        if gn:  # GT has value
            total += 1
            if an == gn:
                matches += 1
            detail[f] = {'gt': gn, 'actual': an, 'match': an == gn}
        else:
            detail[f] = {'gt': '', 'actual': an, 'match': None}
    score = (matches / total) if total else 1.0
    return {
        'evaluator': 'vehicle',
        'score':     round(score, 3),
        'matches':   matches,
        'total':     total,
        'detail':    detail,
    }


def evaluator_parts(actual: dict, gt: dict) -> dict:
    """部品: 部品名称/部品番号/部品価格を評価。"""
    a_items = actual.get('items', []) or []
    g_items = gt.get('items', []) or []
    # 部品行のみ（部品単価>0 or 部品金額>0）
    def _is_part(it):
        return _safe_int(it.get('parts_amount') or it.get('part_price') or 0) > 0

    g_parts = [it for it in g_items if isinstance(it, dict) and _is_part(it)]
    # 品番一致 (GT基準)
    g_pns = [_norm_pn(it.get('parts_no') or it.get('part_number') or '') for it in g_parts]
    g_pn_set = set(p for p in g_pns if p)
    a_pn_set = set(_norm_pn(it.get('parts_no') or it.get('part_number') or '')
                   for it in a_items if isinstance(it, dict))
    a_pn_set = set(p for p in a_pn_set if p)
    pn_match = len(g_pn_set & a_pn_set)
    pn_total = len(g_pn_set)
    pn_score = (pn_match / pn_total) if pn_total else 1.0

    # 部品価格一致 (PN マッチ行で価格も一致する比率)
    price_match = 0
    for git in g_parts:
        gpn = _norm_pn(git.get('parts_no') or git.get('part_number') or '')
        if not gpn: continue
        gprice = _safe_int(git.get('parts_amount') or git.get('part_price') or 0)
        for ait in a_items:
            apn = _norm_pn(ait.get('parts_no') or ait.get('part_number') or '')
            if apn == gpn:
                aprice = _safe_int(ait.get('parts_amount') or ait.get('part_price') or 0)
                if abs(aprice - gprice) <= max(gprice * 0.02, 1):
                    price_match += 1
                break
    price_score = (price_match / pn_total) if pn_total else 1.0

    # 部品名称一致 (PN マッチ行で名称も類似する比率)
    name_match = 0
    for git in g_parts:
        gpn = _norm_pn(git.get('parts_no') or git.get('part_number') or '')
        if not gpn: continue
        gname = _norm_text(git.get('name') or git.get('parts_name') or git.get('work_or_part_name') or '')
        for ait in a_items:
            apn = _norm_pn(ait.get('parts_no') or ait.get('part_number') or '')
            if apn == gpn:
                aname = _norm_text(ait.get('name') or ait.get('parts_name') or ait.get('work_or_part_name') or '')
                # 緩い一致: 部分一致 or 完全一致
                if gname and aname and (gname == aname or gname in aname or aname in gname):
                    name_match += 1
                break
    name_score = (name_match / pn_total) if pn_total else 1.0

    score = (pn_score * 0.4 + price_score * 0.3 + name_score * 0.3)
    return {
        'evaluator':   'parts',
        'score':       round(score, 3),
        'pn_match':    pn_match,
        'pn_total':    pn_total,
        'pn_score':    round(pn_score, 3),
        'price_match': price_match,
        'price_score': round(price_score, 3),
        'name_match':  name_match,
        'name_score':  round(name_score, 3),
    }


def evaluator_labor(actual: dict, gt: dict) -> dict:
    """工賃: 作業内容/工賃/指数を評価。"""
    a_items = actual.get('items', []) or []
    g_items = gt.get('items', []) or []
    def _has_wage(it):
        return _safe_int(it.get('wage') or it.get('labor_fee') or 0) > 0

    g_labor = [it for it in g_items if isinstance(it, dict) and _has_wage(it)]
    # 工賃合計一致
    g_wage_total = sum(_safe_int(it.get('wage') or it.get('labor_fee') or 0) for it in g_items if isinstance(it, dict))
    a_wage_total = sum(_safe_int(it.get('wage') or it.get('labor_fee') or 0) for it in a_items if isinstance(it, dict))
    wage_diff_pct = abs(a_wage_total - g_wage_total) / max(g_wage_total, 1)
    wage_total_score = 1.0 if wage_diff_pct <= 0.005 else max(0.0, 1.0 - wage_diff_pct * 5)

    # 行数一致 (工賃行)
    count_score = min(len(a_items), len(g_items)) / max(len(g_items), 1) if g_items else 1.0

    # 指数一致 (PNベース)
    idx_match = 0
    idx_total = 0
    for git in g_items:
        gpn = _norm_pn(git.get('parts_no') or git.get('part_number') or '')
        gidx = _safe_float(git.get('index_value') or git.get('index', ''))
        if not gpn or gidx == 0: continue
        idx_total += 1
        for ait in a_items:
            apn = _norm_pn(ait.get('parts_no') or ait.get('part_number') or '')
            if apn == gpn:
                aidx = _safe_float(ait.get('index_value') or ait.get('index', ''))
                if abs(aidx - gidx) <= 0.1:
                    idx_match += 1
                break
    idx_score = (idx_match / idx_total) if idx_total else 1.0

    score = (wage_total_score * 0.5 + count_score * 0.2 + idx_score * 0.3)
    return {
        'evaluator':         'labor',
        'score':             round(score, 3),
        'wage_total_score':  round(wage_total_score, 3),
        'wage_diff_pct':     round(wage_diff_pct * 100, 2),
        'count_score':       round(count_score, 3),
        'idx_match':         idx_match,
        'idx_total':         idx_total,
        'idx_score':         round(idx_score, 3),
        'a_wage_total':      a_wage_total,
        'g_wage_total':      g_wage_total,
    }


def evaluate_3way(actual: dict, gt: dict, elapsed_s: float) -> dict:
    """3 Evaluator + 時間スコアを統合"""
    e_v = evaluator_vehicle(actual, gt)
    e_p = evaluator_parts(actual, gt)
    e_l = evaluator_labor(actual, gt)
    t_score = _time_score(elapsed_s)

    # 重み: 時間20% / 車両20% / 部品35% / 工賃25%
    total = 100 * (t_score * 0.20 + e_v['score'] * 0.20
                   + e_p['score'] * 0.35 + e_l['score'] * 0.25)

    return {
        'total_score':  round(total, 2),
        'time_score':   round(t_score, 3),
        'elapsed_s':    elapsed_s,
        'vehicle':      e_v,
        'parts':        e_p,
        'labor':        e_l,
    }
