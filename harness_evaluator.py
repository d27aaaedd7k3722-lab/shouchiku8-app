"""ハーネス Evaluator: PDFをパイプラインに通し、GT と比較してスコア化する。"""
from __future__ import annotations
import os, sys, time, json, math
from concurrent.futures import ThreadPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

from dotenv import load_dotenv
load_dotenv(os.path.join(HERE, '.env'))


def _safe_int(v):
    try:
        return int(str(v).replace(',', ''))
    except Exception:
        return 0


def _safe_float(v):
    try:
        return float(str(v).replace(',', ''))
    except Exception:
        return 0.0


def _norm_pn(s: str) -> str:
    """品番正規化: 大文字化・空白除去・全角→半角"""
    if not s:
        return ''
    return ''.join(str(s).upper().split()).replace('　', '').replace('-', '').replace('・', '')


def run_pipeline(pdf_path: str, model_name: str = None, addata_root: str = '', template: str = '') -> dict:
    """1件のPDFをパイプラインに通し、結果と所要時間を返す。"""
    from pdf_to_neo_pipeline import process_pdf_to_neo
    if not addata_root:
        try:
            from addata_locator import find_addata
            addata_root = find_addata() or ''
        except Exception:
            addata_root = ''
    if not template:
        template = os.path.join(HERE, 'template_toyota.neo')

    t0 = time.perf_counter()
    err = None
    try:
        kwargs = {'addata_root': addata_root, 'template_path': template}
        if model_name:
            kwargs['model_name'] = model_name
        result = process_pdf_to_neo(pdf_path, **kwargs)
    except Exception as e:
        result = {}
        err = str(e)
    elapsed = time.perf_counter() - t0

    items = result.get('items') or []
    ocr   = result.get('ocr_meta') or {}
    return {
        'file':         os.path.basename(pdf_path),
        'elapsed_s':    round(elapsed, 2),
        'items':        items,
        'ocr_meta':     ocr,
        'mode':         result.get('mode', '—'),
        'pdf_grand':    _safe_int(ocr.get('pdf_grand_total', 0)),
        'items_total':  sum(_safe_int(it.get('parts_amount', 0)) + _safe_int(it.get('wage', 0)) for it in items if isinstance(it, dict)),
        'item_count':   len(items),
        'error':        err,
    }


def _time_score(seconds: float) -> float:
    """sigmoid: 15s→1.0, 30s→0.5, 60s→0.1"""
    if seconds <= 0:
        return 0.0
    return 1.0 / (1.0 + math.exp((seconds - 22.5) / 7.5))


def score_against_gt(actual: dict, gt: dict) -> dict:
    """1件の actual を gt と比較してスコア dict を返す。"""
    if actual.get('error'):
        return {
            'file':         actual['file'],
            'elapsed_s':    actual['elapsed_s'],
            'total_score':  0.0,
            'time_score':   0.0,
            'amount_score': 0.0,
            'pn_score':     0.0,
            'idx_score':    0.0,
            'count_score':  0.0,
            'amount_match': False,
            'pn_match':     0,
            'pn_total':     0,
            'idx_match':    0,
            'idx_total':    0,
            'error':        actual['error'],
        }

    # 時間
    t_score = _time_score(actual['elapsed_s'])

    # 金額一致
    a_diff = abs(actual['items_total'] - (gt.get('items_total') or actual['items_total']))
    a_base = max(gt.get('items_total') or 1, 1)
    a_pct  = a_diff / a_base
    a_score = 1.0 if a_pct <= 0.005 else max(0.0, 1.0 - a_pct * 10)

    # 品番一致 (GTにあるものとマッチング)
    gt_items     = gt.get('items') or []
    actual_items = actual.get('items') or []

    # GTの品番をkey、actualから対応する品番を取得
    gt_pns     = [_norm_pn(it.get('parts_no') or it.get('part_number') or '') for it in gt_items if isinstance(it, dict)]
    actual_pns = [_norm_pn(it.get('parts_no') or it.get('part_number') or '') for it in actual_items if isinstance(it, dict)]
    gt_pn_set     = set(p for p in gt_pns if p)
    actual_pn_set = set(p for p in actual_pns if p)
    pn_match = len(gt_pn_set & actual_pn_set)
    pn_total = len(gt_pn_set)
    pn_score = (pn_match / pn_total) if pn_total else 1.0

    # 指数一致 (品番マッチを基準に近接探索)
    idx_match = 0
    idx_total = 0
    for git_dict in gt_items:
        if not isinstance(git_dict, dict):
            continue
        gpn = _norm_pn(git_dict.get('parts_no') or git_dict.get('part_number') or '')
        gidx = _safe_float(git_dict.get('index_value') or git_dict.get('index', ''))
        if not gpn or gidx == 0:
            continue
        idx_total += 1
        for ait in actual_items:
            if not isinstance(ait, dict):
                continue
            apn = _norm_pn(ait.get('parts_no') or ait.get('part_number') or '')
            if apn == gpn:
                aidx = _safe_float(ait.get('index_value') or ait.get('index', ''))
                if abs(aidx - gidx) <= 0.1:
                    idx_match += 1
                break
    idx_score = (idx_match / idx_total) if idx_total else 1.0

    # 行数一致
    count_score = min(actual['item_count'], gt.get('item_count', actual['item_count'])) \
                  / max(gt.get('item_count', actual['item_count']), 1)

    total = 100 * (t_score * 0.30 + a_score * 0.25 + pn_score * 0.20
                   + idx_score * 0.15 + count_score * 0.10)

    return {
        'file':         actual['file'],
        'elapsed_s':    actual['elapsed_s'],
        'total_score':  round(total, 2),
        'time_score':   round(t_score, 3),
        'amount_score': round(a_score, 3),
        'pn_score':     round(pn_score, 3),
        'idx_score':    round(idx_score, 3),
        'count_score':  round(count_score, 3),
        'amount_match': a_pct <= 0.005,
        'pn_match':     pn_match,
        'pn_total':     pn_total,
        'idx_match':    idx_match,
        'idx_total':    idx_total,
        'item_count':   actual['item_count'],
        'pdf_grand':    actual['pdf_grand'],
        'items_total':  actual['items_total'],
    }


def evaluate_all(pdf_paths: list, gt_data: dict, model_name: str = None, parallel: int = 2) -> dict:
    """全PDFを評価。並列実行可能。"""
    results = []
    actuals = []

    def _proc(p):
        return run_pipeline(p, model_name=model_name)

    if parallel > 1:
        with ThreadPoolExecutor(max_workers=parallel) as ex:
            actuals = list(ex.map(_proc, pdf_paths))
    else:
        for p in pdf_paths:
            actuals.append(_proc(p))

    for actual in actuals:
        gt = gt_data.get(actual['file'], {})
        if not gt:
            gt = {'items_total': actual['items_total'], 'item_count': actual['item_count'], 'items': actual['items']}
        score = score_against_gt(actual, gt)
        results.append(score)

    avg_total = sum(r['total_score'] for r in results) / max(len(results), 1)
    avg_time  = sum(r['elapsed_s'] for r in results) / max(len(results), 1)
    avg_pn    = sum(r['pn_score'] for r in results) / max(len(results), 1)
    avg_amt   = sum(r['amount_score'] for r in results) / max(len(results), 1)

    return {
        'avg_total':    round(avg_total, 2),
        'avg_time':     round(avg_time, 2),
        'avg_pn':       round(avg_pn, 3),
        'avg_amount':   round(avg_amt, 3),
        'per_file':     results,
    }


if __name__ == '__main__':
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument('--pdfs', nargs='+', required=True)
    ap.add_argument('--gt',   default='')
    ap.add_argument('--model', default=None)
    ap.add_argument('--out',  default='')
    args = ap.parse_args()

    gt = {}
    if args.gt and os.path.exists(args.gt):
        with open(args.gt, encoding='utf-8') as f:
            gt = json.load(f)

    res = evaluate_all(args.pdfs, gt, model_name=args.model)
    print(json.dumps(res, ensure_ascii=False, indent=2))
    if args.out:
        with open(args.out, 'w', encoding='utf-8') as f:
            json.dump(res, f, ensure_ascii=False, indent=2)
