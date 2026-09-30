# -*- coding: utf-8 -*-
"""human_neo_accuracy.py — **人が作った NEO を正解にして**、下書きの部品コードの当たりを測る。

`code_accuracy.py` の正解は担当が直した reading（担当が書かなかった行は下書きの結果を認めたもの）なので、
担当が気づかなかった取り違えは正解に数えられる＝**上限**しか分からない。こちらは案件フォルダに残っている
**人の NEO**（コグニで作った協定見積・確報）を正解にするので、下書きとは独立している。

行の揃え方は `neo_compare.align`（品番 → 金額 → 品番の違い → 部品金額 → 工賃）。
揃った組のうち**両方に部品コードがある行**だけを数える（人の NEO の手入力行・ベタ打ちの NEO は数えない）。

    PYTHONIOENCODING=utf-8 python .claude/skills/pdf-to-neo/scripts/verify/human_neo_accuracy.py [案件 …] [--base _nc] [-v]
      案件を書かなければ、その base の案件のうち人の NEO が見つかるもの全部
      -v  外れた行を出す（正解 / 下書き / 名前 / 金額）

案件フォルダ（Z:）の場所は `<NEO_CHECK_ROOT>/<base>/cases.json` の src、人の NEO は
`<NEO_CHECK_ROOT>/_verify/survey.json`（survey_cases.py が作る）から引く。**顧客名は出さない**（案件名だけ）。
`-v` で出す部品名は NEO の `PartsName`（ADDATA の部品名か見積書に印字された部品名。20 バイトの欄）で、
顧客名・登録番号は入らない。人の NEO のファイル名は登録番号を含むので**長さだけ**を出す。
終了コード: 1 = 名指しした案件が測れない・1 行も測れなかった
"""
from __future__ import annotations

import argparse
import collections
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.realpath(__file__))))
sys.path.insert(0, os.path.dirname(os.path.realpath(__file__)))
from _common import NEO_CHECK, load_json, work_dir  # noqa: E402
import neo_compare as ncmp  # noqa: E402


def _code(r: dict) -> str:
    c = str(r.get('PartsCode') or '').strip()
    return '' if c in ('', '0', '-1') else c.zfill(4)


def _same_dir(a, b) -> bool:
    """同じ案件フォルダか。cases.json も survey.json も '/' 区切りで書くが、
    区切りの向き・末尾の '/'・大文字小文字で取りこぼさないように正規化して比べる（Codex 指摘）"""
    def norm(x):
        x = str(x or '').rstrip('/\\')
        return os.path.normcase(os.path.normpath(x)) if x else ''
    return bool(norm(a)) and norm(a) == norm(b)


def human_neos(case_src: str) -> list:
    """survey.json から、その案件フォルダにある人の NEO の道を返す（survey に並んだ順）"""
    sv = load_json(os.path.join(NEO_CHECK, '_verify', 'survey.json')) or []
    for r in sv:
        if _same_dir(r.get('dir'), case_src):
            return [os.path.join(str(r['dir']).replace('/', os.sep), n) for n in (r.get('neo') or [])]
    return []


def measure(case: str, base: str, src: str):
    """(測った行, 一致, 外れの一覧, 使った人の NEO の名前) / 測れなければ None"""
    ours = os.path.join(work_dir(base), case, 'auto.neo')
    if not os.path.exists(ours):
        return None
    best = None
    for p in human_neos(src):
        if not os.path.exists(p):
            continue
        try:
            other = ncmp.load(p)
        except Exception:  # noqa: BLE001
            continue
        if sum(1 for r in other if _code(r)) < 5:
            continue   # ベタ打ちの NEO（部品コードが空）は答えにならない
        mine = ncmp.load(ours)
        a, b, _l, _r, pairs = ncmp.align(mine, other)
        n = ok = 0
        bad = []
        for _kind, i, j in pairs:
            x, y = a[i], b[j]
            cy = _code(y)
            if not cy:
                continue    # 人の側が手入力の行
            n += 1
            cx = _code(x)
            if cx == cy:
                ok += 1
            else:
                bad.append({'right': cy, 'got': cx, 'name': str(x.get('PartsName') or '')[:20],
                            'price': x.get('PartsPriceOutTax'), 'wage': x.get('WageOutTax'), 'kind': _kind})
        if n and (best is None or n > best[0]):
            best = (n, ok, bad, os.path.basename(p))
    return best


def _case_list(base: str) -> list:
    """その base の案件一覧。`cases.json` が無ければ `cases*.json` のいちばん大きいものを使う（_batch は cases_batch2.json）"""
    d = work_dir(base)
    p = os.path.join(d, 'cases.json')
    if not os.path.exists(p):
        got = sorted((os.path.getsize(os.path.join(d, f)), f) for f in os.listdir(d)
                     if f.startswith('cases') and f.endswith('.json')) if os.path.isdir(d) else []
        if not got:
            return []
        p = os.path.join(d, got[-1][1])
    c = load_json(p) or []
    return c if isinstance(c, list) else list(c.values())


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('cases', nargs='*')
    ap.add_argument('--base', default='_nc')
    ap.add_argument('-v', action='store_true')
    a = ap.parse_args()
    cases = _case_list(a.base)
    by_name = {c['name']: c for c in cases if isinstance(c, dict)}
    want = a.cases or [c['name'] for c in cases if isinstance(c, dict) and not c.get('skip')]
    tot_n = tot_ok = 0
    kinds = collections.Counter()
    errors = []
    for name in want:
        c = by_name.get(name)
        if not c:
            print(name, '案件一覧に無い')
            errors.append(name)
            continue
        r = measure(name, a.base, c.get('src') or '')
        if r is None:
            if a.cases:
                print(name, '測れない（auto.neo が無い・人の NEO が無い/ベタ打ち・揃う行が無い）')
                errors.append(name)
            continue
        n, ok, bad, neo_name = r
        tot_n += n
        tot_ok += ok
        print(f'{name}: 人の NEO と比べて 正 {ok}/{n}' + (f'  外れ {len(bad)}' if bad else '')
              + f'（{len(neo_name)} 文字の NEO 名は伏せる）')
        for x_ in bad:
            kinds[x_['kind']] += 1
            if a.v:
                print(f"    正 {x_['right']} / 下書き {x_['got'] or '（手入力）'}  {x_['name']} {x_['price']} {x_['wage']}  [{x_['kind']}で揃えた]")
    print(f'計: {tot_ok}/{tot_n}（{tot_ok * 100 / max(tot_n, 1):.1f}%）')
    if kinds:
        print('  外れた行の揃え方: ' + ' / '.join(f'{k} {v}' for k, v in kinds.most_common()))
    if errors:
        print(f'測れなかった案件 {len(errors)}: {", ".join(errors)}')
    return 1 if (errors or tot_n == 0) else 0


if __name__ == '__main__':
    sys.exit(main())
