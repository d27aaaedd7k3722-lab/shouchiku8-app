# -*- coding: utf-8 -*-
"""human_neo_accuracy.py — **人が作った NEO を正解にして**、下書きの部品コードの当たりを測る。

`code_accuracy.py` の正解は担当が直した reading（担当が書かなかった行は下書きの結果を認めたもの）なので、
担当が気づかなかった取り違えは正解に数えられる＝**上限**しか分からない。こちらは案件フォルダに残っている
**人の NEO**（コグニで作った協定見積・確報）を正解にするので、下書きとは独立している。

行の揃え方は**身元が同じ行だけ**（品番・数量・部品代・工賃がそろって同じ）。似た行を寄せる揃え方は使わない。
揃った組のうち、**人の側に部品コードがあり、数量・部品代・工賃がそろって同じ行**だけを数える。
人の NEO は**協定のあと**のものなので、金額の変わった行・足し引きされた行は工場見積と別物で、
どの行と組にするかも決められない（そこを数えると、協定の直しを下書きの取り違えとして数えてしまう）。
ベタ打ちの NEO（部品コードが空）と Claude 製の NEO は使わない。

    PYTHONIOENCODING=utf-8 python .claude/skills/pdf-to-neo/scripts/verify/human_neo_accuracy.py [案件 …] [--base _nc] [-v]
      案件を書かなければ、その base の案件のうち人の NEO が見つかるもの全部
      -v  外れた行を出す（正解 / 下書き / 名前 / 金額）

案件フォルダ（Z:）の場所は `<NEO_CHECK_ROOT>/<base>/cases.json` の src、人の NEO は
`<NEO_CHECK_ROOT>/_verify/survey.json`（survey_cases.py が作る）から引く。**顧客名は出さない**（案件名だけ）。
`-v` で出す部品名は NEO の `PartsName`（ADDATA の部品名か見積書に印字された部品名。20 バイトの欄）で、
顧客名・登録番号は入らない。人の NEO のファイル名は登録番号を含むので**長さだけ**を出す。
終了コード: 1 = 名指しした案件が測れない（人の NEO が無い・協定で全部書き替わって比べる行が無い）・全体で 1 行も測れなかった
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


def _row_key(r):
    """行の身元。品番（空白・ハイフンを除く）＋数量＋部品代＋工賃がそろって同じ行は、同じ明細とみなす。
    **品番の無い行は数えない**（作業行・手入力行。金額だけでは別の明細と取り違える）"""
    pn = ncmp._pn(r)
    if not pn:
        return None
    try:
        qty = int(r.get('PartsCount') or 0)
    except (TypeError, ValueError):
        qty = 0
    return (pn, qty, ncmp._amt(r, 'PartsPriceOutTax'), ncmp._amt(r, 'WageOutTax'))


def measure(case: str, base: str, src: str):
    """(測った行, 一致, 外れの一覧, 使った人の NEO の名前, 内訳) / auto.neo か人の NEO が無ければ None。
    内訳は (下書きの行, 人の NEO の行, 人の側にコードのある行, 測れた行)。

    **品番・数量・部品代・工賃がそろって同じ行だけ**を突き合わせる。人の NEO は協定のあとのもので、
    値段の変わった行・足し引きされた行は工場見積と別物だから比べられない。
    似た行を寄せて組にする揃え方（neo_compare.align）は使わない ——
    組にする途中で、金額の合う相手が別の行に取られて、比べられるはずの行が落ちることがある（2026-09-30 Codex 指摘）。

    同じ身元の行が何本もあるとき（同じクリップを 4 個と 1 個で 2 行に分けた見積）は、
    **どの行がどれかを決められない**ので、部品コードの集まりどうしで見る（並び順は見ない）。

    測れる行が 0 でも（協定で全部書き替わった案件）**None ではなく 0 件として返す**。
    黙って飛ばすと、合計が実際よりきれいに見える（2026-09-30 Codex 指摘）"""
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
        if not any(_code(r) for r in other):
            continue   # ベタ打ちの NEO（部品コードが 1 つも無い）は答えにならない。
            # 少ない行数でも答えにはなるので、本数では切らない（切ると小さい修理の案件が黙って落ちる。Codex 指摘）
        mine = ncmp.load(ours)
        a = [r for r in mine if not int(r.get('ReserveFlag') or 0)]    # 保留の行は合計に入らない
        b = [r for r in other if not int(r.get('ReserveFlag') or 0)]
        ours_by, theirs_by = collections.defaultdict(list), collections.defaultdict(list)
        for r in a:
            k = _row_key(r)
            if k:
                ours_by[k].append(r)
        for r in b:
            k = _row_key(r)
            if k and _code(r):
                theirs_by[k].append(r)
        coded = sum(len(v) for v in theirs_by.values())
        n = ok = 0
        bad = []
        for k, theirs in theirs_by.items():
            mine_rows = ours_by.get(k) or []
            if not mine_rows:
                continue          # 協定で足された行（工場見積に無い）
            # 同じ身元の行は順番に意味が無いので、**切り詰めずに**コードの集まりどうしで数える
            # （先頭から切ると、後ろに合うコードがあるのに外れと数えてしまう。2026-09-30 Codex 指摘）
            cnt_mine = collections.Counter(_code(r) for r in mine_rows)
            cnt_theirs = collections.Counter(_code(r) for r in theirs)
            n_k = min(len(theirs), len(mine_rows))
            ok_k = min(sum(min(v, cnt_mine.get(c, 0)) for c, v in cnt_theirs.items()), n_k)
            n += n_k
            ok += ok_k
            miss = n_k - ok_k
            for c, v in (cnt_theirs - cnt_mine).most_common():   # 人の側にあって下書きに無いコード
                for _ in range(min(v, miss)):
                    bad.append({'right': c, 'got': '/'.join(sorted(cnt_mine.elements())),
                                'name': str(theirs[0].get('PartsName') or '')[:20],
                                'price': theirs[0].get('PartsPriceOutTax'), 'wage': theirs[0].get('WageOutTax'),
                                'kind': '品番＋金額'})
                miss -= min(v, miss)
                if miss <= 0:
                    break
        if best is None or n > best[0]:
            best = (n, ok, bad, os.path.basename(p), (len(a), len(b), coded, n))
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
    tot_n = tot_ok = tot_rows = zero = 0
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
            # 名指しした案件と、**一覧が「人の NEO がある」と言っている案件**は黙って飛ばさない。
            # 飛ばすと、survey の道が古い・NEO が読めない・ベタ打ちだった案件が分母から消えて、
            # ほかの案件の数字だけで合格に見える（2026-09-30 Codex 指摘）
            if a.cases or c.get('human_neo_rows') or c.get('has_human_neo'):
                print(name, '測れない（auto.neo が無い・人の NEO が無い/読めない/ベタ打ち）')
                errors.append(name)
            continue
        n, ok, bad, neo_name, cov = r
        tot_n += n
        tot_ok += ok
        tot_rows += cov[0]
        _cov = (f'　［下書き {cov[0]} 行 / 人の NEO {cov[1]} 行 → 人の側にコードと品番のある {cov[2]} 行 → '
                f'品番・数量・金額まで同じ {cov[3]} 行］')
        if not n:
            zero += 1
            print(f'{name}: **測れる行が無い**（協定で数量・金額が全部変わっている）' + _cov)
            # ここに来た時点で「読める人の NEO はあった」のだから、測れ行 0 はいつでも失敗にする
            # （一覧に human_neo_rows の無い古い案件でも隠さない。Codex 指摘）
            errors.append(name)
            continue
        print(f'{name}: 人の NEO と比べて 正 {ok}/{n}' + (f'  外れ {len(bad)}' if bad else '') + _cov)
        for x_ in bad:
            kinds[x_['kind']] += 1
            if a.v:
                print(f"    正 {x_['right']} / 下書き {x_['got'] or '（手入力）'}  {x_['name']} {x_['price']} {x_['wage']}  [{x_['kind']}で揃えた]")
    print(f'計: {tot_ok}/{tot_n}（{tot_ok * 100 / max(tot_n, 1):.1f}%）'
          + f'　下書きの明細 {tot_rows} 行のうち {tot_n} 行（{tot_n * 100 / max(tot_rows, 1):.0f}%）を測った'
          + (f'　／ 測れる行が 1 つも無かった案件 {zero} 件' if zero else ''))
    if kinds:
        print('  外れた行の揃え方: ' + ' / '.join(f'{k} {v}' for k, v in kinds.most_common()))
    if errors:
        print(f'測れなかった案件 {len(errors)}: {", ".join(errors)}')
    return 1 if (errors or tot_n == 0) else 0


if __name__ == '__main__':
    sys.exit(main())
