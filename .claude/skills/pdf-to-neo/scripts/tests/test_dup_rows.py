# -*- coding: utf-8 -*-
"""同じ名前・同じ単価の行が並ぶときの部品コードの配り方（draft_estimate._dup_ref_pick）。ADDATA は使わない（偽の部品表）。

実機の部品表が枝番（(NO.n)）で位置を分けている族のときだけ、印字の順に 1 つずつ配る。
名前がまったく同じだけの族は触らない（同じ部品を 2 行に書いた見積と見分けられない）。

    PYTHONIOENCODING=utf-8 python .claude/skills/pdf-to-neo/scripts/tests/test_dup_rows.py
"""
from __future__ import annotations

import os
import sys

HERE = os.path.dirname(os.path.realpath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
import skill_env  # noqa: E402
skill_env.apply()
import draft_estimate as de  # noqa: E402
from draft_estimate import _dup_runs  # noqa: E402
from estimate_to_neo import AddataParts  # noqa: E402

FAILS: list[str] = []


class FakeParts:
    """name20_by_ref / block_by_ref / norm_name / block_of だけの部品表"""

    def __init__(self, names: dict, blocks: dict):
        self.name20_by_ref = names
        self.block_by_ref = blocks
        self.norm_name = AddataParts.norm_name

    def block_of(self, ref):
        return self.block_by_ref.get(ref, '')


def drafter(names: dict, blocks: dict, units: dict):
    d = de.Drafter.__new__(de.Drafter)
    d.parts = FakeParts(names, blocks)
    d._std_unit = lambda r, pn='': units.get(r, 0)   # noqa: SLF001
    return d


# 枝番つきの族（ランクル系 リテーナ NO.1〜NO.6 と同じ形）: 6 行に 6 個を印字の順に配る
NUMBERED = {3898: ('LRﾘﾃ-ﾅ(NO.6)',), 3899: ('RRﾘﾃ-ﾅ(NO.5)',),
            3904: ('LRﾘﾃ-ﾅ(NO.3)', 'LRﾘﾃ-ﾅ(NO.4)'), 3905: ('RRﾘﾃ-ﾅ(NO.3)', 'RRﾘﾃ-ﾅ(NO.4)'),
            3910: ('LRﾘﾃ-ﾅ(NO.1)', 'LRﾘﾃ-ﾅ(NO.2)'), 3911: ('RRﾘﾃ-ﾅ(NO.1)', 'RRﾘﾃ-ﾅ(NO.2)')}
# 枝番の無い族（フリードのファスナ・ランクルのエルボジョイントと同じ形）: 触らない
PLAIN = {3900: ('LRﾌﾞﾗｹﾂﾄ',), 3906: ('LRﾌﾞﾗｹﾂﾄ',), 3912: ('LRﾌﾞﾗｹﾂﾄ',)}


def chk(cond, msg):
    if not cond:
        FAILS.append(msg)


def main():
    blocks = {r: 'X35' for r in list(NUMBERED) + list(PLAIN)}
    units = {**{r: 1190 for r in NUMBERED}, **{r: 850 for r in PLAIN}}
    d = drafter({**NUMBERED, **PLAIN}, blocks, units)

    # 1. 枝番つき 6 行: 印字の順に 3898/3899/3904/3905/3910/3911
    got = [d._dup_ref_pick('ﾘﾃｰﾅ', '', 1190, 1, 3898, p, 6) for p in range(6)]
    chk(got == [3898, 3899, 3904, 3905, 3910, 3911], f'1: 枝番つき 6 行の配り方が {got}')

    # 2. 枝番の無い族は触らない（同じ部品を 2 行に書いた見積と見分けられない）
    chk(d._dup_ref_pick('左Rrﾌﾞﾗｹｯﾄ', 'L', 850, 1, 3912, 1, 3) is None,
        '2: 枝番の無い族を配っている（人が確かめた正解では同じ部品コードが 2 行に入る）')

    # 3. 候補の数が行の数と違えば触らない
    chk(d._dup_ref_pick('ﾘﾃｰﾅ', '', 1190, 1, 3898, 1, 3) is None, '3: 候補 6 個・行 3 本で配っている')
    chk(d._dup_ref_pick('ﾘﾃｰﾅ', '', 1190, 1, 3898, 5, 9) is None, '3b: 候補 6 個・行 9 本で配っている')

    # 4. 数十円の小物（同じ単価の部品が多く、偶然と見分けられない）
    d90 = drafter({**NUMBERED}, {r: 'X35' for r in NUMBERED}, {r: 90 for r in NUMBERED})
    chk(d90._dup_ref_pick('ﾘﾃｰﾅ', '', 90, 1, 3898, 1, 6) is None, '4: 単価 90 円でも配っている')

    # 5. 呼び方の境目（1 行・範囲外・金額なし・数量で割り切れない）
    for lbl, args in (('1 行', ('ﾘﾃｰﾅ', '', 1190, 1, 3898, 0, 1)),
                      ('範囲外', ('ﾘﾃｰﾅ', '', 1190, 1, 3898, 6, 6)),
                      ('金額なし', ('ﾘﾃｰﾅ', '', 0, 1, 3898, 1, 6)),
                      ('数量 0', ('ﾘﾃｰﾅ', '', 1190, 0, 3898, 1, 6)),
                      ('割り切れない', ('ﾘﾃｰﾅ', '', 1191, 2, 3898, 1, 6)),
                      ('ref なし', ('ﾘﾃｰﾅ', '', 1190, 1, 0, 1, 6))):
        chk(d._dup_ref_pick(*args) is None, f'5: {lbl} で配っている')

    # 6. 行に左右があれば同じ側だけを候補にする（左 3 個 → 3 行）
    got_l = [d._dup_ref_pick('左ﾘﾃｰﾅ', 'L', 1190, 1, 3898, p, 3) for p in range(3)]
    chk(got_l == [3898, 3904, 3910], f'6: 左の 3 行の配り方が {got_l}')
    got_r = [d._dup_ref_pick('右ﾘﾃｰﾅ', 'R', 1190, 1, 3899, p, 3) for p in range(3)]
    chk(got_r == [3899, 3905, 3911], f'6b: 右の 3 行の配り方が {got_r}')

    # 7. 族（左右・前後を外した名前）は norm_name の 'RR'→'R' 潰しに引きずられない
    chk(d._family_names(3898) == d._family_names(3899) == {'ﾘﾃﾅ'},
        f'7: 左リヤと右リヤが同じ族にならない: {d._family_names(3898)} / {d._family_names(3899)}')

    # 7b. 枝番は括弧無し（'…ﾘﾃ-ﾅNO.2'）でも同じ族にする（ADDATA には両方の書き方がある）
    BARE = {3970: ('Rﾊﾞﾝﾊﾟｱﾂﾊﾟﾘﾃ-ﾅNO.1',), 3974: ('Rﾊﾞﾝﾊﾟｱﾂﾊﾟﾘﾃ-ﾅNO.2',), 3976: ('Rﾊﾞﾝﾊﾟｱﾂﾊﾟﾘﾃ-ﾅNO.3',)}
    db = drafter(BARE, {r: 'X35' for r in BARE}, {r: 155 for r in BARE})
    chk(len({tuple(sorted(db._family_names(r))) for r in BARE}) == 1,
        f'7b: 括弧無しの枝番が同じ族にならない: {[sorted(db._family_names(r)) for r in BARE]}')
    got_b = [db._dup_ref_pick('ﾊﾞﾝﾊﾟｰ ｸﾘｯﾌﾟ', '', 155, 1, 3970, p, 3) for p in range(3)]
    chk(got_b == [3970, 3974, 3976], f'7b: 括弧無しの枝番 3 行の配り方が {got_b}')

    # 7c. 20 文字名の頭の枠（左右・前後）は、空欄（空白）でも字でも同じ族になる。枠の無い名前も壊さない
    FRAME = {1: ('  ﾘｻﾞ-ﾌﾞﾀﾝｸｷﾔﾂﾌﾟ',), 2: (' Rﾘｻﾞ-ﾌﾞﾀﾝｸｷﾔﾂﾌﾟ',), 3: ('LRﾘｻﾞ-ﾌﾞﾀﾝｸｷﾔﾂﾌﾟ',),
             4: ('R ﾘｻﾞ-ﾌﾞﾀﾝｸｷﾔﾂﾌﾟ',), 5: ('ﾘｻﾞ-ﾌﾞﾀﾝｸｷﾔﾂﾌﾟ',)}
    dfr = drafter(FRAME, {r: 'X35' for r in FRAME}, {r: 1380 for r in FRAME})
    fams = {r: tuple(sorted(dfr._family_names(r))) for r in FRAME}
    chk(len(set(fams.values())) == 1, f'7c: 頭の枠の外し方で族が分かれる: {fams}')
    chk(dfr._family_names(2) == {'ﾘｻﾞﾌﾞﾀﾝｸｷﾔﾂﾌﾟ'}, f'7c: 左右が空欄のとき前後の字が残っている: {dfr._family_names(2)}')

    # 7d. 1 つの部品が複数の名前を持つとき、枝番の有無は**当たった族**で見る
    #     （別の族の名前に枝番があるからといって配らない）
    #     13 は 'ｷﾔﾂﾌﾟ' の族だけ。当たった族（ﾎ-ｽ）で絞らないと候補に混ざり、数が合わなくなる
    MIX = {11: ('  ｷﾔﾂﾌﾟ', '  ﾎ-ｽNO.1'), 12: ('  ｷﾔﾂﾌﾟ', '  ﾎ-ｽNO.2'), 13: ('  ｷﾔﾂﾌﾟ',)}
    dmx = drafter(MIX, {r: 'X35' for r in MIX}, {r: 1380 for r in MIX})
    chk(dmx._families(11) == {'ｷﾔﾂﾌﾟ': False, 'ﾎｽ': True}, f'7d: 族ごとの枝番の持ち方が {dmx._families(11)}')
    chk(dmx._dup_ref_pick('ｷｬｯﾌﾟ', '', 1380, 1, 11, 1, 2) is None,
        '7d: 枝番の無い族（ｷﾔﾂﾌﾟ）を、別の名前（ﾎ-ｽNO.n）の枝番を根拠に配っている')
    chk(dmx._dup_ref_pick('ﾎｰｽ', '', 1380, 1, 11, 1, 2) == 12, '7d: 枝番のある族（ﾎ-ｽ）を配っていない')

    # 8. 組の作り方（_dup_runs）: 続けて並んだ行だけを 1 つの組にする
    def R(name, price, **kw):
        return dict({'name': name, 'price': price, 'qty': 1, '_block_title': 'A'}, **kw)
    chk(_dup_runs([R('ﾘﾃｰﾅ', 1190), R('ﾘﾃｰﾅ', 1190), R('ﾘﾃｰﾅ', 1190)]) == {0: (0, 3), 1: (1, 3), 2: (2, 3)},
        '8: 続けて並んだ 3 行が 1 つの組にならない')
    chk(_dup_runs([R('ﾘﾃｰﾅ', 1190), R('ﾎｰｽ', 500), R('ﾘﾃｰﾅ', 1190)]) == {},
        '8b: 間に別の行が入っても同じ組にしている（別の部位の同名の行を巻き込む）')
    chk(_dup_runs([R('ﾘﾃｰﾅ', 1190), R('ﾘﾃｰﾅ', 1190, _block_title='B')]) == {},
        '8c: 見出しをまたいで同じ組にしている')
    chk(_dup_runs([R('ﾘﾃｰﾅ', 1190), R('ﾘﾃｰﾅ', 1190, qty=2)]) == {}, '8d: 数量の違う行を同じ組にしている')
    chk(_dup_runs([R('ﾘﾃｰﾅ', 1190, code='3898'), R('ﾘﾃｰﾅ', 1190, code='3899')]) == {},
        '8e: 部品コードの印字がある行を数えている')
    chk(_dup_runs([R('ﾘﾃｰﾅ', 1190, parts_no='12345-67890'), R('ﾘﾃｰﾅ', 1190, parts_no='12345-67890')]) == {},
        '8f: 品番の印字がある行を数えている')
    chk(_dup_runs([R('ﾘﾃｰﾅ', 1190, manual=True), R('ﾘﾃｰﾅ', 1190, manual=True)]) == {},
        '8g: 手入力の行を数えている')
    chk(_dup_runs([R('ﾘﾃｰﾅ', 0), R('ﾘﾃｰﾅ', 0)]) == {} and _dup_runs([R('', 1190), R('', 1190)]) == {},
        '8h: 金額なし・名前なしの行を数えている')
    # 2 つの組が続けて出てきたら別々に数える
    chk(_dup_runs([R('A', 100), R('A', 100), R('B', 200), R('B', 200)])
        == {0: (0, 2), 1: (1, 2), 2: (0, 2), 3: (1, 2)}, '8i: 続けて出た 2 つの組を分けていない')

    print('test_dup_rows:', 'all ok' if not FAILS else f'{len(FAILS)} 件が不合格')
    for f in FAILS:
        print('  -', f)
    return 1 if FAILS else 0


if __name__ == '__main__':   # 取り込まれただけで止まらないように（テスト収集で読み込まれることがある）
    sys.exit(main())
