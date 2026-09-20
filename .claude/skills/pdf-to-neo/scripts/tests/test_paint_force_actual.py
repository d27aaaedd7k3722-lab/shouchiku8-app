# -*- coding: utf-8 -*-
"""塗装: reading が入力方式「実額」を**指定した**ときは、内訳があっても実額で入れる（2026-09-20 亮平さん指示）。
総額 ＝ 塗装工賃計 ＋ 追加項目 ＋ 材料代。内板骨格塗装・ボデーシーリングは別の欄なので畳まない。ADDATA 不要
    PYTHONIOENCODING=utf-8 python .claude/skills/pdf-to-neo/scripts/tests/test_paint_force_actual.py
"""
from __future__ import annotations

import os
import sys

HERE = os.path.dirname(os.path.realpath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
import draft_estimate as de  # noqa: E402


class _D(de.Drafter):
    """Drafter の塗装まわりだけを使う（読み取りの dict を差し替えて呼ぶ）"""
    def __init__(self, rd):
        self.rd = rd
        self.notes = []


def test_forced_actual_folds_details():
    """パネル・追加項目・材料代があっても、指定されたら実額 1 本に畳む"""
    rd = {'paint': {'input_type': '実額'}, 'totals': {}}
    out = {'total': 100000, 'material': 20000, 'material_rate': 20,
           'panels': [{'name': 'ﾄﾞｱ'}], 'lines': [{'name': 'ﾄﾞｱ', 'wage': 100000}],
           'other': [{'name': 'ｱﾝﾀﾞｰｺｰﾄ', 'wage': 5000}], 'booth': {'time': 0.5}}
    got = _D(rd)._paint_input_type(out)
    assert got.get('input_type') == '実額', got
    assert got.get('total') == 105000, got          # 塗装工賃計 + 追加項目（材料代は生成器が総額に足す）
    assert got.get('material') == 20000, got
    for k in ('panels', 'lines', 'other', 'booth', 'material_rate'):
        assert k not in got, (k, got)


def test_forced_actual_restores_material_from_totals():
    """費用割合モードで額を落としていたら、印字の材料代（合計欄）を戻す（実額は割合を持てない）"""
    rd = {'paint': {'actual': True}, 'totals': {'material': 19226}}
    out = {'total': 66294, 'material_rate': 29, 'panels': [{'name': 'ﾄﾞｱ'}]}
    got = _D(rd)._paint_input_type(out)
    assert got.get('input_type') == '実額', got
    assert got.get('material') == 19226, got
    assert 'material_rate' not in got and 'panels' not in got, got


def test_forced_actual_keeps_frame_and_sealing():
    """内板骨格塗装・ボデーシーリングは塗装計とは別の欄なので畳まない（残っていれば生成器は今までどおり一括計上）"""
    rd = {'paint': {'input_type': '実額'}, 'totals': {}}
    out = {'total': 50000, 'frame': {'engine_room': 1}, 'sealing': {'wage': 3000}, 'panels': [{'name': 'ﾄﾞｱ'}]}
    got = _D(rd)._paint_input_type(out)
    assert got.get('frame') and got.get('sealing'), got
    assert 'panels' not in got, got


def test_index_request_is_untouched():
    """「指数」の指定は畳まない（人の指定が優先）"""
    rd = {'paint': {'input_type': '指数'}, 'totals': {}}
    out = {'total': 50000, 'panels': [{'name': 'ﾄﾞｱ'}], 'material': 10000}
    got = _D(rd)._paint_input_type(out)
    assert got.get('input_type') == '指数' and got.get('panels') and got.get('material') == 10000, got


def test_auto_rule_is_unchanged():
    """自動で実額を選ぶ規則は変えない: 一式だけなら実額、材料代が別に出ていれば実額にしない"""
    d1 = _D({'paint': {}, 'totals': {}})
    got1 = d1._paint_input_type({'total': 99080})
    assert got1.get('input_type') == '実額', got1
    d2 = _D({'paint': {}, 'totals': {}})
    got2 = d2._paint_input_type({'total': 85520, 'material': 19226})
    assert 'input_type' not in got2, got2


def main() -> int:
    fails = 0
    for name, fn in sorted(globals().items()):
        if name.startswith('test_') and callable(fn):
            try:
                fn()
                print('ok  ', name)
            except AssertionError as e:
                fails += 1
                print('FAIL', name, e)
    print('paint_force_actual tests:', 'all ok' if not fails else f'{fails} failed')
    return 1 if fails else 0


if __name__ == '__main__':
    sys.exit(main())
