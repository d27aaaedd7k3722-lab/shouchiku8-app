# -*- coding: utf-8 -*-
"""生成 NEO の構造が実機保存版と同じか（テーブル集合・列・件数・SQLite の整合性）。
明細の金額が合っていても、表が欠けているとコグニの画面で行が消える
    cd files && PYTHONIOENCODING=utf-8 python claude_neo_pipeline/tests/unit_struct.py
"""
from __future__ import annotations

import json
import os
import sqlite3
import sys
import tempfile

HERE = os.path.dirname(os.path.realpath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
import neo_container as _nc  # noqa: E402
from estimate_to_neo import NeoBuilder  # noqa: E402

E = os.path.join(os.path.expanduser('~'), 'Documents', 'NEO_check', '_eva_exp')
SKIP_COUNT = {'DamageBlock', 'Expense', 'PaintingOther', 'Fixer'}  # 雛形由来の固定枠（件数は案件で変わらない）


def tables(neo: bytes) -> dict:
    ck = _nc.find_real_cks(neo)
    dec = _nc.decompress_neo(neo, ck)
    _m, entries = _nc.parse_entries(neo, ck[0])
    files = _nc.extract_files(dec, entries)
    out = {}
    for fname in ('AnSvEm0001.sld', 'AnSvIf0001.sld'):
        if fname not in files:
            continue
        t = tempfile.NamedTemporaryFile(delete=False, suffix='.sld')
        t.write(files[fname])
        t.close()
        con = sqlite3.connect(t.name)
        info = {}
        for (n,) in con.execute("SELECT name FROM sqlite_master WHERE type='table' ORDER BY name"):
            cols = tuple(c[1] for c in con.execute(f'PRAGMA table_info({n})'))
            info[n] = (cols, con.execute(f'SELECT COUNT(*) FROM {n}').fetchone()[0])
        assert con.execute('PRAGMA integrity_check').fetchone()[0] == 'ok', f'{fname} が壊れている'
        con.close()
        os.unlink(t.name)
        out[fname] = info
    return out


def test_structure_matches_cogni():
    tag = 'K1'
    est_p = os.path.join(E, f'nbox_{tag}_estimate.json')
    cog_p = os.path.join(E, f'cogni_{tag}.neo')
    if not os.path.isdir(E):
        print('   （NEO_check/_eva_exp が無い PC なのでスキップ）')
        return
    assert os.path.exists(est_p) and os.path.exists(cog_p), \
        f'比較の基準が無い: {est_p if not os.path.exists(est_p) else cog_p}（ファイル名が変わっていないか確かめる）'
    est = json.load(open(est_p, encoding='utf-8'))
    neo, _ = NeoBuilder().build(est, est['vehicle'], hints=est.get('hints'), labor_rate=est.get('labor_rate') or 8000,
                                est_date=est.get('est_date') or '20260908', insurance={})
    gen, cog = tables(neo), tables(open(cog_p, 'rb').read())
    assert set(gen) == set(cog), f'同梱 DB が違う: {sorted(set(gen) ^ set(cog))}'
    for fname in gen:
        assert set(gen[fname]) == set(cog[fname]), f'{fname} のテーブルが違う: {sorted(set(gen[fname]) ^ set(cog[fname]))}'
        for t in gen[fname]:
            gcols, gcnt = gen[fname][t]
            ccols, ccnt = cog[fname][t]
            assert gcols == ccols, f'{fname}.{t} の列が違う'
            if t not in SKIP_COUNT:
                assert gcnt == ccnt, f'{fname}.{t} の件数が違う: 生成 {gcnt} / 実機 {ccnt}'


if __name__ == '__main__':
    fails = 0
    for name, fn in sorted(globals().items()):
        if name.startswith('test_') and callable(fn):
            try:
                fn()
                print('ok  ', name)
            except AssertionError as e:
                fails += 1
                print('FAIL', name, e)
    print('unit_struct:', 'all ok' if not fails else f'{fails} failed')
    sys.exit(1 if fails else 0)
