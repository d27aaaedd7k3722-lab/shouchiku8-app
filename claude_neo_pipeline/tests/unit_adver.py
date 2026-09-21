# -*- coding: utf-8 -*-
"""ADDATA の形式版（COM\\AdVer）の検査（2026-09-21。本体 AxDBAcsCarDat.dll の逆アセンブルと ADDATA 3 版の実測で確定）

  本体は 11/13/83.DB を AdVer で配置を切り替えて読む:
    0410 以上 0430 未満 → 310 系（11.DB 72 / 13.DB 189 / 83.DB 201 バイト）… 生成器が列まで確かめた配置
    0430 以上           → 330 系（11.DB 89 / 13.DB 206 / 83.DB 218 バイト）
  0430 の ADDATA を今の読み方で読むと、11.DB は例外にならずに別の列を品番・価格として読んでしまう。
  だから確かめていない版は入口で止め、11.DB にも 13/83.DB と同じ長さ検査を入れる。

    cd files && PYTHONIOENCODING=utf-8 python claude_neo_pipeline/tests/unit_adver.py
"""
from __future__ import annotations

import os
import shutil
import sys
import tempfile

HERE = os.path.dirname(os.path.realpath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, ROOT); sys.path.insert(0, os.path.dirname(HERE))
from _addata_db_search import AddataSearchEngine, adver_layout_11, check_adver, read_adver  # noqa: E402

ok = True


def chk(cond, msg):
    global ok
    if not cond:
        ok = False
        print('  NG', msg)
    return cond


print('-- 本体と同じ寄せ方（SearchXXX11/13/83）--')
for n, want in ((300, 300), (310, 310), (319, 310), (320, 320), (330, 330), (400, 330),
                (410, 310), (429, 310), (430, 330), (439, 330)):
    chk(adver_layout_11(n) == want, f'AdVer {n:04d} → {adver_layout_11(n)}（{want} のはず）')

tmp = tempfile.mkdtemp(prefix='unit_adver_')
try:
    os.makedirs(os.path.join(tmp, 'COM'))

    def put(v):
        with open(os.path.join(tmp, 'COM', 'AdVer'), 'wb') as f:
            f.write(v)

    print('-- 確かめた版（0410）は通す --')
    put(b'0410')
    chk(read_adver(tmp) == 410, f'AdVer を読めない（{read_adver(tmp)}）')
    try:
        chk(check_adver(tmp) == 410, 'check_adver が 410 を返さない')
    except ValueError as e:
        chk(False, f'0410 で止めた: {e}')

    print('-- 確かめていない版（0430）は止める --')
    put(b'0430')
    try:
        check_adver(tmp)
        chk(False, '0430 を止めていない（11.DB が 89 バイトになり黙って壊れる）')
    except ValueError as e:
        chk('0430' in str(e), f'エラーに版が出ていない: {e}')
    try:
        AddataSearchEngine(tmp)
        chk(False, 'AddataSearchEngine が 0430 の ADDATA を受け入れた')
    except ValueError:
        pass

    print('-- AdVer が無い ADDATA は止めない（各表の長さ検査に任せる）--')
    os.remove(os.path.join(tmp, 'COM', 'AdVer'))
    chk(read_adver(tmp) is None, 'ファイルが無いのに値を返した')
    try:
        chk(check_adver(tmp) is None, 'ファイルが無いのに値を返した')
    except ValueError as e:
        chk(False, f'AdVer が無いだけで止めた: {e}')

    print('-- 11.DB のレコード長が合わなければ止める（89 バイト = AdVer 0430 の形）--')
    put(b'0410')
    car = 'Z99'
    d = os.path.join(tmp, car[0], car)
    os.makedirs(d)
    with open(os.path.join(d, f'{car}01.DB'), 'wb') as f:
        f.write(b'\x33\x00' + b'\x00' * 100)
    with open(os.path.join(d, f'{car}11.DB'), 'wb') as f:
        f.write(b'\x00' * 400 + b'\x01' * 89 * 3)
    eng = AddataSearchEngine(tmp)
    try:
        eng.load_11db(car)
        chk(False, '89 バイトのレコードを黙って読んだ')
    except ValueError as e:
        chk('11.DB' in str(e), f'エラーに表の名前が出ていない: {e}')
    with open(os.path.join(d, f'{car}11.DB'), 'wb') as f:
        f.write(b'\x00' * 400 + b'\x00' * 72 * 3)
    try:
        eng2 = AddataSearchEngine(tmp)
        eng2.load_11db(car)
    except ValueError as e:
        chk(False, f'正しい長さ（72 バイト）で止めた: {e}')
finally:
    shutil.rmtree(tmp, ignore_errors=True)

print('-- この PC の ADDATA --')
try:
    from addata_vehicle_resolver import find_addata_root
    r = find_addata_root()
    n = check_adver(r)
    print(f'   {r}: AdVer = {n if n is None else f"{n:04d}"}（配置 {adver_layout_11(n) if n else "-"}）')
except ValueError as e:
    chk(False, f'この PC の ADDATA が確かめていない版: {e}')
except Exception as e:  # ADDATA が無い PC では飛ばす
    print(f'   ADDATA が見つからないので飛ばす（{type(e).__name__}）')

print('unit_adver: all ok' if ok else 'unit_adver: NG')
sys.exit(0 if ok else 1)
