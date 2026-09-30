# -*- coding: utf-8 -*-
"""AnSMB.txt の 1 行（142 バイト＋CRLF）を 21 欄ごとに確かめる。
実機比較（audit_cogni_files.py --ansmb）は空白・0 の欄が多い行で一致を見るので、
ここでは全部の欄に見分けの付く値を入れ、欄の位置・幅・境界の扱いを 1 つずつ固定する（2026-09-30）。
欄の並びと位置の根拠: 人が作った実機 NEO 374 本 16,533 行の AnSMB（NEO_FILE_SPEC_COMPLETE.md §5）。
    cd files && PYTHONIOENCODING=utf-8 python claude_neo_pipeline/tests/unit_ansmb.py
"""
from __future__ import annotations

import os
import sys

HERE = os.path.dirname(os.path.realpath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
from estimate_to_neo import NeoBuilder  # noqa: E402

FAILS: list[str] = []


def check(label: str, got, want) -> None:
    if got != want:
        FAILS.append(f'{label}: {got!r} != {want!r}')


def row(**kw) -> dict:
    """架空の明細 1 行（顧客情報なし）。既定は生成器が普通に書く値"""
    r = {'LineNo': 10, 'PartsCode': '0010', 'PartsCodeSub': -1, 'DisposalCode': 1,
         'PartsName': '  Frﾊﾞﾝﾊﾟﾌｪｲｽ', 'PartsNameStandard': ' Fﾊﾞﾝﾊﾟﾌｪｲｽ', 'PartsNo': '52119-ABC01',
         'PartsNoStandard': '52119-ABC00', 'PartsCount': 1, 'OrderFlag': '', 'ReserveFlag': 0, 'RWLinkFlag': 0}
    r.update(kw)
    return r


def line(r: dict) -> bytes:
    out = NeoBuilder.build_ansmb([r])
    check('行末は CRLF', out[-2:], b'\r\n')
    check('本体は 142 バイト', len(out) - 2, 142)
    return out[:-2]


def sl(b: bytes, name: str) -> bytes:
    for n, pos, width in NeoBuilder.ANSMB_FIELDS:
        if n == name:
            return b[pos:pos + width]
    raise KeyError(name)


def main() -> int:
    # 0. 欄の表そのもの: 21 欄・隙間も重なりも無く 0〜142 を埋める
    f = NeoBuilder.ANSMB_FIELDS
    check('欄の数', len(f), 21)
    pos = 0
    for name, p, w in f:
        check(f'{name} の開始位置', p, pos)
        pos = p + w
    check('欄の合計幅', pos, 142)

    # 1. 全欄に見分けの付く値
    b = line(row(LineNo=1230, PartsCode='3810', PartsCodeSub=4, DisposalCode=2, PartsName='ABCDEFGHIJKLMNOPQRSTUVWX',
                 PartsNameStandard='abcdefghijklmnopqrstuvwx', PartsNo='PN-000000000000001', PartsNoStandard='PS-000000000000002',
                 PartsCount=7, OrderFlag='9', ReserveFlag=1, RWLinkFlag=1, _smb_tail='1K     3D  ',
                 _smb_fig_no='5201', _smb_name_code='52119A', _smb_name_code_std='52119A'))
    want = {'LineNo': b'00001230', 'PartsCode': b'3810', 'PartsCodeSub': b'4', 'DisposalCode': b'2',
            'PartsName': b'ABCDEFGHIJKLMNOPQRSTUVWX', 'PartsNameStandard': b'abcdefghijklmnopqrstuvwx',
            'PartsNo': b'PN-000000000000001', 'PartsNoStandard': b'PS-000000000000002', 'PartsCount': b'07',
            'OrderFlag': b'9', 'RecycleFlag': b'0', 'ReserveFlag': b'1', 'RWLinkFlag': b'1',
            'CutWorkFlag': b'1', 'CutWorkL': b'1', 'CutWorkLDisposal': b'K     ', 'CutWorkR': b'3', 'CutWorkRDisposal': b'D     ',
            'PartsFigNo': b'5201    ', 'PartsNameCode': b'52119A', 'PartsNameCodeStandard': b'52119A   '}
    for name, v in want.items():
        check(f'全欄: {name}', sl(b, name), v)

    # 2〜4. PartsCodeSub: -1 は空白、0〜9 はその数字、10 以上は 9
    for sub, w in ((-1, b' '), (0, b'0'), (1, b'1'), (9, b'9'), (10, b'9'), (37, b'9')):
        check(f'PartsCodeSub={sub}', sl(line(row(PartsCodeSub=sub)), 'PartsCodeSub'), w)

    # 4b. ReserveFlag は値そのまま（0 / 1 / 2）
    for v, w in ((0, b'0'), (1, b'1'), (2, b'2')):
        check(f'ReserveFlag={v}', sl(line(row(ReserveFlag=v)), 'ReserveFlag'), w)

    # 5. RWLinkFlag は 103 桁
    check('RWLinkFlag=1', line(row(RWLinkFlag=1))[103:104], b'1')
    check('RWLinkFlag=0', line(row(RWLinkFlag=0))[103:104], b'0')

    # 6. 部分切断作業: 左だけ・右だけ・左右とも・欄が空
    for tail, wf, wl, wld, wr, wrd in (('1K         ', b'1', b'1', b'K     ', b' ', b'      '),
                                        ('       1K  ', b'1', b' ', b'      ', b'1', b'K     '),
                                        ('1K     1K  ', b'1', b'1', b'K     ', b'1', b'K     '),
                                        ('0      0   ', b'0', b'0', b'      ', b'0', b'      '),
                                        ('', b'0', b' ', b'      ', b' ', b'      ')):
        b = line(row(_smb_tail=tail))
        check(f'CutWork {tail!r} フラグ', sl(b, 'CutWorkFlag'), wf)
        check(f'CutWork {tail!r} 左', sl(b, 'CutWorkL') + sl(b, 'CutWorkLDisposal'), wl + wld)
        check(f'CutWork {tail!r} 右', sl(b, 'CutWorkR') + sl(b, 'CutWorkRDisposal'), wr + wrd)

    # 7. 既定: 部品図番・標準名称コードは空白、名称コードは F99999、116〜118 桁は空白
    b = line(row(_smb_tail='1K     1K  '))
    check('既定 PartsFigNo', sl(b, 'PartsFigNo'), b' ' * 8)
    check('既定 PartsNameCode', sl(b, 'PartsNameCode'), b'F99999')
    check('既定 PartsNameCodeStandard', sl(b, 'PartsNameCodeStandard'), b' ' * 9)
    check('116〜118 桁', b[116:119], b'   ')

    # 8. 修理方法の無い手入力行・部品コードの無い行は空白
    b = line(row(PartsCode='', DisposalCode=-1))
    check('部品コード無し', sl(b, 'PartsCode'), b'    ')
    check('修理方法無し', sl(b, 'DisposalCode'), b' ')

    # 9. 全角（CP932）を含んでも欄の境界を越えない
    b = line(row(PartsName='左フロントバンパーフェイス長い名前', PartsNameStandard='ﾌﾛﾝﾄﾊﾞﾝﾊﾟ', PartsNo='リサイクル部品番号超過'))
    check('全角の名称は 24 バイトで切れる', len(sl(b, 'PartsName')), 24)
    _std = 'ﾌﾛﾝﾄﾊﾞﾝﾊﾟ'.encode('cp932')
    check('全角でも標準名称の先頭は 38 桁目', sl(b, 'PartsNameStandard')[:len(_std)], _std)
    check('全角でも数量は 98 桁目', sl(b, 'PartsCount'), b'01')

    # 10. 複数行でも各行 142 バイト＋CRLF
    out = NeoBuilder.build_ansmb([row(LineNo=10), row(LineNo=20, PartsName='ﾘｱﾊﾞﾝﾊﾟ'), row(LineNo=30, _smb_tail='1K     1K  ')])
    ls = out.split(b'\r\n')
    check('複数行の行数', len(ls), 4)
    check('複数行の最後は空', ls[-1], b'')
    for i, l in enumerate(ls[:-1]):
        check(f'{i + 1} 行目の幅', len(l), 142)
        check(f'{i + 1} 行目の行番号', l[:8], f'{(i + 1) * 10:08d}'.encode())

    # 11. 数量: 0 以下は 01
    check('数量 0', sl(line(row(PartsCount=0)), 'PartsCount'), b'01')
    check('数量 -1', sl(line(row(PartsCount=-1)), 'PartsCount'), b'01')

    for m in FAILS:
        print('NG', m)
    print(f'unit_ansmb: {"すべて合格" if not FAILS else f"不合格 {len(FAILS)} 件"}')
    return 1 if FAILS else 0


if __name__ == '__main__':
    sys.exit(main())
