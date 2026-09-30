# -*- coding: utf-8 -*-
"""人が作った実機 NEO の山で、AnSMB.txt の欄が ERParts の列と合っているかを数える（開発用・読むだけ）。
NEO_FILE_SPEC_COMPLETE.md §5 の表の根拠（2026-09-30: 374 本 16,533 行ですべて一致）を、あとから同じ手順で確かめ直すための道具。
AnSMB の行と ERParts の行は **行番号（LineNo）で**対応させる（並び順で対応させると、行の入れ替えがある NEO でずれる）。

    python claude_neo_pipeline/tests/ansmb_corpus.py [--root <NEO の山>] [--limit N]

NEO の山の場所は --root か環境変数 NEO_CORPUS_ROOT（既定 Z:\\ドキュメント）。ファイル名に claude を含む NEO（生成器の出力）は除く。
書き出すのは件数だけ（顧客名・車名・品番は出さない）。NEO は読むだけで、書き換えない。
"""
from __future__ import annotations

import argparse
import collections
import os
import re
import sqlite3
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
import neo_container as nc  # noqa: E402


def digit(v) -> str:
    try:
        n = int(v)
    except (TypeError, ValueError):
        return ' '
    return ' ' if n < 0 else str(min(n, 9))


def scan(root: str, limit: int) -> collections.Counter:
    st = collections.Counter()
    n = 0
    for dp, _dn, fns in os.walk(root):
        for fn in fns:
            if not fn.lower().endswith('.neo') or 'claude' in fn.lower():
                continue
            if limit and n >= limit:
                return st
            try:
                neo = open(os.path.join(dp, fn), 'rb').read()
                ck = nc.find_real_cks(neo)
                raw = nc.decompress_neo(neo, ck)
                _m, en = nc.parse_entries(neo, ck[0])
                files = nc.extract_files(raw, en)
            except Exception:
                st['読めない NEO'] += 1
                continue
            n += 1
            smb = {}
            for l in files.get('AnSMB.txt', b'').split(b'\r\n'):
                if not l:
                    continue
                if len(l) != 142 or not l[:8].isdigit():
                    st['142 バイトでない行'] += 1
                    continue
                smb[int(l[:8])] = l
            q = os.path.join(tempfile.gettempdir(), 'ansmb_corpus.db')
            open(q, 'wb').write(files['AnSvEm0001.sld'])
            c = sqlite3.connect(q)
            c.row_factory = sqlite3.Row
            try:
                for r in c.execute('select LineNo, PartsCodeSub, OrderFlag, ReserveFlag, RWLinkFlag from ERParts'):
                    l = smb.get(r['LineNo'])
                    if l is None:
                        st['AnSMB に無い明細行'] += 1
                        continue
                    st['行'] += 1
                    of = r['OrderFlag']
                    checks = {
                        '[12] PartsCodeSub': chr(l[12]) == digit(r['PartsCodeSub']),
                        '[100] OrderFlag': chr(l[100]) == (' ' if of in (None, '') else str(of)[:1]),
                        '[102] ReserveFlag': chr(l[102]) == digit(r['ReserveFlag'] or 0),
                        '[103] RWLinkFlag': chr(l[103]) == digit(r['RWLinkFlag'] or 0),
                        '[104] CutWorkFlag（英字の有無）': chr(l[104]) == ('1' if re.search(rb'[A-Za-z]', l[105:119]) else '0'),
                        '[116:119] 空白': l[116:119] == b'   ',
                    }
                    for k, ok in checks.items():
                        st[(k, ok)] += 1
                    st[('[119:127] PartsFigNo 入り', bool(l[119:127].strip()))] += 1
                    st[('[127:133] F99999', l[127:133] == b'F99999')] += 1
            finally:
                c.close()
    st['NEO'] = n
    return st


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument('--root', default=os.environ.get('NEO_CORPUS_ROOT') or r'Z:\ドキュメント')
    ap.add_argument('--limit', type=int, default=0)
    a = ap.parse_args()
    if not os.path.isdir(a.root):
        print(f'** NEO の山が無い: {a.root}（--root で指定）。何も確かめていない **')
        return 2
    st = scan(a.root, a.limit)
    print(f"NEO {st['NEO']} 本・行 {st['行']}（読めない NEO {st['読めない NEO']}・142 バイトでない行 {st['142 バイトでない行']}・AnSMB に無い明細行 {st['AnSMB に無い明細行']}）")
    ng = 0
    for k in ('[12] PartsCodeSub', '[100] OrderFlag', '[102] ReserveFlag', '[103] RWLinkFlag', '[104] CutWorkFlag（英字の有無）', '[116:119] 空白'):
        ok, bad = st[(k, True)], st[(k, False)]
        ng += bad
        print(f'  {k}: 一致 {ok} / 不一致 {bad}')
    print(f"  （参考）[119:127] PartsFigNo が入った行 {st[('[119:127] PartsFigNo 入り', True)]}・[127:133] が F99999 でない行 {st[('[127:133] F99999', False)]}")
    print('ansmb_corpus: ' + ('すべて一致' if ng == 0 and st['行'] else f'不一致 {ng} 行' if st['行'] else '行が 0（何も確かめていない）'))
    return 0 if (ng == 0 and st['行']) else 1


if __name__ == '__main__':
    sys.stdout.reconfigure(encoding='utf-8')
    sys.exit(main())
