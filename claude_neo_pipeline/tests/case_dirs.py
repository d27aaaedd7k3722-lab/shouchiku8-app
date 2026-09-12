# -*- coding: utf-8 -*-
"""検証用の案件フォルダを **コード名**で引く（開発機専用）。

実案件のフォルダ名（損保名・顧客名を含む）はリポジトリに書かない。対応表は案件データと同じ場所
`<NEO_CHECK_ROOT>/_cases.json` に置く（git・配布 zip の外）:

    {
      "cases": {"C01": "<C-HR の案件フォルダ名>", "C02": "...", "NONE": "<N-ONE の案件フォルダ名>"},
      "regression": [{"code": "C01", "expect": "見積書合計との一致: OK"}, ...]
    }

対応表が無い PC（配布先など）では `case_dir()` は `<NEO_CHECK_ROOT>/<code>` を返すので、
その名前のフォルダを作れば同じテストが動く。
"""
from __future__ import annotations

import json
import os


def neo_check_root() -> str:
    """案件フォルダの根。環境変数 → %USERPROFILE%/.claude/pdf-to-neo.local.json → 既定（skill_env と同じ規則）"""
    root = os.environ.get('NEO_CHECK_ROOT') or ''
    if not root:
        cfg = os.path.join(os.path.expanduser('~'), '.claude', 'pdf-to-neo.local.json')
        try:
            with open(cfg, encoding='utf-8-sig') as fh:
                root = str((json.load(fh) or {}).get('NEO_CHECK_ROOT') or '')
        except (OSError, ValueError):
            root = ''
    return root or os.path.join(os.path.expanduser('~'), 'Documents', 'NEO_check')


def _table() -> dict:
    p = os.path.join(neo_check_root(), '_cases.json')
    try:
        with open(p, encoding='utf-8-sig') as fh:
            d = json.load(fh)
        return d if isinstance(d, dict) else {}
    except (OSError, ValueError):
        return {}


def case_dir(code: str) -> str:
    """コード名（C01 / NONE …）→ 案件フォルダの絶対パス。対応表に無ければ <root>/<code>"""
    name = str((_table().get('cases') or {}).get(code) or code)
    return os.path.join(neo_check_root(), name)


def regression_cases() -> list:
    """verify_all の案件回帰: [{'code', 'expect'}, …]。対応表が無ければ空（= 回帰は飛ばす）"""
    out = []
    for r in _table().get('regression') or []:
        if isinstance(r, dict) and r.get('code') and r.get('expect'):
            out.append({'code': str(r['code']), 'expect': str(r['expect'])})
    return out
