# -*- coding: utf-8 -*-
"""verify/ の道具が共通で使うもの（パスの解決・make_neo の呼び出し）。パスはスクリプトに書かない（skill_env が PC ごとに解決する）。

作業データ（顧客名・見積の画像・NEO）はすべてリポジトリの外 `<NEO_CHECK_ROOT>/` に置く:
    _verify/survey.json            … 案件フォルダの走査結果（survey_cases.py）
    _verify/noncogni_candidates.json … コグニ以外の書式の候補（noncogni_candidates.py）
    _nc/cases.json, _nc/ncNN/      … 検証する案件（コグニ以外）。reading.json・estimate.json・auto.neo・agent_report.md
    _batch/<名前>/                 … コグニ印刷の自動読み取りの案件（ocr_anchor）
    _prints/<名前>.pdf             … コグニで刷った PDF（案件フォルダは作り直すので外に置く）
"""
from __future__ import annotations

import io
import json
import os
import re
import subprocess
import sys

VERIFY = os.path.dirname(os.path.realpath(__file__))
SCRIPTS = os.path.dirname(VERIFY)
if SCRIPTS not in sys.path:
    sys.path.insert(0, SCRIPTS)
import skill_env  # noqa: E402

ENV = skill_env.apply()
REPO = ENV.get('REPO_ROOT') or os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(SCRIPTS))))
NEO_CHECK = ENV.get('NEO_CHECK_ROOT') or os.path.expandvars(r'%USERPROFILE%\Documents\NEO_check')
CASE_ROOT = os.environ.get('CASE_ROOT') or 'Z:/'   # 元案件の置き場（共有ドライブ。読むだけ）


def work_dir(base: str) -> str:
    """`_nc` / `_batch` のような作業フォルダの名前を NEO_check の下のパスに"""
    return base if os.path.isabs(base) else os.path.join(NEO_CHECK, base)


def load_json(p: str, default=None):
    try:
        return json.load(io.open(p, encoding='utf-8-sig'))
    except (OSError, ValueError):
        return default


def save_json(p: str, obj) -> None:
    os.makedirs(os.path.dirname(p), exist_ok=True)
    tmp = p + '.tmp'
    json.dump(obj, io.open(tmp, 'w', encoding='utf-8'), ensure_ascii=False, indent=1)
    os.replace(tmp, p)


def case_list(base: str) -> tuple[list[str], list[str]]:
    """作業フォルダの案件を (reading.json のある案件, 写し待ちの案件) で返す（名前順）。
    写し待ち = cases.json に載っている・フォルダがあるのに reading.json が無い案件（cases.json の "skip" に理由を書いた案件は除く）。
    写し待ちを黙って飛ばすと「全部合格」に見えるので、道具はこれを失敗として数える（Codex 指摘）"""
    d = work_dir(base)
    if not os.path.isdir(d):
        return [], []
    listed = load_json(os.path.join(d, 'cases.json'), []) or []
    skip = {x.get('name') for x in listed if isinstance(x, dict) and x.get('skip')}
    names = {x.get('name') for x in listed if isinstance(x, dict) and x.get('name')}
    names |= {n for n in os.listdir(d) if os.path.isdir(os.path.join(d, n)) and not n.startswith(('_', '.'))}
    names -= skip
    ready = sorted(n for n in names if os.path.isfile(os.path.join(d, n, 'reading.json')))
    pending = sorted(n for n in names if n not in ready)
    return ready, pending


def case_names(base: str) -> list[str]:
    """作業フォルダの中で reading.json のある案件（名前順）"""
    return case_list(base)[0]


def run_make_neo(case_dir: str, allow_neo_total: bool = True, skip_check: bool = False) -> tuple[str, dict]:
    """納品しない・工場プロファイルに書かない・今のコードで下書きし直す make_neo。戻り値 (出力全文, 要約)。
    allow_neo_total: 下書きが書いた 3 点セット（工場の丸めの説明）を人が認めた扱いで通す（検証の作り直しでは既定で付ける）
    skip_check: 紙上検算（reading_check）の FAIL を承知で進む（既定は止める = 写しの崩れも不合格として数える）"""
    cmd = [sys.executable, os.path.join(SCRIPTS, 'make_neo.py'), case_dir, '--name', 'auto', '--no-profile', '--force-draft']
    if skip_check:
        cmd.append('--skip-check')
    if allow_neo_total:
        cmd.append('--allow-neo-total')
    env = dict(os.environ, PYTHONIOENCODING='utf-8')
    p = subprocess.run(cmd, capture_output=True, text=True, encoding='utf-8', errors='replace', env=env, cwd=REPO)
    out = (p.stdout or '') + (p.stderr or '')
    io.open(os.path.join(case_dir, 'remake.log'), 'w', encoding='utf-8').write(out)
    ng = re.findall(r'不合格[:：].*', out)
    tm = re.search(r'見積書合計との一致[:：]\s*(\S+)', out)
    pp = re.search(r'印刷の予測との突き合わせ == 差 (\d+) 件', out)
    summary = {'ok': ('合格:' in out and not ng), 'total': tm.group(1) if tm else '', 'pred_diff': pp.group(1) if pp else '-',
               'ng': ng[0][:160] if ng else '', 'rc': p.returncode}
    return out, summary
