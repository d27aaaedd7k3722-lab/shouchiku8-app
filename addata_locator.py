#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""ADDATA フォルダ自動検索 (各PCのOneDrive内対応)

検索戦略:
  1. 環境変数 ADDATA_ROOT
  2. C:\\Addata (従来の標準位置)
  3. OneDriveパス候補配下を再帰検索 (深さ4まで)
     - %USERPROFILE%\\OneDrive*
     - C:\\Users\\<user>\\OneDrive - <org>
     - D:\\OneDrive*
  4. レジストリ HKCU\\Software\\Microsoft\\OneDrive
  5. ADDATA フォルダの判定: 子フォルダに 'A'-'Z' 1文字フォルダがあり、
     さらにその下に *01.DB / *11.DB / *12.DB が存在する。
"""
from __future__ import annotations
import os
import sys
import re
from typing import List, Optional

CACHE_KEY = "_ADDATA_LOCATOR_CACHE"
_cache: dict = {}


def _is_valid_addata(path: str, max_check: int = 3) -> bool:
    """path が ADDATA ルートとして妥当か検証（軽量チェック）"""
    if not path or not os.path.isdir(path):
        return False
    try:
        # A-Z 1文字フォルダがあるか（最大3つチェックで早期終了）
        letter_dirs = []
        for entry in os.listdir(path):
            if len(entry) == 1 and entry.isalpha() and os.path.isdir(os.path.join(path, entry)):
                letter_dirs.append(entry)
                if len(letter_dirs) >= 1:
                    break
        if not letter_dirs:
            return False
        # 配下に vehicle_code フォルダ があり、その中に *.DB があるか
        for ld in letter_dirs[:max_check]:
            ld_path = os.path.join(path, ld)
            try:
                for sub in os.listdir(ld_path):
                    sub_path = os.path.join(ld_path, sub)
                    if os.path.isdir(sub_path):
                        try:
                            files = os.listdir(sub_path)
                            if any(f.upper().endswith('.DB') for f in files):
                                return True
                        except OSError:
                            continue
            except OSError:
                continue
        return False
    except OSError:
        return False


def _candidate_onedrive_roots() -> List[str]:
    """OneDriveルート候補を列挙"""
    roots: List[str] = []

    # 1. 環境変数
    for env_key in ("OneDrive", "OneDriveCommercial", "OneDriveConsumer"):
        v = os.environ.get(env_key)
        if v and os.path.isdir(v):
            roots.append(v)

    # 2. ユーザーホーム配下の OneDrive*
    home = os.environ.get("USERPROFILE") or os.path.expanduser("~")
    if home and os.path.isdir(home):
        try:
            for entry in os.listdir(home):
                if entry.startswith("OneDrive"):
                    p = os.path.join(home, entry)
                    if os.path.isdir(p):
                        roots.append(p)
        except OSError:
            pass

    # 3. ドライブ直下の OneDrive*
    for drive in ("C:", "D:", "E:"):
        try:
            if not os.path.isdir(drive + "\\"):
                continue
            for entry in os.listdir(drive + "\\"):
                if entry.startswith("OneDrive"):
                    p = os.path.join(drive + "\\", entry)
                    if os.path.isdir(p):
                        roots.append(p)
        except OSError:
            continue

    # 重複除去・存在確認
    seen = set()
    out = []
    for r in roots:
        rn = os.path.normpath(r)
        if rn not in seen and os.path.isdir(rn):
            seen.add(rn)
            out.append(rn)
    return out


def _walk_for_addata(root: str, max_depth: int = 5,
                    max_dirs: int = 5000) -> Optional[str]:
    """root から再帰検索して 'Addata' フォルダかつ妥当判定で見つける。"""
    if not os.path.isdir(root):
        return None
    visited = 0
    for cur, dirs, _files in os.walk(root):
        visited += 1
        if visited > max_dirs:
            return None
        # 深さ判定
        rel = os.path.relpath(cur, root)
        depth = 0 if rel == "." else rel.count(os.sep) + 1
        if depth > max_depth:
            dirs[:] = []
            continue
        # 大文字小文字を問わず "Addata" マッチ
        for d in dirs:
            if d.lower() == "addata":
                cand = os.path.join(cur, d)
                if _is_valid_addata(cand):
                    return cand
        # 不要な深掘り抑制（OneDrive にはユーザーフォルダが多い）
        # node_modules / .git / __pycache__ / cache / temp 等を除外
        dirs[:] = [d for d in dirs
                   if not d.startswith(".")
                   and d.lower() not in ("node_modules", "__pycache__",
                                          "cache", "temp", "tmp", "logs",
                                          "videos", "music", "ピクチャ",
                                          "pictures")]
    return None


def find_addata(force_refresh: bool = False) -> Optional[str]:
    """ADDATA ルートを自動検索して返す。見つからなければ None。
    結果はモジュールキャッシュ。force_refresh=True で再検索。"""
    if not force_refresh and CACHE_KEY in _cache:
        return _cache[CACHE_KEY]

    # 1. 環境変数
    env_root = os.environ.get("ADDATA_ROOT")
    if env_root and _is_valid_addata(env_root):
        _cache[CACHE_KEY] = env_root
        return env_root

    # 2. 標準位置
    for std in (r"C:\Addata", r"D:\Addata"):
        if _is_valid_addata(std):
            _cache[CACHE_KEY] = std
            return std

    # 3. OneDrive配下を並列検索（複数候補を同時走査で最大3倍速）
    try:
        from concurrent.futures import ThreadPoolExecutor, as_completed
        roots = _candidate_onedrive_roots()
        if roots:
            with ThreadPoolExecutor(max_workers=min(len(roots), 4)) as ex:
                futures = {ex.submit(_walk_for_addata, r, 5, 8000): r for r in roots}
                for fu in as_completed(futures):
                    try:
                        found = fu.result()
                    except Exception:
                        found = None
                    if found:
                        # 残りのfutureはcancel
                        for f in futures:
                            if f is not fu:
                                f.cancel()
                        _cache[CACHE_KEY] = found
                        return found
    except Exception:
        # フォールバック: 直列
        for od in _candidate_onedrive_roots():
            found = _walk_for_addata(od, max_depth=5, max_dirs=8000)
            if found:
                _cache[CACHE_KEY] = found
                return found

    _cache[CACHE_KEY] = None
    return None


def list_candidate_paths() -> List[str]:
    """検索候補を返す（デバッグ用）"""
    out = []
    for env_key in ("ADDATA_ROOT",):
        v = os.environ.get(env_key)
        if v:
            out.append(f"env:{env_key}={v}")
    for std in (r"C:\Addata", r"D:\Addata"):
        out.append(f"std:{std} (exists={os.path.isdir(std)})")
    for od in _candidate_onedrive_roots():
        out.append(f"onedrive:{od}")
    return out


if __name__ == "__main__":
    sys.stdout.reconfigure(encoding="utf-8")
    print("候補:")
    for p in list_candidate_paths():
        print(f"  {p}")
    print()
    found = find_addata()
    print(f"検出結果: {found!r}")
    if found:
        print(f"_is_valid_addata: {_is_valid_addata(found)}")
