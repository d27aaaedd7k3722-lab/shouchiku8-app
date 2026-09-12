# CLAUDE.md

## コミュニケーション規則

- 返答は常に日本語で行うこと。ファイルの修正提案や説明もすべて日本語で行うこと。

## このフォルダに何があるか（2026-09-12 現在）

**NEO を作るコードは2系統あり、置き場所が違う。触る前にどちらの話か確かめること。**

| 系統 | 場所 | 状態 |
|---|---|---|
| **A. pdf-to-neo スキル ＋ 生成器** | このフォルダの `.claude/skills/pdf-to-neo/` と `claude_neo_pipeline/` | **現役**。Claude が見積 PDF を読み、`make_neo.py` 1コマンドで NEO を作る。README.md が入口 |
| **B. Streamlit アプリ（NEO見積変換アプリ）** | **`%USERPROFILE%\dev\neo-estimate`**（別リポジトリ） | **現役**。本番 https://shouchiku-neo-estimate.streamlit.app/ を配信 |

### ⚠️ このフォルダの `app.py` / `pdf_to_neo_pipeline.py` は使わないこと

2026-08-11 で止まった **B の古いコピー**。そのあとに直した不具合が
1つも入っていない（ページ境界の重複行で総額が 42,460 円不足する、
保険欄が空になる、検証が素通りする など）。
**B を触るときは必ず `%USERPROFILE%\dev\neo-estimate` で作業すること。**

`起動.bat` は `dev\neo-estimate` があればそちらを起動する（2026-09-12 に変更。
元の内容は `起動.bat.bak`）。

## 環境の確認（新しい PC では最初に1回）

```
python .claude/skills/pdf-to-neo/scripts/env_check.py --save --install-skill
```

ADDATA・コグニ本体・雛形 NEO の場所を調べて
`%USERPROFILE%\.claude\pdf-to-neo.local.json` に保存し、
個人スキル領域にこのフォルダへのジャンクションを張る。
**この設定は Streamlit アプリ（B）も読む**ので、同じ PC で2つの実装が
別々の ADDATA を掴むことはない。

ADDATA のデータ版が違うと標準品番・標準指数が変わる ＝ 協定見積の中身が
変わる。開発機では版の違う ADDATA が3つ見つかった（2026/08 / 2025/01 / 2020/03）。別の PC では `env_check.py` の「ADDATA データ版」「ADDATA 他の候補」の表示を正として、
どれを使っているかは必ず確認すること。

## 主な文書

| 文書 | 中身 |
|---|---|
| `README.md` | プロジェクトの現況と使い方。**最初に読む** |
| `.claude/skills/pdf-to-neo/HANDOFF.md` | A の引き継ぎ文書（全体の地図・絶対ルール・実機で確かめた事実・未解決）。**README の次に読む** |
| `.claude/skills/pdf-to-neo/SKILL.md` | A の手順書（9段）。HANDOFF の次に読む |
| `NEO_FILE_SPEC_COMPLETE.md` | NEO ファイル仕様（実機で確定した項目） |
| `ADDATA_REVERSE_LOOKUP_SPEC.md` | 車検証 → ADDATA 逆引きの仕様 |
| `dev\neo-estimate\docs\引き継ぎ書.md` | B の引き継ぎ書 |

## 個人情報の扱い

実案件のデータ（`.neo` / 見積 PDF / 車検証）は**リポジトリの外**
（`%USERPROFILE%\Documents\NEO_check\`）に置く。`.gitignore` で
`*.neo` / `*.pdf` / `サンプル見積PDF/` は追跡外にしてある。
解析で実機の `.neo` を読むときは、**金額・コード・フラグの統計だけ**を扱い、
顧客情報は読まない・出さないこと。
