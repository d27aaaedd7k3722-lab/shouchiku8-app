# AGENTS.md — SHOUCHIKU8 NEO（このフォルダ）

Claude Code 以外のエージェント（Codex 等）向けの短い案内。**正本は `CLAUDE.md` → `README.md` → `.claude/skills/pdf-to-neo/HANDOFF.md`**。
この 3 つに書いてあることと食い違ったら、この文書ではなくそちらが正しい。

## 返答
- 常に日本語。

## このフォルダに何があるか
- **現役**: pdf-to-neo スキル（`.claude/skills/pdf-to-neo/`）＋ 生成器（`claude_neo_pipeline/`）。工場見積 PDF → コグニセブン互換 NEO
- **古いコピー（使わない）**: このフォルダ直下の `app.py` / `pdf_to_neo_pipeline.py`（Streamlit アプリ B）。現役の B は別リポジトリ `%USERPROFILE%\dev\neo-estimate`
- 仕様の正: `NEO_FILE_SPEC_COMPLETE.md`（NEO 書式・実機で確定した項目）、`ADDATA_REVERSE_LOOKUP_SPEC.md`（ADDATA 逆引き）

## 作業開始時
1. `CLAUDE.md`・`README.md`・`HANDOFF.md` を読む
2. `git status --short` / `git branch --show-current` / `git log --oneline -n 8`
3. 新しい PC なら `python .claude\skills\pdf-to-neo\scripts\env_check.py --save --install-skill` と `--self-test`

## 禁止事項
- 雛形 NEO・実機 NEO・ADDATA を上書きしない。実案件データ（NEO・見積 PDF・車検証）はリポジトリの外（`%USERPROFILE%\Documents\NEO_check`）に置く
- CP932 / バイナリ offset / SQLite スキーマを実データ検証なしに変えない
- 合計不一致・未検証のまま「完了」にしない
- 顧客情報・取引先名・API キーを文書やプロンプトに出さない

## 検証
- 新しい PC: `python .claude\skills\pdf-to-neo\scripts\env_check.py --self-test`
- 開発機（実機 fixture がある PC）: `bash claude_neo_pipeline/tests/verify_all.sh`
- コード変更は codex-loop（Claude 実装 → Codex レビュー）で

## 記録
- 日誌: `%USERPROFILE%\Documents\第2の脳\05_日誌\YYYY-MM-DD.md`
