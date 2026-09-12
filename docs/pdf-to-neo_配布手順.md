# pdf-to-neo を他の PC で使えるようにする（配布する側の手順）

工場見積 PDF → コグニセブン NEO を、Claude を入れた別の PC で同じようにできるようにするための手順。
渡す側（亮平さん）が何を渡し、受け取る側が何をするかをまとめる。最終更新 2026-09-10。

## 1. 渡すもの（これ 1 つだけ）

配布 zip `pdf-to-neo_bundle_YYYYMMDD.zip`（約 1.5MB。ファイル数は make_bundle の出力を正とする）。作り方:

**渡すのは必ず作り直した当日の zip**。古い zip（2026-09-12 より前）は工場プロファイル（取引先名）が入っていたので渡さない・残さない（make_bundle は今は同梱しない）。

```
cd files
python .claude\skills\pdf-to-neo\scripts\make_bundle.py
```

**この zip に入っているもの**

| 中身 | 役割 |
|---|---|
| `claude_neo_pipeline/` | NEO 生成器の本体（明細・塗装・骨格・費用・合計・AnSMB を書く） |
| `.claude/skills/pdf-to-neo/` | Claude 用のスキル（手順書・判断規則・書式カタログ・チェックリスト・スクリプト一式） |
| `NEO_FILE_SPEC_COMPLETE.md` / `ADDATA_REVERSE_LOOKUP_SPEC.md` | NEO と ADDATA の仕様（判断の根拠） |
| `BUNDLE_README.md` | 受け取る側の導入手順（zip の中に入っている） |
| 雛形 NEO 1 本・部品名辞書 | 生成に必要な参照データ（工場プロファイルは取引先名を含むので入れない。各 PC の `NEO_CHECK_ROOT/_profiles/` に作られる） |

**入っていないもの（入れてはいけないもの）**

- `NEO_check/`（案件データ。顧客名・住所・車台番号を含む）
- 実案件の `*.neo`
- 実機検証用のフィクスチャ `_eva_exp/`（開発機だけで使う。受け取る側には不要）

zip を作るときに「この PC 固有の絶対パス」と「制御文字」が混ざっていないかを自動で検査し、
1 つでもあれば zip を作らずに止まる。だから中身を手で点検する必要はない。

## 2. 受け取る側がやること（1 回だけ・10 分）

`BUNDLE_README.md` に同じことが書いてあるので、zip を渡せばそれで足りる。要点だけ:

1. zip を任意のフォルダに解凍（例 `C:\SHOUCHIKU8\files`。以後この `files` が作業フォルダ）
2. Python 3.11 以上を入れる（追加パッケージ不要。インストール時に「Add python.exe to PATH」にチェック）
3. Claude Code を入れる
4. `files` の中で次を実行（ADDATA とコグニを自動検出し、設定を保存し、スキルを個人領域に登録する）
   ```
   python .claude\skills\pdf-to-neo\scripts\env_check.py --save --install-skill
   ```
5. 受け入れ確認（10 秒）
   ```
   python .claude\skills\pdf-to-neo\scripts\env_check.py --self-test
   ```
   `自己診断: すべて合格` と `結果: 使える` が出れば、その PC が作る NEO は開発機と同じ結果になる
6. `files` で Claude Code を起動し、「この PDF を NEO にして」と頼む

### その PC に要るもの

- **コグニセブンのデータ `Addata`**（必須）。これが無いと NEO は作れない
- コグニセブン本体（`AudaMenu.exe`）。作った NEO を実機で開いて確認するときだけ必要
- `hh.exe`（Windows 標準。塗装指数の CHM を開くのに使う）

### 導入時に必ず見る 2 行

- `ADDATA データ版`（例 2026/08）。**社内で版が違うと標準品番と標準指数が変わる**ので揃える
- `ADDATA 他の候補`。古い `C:\Addata` を残したまま本番データを別の場所に置いている PC で出る。
  出たら `--addata "<正しいパス>" --save` で固定する

## 3. 渡した後の更新

スキルや生成器を直したら zip を作り直して配り直す。受け取る側は上書き解凍して手順 4〜5 をやり直すだけ。
**設定（`%USERPROFILE%\.claude\pdf-to-neo.local.json`）と案件データ（`NEO_check`）は zip に含まれないので消えない。**

## 4. git で配る場合（開発する人だけ）

生成器やスキルを直す人には zip ではなくリポジトリを渡す。その場合は
`.claude/skills/pdf-to-neo/scripts/tests/` のテストと `guess_labor_rate.py` も追跡対象に入っている必要がある
（`claude_neo_pipeline/tests/verify_all.sh` がこれらを必須にしているため、欠けると検証が落ちる）。

使う側は zip だけでよく、git は要らない。
