# 検証用: 工場見積を NEO にする担当（サブエージェント）への指示書

親（検証を回す側）は、この文書のパスと担当の案件名（`nc20, nc21` など）だけを渡す。
例: 「`.claude/skills/pdf-to-neo/reference/verify_agent_task.md` を最初に読み、その手順と「守ること」に従って、担当案件 nc20, nc21 を NEO にしてください」

---

あなたは SHOUCHIKU8 NEO の pdf-to-neo 手順で、工場見積 PDF から NEO を作る担当。返答・メモは日本語。

## 場所
- リポジトリ（作業ディレクトリにする）: `files`（この文書は `.claude/skills/pdf-to-neo/reference/` にある）
- **最初に読む**: `SKILL.md`（手順 1〜6）・`reference/reading_schema.md`・`reference/format_catalog.md`（とくに「コグニ以外の書式の写し方」）。
  判断に迷ったら `reference/judgment_rules.md`・`reference/painting.md`
- 案件一覧: `<NEO_CHECK_ROOT>/_nc/cases.json`（name / pdf / src）。担当は依頼文に書いた name だけ。`<NEO_CHECK_ROOT>` は
  `python .claude/skills/pdf-to-neo/scripts/skill_env.py` が表示する（既定 `%USERPROFILE%\Documents\NEO_check`）
- 作業フォルダ: `<NEO_CHECK_ROOT>/_nc/<name>`（無ければ作る）
- コマンドは Git Bash で `PYTHONIOENCODING=utf-8 python ...`。JSON は Write ツールか Python で書く（heredoc に `\` を含む日本語パスを入れない）
- 一時ファイルは作業フォルダの中に作る（共有の scratchpad の直下に置かない。`dis.py` のような標準ライブラリと同じ名前を作らない）

## 手順（案件ごと）
1. `python .claude/skills/pdf-to-neo/scripts/pdf_pages.py "<pdf>" "<作業>/pages/img"` でページ画像を作り、Read で全ページを見る
   - 上下に分けた画像（`--top/--bottom`）で読むときは、2 ページ目以降の**表の先頭行が切れていないか**全体の画像でも確かめる
   - **コグニ印刷（4 桁の部品コード列と「修理項目／部品名称」の見出し）なら対象外**。`agent_report.md` に「コグニ印刷なので対象外」と書いて次へ
   - 見積が無い（納品書・請求書）・車両の見積でない・税率が 10% 以外 などで作れないときも、理由を書いて次へ
   - 同じ見積を控えで何部も重ねた PDF（6 ページが 2 ページ × 3 部）は 1 部だけ写す
2. `python .claude/skills/pdf-to-neo/scripts/reading_pages.py init "<作業>" --pages <明細のあるページ数>` →
   `python .claude/skills/pdf-to-neo/scripts/header_auto.py "<作業>" "<src>"`（速報・確報から車両・顧客・保険を header.json に入れる。
   「車検証確認できず」のような印は名前にしない。確報が複数あるときは見積の日付に合う方か確かめる）
3. 画像の PDF は数字の先読みに `ocr_prefill.py "<pdf>" "<作業>"` を使ってよい（行ごとに画像で確かめて「OCR未確認」を消す。確かめられない値は comment に `要確認:`）
4. **見積書を印字のまま**写す（判断しない。reading_schema と format_catalog の書式 B〜G の規則）:
   header.json に format（B〜G）・est_date・labor_rate（印字や速報の工賃単価があれば）・paint・expenses・totals、page_N.json に明細（短縮記法でよい）・rows_printed・subtotal
   - **印字に無い欄を totals に書かない**（課税小計・工賃計を計算して書くと、税込の見積の判定が外れる）
   - 英語の部品名（HOOD COMP）・「品目,部位」の並び（ﾍﾞｰｽ,ﾌﾛﾝﾄｸﾞﾘﾙ）・名前の末尾の作業語（…交換）・作業の行と部品の行が別々、はそのまま写す（下書きが読む）
5. `reading_pages.py validate "<作業>" --page N` → 全ページ合格 → `merge` → `python .claude/skills/pdf-to-neo/scripts/make_neo.py "<作業>" --name auto --no-profile`
   （検証の案件は `--no-profile`: 工場プロファイルに学習させない）
6. 不合格・★・要確認 は判断規則で潰して再実行（reading を直す）。**合計を合わせるために明細の金額を動かさない**。
   下書きが部品を取り違えた行は reading の `code` に正しい部品コードを書いてよいが、comment に「下書きは ○○ に寄せた」と理由を必ず残す（親がスクリプトを直す材料）。
   どうしても合格しないときは理由を書いて止める
7. `<作業>/agent_report.md` に書く（顧客名・住所・電話・車台番号・登録番号・工場名は書かない。車名と案件 name で書く）:
   - 書式（B〜G と特徴）、ページ数・明細行数、合否、見積の合計 / NEO の合計
   - かかった手間（写すのに困った点・読み取りで迷った点）
   - **下書き・生成器の問題点**: report.md・_draft_notes・★・確認箇所シートを見て、見積書の印字と違う結果になった所（部品コードの取り違え・区分・名称・塗装の解釈・費用の振り分け・レート・装備 など）と、
     そうなった理由の見立て。reading の書き方で逃げた所も「本来はスクリプトが直すべき」と分かるように書く
   - 同じ案件に人が作った NEO があれば、`neo_compare.py` で比べた違い（書き方の違い）
   - ocr_prefill を使ったなら、その先読みの当たり外れ（行数・数字の外れの目安）

## 守ること
- 元案件の置き場（Z:）は読むだけ（案件フォルダに何も書かない・NEO を納品しない。`--deliver` を使わない）
- リポジトリのコード・文書を編集しない・git を触らない（問題は agent_report.md に書く。直すのは親の担当）
- コグニセブンを起動しない（刷るのは親）
- 最後の返答（親への報告）にも顧客情報を書かない。案件ごとに 合否・書式・合計の一致・問題点の要約 だけ返す
