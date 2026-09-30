# 検証と精度改善の手順書（工場見積 → NEO → コグニで刷る → 突き合わせ → 直す）

pdf-to-neo の**精度を測って上げる**ための手順。NEO を 1 件作る手順（SKILL.md）とは別で、「たくさんの実案件で作って、コグニで刷って、
元の見積書と違う所を見つけて、スクリプトを直す」ときに使う。2026-09-28〜30 に 36 件（コグニ以外）＋ 30 件（コグニ印刷）で回した方法をそのまま手順にした。

**別のチャット・別の担当で続けるときは**: `HANDOFF.md` → `SKILL.md` → この文書 → `docs/pdf-to-neo_ロードマップ.md` の §9〜§13 の順に読む。
作業データ（顧客名・見積の画像・NEO）はすべてリポジトリの外 `<NEO_CHECK_ROOT>`（既定 `%USERPROFILE%\Documents\NEO_check`）にある。

---

## 0. いまの数字（2026-09-30。直したらこれを下回らないこと）

| 物差し | 道具 | いまの値 |
|---|---|---|
| スキル・生成器のテスト | `scripts/tests/test_*.py`・`claude_neo_pipeline/tests/unit_*.py`・`env_check.py --self-test` | 全部合格 |
| 回帰（人が確かめた正解との一致） | `scripts/regress_cases.py` | 22 / 22 |
| コグニ印刷 FAX の自動読み取り | `scripts/ocr_eval.py` | 369 行・**確定なのに違う 0**・確定 342 |
| コグニ以外の書式: 部品コードの当たり | `verify/code_accuracy.py` | **971 / 1,028（94.5%）**（29 件） |
| コグニ以外の書式: 作り直しの合否 | `verify/remake_cases.py --base _nc` | 38 / 38（見積でない nc01・nc09 を除く。紙上検算も通す） |
| コグニ印刷の自動読み取り → NEO | `verify/remake_cases.py --base _batch` | 28 件中 18 合格（`--skip-check` なら 20。sienta・f03 は自動読み取りの写しに紙上検算の FAIL が 1 つずつ残る。ほかの不合格は車両が決まらない t02・t13・f05、FAX の OCR で ADDATA に照合できない f01・f02・f04、t03・t08。既知） |
| コグニで刷った印刷と見積書 | `verify/print_compare.py` | 合計は刷った 36 件すべて一致。行の差は 1 件 0〜3 で全部説明がつく（下の §5） |

---

## 1. 全体の流れ

| 段 | すること | 道具 | 置き場 |
|---|---|---|---|
| ① 探す | 元案件の置き場（Z:）を走査し、工場見積・速報・人の NEO の有無を一覧に | `verify/survey_cases.py` | `_verify/survey.json` |
| ② 選ぶ | コグニ以外の書式の見積を探して、検証する案件に足す | `verify/noncogni_candidates.py --want 40` → `--add 19` | `_nc/cases.json` |
| ③ 写す・作る | サブエージェント（1 体 2〜4 件）が印字どおりに写して make_neo で NEO に | `reference/verify_agent_task.md` を渡す | `_nc/ncNN/`（reading.json・auto.neo・agent_report.md） |
| ④ 刷る | コグニで開いて「見積り1（塗装明細）」を PDF(通常) に | `verify/cogni_open.ps1` ＋ computer-use（§4） | `_prints/ncNN.pdf` |
| ⑤ 突き合わせる | 刷った PDF と下書きの明細・写しの合計を行ごとに | `verify/print_compare.py` | `_nc/print_compare.json` |
| ⑥ 測る | 部品コードの当たり・外れの原因 | `verify/code_accuracy.py -v --why` | |
| ⑦ 直す | 外れの行を追って（`debug_row.py`・`debug_find.py`）スクリプトを直す → 全部の物差しを回す → Codex で見てもらう | codex-loop | |
| ⑧ 記録 | ロードマップ・日誌・（必要なら）format_catalog / judgment_rules | | `docs/pdf-to-neo_ロードマップ.md` |

コグニ印刷の見積（書式 A）は ② の代わりに `ocr_anchor.py --src`（自動読み取り）で `_batch/` に作り、同じ ④〜⑦ を回す。

## 2. 探す・選ぶ（①②）

```bash
PYTHONIOENCODING=utf-8 python .claude/skills/pdf-to-neo/scripts/verify/survey_cases.py            # 数分。ファイル名だけ見る
PYTHONIOENCODING=utf-8 python .claude/skills/pdf-to-neo/scripts/verify/noncogni_candidates.py --want 40  # 数十分（画像の PDF は OCR で書式を見分ける）
PYTHONIOENCODING=utf-8 python .claude/skills/pdf-to-neo/scripts/verify/noncogni_candidates.py --add 19 --max-pages 6
```

- 速報・確報のある案件だけを選ぶ（車両・保険を header_auto で埋めるため）。新しい案件から順
- FAX 受信名の PDF（`0938633113_20260916_172058.pdf`）は見積でないことがある（部品商の納品書・レンタカーの請求書）。担当が見て除く
- 7 ページ以上は控えを重ねた束や別の書類が多いので `--max-pages 6`
- **人が作った NEO がある案件**（`has_human_neo`）は答え合わせに使える（`neo_compare.py`）

## 3. 写す・作る（③）

サブエージェントを並べて回す（1 体 2〜4 件・7 体で 19 件が約 15 分）。渡すのは指示書のパスと案件名だけ:

> `.claude/skills/pdf-to-neo/reference/verify_agent_task.md` を最初に読み、その手順と「守ること」に従って、担当案件 nc20, nc21, nc22 を NEO にしてください。

- 担当は reading で逃げた所（下書きが取り違えたので code を書いた・合わない欄を直した）を `agent_report.md` に「本来はスクリプトが直すべき」として書く。**これが直す材料の一覧**になる
- 親は報告を受けるたびに問題点を 1 つの一覧（scratchpad の issues.md など）に足していく（番号を振ると後で追いやすい）

## 4. コグニで刷る（④）— computer-use

**使ってよいのは「コグニセブン」と `audamain.exe` だけ**（request_access で両方。audamain は見積画面が開いてから）。見積一覧（AxFlLst）は顧客名が並ぶので使わない。
プリンタは使わない（PDF(通常)）。既定プリンタを変えない。案件の NEO を上書き保存しない。

1 件ごとに:

```bash
powershell -NoProfile -ExecutionPolicy Bypass -File .claude/skills/pdf-to-neo/scripts/verify/cogni_open.ps1 -case nc20 -base _nc
```

→ `opened` を確かめてから computer-use（座標は 1456×819 の画面基準。2026-09-29 に 19 件で使った）:

1. コグニの窓をクリック (1100,700) → 印刷のアイコン (104,34)
2. 帳票「見積り1（塗装明細）」(390,218)（塗装明細の無い見積なら「見積り1」(390,146)）→ **PDF(通常)** (656,698)
3. 車両の確認画面が出たらその **PDF(通常)** (1116,64)（汎用車種では出ない。出なくても押して害はない）。保留・コメント行がある NEO は先に「次へ>」の画面が出る（PDF(通常) は (1115,65)）
4. 保存の画面のファイル名 (724,399) に `<NEO_CHECK_ROOT>\_prints\nc20.pdf` のフルパスを打って Enter
5. 次の案件の `cogni_open.ps1` が前の見積画面を閉じる。`SAVE-PROMPT` が出たら「保存しますか」が出ている（コグニが開いた時点で何かを直した合図 = 調べる対象）。**保存せずに閉じる**

よくある詰まり:
- `not opened`（45 秒で開かない）: もう一度回すと開く（19 件で 2 回）
- **日本語入力の小さな窓（TextInputHost）が前に居座り、クリックが全部止まる**: その窓の操作は許可されていないので自分で閉じない・プロセスを止めない。
  人に「コグニのメニューを 1 回クリックするか、入力の窓を閉じてください」と頼む（閉じてもらえばすぐ再開できる）
- 「基本単価の入力」（新規見積）が出たら、ドアのアイコンで抜ける（何も保存されない）

## 5. 突き合わせる（⑤）と、説明のつく差

```bash
PYTHONIOENCODING=utf-8 python .claude/skills/pdf-to-neo/scripts/verify/print_compare.py --base _nc
```

合計が違えば必ず原因を突き止める。行の差のうち次は**説明のつく差**（直さない・直せない）:

| 差 | 理由 |
|---|---|
| 費用名「写真代」→「写真代他」、「エーミング」→「ｴｰﾐﾝｸﾞ費用」 | 社内の雛形の行に寄せる規則（実機 NEO の運用） |
| 合計 +1 円（税込で刷られた見積で費用がある） | コグニ（内税）は費用の**合計**に税をかける。工場は 1 行ずつ税込で足す。下書きが 3 点セットと要確認で予告する（nc30 で実機確認） |
| 価格の無い部品（オイル・ガス）の品番欄「-」 | コグニの標準（11.DB の品番が '-'） |
| 費用名が 20 バイトで切れる | NEO の費用名の欄の長さ |
| 部品価格・品番の枝番の `*` | 工場とこの PC の ADDATA の版の違い |
| 手入力行の部品コード（工場 0000 / 生成 空欄） | コグニ実機で手入力行のコードは空欄 |

刷った後に案件を作り直したら**刷り直してから**比べる（古い NEO の印刷と新しい下書きを比べると差が大量に出る）。

## 6. 測る・直す（⑥⑦）

```bash
PYTHONIOENCODING=utf-8 python .claude/skills/pdf-to-neo/scripts/verify/code_accuracy.py -v --why
PYTHONIOENCODING=utf-8 python .claude/skills/pdf-to-neo/scripts/verify/debug_row.py nc30 ｶﾞﾗｽ ｸﾘｯﾌﾟ --strip
PYTHONIOENCODING=utf-8 python .claude/skills/pdf-to-neo/scripts/verify/debug_find.py nc30 Fｶﾞﾗｽｳｴｻﾞｽﾄﾘｯﾌﾟ --block A30 --unit 1780
```

直したら**全部**回す（どれか 1 つでも下がったら直し方を見直す）:

```bash
for t in .claude/skills/pdf-to-neo/scripts/tests/test_*.py claude_neo_pipeline/tests/unit_*.py; do PYTHONIOENCODING=utf-8 python "$t" >/dev/null 2>&1 || echo "FAIL $t"; done
PYTHONIOENCODING=utf-8 python .claude/skills/pdf-to-neo/scripts/env_check.py --self-test
PYTHONIOENCODING=utf-8 python .claude/skills/pdf-to-neo/scripts/regress_cases.py
PYTHONIOENCODING=utf-8 python .claude/skills/pdf-to-neo/scripts/ocr_eval.py              # ocr_anchor を触ったとき
PYTHONIOENCODING=utf-8 python .claude/skills/pdf-to-neo/scripts/verify/code_accuracy.py
PYTHONIOENCODING=utf-8 python .claude/skills/pdf-to-neo/scripts/verify/remake_cases.py --base _nc
PYTHONIOENCODING=utf-8 python .claude/skills/pdf-to-neo/scripts/verify/remake_cases.py --base _batch   # コグニ印刷に悪さをしていないか
```

`remake_cases.py` は 1 件でも不合格なら終了コード 1（`_batch` は既知の不合格があるので、合格の顔ぶれが §0 と同じかで見る）。
既定で紙上検算も通し（`--skip-check` で飛ばせる）、下書きが書いた 3 点セットは認めた扱い（`--no-allow-neo-total` で外せる）。
`print_compare.py` は刷った PDF の無い案件を「PDF が無い」と数えて出す。終了コード: 1 = 比べられなかった（名指しした案件の PDF が無い・読めない PDF・1 件も比べていない）、
2 = **合計が違う**（下書きが 3 点セットで予告した額でもない。必ず原因を突き止める）。行の差は説明のつく差があるので終了コードにせず、§5 の表で 1 つずつ見る。
`code_accuracy.py` は、落ちた案件がある・1 行も測れなかった・名指しした案件が測れないときに終了コード 1。

直し方の約束（これまでに効いたもの・外したもの）:
- **コグニ印刷（書式 A）に効かせない規則は書式で分ける**（部品コードが刷られる書式に、名前から部品を推す規則を当てない）。作り直し `_batch` で確かめる
- 回帰の正解が昔の下書きの誤りを固めていることがある。**意味で正しいと言えるときだけ** `regress_cases.py --only <案件> --update`
- 名前の完全一致は強い。ただし「ｸﾘｯﾌﾟ」のような部位ごとにある小物の名前は例外
- **同じ行が並んでいても、勝手に別々の部品に配らない**。ADDATA が枝番（(NO.n)）で位置を分けている族だけ配る。
  名前が同じだけの族（ﾌﾞﾗｹﾂﾄ ×3・ｴﾙﾎﾞｼﾞﾖｲﾝﾄ ×3）は、**同じ部品を 2 行に書いた見積と見分けられない**
  （人が確かめた回帰の正解では同じ部品コードが 2 行に入るのが正しかった。2026-09-30 実測）
- 「合計を合わせるために明細を動かす」直し方はしない。数円の差は理由を 3 点セット（neo_total / tolerance / 理由）で残し、`--allow-neo-total` は人が付ける
- コード変更は codex-loop（Codex に 1 周ずつ見せ、指摘を直して、合格まで）
- コミット前に差分を grep して取引先名・顧客名・電話・車台番号・登録番号が無いことを確かめる（GitHub は公開）

## 7. バグハント

まとまった変更のあとに 1 回。範囲の差分をファイルのまとまりで 3 つに分け、Codex を並べて「クラッシュする入力・規則どうしの食い違い・税と丸め・左右前後・
書式 A への悪影響」を探させる。自分でも境界値（空・None・0・負の金額・全角・カンマ付きの数字・「不明商事」のような紛らわしい名前）で関数を叩く
（`scripts/tests/test_edge_values.py`）。見つけたものは直して、§6 の全部を回す。2026-09-29 の記録はロードマップ §13。

## 8. 実機で確かめた事実（この検証で分かったこと）

- 税込で刷られた見積の数量行: 工場は 1 個の税込単価ごとに割り戻す。コグニは NEO の数量行を**見積書の税込額そのまま**で刷る（nc23・nc30・nc38）
- コグニ（内税）は費用の合計に税をかける（工場の印字より 1 円多くなることがある。nc30）
- 材料代の「単価 × 係数」方式はコグニが保持しない（開くと手入力に変わる）→ 生成器は額を手入力で書く
- 手入力行の自由な作業名（DisposalCode -1）は指数の無い行でだけ使える
- 開いた NEO を閉じるときに「保存しますか」が出るのは、コグニが開いた時点で何かを直した合図

## 9. 残っている課題

ロードマップ §11-2・§12（部品コードを 99% に近づける・読み取りを自動に近づける）・§13 の末尾。
いちばん効く次の手は「過去の工場見積 ⇔ 人が作った NEO の組から学ぶ」（§12-2）。
