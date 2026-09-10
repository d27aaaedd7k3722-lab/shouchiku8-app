---
title: Shouchiku8 Neo
emoji: 🚗
colorFrom: blue
colorTo: indigo
sdk: streamlit
sdk_version: "1.45.1"
python_version: "3.11"
app_file: app.py
pinned: false
---

---

# ⚠️ このリポジトリは開発を終了しました（2026-09-10）

NEO見積変換アプリの開発は **[neo-estimate](https://github.com/d27aaaedd7k3722-lab/neo-estimate)** に一本化しました。

- **本番URL**: https://shouchiku-neo-estimate.streamlit.app/ ← `neo-estimate` の `main` を配信
- **開発はすべて `neo-estimate` で行う**
- ローカルの作業場所: `C:\Users\R-T\dev\neo-estimate`

このリポジトリの内容（12周のバグハントで確定した約60件の修正・回帰テスト6本・`docs/引き継ぎ書.md`）は
すべて `neo-estimate` の `d3e92b4` に移してあります。ここは履歴の保存用として残しています。

## なぜ分かれていたか

Streamlit Cloud にアプリが2つあり、本番URLが配信していたのは `neo-estimate`（2026-03 の初版）でした。
このリポジトリで進めていた改修は、誰も使っていない別URL
（shouchiku8-ap-z4idyjptyyhv2n94aefbjd.streamlit.app）にデプロイされていて、
本番には半年間まったく反映されていませんでした。
2026-09-10 に `neo-estimate` を最新版で入れ替え、開発をそちらへ一本化しています。
入れ替え前の 2026-03 版は `neo-estimate` の `backup/2026-03-original` ブランチにあります。
