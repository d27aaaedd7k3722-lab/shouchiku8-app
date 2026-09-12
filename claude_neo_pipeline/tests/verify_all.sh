#!/bin/bash
# 検証一式: 生成器の単体テスト（連動・吸収・設定・入力ガード・型ゆれ・表構造・内部整合）/ FRAME 比較 / ラウンドトリップ /
# ChangeTotal / 色別部品 / 実機 NEO との総当たり（ERParts 全列・AnSMB 142 桁）/ スキルの単体テスト（scripts/tests/test_*.py）/ 案件回帰
SP="$(cd "$(dirname "$0")" && pwd)"
cd "$SP/../.." || exit 1
export PYTHONIOENCODING=utf-8
set -o pipefail   # tail/grep に流しても python の終了コードを残す（Codex 96）
# 案件フォルダの根（開発機の個人名を埋め込まない。regress_cases.py と同じ環境変数を見る）
NEO_CHECK="${NEO_CHECK_ROOT:-$HOME/Documents/NEO_check}"
fail=0
run() { local label="$1"; shift; echo "=== $label"; "$@" || { echo "*** FAILED: $label"; fail=1; }; }
run 'unit' bash -c 'set -o pipefail; python "$0/unit_frame.py" | tail -3' "$SP"
run 'unit eva slot (cogni 2026-09-08)' bash -c 'set -o pipefail; PYTHONIOENCODING=utf-8 python "$0/unit_eva_slot.py" | tail -2' "$SP"
run 'unit manual rows (cogni 2026-09-08)' bash -c 'set -o pipefail; PYTHONIOENCODING=utf-8 python "$0/unit_manual_rows.py" | tail -2' "$SP"
run 'unit settings (cogni 2026-09-08)' bash -c 'set -o pipefail; PYTHONIOENCODING=utf-8 python "$0/unit_settings.py" | tail -2' "$SP"
run 'unit link/absorb (cogni 2026-09-08 H1-H7/G1)' bash -c 'set -o pipefail; PYTHONIOENCODING=utf-8 python "$0/unit_link_absorb.py" | tail -2' "$SP"
run 'AnSMB 142 桁一致 (そのまま保存 25 本・実案件を含む)' bash -c 'set -o pipefail; PYTHONIOENCODING=utf-8 python "$0/audit_cogni_files.py" --ansmb | tail -1' "$SP"
run 'unit guards (入力の境界)' bash -c 'set -o pipefail; PYTHONIOENCODING=utf-8 python "$0/unit_guards.py" | tail -1' "$SP"
run 'frame gen' bash -c 'set -o pipefail; python "$0/test_frame_gen.py" 2>&1 | tail -3' "$SP"
run 'frame wage' bash -c 'set -o pipefail; python "$0/test_frame_wage.py" 2>&1 | tail -2' "$SP"
run 'fbanpa' bash -c 'set -o pipefail; python "$0/test_fbanpa.py" 2>&1 | tail -2' "$SP"
run 'roundtrip' bash -c 'set -o pipefail; timeout 500 python "$0/roundtrip.py" 2>&1 | tail -3' "$SP"
run 'ChangeTotal' bash -c 'set -o pipefail; python "$0/ct_frame.py" 2>&1 | tail -2' "$SP"
run 'color parts (83/13.DB)' bash -c 'set -o pipefail; python "$0/test_color13.py" 2>&1 | tail -2' "$SP"
# 案件回帰（NEO_check/_cases.json に載る案件。フォルダ名は損保名を含むのでリポジトリに書かない）
run '案件回帰 (NEO_check/_cases.json)' bash -c 'set -o pipefail; PYTHONIOENCODING=utf-8 python claude_neo_pipeline/tests/regress_cases.py 2>&1 | tail -8'
# スキル pdf-to-neo の回帰（NEO_check の reading.json 全案件: 再下書きが正解 expected_estimate.json と一致し run_case 合格）
if [ -d "$HOME/Documents/NEO_check/_eva_exp" ]; then
  run 'unit struct (生成 NEO の表構造が実機と同じか)' bash -c 'set -o pipefail; PYTHONIOENCODING=utf-8 python claude_neo_pipeline/tests/unit_struct.py 2>&1 | tail -1'
fi
run 'unit consistency (明細・AnSMB・損傷部品の整合)' bash -c 'set -o pipefail; PYTHONIOENCODING=utf-8 python claude_neo_pipeline/tests/unit_consistency.py 2>&1 | tail -1'
run 'unit types (手書き estimate の型ゆれ)' bash -c 'set -o pipefail; PYTHONIOENCODING=utf-8 python claude_neo_pipeline/tests/unit_types.py 2>&1 | tail -1'
# 引き継ぎ文書（HANDOFF.md）の主張が実装・実データと合っているか（文書が古くなるのを機械で見張る）
run 'unit handoff (引き継ぎ文書と実装の一致)' bash -c 'set -o pipefail; PYTHONIOENCODING=utf-8 python claude_neo_pipeline/tests/unit_handoff.py 2>&1 | tail -1'
if [ -d "$HOME/Documents/NEO_check/_eva_exp" ]; then
  run 'cogni 実機 NEO との総当たり' bash -c 'set -o pipefail; PYTHONIOENCODING=utf-8 python claude_neo_pipeline/tests/audit_cogni_files.py 2>&1 | tail -1'
fi
# 全ファイル一致は「実機ファイルが無いので行っていない」ことを必ず出したいので、条件分岐で丸ごと飛ばさない
# 開発機の関門なので、実機ファイル（NEO_check/_eva_exp）が欠けていたら「未実施のまま合格」にせず失敗させる
run '全ファイル一致（そのまま保存した実機 NEO）' bash -c 'set -o pipefail; PDF_TO_NEO_REQUIRE_FIXTURES=1 PYTHONIOENCODING=utf-8 python claude_neo_pipeline/tests/audit_cogni_files.py --full-files 2>&1 | tail -3'
# スキルの単体テストは glob で全件回す（テストが増えたら自動で拾う。個別に列挙すると新しい分が静かに抜ける）。
# 1 本も無いのは配布物が壊れているということなので失敗にする
# 配布の要になるテストは名前で存在も確かめる（glob 実行だけだと、1 本落ちても他が残っていれば緑になる）
for must in test_skill_env test_pick_grade test_find_ref_by_price test_guess_labor_rate test_reading_check test_reading_pages test_draft_notes test_draft_rules test_alias test_ocr_prefill; do
  [ -f ".claude/skills/pdf-to-neo/scripts/tests/$must.py" ] || { echo "*** FAILED: 必須のスキルテスト $must.py が無い"; fail=1; }
done
skill_tests=$(ls .claude/skills/pdf-to-neo/scripts/tests/test_*.py 2>/dev/null | sort)
if [ -z "$skill_tests" ]; then
  echo '*** FAILED: スキルの単体テスト（.claude/skills/pdf-to-neo/scripts/tests/test_*.py）が 1 本も無い'
  fail=1
else
  for t in $skill_tests; do
    run "skill $(basename "$t" .py)" bash -c 'set -o pipefail; PYTHONIOENCODING=utf-8 python "$0" 2>&1 | tail -2' "$t"
  done
fi
if [ -f .claude/skills/pdf-to-neo/scripts/regress_cases.py ]; then
  run 'skill regress (reading.json cases)' bash -c 'set -o pipefail; PYTHONIOENCODING=utf-8 python .claude/skills/pdf-to-neo/scripts/regress_cases.py 2>&1 | tail -6' 
fi
echo "=== verify_all exit $fail"
exit $fail
