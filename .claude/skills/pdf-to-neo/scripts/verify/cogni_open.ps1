param([Parameter(Mandatory = $true)][string]$case, [string]$base = '_nc', [string]$neo = 'auto.neo')
# 検証用: 作った NEO を関連付けでコグニセブンの見積画面（AudaMain）に直接開く（見積一覧 AxFlLst は顧客名が並ぶので使わない）。
# 前に開いていた見積画面は閉じる。閉じるときに「保存しますか」が出た（コグニが開いた時点で何かを直した）ら止めて知らせる（保存しない）。
# 出力: opened / not opened（45 秒で開かなかった。もう一度回すと開くことが多い）/ SAVE-PROMPT / NO-NEO
# 使い方: powershell -NoProfile -ExecutionPolicy Bypass -File cogni_open.ps1 -case nc20 [-base _nc]
$root = $env:NEO_CHECK_ROOT
if (-not $root) { $root = Join-Path $env:USERPROFILE 'Documents\NEO_check' }
$dir = Join-Path $root (Join-Path $base $case)
$f = Join-Path $dir $neo
Get-Process AudaMain -ErrorAction SilentlyContinue | Where-Object { $_.MainWindowTitle.Length -gt 0 } | ForEach-Object { $_.CloseMainWindow() | Out-Null }
Start-Sleep 2
$left = Get-Process AudaMain -ErrorAction SilentlyContinue | Where-Object { $_.MainWindowTitle.Length -gt 0 }
if ($left) { 'SAVE-PROMPT pid=' + ($left | Select-Object -First 1).Id; exit }
if (-not (Test-Path $f)) { 'NO-NEO ' + $f; exit }
$prints = Join-Path $root '_prints'
New-Item -ItemType Directory -Force $prints | Out-Null
Remove-Item (Join-Path $prints ($case + '.pdf')) -ErrorAction SilentlyContinue
$menu = $env:COGNI_BIN
if (-not $menu) { $menu = 'C:\Program Files (x86)\Audatex\Auda7\Bin\AudaMenu.exe' }
Start-Process $menu -ArgumentList ('"' + $f + '"')
$p = $null
for ($i = 0; $i -lt 45; $i++) {
  Start-Sleep 1
  $p = Get-Process AudaMain -ErrorAction SilentlyContinue | Where-Object { $_.MainWindowTitle.Length -gt 0 }
  if ($p) { break }
}
if ($p) { 'opened' } else { 'not opened' }
