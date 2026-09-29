param([string]$Distribution = 'Debian')
$ErrorActionPreference = 'Stop'
$repoRoot = Split-Path -Parent $PSScriptRoot
# Pass paths as arguments, not interpolated shell source (spaces are supported).
$linuxRoot = & wsl.exe -d $Distribution -- wslpath -a -u $repoRoot.Replace('\', '/')
if ($LASTEXITCODE -ne 0) { throw "Cannot locate checkout in WSL distribution $Distribution" }
& wsl.exe -d $Distribution -- bash ($linuxRoot.Trim() + '/scripts/demo.sh')
if ($LASTEXITCODE -ne 0) { throw "M2Lean demo failed (exit $LASTEXITCODE)" }
