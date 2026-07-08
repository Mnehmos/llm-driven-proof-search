<#
.SYNOPSIS
  Close VS Code windows launched by launch-agents.ps1.

.DESCRIPTION
  Kills the Code.exe process recorded for each targeted issue in
  <AgentsRoot>\state.json. Does NOT delete git worktrees or branches --
  those may hold uncommitted or unpushed work; clean those up manually
  once you've confirmed the work is merged (or intentionally discarded).

.PARAMETER Issues
  Issue numbers to close, e.g. -Issues 159,160. Defaults to all launched
  agents if neither -Issues nor -All is given.

.PARAMETER All
  Close every currently-launched agent window.

.EXAMPLE
  ./close-agents.ps1 -Issues 159
.EXAMPLE
  ./close-agents.ps1 -All
#>
param(
  [int[]]$Issues,
  [switch]$All,
  [string]$AgentsRoot = "F:\Github\.pse-agents"
)

$ErrorActionPreference = "Stop"

$stateFile = Join-Path $AgentsRoot "state.json"
if (-not (Test-Path $stateFile)) {
  Write-Host "No agent state file found at $stateFile -- nothing to close."
  exit 0
}

$raw = Get-Content $stateFile -Raw
$state = if ($raw.Trim().Length -gt 0) { @(ConvertFrom-Json $raw) } else { @() }

$targets = if ($All -or -not $Issues -or $Issues.Count -eq 0) {
  $state
} else {
  $state | Where-Object { $Issues -contains $_.issue }
}

if (-not $targets -or $targets.Count -eq 0) {
  Write-Host "No matching launched agents found in $stateFile."
  exit 0
}

foreach ($t in $targets) {
  if ($t.pid) {
    $p = Get-Process -Id $t.pid -ErrorAction SilentlyContinue
    if ($p -and $p.ProcessName -eq "Code") {
      Write-Host "Closing VS Code for issue #$($t.issue) (pid $($t.pid)) ..."
      Stop-Process -Id $t.pid -Force
    } else {
      Write-Host "Issue #$($t.issue): recorded process (pid $($t.pid)) is not running -- already closed."
    }
  } else {
    Write-Host "Issue #$($t.issue): no pid was recorded at launch time -- close it manually."
  }
}

$closedIssues = @($targets | ForEach-Object { $_.issue })
$remaining = @($state | Where-Object { $closedIssues -notcontains $_.issue })
$remaining | ConvertTo-Json -Depth 4 | Set-Content -Path $stateFile -Encoding utf8

Write-Host ""
Write-Host "Closed $($targets.Count) window(s)."
Write-Host "Worktrees were NOT deleted (they may hold uncommitted work). Review each:"
foreach ($t in $targets) {
  Write-Host "  git -C `"$($t.worktree)`" status   # issue #$($t.issue), branch $($t.branch)"
}
Write-Host ""
Write-Host "Once an issue's PR is merged, clean up manually:"
Write-Host "  git worktree remove <path>"
Write-Host "  git branch -d <branch>"
