<#
.SYNOPSIS
  Launch one isolated VS Code window per Pantograph-epic issue (#158),
  each in its own git worktree + its own VS Code profile so the windows
  don't collide with each other or with your main window.

.DESCRIPTION
  For each issue number given:
    - creates (or reuses) a git worktree at <AgentsRoot>\issue-<N>, on a new
      branch feature/issue-<N> based on origin/develop
    - writes a NEXT_TASK.md briefing into that worktree (issue title, link,
      sprint-order reminder, and the standard-gitflow checklist to follow)
    - launches `code --new-window` with an isolated --user-data-dir and
      --extensions-dir (so it's a genuinely separate process you can close
      independently, not just another window of your main VS Code instance)
  Records what it launched in <AgentsRoot>\state.json for close-agents.ps1.

  Sprint order is per epic #158: 159 -> 162 -> 160 -> 161 -> 163 -> 167 ->
  164 -> 165 -> 166 -> 168. Launching issues out of that order risks an
  agent building against an interface (trait, schema, tool) that doesn't
  exist yet -- this script warns but does not block it.

.PARAMETER Issues
  Issue numbers to launch, e.g. -Issues 159,160

.PARAMETER All
  Launch every child issue (159-168) at once. Use with care -- see the
  sprint-order note above.

.EXAMPLE
  ./launch-agents.ps1 -Issues 159,160
.EXAMPLE
  ./launch-agents.ps1 -All
#>
param(
  [int[]]$Issues,
  [switch]$All,
  [string]$RepoRoot = "F:\Github\mnehmos.llm-driven-proof-search.environment",
  [string]$AgentsRoot = "F:\Github\.pse-agents"
)

$ErrorActionPreference = "Stop"

$AllIssues = @(159, 160, 161, 162, 163, 164, 165, 166, 167, 168)
$Titles = @{
  159 = "InteractiveProofGateway trait and backend abstraction"
  160 = "DB schema for interactive proof sessions, proof-state nodes, tactic-step edges"
  161 = "MCP tools for interactive proof sessions"
  162 = "Proof-state observation model (goals, local context, target, canonical hashes)"
  163 = "Tactic-step replay and proof-script reconstruction"
  164 = "Interactive-session export to trajectory_export / proof_export / training_export"
  165 = "Progress scoring and negative-space labels"
  166 = "Prototype Pantograph adapter behind InteractiveProofGateway"
  167 = "Tests for interactive proof-session vertical slice"
  168 = "Docs: README, readme_first, roadmap for interactive proof sessions"
}
$SprintOrder = @(159, 162, 160, 161, 163, 167, 164, 165, 166, 168)

if ($All) { $Issues = $AllIssues }
if (-not $Issues -or $Issues.Count -eq 0) {
  Write-Host "Sprint order (per epic #158): $($SprintOrder -join ' -> ')"
  Write-Host ""
  Write-Host "Usage:"
  Write-Host "  .\launch-agents.ps1 -Issues 159,160"
  Write-Host "  .\launch-agents.ps1 -All"
  exit 0
}

foreach ($i in $Issues) {
  if (-not $Titles.ContainsKey($i)) {
    Write-Warning "#$i is not one of the known Pantograph-epic child issues (159-168) -- launching it anyway, but NEXT_TASK.md will only have the issue number."
  }
}
$maxRequestedRank = ($Issues | ForEach-Object { $SprintOrder.IndexOf($_) } | Where-Object { $_ -ge 0 } | Measure-Object -Maximum).Maximum
$minRequestedRank = ($Issues | ForEach-Object { $SprintOrder.IndexOf($_) } | Where-Object { $_ -ge 0 } | Measure-Object -Minimum).Minimum
if ($maxRequestedRank -gt $minRequestedRank + ($Issues.Count - 1)) {
  Write-Warning "You're launching issues that are spread out in the stated sprint order ($($SprintOrder -join ' -> ')). Later ones may depend on work earlier ones haven't merged yet."
}

if (-not (Get-Command code -ErrorAction SilentlyContinue)) {
  Write-Error "VS Code CLI 'code' not found on PATH."
  exit 1
}

New-Item -ItemType Directory -Force -Path $AgentsRoot | Out-Null
$stateFile = Join-Path $AgentsRoot "state.json"
$state = @()
if (Test-Path $stateFile) {
  $raw = Get-Content $stateFile -Raw
  if ($raw.Trim().Length -gt 0) { $state = @(ConvertFrom-Json $raw) }
}

$launchedCount = 0
foreach ($issue in $Issues) {
  $branch   = "feature/issue-$issue"
  $worktree = Join-Path $AgentsRoot "issue-$issue"
  $userData = Join-Path $worktree "_vscode-userdata"
  $extDir   = Join-Path $worktree "_vscode-extensions"

  if (-not (Test-Path $worktree)) {
    Write-Host "Creating worktree for #$issue at $worktree (branch $branch, based on develop) ..."
    Push-Location $RepoRoot
    try {
      git fetch origin develop *> $null
      git worktree add -b $branch $worktree develop
    } finally {
      Pop-Location
    }
  } else {
    Write-Host "Worktree for #$issue already exists at $worktree -- reusing it."
  }

  $title = if ($Titles.ContainsKey($issue)) { $Titles[$issue] } else { "(see issue on GitHub)" }
  $taskFile = Join-Path $worktree "NEXT_TASK.md"
  $taskBody = @"
# Agent task: issue #$issue

**$title**
https://github.com/Mnehmos/llm-driven-proof-search/issues/$issue

Parent epic: #158 (Pantograph-style interactive proof sessions).
Sprint order: $($SprintOrder -join ' -> ')
Check the epic and this issue's own body for its actual prerequisites
before starting if this issue isn't at the front of that order.

Branch: ``$branch`` (already checked out in this worktree, based on develop).

## Standard gitflow for this issue

1. Read the full issue body (``gh issue view $issue`` or the URL above) --
   this file only has the title, not the full spec.
2. Confirm prerequisite issues are actually merged into develop before
   starting; if not, stop and say so instead of guessing at an unstable
   API surface.
3. Implement + add tests in this worktree, on this branch.
4. Commit with a message referencing #$issue.
5. Push the branch and open a PR against develop (put ``Closes #$issue`` in
   the PR body). Do not merge it yourself -- leave that for review.
6. Update this file or comment on the issue with what's done / what's left,
   so the next session (or the next /loop firing) can pick it up cold.
"@
  Set-Content -Path $taskFile -Value $taskBody -Encoding utf8

  Write-Host "Launching VS Code for #$issue ..."
  Start-Process -FilePath "code" -ArgumentList @(
    "--new-window",
    "--user-data-dir", "`"$userData`"",
    "--extensions-dir", "`"$extDir`"",
    "`"$worktree`""
  ) | Out-Null

  Start-Sleep -Seconds 2
  $proc = Get-CimInstance Win32_Process -Filter "Name='Code.exe'" |
    Where-Object { $_.CommandLine -and $_.CommandLine.Contains($userData) } |
    Select-Object -First 1

  if (-not $proc) {
    Write-Warning "Couldn't identify the new Code.exe process for #$issue -- close-agents.ps1 won't be able to auto-close this window by PID. Close it manually if needed."
  }

  $entry = [pscustomobject]@{
    issue    = $issue
    branch   = $branch
    worktree = $worktree
    userData = $userData
    extDir   = $extDir
    pid      = $(if ($proc) { $proc.ProcessId } else { $null })
    launched = (Get-Date).ToString("o")
  }
  $state = @($state | Where-Object { $_.issue -ne $issue }) + $entry
  $launchedCount++
}

$state | ConvertTo-Json -Depth 4 | Set-Content -Path $stateFile -Encoding utf8
Write-Host ""
Write-Host "Launched $launchedCount agent window(s). State: $stateFile"
Write-Host "Close them with: .\close-agents.ps1  (or -Issues 159,160 / -All)"
