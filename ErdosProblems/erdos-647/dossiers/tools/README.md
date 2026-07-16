# Fixed-depth search tools

These scripts reproduce the computational search that guided the exact
shift-12 Lean witness. They are **steering evidence only**: the formal claims
used by the project are proved separately in
`proof/Erdos647_Shift12FrontierWitness.lean` and checked by Lean's kernel.

From `ErdosProblems/erdos-647`, run:

```powershell
rustc -C opt-level=3 -C target-cpu=native dossiers\tools\search_depth12.rs -o scratch\search_depth12.exe
.\scratch\search_depth12.exe 100000001 1000000000000 1000000000 1000 2>$null |
  python dossiers\tools\check_depth12_shortlists.py
```

The Rust stage uses a `46189 = 11 * 13 * 17 * 19` wheel, necessary
small-prime filters through the requested bound, and deterministic 64-bit
Miller--Rabin. The Python stage exactly factors the shortlists with SymPy and
checks the divisor budgets.

For the displayed range, the run produced:

- 2,613,389 necessary-sieve survivors;
- 1,414 seven-prime survivors;
- 71 shift-5/9/10 shortlists;
- 15 values passing shift 7;
- four values passing every shift from 1 through 12.

The first value found was `N = 244692464302`, hence
`n = 616625010041040`. The kernel-verified theorem proves this value meets
all budgets through shift 12 and first fails at shift 13. The scan does not
prove minimality, nonexistence outside the range, or any asymptotic claim.
