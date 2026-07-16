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

## Depth-16 prefix-LCM steering scan

`search_depth16_prefix_lcm.rs` performs a deterministic finite search for an
integer `A` for which all sixteen numbers

```text
(720720 / k) * A - 1,  1 <= k <= 16
```

are prime. Such an `A` would make `n = 720720*A` satisfy the first sixteen
divisor budgets by the separately kernel-verified conditional-window theorem.
The scanner itself is computational steering and is not part of the formal
proof.

Build and reproduce the bounded scan from `ErdosProblems/erdos-647` with:

```powershell
rustc -O dossiers\tools\search_depth16_prefix_lcm.rs -o scratch\search_depth16_prefix_lcm.exe
.\scratch\search_depth16_prefix_lcm.exe 1000000000000 16 10000
```

The scanner audits the sixteen coefficients, checks local admissibility for
every sieving prime, and uses deterministic Miller--Rabin bases valid across
the full `u64` range. Completeness of the reduced progression follows from two
necessary conditions: the `k=16` form forces `A` even, and the sixteen roots
modulo 17 exhaust all nonzero residue classes, forcing `A = 0 (mod 17)`.
Consequently it is enough to scan `A = 0 (mod 34)`. All form values in the
reported run fit in `u64`, and the smallest possible form exceeds every
small-prime filter, so filtering never discards a form merely because that form
equals the filtering prime.

The completed 2026-07-15 run reported:

- audited range: `34 <= A <= 1,000,000,000,000`, `A = 0 (mod 34)`;
- 29,411,764,705 forced-progression candidates tested;
- seven candidates surviving the prime filters through 10,000;
- eleven deterministic Miller--Rabin tests after short-circuiting;
- elapsed time 362.415 seconds on 16 threads;
- throughput 81,155,024 forced candidates per second;
- no depth-16 witness in that exact finite range.

This null scan proves neither global nonexistence nor anything outside the
displayed finite range. In particular, it must not be cited as closing the
depth-16 case or Erdős #647. Its purpose is to measure the scarcity of this
specific prefix-LCM prime-tuple construction and steer the next formal attack.
