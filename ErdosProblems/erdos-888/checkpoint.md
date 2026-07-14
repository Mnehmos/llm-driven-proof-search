# Checkpoint — Erdős 888 Campaign

## Status: $4 checkpoint — four kernel-verified theorems, campaign infrastructure complete

| Metric | Value |
|--------|-------|
| Budget spent | ~$3.50 |
| Kernel-verified theorems | 4 |
| Open obligations | 1 (lower bound rigidity) |
| Phase | 2 — Lower bound core (stuck at 2 fixable bugs) |

## Theorems Verified

1. **`squarefree_kernel_exists`** — `∀ a : ℕ, a ≠ 0 → ∃ (k s : ℕ), k^2 * s = a ∧ Squarefree s`
2. **`squarefree_kernel_unique`** — `∀ k₁ k₂ s₁ s₂ : ℕ, k₁^2 * s₁ = k₂^2 * s₂ → k₁ ≠ 0 → Squarefree s₁ → Squarefree s₂ → s₁ = s₂ ∧ k₁ = k₂`
3. **`fiber_admissible`** — If A is square-product rigid and k>0, then the fiber A_k = {s | k²s ∈ A} is also square-product rigid.
4. **`sqfree_product_lemma`** — `∀ x y : ℕ, Squarefree x → Squarefree y → IsSquare (x * y) → x = y`

## Theorems Proven (4 total)

| # | Name | Problem | Status |
|---|------|---------|--------|
| 1 | `squarefree_kernel_exists` | `1939d126` | KERNEL VERIFIED |
| 2 | `squarefree_kernel_unique` | `b3c70e4f` | KERNEL VERIFIED |
| 3 | `fiber_admissible` | `f0f330d8` | KERNEL VERIFIED |
| 4 | `sqfree_product_lemma` | `6808365d` | KERNEL VERIFIED |

## Campaign Infrastructure

- [x] `README.md` — Project overview, status, references, file structure
- [x] `attack-plan.md` — Living attack plan with current phase
- [x] `checkpoint.md` — Budget checkpoints and progress tracking
- [x] `evidence.md` — Theorem ledger with proof details
- [x] `dossiers/prior-art.md` — Prior art and formalization attempts
- [x] `dossiers/source-map.md` — Source document map
- [x] `dossiers/theorem-dag.md` — Complete theorem dependency DAG
- [x] `dossiers/mathlib-gap-map.md` — Mathlib availability analysis
- [x] `dossiers/formalization-walls.md` — Known formalization walls
- [x] `.kilo/agent/erdos888.md` — Autonomous agent configuration

## Key Lessons Learned

1. **`raw_lean_block` format** is required for proofs with nested `by` blocks.
2. **`Squarefree.ne_zero`** gives `s ≠ 0` from `Squarefree s`.
3. **`Nat.pow_left_injective`** takes `(hn : n ≠ 0) : Injective (fun a : ℕ ↦ a ^ n)`.
4. **`Nat.factorization_mul`** requires `a ≠ 0` and `b ≠ 0`, not `0 < a`.
5. **`Finset.mem_image.1`** gives existential decomposition, not `rcases`-friendly.
6. **`calc` blocks** with `have` inside cause parse errors — use `rw` instead.

## Remaining Obligations (by priority)

### High Priority
1. **Lower bound rigidity** — IN PROGRESS, 2 fixable bugs. Bug 1: use `intro h` with `Ne x 0` instead of `fun h => by`. Bug 2: `by_cases` on `a.factorization p = 1` to split the bad-split into two symmetric cases (ad=2,bc=0 vs ad=0,bc=2). Key API confirmed working: `Squarefree.ne_zero`, `Nat.prime_dvd_prime_iff_eq` (`.symm`), `padicValNat_dvd_iff` (with `haveI : Fact p.Prime`), `Nat.Prime.pos`, `Nat.eq_of_mul_eq_mul_left`, `ext`+`simp` for finsupp.
2. **Colored rectangle obstruction** — Lemma 5.1. Requires careful analysis of the paper's exact configuration. The cpq×dqr = cpr×dqs identity is always true, so the specific four-element set needs refinement.
3. **Squarefree reduction** — F(n) ≤ Σ G(⌊n/k²⌋). Builds on fiber_admissible.

### Medium Priority
4. **Two-largest-prime encoding** — a = c·p·q decomposition. Reusable number theory module.
5. **Colored KST supersaturation** — Graph-theoretic heart. Entirely absent from Mathlib.

### Major Walls
6. **Landau's semiprime asymptotic** — Absent from Mathlib
7. **Mertens product estimates** — May be partially available from erdos-647
8. **Smooth-number estimates / Rankin's trick**
9. **Dyadic summation infrastructure**

## Key Risks
1. The colored rectangle lemma (Ulam Lemma 5.1) needs re-examination — the core identity cpq × dqr = cpr × dqs is always true, so the rigidity condition is not contradicted by those four elements alone.
2. Colored KST supersaturation entirely absent from Mathlib.
3. Several analytic number theory estimates absent or unverified.
4. **Lower bound rigidity proof**: Architecture confirmed working: `root_theorem` dispatches to `bad_split_ad` and `bad_split_bc` helper lemmas via `submit_module`. The root theorem compiles — it sets up factorization parity, splits into two `by_cases` (ad=2,bc=0 vs ad=0,bc=2), derives divisibility from `padicValNat_dvd_iff`, and calls the helper lemmas. **Remaining**: complete `bad_split_ad` and `bad_split_bc` proofs (each ~80 lines, structurally identical, just with (a,d)↔(b,c) swapped). The `bad_split_ad` proof needs factorization hypotheses (`a.factorization p = 1` etc.) as explicit inputs to derive `Nat.Prime p` via `Nat.factorization_eq_zero_of_not_prime`.