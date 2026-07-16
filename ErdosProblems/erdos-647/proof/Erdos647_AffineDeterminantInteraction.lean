import Mathlib

/-!
# Erdős #647 — universal affine determinant interaction (Engine A, layer 1)

Snapshot of the exact statement + proof term kernel-verified through the
tracked proof-search pipeline on 2026-07-16.

  problem_version_id  ef11f0f3-eb84-4499-b445-d0518121c5f2
  episode_id          c31387c9-0f87-40d0-8b0a-fa43451c333a
  root_statement_hash 2c28aaa3e5678c00e99af020ab2c661c3254c42fe23655ca37bf63e1f55dacab
  outcome             kernel_verified (root_proved), first tracked attempt
  preverification     7e1ced97-88a9-45c0-9be2-dc5e1198b4ad (kernel_pass)
  import manifest     ["Mathlib.Tactic.Ring", "Mathlib.Tactic.NormNum", "Mathlib"]

Content: the reusable interaction theorem of the cross-shift terminal-leaf
incompatibility program. For any two integer affine forms `L₁(N)=a·N+b`
and `L₂(N)=c·N+d`, every common divisor divides the determinant:

  `g ∣ a·N+b → g ∣ c·N+d → g ∣ a·d−c·b`

via `a·L₂(N) − c·L₁(N) = a·d−c·b`. This supersedes both the classical
special identity `gcd(n−a, n−b) ∣ (b−a)` and this campaign's earlier
`ca·N−1 / cb·N−1` lemma: it handles equal coefficients, different
coefficients, and re-parameterized branch forms (e.g. the shift-16
residual leaves `630Q+433`, `630R+59` under `N=32Q+22`, `N=64R+6`)
uniformly.

Downstream classification of every leaf-form pair by `Δ = a·d−c·b`:
- `Δ = 0`: proportional forms — the highest-value case (coincidence, one
  form dividing another, prime-versus-composite contradictions,
  incompatible divisor-count shapes). The catalog run on 2026-07-16
  (`dossiers/tools/det_catalog.py`) correctly rediscovered the built-in
  proportionalities `315N−2 = 16·(630Q+433) = 32·(630R+59)` on the two
  shift-16 residual branches.
- `|Δ| = 1`: values automatically coprime — pairs removable from
  collision search immediately.
- otherwise: every shared prime divides the fixed integer `Δ` — factor
  it, then compare its finitely many primes against the forced shapes
  and residue conditions. Combined with
  `erdos647_forced_factor_prime_bound` this turns each such pair into a
  finite case check.

Budget-agnostic pure algebra: serves the main declaration (excess `B=2`)
and the budget-parametric limit machinery identically.
-/

theorem erdos647_affine_determinant_interaction :
    ∀ (a b c d N g : ℤ), g ∣ a * N + b → g ∣ c * N + d → g ∣ a * d - c * b := by
  intro a b c d N g h1 h2
  have ha : g ∣ a * (c * N + d) := Dvd.dvd.mul_left h2 a
  have hc : g ∣ c * (a * N + b) := Dvd.dvd.mul_left h1 c
  have h3 : g ∣ a * (c * N + d) - c * (a * N + b) := dvd_sub ha hc
  have h4 : a * (c * N + d) - c * (a * N + b) = a * d - c * b := by ring
  rwa [h4] at h3
