import Mathlib

/-!
# Erdős #647 — Layer B: Möbius-sum-collapses-to-indicator building block

Snapshot of the exact statement + proof term kernel-verified through the
tracked proof-search pipeline on 2026-07-14.

  problem_version_id  99010870-f187-4d38-972e-bce821947ed4
  episode_id          63162d7e-a7d9-4806-aa62-eccafc281a3b
  root_statement_hash aed75a2efa87b2cba64f0718c4f2e90f128c28848ee90bb079bc60ab5fe5fc33
  outcome             kernel_verified (root_proved)
  import manifest     ["Mathlib.Tactic.Ring", "Mathlib.Tactic.NormNum", "Mathlib"]

Content: the classical fact `∑_{d∣m} μ(d) = [m=1]` for `m > 0`, derived
from Mathlib's Dirichlet-convolution identity `μ * ζ = 1`
(`ArithmeticFunction.coe_moebius_mul_coe_zeta`) applied at `m`, unfolded via
`ArithmeticFunction.coe_mul_zeta_apply : (f * ζ) x = ∑ i ∈ divisors x, f i`.
Much cleaner than manually reindexing over `divisorsAntidiagonal` (the
first attempt tried that route and hit missing-lemma-name errors — pivoting
to the `coe_mul_zeta_apply` unfold was a one-shot fix).

This is the core collapse step needed for the Möbius-inversion argument
constructing the explicit optimal Selberg sieve weight function: proving
`∑_{d: l∣d∈D} F(d) = y_l` where `F(d) := ∑_{l': d∣l'∈D} μ(l'/d)·y_l'`
requires, after swapping summation order and reindexing `d = l·e` with
`e ∣ (l'/l)`, exactly this fact applied to `m = l'/l`.
-/

theorem erdos647_moebius_sum_indicator :
    ∀ m : ℕ, 0 < m → ∑ e ∈ m.divisors, (ArithmeticFunction.moebius e : ℝ) = if m = 1 then 1 else 0 := by
  intro m hm
  have h1 : (ArithmeticFunction.moebius * ArithmeticFunction.zeta : ArithmeticFunction ℝ) m = ∑ i ∈ m.divisors, (ArithmeticFunction.moebius i : ℝ) := ArithmeticFunction.coe_mul_zeta_apply
  have h2 : (ArithmeticFunction.moebius * ArithmeticFunction.zeta : ArithmeticFunction ℝ) = 1 := ArithmeticFunction.coe_moebius_mul_coe_zeta
  rw [h2, ArithmeticFunction.one_apply] at h1
  exact h1.symm
