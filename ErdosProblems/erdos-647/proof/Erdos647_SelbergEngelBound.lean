import Mathlib

/-!
# Erdős #647 — Layer B: Selberg optimization, constrained Cauchy-Schwarz core

Snapshot of the exact statement + proof term kernel-verified through the
tracked proof-search pipeline on 2026-07-14.

  problem_version_id  955843bb-83a6-4247-9770-1ac2d24fd4b5
  episode_id          681dda79-46c0-4b93-898c-c2fbe10f06a4
  root_statement_hash fce6db96bc65d32be0656c3f0436dfbf7602ed899b5a39c2aa2d0035fa067b1e
  outcome             kernel_verified (root_proved)
  import manifest     ["Mathlib.Tactic.Ring", "Mathlib.Tactic.NormNum", "Mathlib"]

Content: the abstract algebraic core of the classical Selberg sieve
optimal-weight bound — Sedrakyan's lemma (Titu's / Engel's form of
Cauchy-Schwarz, already in Mathlib as `Finset.sq_sum_div_le_sum_sq_div`)
specialized to a ±1-valued sign sequence. For a finite index set with
positive weights `g`, a sign sequence `μ` (μ_i² = 1), and reals `y` with
`∑ μ_i·y_i = 1`, the quadratic form `∑ y_i²/g_i` is bounded below by
`1/∑ g_i`.

Applied to Mathlib's `SelbergSieve.mainSum_lambdaSquared_eq_sum_mul_sum_sq`
diagonalization (`mainSum (lambdaSquared w) = ∑_l (selbergTerms l)⁻¹ · y_l²`
with `y_l = ∑_{d: l∣d} ν(d)·w(d)`), taking `g = selbergTerms`, `μ` = the
Möbius function on divisors of `prodPrimes` (μ_l² = 1 since l is
squarefree), this gives the universal lower bound
`1/∑ selbergTerms(l) ≤ mainSum(lambdaSquared w)` for every weight function
`w` with `w 1 = 1` — the constraint `∑ μ(l)·y_l = 1` follows from Möbius
inversion (`ν.IsMultiplicative` gives `ν 1 = 1`, plus the Möbius indicator
identity `ArithmeticFunction.coe_moebius_mul_coe_zeta : μ * ζ = 1`).

**Correction to attack-plan.md's earlier note:** the constrained minimum
is `1/∑ selbergTerms(l)`, NOT `1/∑ (selbergTerms l)⁻¹` (the reciprocal
placement in the earlier plan was backwards — verified against the actual
Mathlib diagonalization theorem's coefficient, `(selbergTerms l)⁻¹`, not
`selbergTerms l`, on the `y_l²` term).

Remaining for Layer B: this lemma gives a universal LOWER bound (holds for
every valid `w`), which alone doesn't bound `siftedSum` from above. The
harder remaining piece is exhibiting the EXPLICIT optimal `w` — Möbius-
inverting `y_l = μ(l)·selbergTerms(l)/∑selbergTerms` back to a weight
function `w` — that achieves equality, which is what the sieve upper-bound
application (Layer C) actually needs.
-/

theorem erdos647_selberg_engel_bound :
    ∀ {ι : Type} (s : Finset ι) (g μ y : ι → ℝ), (∀ i ∈ s, 0 < g i) → (∀ i ∈ s, μ i ^ 2 = 1) →
      (∑ i ∈ s, μ i * y i) = 1 → 1 / (∑ i ∈ s, g i) ≤ ∑ i ∈ s, y i ^ 2 / g i := by
  intro ι s g μ y hg hμ hsum
  have hcs := Finset.sq_sum_div_le_sum_sq_div s (fun i => μ i * y i) hg
  rw [hsum] at hcs
  simp only [one_pow] at hcs
  have heq : ∀ i ∈ s, (μ i * y i)^2 / g i = y i ^2 / g i := by
    intro i hi
    have h1 : (μ i)^2 = 1 := hμ i hi
    have h2 : (μ i * y i)^2 = (μ i)^2 * y i ^2 := by ring
    rw [h2, h1, one_mul]
  rw [Finset.sum_congr rfl heq] at hcs
  linarith [hcs]
