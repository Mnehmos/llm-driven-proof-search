import Mathlib

/-!
# Erdős #647 — Layer B/C bridge: aggregate bound on the Selberg λ² weight

Snapshot of the exact statement + proof term kernel-verified through the
tracked proof-search pipeline on 2026-07-14.

  problem_version_id  07a91857-7ade-4719-867a-3836a04ed3ff
  episode_id          759515ed-b704-4f3d-8b2b-45689f8390b7
  root_statement_hash e1a335c630a6dcae767317fd77df12fb00588f6303488a7ddb3628618ce3e402
  outcome             kernel_verified (root_proved)
  import manifest     ["Mathlib.Tactic.Ring", "Mathlib.Tactic.NormNum", "Mathlib"]

Content: given a POINTWISE bound `|w(d1)| ≤ selbergTerms(d1)/ν(d1)` on
every divisor `d1` of `d` (exactly what `erdos647_selberg_weight_bound`
supplies for Layer B's optimal weight), this proves the AGGREGATE bound

  `|lambdaSquared(w)(d)| ≤ (∑_{d1∣d} selbergTerms(d1)/ν(d1))²`

Stated generically over any weight `w` satisfying the pointwise bound
(not tied to the specific optimal-weight formula), making it a clean,
reusable step independent of Layer B's exact construction.

Proof: triangle inequality twice (`Finset.abs_sum_le_sum_abs`, once for
the outer `d1`-sum, once for each inner `d2`-sum) to drop the
`lambdaSquared` definition's `if d=lcm d1 d2 then ... else 0` down to a
plain `|w(d1)|·|w(d2)|` bound (the `if`-branch case split handles both
the "true" branch via `abs_mul` and the "false" branch trivially via
`abs_zero` + `positivity`). The resulting double sum
`∑_{d1,d2∣d}|w(d1)||w(d2)|` factors via `Finset.sum_mul_sum` into
`(∑_{d1∣d}|w(d1)|)²`, then `pow_le_pow_left₀` (monotonicity of squaring
on nonnegative reals) lifts the pointwise sum bound to the squared form.

No Lean bugs — landed first try (all four lemma names —
`Finset.abs_sum_le_sum_abs`, `Finset.sum_mul_sum`, `pow_le_pow_left₀`,
`Nat.lcm`'s role in `BoundingSieve.lambdaSquared`'s `unfold`-able
definition — confirmed via `lean_declaration_lookup` before writing the
proof, following this campaign's established diagnostic-first workflow).
-/

theorem erdos647_lambdaSquared_bound :
    ∀ (s : SelbergSieve) (w : ℕ → ℝ) (d : ℕ), d ∈ s.prodPrimes.divisors →
      (∀ d1 ∈ d.divisors, |w d1| ≤ s.selbergTerms d1 / s.nu d1) →
      |BoundingSieve.lambdaSquared w d| ≤ (∑ d1 ∈ d.divisors, s.selbergTerms d1 / s.nu d1)^2 := by
  intro s w d hd hw
  have hstep : |BoundingSieve.lambdaSquared w d| ≤ ∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors, |w d1| * |w d2| := by
    unfold BoundingSieve.lambdaSquared
    calc |∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors, if d = Nat.lcm d1 d2 then w d1 * w d2 else 0|
        ≤ ∑ d1 ∈ d.divisors, |∑ d2 ∈ d.divisors, if d = Nat.lcm d1 d2 then w d1 * w d2 else 0| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors, |if d = Nat.lcm d1 d2 then w d1 * w d2 else 0| := by
          apply Finset.sum_le_sum
          intro d1 _
          exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors, |w d1| * |w d2| := by
          apply Finset.sum_le_sum
          intro d1 _
          apply Finset.sum_le_sum
          intro d2 _
          split_ifs with h
          · rw [abs_mul]
          · rw [abs_zero]; positivity
  have heq : (∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors, |w d1| * |w d2|) = (∑ d1 ∈ d.divisors, |w d1|) * (∑ d2 ∈ d.divisors, |w d2|) := by
    rw [Finset.sum_mul_sum]
  have hsum_le : (∑ d1 ∈ d.divisors, |w d1|) ≤ ∑ d1 ∈ d.divisors, s.selbergTerms d1 / s.nu d1 :=
    Finset.sum_le_sum hw
  have hsum_nonneg : 0 ≤ ∑ d1 ∈ d.divisors, |w d1| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  calc |BoundingSieve.lambdaSquared w d| ≤ ∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors, |w d1| * |w d2| := hstep
    _ = (∑ d1 ∈ d.divisors, |w d1|) * (∑ d2 ∈ d.divisors, |w d2|) := heq
    _ = (∑ d1 ∈ d.divisors, |w d1|)^2 := by rw [sq]
    _ ≤ (∑ d1 ∈ d.divisors, s.selbergTerms d1 / s.nu d1)^2 := pow_le_pow_left₀ hsum_nonneg hsum_le 2
