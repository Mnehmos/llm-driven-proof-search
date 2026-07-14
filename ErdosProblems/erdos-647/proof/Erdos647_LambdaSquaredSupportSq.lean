import Mathlib

/-!
# Erdős #647 — Layer C errSum repair: generic support lemma for level-truncated λ²

Snapshot of the exact statement + proof term kernel-verified through the
tracked proof-search pipeline on 2026-07-14.

  problem_version_id  271ee635-46fc-4c1f-b132-e7ee9324a69f
  episode_id          144d069e-ac94-4e1b-af35-792117a07a43
  root_statement_hash fb2fd0c5dbf934219efaec5330a7413092a8df0ee1270d8cb7b18a8083a74fe3
  outcome             kernel_verified (root_proved)
  import manifest     ["Mathlib.Tactic.Ring", "Mathlib.Tactic.NormNum", "Mathlib"]

Content: the KEY mechanism that repairs the critical errSum-bound defect
diagnosed this session (Mathlib's `SelbergSieve.level` field is declared
but never actually used anywhere in the library to truncate
`lambdaSquared`'s support, so the crude unrestricted error bound is
plausibly exponential in `π(z)`, reproducing the "Legendre explosion"
already ruled out for a cruder shortcut).

  `(∀ d, R < d → w d = 0) → ∀ d, R*R < d → lambdaSquared(w)(d) = 0`

I.e. if a weight `w` vanishes for all arguments exceeding a truncation
level `R`, then `lambdaSquared(w)` automatically vanishes for all
arguments exceeding `R²` — converting a divisor-sum errSum bound over
ALL divisors of `prodPrimes(z)` (up to `2^π(z)` many) into a bound over
plain integers `d≤R²` (summable by ordinary elementary divisor-counting
estimates, no exponential blowup).

Proof: unfold `lambdaSquared(w)(d) = ∑_{d1∣d}∑_{d2∣d} if d=lcm(d1,d2)
then w(d1)*w(d2) else 0`. In the `d=lcm(d1,d2)` branch, if both `d1≤R`
and `d2≤R`, then (since `lcm(d1,d2) ∣ d1*d2`, via `Nat.lcm_dvd_mul`, and
`d1*d2>0` since `d1,d2∣d` with `d≠0` forces `d1,d2>0`, via
`Nat.pos_of_mem_divisors`) `d = lcm(d1,d2) ≤ d1*d2 ≤ R*R`, contradicting
`R*R<d`. So at least one of `d1>R`/`d2>R` holds, zeroing the
corresponding factor `w(d1)`/`w(d2)`, hence the whole term. Fully
GENERIC — works for ANY weight `w` with the stated vanishing property,
not tied to any specific Selberg-optimal construction — so it is the
reusable, problem-independent core of Milestone A in the level-
truncated-weight repair plan (the remaining pieces — actually
constructing a truncated optimal weight `w_R` via a restricted-divisor-
set Möbius inversion, `w_R(1)=1`, `mainSum(lambdaSquared w_R)=1/L_R` —
are the harder, construction-specific parts still to be done). No Lean
bugs beyond one expected fix (an initial attempt tried to derive
`d1,d2≠0` from a nonexistent `Finset.mem_range` fact on `Nat.divisors`
membership; fixed with `Nat.pos_of_mem_divisors`, the correct lemma for
this exact situation).
-/

theorem erdos647_lambdaSquared_support_sq :
    ∀ (w : ℕ → ℝ) (R : ℕ), (∀ d, R < d → w d = 0) → ∀ d, R*R < d → BoundingSieve.lambdaSquared w d = 0 := by
  intro w R hw d hd
  unfold BoundingSieve.lambdaSquared
  apply Finset.sum_eq_zero
  intro d1 hd1
  apply Finset.sum_eq_zero
  intro d2 hd2
  split_ifs with hlcm
  · by_cases h1 : R < d1
    · rw [hw d1 h1, zero_mul]
    · by_cases h2 : R < d2
      · rw [hw d2 h2, mul_zero]
      · exfalso
        push_neg at h1 h2
        have hd1pos : 0 < d1 := Nat.pos_of_mem_divisors hd1
        have hd2pos : 0 < d2 := Nat.pos_of_mem_divisors hd2
        have hle : Nat.lcm d1 d2 ≤ d1 * d2 := Nat.le_of_dvd (Nat.mul_pos hd1pos hd2pos) (Nat.lcm_dvd_mul d1 d2)
        rw [hlcm] at hd
        have hprod_le : d1 * d2 ≤ R * R := Nat.mul_le_mul h1 h2
        omega
  · rfl
