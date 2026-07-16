import Mathlib

/-!
# Erdős #647 — the positive-lane bridge: √-prefix verification certifies candidacy

Snapshot of the exact statement + proof term kernel-verified through the
tracked proof-search pipeline on 2026-07-16.

  problem_version_id  3d88561c-a86c-4d0e-a5a3-7f6d6e457d4a
  episode_id          c0f03882-7215-4801-a990-442aa0ee1faf
  root_statement_hash aa3eb9bd51d1404b294cc0f22ccd6a143e54fba6a2d9990874a4211fb0317bfb
  outcome             kernel_verified (root_proved), first tracked attempt
  preverification     2edb2919-3e63-49ff-8bd6-f2a4e49e0b17 (kernel_pass)
  import manifest     ["Mathlib.Tactic.Ring", "Mathlib.Tactic.NormNum", "Mathlib"]

Content: `candidate_of_sqrt_prefix`. Verifying the shift budgets
`σ₀(n−k) ≤ k+2` only on the square-root prefix `k < 2·√n` certifies the
FULL Erdős #647 candidate condition `max_{m<n}(m + τ(m)) ≤ n+2`, stated
in the Formal Conjectures supremum form (`⨆ m : Fin n`). Every shift
beyond the prefix is automatically safe, because there
`τ(n−k) ≤ 2·√(n−k) ≤ 2·√n ≤ k+2` (the divisor-pairing bound, inlined
verbatim from `Erdos647_DivisorSqrtDepthReduction.lean`); the `m = 0`
edge of the supremum uses `σ₀(0) = 0`, and each `0 < m < n` corresponds
to the shift `k = n−m`.

**Why this matters (positive lane, main declaration)**: a
computationally discovered √-prefix survivor `N` (with `n = 2520·N`,
from the running wheel search: 45 open residue classes mod 46189,
seven-form Miller–Rabin filter, full incremental prefix check) becomes a
SHORT formal closure of the main declaration —

  `erdos647_candidate_of_sqrt_prefix` + `native_decide` on the finite
  prefix ⟹ `∃ n > 24, (⨆ m : Fin n, m + σ₀ m) ≤ n + 2`.

The search decision procedure and the formal certificate are now the
same object; no additional theory is needed between a hit and a proof.
This also complements the negative lane: the theorem pins the exact
finite obligation (`k < 2·√n`) that any depth-sublinearity theorem must
contradict for large `n`.
-/

theorem erdos647_candidate_of_sqrt_prefix :
    ∀ n : ℕ, 0 < n →
      (∀ k : ℕ, 0 < k → k < n → k < 2 * Nat.sqrt n →
        ArithmeticFunction.sigma 0 (n - k) ≤ k + 2) →
      (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 := by
  intro n hn hpre
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hcard : ∀ x : ℕ, 0 < x → x.divisors.card ≤ 2 * Nat.sqrt x := by
    intro n hn
    let f : ℕ → ℕ × Bool := fun d =>
      if d ≤ Nat.sqrt n then (d - 1, false) else (n / d - 1, true)
    let target : Finset (ℕ × Bool) :=
      (Finset.range (Nat.sqrt n)).product (Finset.univ : Finset Bool)
    have hmaps : Set.MapsTo f (n.divisors : Set ℕ) (target : Set (ℕ × Bool)) := by
      intro d hd
      have hdmem : d ∈ n.divisors := hd
      have hdpos : 0 < d := Nat.pos_of_mem_divisors hdmem
      have hddvd : d ∣ n := Nat.dvd_of_mem_divisors hdmem
      by_cases hsmall : d ≤ Nat.sqrt n
      · simp [f, target, hsmall]
        omega
      · have hmul : d * (n / d) = n := Nat.mul_div_cancel' hddvd
        have hpair := Nat.le_sqrt_of_eq_mul hmul.symm
        have hquot : n / d ≤ Nat.sqrt n := by
          rcases hpair with hd | hq
          · exact False.elim (hsmall hd)
          · exact hq
        have hqpos : 0 < n / d :=
          Nat.div_pos (Nat.le_of_dvd hn hddvd) hdpos
        simp [f, target, hsmall]
        omega
    have hinj : Set.InjOn f (n.divisors : Set ℕ) := by
      intro a ha b hb hab
      have hamem : a ∈ n.divisors := ha
      have hbmem : b ∈ n.divisors := hb
      have hapos : 0 < a := Nat.pos_of_mem_divisors hamem
      have hbpos : 0 < b := Nat.pos_of_mem_divisors hbmem
      have hadvd : a ∣ n := Nat.dvd_of_mem_divisors hamem
      have hbdvd : b ∣ n := Nat.dvd_of_mem_divisors hbmem
      by_cases haS : a ≤ Nat.sqrt n
      · by_cases hbS : b ≤ Nat.sqrt n
        · simp [f, haS, hbS] at hab
          omega
        · simp [f, haS, hbS] at hab
      · by_cases hbS : b ≤ Nat.sqrt n
        · simp [f, haS, hbS] at hab
        · have haqpos : 0 < n / a :=
            Nat.div_pos (Nat.le_of_dvd hn hadvd) hapos
          have hbqpos : 0 < n / b :=
            Nat.div_pos (Nat.le_of_dvd hn hbdvd) hbpos
          have hq : n / a = n / b := by
            simp [f, haS, hbS] at hab
            omega
          have hmula : a * (n / a) = n := Nat.mul_div_cancel' hadvd
          have hmulb : b * (n / b) = n := Nat.mul_div_cancel' hbdvd
          have hmuleq : a * (n / a) = b * (n / a) := by
            rw [hmula, hq, hmulb]
          exact Nat.eq_of_mul_eq_mul_right haqpos hmuleq
    have hcard := Finset.card_le_card_of_injOn f hmaps hinj
    dsimp [target] at hcard
    simpa [Finset.card_product, Nat.mul_comm] using hcard
  have hbudget : ∀ k : ℕ, 0 < k → k < n → ArithmeticFunction.sigma 0 (n - k) ≤ k + 2 := by
    intro k hk0 hkn
    by_cases hk : k < 2 * Nat.sqrt n
    · exact hpre k hk0 hkn hk
    · have hpos : 0 < n - k := by omega
      have hc := hcard (n - k) hpos
      have hsqrt : Nat.sqrt (n - k) ≤ Nat.sqrt n := Nat.sqrt_le_sqrt (Nat.sub_le n k)
      rw [ArithmeticFunction.sigma_zero_apply]
      omega
  apply ciSup_le
  intro m
  rcases Nat.eq_zero_or_pos (m : ℕ) with hm0 | hmpos
  · rw [hm0]
    simp
  · have hmn : (m : ℕ) < n := m.isLt
    have hk0 : 0 < n - (m : ℕ) := by omega
    have hkn : n - (m : ℕ) < n := by omega
    have hb := hbudget (n - (m : ℕ)) hk0 hkn
    have hmk : n - (n - (m : ℕ)) = (m : ℕ) := by omega
    rw [hmk] at hb
    omega
