import Mathlib

/-!
# Erdős #647 — Layer B FINAL ASSEMBLY: the explicit optimal Selberg sieve weight

Snapshot of the exact statement + proof term kernel-verified through the
tracked proof-search pipeline on 2026-07-14.

  problem_version_id  161abe8d-c256-487e-bfff-2181bdb326bb
  episode_id          366a66e4-d8e5-47a3-b7f9-cf629c7eb07b
  root_statement_hash ce9c35261868c4e231b2d8767761b2e0d3b1f9c4e5e44010abe4ac22954c5346
  outcome             kernel_verified (root_proved) — kernel_pass FIRST TRY via verification tool
  import manifest     ["Mathlib.Tactic.Ring", "Mathlib.Tactic.NormNum", "Mathlib"]

Content: **Layer B of the density-bound program is now complete.** For any
`s : SelbergSieve`, there exists a weight function `w : ℕ → ℝ` with
`w 1 = 1` (so `lambdaSquared w` is a valid upper-bound-sieve weight via
Mathlib's `upperMoebius_lambdaSquared`) such that

  `s.mainSum (lambdaSquared w) = 1 / (∑ l ∈ s.prodPrimes.divisors, s.selbergTerms l)`

— the classical Selberg optimal-weight value, matching the universal lower
bound `erdos647_selberg_engel_bound` proves for EVERY valid `w`. Together
these two theorems pin down the constrained minimum exactly (not just
bound it), and combined with Mathlib's
`siftedSum_le_mainSum_errSum_of_upperMoebius` this gives the Selberg sieve
upper bound `siftedSum ≤ totalMass/L + errSum(lambdaSquared w)` with
`L = ∑ selbergTerms(l)`, ready for Layer C's 7-tuple `BoundingSieve`
instantiation.

**Construction** (Möbius inversion): set the target
`y_l := μ(l)·selbergTerms(l)/L` for `l ∈ D := s.prodPrimes.divisors`, then
define `w(d) := (∑_{l':d∣l'∈D} μ(l'/d)·y(l')) / ν(d)`. The swap-and-reindex
Möbius inversion identity (`Erdos647_MoebiusSwapInversion.lean`, INLINED
here since cross-submission lemma referencing is not usable in this
environment) proves this `w` satisfies exactly the diagonalization
constraint `y_l = ∑_{d:l∣d} ν(d)·w(d)` that Mathlib's
`mainSum_lambdaSquared_eq_sum_mul_sum_sq` needs. Two direct consequences:
- At `l=1`: `y_1 = w(1)·ν(1) = w(1)` (since `ν(1)=1` via `IsMultiplicative`),
  and separately `y_1 = ∑_{l'∈D} μ(l')·y_{l'} = ∑_{l'} μ(l')²·selbergTerms(l')/L
  = ∑_{l'} selbergTerms(l')/L = L/L = 1` (using `μ(l')²=1` for squarefree
  `l'`, derived from `moebius_apply_of_squarefree : μ(n) = (-1)^cardFactors n`).
- Substituting the diagonalization into Mathlib's theorem:
  `mainSum(lambdaSquared w) = ∑_l (selbergTerms l)⁻¹·y_l² = ∑_l
  (selbergTerms l)⁻¹·μ(l)²·selbergTerms(l)²/L² = ∑_l selbergTerms(l)/L²
  = L/L² = 1/L`.

**First-try kernel_pass** on the full ~200-line submission — no debugging
rounds needed, since every component (the swap-inversion proof, the
moebius-squared-equals-one fact, the exact `SelbergSieve` field/lemma
names) had already been individually verified via prior diagnostic
submissions before assembly.
-/

theorem erdos647_selberg_optimal_weight :
    ∀ (s : SelbergSieve), ∃ w : ℕ → ℝ, w 1 = 1 ∧
      s.mainSum (BoundingSieve.lambdaSquared w) = 1 / (∑ l ∈ s.prodPrimes.divisors, s.selbergTerms l) := by
  intro s
  set D := s.prodPrimes.divisors with hD_def
  set L := ∑ l ∈ D, s.selbergTerms l with hL_def
  have h1mem : (1:ℕ) ∈ D := Nat.mem_divisors.mpr ⟨one_dvd _, s.prodPrimes_squarefree.ne_zero⟩
  have hLpos : 0 < L := Finset.sum_pos (fun l hl => s.selbergTerms_pos (Nat.dvd_of_mem_divisors hl)) ⟨1, h1mem⟩
  set y : ℕ → ℝ := fun l => if l ∈ D then (ArithmeticFunction.moebius l : ℝ) * s.selbergTerms l / L else 0 with hy_def
  have hmoebius_sq : ∀ l ∈ D, (ArithmeticFunction.moebius l : ℝ)^2 = 1 := by
    intro l hl
    have hsqfree : Squarefree l := BoundingSieve.squarefree_of_dvd_prodPrimes (Nat.dvd_of_mem_divisors hl)
    rw [ArithmeticFunction.moebius_apply_of_squarefree hsqfree]
    push_cast
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  have hswap : ∀ l ∈ D, (∑ d ∈ D, if l ∣ d then
        (∑ l' ∈ D, if d ∣ l' then (ArithmeticFunction.moebius (l'/d) : ℝ) * y l' else 0) else 0) = y l := by
    intro l hl
    have hmi : ∀ m : ℕ, 0 < m → ∑ e ∈ m.divisors, (ArithmeticFunction.moebius e : ℝ) = if m = 1 then 1 else 0 := by
      intro m hm
      have h1 : (ArithmeticFunction.moebius * ArithmeticFunction.zeta : ArithmeticFunction ℝ) m = ∑ i ∈ m.divisors, (ArithmeticFunction.moebius i : ℝ) := ArithmeticFunction.coe_mul_zeta_apply
      have h2 : (ArithmeticFunction.moebius * ArithmeticFunction.zeta : ArithmeticFunction ℝ) = 1 := ArithmeticFunction.coe_moebius_mul_coe_zeta
      rw [h2, ArithmeticFunction.one_apply] at h1
      exact h1.symm
    have hNpos : 0 < s.prodPrimes := s.prodPrimes_squarefree.ne_zero.bot_lt
    have hlpos : 0 < l := Nat.pos_of_mem_divisors hl
    have hldvdN : l ∣ s.prodPrimes := Nat.dvd_of_mem_divisors hl
    have hstep1 : (∑ d ∈ D, if l ∣ d then
          (∑ l' ∈ D, if d ∣ l' then (ArithmeticFunction.moebius (l'/d) : ℝ) * y l' else 0) else 0)
        = ∑ d ∈ D, ∑ l' ∈ D, (if l ∣ d ∧ d ∣ l' then (ArithmeticFunction.moebius (l'/d) : ℝ) * y l' else 0) := by
      apply Finset.sum_congr rfl
      intro d hd
      by_cases hld : l ∣ d
      · simp only [hld, if_true, true_and]
      · rw [if_neg hld]
        symm
        apply Finset.sum_eq_zero
        intro l' _
        exact if_neg (fun h => hld h.1)
    rw [hstep1, Finset.sum_comm]
    have hstep2 : ∑ l' ∈ D, ∑ d ∈ D, (if l ∣ d ∧ d ∣ l' then (ArithmeticFunction.moebius (l'/d) : ℝ) * y l' else 0)
        = ∑ l' ∈ D, (if l' = l then y l' else 0) := by
      apply Finset.sum_congr rfl
      intro l' hl'
      have hl'pos : 0 < l' := Nat.pos_of_mem_divisors hl'
      have hl'dvdN : l' ∣ s.prodPrimes := Nat.dvd_of_mem_divisors hl'
      by_cases hll' : l ∣ l'
      · obtain ⟨m, hm⟩ := hll'
        have hmpos : 0 < m := by
          rcases Nat.eq_zero_or_pos m with h0 | h0
          · exfalso; rw [h0, mul_zero] at hm; omega
          · exact h0
        have hml' : m ∣ l' := ⟨l, by rw [hm]; ring⟩
        have hfilter_eq : D.filter (fun d => l ∣ d ∧ d ∣ l') = l'.divisors.filter (fun d => l ∣ d) := by
          ext d
          simp only [hD_def, Finset.mem_filter, Nat.mem_divisors]
          constructor
          · rintro ⟨⟨_, _⟩, hld, hdl'⟩
            exact ⟨⟨hdl', hl'pos.ne'⟩, hld⟩
          · rintro ⟨⟨hdl', _⟩, hld⟩
            exact ⟨⟨hdl'.trans hl'dvdN, s.prodPrimes_squarefree.ne_zero⟩, hld, hdl'⟩
        have hbij : ∑ d ∈ D, (if l ∣ d ∧ d ∣ l' then (ArithmeticFunction.moebius (l'/d) : ℝ) * y l' else 0)
            = ∑ e ∈ m.divisors, (ArithmeticFunction.moebius e : ℝ) * y l' := by
          rw [← Finset.sum_filter, hfilter_eq]
          apply Finset.sum_nbij' (fun x => l' / x) (fun x => l' / x)
          · intro d hd
            simp only [Finset.mem_filter, Nat.mem_divisors] at hd
            obtain ⟨⟨hdl', _⟩, hld⟩ := hd
            rw [Nat.mem_divisors]
            refine ⟨?_, hmpos.ne'⟩
            obtain ⟨e, he⟩ := hld
            have hde : d * (l' / d) = l' := Nat.mul_div_cancel' hdl'
            have heq1 : l * (e * (l' / d)) = l * m := by rw [← mul_assoc, ← he, hde, hm]
            have hem : e * (l' / d) = m := Nat.eq_of_mul_eq_mul_left hlpos heq1
            exact ⟨e, by rw [← hem]; ring⟩
          · intro e he
            simp only [Finset.mem_coe, Nat.mem_divisors] at he
            simp only [Finset.mem_filter, Nat.mem_divisors]
            obtain ⟨e', he'⟩ := he.1
            have hepos : 0 < e := Nat.pos_of_dvd_of_pos he.1 hmpos
            have hl'e : l' / e = l * e' := by
              have hl'eq : l' = (l * e') * e := by rw [hm, he']; ring
              rw [hl'eq, Nat.mul_div_cancel _ hepos]
            refine ⟨⟨⟨e, by rw [hl'e, hm, he']; ring⟩, hl'pos.ne'⟩, ⟨e', hl'e⟩⟩
          · intro d hd
            simp only [Finset.mem_filter, Nat.mem_divisors] at hd
            obtain ⟨⟨hdl', _⟩, _⟩ := hd
            have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdl' hl'pos
            have hde : (l' / d) * d = l' := Nat.div_mul_cancel hdl'
            have hddpos : 0 < l' / d := Nat.div_pos (Nat.le_of_dvd hl'pos hdl') hdpos
            nth_rewrite 1 [show l' = (l'/d) * d from hde.symm]
            exact Nat.mul_div_cancel_left d hddpos
          · intro e he
            simp only [Finset.mem_coe, Nat.mem_divisors] at he
            have hel' : e ∣ l' := he.1.trans hml'
            have hepos : 0 < e := Nat.pos_of_dvd_of_pos he.1 hmpos
            have hde : (l' / e) * e = l' := Nat.div_mul_cancel hel'
            have hdepos : 0 < l' / e := Nat.div_pos (Nat.le_of_dvd hl'pos hel') hepos
            nth_rewrite 1 [show l' = (l'/e) * e from hde.symm]
            exact Nat.mul_div_cancel_left e hdepos
          · intro d _
            rfl
        rw [hbij, ← Finset.sum_mul, hmi m hmpos]
        have hiff : m = 1 ↔ l' = l := by
          constructor
          · intro h1; rw [hm, h1, mul_one]
          · intro h2
            have heq2 : l * m = l * 1 := by rw [← hm, h2, mul_one]
            exact Nat.eq_of_mul_eq_mul_left hlpos heq2
        simp only [hiff]
        by_cases hcond : l' = l
        · simp [hcond]
        · simp [hcond]
      · have hzero : ∀ d ∈ D, (if l ∣ d ∧ d ∣ l' then (ArithmeticFunction.moebius (l'/d) : ℝ) * y l' else 0) = 0 := by
          intro d hd
          rw [if_neg]
          intro hc
          exact hll' (hc.1.trans hc.2)
        rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero, if_neg]
        intro heq
        exact hll' (heq ▸ dvd_refl l)
    rw [hstep2, Finset.sum_ite_eq' D l y]
    simp [hl]
  set w : ℕ → ℝ := fun d => if d ∈ D then
      (∑ l' ∈ D, if d ∣ l' then (ArithmeticFunction.moebius (l'/d) : ℝ) * y l' else 0) / s.nu d
    else 0 with hw_def
  have hinv : ∀ l ∈ D, (∑ d ∈ D, if l ∣ d then s.nu d * w d else 0) = y l := by
    intro l hl
    rw [← hswap l hl]
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hld : l ∣ d
    · simp only [hld, if_true]
      rw [hw_def]
      simp only [hd, if_true]
      rw [mul_div_cancel₀]
      exact s.nu_ne_zero (Nat.dvd_of_mem_divisors hd)
    · simp [hld]
  refine ⟨w, ?_, ?_⟩
  · have hw1 : w 1 = (∑ l' ∈ D, if (1:ℕ) ∣ l' then (ArithmeticFunction.moebius (l'/1) : ℝ) * y l' else 0) / s.nu 1 := by
      rw [hw_def]; simp [h1mem]
    rw [hw1, s.nu_mult.map_one]
    have hsum1 : (∑ l' ∈ D, if (1:ℕ) ∣ l' then (ArithmeticFunction.moebius (l'/1) : ℝ) * y l' else 0) = 1 := by
      have heq : ∀ l' ∈ D, (if (1:ℕ) ∣ l' then (ArithmeticFunction.moebius (l'/1) : ℝ) * y l' else 0) = s.selbergTerms l' / L := by
        intro l' hl'
        simp only [one_dvd, if_true, Nat.div_one]
        rw [hy_def]
        simp only [hl', if_true]
        have hsq := hmoebius_sq l' hl'
        have hTpos := s.selbergTerms_pos (Nat.dvd_of_mem_divisors hl')
        field_simp
        nlinarith [hsq]
      rw [Finset.sum_congr rfl heq, ← Finset.sum_div, ← hL_def, div_self hLpos.ne']
    rw [hsum1]; norm_num
  · rw [s.mainSum_lambdaSquared_eq_sum_mul_sum_sq w]
    have hstep : ∀ l ∈ D, (s.selbergTerms l)⁻¹ * (∑ d ∈ D, if l ∣ d then s.nu d * w d else 0)^2
        = s.selbergTerms l / L^2 := by
      intro l hl
      rw [hinv l hl, hy_def]
      simp only [hl, if_true]
      have hsq := hmoebius_sq l hl
      have hTpos := s.selbergTerms_pos (Nat.dvd_of_mem_divisors hl)
      field_simp
      nlinarith [hsq, hTpos]
    rw [Finset.sum_congr rfl hstep, ← Finset.sum_div, ← hL_def]
    rw [pow_two, ← div_div, div_self hLpos.ne', one_div]
