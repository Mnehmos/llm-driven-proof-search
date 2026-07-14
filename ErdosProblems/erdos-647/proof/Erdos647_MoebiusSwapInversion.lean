import Mathlib

/-!
# Erdős #647 — Layer B: the multiples-Möbius-inversion swap identity

Snapshot of the exact statement + proof term kernel-verified through the
tracked proof-search pipeline on 2026-07-14.

  problem_version_id  9d2564e5-74e1-4f3e-a6ff-2b36e62b6aee
  episode_id          eff7f736-3a7f-46af-8013-06f8c3d969fb
  root_statement_hash 3267162928b3aa56a525c7362d6bab9aa2a8173e6772bada6c6c3a85326b847f
  outcome             kernel_verified (root_proved)
  import manifest     ["Mathlib.Tactic.Ring", "Mathlib.Tactic.NormNum", "Mathlib"]

Content: the core Möbius-inversion identity for sums over MULTIPLES within
a fixed squarefree divisor lattice (dual to Mathlib's existing "sum over
divisors" inversion `sum_eq_iff_sum_smul_moebius_eq`, which doesn't
directly apply here). For `N` squarefree, `y : ℕ → ℝ`, and `l ∈ N.divisors`,
defining `F(d) := ∑_{l': d∣l'∈N.divisors} μ(l'/d)·y(l')` for each divisor
`d`, this proves `∑_{d: l∣d∈N.divisors} F(d) = y(l)` exactly.

This is the key step for constructing an EXPLICIT optimal Selberg sieve
weight function: it shows that defining `ν(d)·w(d) := F(d)` correctly
inverts the diagonalization constraint `y_l = ∑_{d:l∣d} ν(d)·w(d)` used in
Mathlib's `SelbergSieve.mainSum_lambdaSquared_eq_sum_mul_sum_sq`. Combined
with the target `y_l = μ(l)·selbergTerms(l)/∑selbergTerms` and the
universal lower bound `erdos647_selberg_engel_bound`, this lets one exhibit
the explicit weight achieving equality — the harder remaining half of
Layer B (the universal lower bound alone doesn't bound anything from above;
this gives the matching witness).

**Proof technique** (three debugging rounds via the verification tool, all
now resolved):
1. Merge the two nested `ite`s into one `l∣d ∧ d∣l'`, `Finset.sum_comm` to
   swap `d`/`l'` order, `Finset.sum_congr` per fixed `l'`.
2. For `l ∤ l'`: the whole inner sum is termwise 0 (`l∣d ∧ d∣l'` is
   unsatisfiable, since `l∣d∧d∣l' → l∣l'`).
3. For `l∣l'` (write `l' = l*m`): reduce the double-filtered index set
   `{d ∈ N.divisors : l∣d ∧ d∣l'}` to `l'.divisors.filter (l∣·)` via
   `divisors_filter_dvd_of_dvd`, then biject this with `m.divisors` using
   the SELF-INVERSE involution `x ↦ l'/x` (cleaner than the naive `d↦d/l`
   map, since `μ(l'/d)` then matches the target's `μ(e)` factor directly
   with no extra `m/e` reindexing needed) via `Finset.sum_nbij'`.
4. The inner sum collapses via `∑_{e∈m.divisors} μ(e) = [m=1]` (proved
   inline, same technique as `Erdos647_MoebiusIndicator.lean`), and
   `m=1 ↔ l'=l` (from `l'=l*m`, `l>0`, cancellation).
5. **Two recurring Lean pitfalls hit and fixed**: (a) a bare `simp only
   [hyp]` cannot rewrite an `ite` condition buried inside a `Finset.sum`
   binder — needed `Finset.sum_eq_zero` with a per-term `if_neg` instead;
   (b) the classic `rw`-self-capture bug (also seen in the Layer-A I3
   antiderivative proof): `rw [show l' = (l'/d)*d from ...]` on a goal
   `l'/(l'/d) = d` rewrites BOTH the outer `l'` and the `l'` hidden inside
   `l'/d`, causing infinite unfolding — fixed with `nth_rewrite 1` to
   target only the outer (first) occurrence.
-/

theorem erdos647_moebius_swap_inversion :
    ∀ (N : ℕ) (hN : Squarefree N) (y : ℕ → ℝ) (l : ℕ), l ∈ N.divisors →
      (∑ d ∈ N.divisors, if l ∣ d then
          (∑ l' ∈ N.divisors, if d ∣ l' then (ArithmeticFunction.moebius (l'/d) : ℝ) * y l' else 0)
        else 0) = y l := by
  intro N hN y l hl
  have hmi : ∀ m : ℕ, 0 < m → ∑ e ∈ m.divisors, (ArithmeticFunction.moebius e : ℝ) = if m = 1 then 1 else 0 := by
    intro m hm
    have h1 : (ArithmeticFunction.moebius * ArithmeticFunction.zeta : ArithmeticFunction ℝ) m = ∑ i ∈ m.divisors, (ArithmeticFunction.moebius i : ℝ) := ArithmeticFunction.coe_mul_zeta_apply
    have h2 : (ArithmeticFunction.moebius * ArithmeticFunction.zeta : ArithmeticFunction ℝ) = 1 := ArithmeticFunction.coe_moebius_mul_coe_zeta
    rw [h2, ArithmeticFunction.one_apply] at h1
    exact h1.symm
  have hNpos : 0 < N := hN.ne_zero.bot_lt
  have hlpos : 0 < l := Nat.pos_of_mem_divisors hl
  have hldvdN : l ∣ N := Nat.dvd_of_mem_divisors hl
  have hstep1 : (∑ d ∈ N.divisors, if l ∣ d then
        (∑ l' ∈ N.divisors, if d ∣ l' then (ArithmeticFunction.moebius (l'/d) : ℝ) * y l' else 0) else 0)
      = ∑ d ∈ N.divisors, ∑ l' ∈ N.divisors, (if l ∣ d ∧ d ∣ l' then (ArithmeticFunction.moebius (l'/d) : ℝ) * y l' else 0) := by
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
  have hstep2 : ∑ l' ∈ N.divisors, ∑ d ∈ N.divisors, (if l ∣ d ∧ d ∣ l' then (ArithmeticFunction.moebius (l'/d) : ℝ) * y l' else 0)
      = ∑ l' ∈ N.divisors, (if l' = l then y l' else 0) := by
    apply Finset.sum_congr rfl
    intro l' hl'
    have hl'pos : 0 < l' := Nat.pos_of_mem_divisors hl'
    have hl'dvdN : l' ∣ N := Nat.dvd_of_mem_divisors hl'
    by_cases hll' : l ∣ l'
    · obtain ⟨m, hm⟩ := hll'
      have hmpos : 0 < m := by
        rcases Nat.eq_zero_or_pos m with h0 | h0
        · exfalso; rw [h0, mul_zero] at hm; omega
        · exact h0
      have hml' : m ∣ l' := ⟨l, by rw [hm]; ring⟩
      have hfilter_eq : N.divisors.filter (fun d => l ∣ d ∧ d ∣ l') = l'.divisors.filter (fun d => l ∣ d) := by
        ext d
        simp only [Finset.mem_filter, Nat.mem_divisors]
        constructor
        · rintro ⟨⟨_, _⟩, hld, hdl'⟩
          exact ⟨⟨hdl', hl'pos.ne'⟩, hld⟩
        · rintro ⟨⟨hdl', _⟩, hld⟩
          exact ⟨⟨hdl'.trans hl'dvdN, hN.ne_zero⟩, hld, hdl'⟩
      have hbij : ∑ d ∈ N.divisors, (if l ∣ d ∧ d ∣ l' then (ArithmeticFunction.moebius (l'/d) : ℝ) * y l' else 0)
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
    · have hzero : ∀ d ∈ N.divisors, (if l ∣ d ∧ d ∣ l' then (ArithmeticFunction.moebius (l'/d) : ℝ) * y l' else 0) = 0 := by
        intro d hd
        rw [if_neg]
        intro hc
        exact hll' (hc.1.trans hc.2)
      rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero, if_neg]
      intro heq
      exact hll' (heq ▸ dvd_refl l)
  rw [hstep2, Finset.sum_ite_eq' N.divisors l y]
  simp [hl]
