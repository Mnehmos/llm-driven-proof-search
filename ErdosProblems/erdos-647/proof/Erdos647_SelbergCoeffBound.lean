import Mathlib

/-!
# Erdős #647 — Layer C errSum repair: uniform coefficient bound C₀=4

Snapshot of the exact statement + proof term kernel-verified through the
tracked proof-search pipeline on 2026-07-14.

  problem_version_id  377cbc55-1afc-4842-9060-a6148429b2a5
  episode_id          e03eefc8-89d5-4242-9116-eaa08e60d3a4
  root_statement_hash 0c0686f3d797a73ab2577441a399fc177c0fc8a4bf385351723dbfdfcaa53c7e
  outcome             kernel_verified (root_proved)
  import manifest     ["Mathlib.Tactic.Ring", "Mathlib.Tactic.NormNum", "Mathlib"]

Content: Milestone C of the errSum repair plan — a uniform bound on the
per-prime Selberg factor for OUR own concrete `ν`, at every admissible
prime `p∉{3,5,7}`:

  `1 + (1-ν(p))⁻¹ ≤ 4`

This is the coefficient bound needed for the error-term estimate
`|lambdaSquared(w)(d)|·|rem(d)| ≤ 4^{2ω(d)}·7^{ω(d)} = 112^{ω(d)}`
(combining this with `erdos647_rootUnionCount_le`'s `rootUnionCount(d)≤
7^ω(d)`), regardless of which repair route for the errSum defect is
ultimately used (level-truncated weight support restriction, or a
sharper signed-structure bound) — this coefficient bound is needed
either way.

**Turned out simpler than initially planned**: the naive approach would
case-split `p=2 ∨ p=11 ∨ p>7∧p≠11`, needing the EXACT value `ν(11)=6/11`.
Instead, since `x↦1+(1-x)⁻¹` is increasing in `x`, and `ν(p)≤7/p`
UNIFORMLY for every prime `p>7` (from `erdos647_seventuple_admissible_
general`'s upper-bound direction only — the `≤7` root-union-count
bound, inlined here; the existence/lower-bound `≥1` direction is not
needed for THIS theorem), and any prime `p>7` automatically satisfies
`p≥11` (since 11 is the smallest prime exceeding 7), we get uniformly
`ν(p)≤7/p≤7/11<2/3` for ALL admissible primes `p>7` — no need to single
out `p=11` at all. This gives `1+(1-ν(p))⁻¹ ≤ 1+(1-7/11)⁻¹ = 15/4 ≤ 4`
with margin. The `p=2` case is separate and easy (`ν(2)=1/2` via a
direct `native_decide` count, giving factor exactly `3`).

Two Lean fixes: `div_le_div_iff` doesn't resolve (needs the `₀`-suffixed
`div_le_div_iff₀`, matching this campaign's established convention for
positivity-side-condition division lemmas); and the final algebraic
step needed restructuring — `rw [div_le_iff₀ hxpos] at *` doesn't work
when the goal isn't ALREADY in the exact `a/b≤c` shape (the goal was
`1 + 1/(1-ν(p))≤4`, not `1/(1-ν(p))≤3`), fixed by first isolating a
`have hfinal : 1/(1-ν(p)) ≤ 3` (proven via `div_le_iff₀` cleanly on its
own goal) and closing the original goal with `linarith [hfinal]`.
-/

theorem erdos647_selberg_coeff_bound :
    ∀ p, p.Prime → p ≠ 3 → p ≠ 5 → p ≠ 7 →
      1 + (1 - (ArithmeticFunction.prodPrimeFactors (fun q : ℕ => (((Finset.range q).filter (fun r => (210*r)%q=1 ∨ (315*r)%q=1 ∨ (420*r)%q=1 ∨ (630*r)%q=1 ∨ (840*r)%q=1 ∨ (1260*r)%q=1 ∨ (2520*r)%q=1)).card : ℝ) / q) : ArithmeticFunction ℝ) p)⁻¹ ≤ 4 := by
  intro p hp hp3 hp5 hp7
  have hpne0 : p ≠ 0 := hp.pos.ne'
  rw [ArithmeticFunction.prodPrimeFactors_apply hpne0, hp.primeFactors, Finset.prod_singleton]
  set cnt := ((Finset.range p).filter (fun r => (210*r)%p=1 ∨ (315*r)%p=1 ∨ (420*r)%p=1 ∨ (630*r)%p=1 ∨ (840*r)%p=1 ∨ (1260*r)%p=1 ∨ (2520*r)%p=1)).card with hcnt
  have hppos : (0:ℝ) < p := by exact_mod_cast hp.pos
  have h2le7 : p = 2 ∨ 7 < p := by
    rcases eq_or_ne p 2 with h2 | h2
    · left; exact h2
    · right
      by_contra hle
      push_neg at hle
      have h2le : 2 ≤ p := hp.two_le
      interval_cases p <;> first | (exfalso; omega) | (exfalso; norm_num at hp)
  rcases h2le7 with h2 | h7
  · subst h2
    have hval : cnt = 1 := by rw [hcnt]; native_decide
    rw [hval]
    norm_num
  · haveI : Fact p.Prime := ⟨hp⟩
    haveI : Fact (1 < p) := ⟨hp.one_lt⟩
    have hunique : ∀ (c : ℕ), ¬ p ∣ c → ∀ r1 r2, r1 < p → r2 < p → (c*r1)%p=1 → (c*r2)%p=1 → r1=r2 := by
      intro c hpc r1 r2 hr1 hr2 h1 h2
      have hcne : (c : ZMod p) ≠ 0 := by rwa [Ne, ZMod.natCast_eq_zero_iff]
      have e1 : ((c*r1 : ℕ) : ZMod p) = 1 := by
        have hh := congrArg (Nat.cast (R := ZMod p)) h1
        rw [ZMod.natCast_mod] at hh
        simpa using hh
      have e2 : ((c*r2 : ℕ) : ZMod p) = 1 := by
        have hh := congrArg (Nat.cast (R := ZMod p)) h2
        rw [ZMod.natCast_mod] at hh
        simpa using hh
      have e3 : (c:ZMod p) * (r1:ZMod p) = (c:ZMod p) * (r2:ZMod p) := by
        push_cast at e1 e2
        rw [e1, e2]
      have e4 : (r1 : ZMod p) = (r2 : ZMod p) := mul_left_cancel₀ hcne e3
      have e5 := congrArg ZMod.val e4
      rwa [ZMod.val_cast_of_lt hr1, ZMod.val_cast_of_lt hr2] at e5
    have hnd : ∀ c ∈ ([210,315,420,630,840,1260,2520] : List ℕ), ¬ p ∣ c := by
      intro c hc hpdvd
      have hcdvd : c ∣ 2520 := by fin_cases hc <;> norm_num
      have hpdvd2520 : p ∣ 2520 := hpdvd.trans hcdvd
      have hpmem : p ∈ Nat.primeFactors 2520 := Nat.mem_primeFactors.mpr ⟨hp, hpdvd2520, by norm_num⟩
      have hpf : Nat.primeFactors 2520 = {2,3,5,7} := by native_decide
      rw [hpf] at hpmem
      fin_cases hpmem <;> omega
    have hcard1 : ∀ c ∈ ([210,315,420,630,840,1260,2520] : List ℕ), ((Finset.range p).filter (fun r => (c*r)%p=1)).card ≤ 1 := by
      intro c hc
      rw [Finset.card_le_one]
      intro r1 hr1 r2 hr2
      simp only [Finset.mem_filter, Finset.mem_range] at hr1 hr2
      exact hunique c (hnd c hc) r1 r2 hr1.1 hr2.1 hr1.2 hr2.2
    set S210 := (Finset.range p).filter (fun r => (210*r)%p=1) with hS210
    set S315 := (Finset.range p).filter (fun r => (315*r)%p=1) with hS315
    set S420 := (Finset.range p).filter (fun r => (420*r)%p=1) with hS420
    set S630 := (Finset.range p).filter (fun r => (630*r)%p=1) with hS630
    set S840 := (Finset.range p).filter (fun r => (840*r)%p=1) with hS840
    set S1260 := (Finset.range p).filter (fun r => (1260*r)%p=1) with hS1260
    set S2520 := (Finset.range p).filter (fun r => (2520*r)%p=1) with hS2520
    have hSeq : cnt = (S210 ∪ S315 ∪ S420 ∪ S630 ∪ S840 ∪ S1260 ∪ S2520).card := by
      rw [hcnt]
      congr 1
      ext r
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union, hS210, hS315, hS420, hS630, hS840, hS1260, hS2520]
      tauto
    have hle7 : cnt ≤ 7 := by
      rw [hSeq]
      calc (S210 ∪ S315 ∪ S420 ∪ S630 ∪ S840 ∪ S1260 ∪ S2520).card
          ≤ S210.card + S315.card + S420.card + S630.card + S840.card + S1260.card + S2520.card := by
            apply le_trans (Finset.card_union_le _ _)
            gcongr
            apply le_trans (Finset.card_union_le _ _)
            gcongr
            apply le_trans (Finset.card_union_le _ _)
            gcongr
            apply le_trans (Finset.card_union_le _ _)
            gcongr
            apply le_trans (Finset.card_union_le _ _)
            gcongr
            exact Finset.card_union_le _ _
        _ ≤ 1+1+1+1+1+1+1 := by
            gcongr <;> [exact hcard1 210 (by simp); exact hcard1 315 (by simp); exact hcard1 420 (by simp); exact hcard1 630 (by simp); exact hcard1 840 (by simp); exact hcard1 1260 (by simp); exact hcard1 2520 (by simp)]
        _ = 7 := by norm_num
    have hcntR : (cnt:ℝ) ≤ 7 := by exact_mod_cast hle7
    have hcnt_nonneg : (0:ℝ) ≤ (cnt:ℝ) := by positivity
    have hp11 : (11:ℝ) ≤ (p:ℝ) := by
      have h11 : 11 ≤ p := by
        by_contra hlt
        push_neg at hlt
        interval_cases p <;> first | (exfalso; omega) | (exfalso; norm_num at hp)
      exact_mod_cast h11
    have hnu_le : (cnt:ℝ)/p ≤ 7/11 := by
      rw [div_le_div_iff₀ hppos (by norm_num : (0:ℝ) < 11)]
      nlinarith [hcntR, hp11, hcnt_nonneg]
    have hxpos : (0:ℝ) < 1 - (cnt:ℝ)/p := by linarith
    rw [show (1-(cnt:ℝ)/p)⁻¹ = 1/(1-(cnt:ℝ)/p) from (one_div _).symm]
    have hfinal : 1/(1 - (cnt:ℝ)/p) ≤ 3 := by
      rw [div_le_iff₀ hxpos]
      nlinarith [hnu_le]
    linarith [hfinal]
