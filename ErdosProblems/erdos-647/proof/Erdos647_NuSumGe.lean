import Mathlib

/-!
# Erdős #647 — Layer C growth-rate: Mertens-type lower bound on ∑ν(p)

Snapshot of the exact statement + proof term kernel-verified through the
tracked proof-search pipeline on 2026-07-14.

  problem_version_id  35d5cf81-bde2-4aab-9051-d573c4c4a5a3
  episode_id          58ba850c-d7ff-4096-9c17-343c73aabaf4
  root_statement_hash daba6bd200388daed7a1eb4ee4be28340d939db2b64eda7716e8c0c1462d63f1
  outcome             kernel_verified (root_proved)
  import manifest     ["Mathlib.Tactic.Ring", "Mathlib.Tactic.NormNum", "Mathlib"]

Content: for `z ≥ 11`, a lower bound on the sum of this campaign's own
`ν` over primes `≤z`:

  `7·∑_{p≤z,Prime} 1/p − 7·(1/2+1/3+1/5+1/7+1/11) ≤ ∑_{p≤z,Prime} ν(p)`

This is the FIRST input a Mertens-type growth-rate estimate for
`L=∏(1-ν(p))⁻¹ ~ (log z)^7` needs (combined with `erdos647_mertens_
assembly`'s lower bound on `∑_{p≤z,Prime}1/p` and the elementary
inequality `-log(1-x)≥x`).

Proof: split `S := (Finset.Icc 1 z).filter Nat.Prime` at the threshold
`p>11` (`Finset.sum_filter_add_sum_filter_not`, applied once to `ν` and
once to `1/p`). For `p∈S` with `p>11` (equivalently, since `p` is prime,
`p>7 ∧ p≠11` — there is no prime strictly between 7 and 11): `ν(p)=7/p`
exactly (`erdos647_nu_eq_seven_div_p`'s technique, inlined), giving
`∑_{p>11}ν(p) = 7·∑_{p>11}1/p` termwise. For the `p≤11` part: it's a
SUBSET of `{2,3,5,7,11}` (proved via `interval_cases p <;> revert hpprime
<;> decide` on the 11 candidates `1..11`), so its `1/p`-sum is bounded by
the explicit constant `1/2+1/3+1/5+1/7+1/11`
(`Finset.sum_le_sum_of_subset_of_nonneg`), and its `ν`-sum is simply
dropped as a valid weakening since `ν≥0` everywhere (`ν(p)` is a ratio of
two nonnegative naturals cast to `ℝ`).

**Two Lean fixes this round** (both process, not new math):
1. `rw [hnu_def]` (where `nu` is a `set`-bound local) left an un-beta-
   reduced `(fun p => VALUE) p` term, breaking a SUBSEQUENT `rw` that
   needed to see `VALUE` directly. Fixed by using `simp only [hnu_def]`
   instead — `simp` beta-reduces automatically, `rw` does not. `rw`
   also does NOT look inside a zeta-reducible `set`-bound local without
   an explicit unfold, unlike what might be assumed by analogy with
   defeq-checking elsewhere in this campaign.
2. Repeated `obtain` destructuring-pattern mismatches: after `simp only
   [Finset.mem_filter, Finset.mem_Icc, ...] at hp` on membership in a
   DOUBLY-filtered Finset (`S.filter Q` where `S` itself is `(Finset.Icc
   1 z).filter Nat.Prime`), the resulting hypothesis has shape
   `((1≤p∧p≤z)∧Prime p)∧Q p` (left-associated, 4 atomic facts nested
   3 levels deep) — NOT the flatter 3-or-4-way tuple shape an
   `⟨⟨_,_⟩,_,_⟩`-style pattern assumes. Fixed by matching the exact
   nesting explicitly: `⟨⟨⟨hp1,hpz⟩,hpprime⟩,hcond⟩`.
-/

theorem erdos647_nu_sum_ge_seven_mertens :
    ∀ z : ℕ, 11 ≤ z →
      7 * (∑ p ∈ (Finset.Icc 1 z).filter Nat.Prime, (1/(p:ℝ))) - 7*(1/2+1/3+1/5+1/7+1/11) ≤
      ∑ p ∈ (Finset.Icc 1 z).filter Nat.Prime, (ArithmeticFunction.prodPrimeFactors (fun q : ℕ => (((Finset.range q).filter (fun r => (210*r)%q=1 ∨ (315*r)%q=1 ∨ (420*r)%q=1 ∨ (630*r)%q=1 ∨ (840*r)%q=1 ∨ (1260*r)%q=1 ∨ (2520*r)%q=1)).card : ℝ) / q) : ArithmeticFunction ℝ) p := by
  intro z hz
  set nu : ℕ → ℝ := fun p => (ArithmeticFunction.prodPrimeFactors (fun q : ℕ => (((Finset.range q).filter (fun r => (210*r)%q=1 ∨ (315*r)%q=1 ∨ (420*r)%q=1 ∨ (630*r)%q=1 ∨ (840*r)%q=1 ∨ (1260*r)%q=1 ∨ (2520*r)%q=1)).card : ℝ) / q) : ArithmeticFunction ℝ) p with hnu_def
  set S := (Finset.Icc 1 z).filter Nat.Prime with hS_def
  have hnu_eq_seven : ∀ p, p.Prime → 7 < p → p ≠ 11 → nu p = 7 / p := by
    intro p hp hp7 hp11
    have hpne0 : p ≠ 0 := hp.pos.ne'
    simp only [hnu_def]
    rw [ArithmeticFunction.prodPrimeFactors_apply hpne0, hp.primeFactors, Finset.prod_singleton]
    have hcnt7 : ((Finset.range p).filter (fun r => (210*r)%p=1 ∨ (315*r)%p=1 ∨ (420*r)%p=1 ∨ (630*r)%p=1 ∨ (840*r)%p=1 ∨ (1260*r)%p=1 ∨ (2520*r)%p=1)).card = 7 := by
      haveI : Fact p.Prime := ⟨hp⟩
      haveI : Fact (1 < p) := ⟨hp.one_lt⟩
      have hexists : ∀ (c : ℕ), ¬ p ∣ c → ∃ r < p, (c * r) % p = 1 := by
        intro c hpc
        have hcne : (c : ZMod p) ≠ 0 := by rwa [Ne, ZMod.natCast_eq_zero_iff]
        refine ⟨((c:ZMod p)⁻¹).val, ZMod.val_lt _, ?_⟩
        have h1 : (c:ZMod p) * (c:ZMod p)⁻¹ = 1 := mul_inv_cancel₀ hcne
        have h2 : ((c * ((c:ZMod p)⁻¹).val : ℕ) : ZMod p) = 1 := by
          push_cast; rw [ZMod.natCast_val, ZMod.cast_id]; exact h1
        have h4 : (c * ((c:ZMod p)⁻¹).val) % p < p := Nat.mod_lt _ hp.pos
        have h3 : (((c * ((c:ZMod p)⁻¹).val) % p : ℕ) : ZMod p) = 1 := by rwa [ZMod.natCast_mod]
        have h6 := congrArg ZMod.val h3
        rw [ZMod.val_cast_of_lt h4, ZMod.val_one] at h6
        exact h6
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
      have hnodvd : ∀ d : ℕ, d ≠ 0 → d.primeFactors ⊆ ({2,3,5,7,11}:Finset ℕ) → ¬ p ∣ d := by
        intro d hd0 hsub hpdvd
        have hpmem : p ∈ d.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvd, hd0⟩
        have hp5 := hsub hpmem
        fin_cases hp5 <;> omega
      have hdisj_gen : ∀ c1 c2 : ℕ, c1 < c2 → ¬ p ∣ (c2 - c1) →
          Disjoint ((Finset.range p).filter (fun r => (c1*r)%p=1)) ((Finset.range p).filter (fun r => (c2*r)%p=1)) := by
        intro c1 c2 hlt hpdiff
        apply Finset.disjoint_left.mpr
        intro r hr1 hr2
        simp only [Finset.mem_filter, Finset.mem_range] at hr1 hr2
        apply hpdiff
        have e1 : (c1:ZMod p) * (r:ZMod p) = 1 := by
          have hh := congrArg (Nat.cast (R := ZMod p)) hr1.2
          rw [ZMod.natCast_mod] at hh; push_cast at hh; exact hh
        have e2 : (c2:ZMod p) * (r:ZMod p) = 1 := by
          have hh := congrArg (Nat.cast (R := ZMod p)) hr2.2
          rw [ZMod.natCast_mod] at hh; push_cast at hh; exact hh
        have hrne : (r:ZMod p) ≠ 0 := by
          intro hr0; rw [hr0, mul_zero] at e1; exact zero_ne_one e1
        have e4 : (c1 : ZMod p) = (c2 : ZMod p) := mul_right_cancel₀ hrne (e1.trans e2.symm)
        have hz2 : ((c2 - c1 : ℕ) : ZMod p) = 0 := by
          rw [Nat.cast_sub hlt.le, ← e4, sub_self]
        rwa [ZMod.natCast_eq_zero_iff] at hz2
      set S210 := (Finset.range p).filter (fun r => (210*r)%p=1) with hS210
      set S315 := (Finset.range p).filter (fun r => (315*r)%p=1) with hS315
      set S420 := (Finset.range p).filter (fun r => (420*r)%p=1) with hS420
      set S630 := (Finset.range p).filter (fun r => (630*r)%p=1) with hS630
      set S840 := (Finset.range p).filter (fun r => (840*r)%p=1) with hS840
      set S1260 := (Finset.range p).filter (fun r => (1260*r)%p=1) with hS1260
      set S2520 := (Finset.range p).filter (fun r => (2520*r)%p=1) with hS2520
      clear_value S210 S315 S420 S630 S840 S1260 S2520
      have hcard1 : ∀ c ∈ ([210,315,420,630,840,1260,2520] : List ℕ), ((Finset.range p).filter (fun r => (c*r)%p=1)).card = 1 := by
        intro c hc
        apply le_antisymm
        · rw [Finset.card_le_one]
          intro r1 hr1 r2 hr2
          simp only [Finset.mem_filter, Finset.mem_range] at hr1 hr2
          exact hunique c (hnd c hc) r1 r2 hr1.1 hr2.1 hr1.2 hr2.2
        · obtain ⟨r, hr, hr1⟩ := hexists c (hnd c hc)
          have hrmem : r ∈ (Finset.range p).filter (fun r => (c*r)%p=1) := by simp [hr, hr1]
          exact Finset.card_pos.mpr ⟨r, hrmem⟩
      have hS210c : S210.card = 1 := by rw [hS210]; exact hcard1 210 (by simp)
      have hS315c : S315.card = 1 := by rw [hS315]; exact hcard1 315 (by simp)
      have hS420c : S420.card = 1 := by rw [hS420]; exact hcard1 420 (by simp)
      have hS630c : S630.card = 1 := by rw [hS630]; exact hcard1 630 (by simp)
      have hS840c : S840.card = 1 := by rw [hS840]; exact hcard1 840 (by simp)
      have hS1260c : S1260.card = 1 := by rw [hS1260]; exact hcard1 1260 (by simp)
      have hS2520c : S2520.card = 1 := by rw [hS2520]; exact hcard1 2520 (by simp)
      have D12 : Disjoint S210 S315 := by rw [hS210, hS315]; exact hdisj_gen 210 315 (by norm_num) (hnodvd 105 (by norm_num) (by native_decide))
      have D13 : Disjoint S210 S420 := by rw [hS210, hS420]; exact hdisj_gen 210 420 (by norm_num) (hnodvd 210 (by norm_num) (by native_decide))
      have D14 : Disjoint S210 S630 := by rw [hS210, hS630]; exact hdisj_gen 210 630 (by norm_num) (hnodvd 420 (by norm_num) (by native_decide))
      have D15 : Disjoint S210 S840 := by rw [hS210, hS840]; exact hdisj_gen 210 840 (by norm_num) (hnodvd 630 (by norm_num) (by native_decide))
      have D16 : Disjoint S210 S1260 := by rw [hS210, hS1260]; exact hdisj_gen 210 1260 (by norm_num) (hnodvd 1050 (by norm_num) (by native_decide))
      have D17 : Disjoint S210 S2520 := by rw [hS210, hS2520]; exact hdisj_gen 210 2520 (by norm_num) (hnodvd 2310 (by norm_num) (by native_decide))
      have D23 : Disjoint S315 S420 := by rw [hS315, hS420]; exact hdisj_gen 315 420 (by norm_num) (hnodvd 105 (by norm_num) (by native_decide))
      have D24 : Disjoint S315 S630 := by rw [hS315, hS630]; exact hdisj_gen 315 630 (by norm_num) (hnodvd 315 (by norm_num) (by native_decide))
      have D25 : Disjoint S315 S840 := by rw [hS315, hS840]; exact hdisj_gen 315 840 (by norm_num) (hnodvd 525 (by norm_num) (by native_decide))
      have D26 : Disjoint S315 S1260 := by rw [hS315, hS1260]; exact hdisj_gen 315 1260 (by norm_num) (hnodvd 945 (by norm_num) (by native_decide))
      have D27 : Disjoint S315 S2520 := by rw [hS315, hS2520]; exact hdisj_gen 315 2520 (by norm_num) (hnodvd 2205 (by norm_num) (by native_decide))
      have D34 : Disjoint S420 S630 := by rw [hS420, hS630]; exact hdisj_gen 420 630 (by norm_num) (hnodvd 210 (by norm_num) (by native_decide))
      have D35 : Disjoint S420 S840 := by rw [hS420, hS840]; exact hdisj_gen 420 840 (by norm_num) (hnodvd 420 (by norm_num) (by native_decide))
      have D36 : Disjoint S420 S1260 := by rw [hS420, hS1260]; exact hdisj_gen 420 1260 (by norm_num) (hnodvd 840 (by norm_num) (by native_decide))
      have D37 : Disjoint S420 S2520 := by rw [hS420, hS2520]; exact hdisj_gen 420 2520 (by norm_num) (hnodvd 2100 (by norm_num) (by native_decide))
      have D45 : Disjoint S630 S840 := by rw [hS630, hS840]; exact hdisj_gen 630 840 (by norm_num) (hnodvd 210 (by norm_num) (by native_decide))
      have D46 : Disjoint S630 S1260 := by rw [hS630, hS1260]; exact hdisj_gen 630 1260 (by norm_num) (hnodvd 630 (by norm_num) (by native_decide))
      have D47 : Disjoint S630 S2520 := by rw [hS630, hS2520]; exact hdisj_gen 630 2520 (by norm_num) (hnodvd 1890 (by norm_num) (by native_decide))
      have D56 : Disjoint S840 S1260 := by rw [hS840, hS1260]; exact hdisj_gen 840 1260 (by norm_num) (hnodvd 420 (by norm_num) (by native_decide))
      have D57 : Disjoint S840 S2520 := by rw [hS840, hS2520]; exact hdisj_gen 840 2520 (by norm_num) (hnodvd 1680 (by norm_num) (by native_decide))
      have D67 : Disjoint S1260 S2520 := by rw [hS1260, hS2520]; exact hdisj_gen 1260 2520 (by norm_num) (hnodvd 1260 (by norm_num) (by native_decide))
      have P1_3 : Disjoint (S210∪S315) S420 := Finset.disjoint_union_left.mpr ⟨D13, D23⟩
      have P1_4 : Disjoint (S210∪S315) S630 := Finset.disjoint_union_left.mpr ⟨D14, D24⟩
      have P1_5 : Disjoint (S210∪S315) S840 := Finset.disjoint_union_left.mpr ⟨D15, D25⟩
      have P1_6 : Disjoint (S210∪S315) S1260 := Finset.disjoint_union_left.mpr ⟨D16, D26⟩
      have P1_7 : Disjoint (S210∪S315) S2520 := Finset.disjoint_union_left.mpr ⟨D17, D27⟩
      have P2_4 : Disjoint (S210∪S315∪S420) S630 := Finset.disjoint_union_left.mpr ⟨P1_4, D34⟩
      have P2_5 : Disjoint (S210∪S315∪S420) S840 := Finset.disjoint_union_left.mpr ⟨P1_5, D35⟩
      have P2_6 : Disjoint (S210∪S315∪S420) S1260 := Finset.disjoint_union_left.mpr ⟨P1_6, D36⟩
      have P2_7 : Disjoint (S210∪S315∪S420) S2520 := Finset.disjoint_union_left.mpr ⟨P1_7, D37⟩
      have P3_5 : Disjoint (S210∪S315∪S420∪S630) S840 := Finset.disjoint_union_left.mpr ⟨P2_5, D45⟩
      have P3_6 : Disjoint (S210∪S315∪S420∪S630) S1260 := Finset.disjoint_union_left.mpr ⟨P2_6, D46⟩
      have P3_7 : Disjoint (S210∪S315∪S420∪S630) S2520 := Finset.disjoint_union_left.mpr ⟨P2_7, D47⟩
      have P4_6 : Disjoint (S210∪S315∪S420∪S630∪S840) S1260 := Finset.disjoint_union_left.mpr ⟨P3_6, D56⟩
      have P4_7 : Disjoint (S210∪S315∪S420∪S630∪S840) S2520 := Finset.disjoint_union_left.mpr ⟨P3_7, D57⟩
      have P5_7 : Disjoint (S210∪S315∪S420∪S630∪S840∪S1260) S2520 := Finset.disjoint_union_left.mpr ⟨P4_7, D67⟩
      have hc2 : (S210∪S315).card = 2 := by rw [Finset.card_union_of_disjoint D12, hS210c, hS315c]
      have hc3 : (S210∪S315∪S420).card = 3 := by rw [Finset.card_union_of_disjoint P1_3, hc2, hS420c]
      have hc4 : (S210∪S315∪S420∪S630).card = 4 := by rw [Finset.card_union_of_disjoint P2_4, hc3, hS630c]
      have hc5 : (S210∪S315∪S420∪S630∪S840).card = 5 := by rw [Finset.card_union_of_disjoint P3_5, hc4, hS840c]
      have hc6 : (S210∪S315∪S420∪S630∪S840∪S1260).card = 6 := by rw [Finset.card_union_of_disjoint P4_6, hc5, hS1260c]
      have hc7 : (S210∪S315∪S420∪S630∪S840∪S1260∪S2520).card = 7 := by rw [Finset.card_union_of_disjoint P5_7, hc6, hS2520c]
      have hSeq : (Finset.range p).filter (fun r => (210*r)%p=1 ∨ (315*r)%p=1 ∨ (420*r)%p=1 ∨ (630*r)%p=1 ∨ (840*r)%p=1 ∨ (1260*r)%p=1 ∨ (2520*r)%p=1) = S210 ∪ S315 ∪ S420 ∪ S630 ∪ S840 ∪ S1260 ∪ S2520 := by
        ext r
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union, hS210, hS315, hS420, hS630, hS840, hS1260, hS2520]
        tauto
      rw [hSeq]
      exact hc7
    rw [hcnt7]
    norm_num
  have hnu_nonneg : ∀ p, p.Prime → 0 ≤ nu p := by
    intro p hp
    simp only [hnu_def]
    rw [ArithmeticFunction.prodPrimeFactors_apply hp.pos.ne', hp.primeFactors, Finset.prod_singleton]
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hsplit_nu := Finset.sum_filter_add_sum_filter_not S (fun p => 11 < p) nu
  have hsplit_inv := Finset.sum_filter_add_sum_filter_not S (fun p => 11 < p) (fun p => (1:ℝ)/p)
  have hterm_eq : ∑ p ∈ S.filter (fun p => 11 < p), nu p = 7 * ∑ p ∈ S.filter (fun p => 11 < p), (1/(p:ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    simp only [hS_def, Finset.mem_filter, Finset.mem_Icc] at hp
    obtain ⟨⟨⟨hp1, hpz⟩, hpprime⟩, hp11lt⟩ := hp
    rw [hnu_eq_seven p hpprime (by omega) (by omega)]
    ring
  have hsub : S.filter (fun p => ¬ 11 < p) ⊆ ({2,3,5,7,11} : Finset ℕ) := by
    intro p hp
    simp only [hS_def, Finset.mem_filter, Finset.mem_Icc, not_lt] at hp
    obtain ⟨⟨⟨hp1, hpz⟩, hpprime⟩, hple11⟩ := hp
    simp only [Finset.mem_insert, Finset.mem_singleton]
    interval_cases p <;> revert hpprime <;> decide
  have hbound_small : ∑ p ∈ S.filter (fun p => ¬ 11 < p), (1/(p:ℝ)) ≤ 1/2+1/3+1/5+1/7+1/11 := by
    calc ∑ p ∈ S.filter (fun p => ¬ 11 < p), (1/(p:ℝ))
        ≤ ∑ p ∈ ({2,3,5,7,11}:Finset ℕ), (1/(p:ℝ)) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => by positivity)
      _ = 1/2+1/3+1/5+1/7+1/11 := by norm_num [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton]
  have hnu_small_nonneg : 0 ≤ ∑ p ∈ S.filter (fun p => ¬ 11 < p), nu p := by
    apply Finset.sum_nonneg
    intro p hp
    simp only [hS_def, Finset.mem_filter, Finset.mem_Icc] at hp
    obtain ⟨⟨⟨hp1, hpz⟩, hpprime⟩, hcond⟩ := hp
    exact hnu_nonneg p hpprime
  calc 7 * (∑ p ∈ S, (1/(p:ℝ))) - 7*(1/2+1/3+1/5+1/7+1/11)
      ≤ 7 * (∑ p ∈ S, (1/(p:ℝ))) - 7 * (∑ p ∈ S.filter (fun p => ¬ 11 < p), (1/(p:ℝ))) := by linarith [hbound_small]
    _ = 7 * (∑ p ∈ S.filter (fun p => 11 < p), (1/(p:ℝ))) := by
        rw [← hsplit_inv]; ring
    _ = ∑ p ∈ S.filter (fun p => 11 < p), nu p := hterm_eq.symm
    _ ≤ ∑ p ∈ S.filter (fun p => 11 < p), nu p + ∑ p ∈ S.filter (fun p => ¬ 11 < p), nu p := by linarith [hnu_small_nonneg]
    _ = ∑ p ∈ S, nu p := hsplit_nu
