import Mathlib

/-!
# Erdős #647 — Layer C growth-rate prep: rootUnionCount(p) = 7 for p > 7, p ≠ 11

Snapshot of the exact statement + proof term kernel-verified through the
tracked proof-search pipeline on 2026-07-14.

  problem_version_id  390ef24b-5b8a-4f7e-97cf-65440ad1144c
  episode_id          08ca94f0-1665-4cc2-8127-035d31282911
  root_statement_hash 4c1eefc0a9ecff50a9eb2d15d9e37de0689782a87a5f9375e0731c9863d909c3
  outcome             kernel_verified (root_proved)
  import manifest     ["Mathlib.Tactic.Ring", "Mathlib.Tactic.NormNum", "Mathlib"]

Content: a genuinely NEW structural fact, sharpening the previously-proven
`erdos647_seventuple_admissible_general` ("root-union size between 1 and
7 uniformly for p>7") to an EXACT value: `rootUnionCount(p) = 7` for
EVERY prime `p>7` except `p=11` (where it drops to 6). Confirmed
numerically first (Python, all primes to 300: p=11 is the unique
exception) before formalizing — the "bad primes" set (primes dividing
any pairwise difference among the seven coefficients `{210,315,420,630,
840,1260,2520}`) is exactly `{2,3,5,7,11}`; only the `(k=1,k=12)` pair
(`2520-210=2310=2·3·5·7·11`) brings in the prime 11 (both `2520` and
`210` are `≡1 mod 11`, so their forms collide there).

**Why this matters**: `ν(p) := rootUnionCount(p)/p`, and getting `L =
∏_{p≤z}(1-ν(p))⁻¹` to grow like `(log z)^7` (the exponent the whole
`x/(log x)^7` claim needs) requires knowing `ν(p) ~ 7/p` — NOT just the
weaker `ν(p)∈[1/p, 7/p]` range the earlier admissibility theorem gives.
This theorem supplies exactly that, for all but the single exceptional
prime 11 (whose contribution is a bounded constant factor, not affecting
the asymptotic order).

Proof: reuses `erdos647_seventuple_admissible_general`'s ZMod-p
existence/uniqueness machinery (each coefficient's root is a unique
field inverse) to get 7 singleton root-sets, each of cardinality
EXACTLY 1 (not just ≤1, using both directions this time). The NEW part:
a generic `hdisj_gen` lemma shows two coefficients' root-sets are
disjoint whenever `p` doesn't divide their difference (via `(c1:ZMod p)
= (c2:ZMod p)` cancellation from a shared root, contradicted by
`p∤(c2-c1)`); instantiated for all 21 pairs, each via `hnodvd` (`p >
7 → p ≠ 11 → d.primeFactors ⊆ {2,3,5,7,11} → p∤d`, `native_decide` on
each concrete difference's `primeFactors`). The 21 pairwise facts are
combined into 7-way pairwise disjointness via `Finset.disjoint_union_left`
chained 15 times, then `Finset.card_union_of_disjoint` chained 6 times
gives the exact union cardinality `1+1+1+1+1+1+1=7`.

**One Lean fix (recurring campaign lesson, same class as `erdos647_rem_
bound`'s recursion-depth issue)**: the 7 `set S210 := ... with hS210`
local definitions (each a nontrivial `Finset.filter` over an abstract
`p`), left un-cleared, caused a `(deterministic) timeout at whnf` on the
FINAL `exact hc7` step (200000 heartbeats exhausted) — Lean's
typechecker tried to unfold the accumulated zeta-reducible local defs
while verifying the last `have`'s type against the goal. Fixed with
`clear_value S210 S315 S420 S630 S840 S1260 S2520` immediately after the
`set` block, making them opaque; every downstream reference to `S210`
etc. that needs the underlying filter form (the 7 cardinality facts, the
21 disjointness facts) now goes through the retained equation hypotheses
(`rw [hS210, ...]` before `exact ...`) instead of relying on unfolding.
This is now the THIRD confirmed instance of this exact failure mode in
the campaign (after `erdos647_rem_bound` and this one) — the lesson
generalizes: any proof introducing several `set`-bound `Finset.filter`
locals over an abstract index and then combining them via multiple
downstream `have`s should `clear_value` immediately, by default.
-/

theorem erdos647_seventuple_rootcount_eq_seven :
    ∀ (p : ℕ), p.Prime → 7 < p → p ≠ 11 →
      ((Finset.range p).filter (fun r => (210*r)%p=1 ∨ (315*r)%p=1 ∨ (420*r)%p=1 ∨ (630*r)%p=1 ∨ (840*r)%p=1 ∨ (1260*r)%p=1 ∨ (2520*r)%p=1)).card = 7 := by
  intro p hp hp7 hp11
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
    have hz : ((c2 - c1 : ℕ) : ZMod p) = 0 := by
      rw [Nat.cast_sub hlt.le, ← e4, sub_self]
    rwa [ZMod.natCast_eq_zero_iff] at hz
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
