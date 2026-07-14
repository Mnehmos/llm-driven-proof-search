import Mathlib

/-!
# Erdős #647 — Layer C: THE FULL BoundingSieve INSTANCE

Snapshot of the exact statement + proof term kernel-verified through the
tracked proof-search pipeline on 2026-07-14.

  problem_version_id  a208f3c4-a910-487f-a28b-e3de139cb0e2
  episode_id          47e8efda-abd1-4daa-a324-45e85c2dcbef
  root_statement_hash 08c77c8aa24d6e114b2aac24a3145df5c66f2ad20f1d8f45118ffec1cb18ae24
  outcome             kernel_verified (root_proved)
  import manifest     ["Mathlib.Tactic.Ring", "Mathlib.Tactic.NormNum", "Mathlib"]

Content: for every level `z`, a COMPLETE, concrete `Mathlib.BoundingSieve`
structure instance, built entirely from this campaign's own independently
derived and separately kernel-verified results:

  - `support := (Finset.Icc 1 z).image (∏ᵢ formᵢ)` — the product-of-
    seven-forms map (validated injective in `Erdos647_SupportInjective.lean`).
  - `prodPrimes := ∏_{p prime ≤ z, p∉{3,5,7}} p` (validated squarefree in
    `Erdos647_ProdPrimesSquarefree.lean`).
  - `weights := fun _ => 1`, `totalMass := z`.
  - `nu := ArithmeticFunction.prodPrimeFactors (fun q => rootUnionCount(q)/q)`
    (validated `0<ν(p)<1` for admissible primes in
    `Erdos647_NuAdmissible.lean`; multiplicativity free from the
    `prodPrimeFactors` constructor).

The two remaining structure obligations, `nu_pos_of_prime` and
`nu_lt_one_of_prime`, require showing `p ∣ prodPrimes(z) → p∉{3,5,7}` —
proven here via `hp.prime.dvd_finsetProd_iff` (any prime dividing a
product of primes must itself be one of the factors, via
`Nat.prime_dvd_prime_iff_eq`) — then combined with the previously-proven
`ν`-admissibility theorem.

**This is the first, and hardest-to-assemble, concrete `BoundingSieve`
instance this campaign has built** — first-try `kernel_pass` on the full
~2-sorry-then-filled submission (confirmed the structural/type-matching
skeleton independently first via a `sorry`-placeholder diagnostic
submission before filling in the real proofs, avoiding wasted rounds on
a ~450-line combined submission).

**What remains for the final numeric Layer C theorem** (this instance
itself is complete and requires nothing further to exist): extracting a
useful asymptotic bound needs the `multSum`/`errSum` estimate — summing
`Erdos647_ResidueCountBound.lean`'s per-residue bound over each `d`'s
root-union — then applying Mathlib's
`BoundingSieve.siftedSum_le_mainSum_errSum_of_upperMoebius` combined with
Layer B's `erdos647_selberg_optimal_weight` and Layer A's
`erdos647_mertens_assembly`, choosing an optimal `z=z(x)`.
-/

theorem erdos647_boundingSieve_instance :
    ∀ (z : ℕ), Nonempty BoundingSieve := by
  intro z
  have hmem : ∀ p : ℕ, p.Prime → p ∣ (∏ q ∈ (Finset.range (z+1)).filter (fun q => q.Prime ∧ q ≠ 3 ∧ q ≠ 5 ∧ q ≠ 7), q) → p ≠ 3 ∧ p ≠ 5 ∧ p ≠ 7 := by
    intro p hp hdvd
    simp only [hp.prime.dvd_finsetProd_iff, Finset.mem_filter, Finset.mem_range] at hdvd
    obtain ⟨q, hqmem, hqdvd⟩ := hdvd
    have heq : p = q := (Nat.prime_dvd_prime_iff_eq hp hqmem.2.1).mp hqdvd
    rw [heq]
    exact ⟨hqmem.2.2.1, hqmem.2.2.2.1, hqmem.2.2.2.2⟩
  have hnu_bound : ∀ (p : ℕ), p.Prime → p ≠ 3 → p ≠ 5 → p ≠ 7 →
      0 < (ArithmeticFunction.prodPrimeFactors (fun q : ℕ => (((Finset.range q).filter (fun r => (210*r)%q=1 ∨ (315*r)%q=1 ∨ (420*r)%q=1 ∨ (630*r)%q=1 ∨ (840*r)%q=1 ∨ (1260*r)%q=1 ∨ (2520*r)%q=1)).card : ℝ) / q) : ArithmeticFunction ℝ) p ∧
      (ArithmeticFunction.prodPrimeFactors (fun q : ℕ => (((Finset.range q).filter (fun r => (210*r)%q=1 ∨ (315*r)%q=1 ∨ (420*r)%q=1 ∨ (630*r)%q=1 ∨ (840*r)%q=1 ∨ (1260*r)%q=1 ∨ (2520*r)%q=1)).card : ℝ) / q) : ArithmeticFunction ℝ) p < 1 := by
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
      have : cnt = 1 := by rw [hcnt]; native_decide
      rw [this]
      norm_num
    · haveI : Fact p.Prime := ⟨hp⟩
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
      set S210 := (Finset.range p).filter (fun r => (210*r)%p=1) with hS210
      set S315 := (Finset.range p).filter (fun r => (315*r)%p=1) with hS315
      set S420 := (Finset.range p).filter (fun r => (420*r)%p=1) with hS420
      set S630 := (Finset.range p).filter (fun r => (630*r)%p=1) with hS630
      set S840 := (Finset.range p).filter (fun r => (840*r)%p=1) with hS840
      set S1260 := (Finset.range p).filter (fun r => (1260*r)%p=1) with hS1260
      set S2520 := (Finset.range p).filter (fun r => (2520*r)%p=1) with hS2520
      have hcard1 : ∀ c ∈ ([210,315,420,630,840,1260,2520] : List ℕ), ((Finset.range p).filter (fun r => (c*r)%p=1)).card ≤ 1 := by
        intro c hc
        rw [Finset.card_le_one]
        intro r1 hr1 r2 hr2
        simp only [Finset.mem_filter, Finset.mem_range] at hr1 hr2
        exact hunique c (hnd c hc) r1 r2 hr1.1 hr2.1 hr1.2 hr2.2
      have hS210c : S210.card ≤ 1 := hcard1 210 (by simp)
      have hS315c : S315.card ≤ 1 := hcard1 315 (by simp)
      have hS420c : S420.card ≤ 1 := hcard1 420 (by simp)
      have hS630c : S630.card ≤ 1 := hcard1 630 (by simp)
      have hS840c : S840.card ≤ 1 := hcard1 840 (by simp)
      have hS1260c : S1260.card ≤ 1 := hcard1 1260 (by simp)
      have hS2520c : S2520.card ≤ 1 := hcard1 2520 (by simp)
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
          _ ≤ 1+1+1+1+1+1+1 := by gcongr
          _ = 7 := by norm_num
      have hge1 : 1 ≤ cnt := by
        rw [hSeq]
        obtain ⟨r, hr, hr1⟩ := hexists 2520 (hnd 2520 (by simp))
        have hrmem : r ∈ S2520 := by simp [hS2520, hr, hr1]
        have hpos : 0 < S2520.card := Finset.card_pos.mpr ⟨r, hrmem⟩
        calc 1 ≤ S2520.card := hpos
          _ ≤ (S210 ∪ S315 ∪ S420 ∪ S630 ∪ S840 ∪ S1260 ∪ S2520).card := by
              apply Finset.card_le_card
              intro x hx
              simp only [Finset.mem_union]
              tauto
      have hcntR : (1:ℝ) ≤ (cnt:ℝ) ∧ (cnt:ℝ) ≤ 7 := ⟨by exact_mod_cast hge1, by exact_mod_cast hle7⟩
      constructor
      · apply div_pos (by linarith [hcntR.1]) hppos
      · rw [div_lt_one hppos]
        have : (7:ℝ) < p := by exact_mod_cast h7
        linarith [hcntR.2]
  refine ⟨{
    support := (Finset.Icc 1 z).image (fun N => (210*N-1)*(315*N-1)*(420*N-1)*(630*N-1)*(840*N-1)*(1260*N-1)*(2520*N-1))
    prodPrimes := ∏ p ∈ (Finset.range (z+1)).filter (fun p => p.Prime ∧ p ≠ 3 ∧ p ≠ 5 ∧ p ≠ 7), p
    prodPrimes_squarefree := by
      apply Finset.squarefree_prod_of_pairwise_isCoprime
      · intro p hp q hq hpq
        have hp' := Finset.mem_filter.mp hp
        have hq' := Finset.mem_filter.mp hq
        show IsRelPrime p q
        rw [← Nat.coprime_iff_isRelPrime]
        exact (Nat.coprime_primes hp'.2.1 hq'.2.1).mpr hpq
      · intro p hp
        have hp' := Finset.mem_filter.mp hp
        exact hp'.2.1.squarefree
    weights := fun _ => 1
    weights_nonneg := fun _ => zero_le_one
    totalMass := z
    nu := ArithmeticFunction.prodPrimeFactors (fun q : ℕ => (((Finset.range q).filter (fun r => (210*r)%q=1 ∨ (315*r)%q=1 ∨ (420*r)%q=1 ∨ (630*r)%q=1 ∨ (840*r)%q=1 ∨ (1260*r)%q=1 ∨ (2520*r)%q=1)).card : ℝ) / q)
    nu_mult := ArithmeticFunction.IsMultiplicative.prodPrimeFactors _
    nu_pos_of_prime := fun p hp hdvd => (hnu_bound p hp (hmem p hp hdvd).1 (hmem p hp hdvd).2.1 (hmem p hp hdvd).2.2).1
    nu_lt_one_of_prime := fun p hp hdvd => (hnu_bound p hp (hmem p hp hdvd).1 (hmem p hp hdvd).2.1 (hmem p hp hdvd).2.2).2
  }⟩
