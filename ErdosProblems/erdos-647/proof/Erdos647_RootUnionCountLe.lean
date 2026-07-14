import Mathlib

/-!
# Erdős #647 — Layer C: rootUnionCount(d) ≤ 7^ω(d) for squarefree admissible d

Snapshot of the exact statement + proof term kernel-verified through the
tracked proof-search pipeline on 2026-07-14.

  problem_version_id  c0309264-c251-47f5-89b5-69d913afcf7e
  episode_id          a1eac1cf-4d52-4a21-ab67-83249292f12c
  root_statement_hash 069765c36b4eb115dfde5d60f8a93f5ebce7da7b853f6972397473bf235325d9
  outcome             kernel_verified (root_proved)
  import manifest     ["Mathlib.Tactic.Ring", "Mathlib.Tactic.NormNum", "Mathlib"]

Content: for squarefree `d` with no prime factor in `{3,5,7}`, the
root-union residue count is bounded by `7^ω(d)` (`ω(d) :=
d.primeFactors.card`, the number of DISTINCT prime factors — well-defined
since `d` squarefree). Combines `erdos647_crt_card_finset` (inlined:
`rootUnionCount(d) = ∏_{p∣d} rootUnionCount(p)`, exact equality) with the
per-prime admissibility bound `rootUnionCount(p) ≤ 7` (inlined: `native_decide`
for `p=2`, the `ZMod`-field-inverse existence/uniqueness argument for
`p>7`, both reused verbatim from `Erdos647_SevenTupleAdmissibility.lean`)
to get the crude but clean multiplicative bound `∏_{p∣d} rootUnionCount(p)
≤ ∏_{p∣d} 7 = 7^ω(d)` via `Finset.prod_le_prod` + `Finset.prod_const`.

This supplies the explicit numeric growth bound needed (alongside
`erdos647_rem_bound_squarefree`/`_one` and `erdos647_lambdaSquared_bound`)
to bound `BoundingSieve.errSum` — `rootUnionCount(d)` bounds `|rem(d)|`,
and `7^ω(d)` is the concrete form needed for a divisor-sum growth-rate
estimate.

One Lean bug fixed across 2 rounds: `rw [← hprod_eq2]` (`hprod_eq2 :
∏p∈d.primeFactors,p = d`) applied to the goal
`(range d).filter(...).card = ∏_{p∈d.primeFactors}(...).card` is
SELF-REFERENTIAL — the goal's OWN `d.primeFactors` binder contains the
literal `d`, so a blind `rw[←hprod_eq2]` rewrites `d` EVERYWHERE
including inside `d.primeFactors`, turning it into
`(∏p∈d.primeFactors,p).primeFactors` and breaking the match against
`crt_finset`'s conclusion (which is stated with a FIXED Finset `t`, not
re-derived from the product). Same self-reference class of bug as
`Erdos647_SelbergWeightBound.lean`'s `rw[←hNd]` issue, different
manifestation. Fixed by computing the raw `crt_finset` instantiation
FIRST (as `hraw`, entirely in terms of `d.primeFactors` with no
`∏...`-rewriting needed), THEN `rw [hprod_eq2] at hraw` (forward
direction, only touching the isolated `∏p∈d.primeFactors,p` subterm that
appears from unfolding `crt_finset`'s own `range(∏t,p)` — a subterm that
does NOT recursively contain `d.primeFactors` itself, so no
self-reference). **General reusable lesson: prefer rewriting a
freshly-obtained `have` fact forward, rather than rewriting a compound
goal backward, whenever the rewritten pattern could recur inside a binder
built from the same base term.**
-/

theorem erdos647_rootUnionCount_le :
    ∀ (d : ℕ), Squarefree d → (∀ p ∈ Nat.primeFactors d, p ≠ 3 ∧ p ≠ 5 ∧ p ≠ 7) →
      ((Finset.range d).filter (fun r => ∀ p ∈ Nat.primeFactors d, r%p ∈ (Finset.range p).filter (fun s => (210*s)%p=1 ∨ (315*s)%p=1 ∨ (420*s)%p=1 ∨ (630*s)%p=1 ∨ (840*s)%p=1 ∨ (1260*s)%p=1 ∨ (2520*s)%p=1))).card ≤ 7 ^ (Nat.primeFactors d).card := by
  intro d hd hp_adm
  have hp_prime : ∀ p ∈ d.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have hprod_eq2 : ∏ p ∈ d.primeFactors, p = d := Nat.prod_primeFactors_of_squarefree hd
  have crt_card_two : ∀ (p M : ℕ), 0 < p → 0 < M → Nat.Coprime p M →
      ∀ (Sp T : Finset ℕ), Sp ⊆ Finset.range p → T ⊆ Finset.range M →
      ((Finset.range (p*M)).filter (fun r => r%p ∈ Sp ∧ r%M ∈ T)).card = Sp.card * T.card := by
    intro p M hp hM hcop Sp T hSp hT
    rw [← Finset.card_product]
    apply Finset.card_bij (fun r (_ : r ∈ (Finset.range (p*M)).filter (fun r => r%p ∈ Sp ∧ r%M ∈ T)) => (r%p, r%M))
    · intro r hr
      simp only [Finset.mem_filter] at hr
      simp only [Finset.mem_product]
      exact hr.2
    · intro r1 hr1 r2 hr2 heq
      simp only [Finset.mem_filter, Finset.mem_range] at hr1 hr2
      simp only [Prod.mk.injEq] at heq
      have h1 : r1 ≡ r2 [MOD p] := heq.1
      have h2 : r1 ≡ r2 [MOD M] := heq.2
      have h3 : r1 ≡ r2 [MOD p*M] := (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨h1,h2⟩
      have h4 := h3
      unfold Nat.ModEq at h4
      rwa [Nat.mod_eq_of_lt hr1.1, Nat.mod_eq_of_lt hr2.1] at h4
    · intro b hb
      simp only [Finset.mem_product] at hb
      obtain ⟨a1, b1⟩ := b
      have haP : a1 < p := Finset.mem_range.mp (hSp hb.1)
      have hbM : b1 < M := Finset.mem_range.mp (hT hb.2)
      have hka : (Nat.chineseRemainder hcop a1 b1 : ℕ) ≡ a1 [MOD p] := (Nat.chineseRemainder hcop a1 b1).prop.1
      have hkb : (Nat.chineseRemainder hcop a1 b1 : ℕ) ≡ b1 [MOD M] := (Nat.chineseRemainder hcop a1 b1).prop.2
      have hklt : (Nat.chineseRemainder hcop a1 b1 : ℕ) < p*M := Nat.chineseRemainder_lt_mul hcop a1 b1 hp.ne' hM.ne'
      set k := (Nat.chineseRemainder hcop a1 b1 : ℕ) with hkeq
      clear_value k
      have hkp : k % p = a1 := by
        have h5 := hka; unfold Nat.ModEq at h5; rw [Nat.mod_eq_of_lt haP] at h5; exact h5
      have hkM : k % M = b1 := by
        have h6 := hkb; unfold Nat.ModEq at h6; rw [Nat.mod_eq_of_lt hbM] at h6; exact h6
      have hmemr : k ∈ (Finset.range (p*M)).filter (fun r => r%p ∈ Sp ∧ r%M ∈ T) := by
        simp only [Finset.mem_filter, Finset.mem_range]
        exact ⟨hklt, hkp ▸ hb.1, hkM ▸ hb.2⟩
      refine ⟨k, hmemr, ?_⟩
      simp only [Prod.mk.injEq]
      exact ⟨hkp, hkM⟩
  have crt_finset : ∀ (t : Finset ℕ), (∀ p ∈ t, p.Prime) →
      ∀ (S : ℕ → Finset ℕ), (∀ p ∈ t, S p ⊆ Finset.range p) →
      ((Finset.range (∏ p ∈ t, p)).filter (fun r => ∀ p ∈ t, r % p ∈ S p)).card = ∏ p ∈ t, (S p).card := by
    intro t
    induction t using Finset.induction_on with
    | empty => intro _ S _; simp
    | @insert p t' hp_notin ih =>
      intro hp_all S hS
      have hp_prime2 : p.Prime := hp_all p (Finset.mem_insert_self p t')
      have ht'_prime : ∀ q ∈ t', q.Prime := fun q hq => hp_all q (Finset.mem_insert_of_mem hq)
      have hp_pos : 0 < p := hp_prime2.pos
      have hM_pos : 0 < ∏ q ∈ t', q := Finset.prod_pos (fun q hq => (ht'_prime q hq).pos)
      have hcop : Nat.Coprime p (∏ q ∈ t', q) := by
        apply Nat.Coprime.prod_right
        intro q hq
        rw [Nat.coprime_primes hp_prime2 (ht'_prime q hq)]
        intro heq
        exact hp_notin (heq ▸ hq)
      have hSp : S p ⊆ Finset.range p := hS p (Finset.mem_insert_self p t')
      have hSt' : ∀ q ∈ t', S q ⊆ Finset.range q := fun q hq => hS q (Finset.mem_insert_of_mem hq)
      have hTsub : (Finset.range (∏ q ∈ t', q)).filter (fun r => ∀ q ∈ t', r % q ∈ S q) ⊆ Finset.range (∏ q ∈ t', q) := Finset.filter_subset _ _
      have hTcard : ((Finset.range (∏ q ∈ t', q)).filter (fun r => ∀ q ∈ t', r % q ∈ S q)).card = ∏ q ∈ t', (S q).card := ih ht'_prime S hSt'
      have hmodM : ∀ q ∈ t', ∀ r : ℕ, r % q = (r % (∏ x ∈ t', x)) % q := by
        intro q hq r
        have hqM : q ∣ (∏ x ∈ t', x) := Finset.dvd_prod_of_mem _ hq
        have h1 : r % (∏ x ∈ t', x) ≡ r [MOD (∏ x ∈ t', x)] := Nat.mod_modEq r _
        have h2 : r % (∏ x ∈ t', x) ≡ r [MOD q] := h1.of_dvd hqM
        exact h2.symm
      have hSeteq : (Finset.range (p * ∏ q ∈ t', q)).filter (fun r => ∀ q ∈ insert p t', r % q ∈ S q) =
          (Finset.range (p * ∏ q ∈ t', q)).filter (fun r => r % p ∈ S p ∧ r % (∏ q ∈ t', q) ∈ (Finset.range (∏ q ∈ t', q)).filter (fun r => ∀ q ∈ t', r % q ∈ S q)) := by
        ext r
        simp only [Finset.mem_filter, Finset.mem_range]
        constructor
        · rintro ⟨hrlt, hall⟩
          refine ⟨hrlt, hall p (Finset.mem_insert_self p t'), Nat.mod_lt r hM_pos, ?_⟩
          intro q hq
          rw [← hmodM q hq r]
          exact hall q (Finset.mem_insert_of_mem hq)
        · rintro ⟨hrlt, hpmem, _, hTall⟩
          refine ⟨hrlt, ?_⟩
          intro q hq
          rcases Finset.mem_insert.mp hq with heq | hq'
          · rwa [heq]
          · rw [hmodM q hq' r]
            exact hTall q hq'
      rw [Finset.prod_insert hp_notin, Finset.prod_insert hp_notin, hSeteq,
          crt_card_two p (∏ q ∈ t', q) hp_pos hM_pos hcop (S p) _ hSp hTsub, hTcard]
  have hle7 : ∀ p ∈ d.primeFactors, ((Finset.range p).filter (fun s => (210*s)%p=1 ∨ (315*s)%p=1 ∨ (420*s)%p=1 ∨ (630*s)%p=1 ∨ (840*s)%p=1 ∨ (1260*s)%p=1 ∨ (2520*s)%p=1)).card ≤ 7 := by
    intro p hp
    have hp_prime_p : p.Prime := hp_prime p hp
    have hp3 : p ≠ 3 := (hp_adm p hp).1
    have hp5 : p ≠ 5 := (hp_adm p hp).2.1
    have hp7 : p ≠ 7 := (hp_adm p hp).2.2
    by_cases hp2 : p = 2
    · subst hp2
      have : ((Finset.range 2).filter (fun r => (210*r)%2=1 ∨ (315*r)%2=1 ∨ (420*r)%2=1 ∨ (630*r)%2=1 ∨ (840*r)%2=1 ∨ (1260*r)%2=1 ∨ (2520*r)%2=1)).card = 1 := by native_decide
      omega
    · have hp7lt : 7 < p := by
        by_contra hle
        push_neg at hle
        have h2le : 2 ≤ p := hp_prime_p.two_le
        interval_cases p <;> first | (exfalso; omega) | (exfalso; norm_num at hp_prime_p)
      haveI : Fact p.Prime := ⟨hp_prime_p⟩
      haveI : Fact (1 < p) := ⟨hp_prime_p.one_lt⟩
      have hexists : ∀ (c : ℕ), ¬ p ∣ c → ∃ r < p, (c * r) % p = 1 := by
        intro c hpc
        have hcne : (c : ZMod p) ≠ 0 := by rwa [Ne, ZMod.natCast_eq_zero_iff]
        refine ⟨((c:ZMod p)⁻¹).val, ZMod.val_lt _, ?_⟩
        have h1 : (c:ZMod p) * (c:ZMod p)⁻¹ = 1 := mul_inv_cancel₀ hcne
        have h2 : ((c * ((c:ZMod p)⁻¹).val : ℕ) : ZMod p) = 1 := by
          push_cast; rw [ZMod.natCast_val, ZMod.cast_id]; exact h1
        have h4 : (c * ((c:ZMod p)⁻¹).val) % p < p := Nat.mod_lt _ hp_prime_p.pos
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
          push_cast at e1 e2; rw [e1, e2]
        have e4 : (r1 : ZMod p) = (r2 : ZMod p) := mul_left_cancel₀ hcne e3
        have e5 := congrArg ZMod.val e4
        rwa [ZMod.val_cast_of_lt hr1, ZMod.val_cast_of_lt hr2] at e5
      have hnd : ∀ c ∈ ([210,315,420,630,840,1260,2520] : List ℕ), ¬ p ∣ c := by
        intro c hc hpdvd
        have hcdvd : c ∣ 2520 := by fin_cases hc <;> norm_num
        have hpdvd2520 : p ∣ 2520 := hpdvd.trans hcdvd
        have hpmem : p ∈ Nat.primeFactors 2520 := Nat.mem_primeFactors.mpr ⟨hp_prime_p, hpdvd2520, by norm_num⟩
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
      have hSeq2 : (Finset.range p).filter (fun r => (210*r)%p=1 ∨ (315*r)%p=1 ∨ (420*r)%p=1 ∨ (630*r)%p=1 ∨ (840*r)%p=1 ∨ (1260*r)%p=1 ∨ (2520*r)%p=1) = S210 ∪ S315 ∪ S420 ∪ S630 ∪ S840 ∪ S1260 ∪ S2520 := by
        ext r
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union, hS210, hS315, hS420, hS630, hS840, hS1260, hS2520]
        tauto
      rw [hSeq2]
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
  have hcnt_eq : ((Finset.range d).filter (fun r => ∀ p ∈ Nat.primeFactors d, r%p ∈ (Finset.range p).filter (fun s => (210*s)%p=1 ∨ (315*s)%p=1 ∨ (420*s)%p=1 ∨ (630*s)%p=1 ∨ (840*s)%p=1 ∨ (1260*s)%p=1 ∨ (2520*s)%p=1))).card
      = ∏ p ∈ d.primeFactors, ((Finset.range p).filter (fun s => (210*s)%p=1 ∨ (315*s)%p=1 ∨ (420*s)%p=1 ∨ (630*s)%p=1 ∨ (840*s)%p=1 ∨ (1260*s)%p=1 ∨ (2520*s)%p=1)).card := by
    have hraw := crt_finset d.primeFactors hp_prime (fun p => (Finset.range p).filter (fun s => (210*s)%p=1 ∨ (315*s)%p=1 ∨ (420*s)%p=1 ∨ (630*s)%p=1 ∨ (840*s)%p=1 ∨ (1260*s)%p=1 ∨ (2520*s)%p=1)) (fun p _ => Finset.filter_subset _ _)
    rwa [hprod_eq2] at hraw
  rw [hcnt_eq, ← Finset.prod_const]
  exact Finset.prod_le_prod (fun p _ => Nat.zero_le _) hle7
