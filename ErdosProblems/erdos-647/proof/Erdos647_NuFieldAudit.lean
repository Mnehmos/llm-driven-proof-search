import Mathlib

/-!
# Erdős #647 — exposed-instance squarefree nu field audit

Kernel-verified through the tracked proof-search pipeline on 2026-07-15.

  problem_version_id  21676a9b-32f0-497b-a903-cacd52211606
  episode_id          a8a19a21-345a-4e96-a656-1206b8947f16
  root_statement_hash a0d0f1342429ff9d92538e5fbd2aa2edb3b6127fa5cbb4dd90febc33dc226e8b
  outcome             kernel_verified (root_proved), first tracked attempt
  environment_hash    9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d
  verification_job    e31db2c6-098e-40b3-8915-b998c9dfd99b (kernel_pass)
  result_artifact_hash 1fd88bc0514e6d3c92493ba7bc8bcf5ff8e0cfc98b34e88607f9cc2f274f16b8
-/

theorem erdos647_nu_field_audit :
    ∀ (s : BoundingSieve) (d : ℕ),
      s.nu = ArithmeticFunction.prodPrimeFactors (fun q : ℕ => (((Finset.range q).filter (fun t => (210*t)%q=1 ∨ (315*t)%q=1 ∨ (420*t)%q=1 ∨ (630*t)%q=1 ∨ (840*t)%q=1 ∨ (1260*t)%q=1 ∨ (2520*t)%q=1)).card : ℝ) / q) →
      Squarefree d →
      s.nu d = (((Finset.range d).filter (fun r => ∀ p ∈ Nat.primeFactors d, r%p ∈ (Finset.range p).filter (fun t => (210*t)%p=1 ∨ (315*t)%p=1 ∨ (420*t)%p=1 ∨ (630*t)%p=1 ∨ (840*t)%p=1 ∨ (1260*t)%p=1 ∨ (2520*t)%p=1))).card : ℝ) / d := by
  intro s d hnu hd
  have hraw : (((Finset.range d).filter (fun r => ∀ p ∈ Nat.primeFactors d, r%p ∈ (Finset.range p).filter (fun t => (210*t)%p=1 ∨ (315*t)%p=1 ∨ (420*t)%p=1 ∨ (630*t)%p=1 ∨ (840*t)%p=1 ∨ (1260*t)%p=1 ∨ (2520*t)%p=1))).card : ℝ) / d = ∏ p ∈ Nat.primeFactors d, (((Finset.range p).filter (fun t => (210*t)%p=1 ∨ (315*t)%p=1 ∨ (420*t)%p=1 ∨ (630*t)%p=1 ∨ (840*t)%p=1 ∨ (1260*t)%p=1 ∨ (2520*t)%p=1)).card : ℝ) / p := by
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
    have hcnt_eq : ((Finset.range d).filter (fun r => ∀ p ∈ Nat.primeFactors d, r%p ∈ (Finset.range p).filter (fun s => (210*s)%p=1 ∨ (315*s)%p=1 ∨ (420*s)%p=1 ∨ (630*s)%p=1 ∨ (840*s)%p=1 ∨ (1260*s)%p=1 ∨ (2520*s)%p=1))).card
        = ∏ p ∈ d.primeFactors, ((Finset.range p).filter (fun s => (210*s)%p=1 ∨ (315*s)%p=1 ∨ (420*s)%p=1 ∨ (630*s)%p=1 ∨ (840*s)%p=1 ∨ (1260*s)%p=1 ∨ (2520*s)%p=1)).card := by
      have hraw := crt_finset d.primeFactors hp_prime (fun p => (Finset.range p).filter (fun s => (210*s)%p=1 ∨ (315*s)%p=1 ∨ (420*s)%p=1 ∨ (630*s)%p=1 ∨ (840*s)%p=1 ∨ (1260*s)%p=1 ∨ (2520*s)%p=1)) (fun p _ => Finset.filter_subset _ _)
      rwa [hprod_eq2] at hraw
    have hd_eq : (∏ p ∈ d.primeFactors, (p:ℝ)) = (d:ℝ) := by
      rw [← Nat.cast_prod, hprod_eq2]
    rw [hcnt_eq]
    push_cast
    rw [← hd_eq, Finset.prod_div_distrib]
  rw [hnu, ArithmeticFunction.prodPrimeFactors_apply hd.ne_zero]
  exact hraw.symm
