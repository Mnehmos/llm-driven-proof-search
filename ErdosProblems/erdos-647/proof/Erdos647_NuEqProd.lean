import Mathlib

/-!
# Erdős #647 — Layer C bridging lemma: raw ν(d) = ∏_{p∣d} ν(p)

Snapshot of the exact statement + proof term kernel-verified through the
tracked proof-search pipeline on 2026-07-14.

  problem_version_id  5565853e-8b83-40bb-9579-0bad9b4ea6ab
  episode_id          08a47a29-b0b2-4a22-9522-42699149bf95
  root_statement_hash b35ea25aeda9c89fce5e42e0c7ff69198f65fc49fd0197a1616be32466519c27
  outcome             kernel_verified (root_proved)
  import manifest     ["Mathlib.Tactic.Ring", "Mathlib.Tactic.NormNum", "Mathlib"]

Content: the RAW combinatorial `ν(d) := rootUnionCount(d)/d` used directly
in `erdos647_rem_bound_squarefree` equals the MULTIPLICATIVE product form
`∏_{p∣d} (rootUnionCount(p)/p)` for squarefree `d`. This confirms it is
literally the SAME quantity as the `ArithmeticFunction.prodPrimeFactors`-based
`ν` used throughout the abstract `SelbergSieve` framework
(`erdos647_nu_admissible`, `erdos647_selberg_optimal_weight`,
`erdos647_selberg_weight_bound`) — up to `ArithmeticFunction.prodPrimeFactors_apply`'s
definitional unfolding, which already reduces to exactly this product for
squarefree arguments. Needed before the `rem(d)` bounds (stated with the
raw combinatorial `ν`) and the Selberg weight/`lambdaSquared` bounds
(stated with the abstract `s.nu`) can be combined into a single `errSum`
estimate for a common `s : SelbergSieve` instance.

Proof: `erdos647_crt_card_finset` (inlined) gives `rootUnionCount(d) =
∏_{p∣d} rootUnionCount(p)` as NATURALS; casting to `ℝ`
(`Nat.cast_prod`) and using `d = ∏_{p∣d} p` (squarefree,
`Nat.prod_primeFactors_of_squarefree`) to split the denominator via
`Finset.prod_div_distrib` gives the result.

One small fix: `exact_mod_cast hprod_eq2` alone couldn't bridge `∏
p∈d.primeFactors, (p:ℝ) = (d:ℝ)` from the Nat-level `hprod_eq2 : ∏
p∈d.primeFactors, p = d` — norm_cast's automation didn't fold the product
under the cast automatically here. Fixed with the explicit two-step `rw
[← Nat.cast_prod, hprod_eq2]` (first fold `∏(p:ℝ)` into `↑(∏p)` via
`Nat.cast_prod`, then rewrite the now-exposed Nat-level product using
`hprod_eq2` directly, closing by the automatic `rfl` after `rw`).
-/

theorem erdos647_nu_eq_prod :
    ∀ (d : ℕ), Squarefree d →
      (((Finset.range d).filter (fun r => ∀ p ∈ Nat.primeFactors d, r%p ∈ (Finset.range p).filter (fun s => (210*s)%p=1 ∨ (315*s)%p=1 ∨ (420*s)%p=1 ∨ (630*s)%p=1 ∨ (840*s)%p=1 ∨ (1260*s)%p=1 ∨ (2520*s)%p=1))).card : ℝ) / d
      = ∏ p ∈ Nat.primeFactors d, (((Finset.range p).filter (fun s => (210*s)%p=1 ∨ (315*s)%p=1 ∨ (420*s)%p=1 ∨ (630*s)%p=1 ∨ (840*s)%p=1 ∨ (1260*s)%p=1 ∨ (2520*s)%p=1)).card : ℝ) / p := by
  intro d hd
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
