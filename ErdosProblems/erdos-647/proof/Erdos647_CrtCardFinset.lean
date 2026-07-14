import Mathlib

/-!
# Erdős #647 — Layer C: CRT residue-count product formula (Finset of primes)

Snapshot of the exact statement + proof term kernel-verified through the
tracked proof-search pipeline on 2026-07-14.

  problem_version_id  77c1d1e1-b8f9-4cc1-a615-6ff2c8b7a52d
  episode_id          7cb44a91-02ef-45a1-a3ee-91b7e701dbd0
  root_statement_hash 59ac70e7066924ca1cb9547c9d7c7d9ebcf848bab8344e135b29b73923aeface
  outcome             kernel_verified (root_proved)
  import manifest     ["Mathlib.Tactic.Ring", "Mathlib.Tactic.NormNum", "Mathlib"]

Content: generalizes `erdos647_crt_card_two` (two coprime moduli) to an
arbitrary `Finset ℕ` of primes. For a `Finset t` of primes and residue
subsets `S p ⊆ [0,p)` for every `p ∈ t`, the number of `r < ∏_{p∈t} p`
satisfying `r%p ∈ S p` for EVERY `p ∈ t` is exactly `∏_{p∈t} |S p|`.

This is the combinatorial engine needed to compute `rootUnionCount(d) =
∏_{p∣d} rootUnionCount(p)` for ANY squarefree `d` (not just a product of
two primes), which — combined with `erdos647_squarefree_dvd_iff` and
`erdos647_forms_divisible_iff` — will let `erdos647_rem_bound` extend from
prime `p` to composite squarefree `d`. Required because Mathlib's
`BoundingSieve.errSum` sums `|rem d|` over EVERY `d ∈
prodPrimes(z).divisors`, not just primes (confirmed by reading
`SelbergSieve.lean` directly).

Proof: `Finset.induction_on t`. Base case `t=∅`: both sides are `1`
(`Finset.range 1` filtered by a vacuous `∀`-condition is `{0}`, and the
empty product is `1`). Inductive step `t = insert p t'`: peels `p` off,
treats `M := ∏_{q∈t'} q` as the second modulus, and applies the
TWO-modulus case (`erdos647_crt_card_two`, inlined per this campaign's
established cross-submission-independence requirement) with `Sp := S p`
and `T :=` the recursive filtered set for `t'` (whose card is `∏_{q∈t'}
|S q|` by the induction hypothesis). The one new piece is a mod-reduction
helper `∀ q∈t', r%q = (r%M)%q` (via `Nat.ModEq.of_dvd`, since `q∣M`)
letting the per-prime conditions on `t'`'s primes be rewritten as a single
condition on `r%M`, so the `insert`-case's filtered set over `range(p·M)`
matches the two-modulus lemma's shape exactly (`Finset.ext` + `simp` +
`rintro`/`refine` — the same style used throughout this campaign for
Finset-equality proofs).

No new Lean lessons beyond what `Erdos647_CrtCardTwo.lean` already
recorded — this proof reused that lemma's exact (already-debugged) text
verbatim, inlined as a local `have` before the `induction`, and the
`induction ... with | empty => ... | @insert p t' hp_notin ih => ...`
named-case + explicit-binder-name (`@insert`) syntax worked first try.
-/

theorem erdos647_crt_card_finset :
    ∀ (t : Finset ℕ), (∀ p ∈ t, p.Prime) →
      ∀ (S : ℕ → Finset ℕ), (∀ p ∈ t, S p ⊆ Finset.range p) →
      ((Finset.range (∏ p ∈ t, p)).filter (fun r => ∀ p ∈ t, r % p ∈ S p)).card = ∏ p ∈ t, (S p).card := by
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
        have h5 := hka
        unfold Nat.ModEq at h5
        rw [Nat.mod_eq_of_lt haP] at h5
        exact h5
      have hkM : k % M = b1 := by
        have h6 := hkb
        unfold Nat.ModEq at h6
        rw [Nat.mod_eq_of_lt hbM] at h6
        exact h6
      have hmemr : k ∈ (Finset.range (p*M)).filter (fun r => r%p ∈ Sp ∧ r%M ∈ T) := by
        simp only [Finset.mem_filter, Finset.mem_range]
        exact ⟨hklt, hkp ▸ hb.1, hkM ▸ hb.2⟩
      refine ⟨k, hmemr, ?_⟩
      simp only [Prod.mk.injEq]
      exact ⟨hkp, hkM⟩
  intro t
  induction t using Finset.induction_on with
  | empty =>
    intro _ S _
    simp
  | @insert p t' hp_notin ih =>
    intro hp_all S hS
    have hp_prime : p.Prime := hp_all p (Finset.mem_insert_self p t')
    have ht'_prime : ∀ q ∈ t', q.Prime := fun q hq => hp_all q (Finset.mem_insert_of_mem hq)
    have hp_pos : 0 < p := hp_prime.pos
    have hM_pos : 0 < ∏ q ∈ t', q := Finset.prod_pos (fun q hq => (ht'_prime q hq).pos)
    have hcop : Nat.Coprime p (∏ q ∈ t', q) := by
      apply Nat.Coprime.prod_right
      intro q hq
      rw [Nat.coprime_primes hp_prime (ht'_prime q hq)]
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
