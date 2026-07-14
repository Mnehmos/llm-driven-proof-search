import Mathlib

/-!
# Erdős #647 — Layer C: CRT residue-count product formula (two moduli)

Snapshot of the exact statement + proof term kernel-verified through the
tracked proof-search pipeline on 2026-07-14.

  problem_version_id  4d884823-ff12-42bb-9451-c9206f999afd
  episode_id          b0e46fad-8b90-4387-8982-4d5fd357db15
  root_statement_hash d4969a40fee0fdeb0005e45d52efc5aa992e243525b10e59321fb56abcaedc5e
  outcome             kernel_verified (root_proved)
  import manifest     ["Mathlib.Tactic.Ring", "Mathlib.Tactic.NormNum", "Mathlib"]

Content: a general-purpose (sieve-independent) Chinese Remainder Theorem
counting fact — for coprime moduli `p`, `M` and residue subsets `Sp ⊆
[0,p)`, `T ⊆ [0,M)`, the number of `r < p·M` with `r%p ∈ Sp` AND `r%M ∈ T`
is EXACTLY `|Sp|·|T|`. This is the combinatorial engine for extending
`erdos647_rem_bound` (proven only for prime `p`, see
`Erdos647_RemBound.lean`) to composite squarefree `d`: since
`BoundingSieve.errSum` (Mathlib's `SelbergSieve.lean`) sums `|rem d|` over
EVERY `d ∈ prodPrimes(z).divisors` — not just primes — the seven-tuple
sieve's error term genuinely needs `rootUnionCount(d) = ∏_{p∣d}
rootUnionCount(p)` for squarefree `d`, which this lemma will let be proven
by induction on `d`'s prime factors (peeling off one prime `p` at a time,
treating the rest as the composite modulus `M`).

Proof: `Finset.card_bij` with the explicit CRT bijection `r ↦ (r%p, r%M)`
between the filtered range-Finset and `Sp ×ˢ T`. Injectivity via
`Nat.modEq_and_modEq_iff_modEq_mul` (two separate congruences combine into
one mod `p·M`, then bounded residues below `p·M` forces equality).
Surjectivity via `Nat.chineseRemainder` (existence) + `Nat.chineseRemainder_lt_mul`
(the witness is `< p·M`).

Key new Lean lesson (distinct from the `clear_value`-for-recursion lesson
in `Erdos647_RemBound.lean`): **rewriting inside a term that carries a
`Subtype`'s dependent proof (e.g. `↑(Nat.chineseRemainder hcop a b)`, whose
very TYPE mentions `a`,`b`) can fail with "motive is not type correct"**,
even for a seemingly ordinary `rw` on a derived `Nat` equation — and
`obtain ⟨k, hka, hkb⟩ := Nat.chineseRemainder hcop a b` does NOT
retroactively fold a `have` proven *before* the `obtain` into the new
opaque `k` (unlike a hypothesis-based `rcases h : ...`, plain `obtain` on
a fresh expression does not generalize prior unrelated hypotheses). The
fix that worked: state ALL facts about the CRT witness (`hka`, `hkb`,
`hklt`) FIRST while still written as `(Nat.chineseRemainder hcop a b :
ℕ)`, THEN `set k := (Nat.chineseRemainder hcop a b : ℕ) with hkeq;
clear_value k` — `set` retroactively folds every matching occurrence in
the already-existing hypotheses into the new opaque `k`, after which `k`
is a plain `Nat` local constant with no dependent-type baggage, so all
subsequent `rw`/`unfold` on facts about it work with zero friction.
-/

theorem erdos647_crt_card_two :
    ∀ (p M : ℕ), 0 < p → 0 < M → Nat.Coprime p M →
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
