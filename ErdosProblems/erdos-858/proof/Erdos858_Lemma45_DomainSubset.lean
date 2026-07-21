/-
Erdős Problem #858 — Lemma 4.5 connection, `C_N(a)` domain subset (Chojecki 2026).

The harder ("forward") half of the `C_N(a)=R_N(a)/a` Finset-bijection's
Stage A: the `π(n)=a` filter set is a SUBSET of the union of the `P_N(a)`-
image and `Q_N(a)`-image. Companion to `lemma45_CN_domain_supset`
(`Erdos858_Lemma45_DomainSupset.lean`) — together these two give the full
Finset equality (via `Finset.Subset.antisymm`, not yet assembled).

Uses `lemma45_forward_classification_v2` (`Erdos858_Lemma45_ForwardClassificationV2.lean`,
taken as hypothesis `hfwd`) to classify each `n` as `a·p` or `a·p·q`; the
semiprime case handles the `p≤q` ordering (needed to match `Q_N(a)`'s
ordered-pair domain) via a `Classical.em (p≤q)` case-split, swapping to the
witness `(q,p)` (using `ring` to reconcile `a·q·p=a·p·q`) when `q<p`.

Kernel-verified via the proofsearch MCP:
  episode 01b9f7a0-611b-4f61-8b58-21884e1eeb3c,
  problem_version_id e214ed24-8952-4df8-9b09-0513707791bf.
Outcome: kernel_verified / root_kernel_verified (3rd submission — round 1
used the nonexistent `le_or_lt` identifier [confirmed absent in this pin, a
2nd confirmation of the same lesson from #174 — always use `Classical.em`+
`not_le.mp` for a le-vs-lt split]; round 2 then hit a SELF-INFLICTED
instance of the well-known bare-`:= by tac;`-swallows-chain pitfall, this
time at DOUBLY-NESTED depth — several inner `have e : ... := by ring`
sub-haves were left unparenthesized before further chain within an ALREADY-
parenthesized outer `(by ...)` block, so the bare `by ring` silently
swallowed everything after it as more tactics for its own [already-closed]
goal, producing cascading "No goals to be solved" errors; fixed by
parenthesizing every inner `by` throughout, no matter the nesting depth).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash dbbb40c44f8465dcdb62ac895184a74409b152902d7df3444997296a0ff50696.

**Lean lessons (significant, banked for reuse)**:
(1) `le_or_lt` does NOT exist in this pin — CONFIRMED a second time (first
    seen at #174). Always use `(Classical.em (a≤b))` + `not_le.mp` for a
    le-vs-lt trichotomy split; never guess `le_or_lt`/`lt_or_le` exists.
(2) **Parenthesizing only the OUTER `by`-block is NOT sufficient** — every
    INNER `have h := by tac` with more chain following WITHIN that same
    outer block also needs its own parens, regardless of nesting depth.
    A `have e : T := by ring` nested three levels deep inside an already-
    parenthesized `(by ...)`, if left bare, STILL swallows everything after
    it up to the next unmatched `)`.
-/
import Mathlib

namespace Erdos858

/-- `C_N(a)` domain subset: `{n:π n=a}` is a subset of the union of the
`P_N(a)`/`Q_N(a)` images. The harder half of Stage A for the `C_N=R_N/a`
bijection — needs a WLOG `p≤q` swap for the semiprime case. -/
theorem lemma45_CN_domain_subset :
    ∀ (π : ℕ → ℕ) (N a : ℕ), 1 ≤ a →
      (∀ n : ℕ, n ∈ Finset.Icc 1 N → π n = a →
        (∃ p : ℕ, Nat.Prime p ∧ a < p ∧ n = a * p) ∨ (∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ a < p ∧ a < q ∧ n = a * p * q)) →
      (Finset.Icc 1 N).filter (fun n => π n = a) ⊆
        ((Finset.Icc (a+1) N).filter (fun p => Nat.Prime p ∧ a * p ≤ N)).image (fun p => a * p)
        ∪ (((Finset.Icc (a+1) N) ×ˢ (Finset.Icc (a+1) N)).filter
            (fun pq => Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧ pq.1 ≤ pq.2 ∧ a * (pq.1 * pq.2) ≤ N)).image
            (fun pq => a * pq.1 * pq.2) := by
  intro π N a ha hfwd
  intro n hn
  rw [Finset.mem_filter] at hn
  obtain ⟨hnmem, hpna⟩ := hn
  have hnN : n ≤ N := (Finset.mem_Icc.mp hnmem).2
  rw [Finset.mem_union]
  rcases hfwd n hnmem hpna with ⟨p,hp,hap,hnp⟩ | ⟨p,q,hp,hq,hap,haq,hnpq⟩
  · left
    rw [Finset.mem_image]
    refine ⟨p, ?_, hnp.symm⟩
    rw [Finset.mem_filter, Finset.mem_Icc]
    have hapN : a*p ≤ N := (by rw [← hnp]; exact hnN)
    have h1 : p ≤ a*p := (by nlinarith [ha, hp.pos])
    exact ⟨⟨by omega, by omega⟩, hp, hapN⟩
  · right
    rw [Finset.mem_image]
    rcases Classical.em (p ≤ q) with hpq | hpq
    · refine ⟨(p,q), ?_, hnpq.symm⟩
      rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
      have hapqN : a*p*q ≤ N := (by rw [← hnpq]; exact hnN)
      have e1 : a*(p*q) = a*p*q := (by ring)
      have hapqN' : a*(p*q) ≤ N := (by rw [e1]; exact hapqN)
      have e2 : a*p*q = p*(a*q) := (by ring)
      have h1 : 1 ≤ a*q := (by have h2 := Nat.mul_pos (show 0<a by omega) hq.pos; omega)
      have hp_le : p ≤ a*p*q := (by rw [e2]; nlinarith [h1])
      have e3 : a*p*q = q*(a*p) := (by ring)
      have h3 : 1 ≤ a*p := (by have h4 := Nat.mul_pos (show 0<a by omega) hp.pos; omega)
      have hq_le : q ≤ a*p*q := (by rw [e3]; nlinarith [h3])
      exact ⟨⟨⟨by omega, by omega⟩,⟨by omega, by omega⟩⟩, hp, hq, hpq, hapqN'⟩
    · have hqp : q < p := not_le.mp hpq
      refine ⟨(q,p), ?_, ?_⟩
      · rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
        have hapqN : a*p*q ≤ N := (by rw [← hnpq]; exact hnN)
        have e1 : a*(q*p) = a*p*q := (by ring)
        have hqpN' : a*(q*p) ≤ N := (by rw [e1]; exact hapqN)
        have e3 : a*p*q = q*(a*p) := (by ring)
        have h3 : 1 ≤ a*p := (by have h4 := Nat.mul_pos (show 0<a by omega) hp.pos; omega)
        have hq_le : q ≤ a*p*q := (by rw [e3]; nlinarith [h3])
        have e2 : a*p*q = p*(a*q) := (by ring)
        have h1 : 1 ≤ a*q := (by have h2 := Nat.mul_pos (show 0<a by omega) hq.pos; omega)
        have hp_le : p ≤ a*p*q := (by rw [e2]; nlinarith [h1])
        exact ⟨⟨⟨by omega, by omega⟩,⟨by omega, by omega⟩⟩, hq, hp, by omega, hqpN'⟩
      · have e2 : a*q*p = a*p*q := (by ring)
        have e : a*q*p = n := (by rw [e2]; exact hnpq.symm)
        exact e

end Erdos858
