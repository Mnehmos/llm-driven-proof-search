/-
Erdős Problem #858 — Lemma 4.5 connection, `C_N(a)` domain superset (Chojecki 2026).

The easier ("reverse") half of the `C_N(a)=R_N(a)/a` Finset-bijection's
Stage A: the union of the `P_N(a)`-image (`a·p` for valid primes `p`) and
`Q_N(a)`-image (`a·p·q` for valid ORDERED prime pairs `p≤q`) is a SUBSET of
the `π(n)=a` filter set. Uses `literal_pi_value_ap`/`literal_pi_value_apq`
(`Erdos858_LiteralPiValueAp.lean`/`Erdos858_LiteralPiValueApq.lean`, taken
as hypotheses `hrevap`/`hrevapq`) directly — no case-split needed since the
domain sets already carry the `p≤q` ordering matching `hrevapq`'s argument
order (matches `Erdos858_Prop46_PNMonotone.lean`/`QNMonotone.lean`'s EXACT
domains).

Proof: destructure `union`/`image`/`filter` memberships explicitly via
`rw`+`obtain` (not `simp`+`rintro`, for a predictable pattern), then apply
`hrevap`/`hrevapq` directly.

Kernel-verified via the proofsearch MCP:
  episode 06c8cdc9-3daf-43db-be56-89ebd428e61e,
  problem_version_id 2b4c4863-25a1-4c53-9d57-2417d190015b.
Outcome: kernel_verified / root_kernel_verified (3rd submission — round 1
hit a genuine `nlinarith` degree-3-product limitation (`1≤a*p*q` from three
separate `≥1` facts needs an explicit `Nat.mul_pos` chain, not a bare
`nlinarith` hint list); round 2 then hit a SUBTLER issue, documented below.
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash bba4e0a15ea49b31071343806ac336eb5bce398a978b11f3537864f52fcfb693.

**Lean lessons (significant, banked for reuse)**:
(1) `nlinarith`'s default search does not reach DEGREE-3 products (e.g.
    `1≤a*p*q` from `1≤a,1≤p,1≤q`) even with explicit `.pos` hints for each
    factor — decompose into two chained `Nat.mul_pos` calls (degree-2 each)
    instead of hoping `nlinarith` finds the triple combination.
(2) **After `obtain ⟨⟨p,q⟩, ...⟩ := hn` destructures a `Finset.mem_image`
    witness of PRODUCT type, hypotheses whose ORIGINAL statement mentioned
    the bound pair variable's `.1`/`.2` projections remain in UNREDUCED
    `(p,q).1`/`(p,q).2` form** — even though defeq to `p`/`q`. Term
    application (passing such a hypothesis as a function argument) and
    `ring`/`exact` tolerate the defeq silently, but `omega`/`nlinarith`
    treat the unreduced projection as a DIFFERENT OPAQUE ATOM from the
    clean variable, breaking any attempt to relate the two. Fix: immediately
    re-type EVERY such hypothesis via an explicit type-ascribed `have`
    (`have hclean : CleanStatement := hOriginal`, defeq-checked) right after
    the `obtain`, before any `omega`/`nlinarith` call that needs to relate
    it to clean-variable goals.
-/
import Mathlib

namespace Erdos858

/-- `C_N(a)` domain superset: the union of the `P_N(a)`/`Q_N(a)` images is a
subset of `{n:π n=a}`. The easier half of Stage A for the `C_N=R_N/a`
bijection. -/
theorem lemma45_CN_domain_supset :
    ∀ (π : ℕ → ℕ) (N a : ℕ), 1 ≤ a →
      (∀ p : ℕ, Nat.Prime p → a < p → π (a * p) = a) →
      (∀ p q : ℕ, Nat.Prime p → Nat.Prime q → a < p → a < q → π (a * p * q) = a) →
      (((Finset.Icc (a+1) N).filter (fun p => Nat.Prime p ∧ a * p ≤ N)).image (fun p => a * p)
        ∪ (((Finset.Icc (a+1) N) ×ˢ (Finset.Icc (a+1) N)).filter
            (fun pq => Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧ pq.1 ≤ pq.2 ∧ a * (pq.1 * pq.2) ≤ N)).image
            (fun pq => a * pq.1 * pq.2))
        ⊆ (Finset.Icc 1 N).filter (fun n => π n = a) := by
  intro π N a ha hrevap hrevapq
  intro n hn
  rw [Finset.mem_union] at hn
  rw [Finset.mem_filter, Finset.mem_Icc]
  rcases hn with hn | hn
  · rw [Finset.mem_image] at hn
    obtain ⟨p, hpmem, hpn⟩ := hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hpmem
    obtain ⟨⟨hap1, hpN⟩, hp, hapN⟩ := hpmem
    rw [← hpn]
    refine ⟨⟨?_, hapN⟩, hrevap p hp (by omega)⟩
    nlinarith [ha, hp.pos]
  · rw [Finset.mem_image] at hn
    obtain ⟨⟨p,q⟩, hpqmem, hpqn0⟩ := hn
    have hpqn : a*p*q = n := hpqn0
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hpqmem
    obtain ⟨⟨⟨hap10,hpN0⟩,⟨haq10,hqN0⟩⟩, hp0, hq0, hpq0, hapqN0⟩ := hpqmem
    have hap1 : a+1 ≤ p := hap10
    have hpN : p ≤ N := hpN0
    have haq1 : a+1 ≤ q := haq10
    have hqN : q ≤ N := hqN0
    have hp : Nat.Prime p := hp0
    have hq : Nat.Prime q := hq0
    have hpq : p ≤ q := hpq0
    have hapqN : a*(p*q) ≤ N := hapqN0
    have hapqN' : a*p*q ≤ N := (by have e : a*p*q = a*(p*q) := (by ring); rw [e]; exact hapqN)
    have hpos : 0 < a*p*q := (by have h1 : 0 < a*p := Nat.mul_pos (by omega) hp.pos; exact Nat.mul_pos h1 hq.pos)
    rw [← hpqn]
    refine ⟨⟨by omega, hapqN'⟩, hrevapq p q hp hq (by omega) (by omega)⟩

end Erdos858
