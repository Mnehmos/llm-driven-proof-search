/-
Erdős Problem #858 — π-value bridge (Chojecki 2026).

Connects the EXISTENCE+UNIQUENESS characterization of a valid parent (as
proven by `lemma27_pi_ap_full` and `lemma45_pi_apq_full` — which only show
`a⪯n` plus "no `b` strictly between `a` and `n`") to the LITERAL value
`π(n)=a`, using π's ACTUAL maximality axiom.

**This closes a genuine scoping gap** discovered while trying to connect
Lemma 4.5's existence/uniqueness facts to the `C_N(a)` sum identity: the
existence+uniqueness conjunction alone does NOT immediately give `π(n)=a`
without also knowing π is the MAXIMUM valid ancestor. The real Lean form of
π-maximality was found in `Erdos858_ConcretePiAxioms.lean`'s
`concrete_pi_axioms` (3rd conjunct): `z<m → z⪯m → z≤π(m)` — this is the
axiom used abstractly (per that file's own docstring) throughout the §3
frontier-sweep theorems, but had not yet been invoked anywhere in the
Lemma 4.5 connection effort.

Proof: maximality gives `a≤π(n)`. If `a=π(n)`, done. If `a<π(n)` strictly,
the sandwich lemma (`lemma21_sandwich`, `Erdos858_Lemma21_Sandwich.lean` —
`a⪯n,b⪯n,a<b<n⟹a⪯b`) applied at `a,π(n),n` gives `a⪯π(n)`; then the
uniqueness hypothesis applied at `b:=π(n)` (using `a⪯π(n)` just derived and
`π(n)⪯n` from soundness) gives `π(n)=a∨π(n)=n`; the second disjunct
contradicts `π(n)<n` (the standard range axiom), leaving `π(n)=a`.

This is fully GENERIC (no dependence on the `a·p`/`a·p·q` shape) — it
applies uniformly to BOTH `lemma27_pi_ap_full` (instantiated with its
existence+uniqueness halves) and `lemma45_pi_apq_full`, giving the literal
`π(a·p)=a` and `π(a·p·q)=a` facts needed for the `C_N(a)=R_N(a)/a`
Finset-bijection.

Uses `proof_format=raw_lean_block` for the nested `rcases` bullets.

Kernel-verified via the proofsearch MCP:
  episode 7fd275b1-6f91-4b0c-8cee-dce0fb9f244d,
  problem_version_id 4a3ec5df-bfb9-4ecc-874d-07d3a5705edf.
Outcome: kernel_verified / root_kernel_verified (1st submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 02b57d69ed11b74f36a09e4231bbd57db4745ffc60b875cced9c2d8b74d4ac13.
-/
import Mathlib

namespace Erdos858

/-- π-value bridge: existence (`a⪯n`) + uniqueness (no `b` strictly between)
+ soundness (`π(n)⪯n`) + range (`π(n)<n`) + maximality (`z<m∧z⪯m→z≤π(m)`) +
the sandwich lemma together give the literal `π(n)=a`. Generic — applies to
both `π(a·p)=a` and `π(a·p·q)=a`. -/
theorem pi_value_bridge :
    ∀ (π : ℕ → ℕ) (a n : ℕ), a < n →
      (∃ t : ℕ, n = a * t ∧ ∀ p : ℕ, Nat.Prime p → p ∣ t → a < p) →
      (∀ b : ℕ, (∃ t : ℕ, b = a * t ∧ ∀ p : ℕ, Nat.Prime p → p ∣ t → a < p) →
        (∃ t : ℕ, n = b * t ∧ ∀ p : ℕ, Nat.Prime p → p ∣ t → b < p) → b = a ∨ b = n) →
      (∃ t : ℕ, n = π n * t ∧ ∀ p : ℕ, Nat.Prime p → p ∣ t → π n < p) →
      π n < n →
      (∀ z m : ℕ, z < m → (∃ t : ℕ, m = z * t ∧ ∀ p : ℕ, Nat.Prime p → p ∣ t → z < p) → z ≤ π m) →
      (∀ a' b' n' : ℕ, a' < b' → b' < n' →
        (∃ u : ℕ, n' = a' * u ∧ ∀ p : ℕ, Nat.Prime p → p ∣ u → a' < p) →
        (∃ v : ℕ, n' = b' * v ∧ ∀ p : ℕ, Nat.Prime p → p ∣ v → b' < p) →
        ∃ t : ℕ, b' = a' * t ∧ ∀ p : ℕ, Nat.Prime p → p ∣ t → a' < p) →
      π n = a := by
  intro π a n han hex huniq hsound hrange hmax hsandwich
  have hale : a ≤ π n := hmax a n han hex
  rcases hale.lt_or_eq with hlt | heq
  · have hasand : ∃ t : ℕ, π n = a*t ∧ ∀ p : ℕ, Nat.Prime p → p ∣ t → a < p := hsandwich a (π n) n hlt hrange hex hsound
    rcases huniq (π n) hasand hsound with h1 | h1
    · exact h1
    · exfalso
      omega
  · exact heq.symm

end Erdos858
