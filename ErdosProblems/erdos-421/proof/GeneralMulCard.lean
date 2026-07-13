/-
Stepping-stone toward Selfridge's construction (Erdos Problem #786,
erdos_786.parts.i.selfridge in google-deepmind/formal-conjectures, still
`sorry` there). Generalizes the density-1/4 result's multiplicity-one
argument from one prime to an arbitrary finite set of primes.

Snapshot reconstructed from proofsearch MCP episode 318d5fcd-17af-4688-8f15-f4437dbdc4ce,
problem_version_id a9f3f35b-7495-44ba-a62b-78a5dc96be0b. Kernel-verified on
the first submission attempt.
-/

/-- If every element of `c` is divisible by exactly one prime in `S` (to
the first power -- i.e. its `S`-factorization exponents sum to `1`), then
the total `S`-factorization-exponent-sum of `c`'s product equals `c.card`. -/
theorem sum_factorization_prod_eq_card (S : Finset ℕ) (c : Finset ℕ)
    (hc : ∀ n ∈ c, (∑ q ∈ S, n.factorization q) = 1) (hcne : ∀ n ∈ c, n ≠ 0) :
    ∑ q ∈ S, (c.prod id).factorization q = c.card := by
  have step1 : ∀ q ∈ S, (c.prod id).factorization q = ∑ n ∈ c, n.factorization q :=
    fun q _ => Nat.factorization_prod_apply hcne
  rw [Finset.sum_congr rfl step1, Finset.sum_comm, Finset.sum_congr rfl hc]
  simp

/-- Multiplicity-one for an arbitrary finite set of primes `S`: if `a, b`
are finite sets of naturals each divisible by exactly one prime of `S`
(the set `A_S = {n | ∑_{q∈S} n.factorization q = 1}` from Selfridge's
construction), and `a`, `b` have the same product, then `a.card = b.card`.
This is the ℕ-specialization of the corpus's `Set.IsMulCardSet A_S`. -/
theorem general_mulCard (S : Finset ℕ) (a b : Finset ℕ)
    (ha : ∀ n ∈ a, (∑ q ∈ S, n.factorization q) = 1)
    (hb : ∀ n ∈ b, (∑ q ∈ S, n.factorization q) = 1)
    (hab : a.prod id = b.prod id) : a.card = b.card := by
  have hane : ∀ n ∈ a, n ≠ 0 := by
    intro n hn hn0
    have h1 := ha n hn
    rw [hn0, Nat.factorization_zero] at h1
    simp at h1
  have hbne : ∀ n ∈ b, n ≠ 0 := by
    intro n hn hn0
    have h1 := hb n hn
    rw [hn0, Nat.factorization_zero] at h1
    simp at h1
  have hka := sum_factorization_prod_eq_card S a ha hane
  have hkb := sum_factorization_prod_eq_card S b hb hbne
  rw [hab] at hka
  exact hka.symm.trans hkb

/-
What this does NOT establish: Selfridge's actual density-1/e-epsilon claim
(erdos_786.parts.i.selfridge) additionally needs, for a suitable finite set
of consecutive primes S starting at a sufficiently large prime p:
  1. Existence of the cutoff k (sum of first k+1 reciprocals crosses 1) --
     tractable via Mathlib's `Nat.Primes.not_summable_one_div` /
     `not_summable_one_div_on_primes` (divergence of the prime harmonic
     series forces partial sums unbounded).
  2. A Mertens-third-theorem-style asymptotic: as the starting prime p ->
     infinity, prod_{q in S} (1 - 1/q) -> e^{-1}, given sum_{q in S} 1/q is
     held near 1 and each individual 1/q -> 0. No ready-made Mathlib lemma
     for this was found (searched Mathlib/NumberTheory for "Mertens";
     nothing). This is a genuinely deep analytic-number-theory estimate
     (needs log/exp Taylor-remainder bounds plus a tail estimate on
     sum 1/q^2 for primes q >= p) and represents the real, substantial,
     multi-session remaining blocker toward a from-scratch Lean proof of
     erdos_786.parts.i.selfridge -- not this multiplicity lemma.
-/
