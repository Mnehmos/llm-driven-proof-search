import Mathlib

/-!
# Erdős #647 — Layer B/C assembly: a multiplicative sum-over-divisors identity

Snapshot of the exact statement + proof term kernel-verified through the
tracked proof-search pipeline on 2026-07-14.

  problem_version_id  d7690fb9-b7a6-433d-8163-5ea7d18e9ad9
  episode_id          f482ac9c-75b0-4b0b-8ffa-98f99afabcab
  root_statement_hash af16bc5cdc5f108e76871b628ae7b5341393a9440c81684a8ec5b37d0993c5e9
  outcome             kernel_verified (root_proved)
  import manifest     ["Mathlib.Tactic.Ring", "Mathlib.Tactic.NormNum", "Mathlib"]

Content: a general (sieve-independent) multiplicative sum-over-divisors
identity — for a `Finset t` of DISTINCT primes and any `f : ℕ → ℝ`:

  `∑_{d1∣∏t} ∏_{p∈d1.primeFactors} f(p) = ∏_{p∈t} (1 + f(p))`

Combined with `selbergTerms_apply` (`selbergTerms(d1) = ν(d1)·∏_{p∈d1.primeFactors}
(1-ν(p))⁻¹`, giving `selbergTerms(d1)/ν(d1) = ∏_{p∈d1.primeFactors}(1-ν(p))⁻¹`),
this gives a CLOSED FORM for the divisor sum
`∑_{d1∣d} selbergTerms(d1)/ν(d1) = ∏_{p∈d.primeFactors}(1+(1-ν(p))⁻¹)` that
`erdos647_lambdaSquared_bound`'s conclusion needs bounded/computed — the
next step toward a concrete `errSum` estimate.

Proof: `Finset.induction_on t`. Base case `t=∅`: both sides are `1`
(empty product/only-divisor-is-1). Inductive step `t=insert p t'`: splits
`(p·M).divisors` (`M:=∏t'`) into `M.divisors ∪ (M.divisors.image (p··))`
— a DISJOINT union since `p` coprime to `M` (any element of the image is
divisible by `p`, while `M.divisors`' elements can't be, else `p∣M`
contradicting coprimality) — then shows the second piece's sum equals
`f(p) · ∑_{d1∣M}(...)` via `Nat.primeFactors_mul` (`(p·b).primeFactors =
insert p b.primeFactors` for `b` coprime to `p`) and `Finset.prod_insert`.
Combining: `∑_{d1∣pM}(...) = (1+f(p))·∑_{d1∣M}(...) = (1+f(p))·∏_{q∈t'}(1+f(q))
= ∏_{q∈insert p t'}(1+f(q))` via the induction hypothesis.

Three Lean fixes across 3 rounds:
1. `rw [Finset.prod_insert hp_notin]` (no explicit function argument) is
   AMBIGUOUS when the goal has TWO separate `∏x∈insert p t', ?g x`-shaped
   occurrences with DIFFERENT `?g` (here: the domain product `∏p∈insert p
   t',p` inside `.divisors` on the LHS, and `∏p∈insert p t',(1+f p)` on
   the RHS) — `rw` silently unified with whichever it found first
   (the LHS one), leaving the RHS untouched and breaking a later `rw`
   that expected the RHS already expanded. Fixed with `conv_lhs =>
   rw[...]` / `conv_rhs => rw[...]` to target each side explicitly.
2. After `simp only [Finset.mem_union, Finset.mem_image, Nat.mem_divisors]`
   fully unfolds an iff-goal (including nested `∃`-bound memberships), a
   LATER `rw [Nat.mem_divisors]` on an already-unfolded sub-goal is a
   redundant no-op (same "already unfolded" pattern seen earlier this
   session in `Erdos647_RemBoundSquarefree.lean`) — fixed by simply
   deleting the redundant calls and working with the already-unfolded
   raw conjunction directly.
3. `Nat.Coprime.dvd_of_dvd_mul_left` expects its coprimality hypothesis
   with the DIVIDING element FIRST (`d1.Coprime p`, matching `d1 ∣ p*n`),
   not `p.Coprime d1` — a `.symm` was needed on the constructed
   coprimality fact to match argument order.
-/

theorem erdos647_divisor_sum_prod_one_add :
    ∀ (t : Finset ℕ), (∀ p ∈ t, p.Prime) → ∀ (f : ℕ → ℝ),
      ∑ d1 ∈ (∏ p ∈ t, p).divisors, ∏ p ∈ d1.primeFactors, f p = ∏ p ∈ t, (1 + f p) := by
  intro t
  induction t using Finset.induction_on with
  | empty => intro f; simp
  | @insert p t' hp_notin ih =>
    intro hp_all f
    have hp_prime : p.Prime := hp_all p (Finset.mem_insert_self p t')
    have ht'_prime : ∀ q ∈ t', q.Prime := fun q hq => hp_all q (Finset.mem_insert_of_mem hq)
    have hM_pos : 0 < ∏ q ∈ t', q := Finset.prod_pos (fun q hq => (ht'_prime q hq).pos)
    have hcop : Nat.Coprime p (∏ q ∈ t', q) := by
      apply Nat.Coprime.prod_right
      intro q hq
      rw [Nat.coprime_primes hp_prime (ht'_prime q hq)]
      intro heq; exact hp_notin (heq ▸ hq)
    conv_lhs => rw [Finset.prod_insert hp_notin]
    conv_rhs => rw [Finset.prod_insert hp_notin]
    rw [← ih ht'_prime f]
    have hMne0 : (∏ q ∈ t', q) ≠ 0 := hM_pos.ne'
    have hpMne0 : (p * ∏ q ∈ t', q) ≠ 0 := Nat.mul_ne_zero hp_prime.pos.ne' hMne0
    have hsplit : (p * ∏ q ∈ t', q).divisors = (∏ q ∈ t', q).divisors ∪ (∏ q ∈ t', q).divisors.image (fun b => p*b) := by
      ext d1
      simp only [Finset.mem_union, Finset.mem_image, Nat.mem_divisors]
      constructor
      · rintro ⟨hdvd, _⟩
        by_cases hpd : p ∣ d1
        · obtain ⟨e, he⟩ := hpd
          right
          refine ⟨e, ⟨?_, hMne0⟩, he.symm⟩
          rw [he] at hdvd
          exact (mul_dvd_mul_iff_left hp_prime.pos.ne').mp hdvd
        · left
          refine ⟨?_, hMne0⟩
          have hcop2 : Nat.Coprime d1 p := ((Nat.Prime.coprime_iff_not_dvd hp_prime).mpr hpd).symm
          exact (Nat.Coprime.dvd_of_dvd_mul_left hcop2 hdvd)
      · rintro (⟨hdvd, _⟩ | ⟨e, ⟨he, _⟩, heq⟩)
        · exact ⟨hdvd.trans ⟨p, by ring⟩, hpMne0⟩
        · rw [← heq]
          exact ⟨mul_dvd_mul_left p he, hpMne0⟩
    rw [hsplit]
    have hdisj : Disjoint ((∏ q ∈ t', q).divisors) ((∏ q ∈ t', q).divisors.image (fun b => p*b)) := by
      apply Finset.disjoint_left.mpr
      intro a ha1 ha2
      simp only [Finset.mem_image] at ha2
      obtain ⟨e, he, heq⟩ := ha2
      have haM : a ∣ (∏ q ∈ t', q) := Nat.dvd_of_mem_divisors ha1
      have hpa : p ∣ a := by rw [← heq]; exact Dvd.intro e rfl
      have hpM : p ∣ (∏ q ∈ t', q) := hpa.trans haM
      exact absurd (Nat.eq_one_of_dvd_coprimes hcop (dvd_refl p) hpM) hp_prime.ne_one
    rw [Finset.sum_union hdisj]
    have hstep2 : ∑ b ∈ (∏ q ∈ t', q).divisors.image (fun b => p*b), ∏ p_1 ∈ b.primeFactors, f p_1
        = f p * ∑ b ∈ (∏ q ∈ t', q).divisors, ∏ p_1 ∈ b.primeFactors, f p_1 := by
      rw [Finset.mul_sum]
      rw [Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro b hb
        have hbM : b ∣ (∏ q ∈ t', q) := Nat.dvd_of_mem_divisors hb
        have hcopb : Nat.Coprime p b := hcop.coprime_dvd_right hbM
        have hbne0 : b ≠ 0 := by
          intro hb0; rw [hb0] at hbM; exact hMne0 (Nat.eq_zero_of_zero_dvd hbM)
        have hpb_pf : (p * b).primeFactors = insert p b.primeFactors := by
          rw [Nat.primeFactors_mul hp_prime.ne_zero hbne0, Nat.Prime.primeFactors hp_prime]
          rfl
        rw [hpb_pf]
        rw [Finset.prod_insert]
        intro hpmem
        have : p ∣ b := Nat.dvd_of_mem_primeFactors hpmem
        exact absurd (Nat.eq_one_of_dvd_coprimes hcopb (dvd_refl p) this) hp_prime.ne_one
      · intro a1 ha1 a2 ha2 heq
        exact Nat.eq_of_mul_eq_mul_left hp_prime.pos heq
    rw [hstep2]
    ring
