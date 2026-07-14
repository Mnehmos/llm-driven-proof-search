import Mathlib

/-!
# Erdős #647 — Layer C: concrete closed form for ∑_{d1∣d} selbergTerms(d1)/ν(d1)

Snapshot of the exact statement + proof term kernel-verified through the
tracked proof-search pipeline on 2026-07-14.

  problem_version_id  3744be83-afb4-410d-812c-81a30e4489a1
  episode_id          15a98239-1c67-4401-bad5-90e23b8b0a6f
  root_statement_hash 671c2fbe21a2d48baeac91eac51a31551e70b5d36afd7930c0c59d9a17127488
  outcome             kernel_verified (root_proved)
  import manifest     ["Mathlib.Tactic.Ring", "Mathlib.Tactic.NormNum", "Mathlib"]

Content: for any `s : SelbergSieve` and `d ∈ s.prodPrimes.divisors`:

  `∑_{d1∣d} selbergTerms(d1)/ν(d1) = ∏_{p∈d.primeFactors} (1+(1-ν(p))⁻¹)`

This makes `erdos647_lambdaSquared_bound`'s bound
(`|lambdaSquared w d| ≤ (∑_{d1∣d}selbergTerms(d1)/ν(d1))²`) fully concrete
— the next piece toward bounding `BoundingSieve.errSum`.

Since cross-submission references don't work, this submission inlines a
specialized copy of `erdos647_divisor_sum_prod_one_add`'s general identity
(`∑_{d1∣∏t} ∏_{p∈d1.primeFactors} f(p) = ∏_{p∈t}(1+f(p))` for a Finset `t`
of distinct primes and any `f`) as a local `have`, instantiated with
`t := d.primeFactors` and `f(p) := (1-ν(p))⁻¹`. `d = ∏_{p∈d.primeFactors}p`
comes from `Nat.prod_primeFactors_of_squarefree` (`d` squarefree since it
divides `s.prodPrimes`, which is squarefree by the `SelbergSieve`/
`BoundingSieve` structure). Each term `selbergTerms(d1)/ν(d1)` is then
converted to `∏_{p∈d1.primeFactors}(1-ν(p))⁻¹` via Mathlib's
`selbergTerms_apply` (`selbergTerms(d1) = ν(d1)·∏_{p∈d1.primeFactors}
(1-ν(p))⁻¹`) divided through by `ν(d1) ≠ 0` (`BoundingSieve.
nu_pos_of_dvd_prodPrimes`, valid since `d1∣d∣s.prodPrimes`).

One care point avoiding a self-referential rewrite (a recurring bug class
this campaign): the auxiliary equality
`∑_{d1∣d} ∏_{p∈d1.primeFactors} f(p) = ∏_{p∈d.primeFactors}(1+f(p))` needs
`d.divisors` rewritten to `(∏_{p∈d.primeFactors}p).divisors` on ONLY the
LHS — a plain `rw [← hdeq]` on the full goal would also corrupt the RHS's
own `d.primeFactors` occurrence (which itself contains `d`), so
`conv_lhs => rw [← hdeq]` is used instead to scope the rewrite.
-/

theorem erdos647_divisor_sum_selbergTerms_div_nu :
    ∀ (s : SelbergSieve) (d : ℕ), d ∈ s.prodPrimes.divisors →
      ∑ d1 ∈ d.divisors, s.selbergTerms d1 / s.nu d1 = ∏ p ∈ d.primeFactors, (1 + (1 - s.nu p)⁻¹) := by
  intro s d hd
  have hdvdN : d ∣ s.prodPrimes := Nat.dvd_of_mem_divisors hd
  have hdsqfree : Squarefree d := Squarefree.squarefree_of_dvd hdvdN s.prodPrimes_squarefree
  have hdeq : (∏ p ∈ d.primeFactors, p) = d := Nat.prod_primeFactors_of_squarefree hdsqfree
  have hp_all : ∀ p ∈ d.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have hgeneral : ∀ (t : Finset ℕ), (∀ p ∈ t, p.Prime) → ∀ (f : ℕ → ℝ),
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
  have hsum_eq : ∑ d1 ∈ d.divisors, ∏ p ∈ d1.primeFactors, (1 - s.nu p)⁻¹ = ∏ p ∈ d.primeFactors, (1 + (1 - s.nu p)⁻¹) := by
    conv_lhs => rw [← hdeq]
    exact hgeneral d.primeFactors hp_all (fun p => (1 - s.nu p)⁻¹)
  rw [← hsum_eq]
  apply Finset.sum_congr rfl
  intro d1 hd1
  rw [Nat.mem_divisors] at hd1
  have hd1dvdN : d1 ∣ s.prodPrimes := hd1.1.trans hdvdN
  have hnud1pos : 0 < s.nu d1 := BoundingSieve.nu_pos_of_dvd_prodPrimes hd1dvdN
  rw [s.selbergTerms_apply]
  rw [mul_comm, mul_div_assoc, div_self (ne_of_gt hnud1pos), mul_one]
