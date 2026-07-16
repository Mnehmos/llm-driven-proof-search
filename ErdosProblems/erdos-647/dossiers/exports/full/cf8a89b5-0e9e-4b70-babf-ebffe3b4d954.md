# ⚠️ KERNEL-VERIFIED FORMAL STATEMENT — FIDELITY NOT YET VERIFIED — Erdos #647 closing route: turn the optimal weight pointwise estimate and uniform per-prime Selberg factor bound 4 into |lambdaSquared(w)(d)| <= 16^omega(d).

> This proof establishes:
>
> `∀ (s : SelbergSieve) (w : ℕ → ℝ),
      (∀ d ∈ s.prodPrimes.divisors, |w d| ≤ s.selbergTerms d / s.nu d) →
      (∀ p ∈ s.prodPrimes.primeFactors, 1 + (1 - s.nu p)⁻¹ ≤ 4) →
      ∀ d ∈ s.prodPrimes.divisors,
        |BoundingSieve.lambdaSquared w d| ≤ (16:ℝ)^d.primeFactors.card`
>
> It does **not yet** certify the source claim above.

**Root goal (formal):** `∀ (s : SelbergSieve) (w : ℕ → ℝ),
      (∀ d ∈ s.prodPrimes.divisors, |w d| ≤ s.selbergTerms d / s.nu d) →
      (∀ p ∈ s.prodPrimes.primeFactors, 1 + (1 - s.nu p)⁻¹ ≤ 4) →
      ∀ d ∈ s.prodPrimes.divisors,
        |BoundingSieve.lambdaSquared w d| ≤ (16:ℝ)^d.primeFactors.card`

| Proof soundness | Statement fidelity | Canonical promotion | Training eligibility |
|---|---|---|---|
| VERIFIED | ATTESTED (unsafe_dev_attestation — not reviewed) | BLOCKED | QUARANTINED |

| episode | state | steps | budget left (μ$) | started | finished |
|---|---|---|---|---|---|
| `cf8a89b5-0e9e-4b70-babf-ebffe3b4d954` | terminated (root_proved) | 2 | — | 2026-07-15T19:16:23 | 2026-07-15T19:17:49 |

## Proof tree

- ✅ **root_theorem** : `∀ (s : SelbergSieve) (w : ℕ → ℝ),
      (∀ d ∈ s.prodPrimes.divisors, |w d| ≤ s.selbergTerms d / s.nu d) →
      (∀ p ∈ s.prodPrimes.primeFactors, 1 + (1 - s.nu p)⁻¹ ≤ 4) →
      ∀ d ∈ s.prodPrimes.divisors,
        |BoundingSieve.lambdaSquared w d| ≤ (16:ℝ)^d.primeFactors.card`

## The proof, assembled

```lean
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib

theorem root_theorem : ∀ (s : SelbergSieve) (w : ℕ → ℝ),
      (∀ d ∈ s.prodPrimes.divisors, |w d| ≤ s.selbergTerms d / s.nu d) →
      (∀ p ∈ s.prodPrimes.primeFactors, 1 + (1 - s.nu p)⁻¹ ≤ 4) →
      ∀ d ∈ s.prodPrimes.divisors,
        |BoundingSieve.lambdaSquared w d| ≤ (16:ℝ)^d.primeFactors.card := by

  intro s w hw hcoeff
  have hNne0 : s.prodPrimes ≠ 0 := s.prodPrimes_squarefree.ne_zero
  have hlambda_bound : ∀ d ∈ s.prodPrimes.divisors, |BoundingSieve.lambdaSquared w d| ≤ (∑ d1 ∈ d.divisors, s.selbergTerms d1 / s.nu d1)^2 := by
    intro d hd
    have hdvdN : d ∣ s.prodPrimes := Nat.dvd_of_mem_divisors hd
    have hwd : ∀ d1 ∈ d.divisors, |w d1| ≤ s.selbergTerms d1 / s.nu d1 := by
      intro d1 hd1
      have hd1dvd : d1 ∣ d := Nat.dvd_of_mem_divisors hd1
      exact hw d1 (Nat.mem_divisors.mpr ⟨hd1dvd.trans hdvdN, hNne0⟩)
    have hstep : |BoundingSieve.lambdaSquared w d| ≤ ∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors, |w d1| * |w d2| := by
      unfold BoundingSieve.lambdaSquared
      calc |∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors, if d = Nat.lcm d1 d2 then w d1 * w d2 else 0|
          ≤ ∑ d1 ∈ d.divisors, |∑ d2 ∈ d.divisors, if d = Nat.lcm d1 d2 then w d1 * w d2 else 0| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors, |if d = Nat.lcm d1 d2 then w d1 * w d2 else 0| := by
            apply Finset.sum_le_sum
            intro d1 _
            exact Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors, |w d1| * |w d2| := by
            apply Finset.sum_le_sum
            intro d1 _
            apply Finset.sum_le_sum
            intro d2 _
            split_ifs with h
            · rw [abs_mul]
            · rw [abs_zero]; positivity
    have heq : (∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors, |w d1| * |w d2|) = (∑ d1 ∈ d.divisors, |w d1|) * (∑ d2 ∈ d.divisors, |w d2|) := by
      rw [Finset.sum_mul_sum]
    have hsum_le : (∑ d1 ∈ d.divisors, |w d1|) ≤ ∑ d1 ∈ d.divisors, s.selbergTerms d1 / s.nu d1 :=
      Finset.sum_le_sum hwd
    have hsum_nonneg : 0 ≤ ∑ d1 ∈ d.divisors, |w d1| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    calc |BoundingSieve.lambdaSquared w d| ≤ ∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors, |w d1| * |w d2| := hstep
      _ = (∑ d1 ∈ d.divisors, |w d1|) * (∑ d2 ∈ d.divisors, |w d2|) := heq
      _ = (∑ d1 ∈ d.divisors, |w d1|)^2 := by rw [sq]
      _ ≤ (∑ d1 ∈ d.divisors, s.selbergTerms d1 / s.nu d1)^2 := pow_le_pow_left₀ hsum_nonneg hsum_le 2
  have hclosed_form : ∀ d ∈ s.prodPrimes.divisors, ∑ d1 ∈ d.divisors, s.selbergTerms d1 / s.nu d1 = ∏ p ∈ d.primeFactors, (1 + (1 - s.nu p)⁻¹) := by
    intro d hd
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
  intro d hd
  have hdvdN : d ∣ s.prodPrimes := Nat.dvd_of_mem_divisors hd
  have hfactor_nonneg : ∀ p ∈ d.primeFactors,
      0 ≤ 1 + (1 - s.nu p)⁻¹ := by
    intro p hp
    have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpdvdN : p ∣ s.prodPrimes := (Nat.dvd_of_mem_primeFactors hp).trans hdvdN
    have hnult : s.nu p < 1 := s.nu_lt_one_of_prime p hpprime hpdvdN
    have hpos : 0 < (1 - s.nu p)⁻¹ := inv_pos.mpr (by linarith)
    linarith
  have hfac : (∏ p ∈ d.primeFactors, (1 + (1 - s.nu p)⁻¹)) ≤
      (4:ℝ)^d.primeFactors.card := by
    calc
      (∏ p ∈ d.primeFactors, (1 + (1 - s.nu p)⁻¹)) ≤
          ∏ p ∈ d.primeFactors, (4:ℝ) := by
        apply Finset.prod_le_prod hfactor_nonneg
        intro p hp
        exact hcoeff p (Nat.primeFactors_mono hdvdN hNne0 hp)
      _ = (4:ℝ)^d.primeFactors.card := by simp
  have hfac_nonneg : 0 ≤ (∏ p ∈ d.primeFactors, (1 + (1 - s.nu p)⁻¹)) := by
    apply Finset.prod_nonneg
    exact hfactor_nonneg
  calc
    |BoundingSieve.lambdaSquared w d| ≤
        (∑ d1 ∈ d.divisors, s.selbergTerms d1 / s.nu d1)^2 :=
      hlambda_bound d hd
    _ = (∏ p ∈ d.primeFactors, (1 + (1 - s.nu p)⁻¹))^2 := by
      rw [hclosed_form d hd]
    _ ≤ ((4:ℝ)^d.primeFactors.card)^2 :=
      pow_le_pow_left₀ hfac_nonneg hfac 2
    _ = (16:ℝ)^d.primeFactors.card := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num

```

## How it went — every attempt, in order

| # | obligation | action | detail | verdict |
|---|---|---|---|---|
| 2 | `root_theorem` | solve | `intro s w hw hcoeff ;   have hNne0 : s.prodPrimes ≠ 0 := s.prodPrimes_squarefree.ne_zero ;   have hlambda_bound : ∀ d ∈ s.prodPrimes.divisors, \|BoundingSieve.lambdaSquared w d\| ≤ (∑ d1 ∈ d.divisors, s.selbergTerms d1 / s.nu d1)^2 := by ;     intro d hd ;     have hdvdN : d ∣ s.prodPrimes := Nat.dvd_of_mem_divisors hd ;     have hwd : ∀ d1 ∈ d.divisors, \|w d1\| ≤ s.selbergTerms d1 / s.nu d1 := by ;       intro d1 hd1 ;       have hd1dvd : d1 ∣ d := Nat.dvd_of_mem_divisors hd1 ;       exact hw d1 (Nat.mem_divisors.mpr ⟨hd1dvd.trans hdvdN, hNne0⟩) ;     have hstep : \|BoundingSieve.lambdaSquared w d\| ≤ ∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors, \|w d1\| * \|w d2\| := by ;       unfold BoundingSieve.lambdaSquared ;       calc \|∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors, if d = Nat.lcm d1 d2 then w d1 * w d2 else 0\| ;           ≤ ∑ d1 ∈ d.divisors, \|∑ d2 ∈ d.divisors, if d = Nat.lcm d1 d2 then w d1 * w d2 else 0\| := Finset.abs_sum_le_sum_abs _ _ ;         _ ≤ ∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors, \|if d = Nat.lcm d1 d2 then w d1 * w d2 else 0\| := by ;             apply Finset.sum_le_sum ;             intro d1 _ ;             exact Finset.abs_sum_le_sum_abs _ _ ;         _ ≤ ∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors, \|w d1\| * \|w d2\| := by ;             apply Finset.sum_le_sum ;             intro d1 _ ;             apply Finset.sum_le_sum ;             intro d2 _ ;             split_ifs with h ;             · rw [abs_mul] ;             · rw [abs_zero]; positivity ;     have heq : (∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors, \|w d1\| * \|w d2\|) = (∑ d1 ∈ d.divisors, \|w d1\|) * (∑ d2 ∈ d.divisors, \|w d2\|) := by ;       rw [Finset.sum_mul_sum] ;     have hsum_le : (∑ d1 ∈ d.divisors, \|w d1\|) ≤ ∑ d1 ∈ d.divisors, s.selbergTerms d1 / s.nu d1 := ;       Finset.sum_le_sum hwd ;     have hsum_nonneg : 0 ≤ ∑ d1 ∈ d.divisors, \|w d1\| := Finset.sum_nonneg (fun _ _ => abs_nonneg _) ;     calc \|BoundingSieve.lambdaSquared w d\| ≤ ∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors, \|w d1\| * \|w d2\| := hstep ;       _ = (∑ d1 ∈ d.divisors, \|w d1\|) * (∑ d2 ∈ d.divisors, \|w d2\|) := heq ;       _ = (∑ d1 ∈ d.divisors, \|w d1\|)^2 := by rw [sq] ;       _ ≤ (∑ d1 ∈ d.divisors, s.selbergTerms d1 / s.nu d1)^2 := pow_le_pow_left₀ hsum_nonneg hsum_le 2 ;   have hclosed_form : ∀ d ∈ s.prodPrimes.divisors, ∑ d1 ∈ d.divisors, s.selbergTerms d1 / s.nu d1 = ∏ p ∈ d.primeFactors, (1 + (1 - s.nu p)⁻¹) := by ;     intro d hd ;     have hdvdN : d ∣ s.prodPrimes := Nat.dvd_of_mem_divisors hd ;     have hdsqfree : Squarefree d := Squarefree.squarefree_of_dvd hdvdN s.prodPrimes_squarefree ;     have hdeq : (∏ p ∈ d.primeFactors, p) = d := Nat.prod_primeFactors_of_squarefree hdsqfree ;     have hp_all : ∀ p ∈ d.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp ;     have hgeneral : ∀ (t : Finset ℕ), (∀ p ∈ t, p.Prime) → ∀ (f : ℕ → ℝ), ;         ∑ d1 ∈ (∏ p ∈ t, p).divisors, ∏ p ∈ d1.primeFactors, f p = ∏ p ∈ t, (1 + f p) := by ;       intro t ;       induction t using Finset.induction_on with ;       \| empty => intro f; simp ;       \| @insert p t' hp_notin ih => ;         intro hp_all f ;         have hp_prime : p.Prime := hp_all p (Finset.mem_insert_self p t') ;         have ht'_prime : ∀ q ∈ t', q.Prime := fun q hq => hp_all q (Finset.mem_insert_of_mem hq) ;         have hM_pos : 0 < ∏ q ∈ t', q := Finset.prod_pos (fun q hq => (ht'_prime q hq).pos) ;         have hcop : Nat.Coprime p (∏ q ∈ t', q) := by ;           apply Nat.Coprime.prod_right ;           intro q hq ;           rw [Nat.coprime_primes hp_prime (ht'_prime q hq)] ;           intro heq; exact hp_notin (heq ▸ hq) ;         conv_lhs => rw [Finset.prod_insert hp_notin] ;         conv_rhs => rw [Finset.prod_insert hp_notin] ;         rw [← ih ht'_prime f] ;         have hMne0 : (∏ q ∈ t', q) ≠ 0 := hM_pos.ne' ;         have hpMne0 : (p * ∏ q ∈ t', q) ≠ 0 := Nat.mul_ne_zero hp_prime.pos.ne' hMne0 ;         have hsplit : (p * ∏ q ∈ t', q).divisors = (∏ q ∈ t', q).divisors ∪ (∏ q ∈ t', q).divisors.image (fun b => p*b) := by ;           ext d1 ;           simp only [Finset.mem_union, Finset.mem_image, Nat.mem_divisors] ;           constructor ;           · rintro ⟨hdvd, _⟩ ;             by_cases hpd : p ∣ d1 ;             · obtain ⟨e, he⟩ := hpd ;               right ;               refine ⟨e, ⟨?_, hMne0⟩, he.symm⟩ ;               rw [he] at hdvd ;               exact (mul_dvd_mul_iff_left hp_prime.pos.ne').mp hdvd ;             · left ;               refine ⟨?_, hMne0⟩ ;               have hcop2 : Nat.Coprime d1 p := ((Nat.Prime.coprime_iff_not_dvd hp_prime).mpr hpd).symm ;               exact (Nat.Coprime.dvd_of_dvd_mul_left hcop2 hdvd) ;           · rintro (⟨hdvd, _⟩ \| ⟨e, ⟨he, _⟩, heq⟩) ;             · exact ⟨hdvd.trans ⟨p, by ring⟩, hpMne0⟩ ;             · rw [← heq] ;               exact ⟨mul_dvd_mul_left p he, hpMne0⟩ ;         rw [hsplit] ;         have hdisj : Disjoint ((∏ q ∈ t', q).divisors) ((∏ q ∈ t', q).divisors.image (fun b => p*b)) := by ;           apply Finset.disjoint_left.mpr ;           intro a ha1 ha2 ;           simp only [Finset.mem_image] at ha2 ;           obtain ⟨e, he, heq⟩ := ha2 ;           have haM : a ∣ (∏ q ∈ t', q) := Nat.dvd_of_mem_divisors ha1 ;           have hpa : p ∣ a := by rw [← heq]; exact Dvd.intro e rfl ;           have hpM : p ∣ (∏ q ∈ t', q) := hpa.trans haM ;           exact absurd (Nat.eq_one_of_dvd_coprimes hcop (dvd_refl p) hpM) hp_prime.ne_one ;         rw [Finset.sum_union hdisj] ;         have hstep2 : ∑ b ∈ (∏ q ∈ t', q).divisors.image (fun b => p*b), ∏ p_1 ∈ b.primeFactors, f p_1 ;             = f p * ∑ b ∈ (∏ q ∈ t', q).divisors, ∏ p_1 ∈ b.primeFactors, f p_1 := by ;           rw [Finset.mul_sum] ;           rw [Finset.sum_image] ;           · apply Finset.sum_congr rfl ;             intro b hb ;             have hbM : b ∣ (∏ q ∈ t', q) := Nat.dvd_of_mem_divisors hb ;             have hcopb : Nat.Coprime p b := hcop.coprime_dvd_right hbM ;             have hbne0 : b ≠ 0 := by ;               intro hb0; rw [hb0] at hbM; exact hMne0 (Nat.eq_zero_of_zero_dvd hbM) ;             have hpb_pf : (p * b).primeFactors = insert p b.primeFactors := by ;               rw [Nat.primeFactors_mul hp_prime.ne_zero hbne0, Nat.Prime.primeFactors hp_prime] ;               rfl ;             rw [hpb_pf] ;             rw [Finset.prod_insert] ;             intro hpmem ;             have : p ∣ b := Nat.dvd_of_mem_primeFactors hpmem ;             exact absurd (Nat.eq_one_of_dvd_coprimes hcopb (dvd_refl p) this) hp_prime.ne_one ;           · intro a1 ha1 a2 ha2 heq ;             exact Nat.eq_of_mul_eq_mul_left hp_prime.pos heq ;         rw [hstep2] ;         ring ;     have hsum_eq : ∑ d1 ∈ d.divisors, ∏ p ∈ d1.primeFactors, (1 - s.nu p)⁻¹ = ∏ p ∈ d.primeFactors, (1 + (1 - s.nu p)⁻¹) := by ;       conv_lhs => rw [← hdeq] ;       exact hgeneral d.primeFactors hp_all (fun p => (1 - s.nu p)⁻¹) ;     rw [← hsum_eq] ;     apply Finset.sum_congr rfl ;     intro d1 hd1 ;     rw [Nat.mem_divisors] at hd1 ;     have hd1dvdN : d1 ∣ s.prodPrimes := hd1.1.trans hdvdN ;     have hnud1pos : 0 < s.nu d1 := BoundingSieve.nu_pos_of_dvd_prodPrimes hd1dvdN ;     rw [s.selbergTerms_apply] ;     rw [mul_comm, mul_div_assoc, div_self (ne_of_gt hnud1pos), mul_one] ;   intro d hd ;   have hdvdN : d ∣ s.prodPrimes := Nat.dvd_of_mem_divisors hd ;   have hfac : (∏ p ∈ d.primeFactors, (1 + (1 - s.nu p)⁻¹)) ≤ ;       (4:ℝ)^d.primeFactors.card := by ;     calc ;       (∏ p ∈ d.primeFactors, (1 + (1 - s.nu p)⁻¹)) ≤ ;           ∏ p ∈ d.primeFactors, (4:ℝ) := by ;         apply Finset.prod_le_prod' ;         intro p hp ;         exact hcoeff p (Nat.primeFactors_mono hdvdN hNne0 hp) ;       _ = (4:ℝ)^d.primeFactors.card := by simp ;   have hfac_nonneg : 0 ≤ (∏ p ∈ d.primeFactors, (1 + (1 - s.nu p)⁻¹)) := by ;     apply Finset.prod_nonneg ;     intro p hp ;     have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp ;     have hpdvdN : p ∣ s.prodPrimes := (Nat.dvd_of_mem_primeFactors hp).trans hdvdN ;     have hnult : s.nu p < 1 := s.nu_lt_one_of_prime p hpprime hpdvdN ;     have hpos : 0 < (1 - s.nu p)⁻¹ := inv_pos.mpr (by linarith) ;     linarith ;   calc ;     \|BoundingSieve.lambdaSquared w d\| ≤ ;         (∑ d1 ∈ d.divisors, s.selbergTerms d1 / s.nu d1)^2 := ;       hlambda_bound d hd ;     _ = (∏ p ∈ d.primeFactors, (1 + (1 - s.nu p)⁻¹))^2 := by ;       rw [hclosed_form d hd] ;     _ ≤ ((4:ℝ)^d.primeFactors.card)^2 := ;       pow_le_pow_left₀ hfac_nonneg hfac 2 ;     _ = (16:ℝ)^d.primeFactors.card := by ;       rw [← pow_mul, mul_comm, pow_mul] ;       norm_num` | ❌ kernel_fail |
| 3 | `root_theorem` | solve | `intro s w hw hcoeff ;   have hNne0 : s.prodPrimes ≠ 0 := s.prodPrimes_squarefree.ne_zero ;   have hlambda_bound : ∀ d ∈ s.prodPrimes.divisors, \|BoundingSieve.lambdaSquared w d\| ≤ (∑ d1 ∈ d.divisors, s.selbergTerms d1 / s.nu d1)^2 := by ;     intro d hd ;     have hdvdN : d ∣ s.prodPrimes := Nat.dvd_of_mem_divisors hd ;     have hwd : ∀ d1 ∈ d.divisors, \|w d1\| ≤ s.selbergTerms d1 / s.nu d1 := by ;       intro d1 hd1 ;       have hd1dvd : d1 ∣ d := Nat.dvd_of_mem_divisors hd1 ;       exact hw d1 (Nat.mem_divisors.mpr ⟨hd1dvd.trans hdvdN, hNne0⟩) ;     have hstep : \|BoundingSieve.lambdaSquared w d\| ≤ ∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors, \|w d1\| * \|w d2\| := by ;       unfold BoundingSieve.lambdaSquared ;       calc \|∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors, if d = Nat.lcm d1 d2 then w d1 * w d2 else 0\| ;           ≤ ∑ d1 ∈ d.divisors, \|∑ d2 ∈ d.divisors, if d = Nat.lcm d1 d2 then w d1 * w d2 else 0\| := Finset.abs_sum_le_sum_abs _ _ ;         _ ≤ ∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors, \|if d = Nat.lcm d1 d2 then w d1 * w d2 else 0\| := by ;             apply Finset.sum_le_sum ;             intro d1 _ ;             exact Finset.abs_sum_le_sum_abs _ _ ;         _ ≤ ∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors, \|w d1\| * \|w d2\| := by ;             apply Finset.sum_le_sum ;             intro d1 _ ;             apply Finset.sum_le_sum ;             intro d2 _ ;             split_ifs with h ;             · rw [abs_mul] ;             · rw [abs_zero]; positivity ;     have heq : (∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors, \|w d1\| * \|w d2\|) = (∑ d1 ∈ d.divisors, \|w d1\|) * (∑ d2 ∈ d.divisors, \|w d2\|) := by ;       rw [Finset.sum_mul_sum] ;     have hsum_le : (∑ d1 ∈ d.divisors, \|w d1\|) ≤ ∑ d1 ∈ d.divisors, s.selbergTerms d1 / s.nu d1 := ;       Finset.sum_le_sum hwd ;     have hsum_nonneg : 0 ≤ ∑ d1 ∈ d.divisors, \|w d1\| := Finset.sum_nonneg (fun _ _ => abs_nonneg _) ;     calc \|BoundingSieve.lambdaSquared w d\| ≤ ∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors, \|w d1\| * \|w d2\| := hstep ;       _ = (∑ d1 ∈ d.divisors, \|w d1\|) * (∑ d2 ∈ d.divisors, \|w d2\|) := heq ;       _ = (∑ d1 ∈ d.divisors, \|w d1\|)^2 := by rw [sq] ;       _ ≤ (∑ d1 ∈ d.divisors, s.selbergTerms d1 / s.nu d1)^2 := pow_le_pow_left₀ hsum_nonneg hsum_le 2 ;   have hclosed_form : ∀ d ∈ s.prodPrimes.divisors, ∑ d1 ∈ d.divisors, s.selbergTerms d1 / s.nu d1 = ∏ p ∈ d.primeFactors, (1 + (1 - s.nu p)⁻¹) := by ;     intro d hd ;     have hdvdN : d ∣ s.prodPrimes := Nat.dvd_of_mem_divisors hd ;     have hdsqfree : Squarefree d := Squarefree.squarefree_of_dvd hdvdN s.prodPrimes_squarefree ;     have hdeq : (∏ p ∈ d.primeFactors, p) = d := Nat.prod_primeFactors_of_squarefree hdsqfree ;     have hp_all : ∀ p ∈ d.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp ;     have hgeneral : ∀ (t : Finset ℕ), (∀ p ∈ t, p.Prime) → ∀ (f : ℕ → ℝ), ;         ∑ d1 ∈ (∏ p ∈ t, p).divisors, ∏ p ∈ d1.primeFactors, f p = ∏ p ∈ t, (1 + f p) := by ;       intro t ;       induction t using Finset.induction_on with ;       \| empty => intro f; simp ;       \| @insert p t' hp_notin ih => ;         intro hp_all f ;         have hp_prime : p.Prime := hp_all p (Finset.mem_insert_self p t') ;         have ht'_prime : ∀ q ∈ t', q.Prime := fun q hq => hp_all q (Finset.mem_insert_of_mem hq) ;         have hM_pos : 0 < ∏ q ∈ t', q := Finset.prod_pos (fun q hq => (ht'_prime q hq).pos) ;         have hcop : Nat.Coprime p (∏ q ∈ t', q) := by ;           apply Nat.Coprime.prod_right ;           intro q hq ;           rw [Nat.coprime_primes hp_prime (ht'_prime q hq)] ;           intro heq; exact hp_notin (heq ▸ hq) ;         conv_lhs => rw [Finset.prod_insert hp_notin] ;         conv_rhs => rw [Finset.prod_insert hp_notin] ;         rw [← ih ht'_prime f] ;         have hMne0 : (∏ q ∈ t', q) ≠ 0 := hM_pos.ne' ;         have hpMne0 : (p * ∏ q ∈ t', q) ≠ 0 := Nat.mul_ne_zero hp_prime.pos.ne' hMne0 ;         have hsplit : (p * ∏ q ∈ t', q).divisors = (∏ q ∈ t', q).divisors ∪ (∏ q ∈ t', q).divisors.image (fun b => p*b) := by ;           ext d1 ;           simp only [Finset.mem_union, Finset.mem_image, Nat.mem_divisors] ;           constructor ;           · rintro ⟨hdvd, _⟩ ;             by_cases hpd : p ∣ d1 ;             · obtain ⟨e, he⟩ := hpd ;               right ;               refine ⟨e, ⟨?_, hMne0⟩, he.symm⟩ ;               rw [he] at hdvd ;               exact (mul_dvd_mul_iff_left hp_prime.pos.ne').mp hdvd ;             · left ;               refine ⟨?_, hMne0⟩ ;               have hcop2 : Nat.Coprime d1 p := ((Nat.Prime.coprime_iff_not_dvd hp_prime).mpr hpd).symm ;               exact (Nat.Coprime.dvd_of_dvd_mul_left hcop2 hdvd) ;           · rintro (⟨hdvd, _⟩ \| ⟨e, ⟨he, _⟩, heq⟩) ;             · exact ⟨hdvd.trans ⟨p, by ring⟩, hpMne0⟩ ;             · rw [← heq] ;               exact ⟨mul_dvd_mul_left p he, hpMne0⟩ ;         rw [hsplit] ;         have hdisj : Disjoint ((∏ q ∈ t', q).divisors) ((∏ q ∈ t', q).divisors.image (fun b => p*b)) := by ;           apply Finset.disjoint_left.mpr ;           intro a ha1 ha2 ;           simp only [Finset.mem_image] at ha2 ;           obtain ⟨e, he, heq⟩ := ha2 ;           have haM : a ∣ (∏ q ∈ t', q) := Nat.dvd_of_mem_divisors ha1 ;           have hpa : p ∣ a := by rw [← heq]; exact Dvd.intro e rfl ;           have hpM : p ∣ (∏ q ∈ t', q) := hpa.trans haM ;           exact absurd (Nat.eq_one_of_dvd_coprimes hcop (dvd_refl p) hpM) hp_prime.ne_one ;         rw [Finset.sum_union hdisj] ;         have hstep2 : ∑ b ∈ (∏ q ∈ t', q).divisors.image (fun b => p*b), ∏ p_1 ∈ b.primeFactors, f p_1 ;             = f p * ∑ b ∈ (∏ q ∈ t', q).divisors, ∏ p_1 ∈ b.primeFactors, f p_1 := by ;           rw [Finset.mul_sum] ;           rw [Finset.sum_image] ;           · apply Finset.sum_congr rfl ;             intro b hb ;             have hbM : b ∣ (∏ q ∈ t', q) := Nat.dvd_of_mem_divisors hb ;             have hcopb : Nat.Coprime p b := hcop.coprime_dvd_right hbM ;             have hbne0 : b ≠ 0 := by ;               intro hb0; rw [hb0] at hbM; exact hMne0 (Nat.eq_zero_of_zero_dvd hbM) ;             have hpb_pf : (p * b).primeFactors = insert p b.primeFactors := by ;               rw [Nat.primeFactors_mul hp_prime.ne_zero hbne0, Nat.Prime.primeFactors hp_prime] ;               rfl ;             rw [hpb_pf] ;             rw [Finset.prod_insert] ;             intro hpmem ;             have : p ∣ b := Nat.dvd_of_mem_primeFactors hpmem ;             exact absurd (Nat.eq_one_of_dvd_coprimes hcopb (dvd_refl p) this) hp_prime.ne_one ;           · intro a1 ha1 a2 ha2 heq ;             exact Nat.eq_of_mul_eq_mul_left hp_prime.pos heq ;         rw [hstep2] ;         ring ;     have hsum_eq : ∑ d1 ∈ d.divisors, ∏ p ∈ d1.primeFactors, (1 - s.nu p)⁻¹ = ∏ p ∈ d.primeFactors, (1 + (1 - s.nu p)⁻¹) := by ;       conv_lhs => rw [← hdeq] ;       exact hgeneral d.primeFactors hp_all (fun p => (1 - s.nu p)⁻¹) ;     rw [← hsum_eq] ;     apply Finset.sum_congr rfl ;     intro d1 hd1 ;     rw [Nat.mem_divisors] at hd1 ;     have hd1dvdN : d1 ∣ s.prodPrimes := hd1.1.trans hdvdN ;     have hnud1pos : 0 < s.nu d1 := BoundingSieve.nu_pos_of_dvd_prodPrimes hd1dvdN ;     rw [s.selbergTerms_apply] ;     rw [mul_comm, mul_div_assoc, div_self (ne_of_gt hnud1pos), mul_one] ;   intro d hd ;   have hdvdN : d ∣ s.prodPrimes := Nat.dvd_of_mem_divisors hd ;   have hfactor_nonneg : ∀ p ∈ d.primeFactors, ;       0 ≤ 1 + (1 - s.nu p)⁻¹ := by ;     intro p hp ;     have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp ;     have hpdvdN : p ∣ s.prodPrimes := (Nat.dvd_of_mem_primeFactors hp).trans hdvdN ;     have hnult : s.nu p < 1 := s.nu_lt_one_of_prime p hpprime hpdvdN ;     have hpos : 0 < (1 - s.nu p)⁻¹ := inv_pos.mpr (by linarith) ;     linarith ;   have hfac : (∏ p ∈ d.primeFactors, (1 + (1 - s.nu p)⁻¹)) ≤ ;       (4:ℝ)^d.primeFactors.card := by ;     calc ;       (∏ p ∈ d.primeFactors, (1 + (1 - s.nu p)⁻¹)) ≤ ;           ∏ p ∈ d.primeFactors, (4:ℝ) := by ;         apply Finset.prod_le_prod hfactor_nonneg ;         intro p hp ;         exact hcoeff p (Nat.primeFactors_mono hdvdN hNne0 hp) ;       _ = (4:ℝ)^d.primeFactors.card := by simp ;   have hfac_nonneg : 0 ≤ (∏ p ∈ d.primeFactors, (1 + (1 - s.nu p)⁻¹)) := by ;     apply Finset.prod_nonneg ;     exact hfactor_nonneg ;   calc ;     \|BoundingSieve.lambdaSquared w d\| ≤ ;         (∑ d1 ∈ d.divisors, s.selbergTerms d1 / s.nu d1)^2 := ;       hlambda_bound d hd ;     _ = (∏ p ∈ d.primeFactors, (1 + (1 - s.nu p)⁻¹))^2 := by ;       rw [hclosed_form d hd] ;     _ ≤ ((4:ℝ)^d.primeFactors.card)^2 := ;       pow_le_pow_left₀ hfac_nonneg hfac 2 ;     _ = (16:ℝ)^d.primeFactors.card := by ;       rw [← pow_mul, mul_comm, pow_mul] ;       norm_num` | ✅ kernel_pass |

## Verification context

- **Environment hash:** `9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d`
- **Import manifest hash:** `aaf21893d520a78dee0787a1bcaf939ee6b922265ff670c272e2e1d450dd29a7`
- **Import manifest:** `["Mathlib.Tactic.Ring","Mathlib.Tactic.NormNum","Mathlib"]`
- **proof_body_redacted:** false

## Integrity

4 hash-chained trajectory events, `209cfcbb01d3…` → `100908341b7b…` (GENESIS-anchored). Re-verify anytime with `episode_replay`.
