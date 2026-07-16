# ⚠️ KERNEL-VERIFIED FORMAL STATEMENT — FIDELITY NOT YET VERIFIED — Erdos #647 (Erdos-Selfridge), Layer C/B assembly — a general multiplicative-sum-over-divisors identity: for a Finset t of distinct primes and any real-valued f, the sum over divisors of prod(t) of prod_{p|d1} f(p) equals prod_{p in t} (1+f(p)). Proven by induction on t (Finset.induction_on), splitting divisors(p*M) into divisors(M) union p*divisors(M) (disjoint since p coprime to M), using Nat.primeFactors_mul to show (p*b).primeFactors = insert p b.primeFactors for b coprime to p. This gives a closed form for sums like sum_{d1|d} selbergTerms(d1)/nu(d1) (since selbergTerms(d1)/nu(d1) = prod_{p|d1} 1/(1-nu(p)) via selbergTerms_apply), needed to bound BoundingSieve.errSum for the density-bound program (Hughes-Kitamura Theorem 3), Layer C of the campaign.

> This proof establishes:
>
> `∀ (t : Finset ℕ), (∀ p ∈ t, p.Prime) → ∀ (f : ℕ → ℝ),
  ∑ d1 ∈ (∏ p ∈ t, p).divisors, ∏ p ∈ d1.primeFactors, f p = ∏ p ∈ t, (1 + f p)`
>
> It does **not yet** certify the source claim above.

**Root goal (formal):** `∀ (t : Finset ℕ), (∀ p ∈ t, p.Prime) → ∀ (f : ℕ → ℝ),
  ∑ d1 ∈ (∏ p ∈ t, p).divisors, ∏ p ∈ d1.primeFactors, f p = ∏ p ∈ t, (1 + f p)`

| Proof soundness | Statement fidelity | Canonical promotion | Training eligibility |
|---|---|---|---|
| VERIFIED | ATTESTED (unsafe_dev_attestation — not reviewed) | BLOCKED | QUARANTINED |

| episode | state | steps | budget left (μ$) | started | finished |
|---|---|---|---|---|---|
| `f482ac9c-75b0-4b0b-8ffa-98f99afabcab` | terminated (root_proved) | 1 | — | 2026-07-14T19:42:30 | 2026-07-14T19:43:15 |

## Proof tree

- ✅ **root_theorem** : `∀ (t : Finset ℕ), (∀ p ∈ t, p.Prime) → ∀ (f : ℕ → ℝ),
  ∑ d1 ∈ (∏ p ∈ t, p).divisors, ∏ p ∈ d1.primeFactors, f p = ∏ p ∈ t, (1 + f p)`

## The proof, assembled

```lean
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib

theorem root_theorem : ∀ (t : Finset ℕ), (∀ p ∈ t, p.Prime) → ∀ (f : ℕ → ℝ),
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

```

## How it went — every attempt, in order

| # | obligation | action | detail | verdict |
|---|---|---|---|---|
| 2 | `root_theorem` | solve | `intro t ; induction t using Finset.induction_on with ; \| empty => intro f; simp ; \| @insert p t' hp_notin ih => ;   intro hp_all f ;   have hp_prime : p.Prime := hp_all p (Finset.mem_insert_self p t') ;   have ht'_prime : ∀ q ∈ t', q.Prime := fun q hq => hp_all q (Finset.mem_insert_of_mem hq) ;   have hM_pos : 0 < ∏ q ∈ t', q := Finset.prod_pos (fun q hq => (ht'_prime q hq).pos) ;   have hcop : Nat.Coprime p (∏ q ∈ t', q) := by ;     apply Nat.Coprime.prod_right ;     intro q hq ;     rw [Nat.coprime_primes hp_prime (ht'_prime q hq)] ;     intro heq; exact hp_notin (heq ▸ hq) ;   conv_lhs => rw [Finset.prod_insert hp_notin] ;   conv_rhs => rw [Finset.prod_insert hp_notin] ;   rw [← ih ht'_prime f] ;   have hMne0 : (∏ q ∈ t', q) ≠ 0 := hM_pos.ne' ;   have hpMne0 : (p * ∏ q ∈ t', q) ≠ 0 := Nat.mul_ne_zero hp_prime.pos.ne' hMne0 ;   have hsplit : (p * ∏ q ∈ t', q).divisors = (∏ q ∈ t', q).divisors ∪ (∏ q ∈ t', q).divisors.image (fun b => p*b) := by ;     ext d1 ;     simp only [Finset.mem_union, Finset.mem_image, Nat.mem_divisors] ;     constructor ;     · rintro ⟨hdvd, _⟩ ;       by_cases hpd : p ∣ d1 ;       · obtain ⟨e, he⟩ := hpd ;         right ;         refine ⟨e, ⟨?_, hMne0⟩, he.symm⟩ ;         rw [he] at hdvd ;         exact (mul_dvd_mul_iff_left hp_prime.pos.ne').mp hdvd ;       · left ;         refine ⟨?_, hMne0⟩ ;         have hcop2 : Nat.Coprime d1 p := ((Nat.Prime.coprime_iff_not_dvd hp_prime).mpr hpd).symm ;         exact (Nat.Coprime.dvd_of_dvd_mul_left hcop2 hdvd) ;     · rintro (⟨hdvd, _⟩ \| ⟨e, ⟨he, _⟩, heq⟩) ;       · exact ⟨hdvd.trans ⟨p, by ring⟩, hpMne0⟩ ;       · rw [← heq] ;         exact ⟨mul_dvd_mul_left p he, hpMne0⟩ ;   rw [hsplit] ;   have hdisj : Disjoint ((∏ q ∈ t', q).divisors) ((∏ q ∈ t', q).divisors.image (fun b => p*b)) := by ;     apply Finset.disjoint_left.mpr ;     intro a ha1 ha2 ;     simp only [Finset.mem_image] at ha2 ;     obtain ⟨e, he, heq⟩ := ha2 ;     have haM : a ∣ (∏ q ∈ t', q) := Nat.dvd_of_mem_divisors ha1 ;     have hpa : p ∣ a := by rw [← heq]; exact Dvd.intro e rfl ;     have hpM : p ∣ (∏ q ∈ t', q) := hpa.trans haM ;     exact absurd (Nat.eq_one_of_dvd_coprimes hcop (dvd_refl p) hpM) hp_prime.ne_one ;   rw [Finset.sum_union hdisj] ;   have hstep2 : ∑ b ∈ (∏ q ∈ t', q).divisors.image (fun b => p*b), ∏ p_1 ∈ b.primeFactors, f p_1 ;       = f p * ∑ b ∈ (∏ q ∈ t', q).divisors, ∏ p_1 ∈ b.primeFactors, f p_1 := by ;     rw [Finset.mul_sum] ;     rw [Finset.sum_image] ;     · apply Finset.sum_congr rfl ;       intro b hb ;       have hbM : b ∣ (∏ q ∈ t', q) := Nat.dvd_of_mem_divisors hb ;       have hcopb : Nat.Coprime p b := hcop.coprime_dvd_right hbM ;       have hbne0 : b ≠ 0 := by ;         intro hb0; rw [hb0] at hbM; exact hMne0 (Nat.eq_zero_of_zero_dvd hbM) ;       have hpb_pf : (p * b).primeFactors = insert p b.primeFactors := by ;         rw [Nat.primeFactors_mul hp_prime.ne_zero hbne0, Nat.Prime.primeFactors hp_prime] ;         rfl ;       rw [hpb_pf] ;       rw [Finset.prod_insert] ;       intro hpmem ;       have : p ∣ b := Nat.dvd_of_mem_primeFactors hpmem ;       exact absurd (Nat.eq_one_of_dvd_coprimes hcopb (dvd_refl p) this) hp_prime.ne_one ;     · intro a1 ha1 a2 ha2 heq ;       exact Nat.eq_of_mul_eq_mul_left hp_prime.pos heq ;   rw [hstep2] ;   ring` | ✅ kernel_pass |

## Verification context

- **Environment hash:** `9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d`
- **Import manifest hash:** `aaf21893d520a78dee0787a1bcaf939ee6b922265ff670c272e2e1d450dd29a7`
- **Import manifest:** `["Mathlib.Tactic.Ring","Mathlib.Tactic.NormNum","Mathlib"]`
- **proof_body_redacted:** false

## Integrity

3 hash-chained trajectory events, `48993d3ff964…` → `f7d1525ef97a…` (GENESIS-anchored). Re-verify anytime with `episode_replay`.
