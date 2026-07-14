import Mathlib

/-!
# Erdős #647 — Layer C: conditional termwise errSum bound

Snapshot of the exact statement + proof term kernel-verified through the
tracked proof-search pipeline on 2026-07-14.

  problem_version_id  cc1e4633-be7b-407e-a3b8-e051dd0711d7
  episode_id          645a9ac0-9894-4b31-bfcc-5cf4f12c3b69
  root_statement_hash 3f10c84bdf45a24ccc11a9c9ca7d6b5ced4a88988740f898656c7146b8f35c34
  outcome             kernel_verified (root_proved)
  import manifest     ["Mathlib.Tactic.Ring", "Mathlib.Tactic.NormNum", "Mathlib"]

Content: for any `s : SelbergSieve` and any weight `w` satisfying the
POINTWISE Selberg magnitude bound `|w(d)| ≤ selbergTerms(d)/ν(d)` on all
of `s.prodPrimes.divisors` (exactly what `erdos647_selberg_weight_bound`
supplies for Layer B's optimal weight), the ABSTRACT
`errSum(lambdaSquared w) = ∑_{d∣prodPrimes} |lambdaSquared w d|·|rem d|`
is bounded termwise:

  `errSum(lambdaSquared w) ≤ ∑_{d∣prodPrimes} (∏_{p∈d.primeFactors}
    (1+(1-ν(p))⁻¹))² · |rem d|`

This is a CONDITIONAL assembly theorem: it leaves `|rem d|` as a free
abstract quantity (Mathlib's own `s.rem`), deliberately NOT tied to this
campaign's own concrete seven-tuple construction. Per the strategy
recorded in campaign memory ("prove a conditional final-assembly theorem
first... this decouples assembly wiring from proving the weight bound"),
this decouples the errSum-bounding wiring (done here, fully generic and
reusable for ANY SelbergSieve instance) from the separate task of
bounding `|rem d|` itself for OUR specific instance (via
`erdos647_rem_bound_squarefree`/`erdos647_rem_bound_one`, already done) —
that final substitution can only happen inside one large self-contained
submission (per the `Nonempty BoundingSieve`/no-cross-reference
environment constraint), but the wiring proven here is ready to receive
it directly.

Since cross-submission references don't work, this submission inlines
(as two separate local `have` blocks, each independently scoped so their
internal variable names don't collide) the full proof bodies of:
1. `erdos647_lambdaSquared_bound`'s pointwise argument (double triangle
   inequality + `Finset.sum_mul_sum` + `pow_le_pow_left₀`), restricted to
   the specific `d` at hand via `hwd` (derived from the global hypothesis
   `hw` by `d1∣d∣prodPrimes ⟹ d1∈prodPrimes.divisors`).
2. `erdos647_divisor_sum_selbergTerms_div_nu`'s closed-form identity
   (inlined `divisor_sum_prod_one_add` induction + `selbergTerms_apply`).

Then `unfold BoundingSieve.errSum; apply Finset.sum_le_sum` reduces to a
termwise goal `|lambdaSquared w d|·|rem d| ≤ (∏...)²·|rem d|`, closed by
`mul_le_mul_of_nonneg_right` (using `abs_nonneg (s.rem d)`) feeding in the
two `have`s. No new Lean bugs — landed FIRST TRY on both the untracked
pre-check and the tracked pipeline, since every piece reused was already
independently debugged.
-/

theorem erdos647_errSum_conditional_bound :
    ∀ (s : SelbergSieve) (w : ℕ → ℝ),
      (∀ d ∈ s.prodPrimes.divisors, |w d| ≤ s.selbergTerms d / s.nu d) →
      s.errSum (BoundingSieve.lambdaSquared w) ≤
        ∑ d ∈ s.prodPrimes.divisors, (∏ p ∈ d.primeFactors, (1 + (1 - s.nu p)⁻¹))^2 * |s.rem d| := by
  intro s w hw
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
  unfold BoundingSieve.errSum
  apply Finset.sum_le_sum
  intro d hd
  refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
  rw [← hclosed_form d hd]
  exact hlambda_bound d hd
