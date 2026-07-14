import Mathlib

/-!
# Erdős #647 — Layer C errSum repair: weighted-tail bound / L_R growth preservation

Snapshot of the exact statement + proof term kernel-verified through the
tracked proof-search pipeline on 2026-07-14.

  problem_version_id  4e75f137-8483-4af5-8b24-e7db33ffc25d
  episode_id          a80c609c-cae6-4a75-ab4b-6d4b7d18e56e
  root_statement_hash 18e85c331ce45bb88482c493931c19b3feb8ccfc8a369dde14e3592b20cc43fe
  outcome             kernel_verified (root_proved)
  import manifest     ["Mathlib.Tactic.Ring", "Mathlib.Tactic.NormNum", "Mathlib"]

Content: Milestone A/B — the key growth-preservation step of the level-
truncated Selberg weight repair plan. For any `SelbergSieve s` and
truncation level `R>1`:

  `∑_{d∣prodPrimes, d>R} selbergTerms(d) ≤ L · (∑_p ν(p)·log p) / log R`

where `L := ∑_{l∣prodPrimes} selbergTerms(l)`. Combined with the trivial
split `L = L_R + tail` (where `L_R := ∑_{d∣prodPrimes, d≤R}
selbergTerms(d)` is the level-truncated Selberg denominator), this gives

  `L_R ≥ L·(1 − [∑_p ν(p)·log p] / log R)`

i.e. `L_R` retains `L`'s growth rate once `R` is large enough relative to
`∑_p ν(p)·log p` — this is the piece that lets the truncated construction
`w_R` (still to be built — the harder remaining Milestone A piece, a full
re-derivation of `erdos647_selberg_optimal_weight`'s Möbius-inversion
argument with the restricted divisor set `D_R` replacing `D`) retain a
main term matching the untruncated one's `L≳(log z)^7` growth, while
`erdos647_lambdaSquared_support_sq` gives the matching finite-support
control on the error side.

Proof: inlines the entire `erdos647_selberg_log_moment` derivation (the
combined induction over an abstract `Finset` of primes; cross-submission
references don't work in this environment, so every tracked submission
must be fully self-contained) to get the log-moment identity as a local
`have`, then argues: for `d>R>1`, `log d > log R > 0`
(`Real.log_lt_log`), so termwise `selbergTerms(d) ≤
selbergTerms(d)·log(d)/log(R)` (since `selbergTerms(d)>0`, from Mathlib's
own `selbergTerms_pos`); summing this bound over the `d>R` filter,
extending the numerator sum to ALL divisors (valid since every term
`selbergTerms(d)·log(d)≥0`, via `Finset.sum_le_sum_of_subset_of_nonneg`),
and substituting the log-moment identity gives the claimed bound. Zero
Lean bugs — kernel-verified FIRST TRY on both the untracked pre-check and
the tracked pipeline, the first "no-new-bugs" submission in the errSum
repair sequence so far (every other piece needed at least one
verification-tool round trip).
-/

theorem erdos647_selberg_L_tail_bound :
    ∀ (s : SelbergSieve) (R : ℕ), 1 < R →
      ∑ d ∈ s.prodPrimes.divisors.filter (fun d => R < d), s.selbergTerms d ≤
        (∑ l ∈ s.prodPrimes.divisors, s.selbergTerms l) *
          (∑ p ∈ s.prodPrimes.primeFactors, s.nu p * Real.log p) / Real.log R := by
  intro s R hR
  have hcombined : ∀ (t : Finset ℕ), (∀ p ∈ t, p.Prime) → (∏ p ∈ t, p) ∣ s.prodPrimes →
      (∑ d1 ∈ (∏ p ∈ t, p).divisors, s.selbergTerms d1 * (∑ q ∈ d1.primeFactors, Real.log q)
        = (∑ d1 ∈ (∏ p ∈ t, p).divisors, s.selbergTerms d1) * ∑ p ∈ t, s.nu p * Real.log p) := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro hp_all htdvd
      simp
    | @insert p t' hp_notin ih =>
      intro hp_all htdvd
      have hp_prime : p.Prime := hp_all p (Finset.mem_insert_self p t')
      have ht'_prime : ∀ q ∈ t', q.Prime := fun q hq => hp_all q (Finset.mem_insert_of_mem hq)
      rw [Finset.prod_insert hp_notin] at htdvd ⊢
      rw [Finset.sum_insert hp_notin]
      set M := ∏ q ∈ t', q with hM_def
      have hMdvd : M ∣ s.prodPrimes := dvd_trans ⟨p, by ring⟩ htdvd
      have hpMsqfree : Squarefree (p * M) := Squarefree.squarefree_of_dvd htdvd s.prodPrimes_squarefree
      have hMsqfree : Squarefree M := Squarefree.squarefree_of_dvd hMdvd s.prodPrimes_squarefree
      have hcop : Nat.Coprime p M := Nat.coprime_of_squarefree_mul hpMsqfree
      have hMne0 : M ≠ 0 := hMsqfree.ne_zero
      have hpMne0 : p * M ≠ 0 := Nat.mul_ne_zero hp_prime.pos.ne' hMne0
      have hsplit : (p * M).divisors = M.divisors ∪ M.divisors.image (fun b => p * b) := by
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
            exact Nat.Coprime.dvd_of_dvd_mul_left hcop2 hdvd
        · rintro (⟨hdvd, _⟩ | ⟨e, ⟨he, _⟩, heq⟩)
          · exact ⟨hdvd.trans ⟨p, by ring⟩, hpMne0⟩
          · rw [← heq]
            exact ⟨mul_dvd_mul_left p he, hpMne0⟩
      have hdisj : Disjoint M.divisors (M.divisors.image (fun b => p * b)) := by
        apply Finset.disjoint_left.mpr
        intro a ha1 ha2
        simp only [Finset.mem_image] at ha2
        obtain ⟨e, he, heq⟩ := ha2
        have haM : a ∣ M := Nat.dvd_of_mem_divisors ha1
        have hpa : p ∣ a := by rw [← heq]; exact Dvd.intro e rfl
        have hpM : p ∣ M := hpa.trans haM
        exact absurd (Nat.eq_one_of_dvd_coprimes hcop (dvd_refl p) hpM) hp_prime.ne_one
      have hstep2gen : ∀ (f : ℕ → ℝ), ∑ b ∈ M.divisors.image (fun b => p * b), f b
          = ∑ e ∈ M.divisors, f (p * e) := by
        intro f
        apply Finset.sum_image
        intro a1 ha1 a2 ha2 heq
        exact Nat.eq_of_mul_eq_mul_left hp_prime.pos heq
      have hpe_pf : ∀ e ∈ M.divisors, (p * e).primeFactors = insert p e.primeFactors := by
        intro e he
        have heM : e ∣ M := Nat.dvd_of_mem_divisors he
        have hene0 : e ≠ 0 := by
          intro he0; rw [he0] at heM; exact hMne0 (Nat.eq_zero_of_zero_dvd heM)
        rw [Nat.primeFactors_mul hp_prime.ne_zero hene0, Nat.Prime.primeFactors hp_prime]
        rfl
      have hpnotin : ∀ e ∈ M.divisors, p ∉ e.primeFactors := by
        intro e he hpmem
        have heM : e ∣ M := Nat.dvd_of_mem_divisors he
        have hcopP : Nat.Coprime p e := hcop.coprime_dvd_right heM
        have : p ∣ e := Nat.dvd_of_mem_primeFactors hpmem
        exact absurd (Nat.eq_one_of_dvd_coprimes hcopP (dvd_refl p) this) hp_prime.ne_one
      have hmul : ∀ e ∈ M.divisors, s.selbergTerms (p * e) = s.selbergTerms p * s.selbergTerms e := by
        intro e he
        have heM : e ∣ M := Nat.dvd_of_mem_divisors he
        have hcopP : Nat.Coprime p e := hcop.coprime_dvd_right heM
        exact s.selbergTerms_isMultiplicative.map_mul_of_coprime hcopP
      have hLnew : ∑ d1 ∈ M.divisors ∪ M.divisors.image (fun b => p * b), s.selbergTerms d1
          = (1 + s.selbergTerms p) * ∑ e ∈ M.divisors, s.selbergTerms e := by
        rw [Finset.sum_union hdisj, hstep2gen]
        have : ∑ e ∈ M.divisors, s.selbergTerms (p * e) = s.selbergTerms p * ∑ e ∈ M.divisors, s.selbergTerms e := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl hmul
        rw [this]
        ring
      have hpdvdN : p ∣ s.prodPrimes := dvd_trans ⟨M, rfl⟩ htdvd
      have hnudpos : 0 < s.nu p := BoundingSieve.nu_pos_of_dvd_prodPrimes hpdvdN
      have hnudlt1 : s.nu p < 1 := s.nu_lt_one_of_prime p hp_prime hpdvdN
      have hkey : s.selbergTerms p = (1 + s.selbergTerms p) * s.nu p := by
        rw [s.selbergTerms_apply, hp_prime.primeFactors, Finset.prod_singleton]
        have h1mx : (1:ℝ) - s.nu p ≠ 0 := by linarith
        field_simp
        ring
      rw [hsplit, Finset.sum_union hdisj]
      have hlogterm : ∀ e ∈ M.divisors, s.selbergTerms (p*e) * (∑ q ∈ (p*e).primeFactors, Real.log q)
          = s.selbergTerms p * Real.log p * s.selbergTerms e + s.selbergTerms p * (s.selbergTerms e * (∑ q ∈ e.primeFactors, Real.log q)) := by
        intro e he
        rw [hpe_pf e he, Finset.sum_insert (hpnotin e he), hmul e he]
        ring
      rw [hstep2gen (fun b => s.selbergTerms b * (∑ q ∈ b.primeFactors, Real.log q))]
      rw [Finset.sum_congr rfl hlogterm]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      rw [ih ht'_prime hMdvd]
      rw [hLnew]
      have hexpand : s.selbergTerms p * Real.log p * (∑ e ∈ M.divisors, s.selbergTerms e) = (1 + s.selbergTerms p) * (∑ e ∈ M.divisors, s.selbergTerms e) * (s.nu p * Real.log p) := by
        conv_lhs => rw [hkey]
        ring
      rw [hexpand]
      ring
  have heq : (∏ p ∈ s.prodPrimes.primeFactors, p) = s.prodPrimes := Nat.prod_primeFactors_of_squarefree s.prodPrimes_squarefree
  have hp_all : ∀ p ∈ s.prodPrimes.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have hdvd_self : (∏ p ∈ s.prodPrimes.primeFactors, p) ∣ s.prodPrimes := by rw [heq]
  have hres := hcombined s.prodPrimes.primeFactors hp_all hdvd_self
  rw [heq] at hres
  have hlogeq : ∀ d1 ∈ s.prodPrimes.divisors, Real.log d1 = ∑ q ∈ d1.primeFactors, Real.log q := by
    intro d1 hd1
    have hd1dvd : d1 ∣ s.prodPrimes := Nat.dvd_of_mem_divisors hd1
    have hd1sqfree : Squarefree d1 := Squarefree.squarefree_of_dvd hd1dvd s.prodPrimes_squarefree
    have hd1eq : (∏ q ∈ d1.primeFactors, q) = d1 := Nat.prod_primeFactors_of_squarefree hd1sqfree
    conv_lhs => rw [← hd1eq]
    rw [Nat.cast_prod, Real.log_prod]
    intro q hq
    exact_mod_cast (Nat.prime_of_mem_primeFactors hq).ne_zero
  have hlogmoment : ∑ d ∈ s.prodPrimes.divisors, s.selbergTerms d * Real.log d =
      (∑ l ∈ s.prodPrimes.divisors, s.selbergTerms l) * ∑ p ∈ s.prodPrimes.primeFactors, s.nu p * Real.log p := by
    rw [Finset.sum_congr rfl (fun d1 hd1 => by rw [hlogeq d1 hd1])]
    exact hres
  have hlogRpos : 0 < Real.log R := Real.log_pos (by exact_mod_cast hR)
  have hRpos : 0 < R := lt_trans one_pos hR
  have hterm : ∀ d ∈ s.prodPrimes.divisors.filter (fun d => R < d), s.selbergTerms d ≤ s.selbergTerms d * Real.log d / Real.log R := by
    intro d hd
    simp only [Finset.mem_filter] at hd
    obtain ⟨hddvd, hRd⟩ := hd
    have hdpos : 0 < s.selbergTerms d := s.selbergTerms_pos (Nat.dvd_of_mem_divisors hddvd)
    have hdRlog : Real.log R < Real.log d := Real.log_lt_log (by exact_mod_cast hRpos) (by exact_mod_cast hRd)
    rw [le_div_iff₀ hlogRpos]
    exact mul_le_mul_of_nonneg_left hdRlog.le hdpos.le
  have hnonneg : ∀ d ∈ s.prodPrimes.divisors, 0 ≤ s.selbergTerms d * Real.log d := by
    intro d hd
    have hdpos : 0 < s.selbergTerms d := s.selbergTerms_pos (Nat.dvd_of_mem_divisors hd)
    have hdge1 : 1 ≤ d := Nat.pos_of_mem_divisors hd
    have hlogdnn : (0:ℝ) ≤ Real.log d := Real.log_nonneg (by exact_mod_cast hdge1)
    exact mul_nonneg hdpos.le hlogdnn
  have hsub : s.prodPrimes.divisors.filter (fun d => R < d) ⊆ s.prodPrimes.divisors := Finset.filter_subset _ _
  have hnumineq : ∑ d ∈ s.prodPrimes.divisors.filter (fun d => R < d), s.selbergTerms d * Real.log d ≤ ∑ d ∈ s.prodPrimes.divisors, s.selbergTerms d * Real.log d :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun d hd _ => hnonneg d hd)
  calc ∑ d ∈ s.prodPrimes.divisors.filter (fun d => R < d), s.selbergTerms d
      ≤ ∑ d ∈ s.prodPrimes.divisors.filter (fun d => R < d), s.selbergTerms d * Real.log d / Real.log R :=
        Finset.sum_le_sum hterm
    _ = (∑ d ∈ s.prodPrimes.divisors.filter (fun d => R < d), s.selbergTerms d * Real.log d) / Real.log R := by
        rw [Finset.sum_div]
    _ ≤ (∑ d ∈ s.prodPrimes.divisors, s.selbergTerms d * Real.log d) / Real.log R :=
        (div_le_div_iff_of_pos_right hlogRpos).mpr hnumineq
    _ = (∑ l ∈ s.prodPrimes.divisors, s.selbergTerms l) * (∑ p ∈ s.prodPrimes.primeFactors, s.nu p * Real.log p) / Real.log R := by
        rw [hlogmoment]
