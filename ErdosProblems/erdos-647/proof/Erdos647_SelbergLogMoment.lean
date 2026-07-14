import Mathlib

/-!
# Erdős #647 — Layer C errSum repair: log-moment identity for selbergTerms

Snapshot of the exact statement + proof term kernel-verified through the
tracked proof-search pipeline on 2026-07-14.

  problem_version_id  6844eda7-3e4d-4278-8abd-09b4e8e48e0b
  episode_id          f4aa4989-c3bb-4cd0-8786-fa649b80dac6
  root_statement_hash 32c885e79b9fd7d05819d04d0febd3b64579d424b806b38d0f1f8c3ea63a671e
  outcome             kernel_verified (root_proved)
  import manifest     ["Mathlib.Tactic.Ring", "Mathlib.Tactic.NormNum", "Mathlib"]

Content: Milestone A/B support for the level-truncated Selberg weight
repair plan — the log-moment identity

  `∑_{d∣prodPrimes} selbergTerms(d)·log(d) = L · ∑_{p∣prodPrimes} ν(p)·log(p)`

where `L := ∑_{l∣prodPrimes} selbergTerms(l)`. This is the identity needed
to show the level-truncated Selberg denominator `L_R := ∑_{d∣prodPrimes,
d≤R} selbergTerms(d)` retains the growth rate of the full `L`, via the
weighted-tail estimate `∑_{d>R} selbergTerms(d) ≤ (L/log R)·∑_p ν(p)·log p`
(since `log d > log R` for `d>R>1`, so `selbergTerms(d) ≤
selbergTerms(d)·log(d)/log(R)` termwise, and dropping the `d≤R` part of
the log-moment sum only increases the RHS since `selbergTerms≥0`,
`log≥0`). This gives `L_R ≥ L·(1 − [∑_p ν(p)·log p]/log R)`, so `L_R ≳ L`
once `R` is large enough relative to `∑ν(p)log p` — the key growth-
preservation step flagged as needing rigorous derivation by the deep-
research pass (task w7x3bu4fp) into the classical Selberg truncation
normalization.

Proof: combined induction over an abstract `Finset t` of primes,
generalizing over `(∏t) ∣ s.prodPrimes`, proving simultaneously the
per-`t` identity `∑_{d1∣∏t} selbergTerms(d1)·∑_{q∈d1.primeFactors}log(q)
= (∑_{d1∣∏t}selbergTerms(d1))·∑_{p∈t}ν(p)·log(p)` (in terms of the
per-prime-factor log expansion, matching the induction's internal
structure), then specializing `t := s.prodPrimes.primeFactors` and
converting `log(d1)` (the theorem statement's form, for squarefree `d1`)
to `∑_{q∈d1.primeFactors}log(q)` via `Nat.prod_primeFactors_of_squarefree`
+ `Real.log_prod`. The inductive step's key algebraic identity is
`selbergTerms(p) = (1+selbergTerms(p))·ν(p)` for prime `p∣prodPrimes`
(from `selbergTerms_apply` + `field_simp`/`ring`, using `ν(p)∈(0,1)`).

Two Lean bugs, both the SAME self-referential-rewrite pattern already
seen multiple times this campaign (rewriting a goal with a hypothesis
whose own RHS still contains the LHS pattern corrupts BOTH sides of the
goal, not just the intended occurrence): (1) `have hpdvdN : p ∣
s.prodPrimes := ⟨M, by rw [← htdvd]⟩` is invalid (`htdvd` is a dvd-proof,
not an equation) — fixed with `dvd_trans ⟨M, rfl⟩ htdvd`; (2) the
`hexpand` step's `rw [hkey]` (where `hkey : selbergTerms p = (1 +
selbergTerms p)·ν(p)`) blindly rewrote `selbergTerms p` on BOTH sides of
the goal, including inside the `(1 + selbergTerms p)` factor already
present on the goal's RHS, corrupting it with a spurious extra `ν(p)²`
cross term (confirmed by reading the exact unsolved-goals diagnostic
after the first submission's `kernel_fail`) — fixed by scoping to `conv_lhs
=> rw [hkey]` so only the LHS's occurrence is rewritten, matching this
campaign's established fix pattern for this exact bug class. Also needed
a final `Real.log d = ∑_{q∈d.primeFactors} log q` conversion for
squarefree `d`, using `conv_lhs => rw [← hd1eq]` proactively (not `rw`
directly) to avoid the same self-referential-rewrite risk (the rewrite
target `d1` appears both as the log argument and inside `d1.primeFactors`
on the RHS).
-/

theorem erdos647_selberg_log_moment :
    ∀ (s : SelbergSieve), ∑ d ∈ s.prodPrimes.divisors, s.selbergTerms d * Real.log d =
      (∑ l ∈ s.prodPrimes.divisors, s.selbergTerms l) *
        ∑ p ∈ s.prodPrimes.primeFactors, s.nu p * Real.log p := by
  intro s
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
  rw [Finset.sum_congr rfl (fun d1 hd1 => by rw [hlogeq d1 hd1])]
  exact hres
