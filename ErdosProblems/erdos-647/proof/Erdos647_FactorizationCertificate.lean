import Mathlib

/-!
# Erdős #647 — verified batch-factorization certificate core

The checker verifies only the supplied prime factors, their distinctness, and
their product.  Its soundness theorem reconstructs the divisor count by
multiplicativity; it never asks Lean to factor the full certified value.

The definition-free replay theorem `erdos647_checkFactorizationData_sound`
was independently kernel-verified through the tracked proof-search pipeline
on 2026-07-16:

* preverification job: `80422540-b6a7-4682-9b89-b77c30604731`
* problem version: `ae3a7e5a-d259-42f1-8f56-d9b880cf2961`
* episode: `ac5c8417-b427-4d6b-a69e-55b17e0d17d0`
* root statement hash:
  `c74c6cb9eed3d984c226fc7a1949e55016ec2fe7a20798eae544c2194aadd4d8`
* outcome: `kernel_verified`

The end-to-end candidate theorem
`erdos647_candidate_of_factorizationBatchData` was independently tracked as
well:

* preverification job: `3b9ce01b-8dfe-45f0-a681-117c7f825ab3`
* problem version: `e3f5efd7-c500-43a2-a263-aab73836831c`
* episode: `22e0e381-4bb0-4658-9b17-8e3415ff17d0`
* root statement hash:
  `a7abc43acd2384b26bd2c618f9396da8d7ba7189ad98f174bb19da0fc6bd3634`
* outcome: `kernel_verified`
-/

structure Erdos647FactorizationCertificate where
  value : ℕ
  factors : List (ℕ × ℕ)
deriving Repr

def erdos647_factorProduct (fs : List (ℕ × ℕ)) : ℕ :=
  (fs.map fun pe => pe.1 ^ pe.2).prod

def erdos647_certifiedTau (fs : List (ℕ × ℕ)) : ℕ :=
  (fs.map fun pe => pe.2 + 1).prod

def Erdos647ValidFactors : List (ℕ × ℕ) → Prop
  | [] => True
  | (p, _) :: fs =>
      p.Prime ∧ (∀ pe ∈ fs, p ≠ pe.1) ∧ Erdos647ValidFactors fs

def erdos647_validFactorsDecidable :
    ∀ fs : List (ℕ × ℕ), Decidable (Erdos647ValidFactors fs)
  | [] => isTrue trivial
  | (p, _) :: fs =>
      if hp : p.Prime then
        if hd : ∀ pe ∈ fs, p ≠ pe.1 then
          match erdos647_validFactorsDecidable fs with
          | isTrue ht => isTrue ⟨hp, hd, ht⟩
          | isFalse ht => isFalse (fun h => ht h.2.2)
        else isFalse (fun h => hd h.2.1)
      else isFalse (fun h => hp h.1)

instance (fs : List (ℕ × ℕ)) : Decidable (Erdos647ValidFactors fs) :=
  erdos647_validFactorsDecidable fs

def Erdos647FactorizationCertificate.check
    (c : Erdos647FactorizationCertificate) : Bool :=
  decide (Erdos647ValidFactors c.factors ∧
    erdos647_factorProduct c.factors = c.value)

theorem erdos647_validFactors_prime_of_mem :
    ∀ fs : List (ℕ × ℕ), Erdos647ValidFactors fs →
      ∀ pe ∈ fs, pe.1.Prime := by
  intro fs
  induction fs with
  | nil => simp
  | cons hd tl ih =>
    rcases hd with ⟨p, a⟩
    intro hvalid pe hmem
    simp only [Erdos647ValidFactors] at hvalid
    rcases hvalid with ⟨hp, hdistinct, htail⟩
    simp only [List.mem_cons] at hmem
    rcases hmem with rfl | hmem
    · exact hp
    · exact ih htail pe hmem

theorem erdos647_sigma_factorProduct :
    ∀ fs : List (ℕ × ℕ), Erdos647ValidFactors fs →
      ArithmeticFunction.sigma 0 (erdos647_factorProduct fs) =
        erdos647_certifiedTau fs := by
  intro fs
  induction fs with
  | nil => simp [erdos647_factorProduct, erdos647_certifiedTau]
  | cons hd tl ih =>
    rcases hd with ⟨p, a⟩
    intro hvalid
    simp only [Erdos647ValidFactors] at hvalid
    rcases hvalid with ⟨hp, hdistinct, htail⟩
    have hcopBase : Nat.Coprime p (erdos647_factorProduct tl) := by
      rw [erdos647_factorProduct, Nat.coprime_list_prod_right_iff]
      intro qpow hqpow
      simp only [List.mem_map] at hqpow
      obtain ⟨qe, hqemem, rfl⟩ := hqpow
      rcases qe with ⟨q, e⟩
      have hqprime : q.Prime :=
        erdos647_validFactors_prime_of_mem tl htail (q, e) hqemem
      have hpq : p ≠ q := hdistinct (q, e) hqemem
      exact ((Nat.coprime_primes hp hqprime).mpr hpq).pow_right e
    have hcop : Nat.Coprime (p ^ a) (erdos647_factorProduct tl) :=
      hcopBase.pow_left a
    change ArithmeticFunction.sigma 0
        (p ^ a * erdos647_factorProduct tl) =
      (a + 1) * erdos647_certifiedTau tl
    rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
      ArithmeticFunction.sigma_zero_apply_prime_pow hp, ih htail]

theorem erdos647_checkFactorization_sound :
    ∀ c : Erdos647FactorizationCertificate,
      c.check = true →
      ArithmeticFunction.sigma 0 c.value =
        erdos647_certifiedTau c.factors := by
  intro c hcheck
  unfold Erdos647FactorizationCertificate.check at hcheck
  have hvalid : Erdos647ValidFactors c.factors ∧
      erdos647_factorProduct c.factors = c.value := of_decide_eq_true hcheck
  rcases hvalid with ⟨hvalid, hprod⟩
  rw [← hprod]
  exact erdos647_sigma_factorProduct c.factors hvalid

/-- A definition-free statement of the batch checker soundness theorem.
This is the form used for the independent tracked proof-search replay. -/
theorem erdos647_checkFactorizationData_sound :
    ∀ (value : ℕ) (fs : List (ℕ × ℕ)),
      decide
        (fs.Pairwise (fun x y => x.1 ≠ y.1) ∧
          (∀ pe ∈ fs, pe.1.Prime) ∧
          (fs.map fun pe => pe.1 ^ pe.2).prod = value) = true →
      ArithmeticFunction.sigma 0 value =
        (fs.map fun pe => pe.2 + 1).prod := by
  intro value fs
  induction fs generalizing value with
  | nil =>
    intro hcheck
    have hvalid :
        [].Pairwise (fun x y : ℕ × ℕ => x.1 ≠ y.1) ∧
          (∀ pe ∈ ([] : List (ℕ × ℕ)), pe.1.Prime) ∧
          (([].map fun pe : ℕ × ℕ => pe.1 ^ pe.2).prod = value) :=
      of_decide_eq_true hcheck
    simp only [List.map_nil, List.prod_nil] at hvalid ⊢
    rcases hvalid with ⟨_, _, rfl⟩
    native_decide
  | cons hd tl ih =>
    rcases hd with ⟨p, a⟩
    intro hcheck
    have hvalid :
        ((p, a) :: tl).Pairwise (fun x y : ℕ × ℕ => x.1 ≠ y.1) ∧
          (∀ pe ∈ (p, a) :: tl, pe.1.Prime) ∧
          ((((p, a) :: tl).map fun pe => pe.1 ^ pe.2).prod = value) :=
      of_decide_eq_true hcheck
    rcases hvalid with ⟨hpair, hprimes, hprod⟩
    have hp : p.Prime := hprimes (p, a) (by simp)
    have hpairTail : tl.Pairwise (fun x y : ℕ × ℕ => x.1 ≠ y.1) :=
      (List.pairwise_cons.mp hpair).2
    have hdistinct : ∀ pe ∈ tl, p ≠ pe.1 :=
      (List.pairwise_cons.mp hpair).1
    have hprimesTail : ∀ pe ∈ tl, pe.1.Prime := by
      intro pe hmem
      exact hprimes pe (by simp [hmem])
    have htailCheck :
        decide
          (tl.Pairwise (fun x y : ℕ × ℕ => x.1 ≠ y.1) ∧
            (∀ pe ∈ tl, pe.1.Prime) ∧
            (tl.map fun pe => pe.1 ^ pe.2).prod =
              (tl.map fun pe => pe.1 ^ pe.2).prod) = true := by
      apply decide_eq_true
      exact ⟨hpairTail, hprimesTail, rfl⟩
    have htailSigma := ih (tl.map fun pe => pe.1 ^ pe.2).prod htailCheck
    have hcopBase : Nat.Coprime p (tl.map fun pe => pe.1 ^ pe.2).prod := by
      rw [Nat.coprime_list_prod_right_iff]
      intro qpow hqpow
      simp only [List.mem_map] at hqpow
      obtain ⟨qe, hqemem, rfl⟩ := hqpow
      rcases qe with ⟨q, e⟩
      have hqprime : q.Prime := hprimesTail (q, e) hqemem
      have hpq : p ≠ q := hdistinct (q, e) hqemem
      exact ((Nat.coprime_primes hp hqprime).mpr hpq).pow_right e
    have hcop : Nat.Coprime (p ^ a) (tl.map fun pe => pe.1 ^ pe.2).prod :=
      hcopBase.pow_left a
    rw [← hprod]
    simp only [List.map_cons, List.prod_cons]
    rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
      ArithmeticFunction.sigma_zero_apply_prime_pow hp, htailSigma]

/-!
# Erdős #647 — verified finite shift-factorization batch checker

This section extends the single-value factorization checker
with a shift index, a finite coverage checker, and a power-prefix specialization.
No order or uniqueness assumption is made on the certificate list: coverage is
existential, so duplicate and out-of-order certificates are harmless.


The definition-free theorem `erdos647_factorizationBatchData_sound` was
independently kernel-verified through the tracked proof-search pipeline on
2026-07-16:

* preverification job: `98d9efe7-d5dc-4746-81b5-39f8a71d3d48`
* problem version: `c339958e-a432-4ac7-b0e8-fef64bf29ed8`
* episode: `5a454c61-c939-4f00-9a34-a3001751ead8`
* root statement hash:
  `20fb2e9169dbb42e52705ae846ba866e3fc0fbfd8bc667f4565a833142dd6d76`
* outcome: `kernel_verified`
-/

structure Erdos647ShiftFactorizationCertificate where
  shift : ℕ
  factorization : Erdos647FactorizationCertificate
deriving Repr

/-- Check one shift certificate against the ambient value `n` and budget `B`. -/
def Erdos647ShiftFactorizationCertificate.check
    (n B : ℕ) (c : Erdos647ShiftFactorizationCertificate) : Bool :=
  decide
    (c.factorization.check = true ∧
      0 < c.shift ∧
      c.shift < n ∧
      c.factorization.value = n - c.shift ∧
      erdos647_certifiedTau c.factorization.factors ≤ B + c.shift)

theorem erdos647_shiftFactorizationCheck_sound
    (n B : ℕ) (c : Erdos647ShiftFactorizationCertificate)
    (hcheck : c.check n B = true) :
    0 < c.shift ∧
      c.shift < n ∧
      ArithmeticFunction.sigma 0 (n - c.shift) ≤ B + c.shift := by
  unfold Erdos647ShiftFactorizationCertificate.check at hcheck
  have h := of_decide_eq_true hcheck
  rcases h with ⟨hfactor, hk0, hkn, hvalue, hbudget⟩
  have hsigma := erdos647_checkFactorization_sound c.factorization hfactor
  refine ⟨hk0, hkn, ?_⟩
  rw [← hvalue, hsigma]
  exact hbudget

/--
Check that every index in a finite required-shift set has at least one sound
certificate.  This is executable because both quantifiers are bounded by a
`Finset`/`List`.
-/
def erdos647_shiftBatchCheck
    (n B : ℕ) (required : Finset ℕ)
    (certificates : List Erdos647ShiftFactorizationCertificate) : Bool :=
  decide
    (∀ k ∈ required,
      ∃ c ∈ certificates, c.shift = k ∧ c.check n B = true)

theorem erdos647_shiftBatchCheck_sound
    (n B : ℕ) (required : Finset ℕ)
    (certificates : List Erdos647ShiftFactorizationCertificate)
    (hcheck : erdos647_shiftBatchCheck n B required certificates = true) :
    ∀ k ∈ required,
      ArithmeticFunction.sigma 0 (n - k) ≤ B + k := by
  unfold erdos647_shiftBatchCheck at hcheck
  have hcoverage := of_decide_eq_true hcheck
  intro k hk
  obtain ⟨c, hc, hcshift, hccheck⟩ := hcoverage k hk
  have hsound := erdos647_shiftFactorizationCheck_sound n B c hccheck
  rw [← hcshift]
  exact hsound.2.2

/-- The exact finite set that a generic `r`-power prefix argument must check. -/
def erdos647_powerPrefixRequired
    (r A C B n : ℕ) : Finset ℕ :=
  (Finset.range n).filter
    (fun k => 0 < k ∧ A * (B + k) ^ r < C * (n - k))

def erdos647_powerPrefixBatchCheck
    (r A C B n : ℕ)
    (certificates : List Erdos647ShiftFactorizationCertificate) : Bool :=
  erdos647_shiftBatchCheck n B
    (erdos647_powerPrefixRequired r A C B n) certificates

theorem erdos647_powerPrefixBatchCheck_sound
    (r A C B n : ℕ)
    (certificates : List Erdos647ShiftFactorizationCertificate)
    (hcheck :
      erdos647_powerPrefixBatchCheck r A C B n certificates = true) :
    ∀ k : ℕ, 0 < k → k < n →
      A * (B + k) ^ r < C * (n - k) →
      ArithmeticFunction.sigma 0 (n - k) ≤ B + k := by
  intro k hk0 hkn hprefix
  have hbatch := erdos647_shiftBatchCheck_sound n B
    (erdos647_powerPrefixRequired r A C B n) certificates hcheck
  apply hbatch k
  simp [erdos647_powerPrefixRequired, hkn, hk0, hprefix]

/-!
The next theorem deliberately mentions only Mathlib types and definitions.
It is the definition-free root statement suitable for independent proof-search
tracking.  Each certificate is a pair `(shift, factors)`.
-/

theorem erdos647_factorizationBatchData_sound :
    ∀ (n B : ℕ) (required : Finset ℕ)
      (certificates : List (ℕ × List (ℕ × ℕ))),
      decide
        (∀ k ∈ required,
          ∃ c ∈ certificates,
            c.1 = k ∧
            c.2.Pairwise (fun x y => x.1 ≠ y.1) ∧
            (∀ pe ∈ c.2, pe.1.Prime) ∧
            (c.2.map fun pe => pe.1 ^ pe.2).prod = n - k ∧
            (c.2.map fun pe => pe.2 + 1).prod ≤ B + k) = true →
      ∀ k ∈ required,
        ArithmeticFunction.sigma 0 (n - k) ≤ B + k := by
  intro n B required certificates hcheck
  have hfactorSound :
      ∀ (value : ℕ) (fs : List (ℕ × ℕ)),
        decide
          (fs.Pairwise (fun x y => x.1 ≠ y.1) ∧
            (∀ pe ∈ fs, pe.1.Prime) ∧
            (fs.map fun pe => pe.1 ^ pe.2).prod = value) = true →
        ArithmeticFunction.sigma 0 value =
          (fs.map fun pe => pe.2 + 1).prod := by
    intro value fs
    induction fs generalizing value with
    | nil =>
      intro hvalid
      have h :
          [].Pairwise (fun x y : ℕ × ℕ => x.1 ≠ y.1) ∧
            (∀ pe ∈ ([] : List (ℕ × ℕ)), pe.1.Prime) ∧
            (([].map fun pe : ℕ × ℕ => pe.1 ^ pe.2).prod = value) :=
        of_decide_eq_true hvalid
      simp only [List.map_nil, List.prod_nil] at h ⊢
      rcases h with ⟨_, _, rfl⟩
      native_decide
    | cons hd tl ih =>
      rcases hd with ⟨p, a⟩
      intro hvalid
      have h :
          ((p, a) :: tl).Pairwise
              (fun x y : ℕ × ℕ => x.1 ≠ y.1) ∧
            (∀ pe ∈ (p, a) :: tl, pe.1.Prime) ∧
            ((((p, a) :: tl).map fun pe => pe.1 ^ pe.2).prod = value) :=
        of_decide_eq_true hvalid
      rcases h with ⟨hpair, hprimes, hprod⟩
      have hp : p.Prime := hprimes (p, a) (by simp)
      have hpairTail :
          tl.Pairwise (fun x y : ℕ × ℕ => x.1 ≠ y.1) :=
        (List.pairwise_cons.mp hpair).2
      have hdistinct : ∀ pe ∈ tl, p ≠ pe.1 :=
        (List.pairwise_cons.mp hpair).1
      have hprimesTail : ∀ pe ∈ tl, pe.1.Prime := by
        intro pe hmem
        exact hprimes pe (by simp [hmem])
      have htailCheck :
          decide
            (tl.Pairwise (fun x y : ℕ × ℕ => x.1 ≠ y.1) ∧
              (∀ pe ∈ tl, pe.1.Prime) ∧
              (tl.map fun pe => pe.1 ^ pe.2).prod =
                (tl.map fun pe => pe.1 ^ pe.2).prod) = true := by
        apply decide_eq_true
        exact ⟨hpairTail, hprimesTail, rfl⟩
      have htailSigma :=
        ih (tl.map fun pe => pe.1 ^ pe.2).prod htailCheck
      have hcopBase :
          Nat.Coprime p (tl.map fun pe => pe.1 ^ pe.2).prod := by
        rw [Nat.coprime_list_prod_right_iff]
        intro qpow hqpow
        simp only [List.mem_map] at hqpow
        obtain ⟨qe, hqemem, rfl⟩ := hqpow
        rcases qe with ⟨q, e⟩
        have hqprime : q.Prime := hprimesTail (q, e) hqemem
        have hpq : p ≠ q := hdistinct (q, e) hqemem
        exact ((Nat.coprime_primes hp hqprime).mpr hpq).pow_right e
      have hcop :
          Nat.Coprime (p ^ a) (tl.map fun pe => pe.1 ^ pe.2).prod :=
        hcopBase.pow_left a
      rw [← hprod]
      simp only [List.map_cons, List.prod_cons]
      rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
        ArithmeticFunction.sigma_zero_apply_prime_pow hp, htailSigma]
  have hcoverage :
      ∀ k ∈ required,
        ∃ c ∈ certificates,
          c.1 = k ∧
          c.2.Pairwise (fun x y => x.1 ≠ y.1) ∧
          (∀ pe ∈ c.2, pe.1.Prime) ∧
          (c.2.map fun pe => pe.1 ^ pe.2).prod = n - k ∧
          (c.2.map fun pe => pe.2 + 1).prod ≤ B + k :=
    of_decide_eq_true hcheck
  intro k hk
  obtain ⟨c, hc, hcshift, hpair, hprimes, hprod, hbudget⟩ :=
    hcoverage k hk
  have hfactorCheck :
      decide
        (c.2.Pairwise (fun x y => x.1 ≠ y.1) ∧
          (∀ pe ∈ c.2, pe.1.Prime) ∧
          (c.2.map fun pe => pe.1 ^ pe.2).prod = n - k) = true := by
    apply decide_eq_true
    exact ⟨hpair, hprimes, hprod⟩
  have hsigma := hfactorSound (n - k) c.2 hfactorCheck
  rw [hsigma]
  exact hbudget

/-- End-to-end positive certificate interface.  A compact factorization batch
covering exactly the generic power-prefix shifts certifies the full supremum
candidate condition; shifts outside the batch are discharged by the supplied
global divisor-power bound. -/
theorem erdos647_candidate_of_factorizationBatchData :
    ∀ (r A C n : ℕ)
      (certificates : List (ℕ × List (ℕ × ℕ))),
      0 < r →
      0 < A →
      0 < n →
      (∀ m : ℕ, 1 ≤ m →
        A * (ArithmeticFunction.sigma 0 m) ^ r ≤ C * m) →
      decide
        (∀ k ∈ (Finset.range n).filter
            (fun k => 0 < k ∧ A * (k + 2) ^ r < C * (n - k)),
          ∃ c ∈ certificates,
            c.1 = k ∧
            c.2.Pairwise (fun x y => x.1 ≠ y.1) ∧
            (∀ pe ∈ c.2, pe.1.Prime) ∧
            (c.2.map fun pe => pe.1 ^ pe.2).prod = n - k ∧
            (c.2.map fun pe => pe.2 + 1).prod ≤ k + 2) = true →
      (⨆ m : Fin n,
        (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 := by
  intro r A C n certificates hr hA hn hdiv hcheck
  let required := (Finset.range n).filter
    (fun k => 0 < k ∧ A * (k + 2) ^ r < C * (n - k))
  have hbatch := erdos647_factorizationBatchData_sound
    n 2 required certificates (by simpa [required, Nat.add_comm] using hcheck)
  have hprefix : ∀ k : ℕ, 0 < k → k < n →
      A * (k + 2) ^ r < C * (n - k) →
      ArithmeticFunction.sigma 0 (n - k) ≤ k + 2 := by
    intro k hk0 hkn hk
    have hkreq : k ∈ required := by
      simp [required, hkn, hk0, hk]
    simpa [Nat.add_comm] using hbatch k hkreq
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hbudget : ∀ k : ℕ, 0 < k → k < n →
      ArithmeticFunction.sigma 0 (n - k) ≤ k + 2 := by
    intro k hk0 hkn
    by_cases hk : A * (k + 2) ^ r < C * (n - k)
    · exact hprefix k hk0 hkn hk
    · push Not at hk
      have hmpos : 1 ≤ n - k := by omega
      have hbound := hdiv (n - k) hmpos
      have hmul :
          A * (ArithmeticFunction.sigma 0 (n - k)) ^ r ≤
            A * (k + 2) ^ r := hbound.trans hk
      have hpows :
          (ArithmeticFunction.sigma 0 (n - k)) ^ r ≤ (k + 2) ^ r :=
        le_of_mul_le_mul_left hmul hA
      exact (Nat.pow_le_pow_iff_left (Nat.ne_of_gt hr)).mp hpows
  apply ciSup_le
  intro m
  rcases Nat.eq_zero_or_pos (m : ℕ) with hm0 | hmpos
  · rw [hm0]
    simp
  · have hmn : (m : ℕ) < n := m.isLt
    have hk0 : 0 < n - (m : ℕ) := by omega
    have hkn : n - (m : ℕ) < n := by omega
    have hb := hbudget (n - (m : ℕ)) hk0 hkn
    have hmk : n - (n - (m : ℕ)) = (m : ℕ) := by omega
    rw [hmk] at hb
    omega

/-! A tiny executable smoke test: `10 - 1 = 3^2` and `τ(9) = 3 ≤ 2 + 1`. -/

def erdos647_batchSmokeCertificates :
    List Erdos647ShiftFactorizationCertificate :=
  [{ shift := 1,
     factorization := { value := 9, factors := [(3, 2)] } }]

example :
    erdos647_shiftBatchCheck 10 2 {1}
      erdos647_batchSmokeCertificates = true := by
  native_decide
