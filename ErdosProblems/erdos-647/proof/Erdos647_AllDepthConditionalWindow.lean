import Mathlib

/-!
# Erdős #647 — conditional finite windows at every fixed depth

This file reconstructs and strengthens the conditional finite-window package
from Scott Hughes's `erdos647-proof-chain`, specifically
`lean/Erdos647ConditionalFiniteWindow.lean` at commit
`be657cf1b89aebb98bbb8117f29c0456a8435ac6`.

Hughes introduced the prefix-LCM construction and proved the exact identity

`τ(prefixLcm K * t - k) = 2 * τ(k)`

under a prime-cofactor hypothesis.  His generic theorem accepted
`2 * τ(k) ≤ k + 2` as an argument, with concrete native checks through depths
20 and 80.  The development below proves that small-factor inequality
uniformly for every positive `k`, so the conditional construction works at
an arbitrary fixed depth `K` without a finite cutoff.

The word **conditional** is essential.  `PrimeCofactorHyp K t` is an explicit
hypothesis asserting simultaneous primality of finitely many linear forms.
This file proves the deterministic implication from that hypothesis to the
divisor budgets.  It does not prove that a suitable `t` exists, does not prove
a prime-tuples conjecture, and does not close an open research declaration by
itself.

Proof-search provenance for the standalone arbitrary-depth theorem:

* verification job `11410566-b988-4a38-8960-a025cc835f04`:
  `kernel_pass`;
* problem version `7d956b60-f919-400b-a005-b74106be004c`;
* episode `97adcc1e-87a6-4870-80da-172f3771d4b4`:
  `kernel_verified` (`root_proved`);
* root statement hash
  `0a027be3df9f79e5ed949f7c63af4a5b22743ec0b2d0e8c4cf4e51c1ff6323dd`.
-/

namespace Erdos647AllDepthConditionalWindow

open Finset

/-- The prefix least common multiple `lcm(1, ..., K)`. -/
def prefixLcm (K : ℕ) : ℕ :=
  (Finset.Icc 1 K).lcm id

/-- The linear cofactor in the `k`-th shifted factorization. -/
def primeCofactor (K t k : ℕ) : ℕ :=
  (prefixLcm K / k) * t - 1

/-- Every divisor-count budget through the fixed depth `K`. -/
def WindowGood (K n : ℕ) : Prop :=
  ∀ k, 1 ≤ k → k ≤ K → ArithmeticFunction.sigma 0 (n - k) ≤ k + 2

/-- The simultaneous primality and size hypothesis used by the construction.

This is a hypothesis, not an existence theorem.
-/
def PrimeCofactorHyp (K t : ℕ) : Prop :=
  ∀ k, 1 ≤ k → k ≤ K →
    Nat.Prime (primeCofactor K t k) ∧ k < primeCofactor K t k

/-- Every positive `k ≤ K` divides the prefix LCM. -/
theorem dvd_prefixLcm {K k : ℕ} (hk1 : 1 ≤ k) (hkK : k ≤ K) :
    k ∣ prefixLcm K := by
  classical
  simpa [prefixLcm] using
    (Finset.dvd_lcm (s := Finset.Icc 1 K) (f := id)
      (by simpa using Finset.mem_Icc.mpr ⟨hk1, hkK⟩))

/-- Full-value factorization of a shifted prefix-LCM value. -/
theorem sub_eq_mul_primeCofactor {K t k : ℕ}
    (hk1 : 1 ≤ k) (hkK : k ≤ K) :
    prefixLcm K * t - k = k * primeCofactor K t k := by
  have hdvd : k ∣ prefixLcm K := dvd_prefixLcm hk1 hkK
  rw [primeCofactor]
  have hmul : (((prefixLcm K / k) * k) * t) =
      k * ((prefixLcm K / k) * t) := by
    ring
  calc
    prefixLcm K * t - k
        = (((prefixLcm K / k) * k) * t) - k := by
            rw [Nat.div_mul_cancel hdvd]
    _ = k * ((prefixLcm K / k) * t) - k := by rw [hmul]
    _ = k * (((prefixLcm K / k) * t) - 1) := by
          conv_rhs => rw [Nat.mul_sub_left_distrib, Nat.mul_one]

/-- The small factor is coprime to its strictly larger prime cofactor. -/
theorem coprime_of_primeCofactor {K t k : ℕ}
    (hk1 : 1 ≤ k) (hprime : Nat.Prime (primeCofactor K t k))
    (hgt : k < primeCofactor K t k) :
    Nat.Coprime k (primeCofactor K t k) := by
  have hnot : ¬ primeCofactor K t k ∣ k := by
    intro hdiv
    have hle : primeCofactor K t k ≤ k := Nat.le_of_dvd hk1 hdiv
    exact Nat.not_le_of_lt hgt hle
  exact Nat.Coprime.symm (hprime.coprime_iff_not_dvd.mpr hnot)

/-- A prime has exactly two positive divisors. -/
theorem divisors_card_prime {q : ℕ} (hq : Nat.Prime q) :
    q.divisors.card = 2 := by
  rw [Nat.Prime.divisors hq]
  exact Finset.card_pair hq.one_lt.ne

/-- Exact divisor count for the shifted construction. -/
theorem tau_eq_two_mul_divisors {K t k : ℕ}
    (hk1 : 1 ≤ k) (hkK : k ≤ K)
    (hprime : Nat.Prime (primeCofactor K t k))
    (hgt : k < primeCofactor K t k) :
    (prefixLcm K * t - k).divisors.card = 2 * k.divisors.card := by
  have hfactor : prefixLcm K * t - k = k * primeCofactor K t k :=
    sub_eq_mul_primeCofactor hk1 hkK
  have hcop : Nat.Coprime k (primeCofactor K t k) :=
    coprime_of_primeCofactor hk1 hprime hgt
  calc
    (prefixLcm K * t - k).divisors.card
        = (k * primeCofactor K t k).divisors.card := by rw [hfactor]
    _ = k.divisors.card * (primeCofactor K t k).divisors.card :=
      hcop.card_divisors_mul
    _ = k.divisors.card * 2 := by rw [divisors_card_prime hprime]
    _ = 2 * k.divisors.card := by omega

/-- Uniform elementary divisor bound, valid for every positive natural number.

Every proper divisor of `k` is at most `k / 2`; adding `k` itself gives
`τ(k) ≤ k / 2 + 1`, which implies the stated bound.
-/
theorem two_mul_divisors_card_le_add_two (k : ℕ) (hk1 : 1 ≤ k) :
    2 * k.divisors.card ≤ k + 2 := by
  have hk0 : k ≠ 0 := by omega
  have hsub : k.properDivisors ⊆ Finset.Icc 1 (k / 2) := by
    intro d hd
    have hdpos : 1 ≤ d := Nat.pos_of_mem_properDivisors hd
    obtain ⟨q, hq, hk⟩ :=
      (Nat.mem_properDivisors_iff_exists hk0).mp hd
    have hd2 : d * 2 ≤ k := by
      rw [hk]
      exact Nat.mul_le_mul_left d hq
    have hdhalf : d ≤ k / 2 :=
      (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).mpr hd2
    exact Finset.mem_Icc.mpr ⟨hdpos, hdhalf⟩
  have hproper : k.properDivisors.card ≤ k / 2 := by
    calc
      k.properDivisors.card ≤ (Finset.Icc 1 (k / 2)).card :=
        Finset.card_le_card hsub
      _ = k / 2 := by rw [Nat.card_Icc]; omega
  have hcard : k.divisors.card = k.properDivisors.card + 1 := by
    rw [← Nat.insert_self_properDivisors hk0,
      Finset.card_insert_of_notMem Nat.self_notMem_properDivisors]
  omega

/-- Arbitrary-depth conditional finite-window theorem.

If all prefix-LCM cofactors through depth `K` are prime and larger than their
corresponding shifts, then `prefixLcm K * t` satisfies every Erdős #647
divisor budget through that depth.
-/
theorem allDepthConditionalWindow {K t : ℕ}
    (hprime : PrimeCofactorHyp K t) :
    WindowGood K (prefixLcm K * t) := by
  intro k hk1 hkK
  obtain ⟨hqprime, hqgt⟩ := hprime k hk1 hkK
  rw [ArithmeticFunction.sigma_zero_apply,
    tau_eq_two_mul_divisors hk1 hkK hqprime hqgt]
  exact two_mul_divisors_card_le_add_two k hk1

/-!
The following exported theorem repeats the short deterministic argument with
the construction expanded in its statement.  This makes the publication
artifact and its proof-search episode independent of namespace-local helper
declarations.
-/

/-- Standalone, fully exposed arbitrary-depth conditional-window theorem. -/
theorem erdos647_all_depth_conditional_window :
    ∀ K t : ℕ,
      (∀ k, 1 ≤ k → k ≤ K →
        Nat.Prime ((((Finset.Icc 1 K).lcm id / k) * t) - 1) ∧
          k < (((Finset.Icc 1 K).lcm id / k) * t - 1)) →
      ∀ k, 1 ≤ k → k ≤ K →
        ArithmeticFunction.sigma 0 ((Finset.Icc 1 K).lcm id * t - k) ≤
          k + 2 := by
  intro K t hprime k hk1 hkK
  let L : ℕ := (Finset.Icc 1 K).lcm id
  let q : ℕ := (L / k) * t - 1
  have hpair : Nat.Prime q ∧ k < q := by
    simpa [L, q] using hprime k hk1 hkK
  obtain ⟨hqprime, hqgt⟩ := hpair
  have hdvd : k ∣ L := by
    dsimp [L]
    simpa using
      (Finset.dvd_lcm (s := Finset.Icc 1 K) (f := id)
        (by simpa using Finset.mem_Icc.mpr ⟨hk1, hkK⟩))
  have hfactor : L * t - k = k * q := by
    dsimp [q]
    have hmul : (((L / k) * k) * t) = k * ((L / k) * t) := by
      ring
    calc
      L * t - k = (((L / k) * k) * t) - k := by
        rw [Nat.div_mul_cancel hdvd]
      _ = k * ((L / k) * t) - k := by rw [hmul]
      _ = k * (((L / k) * t) - 1) := by
        conv_rhs => rw [Nat.mul_sub_left_distrib, Nat.mul_one]
  have hcop : Nat.Coprime k q := by
    have hnot : ¬ q ∣ k := by
      intro hdiv
      have hle : q ≤ k := Nat.le_of_dvd hk1 hdiv
      exact Nat.not_le_of_lt hqgt hle
    exact Nat.Coprime.symm (hqprime.coprime_iff_not_dvd.mpr hnot)
  have hqcard : q.divisors.card = 2 := by
    rw [Nat.Prime.divisors hqprime]
    exact Finset.card_pair hqprime.one_lt.ne
  have htau : (L * t - k).divisors.card = 2 * k.divisors.card := by
    calc
      (L * t - k).divisors.card = (k * q).divisors.card := by rw [hfactor]
      _ = k.divisors.card * q.divisors.card := hcop.card_divisors_mul
      _ = k.divisors.card * 2 := by rw [hqcard]
      _ = 2 * k.divisors.card := by omega
  have hk0 : k ≠ 0 := by omega
  have hsub : k.properDivisors ⊆ Finset.Icc 1 (k / 2) := by
    intro d hd
    have hdpos : 1 ≤ d := Nat.pos_of_mem_properDivisors hd
    obtain ⟨a, ha, hka⟩ :=
      (Nat.mem_properDivisors_iff_exists hk0).mp hd
    have hd2 : d * 2 ≤ k := by
      rw [hka]
      exact Nat.mul_le_mul_left d ha
    have hdhalf : d ≤ k / 2 :=
      (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).mpr hd2
    exact Finset.mem_Icc.mpr ⟨hdpos, hdhalf⟩
  have hproper : k.properDivisors.card ≤ k / 2 := by
    calc
      k.properDivisors.card ≤ (Finset.Icc 1 (k / 2)).card :=
        Finset.card_le_card hsub
      _ = k / 2 := by rw [Nat.card_Icc]; omega
  have hcard : k.divisors.card = k.properDivisors.card + 1 := by
    rw [← Nat.insert_self_properDivisors hk0,
      Finset.card_insert_of_notMem Nat.self_notMem_properDivisors]
  change ArithmeticFunction.sigma 0 (L * t - k) ≤ k + 2
  rw [ArithmeticFunction.sigma_zero_apply, htau]
  omega

end Erdos647AllDepthConditionalWindow
