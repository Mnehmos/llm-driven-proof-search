import Mathlib

/-!
# Erdős #647 — exact shift-difference gcd and large-factor novelty

Kernel-verified development for the growing-gauntlet lane.  The central
identity is

`gcd (n - k₁) (n - k₂) = gcd (n - k₁) (k₂ - k₁)`

for ordered shifts `k₁ ≤ k₂ < n`.  Thus every common divisor of two shifted
values divides the coordinate difference, and any chosen factor larger than
that difference cannot be reused.  The final theorem packages this as a
finite injectivity/cardinality statement without requiring the shifted values
themselves to be pairwise coprime.  If those distinct factors are prime and
all divide one positive host `H`, the final theorem gives the exponential
accumulation bound `2 ^ shifts.card ≤ H`.

Three strongest roots were independently verified through the tracked
proof-search pipeline on 2026-07-16.

Exact gcd transport:

* preverification job: `4211239a-a002-4a04-9449-95a27ea25f6c`
* problem version: `014f5c3b-3287-4c91-8819-50d360817dbf`
* episode: `3e3a35df-8d76-42fa-8323-e6af0aa7c2d6`
* root statement hash:
  `180fddff638fa431117e9a1aaa289c12154122ea6ac02b3729dc48ae937765be`

Finite large-factor injectivity and exact image cardinality:

* preverification job: `f3dc66db-7a55-41da-af6c-8ab9072edff0`
* problem version: `e97682df-b183-42f9-9e0f-4d5bdbaf85cb`
* episode: `644db370-4230-4bf7-bc84-42c2530f42ae`
* root statement hash:
  `218736f155639fda6a47e014dcfdb831571e322f35b6283bf8d56751d8884502`

Exponential shared-prime-host accumulation:

* preverification job: `ca04211f-21c2-43ab-9ffa-9ead00af15cc`
* problem version: `3f78f80a-f7d3-484a-b8d7-1548757fda96`
* episode: `5e865863-6979-4f24-975f-843595edfe10`
* root statement hash:
  `690dee8209ad2f6e2c5c8c47d7b60416ff1c4146ca1ed73ad7db1639c4406a1b`

All three tracked outcomes are `kernel_verified`.
-/

/-- Exact Euclidean transport from two shifted values to their shift gap. -/
theorem erdos647_shift_gcd_eq_gcd_difference :
    ∀ n k₁ k₂ : ℕ, k₁ ≤ k₂ → k₂ < n →
      Nat.gcd (n - k₁) (n - k₂) = Nat.gcd (n - k₁) (k₂ - k₁) := by
  intro n k₁ k₂ hk₁k₂ hk₂n
  apply Nat.dvd_antisymm
  · apply Nat.dvd_gcd
    · exact Nat.gcd_dvd_left _ _
    · have h := Nat.dvd_sub
        (Nat.gcd_dvd_left (n - k₁) (n - k₂))
        (Nat.gcd_dvd_right (n - k₁) (n - k₂))
      have hgap : (n - k₁) - (n - k₂) = k₂ - k₁ := by omega
      rwa [hgap] at h
  · apply Nat.dvd_gcd
    · exact Nat.gcd_dvd_left _ _
    · have h := Nat.dvd_sub
        (Nat.gcd_dvd_left (n - k₁) (k₂ - k₁))
        (Nat.gcd_dvd_right (n - k₁) (k₂ - k₁))
      have hshift : (n - k₁) - (k₂ - k₁) = n - k₂ := by omega
      rwa [hshift] at h

/-- Every common divisor of two ordered shifted values divides their gap. -/
theorem erdos647_shift_common_divisor_dvd_difference :
    ∀ n k₁ k₂ d : ℕ, k₁ ≤ k₂ → k₂ < n →
      d ∣ n - k₁ → d ∣ n - k₂ → d ∣ k₂ - k₁ := by
  intro n k₁ k₂ d hk₁k₂ hk₂n hd₁ hd₂
  have h := Nat.dvd_sub hd₁ hd₂
  have hgap : (n - k₁) - (n - k₂) = k₂ - k₁ := by omega
  rwa [hgap] at h

/-- Ordered shifted values are coprime exactly when the first value is
coprime to the coordinate gap. -/
theorem erdos647_shift_coprime_iff_coprime_difference :
    ∀ n k₁ k₂ : ℕ, k₁ ≤ k₂ → k₂ < n →
      (Nat.Coprime (n - k₁) (n - k₂) ↔
        Nat.Coprime (n - k₁) (k₂ - k₁)) := by
  intro n k₁ k₂ hk₁k₂ hk₂n
  unfold Nat.Coprime
  rw [erdos647_shift_gcd_eq_gcd_difference n k₁ k₂ hk₁k₂ hk₂n]

/-- A prime (indeed, any positive factor) larger than the shift gap cannot
divide both shifted values. -/
theorem erdos647_large_prime_cannot_repeat_across_shifts :
    ∀ n k₁ k₂ p : ℕ, k₁ < k₂ → k₂ < n → p.Prime → k₂ - k₁ < p →
      p ∣ n - k₁ → ¬ p ∣ n - k₂ := by
  intro n k₁ k₂ p hk₁k₂ hk₂n hp hgaplt hp₁ hp₂
  have hgap : p ∣ k₂ - k₁ :=
    erdos647_shift_common_divisor_dvd_difference n k₁ k₂ p hk₁k₂.le hk₂n hp₁ hp₂
  have hgap_pos : 0 < k₂ - k₁ := by omega
  have hple : p ≤ k₂ - k₁ := Nat.le_of_dvd hgap_pos hgap
  omega

/-- Exact finite criterion for a shifted block to be pairwise coprime. -/
theorem erdos647_shift_finset_pairwise_coprime_iff_differences :
    ∀ (n : ℕ) (shifts : Finset ℕ),
      (∀ k ∈ shifts, k < n) →
      ((∀ k₁ ∈ shifts, ∀ k₂ ∈ shifts, k₁ ≠ k₂ →
          Nat.Coprime (n - k₁) (n - k₂)) ↔
        ∀ k₁ ∈ shifts, ∀ k₂ ∈ shifts, k₁ < k₂ →
          Nat.Coprime (n - k₁) (k₂ - k₁)) := by
  intro n shifts hlt
  constructor
  · intro hpair k₁ hk₁ k₂ hk₂ hk₁k₂
    rw [← erdos647_shift_coprime_iff_coprime_difference n k₁ k₂ hk₁k₂.le
      (hlt k₂ hk₂)]
    exact hpair k₁ hk₁ k₂ hk₂ (ne_of_lt hk₁k₂)
  · intro hgap k₁ hk₁ k₂ hk₂ hkne
    rcases lt_or_gt_of_ne hkne with hk₁k₂ | hk₂k₁
    · rw [erdos647_shift_coprime_iff_coprime_difference n k₁ k₂ hk₁k₂.le
        (hlt k₂ hk₂)]
      exact hgap k₁ hk₁ k₂ hk₂ hk₁k₂
    · rw [Nat.coprime_comm]
      rw [erdos647_shift_coprime_iff_coprime_difference n k₂ k₁ hk₂k₁.le
        (hlt k₁ hk₁)]
      exact hgap k₂ hk₂ k₁ hk₁ hk₂k₁

/--
Finite large-factor novelty.  If `factor k` divides `n-k` and is larger
than every forward gap out of `k`, then distinct shifts receive distinct
factors.  The cardinality conclusion is the exact counting interface needed
by a growing-gauntlet argument; primality may be supplied separately by the
caller when the factors are chosen prime.
-/
theorem erdos647_large_shift_factors_injective :
    ∀ (n : ℕ) (shifts : Finset ℕ) (factor : ℕ → ℕ),
      (∀ k ∈ shifts, k < n) →
      (∀ k ∈ shifts, factor k ∣ n - k) →
      (∀ k₁ ∈ shifts, ∀ k₂ ∈ shifts, k₁ < k₂ → k₂ - k₁ < factor k₁) →
      Set.InjOn factor (shifts : Set ℕ) ∧
        (shifts.image factor).card = shifts.card := by
  intro n shifts factor hlt hdvd hlarge
  have hinj : Set.InjOn factor (shifts : Set ℕ) := by
    intro k₁ hk₁ k₂ hk₂ heq
    simp only [Finset.mem_coe] at hk₁ hk₂
    by_contra hkne
    rcases lt_or_gt_of_ne hkne with hk₁k₂ | hk₂k₁
    · have hgap : factor k₁ ∣ k₂ - k₁ :=
        erdos647_shift_common_divisor_dvd_difference n k₁ k₂ (factor k₁)
          hk₁k₂.le (hlt k₂ hk₂) (hdvd k₁ hk₁) (by simpa [heq] using hdvd k₂ hk₂)
      have hgap_pos : 0 < k₂ - k₁ := by omega
      have hle := Nat.le_of_dvd hgap_pos hgap
      exact (not_lt_of_ge hle) (hlarge k₁ hk₁ k₂ hk₂ hk₁k₂)
    · have hgap : factor k₂ ∣ k₁ - k₂ :=
        erdos647_shift_common_divisor_dvd_difference n k₂ k₁ (factor k₂)
          hk₂k₁.le (hlt k₁ hk₁) (hdvd k₂ hk₂) (by simpa [heq] using hdvd k₁ hk₁)
      have hgap_pos : 0 < k₁ - k₂ := by omega
      have hle := Nat.le_of_dvd hgap_pos hgap
      exact (not_lt_of_ge hle) (hlarge k₂ hk₂ k₁ hk₁ hk₂k₁)
  exact ⟨hinj, Finset.card_image_iff.mpr hinj⟩

/--
Shared-host consequence for a growing shifted gauntlet.  A distinct large
prime is selected from each shifted value.  Shift-difference non-reuse makes
the selected primes injective, so if they are all forced into one positive
host `H`, then `H` is at least exponential in the number of shifts.
-/
theorem erdos647_large_shift_prime_host_bound :
    ∀ (n : ℕ) (shifts : Finset ℕ) (factor : ℕ → ℕ) (H : ℕ),
      0 < H →
      (∀ k ∈ shifts, k < n) →
      (∀ k ∈ shifts,
        (factor k).Prime ∧ factor k ∣ n - k ∧ factor k ∣ H) →
      (∀ k₁ ∈ shifts, ∀ k₂ ∈ shifts,
        k₁ < k₂ → k₂ - k₁ < factor k₁) →
      2 ^ shifts.card ≤ H := by
  intro n shifts factor H hH hlt hfactor hlarge
  have hnovel := erdos647_large_shift_factors_injective n shifts factor hlt
    (fun k hk => (hfactor k hk).2.1) hlarge
  let primes := shifts.image factor
  have hcard : primes.card = shifts.card := by
    dsimp [primes]
    exact hnovel.2
  have hprime : ∀ p ∈ primes, p.Prime := by
    intro p hp
    dsimp [primes] at hp
    simp only [Finset.mem_image] at hp
    obtain ⟨k, hk, rfl⟩ := hp
    exact (hfactor k hk).1
  have hsubset : primes ⊆ H.primeFactors := by
    intro p hp
    have hpPrime : p.Prime := hprime p hp
    dsimp [primes] at hp
    simp only [Finset.mem_image] at hp
    obtain ⟨k, hk, rfl⟩ := hp
    exact Nat.mem_primeFactors.mpr
      ⟨hpPrime, (hfactor k hk).2.2, ne_of_gt hH⟩
  have hprodDvd : (∏ p ∈ primes, p) ∣ H := by
    exact (Finset.prod_dvd_prod_of_subset primes H.primeFactors
      (fun p => p) hsubset).trans (Nat.prod_primeFactors_dvd H)
  calc
    2 ^ shifts.card = 2 ^ primes.card := by rw [hcard]
    _ = ∏ p ∈ primes, 2 := by simp
    _ ≤ ∏ p ∈ primes, p := by
      apply Finset.prod_le_prod'
      intro p hp
      exact (hprime p hp).two_le
    _ ≤ H := Nat.le_of_dvd hH hprodDvd
