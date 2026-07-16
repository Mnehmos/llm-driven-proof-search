import Mathlib

/-!
# Erdős #647 — arbitrary pairwise-coprime blocks produce novel primes

This is the first generic production/novelty theorem for the growing-gauntlet
lane.  A finite block of pairwise-coprime values larger than one produces one
distinct prime divisor per value (chosen canonically as `Nat.minFac`).  If no
prime from an older finite catalog divides a value in the new block, every
produced prime is genuinely new relative to that catalog.

The result is deliberately conditional on pairwise coprimality and avoidance
of the old catalog.  It does not by itself prove that Erdős #647 candidates
generate arbitrarily large such blocks; that production hypothesis remains
the open mathematical seam.

Both declarations were independently kernel-verified through the tracked
proof-search pipeline on 2026-07-16.

Production/novelty theorem:

* preverification job: `e8584b86-ad8f-4bcf-be78-9f145dd14a45`
* problem version: `cc66c3da-fe7c-42fd-b493-5b1b5e71a0ca`
* episode: `89a875c4-8854-4ad7-b1f3-1953bf797918`
* root statement hash:
  `2c9868b1ee2401420669d455ee7fd245705cafbeac64f8a302ea169822385808`

Shared-host accumulation theorem:

* preverification job: `af48ba8a-9f80-4301-a2b9-9775cb5e98e3`
* problem version: `169f1332-6dae-4fb5-a544-d16849465b0d`
* episode: `1b13572b-7738-4822-b046-358ca49a8ad8`
* root statement hash:
  `d7c77eeae0ffb1e2aa4593afe724a15614f1de8b8f9269aed3906f930442ce45`

Both tracked outcomes are `kernel_verified`.
-/

theorem erdos647_pairwise_coprime_block_produces_novel_primes :
    ∀ (block old : Finset ℕ),
      (∀ m ∈ block, 1 < m) →
      (∀ m ∈ block, ∀ n ∈ block, m ≠ n → Nat.Coprime m n) →
      (∀ p ∈ old, ∀ m ∈ block, ¬ p ∣ m) →
      (block.image Nat.minFac).card = block.card ∧
        Disjoint old (block.image Nat.minFac) ∧
        ∀ p ∈ block.image Nat.minFac,
          p.Prime ∧ ∃ m ∈ block, p ∣ m := by
  intro block old hlarge hcop hold
  have hinj : Set.InjOn Nat.minFac (block : Set ℕ) := by
    intro m hm n hn hfac
    simp only [Finset.mem_coe] at hm hn
    by_contra hmn
    have hmnCop : Nat.Coprime m n := hcop m hm n hn hmn
    have hmPrime : m.minFac.Prime := Nat.minFac_prime (ne_of_gt (hlarge m hm))
    have hmDvd : m.minFac ∣ m := Nat.minFac_dvd m
    have hnDvd : m.minFac ∣ n := by
      rw [hfac]
      exact Nat.minFac_dvd n
    exact hmPrime.ne_one (Nat.eq_one_of_dvd_coprimes hmnCop hmDvd hnDvd)
  have hcard : (block.image Nat.minFac).card = block.card :=
    Finset.card_image_iff.mpr hinj
  have hdisj : Disjoint old (block.image Nat.minFac) := by
    rw [Finset.disjoint_left]
    intro p hpold hpnew
    simp only [Finset.mem_image] at hpnew
    obtain ⟨m, hm, rfl⟩ := hpnew
    exact hold m.minFac hpold m hm (Nat.minFac_dvd m)
  refine ⟨hcard, hdisj, ?_⟩
  intro p hp
  simp only [Finset.mem_image] at hp
  obtain ⟨m, hm, rfl⟩ := hp
  exact ⟨Nat.minFac_prime (ne_of_gt (hlarge m hm)),
    ⟨m, hm, Nat.minFac_dvd m⟩⟩

/-- If all of the distinct primes produced by a pairwise-coprime block divide
one positive host, then the host is at least exponential in the block size.
This isolates the precise shared-host accumulation mechanism needed by the
negative lane; without the `hhost` premise, pairwise coprimality alone gives no
size contradiction. -/
theorem erdos647_shared_host_bounds_pairwise_coprime_block :
    ∀ (block : Finset ℕ) (H : ℕ),
      0 < H →
      (∀ m ∈ block, 1 < m) →
      (∀ m ∈ block, ∀ n ∈ block, m ≠ n → Nat.Coprime m n) →
      (∀ m ∈ block, m.minFac ∣ H) →
      2 ^ block.card ≤ H := by
  intro block H hH hlarge hcop hhost
  let primes := block.image Nat.minFac
  have hinj : Set.InjOn Nat.minFac (block : Set ℕ) := by
    intro m hm n hn hfac
    simp only [Finset.mem_coe] at hm hn
    by_contra hmn
    have hmnCop : Nat.Coprime m n := hcop m hm n hn hmn
    have hmPrime : m.minFac.Prime := Nat.minFac_prime (ne_of_gt (hlarge m hm))
    have hmDvd : m.minFac ∣ m := Nat.minFac_dvd m
    have hnDvd : m.minFac ∣ n := by
      rw [hfac]
      exact Nat.minFac_dvd n
    exact hmPrime.ne_one (Nat.eq_one_of_dvd_coprimes hmnCop hmDvd hnDvd)
  have hcard : primes.card = block.card := by
    dsimp [primes]
    exact Finset.card_image_iff.mpr hinj
  have hprime : ∀ p ∈ primes, p.Prime := by
    intro p hp
    dsimp [primes] at hp
    simp only [Finset.mem_image] at hp
    obtain ⟨m, hm, rfl⟩ := hp
    exact Nat.minFac_prime (ne_of_gt (hlarge m hm))
  have hsubset : primes ⊆ H.primeFactors := by
    intro p hp
    have hpPrime : p.Prime := hprime p hp
    dsimp [primes] at hp
    simp only [Finset.mem_image] at hp
    obtain ⟨m, hm, rfl⟩ := hp
    exact Nat.mem_primeFactors.mpr
      ⟨hpPrime, hhost m hm, ne_of_gt hH⟩
  have hprodDvd : (∏ p ∈ primes, p) ∣ H := by
    exact (Finset.prod_dvd_prod_of_subset primes H.primeFactors (fun p => p) hsubset).trans
      (Nat.prod_primeFactors_dvd H)
  calc
    2 ^ block.card = 2 ^ primes.card := by rw [hcard]
    _ = ∏ p ∈ primes, 2 := by simp
    _ ≤ ∏ p ∈ primes, p := by
      apply Finset.prod_le_prod'
      intro p hp
      exact (hprime p hp).two_le
    _ ≤ H := Nat.le_of_dvd hH hprodDvd
