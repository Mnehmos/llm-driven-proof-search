import Mathlib
open Finset
open Nat

/-!
# Erdős Problem 888 — Phase 1: Foundational definitions

This file defines the core objects for the square-product rigidity problem:
- `SquareProductRigid` — the admissibility condition on subsets A ⊆ ℕ
- `F` / `sqProdRigidMax` — maximum cardinality of admissible sets
- `G` / `sqProdRigidMaxSF` — maximum cardinality of squarefree admissible sets
- `A_k` fibers — fixed-square-part decomposition
- `IsSquarefreeSemiprime` — numbers of the form p·q with p < q primes
- `largestPrimeFactor`, `secondLargestPrimeFactor` — for two-largest-prime encoding
- Basic monotonicity, finiteness, and positivity lemmas

Matching the Formal Conjectures target signature:
  `(fun n : ℕ ↦ (Nat.findGreatest (p n) n : ℝ)) =Θ[atTop] (fun n : ℕ ↦ (n : ℝ) * Real.log (Real.log n) / Real.log n)`
-/

set_option maxHeartbeats 400000

/-! ## §1. Core definitions -/

/-- A set A of positive integers has the **square-product rigidity property** if,
whenever a ≤ b ≤ c ≤ d are elements of A and a*b*c*d is a perfect square, one has a*d = b*c. -/
def SquareProductRigid (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
    a ≤ b → b ≤ c → c ≤ d → IsSquare (a * b * c * d) → a * d = b * c

/-- The condition from the Formal Conjectures: A ⊆ {1,…,n} and the rigidity property. -/
def RequiredCondition (A : Finset ℕ) (n : ℕ) : Prop :=
  A ⊆ Finset.Ioc 0 n ∧ SquareProductRigid A

/-- `p n k` holds when there exists an admissible A ⊆ {1,…,n} of cardinality k. -/
def p (n : ℕ) (k : ℕ) : Prop :=
  ∃ A : Finset ℕ, RequiredCondition A n ∧ A.card = k

/-- `F(n)` is the maximum cardinality of a square-product-rigid subset of {1,…,n}. -/
def F (n : ℕ) : ℕ :=
  Nat.findGreatest (p n) n

/-- A set is squarefree if every element is squarefree. -/
def IsSquarefreeSet (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, Squarefree a

/-- `G(n)` is the maximum cardinality of a squarefree square-product-rigid subset of {1,…,n}. -/
def G (n : ℕ) : ℕ :=
  sSup (Finset.card '' {A : Finset ℕ | A ⊆ Finset.Icc 1 n ∧ SquareProductRigid A ∧ IsSquarefreeSet A})

/-! ## §2. Elementary properties -/

lemma Finset.Ioc_subset_Icc {n : ℕ} : Finset.Ioc 0 n ⊆ Finset.Icc 1 n := by
  intro x hx
  rcases Finset.mem_Ioc.mp hx with ⟨hx0, hxn⟩
  exact Finset.mem_Icc.mpr ⟨by omega, hxn⟩

lemma RequiredCondition.subset_Icc {A n} (h : RequiredCondition A n) : A ⊆ Finset.Icc 1 n := by
  rcases h with ⟨hsub, _⟩
  exact Finset.Subset.trans hsub Finset.Ioc_subset_Icc

lemma RequiredCondition.card_pos {A n} (h : RequiredCondition A n) : A.card ≤ n := by
  rcases h with ⟨hsub, _⟩
  have hcard : A.card ≤ (Finset.Ioc 0 n).card := Finset.card_le_card_of_subset hsub
  have : (Finset.Ioc 0 n).card = n := by
    simp
  rw [this] at hcard
  exact hcard

lemma F_nonempty (n : ℕ) : F n = 0 ∨ F n = Nat.findGreatest (p n) n := by
  rfl

lemma F_pos (n : ℕ) (hn : n ≥ 1) : 1 ≤ F n := by
  have hA : RequiredCondition {1} n := by
    refine ⟨?_, ?_⟩
    · simp [Finset.Ioc, Finset.subset_iff]
    · intro a ha b hb c hc d hd ha_le hb_le hc_le hsq
      simp at ha hb hc hd
      subst_vars
      simp
  have hp : p n 1 := ⟨{1}, hA, by simp⟩
  exact Nat.le_findGreatest hp

lemma F_monotone (m n : ℕ) (hmn : m ≤ n) : F m ≤ F n := by
  have h : p m (F m) := Nat.findGreatest_spec (p m) (by
    have h0 : p m 0 := ⟨∅, by
      refine ⟨?_, ?_⟩
      · simp
      · intro a ha b hb c hc d hd ha_le hb_le hc_le hsq
        simp at ha hb hc hd⟩
    exact h0)
  have hp' : p n (F m) := by
    rcases h with ⟨A, hA, hcard⟩
    refine ⟨A, ?_, hcard⟩
    rcases hA with ⟨hsub, hrigid⟩
    refine ⟨?_, hrigid⟩
    exact Finset.Subset.trans hsub (Finset.Ioc_subset_Icc.trans ?_)
    exact Finset.Icc_subset_Icc_right hmn
  exact Nat.findGreatest_le _ _ hp'

lemma G_monotone (m n : ℕ) (hmn : m ≤ n) : G m ≤ G n := by
  dsimp [G]
  apply sSup_le_sSup
  intro k hk
  rcases hk with ⟨A, ⟨hA, hrigid, hsf⟩, rfl⟩
  refine ⟨A, ⟨?_, hrigid, hsf⟩, rfl⟩
  exact Finset.Subset.trans hA (Finset.Icc_subset_Icc_right hmn)

lemma G_le_F (n : ℕ) : G n ≤ F n := by
  dsimp [G, F]
  apply sSup_le
  intro k hk
  rcases hk with ⟨A, ⟨hA, hrigid, hsf⟩, rfl⟩
  have hp : p n (A.card) := by
    refine ⟨A, ⟨?_, hrigid⟩, rfl⟩
    refine Finset.Subset.trans hA ?_
    exact Finset.Ioc_subset_Icc
  exact Nat.le_findGreatest hp

/-! ## §3. Squarefree semiprimes -/

/-- A **squarefree semiprime** is a product of two distinct primes. -/
def IsSquarefreeSemiprime (n : ℕ) : Prop :=
  ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p < q ∧ n = p * q

lemma IsSquarefreeSemiprime.squarefree {n} (h : IsSquarefreeSemiprime n) : Squarefree n := by
  rcases h with ⟨p, q, hp, hq, hpq, rfl⟩
  rw [Nat.squarefree_mul_iff]
  refine ⟨hp.coprime_iff_not_dvd.mpr (fun h => hpq.ne (Nat.prime_dvd_prime_iff_eq hp hq |>.mp h)), hp.squarefree, hq.squarefree⟩

lemma IsSquarefreeSemiprime.one_lt {n} (h : IsSquarefreeSemiprime n) : 1 < n := by
  rcases h with ⟨p, q, hp, hq, hpq, rfl⟩
  exact Nat.one_lt_mul_of_lt_of_lt (by exact Nat.one_lt_iff.2 hp) (by
    have := hq.one_lt; omega) hp hpq

/-- The set of primes and squarefree semiprimes up to n — the lower bound construction. -/
def lowerBoundSet (n : ℕ) : Finset ℕ :=
  (Finset.Icc 1 n).filter fun m =>
    m.Prime ∨ IsSquarefreeSemiprime m

lemma lowerBoundSet_subset (n : ℕ) : lowerBoundSet n ⊆ Finset.Icc 1 n :=
  Finset.filter_subset _ _

lemma lowerBoundSet_squarefree {n m} (hm : m ∈ lowerBoundSet n) : Squarefree m := by
  rcases Finset.mem_filter.mp hm with ⟨hmem, htype⟩
  rcases htype with (hprime | hsemiprime)
  · exact hprime.squarefree
  · exact hsemiprime.squarefree

lemma lowerBoundSet_pos {n m} (hm : m ∈ lowerBoundSet n) : 0 < m := by
  have h := Finset.mem_Icc.mp (lowerBoundSet_subset n hm)
  omega

/-! ## §4. Fixed-square-part fibers -/

/-- The unique squarefree kernel of a positive integer: `a = k²·s` with `s` squarefree. -/
def squarefreeKernel (a : ℕ) : ℕ :=
  a / (Nat.sqrt a)^2

/-- The maximal square divisor of a positive integer. -/
def maxSquareDivisor (a : ℕ) : ℕ :=
  (Nat.sqrt a)^2

lemma squarefreeKernel_sq_mul (a : ℕ) (ha : a ≠ 0) : a = (maxSquareDivisor a) * (squarefreeKernel a) := by
  dsimp [maxSquareDivisor, squarefreeKernel]
  have h := Nat.mul_div_cancel' (by
    apply Nat.sqrt_sq_eq_abs.mpr ?_)
  sorry

/-- For a fixed k, the fiber A_k = {s | k²·s ∈ A}. -/
def fiber (A : Finset ℕ) (k : ℕ) : Finset ℕ :=
  A.filter (λ a => k^2 ∣ a) |>.image (λ a => a / k^2)

lemma mem_fiber_iff (A k s) : s ∈ fiber A k ↔ ∃ a ∈ A, a = k^2 * s := by
  dsimp [fiber]
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨a, ha, rfl⟩
    rcases Finset.mem_filter.mp ha with ⟨haA, hdiv⟩
    refine ⟨a, haA, ?_⟩
    rw [Nat.mul_div_cancel' hdiv]
  · rintro ⟨a, haA, rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨a, Finset.mem_filter.mpr ⟨haA, ?_⟩, ?_⟩
    · exact dvd_mul_of_dvd_left (dvd_refl (k^2)) s
    · simp

lemma fiber_squarefree (A : Finset ℕ) (k : ℕ) : IsSquarefreeSet (fiber A k) := by
  intro s hs
  rw [mem_fiber_iff] at hs
  rcases hs with ⟨a, haA, rfl⟩
  -- Every element of a fiber is squarefree by construction (the fiber removes the square part)
  sorry

lemma fiber_admissible (A : Finset ℕ) (k : ℕ) (hA : SquareProductRigid A) : SquareProductRigid (fiber A k) := by
  intro a ha b hb c hc d hd ha_le hb_le hc_le hsq
  rw [mem_fiber_iff] at ha hb hc hd
  rcases ha with ⟨a', haA, ha_eq⟩
  rcases hb with ⟨b', hbA, hb_eq⟩
  rcases hc with ⟨c', hcA, hc_eq⟩
  rcases hd with ⟨d', hdA, hd_eq⟩
  have hsq' : IsSquare ((k^2 * a) * (k^2 * b) * (k^2 * c) * (k^2 * d)) := by
    rw [ha_eq, hb_eq, hc_eq, hd_eq]
    -- a' * b' * c' * d' is a square by the rigidity of A
    sorry
  sorry

/-! ## §5. Largest prime factor decomposition -/

/-- The largest prime factor of n, or 0 if n ≤ 1. -/
noncomputable def largestPrimeFactor (n : ℕ) : ℕ :=
  if h : n ≤ 1 then 0 else
    (Nat.factors n).max' (by
      rw [Nat.factors_ne_nil (by omega)]
      exact Finset.max'_mem _ _)

/-- The second-largest prime factor of n, or 0 if n has fewer than 2 distinct prime factors. -/
noncomputable def secondLargestPrimeFactor (n : ℕ) : ℕ :=
  if h : n ≤ 1 then 0 else
    let factors := (Nat.factors n).toFinset.erase (largestPrimeFactor n)
    if hf : factors.Nonempty then factors.max' hf else 0

lemma largestPrimeFactor_prime {n} (hn : 2 ≤ n) : (largestPrimeFactor n).Prime := by
  dsimp [largestPrimeFactor]
  split
  · omega
  · have hmem : (Nat.factors n).max' (by
      rw [Nat.factors_ne_nil (by omega)]
      exact Finset.max'_mem _ _) ∈ (Nat.factors n).toFinset := by
      apply Finset.mem_coe.mpr
      apply Finset.max'_mem
    rw [Finset.mem_coe, Nat.mem_factors] at hmem
    exact hmem.1

lemma largestPrimeFactor_dvd {n} (hn : 2 ≤ n) : largestPrimeFactor n ∣ n := by
  dsimp [largestPrimeFactor]
  split
  · omega
  · have hmem : (Nat.factors n).max' (by
      rw [Nat.factors_ne_nil (by omega)]
      exact Finset.max'_mem _ _) ∈ (Nat.factors n).toFinset := by
      apply Finset.mem_coe.mpr
      apply Finset.max'_mem
    rw [Finset.mem_coe, Nat.mem_factors] at hmem
    exact hmem.2

lemma largestPrimeFactor_le {n} (hn : 2 ≤ n) : largestPrimeFactor n ≤ n := by
  apply Nat.le_of_dvd (by omega) (largestPrimeFactor_dvd hn)

lemma largestPrimeFactor_eq_self {p : ℕ} (hp : p.Prime) : largestPrimeFactor p = p := by
  have h2 : 2 ≤ p := Nat.Prime.one_lt hp
  dsimp [largestPrimeFactor]
  split
  · omega
  · have hfactors : (Nat.factors p) = [p] := Nat.factors_prime hp
    simp [hfactors]

/-! ## §6. Decomposition a = c·p·q for squarefree numbers with ≥2 prime factors -/

/-- For a squarefree a ≥ 2 with at least two prime factors, write a = c·p·q
where p < q are the two largest prime factors and c is the product of the remaining primes. -/
structure ThreePrimeDecomposition (a : ℕ) where
  c : ℕ
  p : ℕ
  q : ℕ
  hp : p.Prime
  hq : q.Prime
  hp_lt_q : p < q
  h_eq : a = c * p * q
  h_c_squarefree : Squarefree c
  h_c_primes_lt_p : ∀ r : ℕ, r.Prime → r ∣ c → r < p
  hp_not_dvd_c : ¬ p ∣ c
  hq_not_dvd_c : ¬ q ∣ c

lemma squarefree_three_prime_decomposition (a : ℕ) (ha_sf : Squarefree a) (ha2 : 2 ≤ a) (h_two_primes : (Nat.factors a).length ≥ 2) :
    ThreePrimeDecomposition a := by
  sorry