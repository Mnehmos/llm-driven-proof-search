import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib

/-!
# Erdős #647 — Family 3: bridging-closure theorems

Self-contained Lean source (checks against Mathlib with `lake`; no project DB
needed), recovered via `proof_export{episode_id, format: "lean"}` against the
pinned environment (`environment_hash 9e26d28e…`).

Each theorem derives a sieve-row exclusion `coeff·N % ℓ ≠ 1` (for the stated
prime range) DIRECTLY from the matching Family-2 classification theorem, so
the modular reduction rests on proofs, not on trusting a `native_decide`
predicate count. Named `erdos647_bridge{shift}_le{19,29}`.

**Coverage status**: all 8 shifts at `11 ≤ ℓ ≤ 19` (legacy tier) are here.
At the wider `11 ≤ ℓ ≤ 29` (current tier, backing the mod-23/mod-29
sub-AP refinements): 8 of 13 are here (shifts 1,2,3,4,6,8,9,10); the
remaining 5 (shifts 5,12,18,20,24) are NOT yet committed — their proof
bodies are in the environment but not yet exported into this file. See
../../dossiers/episode-index.tsv for their episode_ids
(`7e6d5dde/8f8a0eb1` shift5, `84df59dc/983581b5` shift12,
`b0d5b386/d24bc12f` shift18, `9c93a1d6/d0050e73` shift20,
`b1b996c8/4aed44d9` shift24) — pull with `proof_export{episode_id,
format:"lean"}` and append following the pattern below.
-/

theorem erdos647_bridge1_le19 :
    ∀ n N ℓ : ℕ, 84 < n → (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 →
      n = 2520 * N → Nat.Prime ℓ → 11 ≤ ℓ → ℓ ≤ 19 → 2520 * N % ℓ ≠ 1 := by
  intro n N ℓ hn H hnN hℓ h11 h19 hmod
  have shift : ArithmeticFunction.sigma 0 (n - 1) ≤ 3 := by
    have hsub : n - 1 < n := (by omega)
    let f : Fin n → ℕ := fun x => (x : ℕ) + ArithmeticFunction.sigma 0 x
    have hbdd : BddAbove (Set.range f) := by
      refine ⟨2 * n, ?_⟩
      rintro y ⟨x, rfl⟩
      dsimp [f]
      rw [ArithmeticFunction.sigma_zero_apply]
      have hc := Nat.card_divisors_le_self (x : ℕ)
      have hx : (x : ℕ) < n := x.isLt
      omega
    let mm : Fin n := ⟨n - 1, hsub⟩
    have hm : f mm ≤ n + 2 := le_trans (le_ciSup hbdd mm) H
    dsimp [f, mm] at hm
    omega
  have hn1 : 2 ≤ n - 1 := (by omega)
  have hchar : Nat.Prime (n - 1) ∨ ∃ p : ℕ, Nat.Prime p ∧ n - 1 = p ^ 2 := by
    have hcard := shift
    rw [ArithmeticFunction.sigma_zero_apply] at hcard
    have hr0 : n - 1 ≠ 0 := (by omega)
    have hr1 : n - 1 ≠ 1 := (by omega)
    have hp : ((n - 1).minFac).Prime := Nat.minFac_prime hr1
    by_cases hpr : (n - 1).minFac = n - 1
    · exact Or.inl (hpr ▸ hp)
    · right
      refine ⟨(n - 1).minFac, hp, ?_⟩
      have hpd : (n - 1).minFac ∣ (n - 1) := Nat.minFac_dvd (n - 1)
      have hp2 : 2 ≤ (n - 1).minFac := hp.two_le
      have hplt : (n - 1).minFac < n - 1 := lt_of_le_of_ne (Nat.le_of_dvd (by omega) hpd) hpr
      have hsub2 : ({1, (n - 1).minFac, n - 1} : Finset ℕ) ⊆ (n - 1).divisors := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rw [Nat.mem_divisors]
        rcases hx with rfl | rfl | rfl
        · exact ⟨one_dvd _, hr0⟩
        · exact ⟨hpd, hr0⟩
        · exact ⟨dvd_rfl, hr0⟩
      have hcard3 : ({1, (n - 1).minFac, n - 1} : Finset ℕ).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
      have heq : (n - 1).divisors = {1, (n - 1).minFac, n - 1} :=
        (Finset.eq_of_subset_of_card_le hsub2 (by rw [hcard3]; exact hcard)).symm
      have hmul : (n - 1).minFac * ((n - 1) / (n - 1).minFac) = n - 1 := Nat.mul_div_cancel' hpd
      have hqd : (n - 1) / (n - 1).minFac ∣ (n - 1) := ⟨(n - 1).minFac, by rw [Nat.mul_comm]; exact hmul.symm⟩
      have hqmem : (n - 1) / (n - 1).minFac ∈ (n - 1).divisors := Nat.mem_divisors.mpr ⟨hqd, hr0⟩
      rw [heq] at hqmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hqmem
      rcases hqmem with h1 | h2 | h3
      · rw [h1, mul_one] at hmul
        exact absurd hmul (Nat.ne_of_lt hplt)
      · rw [h2] at hmul
        rw [pow_two]
        exact hmul.symm
      · rw [h3] at hmul
        exfalso
        nlinarith [hp2, hn1, hmul]
  have hn_mod : n % ℓ = 1 := by rw [hnN]; exact hmod
  have hdivmod := Nat.div_add_mod n ℓ
  have hdvd : ℓ ∣ (n - 1) := ⟨n / ℓ, by omega⟩
  have hN1 : 1 ≤ N := by
    by_contra h
    push_neg at h
    interval_cases N
    simp at hmod
  have hnbig : 2519 ≤ n - 1 := (by omega)
  rcases hchar with hp | ⟨p, hp, heq⟩
  · have hor := Nat.Prime.eq_one_or_self_of_dvd hp ℓ hdvd
    omega
  · rw [heq] at hdvd
    have hℓp : ℓ ∣ p := hℓ.dvd_of_dvd_pow hdvd
    have heqlp : ℓ = p := (Nat.prime_dvd_prime_iff_eq hℓ hp).mp hℓp
    have hℓ2 : ℓ ^ 2 ≤ 361 := (by nlinarith [h19])
    rw [← heqlp] at heq
    omega

theorem erdos647_bridge2_le19 :
    ∀ n N ℓ : ℕ, 84 < n → (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 →
      n = 2520 * N → Nat.Prime ℓ → 11 ≤ ℓ → ℓ ≤ 19 → 1260 * N % ℓ ≠ 1 := by
  intro n N ℓ hn H hnN hℓ h11 h19 hmod
  have shift : ArithmeticFunction.sigma 0 (n - 2) ≤ 4 := by
    have hsub : n - 2 < n := (by omega)
    let f : Fin n → ℕ := fun x => (x : ℕ) + ArithmeticFunction.sigma 0 x
    have hbdd : BddAbove (Set.range f) := by
      refine ⟨2 * n, ?_⟩
      rintro y ⟨x, rfl⟩
      dsimp [f]
      rw [ArithmeticFunction.sigma_zero_apply]
      have hc := Nat.card_divisors_le_self (x : ℕ)
      have hx : (x : ℕ) < n := x.isLt
      omega
    let mm : Fin n := ⟨n - 2, hsub⟩
    have hm : f mm ≤ n + 2 := le_trans (le_ciSup hbdd mm) H
    dsimp [f, mm] at hm
    omega
  have hN1 : 1 ≤ N := by
    by_contra h
    push_neg at h
    interval_cases N
    simp at hmod
  have hn2 : n - 2 = 2 * (1260 * N - 1) := (by omega)
  have hcop : Nat.Coprime 2 (1260 * N - 1) := (Nat.prime_two.coprime_iff_not_dvd).mpr (by omega)
  have hsig2 : ArithmeticFunction.sigma 0 2 = 2 := by native_decide
  have hmulsig : ArithmeticFunction.sigma 0 (n - 2) = 2 * ArithmeticFunction.sigma 0 (1260 * N - 1) := by
    rw [hn2, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop, hsig2]
  have hsigr : ArithmeticFunction.sigma 0 (1260 * N - 1) ≤ 2 := (by omega)
  have hr2 : 2 ≤ 1260 * N - 1 := (by omega)
  have hprime : Nat.Prime (1260 * N - 1) := by
    rw [ArithmeticFunction.sigma_zero_apply] at hsigr
    have hr0 : (1260 * N - 1) ≠ 0 := (by omega)
    have h2 : ({1, 1260 * N - 1} : Finset ℕ) ⊆ (1260 * N - 1).divisors := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [Nat.mem_divisors]
      rcases hx with rfl | rfl
      · exact ⟨one_dvd _, hr0⟩
      · exact ⟨dvd_rfl, hr0⟩
    have hc2 : ({1, 1260 * N - 1} : Finset ℕ).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
    have heq : (1260 * N - 1).divisors = {1, 1260 * N - 1} :=
      (Finset.eq_of_subset_of_card_le h2 (by rw [hc2]; exact hsigr)).symm
    rw [Nat.prime_def_lt]
    refine ⟨by omega, ?_⟩
    intro mm hmlt hmdvd
    have hmem : mm ∈ (1260 * N - 1).divisors := Nat.mem_divisors.mpr ⟨hmdvd, hr0⟩
    rw [heq] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h1 | h1
    · exact h1
    · omega
  have hn_mod : (1260 * N) % ℓ = 1 → False := by
    intro hm
    have hdivmod := Nat.div_add_mod (1260 * N) ℓ
    have hdvd : ℓ ∣ (1260 * N - 1) := ⟨1260 * N / ℓ, by omega⟩
    have hor := Nat.Prime.eq_one_or_self_of_dvd hprime ℓ hdvd
    omega
  exact hn_mod hmod

theorem erdos647_bridge3_le19 :
    ∀ n N ℓ : ℕ, 84 < n → (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 →
      n = 2520 * N → Nat.Prime ℓ → 11 ≤ ℓ → ℓ ≤ 19 → 840 * N % ℓ ≠ 1 := by
  intro n N ℓ hn H hnN hℓ h11 h19 hmod
  have shift : ArithmeticFunction.sigma 0 (n - 3) ≤ 5 := by
    have hsub : n - 3 < n := (by omega)
    let f : Fin n → ℕ := fun x => (x : ℕ) + ArithmeticFunction.sigma 0 x
    have hbdd : BddAbove (Set.range f) := by
      refine ⟨2 * n, ?_⟩
      rintro y ⟨x, rfl⟩
      dsimp [f]
      rw [ArithmeticFunction.sigma_zero_apply]
      have hc := Nat.card_divisors_le_self (x : ℕ)
      have hx : (x : ℕ) < n := x.isLt
      omega
    let mm : Fin n := ⟨n - 3, hsub⟩
    have hm : f mm ≤ n + 2 := le_trans (le_ciSup hbdd mm) H
    dsimp [f, mm] at hm
    omega
  have hN1 : 1 ≤ N := by
    by_contra h
    push_neg at h
    interval_cases N
    simp at hmod
  have hn3 : n - 3 = 3 * (840 * N - 1) := (by omega)
  have hcop : Nat.Coprime 3 (840 * N - 1) := (Nat.prime_three.coprime_iff_not_dvd).mpr (by omega)
  have hsig3 : ArithmeticFunction.sigma 0 3 = 2 := by native_decide
  have hmulsig : ArithmeticFunction.sigma 0 (n - 3) = 2 * ArithmeticFunction.sigma 0 (840 * N - 1) := by
    rw [hn3, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop, hsig3]
  have hsigr : ArithmeticFunction.sigma 0 (840 * N - 1) ≤ 2 := (by omega)
  have hr2 : 2 ≤ 840 * N - 1 := (by omega)
  have hprime : Nat.Prime (840 * N - 1) := by
    rw [ArithmeticFunction.sigma_zero_apply] at hsigr
    have hr0 : (840 * N - 1) ≠ 0 := (by omega)
    have h2 : ({1, 840 * N - 1} : Finset ℕ) ⊆ (840 * N - 1).divisors := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [Nat.mem_divisors]
      rcases hx with rfl | rfl
      · exact ⟨one_dvd _, hr0⟩
      · exact ⟨dvd_rfl, hr0⟩
    have hc2 : ({1, 840 * N - 1} : Finset ℕ).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
    have heq : (840 * N - 1).divisors = {1, 840 * N - 1} :=
      (Finset.eq_of_subset_of_card_le h2 (by rw [hc2]; exact hsigr)).symm
    rw [Nat.prime_def_lt]
    refine ⟨by omega, ?_⟩
    intro mm hmlt hmdvd
    have hmem : mm ∈ (840 * N - 1).divisors := Nat.mem_divisors.mpr ⟨hmdvd, hr0⟩
    rw [heq] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h1 | h1
    · exact h1
    · omega
  have hn_mod : (840 * N) % ℓ = 1 → False := by
    intro hm
    have hdivmod := Nat.div_add_mod (840 * N) ℓ
    have hdvd : ℓ ∣ (840 * N - 1) := ⟨840 * N / ℓ, by omega⟩
    have hor := Nat.Prime.eq_one_or_self_of_dvd hprime ℓ hdvd
    omega
  exact hn_mod hmod

theorem erdos647_bridge4_le19 :
    ∀ n N ℓ : ℕ, 84 < n → (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 →
      n = 2520 * N → Nat.Prime ℓ → 11 ≤ ℓ → ℓ ≤ 19 → 630 * N % ℓ ≠ 1 := by
  intro n N ℓ hn H hnN hℓ h11 h19 hmod
  have shift : ArithmeticFunction.sigma 0 (n - 4) ≤ 6 := by
    have hsub : n - 4 < n := (by omega)
    let f : Fin n → ℕ := fun x => (x : ℕ) + ArithmeticFunction.sigma 0 x
    have hbdd : BddAbove (Set.range f) := by
      refine ⟨2 * n, ?_⟩
      rintro y ⟨x, rfl⟩
      dsimp [f]
      rw [ArithmeticFunction.sigma_zero_apply]
      have hc := Nat.card_divisors_le_self (x : ℕ)
      have hx : (x : ℕ) < n := x.isLt
      omega
    let mm : Fin n := ⟨n - 4, hsub⟩
    have hm : f mm ≤ n + 2 := le_trans (le_ciSup hbdd mm) H
    dsimp [f, mm] at hm
    omega
  have hN1 : 1 ≤ N := by
    by_contra h
    push_neg at h
    interval_cases N
    simp at hmod
  have hn4 : n - 4 = 4 * (630 * N - 1) := (by omega)
  have hcop : Nat.Coprime 4 (630 * N - 1) :=
    Nat.Coprime.pow_left 2 ((Nat.prime_two.coprime_iff_not_dvd).mpr (by omega))
  have hsig4 : ArithmeticFunction.sigma 0 4 = 3 := by native_decide
  have hmulsig : ArithmeticFunction.sigma 0 (n - 4) = 3 * ArithmeticFunction.sigma 0 (630 * N - 1) := by
    rw [hn4, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop, hsig4]
  have hsigr : ArithmeticFunction.sigma 0 (630 * N - 1) ≤ 2 := (by omega)
  have hr2 : 2 ≤ 630 * N - 1 := (by omega)
  have hprime : Nat.Prime (630 * N - 1) := by
    rw [ArithmeticFunction.sigma_zero_apply] at hsigr
    have hr0 : (630 * N - 1) ≠ 0 := (by omega)
    have h2 : ({1, 630 * N - 1} : Finset ℕ) ⊆ (630 * N - 1).divisors := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [Nat.mem_divisors]
      rcases hx with rfl | rfl
      · exact ⟨one_dvd _, hr0⟩
      · exact ⟨dvd_rfl, hr0⟩
    have hc2 : ({1, 630 * N - 1} : Finset ℕ).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
    have heq : (630 * N - 1).divisors = {1, 630 * N - 1} :=
      (Finset.eq_of_subset_of_card_le h2 (by rw [hc2]; exact hsigr)).symm
    rw [Nat.prime_def_lt]
    refine ⟨by omega, ?_⟩
    intro mm hmlt hmdvd
    have hmem : mm ∈ (630 * N - 1).divisors := Nat.mem_divisors.mpr ⟨hmdvd, hr0⟩
    rw [heq] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h1 | h1
    · exact h1
    · omega
  have hn_mod : (630 * N) % ℓ = 1 → False := by
    intro hm
    have hdivmod := Nat.div_add_mod (630 * N) ℓ
    have hdvd : ℓ ∣ (630 * N - 1) := ⟨630 * N / ℓ, by omega⟩
    have hor := Nat.Prime.eq_one_or_self_of_dvd hprime ℓ hdvd
    omega
  exact hn_mod hmod

theorem erdos647_bridge6_le19 :
    ∀ n N ℓ : ℕ, 84 < n → (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 →
      n = 2520 * N → Nat.Prime ℓ → 11 ≤ ℓ → ℓ ≤ 19 → 420 * N % ℓ ≠ 1 := by
  intro n N ℓ hn H hnN hℓ h11 h19 hmod
  have shift : ArithmeticFunction.sigma 0 (n - 6) ≤ 8 := by
    have hsub : n - 6 < n := (by omega)
    let f : Fin n → ℕ := fun x => (x : ℕ) + ArithmeticFunction.sigma 0 x
    have hbdd : BddAbove (Set.range f) := by
      refine ⟨2 * n, ?_⟩
      rintro y ⟨x, rfl⟩
      dsimp [f]
      rw [ArithmeticFunction.sigma_zero_apply]
      have hc := Nat.card_divisors_le_self (x : ℕ)
      have hx : (x : ℕ) < n := x.isLt
      omega
    let mm : Fin n := ⟨n - 6, hsub⟩
    have hm : f mm ≤ n + 2 := le_trans (le_ciSup hbdd mm) H
    dsimp [f, mm] at hm
    omega
  have hN1 : 1 ≤ N := by
    by_contra h
    push_neg at h
    interval_cases N
    simp at hmod
  have hn6 : n - 6 = 6 * (420 * N - 1) := (by omega)
  have hcop : Nat.Coprime 6 (420 * N - 1) :=
    Nat.Coprime.mul ((Nat.prime_two.coprime_iff_not_dvd).mpr (by omega)) ((Nat.prime_three.coprime_iff_not_dvd).mpr (by omega))
  have hsig6 : ArithmeticFunction.sigma 0 6 = 4 := by native_decide
  have hmulsig : ArithmeticFunction.sigma 0 (n - 6) = 4 * ArithmeticFunction.sigma 0 (420 * N - 1) := by
    rw [hn6, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop, hsig6]
  have hsigr : ArithmeticFunction.sigma 0 (420 * N - 1) ≤ 2 := (by omega)
  have hr2 : 2 ≤ 420 * N - 1 := (by omega)
  have hprime : Nat.Prime (420 * N - 1) := by
    rw [ArithmeticFunction.sigma_zero_apply] at hsigr
    have hr0 : (420 * N - 1) ≠ 0 := (by omega)
    have h2 : ({1, 420 * N - 1} : Finset ℕ) ⊆ (420 * N - 1).divisors := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [Nat.mem_divisors]
      rcases hx with rfl | rfl
      · exact ⟨one_dvd _, hr0⟩
      · exact ⟨dvd_rfl, hr0⟩
    have hc2 : ({1, 420 * N - 1} : Finset ℕ).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
    have heq : (420 * N - 1).divisors = {1, 420 * N - 1} :=
      (Finset.eq_of_subset_of_card_le h2 (by rw [hc2]; exact hsigr)).symm
    rw [Nat.prime_def_lt]
    refine ⟨by omega, ?_⟩
    intro mm hmlt hmdvd
    have hmem : mm ∈ (420 * N - 1).divisors := Nat.mem_divisors.mpr ⟨hmdvd, hr0⟩
    rw [heq] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h1 | h1
    · exact h1
    · omega
  have hn_mod : (420 * N) % ℓ = 1 → False := by
    intro hm
    have hdivmod := Nat.div_add_mod (420 * N) ℓ
    have hdvd : ℓ ∣ (420 * N - 1) := ⟨420 * N / ℓ, by omega⟩
    have hor := Nat.Prime.eq_one_or_self_of_dvd hprime ℓ hdvd
    omega
  exact hn_mod hmod

theorem erdos647_bridge8_le19 :
    ∀ n N ℓ : ℕ, 84 < n → (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 →
      n = 2520 * N → Nat.Prime ℓ → 11 ≤ ℓ → ℓ ≤ 19 → 315 * N % ℓ ≠ 1 := by
  intro n N ℓ hn H hnN hℓ h11 h19 hmod
  have hprime2 : ∀ x : ℕ, 2 ≤ x → ArithmeticFunction.sigma 0 x ≤ 2 → Nat.Prime x := by
    intro x hx hs
    rw [ArithmeticFunction.sigma_zero_apply] at hs
    have hx0 : x ≠ 0 := (by omega)
    have hsub : ({1, x} : Finset ℕ) ⊆ x.divisors := by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rw [Nat.mem_divisors]
      rcases hy with rfl | rfl
      · exact ⟨one_dvd _, hx0⟩
      · exact ⟨dvd_rfl, hx0⟩
    have hc2 : ({1, x} : Finset ℕ).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
    have heq : x.divisors = {1, x} := (Finset.eq_of_subset_of_card_le hsub (by rw [hc2]; exact hs)).symm
    rw [Nat.prime_def_lt]
    refine ⟨by omega, ?_⟩
    intro mm hmlt hmdvd
    have hmem : mm ∈ x.divisors := Nat.mem_divisors.mpr ⟨hmdvd, hx0⟩
    rw [heq] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h1 | h1
    · exact h1
    · omega
  have shift : ArithmeticFunction.sigma 0 (n - 8) ≤ 10 := by
    have hsub : n - 8 < n := (by omega)
    let f : Fin n → ℕ := fun x => (x : ℕ) + ArithmeticFunction.sigma 0 x
    have hbdd : BddAbove (Set.range f) := by
      refine ⟨2 * n, ?_⟩
      rintro y ⟨x, rfl⟩
      dsimp [f]
      rw [ArithmeticFunction.sigma_zero_apply]
      have hc := Nat.card_divisors_le_self (x : ℕ)
      have hx : (x : ℕ) < n := x.isLt
      omega
    let mm : Fin n := ⟨n - 8, hsub⟩
    have hm : f mm ≤ n + 2 := le_trans (le_ciSup hbdd mm) H
    dsimp [f, mm] at hm
    omega
  have hN1 : 1 ≤ N := by
    by_contra h
    push_neg at h
    interval_cases N
    simp at hmod
  have hn8 : n - 8 = 8 * (315 * N - 1) := (by omega)
  obtain ⟨a, s, hs_odd, hrs⟩ := Nat.exists_eq_two_pow_mul_odd (show 315 * N - 1 ≠ 0 by omega)
  have hs1 : 1 ≤ s := by
    rcases Nat.eq_zero_or_pos s with h | h
    · rw [h, Nat.mul_zero] at hrs; omega
    · exact h
  have hodd2 : ¬ (2 ∣ s) := (by have := Nat.odd_iff.mp hs_odd; omega)
  have hcop2 : Nat.Coprime 2 s := (Nat.prime_two.coprime_iff_not_dvd).mpr hodd2
  have hcop : Nat.Coprime (2 ^ (a + 3)) s := hcop2.pow_left (a + 3)
  have hn8s : n - 8 = 2 ^ (a + 3) * s := by rw [hn8, hrs, pow_add] <;> ring
  have hsig8 : ArithmeticFunction.sigma 0 (n - 8) = (a + 4) * ArithmeticFunction.sigma 0 s := by
    rw [hn8s, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop, ArithmeticFunction.sigma_zero_apply_prime_pow Nat.prime_two] <;> ring
  have hbudget : (a + 4) * ArithmeticFunction.sigma 0 s ≤ 10 := (by rw [← hsig8]; exact shift)
  have hcases : a = 0 ∨ a = 1 ∨ 2 ≤ a := (by omega)
  have hchar8 : Nat.Prime (315 * N - 1) ∨ ∃ p : ℕ, Nat.Prime p ∧ (315 * N - 1) = 2 * p := by
    rcases hcases with rfl | rfl | ha
    · have hrs0 : (315 * N - 1) = s := by rw [hrs] <;> ring
      have hsle : ArithmeticFunction.sigma 0 (315 * N - 1) ≤ 2 := by rw [hrs0]; omega
      exact Or.inl (hprime2 (315 * N - 1) (by omega) hsle)
    · have hrs1 : (315 * N - 1) = 2 * s := by rw [hrs] <;> ring
      have hsle : ArithmeticFunction.sigma 0 s ≤ 2 := (by omega)
      exact Or.inr ⟨s, hprime2 s (by omega) hsle, hrs1⟩
    · exfalso
      have h6 : 6 * ArithmeticFunction.sigma 0 s ≤ 10 := le_trans (Nat.mul_le_mul_right (ArithmeticFunction.sigma 0 s) (by omega : (6:ℕ) ≤ a + 4)) hbudget
      have hsle1 : ArithmeticFunction.sigma 0 s ≤ 1 := (by omega)
      have hs_eq1 : s = 1 := by
        by_contra hne
        rw [ArithmeticFunction.sigma_zero_apply] at hsle1
        have hcard : 1 < s.divisors.card := Finset.one_lt_card.mpr ⟨1, Nat.one_mem_divisors.mpr (by omega), s, Nat.mem_divisors_self s (by omega), by omega⟩
        omega
      have hsig1 : ArithmeticFunction.sigma 0 s = 1 := (by rw [hs_eq1]; native_decide)
      have hale6 : a ≤ 6 := by rw [hsig1, Nat.mul_one] at hbudget; omega
      rw [hs_eq1, Nat.mul_one] at hrs
      have hpow : (2:ℕ) ^ a ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) hale6
      have h64 : (2:ℕ) ^ 6 = 64 := (by norm_num)
      omega
  have hdivmod := Nat.div_add_mod (315 * N) ℓ
  have hdvd : ℓ ∣ (315 * N - 1) := ⟨315 * N / ℓ, by omega⟩
  rcases hchar8 with hp | ⟨p, hp, heq⟩
  · have hor := Nat.Prime.eq_one_or_self_of_dvd hp ℓ hdvd
    omega
  · rw [heq] at hdvd
    have h2dvd : ¬ ℓ ∣ 2 := by
      intro hc
      have := Nat.le_of_dvd (by norm_num) hc
      omega
    have hℓp : ℓ ∣ p := (hℓ.dvd_mul.mp hdvd).resolve_left h2dvd
    have heqlp : ℓ = p := (Nat.prime_dvd_prime_iff_eq hℓ hp).mp hℓp
    rw [← heqlp] at heq
    omega

theorem erdos647_bridge9_le19 :
    ∀ n N ℓ : ℕ, 84 < n → (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 →
      n = 2520 * N → Nat.Prime ℓ → 11 ≤ ℓ → ℓ ≤ 19 → 280 * N % ℓ ≠ 1 := by
  intro n N ℓ hn H hnN hℓ h11 h19 hmod
  have hprime2 : ∀ x : ℕ, 2 ≤ x → ArithmeticFunction.sigma 0 x ≤ 2 → Nat.Prime x := by
    intro x hx hs
    rw [ArithmeticFunction.sigma_zero_apply] at hs
    have hx0 : x ≠ 0 := (by omega)
    have hsub : ({1, x} : Finset ℕ) ⊆ x.divisors := by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rw [Nat.mem_divisors]
      rcases hy with rfl | rfl
      · exact ⟨one_dvd _, hx0⟩
      · exact ⟨dvd_rfl, hx0⟩
    have hc2 : ({1, x} : Finset ℕ).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
    have heq : x.divisors = {1, x} := (Finset.eq_of_subset_of_card_le hsub (by rw [hc2]; exact hs)).symm
    rw [Nat.prime_def_lt]
    refine ⟨by omega, ?_⟩
    intro mm hmlt hmdvd
    have hmem : mm ∈ x.divisors := Nat.mem_divisors.mpr ⟨hmdvd, hx0⟩
    rw [heq] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h1 | h1
    · exact h1
    · omega
  have hchar : ∀ r : ℕ, 2 ≤ r → ArithmeticFunction.sigma 0 r ≤ 3 → Nat.Prime r ∨ ∃ p : ℕ, Nat.Prime p ∧ r = p ^ 2 := by
    intro r hr hcard
    rw [ArithmeticFunction.sigma_zero_apply] at hcard
    have hr0 : r ≠ 0 := (by omega)
    have hr1 : r ≠ 1 := (by omega)
    have hp : (r.minFac).Prime := Nat.minFac_prime hr1
    by_cases hpr : r.minFac = r
    · exact Or.inl (hpr ▸ hp)
    · right
      refine ⟨r.minFac, hp, ?_⟩
      have hpd : r.minFac ∣ r := Nat.minFac_dvd r
      have hp2 : 2 ≤ r.minFac := hp.two_le
      have hplt : r.minFac < r := lt_of_le_of_ne (Nat.le_of_dvd (by omega) hpd) hpr
      have hsub2 : ({1, r.minFac, r} : Finset ℕ) ⊆ r.divisors := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rw [Nat.mem_divisors]
        rcases hx with rfl | rfl | rfl
        · exact ⟨one_dvd r, hr0⟩
        · exact ⟨hpd, hr0⟩
        · exact ⟨dvd_rfl, hr0⟩
      have hcard3 : ({1, r.minFac, r} : Finset ℕ).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
      have heq : r.divisors = {1, r.minFac, r} :=
        (Finset.eq_of_subset_of_card_le hsub2 (by rw [hcard3]; exact hcard)).symm
      have hmul : r.minFac * (r / r.minFac) = r := Nat.mul_div_cancel' hpd
      have hqd : r / r.minFac ∣ r := ⟨r.minFac, by rw [Nat.mul_comm]; exact hmul.symm⟩
      have hqmem : r / r.minFac ∈ r.divisors := Nat.mem_divisors.mpr ⟨hqd, hr0⟩
      rw [heq] at hqmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hqmem
      rcases hqmem with h1 | h2 | h3
      · rw [h1, mul_one] at hmul
        exact absurd hmul (Nat.ne_of_lt hplt)
      · rw [h2] at hmul
        rw [pow_two]
        exact hmul.symm
      · rw [h3] at hmul
        exfalso
        nlinarith [hp2, hr, hmul]
  have shift : ArithmeticFunction.sigma 0 (n - 9) ≤ 11 := by
    have hsub : n - 9 < n := (by omega)
    let f : Fin n → ℕ := fun x => (x : ℕ) + ArithmeticFunction.sigma 0 x
    have hbdd : BddAbove (Set.range f) := by
      refine ⟨2 * n, ?_⟩
      rintro y ⟨x, rfl⟩
      dsimp [f]
      rw [ArithmeticFunction.sigma_zero_apply]
      have hc := Nat.card_divisors_le_self (x : ℕ)
      have hx : (x : ℕ) < n := x.isLt
      omega
    let mm : Fin n := ⟨n - 9, hsub⟩
    have hm : f mm ≤ n + 2 := le_trans (le_ciSup hbdd mm) H
    dsimp [f, mm] at hm
    omega
  have hN1 : 1 ≤ N := by
    by_contra h
    push_neg at h
    interval_cases N
    simp at hmod
  have hn9 : n - 9 = 9 * (280 * N - 1) := (by omega)
  obtain ⟨b, s, hnd, hrs⟩ := Nat.exists_eq_pow_mul_and_not_dvd (show 280 * N - 1 ≠ 0 by omega) 3 (by norm_num)
  have hs0 : s ≠ 0 := (by rintro rfl; exact hnd (dvd_zero 3))
  have hcop2 : Nat.Coprime 3 s := (Nat.prime_three.coprime_iff_not_dvd).mpr hnd
  have hcop : Nat.Coprime (3 ^ (b + 2)) s := hcop2.pow_left (b + 2)
  have hn9s : n - 9 = 3 ^ (b + 2) * s := by rw [hn9, hrs, pow_add] <;> ring
  have hsig9 : ArithmeticFunction.sigma 0 (n - 9) = (b + 3) * ArithmeticFunction.sigma 0 s := by
    rw [hn9s, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop, ArithmeticFunction.sigma_zero_apply_prime_pow Nat.prime_three] <;> ring
  have hbudget : (b + 3) * ArithmeticFunction.sigma 0 s ≤ 11 := (by rw [← hsig9]; exact shift)
  have hcases : b = 0 ∨ b = 1 ∨ b = 2 ∨ 3 ≤ b := (by omega)
  have hchar9 : Nat.Prime (280 * N - 1) ∨ (∃ p : ℕ, Nat.Prime p ∧ (280 * N - 1) = p ^ 2) ∨ (∃ p : ℕ, Nat.Prime p ∧ (280 * N - 1) = 3 * p) ∨ (∃ p : ℕ, Nat.Prime p ∧ (280 * N - 1) = 9 * p) := by
    rcases hcases with rfl | rfl | rfl | hb
    · have hrs0 : (280 * N - 1) = s := by rw [hrs] <;> ring
      have hsle : ArithmeticFunction.sigma 0 (280 * N - 1) ≤ 3 := by rw [hrs0]; omega
      have hs2 : 2 ≤ 280 * N - 1 := (by omega)
      rcases hchar (280 * N - 1) hs2 hsle with hp | ⟨p, hp, heqp⟩
      · exact Or.inl hp
      · exact Or.inr (Or.inl ⟨p, hp, heqp⟩)
    · have hrs1 : (280 * N - 1) = 3 * s := by rw [hrs] <;> ring
      have hsle : ArithmeticFunction.sigma 0 s ≤ 2 := (by omega)
      exact Or.inr (Or.inr (Or.inl ⟨s, hprime2 s (by omega) hsle, hrs1⟩))
    · have hrs2 : (280 * N - 1) = 9 * s := by rw [hrs] <;> ring
      have hsle : ArithmeticFunction.sigma 0 s ≤ 2 := (by omega)
      exact Or.inr (Or.inr (Or.inr ⟨s, hprime2 s (by omega) hsle, hrs2⟩))
    · exfalso
      have h6 : 6 * ArithmeticFunction.sigma 0 s ≤ 11 := le_trans (Nat.mul_le_mul_right (ArithmeticFunction.sigma 0 s) (by omega : (6:ℕ) ≤ b + 3)) hbudget
      have hsle1 : ArithmeticFunction.sigma 0 s ≤ 1 := (by omega)
      have hs_eq1 : s = 1 := by
        by_contra hne
        rw [ArithmeticFunction.sigma_zero_apply] at hsle1
        have hcard : 1 < s.divisors.card := Finset.one_lt_card.mpr ⟨1, Nat.one_mem_divisors.mpr hs0, s, Nat.mem_divisors_self s hs0, by omega⟩
        omega
      have hsig1 : ArithmeticFunction.sigma 0 s = 1 := (by rw [hs_eq1]; native_decide)
      have hble8 : b ≤ 8 := by rw [hsig1, Nat.mul_one] at hbudget; omega
      rw [hs_eq1, Nat.mul_one] at hrs
      interval_cases b <;> norm_num at hrs <;> omega
  have hdivmod := Nat.div_add_mod (280 * N) ℓ
  have hdvd : ℓ ∣ (280 * N - 1) := ⟨280 * N / ℓ, by omega⟩
  have h3dvd : ¬ ℓ ∣ 3 := by
    intro hc
    have := Nat.le_of_dvd (by norm_num) hc
    omega
  rcases hchar9 with hp | hp2 | hp3 | hp9
  · have hor := Nat.Prime.eq_one_or_self_of_dvd hp ℓ hdvd
    omega
  · obtain ⟨p, hp, heq⟩ := hp2
    rw [heq] at hdvd
    have hℓp : ℓ ∣ p := hℓ.dvd_of_dvd_pow hdvd
    have heqlp : ℓ = p := (Nat.prime_dvd_prime_iff_eq hℓ hp).mp hℓp
    rw [← heqlp] at heq
    interval_cases ℓ <;> omega
  · obtain ⟨p, hp, heq⟩ := hp3
    rw [heq] at hdvd
    have hℓp : ℓ ∣ p := (hℓ.dvd_mul.mp hdvd).resolve_left h3dvd
    have heqlp : ℓ = p := (Nat.prime_dvd_prime_iff_eq hℓ hp).mp hℓp
    rw [← heqlp] at heq
    omega
  · obtain ⟨p, hp, heq⟩ := hp9
    rw [heq] at hdvd
    have h9dvd : ℓ ∣ 9 * p := hdvd
    have hℓp : ℓ ∣ p := (hℓ.dvd_mul.mp h9dvd).resolve_left (by
      intro hc9
      have h9 : ℓ ∣ 3 * 3 := by norm_num at hc9 ⊢; exact hc9
      have := (hℓ.dvd_mul.mp h9).resolve_left h3dvd
      exact h3dvd this)
    have heqlp : ℓ = p := (Nat.prime_dvd_prime_iff_eq hℓ hp).mp hℓp
    rw [← heqlp] at heq
    omega

theorem erdos647_bridge10_le19 :
    ∀ n N ℓ : ℕ, 84 < n → (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 →
      n = 2520 * N → Nat.Prime ℓ → 11 ≤ ℓ → ℓ ≤ 19 → 252 * N % ℓ ≠ 1 := by
  intro n N ℓ hn H hnN hℓ h11 h19 hmod
  have hprime2 : ∀ x : ℕ, 2 ≤ x → ArithmeticFunction.sigma 0 x ≤ 2 → Nat.Prime x := by
    intro x hx hs
    rw [ArithmeticFunction.sigma_zero_apply] at hs
    have hx0 : x ≠ 0 := (by omega)
    have hsub : ({1, x} : Finset ℕ) ⊆ x.divisors := by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rw [Nat.mem_divisors]
      rcases hy with rfl | rfl
      · exact ⟨one_dvd _, hx0⟩
      · exact ⟨dvd_rfl, hx0⟩
    have hc2 : ({1, x} : Finset ℕ).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
    have heq : x.divisors = {1, x} := (Finset.eq_of_subset_of_card_le hsub (by rw [hc2]; exact hs)).symm
    rw [Nat.prime_def_lt]
    refine ⟨by omega, ?_⟩
    intro mm hmlt hmdvd
    have hmem : mm ∈ x.divisors := Nat.mem_divisors.mpr ⟨hmdvd, hx0⟩
    rw [heq] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h1 | h1
    · exact h1
    · omega
  have hchar : ∀ r : ℕ, 2 ≤ r → ArithmeticFunction.sigma 0 r ≤ 3 → Nat.Prime r ∨ ∃ p : ℕ, Nat.Prime p ∧ r = p ^ 2 := by
    intro r hr hcard
    rw [ArithmeticFunction.sigma_zero_apply] at hcard
    have hr0 : r ≠ 0 := (by omega)
    have hr1 : r ≠ 1 := (by omega)
    have hp : (r.minFac).Prime := Nat.minFac_prime hr1
    by_cases hpr : r.minFac = r
    · exact Or.inl (hpr ▸ hp)
    · right
      refine ⟨r.minFac, hp, ?_⟩
      have hpd : r.minFac ∣ r := Nat.minFac_dvd r
      have hp2 : 2 ≤ r.minFac := hp.two_le
      have hplt : r.minFac < r := lt_of_le_of_ne (Nat.le_of_dvd (by omega) hpd) hpr
      have hsub2 : ({1, r.minFac, r} : Finset ℕ) ⊆ r.divisors := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rw [Nat.mem_divisors]
        rcases hx with rfl | rfl | rfl
        · exact ⟨one_dvd r, hr0⟩
        · exact ⟨hpd, hr0⟩
        · exact ⟨dvd_rfl, hr0⟩
      have hcard3 : ({1, r.minFac, r} : Finset ℕ).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
      have heq : r.divisors = {1, r.minFac, r} :=
        (Finset.eq_of_subset_of_card_le hsub2 (by rw [hcard3]; exact hcard)).symm
      have hmul : r.minFac * (r / r.minFac) = r := Nat.mul_div_cancel' hpd
      have hqd : r / r.minFac ∣ r := ⟨r.minFac, by rw [Nat.mul_comm]; exact hmul.symm⟩
      have hqmem : r / r.minFac ∈ r.divisors := Nat.mem_divisors.mpr ⟨hqd, hr0⟩
      rw [heq] at hqmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hqmem
      rcases hqmem with h1 | h2 | h3
      · rw [h1, mul_one] at hmul
        exact absurd hmul (Nat.ne_of_lt hplt)
      · rw [h2] at hmul
        rw [pow_two]
        exact hmul.symm
      · rw [h3] at hmul
        exfalso
        nlinarith [hp2, hr, hmul]
  have shift : ArithmeticFunction.sigma 0 (n - 10) ≤ 12 := by
    have hsub : n - 10 < n := (by omega)
    let f : Fin n → ℕ := fun x => (x : ℕ) + ArithmeticFunction.sigma 0 x
    have hbdd : BddAbove (Set.range f) := by
      refine ⟨2 * n, ?_⟩
      rintro y ⟨x, rfl⟩
      dsimp [f]
      rw [ArithmeticFunction.sigma_zero_apply]
      have hc := Nat.card_divisors_le_self (x : ℕ)
      have hx : (x : ℕ) < n := x.isLt
      omega
    let mm : Fin n := ⟨n - 10, hsub⟩
    have hm : f mm ≤ n + 2 := le_trans (le_ciSup hbdd mm) H
    dsimp [f, mm] at hm
    omega
  have hN1 : 1 ≤ N := by
    by_contra h
    push_neg at h
    interval_cases N
    simp at hmod
  have hn10 : n - 10 = 10 * (252 * N - 1) := (by omega)
  have hrodd : ¬ (2 ∣ 252 * N - 1) := (by omega)
  obtain ⟨c, s, hnd, hrs⟩ := Nat.exists_eq_pow_mul_and_not_dvd (show 252 * N - 1 ≠ 0 by omega) 5 (by norm_num)
  have hs0 : s ≠ 0 := (by rintro rfl; exact hnd (dvd_zero 5))
  have hsodd : ¬ (2 ∣ s) := by
    intro hcon
    apply hrodd
    rw [hrs]
    exact Dvd.dvd.mul_left hcon (5 ^ c)
  have hcop25 : Nat.Coprime (2 * 5 ^ (c + 1)) s := by
    have h2s : Nat.Coprime 2 s := (Nat.prime_two.coprime_iff_not_dvd).mpr hsodd
    have h5s : Nat.Coprime 5 s := (by norm_num : Nat.Prime 5).coprime_iff_not_dvd.mpr hnd
    exact h2s.mul (h5s.pow_left (c + 1))
  have hn10s : n - 10 = (2 * 5 ^ (c + 1)) * s := by rw [hn10, hrs] <;> ring
  have hsig10 : ArithmeticFunction.sigma 0 (n - 10) = (2 * (c + 2)) * ArithmeticFunction.sigma 0 s := by
    rw [hn10s, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop25]
    have h2v : ArithmeticFunction.sigma 0 (2 * 5 ^ (c + 1)) = 2 * (c + 2) := by
      have hcop2_5 : Nat.Coprime 2 (5 ^ (c + 1)) := (Nat.prime_two.coprime_iff_not_dvd).mpr (by
        intro hcon; have := (Nat.prime_two.dvd_of_dvd_pow hcon); omega)
      rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop2_5]
      have hs2 : ArithmeticFunction.sigma 0 2 = 2 := by native_decide
      rw [hs2, ArithmeticFunction.sigma_zero_apply_prime_pow (by norm_num : Nat.Prime 5)] <;> ring
    rw [h2v]
  have hbudget : (2 * (c + 2)) * ArithmeticFunction.sigma 0 s ≤ 12 := (by rw [← hsig10]; exact shift)
  have hcases : c = 0 ∨ c = 1 ∨ 2 ≤ c := (by omega)
  have hchar10 : Nat.Prime (252 * N - 1) ∨ (∃ p : ℕ, Nat.Prime p ∧ (252 * N - 1) = p ^ 2) ∨ (∃ p : ℕ, Nat.Prime p ∧ (252 * N - 1) = 5 * p) := by
    rcases hcases with rfl | rfl | hc
    · have hrs0 : (252 * N - 1) = s := by rw [hrs] <;> ring
      have hsle : ArithmeticFunction.sigma 0 (252 * N - 1) ≤ 3 := by rw [hrs0]; omega
      have hs2 : 2 ≤ 252 * N - 1 := (by omega)
      rcases hchar (252 * N - 1) hs2 hsle with hp | ⟨p, hp, heqp⟩
      · exact Or.inl hp
      · exact Or.inr (Or.inl ⟨p, hp, heqp⟩)
    · have hrs1 : (252 * N - 1) = 5 * s := by rw [hrs] <;> ring
      have hsle : ArithmeticFunction.sigma 0 s ≤ 2 := (by omega)
      exact Or.inr (Or.inr ⟨s, hprime2 s (by omega) hsle, hrs1⟩)
    · exfalso
      have h8 : 8 * ArithmeticFunction.sigma 0 s ≤ 12 := le_trans (Nat.mul_le_mul_right (ArithmeticFunction.sigma 0 s) (by omega : (8:ℕ) ≤ 2 * (c + 2))) hbudget
      have hsle1 : ArithmeticFunction.sigma 0 s ≤ 1 := (by omega)
      have hs_eq1 : s = 1 := by
        by_contra hne
        rw [ArithmeticFunction.sigma_zero_apply] at hsle1
        have hcard : 1 < s.divisors.card := Finset.one_lt_card.mpr ⟨1, Nat.one_mem_divisors.mpr hs0, s, Nat.mem_divisors_self s hs0, by omega⟩
        omega
      have hsig1 : ArithmeticFunction.sigma 0 s = 1 := (by rw [hs_eq1]; native_decide)
      have hcle4 : c ≤ 4 := by rw [hsig1, Nat.mul_one] at hbudget; omega
      rw [hs_eq1, Nat.mul_one] at hrs
      interval_cases c <;> norm_num at hrs <;> omega
  have hdivmod := Nat.div_add_mod (252 * N) ℓ
  have hdvd : ℓ ∣ (252 * N - 1) := ⟨252 * N / ℓ, by omega⟩
  have h5dvd : ¬ ℓ ∣ 5 := by
    intro hc
    have := Nat.le_of_dvd (by norm_num) hc
    omega
  rcases hchar10 with hp | hp2 | hp5
  · have hor := Nat.Prime.eq_one_or_self_of_dvd hp ℓ hdvd
    omega
  · obtain ⟨p, hp, heq⟩ := hp2
    rw [heq] at hdvd
    have hℓp : ℓ ∣ p := hℓ.dvd_of_dvd_pow hdvd
    have heqlp : ℓ = p := (Nat.prime_dvd_prime_iff_eq hℓ hp).mp hℓp
    rw [← heqlp] at heq
    interval_cases ℓ <;> omega
  · obtain ⟨p, hp, heq⟩ := hp5
    rw [heq] at hdvd
    have hℓp : ℓ ∣ p := (hℓ.dvd_mul.mp hdvd).resolve_left h5dvd
    have heqlp : ℓ = p := (Nat.prime_dvd_prime_iff_eq hℓ hp).mp hℓp
    rw [← heqlp] at heq
    omega

theorem erdos647_bridge1_le29 :
    ∀ n N ℓ : ℕ, 84 < n → (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 →
      n = 2520 * N → Nat.Prime ℓ → 11 ≤ ℓ → ℓ ≤ 29 → 2520 * N % ℓ ≠ 1 := by
  intro n N ℓ hn H hnN hℓ h11 h29 hmod
  have shift : ArithmeticFunction.sigma 0 (n - 1) ≤ 3 := by
    have hsub : n - 1 < n := (by omega)
    let f : Fin n → ℕ := fun x => (x : ℕ) + ArithmeticFunction.sigma 0 x
    have hbdd : BddAbove (Set.range f) := by
      refine ⟨2 * n, ?_⟩
      rintro y ⟨x, rfl⟩
      dsimp [f]
      rw [ArithmeticFunction.sigma_zero_apply]
      have hc := Nat.card_divisors_le_self (x : ℕ)
      have hx : (x : ℕ) < n := x.isLt
      omega
    let mm : Fin n := ⟨n - 1, hsub⟩
    have hm : f mm ≤ n + 2 := le_trans (le_ciSup hbdd mm) H
    dsimp [f, mm] at hm
    omega
  have hn1 : 2 ≤ n - 1 := (by omega)
  have hchar : Nat.Prime (n - 1) ∨ ∃ p : ℕ, Nat.Prime p ∧ n - 1 = p ^ 2 := by
    have hcard := shift
    rw [ArithmeticFunction.sigma_zero_apply] at hcard
    have hr0 : n - 1 ≠ 0 := (by omega)
    have hr1 : n - 1 ≠ 1 := (by omega)
    have hp : ((n - 1).minFac).Prime := Nat.minFac_prime hr1
    by_cases hpr : (n - 1).minFac = n - 1
    · exact Or.inl (hpr ▸ hp)
    · right
      refine ⟨(n - 1).minFac, hp, ?_⟩
      have hpd : (n - 1).minFac ∣ (n - 1) := Nat.minFac_dvd (n - 1)
      have hp2 : 2 ≤ (n - 1).minFac := hp.two_le
      have hplt : (n - 1).minFac < n - 1 := lt_of_le_of_ne (Nat.le_of_dvd (by omega) hpd) hpr
      have hsub2 : ({1, (n - 1).minFac, n - 1} : Finset ℕ) ⊆ (n - 1).divisors := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rw [Nat.mem_divisors]
        rcases hx with rfl | rfl | rfl
        · exact ⟨one_dvd _, hr0⟩
        · exact ⟨hpd, hr0⟩
        · exact ⟨dvd_rfl, hr0⟩
      have hcard3 : ({1, (n - 1).minFac, n - 1} : Finset ℕ).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
      have heq : (n - 1).divisors = {1, (n - 1).minFac, n - 1} :=
        (Finset.eq_of_subset_of_card_le hsub2 (by rw [hcard3]; exact hcard)).symm
      have hmul : (n - 1).minFac * ((n - 1) / (n - 1).minFac) = n - 1 := Nat.mul_div_cancel' hpd
      have hqd : (n - 1) / (n - 1).minFac ∣ (n - 1) := ⟨(n - 1).minFac, by rw [Nat.mul_comm]; exact hmul.symm⟩
      have hqmem : (n - 1) / (n - 1).minFac ∈ (n - 1).divisors := Nat.mem_divisors.mpr ⟨hqd, hr0⟩
      rw [heq] at hqmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hqmem
      rcases hqmem with h1 | h2 | h3
      · rw [h1, mul_one] at hmul
        exact absurd hmul (Nat.ne_of_lt hplt)
      · rw [h2] at hmul
        rw [pow_two]
        exact hmul.symm
      · rw [h3] at hmul
        exfalso
        nlinarith [hp2, hn1, hmul]
  have hn_mod : n % ℓ = 1 := by rw [hnN]; exact hmod
  have hdivmod := Nat.div_add_mod n ℓ
  have hdvd : ℓ ∣ (n - 1) := ⟨n / ℓ, by omega⟩
  have hN1 : 1 ≤ N := by
    by_contra h
    push_neg at h
    interval_cases N
    simp at hmod
  have hnbig : 2519 ≤ n - 1 := (by omega)
  rcases hchar with hp | ⟨p, hp, heq⟩
  · have hor := Nat.Prime.eq_one_or_self_of_dvd hp ℓ hdvd
    omega
  · rw [heq] at hdvd
    have hℓp : ℓ ∣ p := hℓ.dvd_of_dvd_pow hdvd
    have heqlp : ℓ = p := (Nat.prime_dvd_prime_iff_eq hℓ hp).mp hℓp
    have hℓ2 : ℓ ^ 2 ≤ 841 := (by nlinarith [h29])
    rw [← heqlp] at heq
    omega

theorem erdos647_bridge2_le29 :
    ∀ n N ℓ : ℕ, 84 < n → (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 →
      n = 2520 * N → Nat.Prime ℓ → 11 ≤ ℓ → ℓ ≤ 29 → 1260 * N % ℓ ≠ 1 := by
  intro n N ℓ hn H hnN hℓ h11 h29 hmod
  have shift : ArithmeticFunction.sigma 0 (n - 2) ≤ 4 := by
    have hsub : n - 2 < n := (by omega)
    let f : Fin n → ℕ := fun x => (x : ℕ) + ArithmeticFunction.sigma 0 x
    have hbdd : BddAbove (Set.range f) := by
      refine ⟨2 * n, ?_⟩
      rintro y ⟨x, rfl⟩
      dsimp [f]
      rw [ArithmeticFunction.sigma_zero_apply]
      have hc := Nat.card_divisors_le_self (x : ℕ)
      have hx : (x : ℕ) < n := x.isLt
      omega
    let mm : Fin n := ⟨n - 2, hsub⟩
    have hm : f mm ≤ n + 2 := le_trans (le_ciSup hbdd mm) H
    dsimp [f, mm] at hm
    omega
  have hN1 : 1 ≤ N := by
    by_contra h
    push_neg at h
    interval_cases N
    simp at hmod
  have hn2 : n - 2 = 2 * (1260 * N - 1) := (by omega)
  have hcop : Nat.Coprime 2 (1260 * N - 1) := (Nat.prime_two.coprime_iff_not_dvd).mpr (by omega)
  have hsig2 : ArithmeticFunction.sigma 0 2 = 2 := by native_decide
  have hmulsig : ArithmeticFunction.sigma 0 (n - 2) = 2 * ArithmeticFunction.sigma 0 (1260 * N - 1) := by
    rw [hn2, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop, hsig2]
  have hsigr : ArithmeticFunction.sigma 0 (1260 * N - 1) ≤ 2 := (by omega)
  have hr2 : 2 ≤ 1260 * N - 1 := (by omega)
  have hprime : Nat.Prime (1260 * N - 1) := by
    rw [ArithmeticFunction.sigma_zero_apply] at hsigr
    have hr0 : (1260 * N - 1) ≠ 0 := (by omega)
    have h2 : ({1, 1260 * N - 1} : Finset ℕ) ⊆ (1260 * N - 1).divisors := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [Nat.mem_divisors]
      rcases hx with rfl | rfl
      · exact ⟨one_dvd _, hr0⟩
      · exact ⟨dvd_rfl, hr0⟩
    have hc2 : ({1, 1260 * N - 1} : Finset ℕ).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
    have heq : (1260 * N - 1).divisors = {1, 1260 * N - 1} :=
      (Finset.eq_of_subset_of_card_le h2 (by rw [hc2]; exact hsigr)).symm
    rw [Nat.prime_def_lt]
    refine ⟨by omega, ?_⟩
    intro mm hmlt hmdvd
    have hmem : mm ∈ (1260 * N - 1).divisors := Nat.mem_divisors.mpr ⟨hmdvd, hr0⟩
    rw [heq] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h1 | h1
    · exact h1
    · omega
  have hn_mod : (1260 * N) % ℓ = 1 → False := by
    intro hm
    have hdivmod := Nat.div_add_mod (1260 * N) ℓ
    have hdvd : ℓ ∣ (1260 * N - 1) := ⟨1260 * N / ℓ, by omega⟩
    have hor := Nat.Prime.eq_one_or_self_of_dvd hprime ℓ hdvd
    omega
  exact hn_mod hmod

theorem erdos647_bridge3_le29 :
    ∀ n N ℓ : ℕ, 84 < n → (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 →
      n = 2520 * N → Nat.Prime ℓ → 11 ≤ ℓ → ℓ ≤ 29 → 840 * N % ℓ ≠ 1 := by
  intro n N ℓ hn H hnN hℓ h11 h29 hmod
  have shift : ArithmeticFunction.sigma 0 (n - 3) ≤ 5 := by
    have hsub : n - 3 < n := (by omega)
    let f : Fin n → ℕ := fun x => (x : ℕ) + ArithmeticFunction.sigma 0 x
    have hbdd : BddAbove (Set.range f) := by
      refine ⟨2 * n, ?_⟩
      rintro y ⟨x, rfl⟩
      dsimp [f]
      rw [ArithmeticFunction.sigma_zero_apply]
      have hc := Nat.card_divisors_le_self (x : ℕ)
      have hx : (x : ℕ) < n := x.isLt
      omega
    let mm : Fin n := ⟨n - 3, hsub⟩
    have hm : f mm ≤ n + 2 := le_trans (le_ciSup hbdd mm) H
    dsimp [f, mm] at hm
    omega
  have hN1 : 1 ≤ N := by
    by_contra h
    push_neg at h
    interval_cases N
    simp at hmod
  have hn3 : n - 3 = 3 * (840 * N - 1) := (by omega)
  have hcop : Nat.Coprime 3 (840 * N - 1) := (Nat.prime_three.coprime_iff_not_dvd).mpr (by omega)
  have hsig3 : ArithmeticFunction.sigma 0 3 = 2 := by native_decide
  have hmulsig : ArithmeticFunction.sigma 0 (n - 3) = 2 * ArithmeticFunction.sigma 0 (840 * N - 1) := by
    rw [hn3, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop, hsig3]
  have hsigr : ArithmeticFunction.sigma 0 (840 * N - 1) ≤ 2 := (by omega)
  have hr2 : 2 ≤ 840 * N - 1 := (by omega)
  have hprime : Nat.Prime (840 * N - 1) := by
    rw [ArithmeticFunction.sigma_zero_apply] at hsigr
    have hr0 : (840 * N - 1) ≠ 0 := (by omega)
    have h2 : ({1, 840 * N - 1} : Finset ℕ) ⊆ (840 * N - 1).divisors := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [Nat.mem_divisors]
      rcases hx with rfl | rfl
      · exact ⟨one_dvd _, hr0⟩
      · exact ⟨dvd_rfl, hr0⟩
    have hc2 : ({1, 840 * N - 1} : Finset ℕ).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
    have heq : (840 * N - 1).divisors = {1, 840 * N - 1} :=
      (Finset.eq_of_subset_of_card_le h2 (by rw [hc2]; exact hsigr)).symm
    rw [Nat.prime_def_lt]
    refine ⟨by omega, ?_⟩
    intro mm hmlt hmdvd
    have hmem : mm ∈ (840 * N - 1).divisors := Nat.mem_divisors.mpr ⟨hmdvd, hr0⟩
    rw [heq] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h1 | h1
    · exact h1
    · omega
  have hn_mod : (840 * N) % ℓ = 1 → False := by
    intro hm
    have hdivmod := Nat.div_add_mod (840 * N) ℓ
    have hdvd : ℓ ∣ (840 * N - 1) := ⟨840 * N / ℓ, by omega⟩
    have hor := Nat.Prime.eq_one_or_self_of_dvd hprime ℓ hdvd
    omega
  exact hn_mod hmod

theorem erdos647_bridge4_le29 :
    ∀ n N ℓ : ℕ, 84 < n → (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 →
      n = 2520 * N → Nat.Prime ℓ → 11 ≤ ℓ → ℓ ≤ 29 → 630 * N % ℓ ≠ 1 := by
  intro n N ℓ hn H hnN hℓ h11 h29 hmod
  have shift : ArithmeticFunction.sigma 0 (n - 4) ≤ 6 := by
    have hsub : n - 4 < n := (by omega)
    let f : Fin n → ℕ := fun x => (x : ℕ) + ArithmeticFunction.sigma 0 x
    have hbdd : BddAbove (Set.range f) := by
      refine ⟨2 * n, ?_⟩
      rintro y ⟨x, rfl⟩
      dsimp [f]
      rw [ArithmeticFunction.sigma_zero_apply]
      have hc := Nat.card_divisors_le_self (x : ℕ)
      have hx : (x : ℕ) < n := x.isLt
      omega
    let mm : Fin n := ⟨n - 4, hsub⟩
    have hm : f mm ≤ n + 2 := le_trans (le_ciSup hbdd mm) H
    dsimp [f, mm] at hm
    omega
  have hN1 : 1 ≤ N := by
    by_contra h
    push_neg at h
    interval_cases N
    simp at hmod
  have hn4 : n - 4 = 4 * (630 * N - 1) := (by omega)
  have hcop : Nat.Coprime 4 (630 * N - 1) :=
    Nat.Coprime.pow_left 2 ((Nat.prime_two.coprime_iff_not_dvd).mpr (by omega))
  have hsig4 : ArithmeticFunction.sigma 0 4 = 3 := by native_decide
  have hmulsig : ArithmeticFunction.sigma 0 (n - 4) = 3 * ArithmeticFunction.sigma 0 (630 * N - 1) := by
    rw [hn4, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop, hsig4]
  have hsigr : ArithmeticFunction.sigma 0 (630 * N - 1) ≤ 2 := (by omega)
  have hr2 : 2 ≤ 630 * N - 1 := (by omega)
  have hprime : Nat.Prime (630 * N - 1) := by
    rw [ArithmeticFunction.sigma_zero_apply] at hsigr
    have hr0 : (630 * N - 1) ≠ 0 := (by omega)
    have h2 : ({1, 630 * N - 1} : Finset ℕ) ⊆ (630 * N - 1).divisors := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [Nat.mem_divisors]
      rcases hx with rfl | rfl
      · exact ⟨one_dvd _, hr0⟩
      · exact ⟨dvd_rfl, hr0⟩
    have hc2 : ({1, 630 * N - 1} : Finset ℕ).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
    have heq : (630 * N - 1).divisors = {1, 630 * N - 1} :=
      (Finset.eq_of_subset_of_card_le h2 (by rw [hc2]; exact hsigr)).symm
    rw [Nat.prime_def_lt]
    refine ⟨by omega, ?_⟩
    intro mm hmlt hmdvd
    have hmem : mm ∈ (630 * N - 1).divisors := Nat.mem_divisors.mpr ⟨hmdvd, hr0⟩
    rw [heq] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h1 | h1
    · exact h1
    · omega
  have hn_mod : (630 * N) % ℓ = 1 → False := by
    intro hm
    have hdivmod := Nat.div_add_mod (630 * N) ℓ
    have hdvd : ℓ ∣ (630 * N - 1) := ⟨630 * N / ℓ, by omega⟩
    have hor := Nat.Prime.eq_one_or_self_of_dvd hprime ℓ hdvd
    omega
  exact hn_mod hmod

theorem erdos647_bridge6_le29 :
    ∀ n N ℓ : ℕ, 84 < n → (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 →
      n = 2520 * N → Nat.Prime ℓ → 11 ≤ ℓ → ℓ ≤ 29 → 420 * N % ℓ ≠ 1 := by
  intro n N ℓ hn H hnN hℓ h11 h29 hmod
  have shift : ArithmeticFunction.sigma 0 (n - 6) ≤ 8 := by
    have hsub : n - 6 < n := (by omega)
    let f : Fin n → ℕ := fun x => (x : ℕ) + ArithmeticFunction.sigma 0 x
    have hbdd : BddAbove (Set.range f) := by
      refine ⟨2 * n, ?_⟩
      rintro y ⟨x, rfl⟩
      dsimp [f]
      rw [ArithmeticFunction.sigma_zero_apply]
      have hc := Nat.card_divisors_le_self (x : ℕ)
      have hx : (x : ℕ) < n := x.isLt
      omega
    let mm : Fin n := ⟨n - 6, hsub⟩
    have hm : f mm ≤ n + 2 := le_trans (le_ciSup hbdd mm) H
    dsimp [f, mm] at hm
    omega
  have hN1 : 1 ≤ N := by
    by_contra h
    push_neg at h
    interval_cases N
    simp at hmod
  have hn6 : n - 6 = 6 * (420 * N - 1) := (by omega)
  have hcop : Nat.Coprime 6 (420 * N - 1) :=
    Nat.Coprime.mul ((Nat.prime_two.coprime_iff_not_dvd).mpr (by omega)) ((Nat.prime_three.coprime_iff_not_dvd).mpr (by omega))
  have hsig6 : ArithmeticFunction.sigma 0 6 = 4 := by native_decide
  have hmulsig : ArithmeticFunction.sigma 0 (n - 6) = 4 * ArithmeticFunction.sigma 0 (420 * N - 1) := by
    rw [hn6, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop, hsig6]
  have hsigr : ArithmeticFunction.sigma 0 (420 * N - 1) ≤ 2 := (by omega)
  have hr2 : 2 ≤ 420 * N - 1 := (by omega)
  have hprime : Nat.Prime (420 * N - 1) := by
    rw [ArithmeticFunction.sigma_zero_apply] at hsigr
    have hr0 : (420 * N - 1) ≠ 0 := (by omega)
    have h2 : ({1, 420 * N - 1} : Finset ℕ) ⊆ (420 * N - 1).divisors := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [Nat.mem_divisors]
      rcases hx with rfl | rfl
      · exact ⟨one_dvd _, hr0⟩
      · exact ⟨dvd_rfl, hr0⟩
    have hc2 : ({1, 420 * N - 1} : Finset ℕ).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
    have heq : (420 * N - 1).divisors = {1, 420 * N - 1} :=
      (Finset.eq_of_subset_of_card_le h2 (by rw [hc2]; exact hsigr)).symm
    rw [Nat.prime_def_lt]
    refine ⟨by omega, ?_⟩
    intro mm hmlt hmdvd
    have hmem : mm ∈ (420 * N - 1).divisors := Nat.mem_divisors.mpr ⟨hmdvd, hr0⟩
    rw [heq] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h1 | h1
    · exact h1
    · omega
  have hn_mod : (420 * N) % ℓ = 1 → False := by
    intro hm
    have hdivmod := Nat.div_add_mod (420 * N) ℓ
    have hdvd : ℓ ∣ (420 * N - 1) := ⟨420 * N / ℓ, by omega⟩
    have hor := Nat.Prime.eq_one_or_self_of_dvd hprime ℓ hdvd
    omega
  exact hn_mod hmod

theorem erdos647_bridge8_le29 :
    ∀ n N ℓ : ℕ, 84 < n → (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 →
      n = 2520 * N → Nat.Prime ℓ → 11 ≤ ℓ → ℓ ≤ 29 → 315 * N % ℓ ≠ 1 := by
  intro n N ℓ hn H hnN hℓ h11 h29 hmod
  have hprime2 : ∀ x : ℕ, 2 ≤ x → ArithmeticFunction.sigma 0 x ≤ 2 → Nat.Prime x := by
    intro x hx hs
    rw [ArithmeticFunction.sigma_zero_apply] at hs
    have hx0 : x ≠ 0 := (by omega)
    have hsub : ({1, x} : Finset ℕ) ⊆ x.divisors := by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rw [Nat.mem_divisors]
      rcases hy with rfl | rfl
      · exact ⟨one_dvd _, hx0⟩
      · exact ⟨dvd_rfl, hx0⟩
    have hc2 : ({1, x} : Finset ℕ).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
    have heq : x.divisors = {1, x} := (Finset.eq_of_subset_of_card_le hsub (by rw [hc2]; exact hs)).symm
    rw [Nat.prime_def_lt]
    refine ⟨by omega, ?_⟩
    intro mm hmlt hmdvd
    have hmem : mm ∈ x.divisors := Nat.mem_divisors.mpr ⟨hmdvd, hx0⟩
    rw [heq] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h1 | h1
    · exact h1
    · omega
  have shift : ArithmeticFunction.sigma 0 (n - 8) ≤ 10 := by
    have hsub : n - 8 < n := (by omega)
    let f : Fin n → ℕ := fun x => (x : ℕ) + ArithmeticFunction.sigma 0 x
    have hbdd : BddAbove (Set.range f) := by
      refine ⟨2 * n, ?_⟩
      rintro y ⟨x, rfl⟩
      dsimp [f]
      rw [ArithmeticFunction.sigma_zero_apply]
      have hc := Nat.card_divisors_le_self (x : ℕ)
      have hx : (x : ℕ) < n := x.isLt
      omega
    let mm : Fin n := ⟨n - 8, hsub⟩
    have hm : f mm ≤ n + 2 := le_trans (le_ciSup hbdd mm) H
    dsimp [f, mm] at hm
    omega
  have hN1 : 1 ≤ N := by
    by_contra h
    push_neg at h
    interval_cases N
    simp at hmod
  have hn8 : n - 8 = 8 * (315 * N - 1) := (by omega)
  obtain ⟨a, s, hs_odd, hrs⟩ := Nat.exists_eq_two_pow_mul_odd (show 315 * N - 1 ≠ 0 by omega)
  have hs1 : 1 ≤ s := by
    rcases Nat.eq_zero_or_pos s with h | h
    · rw [h, Nat.mul_zero] at hrs; omega
    · exact h
  have hodd2 : ¬ (2 ∣ s) := (by have := Nat.odd_iff.mp hs_odd; omega)
  have hcop2 : Nat.Coprime 2 s := (Nat.prime_two.coprime_iff_not_dvd).mpr hodd2
  have hcop : Nat.Coprime (2 ^ (a + 3)) s := hcop2.pow_left (a + 3)
  have hn8s : n - 8 = 2 ^ (a + 3) * s := by rw [hn8, hrs, pow_add] <;> ring
  have hsig8 : ArithmeticFunction.sigma 0 (n - 8) = (a + 4) * ArithmeticFunction.sigma 0 s := by
    rw [hn8s, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop, ArithmeticFunction.sigma_zero_apply_prime_pow Nat.prime_two] <;> ring
  have hbudget : (a + 4) * ArithmeticFunction.sigma 0 s ≤ 10 := (by rw [← hsig8]; exact shift)
  have hcases : a = 0 ∨ a = 1 ∨ 2 ≤ a := (by omega)
  have hchar8 : Nat.Prime (315 * N - 1) ∨ ∃ p : ℕ, Nat.Prime p ∧ (315 * N - 1) = 2 * p := by
    rcases hcases with rfl | rfl | ha
    · have hrs0 : (315 * N - 1) = s := by rw [hrs] <;> ring
      have hsle : ArithmeticFunction.sigma 0 (315 * N - 1) ≤ 2 := by rw [hrs0]; omega
      exact Or.inl (hprime2 (315 * N - 1) (by omega) hsle)
    · have hrs1 : (315 * N - 1) = 2 * s := by rw [hrs] <;> ring
      have hsle : ArithmeticFunction.sigma 0 s ≤ 2 := (by omega)
      exact Or.inr ⟨s, hprime2 s (by omega) hsle, hrs1⟩
    · exfalso
      have h6 : 6 * ArithmeticFunction.sigma 0 s ≤ 10 := le_trans (Nat.mul_le_mul_right (ArithmeticFunction.sigma 0 s) (by omega : (6:ℕ) ≤ a + 4)) hbudget
      have hsle1 : ArithmeticFunction.sigma 0 s ≤ 1 := (by omega)
      have hs_eq1 : s = 1 := by
        by_contra hne
        rw [ArithmeticFunction.sigma_zero_apply] at hsle1
        have hcard : 1 < s.divisors.card := Finset.one_lt_card.mpr ⟨1, Nat.one_mem_divisors.mpr (by omega), s, Nat.mem_divisors_self s (by omega), by omega⟩
        omega
      have hsig1 : ArithmeticFunction.sigma 0 s = 1 := (by rw [hs_eq1]; native_decide)
      have hale6 : a ≤ 6 := by rw [hsig1, Nat.mul_one] at hbudget; omega
      rw [hs_eq1, Nat.mul_one] at hrs
      have hpow : (2:ℕ) ^ a ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) hale6
      have h64 : (2:ℕ) ^ 6 = 64 := (by norm_num)
      omega
  have hdivmod := Nat.div_add_mod (315 * N) ℓ
  have hdvd : ℓ ∣ (315 * N - 1) := ⟨315 * N / ℓ, by omega⟩
  rcases hchar8 with hp | ⟨p, hp, heq⟩
  · have hor := Nat.Prime.eq_one_or_self_of_dvd hp ℓ hdvd
    omega
  · rw [heq] at hdvd
    have h2dvd : ¬ ℓ ∣ 2 := by
      intro hc
      have := Nat.le_of_dvd (by norm_num) hc
      omega
    have hℓp : ℓ ∣ p := (hℓ.dvd_mul.mp hdvd).resolve_left h2dvd
    have heqlp : ℓ = p := (Nat.prime_dvd_prime_iff_eq hℓ hp).mp hℓp
    rw [← heqlp] at heq
    omega

theorem erdos647_bridge9_le29 :
    ∀ n N ℓ : ℕ, 84 < n → (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 →
      n = 2520 * N → Nat.Prime ℓ → 11 ≤ ℓ → ℓ ≤ 29 → 280 * N % ℓ ≠ 1 := by
  intro n N ℓ hn H hnN hℓ h11 h29 hmod
  have hprime2 : ∀ x : ℕ, 2 ≤ x → ArithmeticFunction.sigma 0 x ≤ 2 → Nat.Prime x := by
    intro x hx hs
    rw [ArithmeticFunction.sigma_zero_apply] at hs
    have hx0 : x ≠ 0 := (by omega)
    have hsub : ({1, x} : Finset ℕ) ⊆ x.divisors := by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rw [Nat.mem_divisors]
      rcases hy with rfl | rfl
      · exact ⟨one_dvd _, hx0⟩
      · exact ⟨dvd_rfl, hx0⟩
    have hc2 : ({1, x} : Finset ℕ).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
    have heq : x.divisors = {1, x} := (Finset.eq_of_subset_of_card_le hsub (by rw [hc2]; exact hs)).symm
    rw [Nat.prime_def_lt]
    refine ⟨by omega, ?_⟩
    intro mm hmlt hmdvd
    have hmem : mm ∈ x.divisors := Nat.mem_divisors.mpr ⟨hmdvd, hx0⟩
    rw [heq] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h1 | h1
    · exact h1
    · omega
  have hchar : ∀ r : ℕ, 2 ≤ r → ArithmeticFunction.sigma 0 r ≤ 3 → Nat.Prime r ∨ ∃ p : ℕ, Nat.Prime p ∧ r = p ^ 2 := by
    intro r hr hcard
    rw [ArithmeticFunction.sigma_zero_apply] at hcard
    have hr0 : r ≠ 0 := (by omega)
    have hr1 : r ≠ 1 := (by omega)
    have hp : (r.minFac).Prime := Nat.minFac_prime hr1
    by_cases hpr : r.minFac = r
    · exact Or.inl (hpr ▸ hp)
    · right
      refine ⟨r.minFac, hp, ?_⟩
      have hpd : r.minFac ∣ r := Nat.minFac_dvd r
      have hp2 : 2 ≤ r.minFac := hp.two_le
      have hplt : r.minFac < r := lt_of_le_of_ne (Nat.le_of_dvd (by omega) hpd) hpr
      have hsub2 : ({1, r.minFac, r} : Finset ℕ) ⊆ r.divisors := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rw [Nat.mem_divisors]
        rcases hx with rfl | rfl | rfl
        · exact ⟨one_dvd r, hr0⟩
        · exact ⟨hpd, hr0⟩
        · exact ⟨dvd_rfl, hr0⟩
      have hcard3 : ({1, r.minFac, r} : Finset ℕ).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
      have heq : r.divisors = {1, r.minFac, r} :=
        (Finset.eq_of_subset_of_card_le hsub2 (by rw [hcard3]; exact hcard)).symm
      have hmul : r.minFac * (r / r.minFac) = r := Nat.mul_div_cancel' hpd
      have hqd : r / r.minFac ∣ r := ⟨r.minFac, by rw [Nat.mul_comm]; exact hmul.symm⟩
      have hqmem : r / r.minFac ∈ r.divisors := Nat.mem_divisors.mpr ⟨hqd, hr0⟩
      rw [heq] at hqmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hqmem
      rcases hqmem with h1 | h2 | h3
      · rw [h1, mul_one] at hmul
        exact absurd hmul (Nat.ne_of_lt hplt)
      · rw [h2] at hmul
        rw [pow_two]
        exact hmul.symm
      · rw [h3] at hmul
        exfalso
        nlinarith [hp2, hr, hmul]
  have shift : ArithmeticFunction.sigma 0 (n - 9) ≤ 11 := by
    have hsub : n - 9 < n := (by omega)
    let f : Fin n → ℕ := fun x => (x : ℕ) + ArithmeticFunction.sigma 0 x
    have hbdd : BddAbove (Set.range f) := by
      refine ⟨2 * n, ?_⟩
      rintro y ⟨x, rfl⟩
      dsimp [f]
      rw [ArithmeticFunction.sigma_zero_apply]
      have hc := Nat.card_divisors_le_self (x : ℕ)
      have hx : (x : ℕ) < n := x.isLt
      omega
    let mm : Fin n := ⟨n - 9, hsub⟩
    have hm : f mm ≤ n + 2 := le_trans (le_ciSup hbdd mm) H
    dsimp [f, mm] at hm
    omega
  have hN1 : 1 ≤ N := by
    by_contra h
    push_neg at h
    interval_cases N
    simp at hmod
  have hn9 : n - 9 = 9 * (280 * N - 1) := (by omega)
  obtain ⟨b, s, hnd, hrs⟩ := Nat.exists_eq_pow_mul_and_not_dvd (show 280 * N - 1 ≠ 0 by omega) 3 (by norm_num)
  have hs0 : s ≠ 0 := (by rintro rfl; exact hnd (dvd_zero 3))
  have hcop2 : Nat.Coprime 3 s := (Nat.prime_three.coprime_iff_not_dvd).mpr hnd
  have hcop : Nat.Coprime (3 ^ (b + 2)) s := hcop2.pow_left (b + 2)
  have hn9s : n - 9 = 3 ^ (b + 2) * s := by rw [hn9, hrs, pow_add] <;> ring
  have hsig9 : ArithmeticFunction.sigma 0 (n - 9) = (b + 3) * ArithmeticFunction.sigma 0 s := by
    rw [hn9s, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop, ArithmeticFunction.sigma_zero_apply_prime_pow Nat.prime_three] <;> ring
  have hbudget : (b + 3) * ArithmeticFunction.sigma 0 s ≤ 11 := (by rw [← hsig9]; exact shift)
  have hcases : b = 0 ∨ b = 1 ∨ b = 2 ∨ 3 ≤ b := (by omega)
  have hchar9 : Nat.Prime (280 * N - 1) ∨ (∃ p : ℕ, Nat.Prime p ∧ (280 * N - 1) = p ^ 2) ∨ (∃ p : ℕ, Nat.Prime p ∧ (280 * N - 1) = 3 * p) ∨ (∃ p : ℕ, Nat.Prime p ∧ (280 * N - 1) = 9 * p) := by
    rcases hcases with rfl | rfl | rfl | hb
    · have hrs0 : (280 * N - 1) = s := by rw [hrs] <;> ring
      have hsle : ArithmeticFunction.sigma 0 (280 * N - 1) ≤ 3 := by rw [hrs0]; omega
      have hs2 : 2 ≤ 280 * N - 1 := (by omega)
      rcases hchar (280 * N - 1) hs2 hsle with hp | ⟨p, hp, heqp⟩
      · exact Or.inl hp
      · exact Or.inr (Or.inl ⟨p, hp, heqp⟩)
    · have hrs1 : (280 * N - 1) = 3 * s := by rw [hrs] <;> ring
      have hsle : ArithmeticFunction.sigma 0 s ≤ 2 := (by omega)
      exact Or.inr (Or.inr (Or.inl ⟨s, hprime2 s (by omega) hsle, hrs1⟩))
    · have hrs2 : (280 * N - 1) = 9 * s := by rw [hrs] <;> ring
      have hsle : ArithmeticFunction.sigma 0 s ≤ 2 := (by omega)
      exact Or.inr (Or.inr (Or.inr ⟨s, hprime2 s (by omega) hsle, hrs2⟩))
    · exfalso
      have h6 : 6 * ArithmeticFunction.sigma 0 s ≤ 11 := le_trans (Nat.mul_le_mul_right (ArithmeticFunction.sigma 0 s) (by omega : (6:ℕ) ≤ b + 3)) hbudget
      have hsle1 : ArithmeticFunction.sigma 0 s ≤ 1 := (by omega)
      have hs_eq1 : s = 1 := by
        by_contra hne
        rw [ArithmeticFunction.sigma_zero_apply] at hsle1
        have hcard : 1 < s.divisors.card := Finset.one_lt_card.mpr ⟨1, Nat.one_mem_divisors.mpr hs0, s, Nat.mem_divisors_self s hs0, by omega⟩
        omega
      have hsig1 : ArithmeticFunction.sigma 0 s = 1 := (by rw [hs_eq1]; native_decide)
      have hble8 : b ≤ 8 := by rw [hsig1, Nat.mul_one] at hbudget; omega
      rw [hs_eq1, Nat.mul_one] at hrs
      interval_cases b <;> norm_num at hrs <;> omega
  have hdivmod := Nat.div_add_mod (280 * N) ℓ
  have hdvd : ℓ ∣ (280 * N - 1) := ⟨280 * N / ℓ, by omega⟩
  have h3dvd : ¬ ℓ ∣ 3 := by
    intro hc
    have := Nat.le_of_dvd (by norm_num) hc
    omega
  rcases hchar9 with hp | hp2 | hp3 | hp9
  · have hor := Nat.Prime.eq_one_or_self_of_dvd hp ℓ hdvd
    omega
  · obtain ⟨p, hp, heq⟩ := hp2
    rw [heq] at hdvd
    have hℓp : ℓ ∣ p := hℓ.dvd_of_dvd_pow hdvd
    have heqlp : ℓ = p := (Nat.prime_dvd_prime_iff_eq hℓ hp).mp hℓp
    rw [← heqlp] at heq
    interval_cases ℓ <;> omega
  · obtain ⟨p, hp, heq⟩ := hp3
    rw [heq] at hdvd
    have hℓp : ℓ ∣ p := (hℓ.dvd_mul.mp hdvd).resolve_left h3dvd
    have heqlp : ℓ = p := (Nat.prime_dvd_prime_iff_eq hℓ hp).mp hℓp
    rw [← heqlp] at heq
    omega
  · obtain ⟨p, hp, heq⟩ := hp9
    rw [heq] at hdvd
    have h9dvd : ℓ ∣ 9 * p := hdvd
    have hℓp : ℓ ∣ p := (hℓ.dvd_mul.mp h9dvd).resolve_left (by
      intro hc9
      have h9 : ℓ ∣ 3 * 3 := by norm_num at hc9 ⊢; exact hc9
      have := (hℓ.dvd_mul.mp h9).resolve_left h3dvd
      exact h3dvd this)
    have heqlp : ℓ = p := (Nat.prime_dvd_prime_iff_eq hℓ hp).mp hℓp
    rw [← heqlp] at heq
    omega

theorem erdos647_bridge10_le29 :
    ∀ n N ℓ : ℕ, 84 < n → (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 →
      n = 2520 * N → Nat.Prime ℓ → 11 ≤ ℓ → ℓ ≤ 29 → 252 * N % ℓ ≠ 1 := by
  intro n N ℓ hn H hnN hℓ h11 h29 hmod
  have hprime2 : ∀ x : ℕ, 2 ≤ x → ArithmeticFunction.sigma 0 x ≤ 2 → Nat.Prime x := by
    intro x hx hs
    rw [ArithmeticFunction.sigma_zero_apply] at hs
    have hx0 : x ≠ 0 := (by omega)
    have hsub : ({1, x} : Finset ℕ) ⊆ x.divisors := by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rw [Nat.mem_divisors]
      rcases hy with rfl | rfl
      · exact ⟨one_dvd _, hx0⟩
      · exact ⟨dvd_rfl, hx0⟩
    have hc2 : ({1, x} : Finset ℕ).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
    have heq : x.divisors = {1, x} := (Finset.eq_of_subset_of_card_le hsub (by rw [hc2]; exact hs)).symm
    rw [Nat.prime_def_lt]
    refine ⟨by omega, ?_⟩
    intro mm hmlt hmdvd
    have hmem : mm ∈ x.divisors := Nat.mem_divisors.mpr ⟨hmdvd, hx0⟩
    rw [heq] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h1 | h1
    · exact h1
    · omega
  have hchar : ∀ r : ℕ, 2 ≤ r → ArithmeticFunction.sigma 0 r ≤ 3 → Nat.Prime r ∨ ∃ p : ℕ, Nat.Prime p ∧ r = p ^ 2 := by
    intro r hr hcard
    rw [ArithmeticFunction.sigma_zero_apply] at hcard
    have hr0 : r ≠ 0 := (by omega)
    have hr1 : r ≠ 1 := (by omega)
    have hp : (r.minFac).Prime := Nat.minFac_prime hr1
    by_cases hpr : r.minFac = r
    · exact Or.inl (hpr ▸ hp)
    · right
      refine ⟨r.minFac, hp, ?_⟩
      have hpd : r.minFac ∣ r := Nat.minFac_dvd r
      have hp2 : 2 ≤ r.minFac := hp.two_le
      have hplt : r.minFac < r := lt_of_le_of_ne (Nat.le_of_dvd (by omega) hpd) hpr
      have hsub2 : ({1, r.minFac, r} : Finset ℕ) ⊆ r.divisors := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rw [Nat.mem_divisors]
        rcases hx with rfl | rfl | rfl
        · exact ⟨one_dvd r, hr0⟩
        · exact ⟨hpd, hr0⟩
        · exact ⟨dvd_rfl, hr0⟩
      have hcard3 : ({1, r.minFac, r} : Finset ℕ).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
      have heq : r.divisors = {1, r.minFac, r} :=
        (Finset.eq_of_subset_of_card_le hsub2 (by rw [hcard3]; exact hcard)).symm
      have hmul : r.minFac * (r / r.minFac) = r := Nat.mul_div_cancel' hpd
      have hqd : r / r.minFac ∣ r := ⟨r.minFac, by rw [Nat.mul_comm]; exact hmul.symm⟩
      have hqmem : r / r.minFac ∈ r.divisors := Nat.mem_divisors.mpr ⟨hqd, hr0⟩
      rw [heq] at hqmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hqmem
      rcases hqmem with h1 | h2 | h3
      · rw [h1, mul_one] at hmul
        exact absurd hmul (Nat.ne_of_lt hplt)
      · rw [h2] at hmul
        rw [pow_two]
        exact hmul.symm
      · rw [h3] at hmul
        exfalso
        nlinarith [hp2, hr, hmul]
  have shift : ArithmeticFunction.sigma 0 (n - 10) ≤ 12 := by
    have hsub : n - 10 < n := (by omega)
    let f : Fin n → ℕ := fun x => (x : ℕ) + ArithmeticFunction.sigma 0 x
    have hbdd : BddAbove (Set.range f) := by
      refine ⟨2 * n, ?_⟩
      rintro y ⟨x, rfl⟩
      dsimp [f]
      rw [ArithmeticFunction.sigma_zero_apply]
      have hc := Nat.card_divisors_le_self (x : ℕ)
      have hx : (x : ℕ) < n := x.isLt
      omega
    let mm : Fin n := ⟨n - 10, hsub⟩
    have hm : f mm ≤ n + 2 := le_trans (le_ciSup hbdd mm) H
    dsimp [f, mm] at hm
    omega
  have hN1 : 1 ≤ N := by
    by_contra h
    push_neg at h
    interval_cases N
    simp at hmod
  have hn10 : n - 10 = 10 * (252 * N - 1) := (by omega)
  have hrodd : ¬ (2 ∣ 252 * N - 1) := (by omega)
  obtain ⟨c, s, hnd, hrs⟩ := Nat.exists_eq_pow_mul_and_not_dvd (show 252 * N - 1 ≠ 0 by omega) 5 (by norm_num)
  have hs0 : s ≠ 0 := (by rintro rfl; exact hnd (dvd_zero 5))
  have hsodd : ¬ (2 ∣ s) := by
    intro hcon
    apply hrodd
    rw [hrs]
    exact Dvd.dvd.mul_left hcon (5 ^ c)
  have hcop25 : Nat.Coprime (2 * 5 ^ (c + 1)) s := by
    have h2s : Nat.Coprime 2 s := (Nat.prime_two.coprime_iff_not_dvd).mpr hsodd
    have h5s : Nat.Coprime 5 s := (by norm_num : Nat.Prime 5).coprime_iff_not_dvd.mpr hnd
    exact h2s.mul (h5s.pow_left (c + 1))
  have hn10s : n - 10 = (2 * 5 ^ (c + 1)) * s := by rw [hn10, hrs] <;> ring
  have hsig10 : ArithmeticFunction.sigma 0 (n - 10) = (2 * (c + 2)) * ArithmeticFunction.sigma 0 s := by
    rw [hn10s, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop25]
    have h2v : ArithmeticFunction.sigma 0 (2 * 5 ^ (c + 1)) = 2 * (c + 2) := by
      have hcop2_5 : Nat.Coprime 2 (5 ^ (c + 1)) := (Nat.prime_two.coprime_iff_not_dvd).mpr (by
        intro hcon; have := (Nat.prime_two.dvd_of_dvd_pow hcon); omega)
      rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop2_5]
      have hs2 : ArithmeticFunction.sigma 0 2 = 2 := by native_decide
      rw [hs2, ArithmeticFunction.sigma_zero_apply_prime_pow (by norm_num : Nat.Prime 5)] <;> ring
    rw [h2v]
  have hbudget : (2 * (c + 2)) * ArithmeticFunction.sigma 0 s ≤ 12 := (by rw [← hsig10]; exact shift)
  have hcases : c = 0 ∨ c = 1 ∨ 2 ≤ c := (by omega)
  have hchar10 : Nat.Prime (252 * N - 1) ∨ (∃ p : ℕ, Nat.Prime p ∧ (252 * N - 1) = p ^ 2) ∨ (∃ p : ℕ, Nat.Prime p ∧ (252 * N - 1) = 5 * p) := by
    rcases hcases with rfl | rfl | hc
    · have hrs0 : (252 * N - 1) = s := by rw [hrs] <;> ring
      have hsle : ArithmeticFunction.sigma 0 (252 * N - 1) ≤ 3 := by rw [hrs0]; omega
      have hs2 : 2 ≤ 252 * N - 1 := (by omega)
      rcases hchar (252 * N - 1) hs2 hsle with hp | ⟨p, hp, heqp⟩
      · exact Or.inl hp
      · exact Or.inr (Or.inl ⟨p, hp, heqp⟩)
    · have hrs1 : (252 * N - 1) = 5 * s := by rw [hrs] <;> ring
      have hsle : ArithmeticFunction.sigma 0 s ≤ 2 := (by omega)
      exact Or.inr (Or.inr ⟨s, hprime2 s (by omega) hsle, hrs1⟩)
    · exfalso
      have h8 : 8 * ArithmeticFunction.sigma 0 s ≤ 12 := le_trans (Nat.mul_le_mul_right (ArithmeticFunction.sigma 0 s) (by omega : (8:ℕ) ≤ 2 * (c + 2))) hbudget
      have hsle1 : ArithmeticFunction.sigma 0 s ≤ 1 := (by omega)
      have hs_eq1 : s = 1 := by
        by_contra hne
        rw [ArithmeticFunction.sigma_zero_apply] at hsle1
        have hcard : 1 < s.divisors.card := Finset.one_lt_card.mpr ⟨1, Nat.one_mem_divisors.mpr hs0, s, Nat.mem_divisors_self s hs0, by omega⟩
        omega
      have hsig1 : ArithmeticFunction.sigma 0 s = 1 := (by rw [hs_eq1]; native_decide)
      have hcle4 : c ≤ 4 := by rw [hsig1, Nat.mul_one] at hbudget; omega
      rw [hs_eq1, Nat.mul_one] at hrs
      interval_cases c <;> norm_num at hrs <;> omega
  have hdivmod := Nat.div_add_mod (252 * N) ℓ
  have hdvd : ℓ ∣ (252 * N - 1) := ⟨252 * N / ℓ, by omega⟩
  have h5dvd : ¬ ℓ ∣ 5 := by
    intro hc
    have := Nat.le_of_dvd (by norm_num) hc
    omega
  rcases hchar10 with hp | hp2 | hp5
  · have hor := Nat.Prime.eq_one_or_self_of_dvd hp ℓ hdvd
    omega
  · obtain ⟨p, hp, heq⟩ := hp2
    rw [heq] at hdvd
    have hℓp : ℓ ∣ p := hℓ.dvd_of_dvd_pow hdvd
    have heqlp : ℓ = p := (Nat.prime_dvd_prime_iff_eq hℓ hp).mp hℓp
    rw [← heqlp] at heq
    interval_cases ℓ <;> omega
  · obtain ⟨p, hp, heq⟩ := hp5
    rw [heq] at hdvd
    have hℓp : ℓ ∣ p := (hℓ.dvd_mul.mp hdvd).resolve_left h5dvd
    have heqlp : ℓ = p := (Nat.prime_dvd_prime_iff_eq hℓ hp).mp hℓp
    rw [← heqlp] at heq
    omega
