import Mathlib

/-!
# Erdős 647: large candidates are divisible by 2520

This file assembles the kernel-verified congruence exclusions recovered from the
proof-search archive.  Each long component below was independently checked in
its originating episode; the final theorem is the concrete interface needed by
the seven-form reindexing.

Proof-search episodes:
* `candidate_dvd_four`: `e5c18ce8-f159-4f38-92af-443ac9ad668d`
* `candidate_dvd_three_of_four`: `e323509e-4d27-4091-9092-0e8edd2a96f0`
* `candidate_dvd_five_of_six`: `aae17408-0792-49c4-b8aa-00a307711dea`
* `candidate_dvd_eight_of_four`: `4edd4cea-3c41-4b16-aa93-0cb747908c00`
* `candidate_dvd_nine_of_six`: `4884fb8e-01a6-41b8-8c8a-d407faa9b7e9`
* `candidate_not_mod_seven_one`: `5b0b40ad-6e9d-445f-b2bf-881329a4bc53`
* `candidate_not_mod_seven_two`: `6da10309-7f69-4308-a657-8d02d4248e19`
* `candidate_not_mod_seven_three`: `632efd9d-4bb3-44f5-8b2f-56dcfd7e9ac9`
* `candidate_not_mod_seven_four`: `44940218-7ebf-411b-a127-eb84db3a916d`
* `candidate_not_mod_seven_five`: `aa75eef8-88d2-4020-974a-e7f58d364fac`
* `candidate_not_mod_seven_six`: `daf66559-2dde-4610-8521-3d8f80f08a22`
* `dvd_seven_of_nonzero_residues`: `3b9b2497-773b-4ac5-a7f9-8c74e2369869`
* `dvd_2520_of_dvd_thirty_seven_eight_nine`: `aab8fbdc-c688-4511-b2f6-6f1f9aa5af2e`
-/

namespace Erdos647

theorem candidate_dvd_four : ∀ n : ℕ, 10 < n → (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 → 4 ∣ n := by
  intro n hn H
  have shift : ∀ k : ℕ, 0 < k → k < n → ArithmeticFunction.sigma 0 (n - k) ≤ k + 2 := by
    intro k hk hkn
    have hsub : n - k < n := by omega
    let f : Fin n → ℕ := fun x => (x : ℕ) + ArithmeticFunction.sigma 0 x
    have hbdd : BddAbove (Set.range f) := by
      refine ⟨2 * n, ?_⟩
      rintro y ⟨x, rfl⟩
      dsimp [f]
      rw [ArithmeticFunction.sigma_zero_apply]
      have hc := Nat.card_divisors_le_self (x : ℕ)
      have hx : (x : ℕ) < n := x.isLt
      omega
    let m : Fin n := ⟨n - k, hsub⟩
    have hm : f m ≤ n + 2 := le_trans (le_ciSup hbdd m) H
    dsimp [f, m] at hm
    omega
  have evenTau : ∀ a : ℕ, 4 < a → Even a → 4 ≤ ArithmeticFunction.sigma 0 a := by
    intro a ha heven
    rcases heven with ⟨b, hb⟩
    have hbgt : 2 < b := by omega
    rw [ArithmeticFunction.sigma_zero_apply]
    have hs : ({1, 2, b, a} : Finset ℕ) ⊆ a.divisors := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [Nat.mem_divisors]
      constructor
      · rcases hx with rfl | rfl | rfl | rfl
        · exact one_dvd a
        · use b
          omega
        · use 2
          omega
        · exact dvd_rfl
      · omega
    have hba : b ≠ a := by omega
    have h2b : 2 ≠ b := by omega
    have h1b : 1 ≠ b := by omega
    have h1a : 1 ≠ a := by omega
    have h2a : 2 ≠ a := by omega
    have hcard : ({1, 2, b, a} : Finset ℕ).card = 4 := by
      simp [hba, h2b, h1b, h1a, h2a]
    calc
      4 = ({1, 2, b, a} : Finset ℕ).card := hcard.symm
      _ ≤ a.divisors.card := Finset.card_le_card hs
  have fourTau : ∀ a : ℕ, 8 < a → 4 ∣ a → 5 ≤ ArithmeticFunction.sigma 0 a := by
    intro a ha hdiv
    rcases hdiv with ⟨b, hb⟩
    have hbgt : 2 < b := by omega
    rw [ArithmeticFunction.sigma_zero_apply]
    have hs : ({1, 2, 4, 2 * b, a} : Finset ℕ) ⊆ a.divisors := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [Nat.mem_divisors]
      constructor
      · rcases hx with rfl | rfl | rfl | rfl | rfl
        · exact one_dvd a
        · use 2 * b
          omega
        · use b
        · use 2
          omega
        · exact dvd_rfl
      · omega
    have h1c : 1 ≠ 2 * b := by omega
    have h1a : 1 ≠ a := by omega
    have h2c : 2 ≠ 2 * b := by omega
    have h2a : 2 ≠ a := by omega
    have h4c : 4 ≠ 2 * b := by omega
    have h4a : 4 ≠ a := by omega
    have hca : 2 * b ≠ a := by omega
    have hcard : ({1, 2, 4, 2 * b, a} : Finset ℕ).card = 5 := by
      simp [h1c, h1a, h2c, h2a, h4c, h4a, hca]
    calc
      5 = ({1, 2, 4, 2 * b, a} : Finset ℕ).card := hcard.symm
      _ ≤ a.divisors.card := Finset.card_le_card hs
  have hneven : Even n := by
    rcases Nat.even_or_odd n with he | ho
    · exact he
    · exfalso
      have hepred : Even (n - 1) := by
        rcases ho with ⟨b, hb⟩
        use b
        omega
      have hlo := shift 1 (by omega) (by omega)
      have hhi := evenTau (n - 1) (by omega) hepred
      omega
  rcases hneven with ⟨q, hq⟩
  rcases Nat.even_or_odd q with hqe | hqo
  · rcases hqe with ⟨r, hr⟩
    use r
    omega
  · exfalso
    have hfour : 4 ∣ n - 2 := by
      rcases hqo with ⟨r, hr⟩
      use r
      omega
    have hlo := shift 2 (by omega) (by omega)
    have hhi := fourTau (n - 2) (by omega) hfour
    omega

theorem candidate_dvd_three_of_four : ∀ n : ℕ, 24 < n → (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 → 4 ∣ n → 3 ∣ n := by
  intro n hn H hfourN
  have shift : ∀ k : ℕ, 0 < k → k < n → ArithmeticFunction.sigma 0 (n - k) ≤ k + 2 := by
    intro k hk hkn
    have hsub : n - k < n := by omega
    let f : Fin n → ℕ := fun x => (x : ℕ) + ArithmeticFunction.sigma 0 x
    have hbdd : BddAbove (Set.range f) := by
      refine ⟨2 * n, ?_⟩
      rintro y ⟨x, rfl⟩
      dsimp [f]
      rw [ArithmeticFunction.sigma_zero_apply]
      have hc := Nat.card_divisors_le_self (x : ℕ)
      have hx : (x : ℕ) < n := x.isLt
      omega
    let m : Fin n := ⟨n - k, hsub⟩
    have hm : f m ≤ n + 2 := le_trans (le_ciSup hbdd m) H
    dsimp [f, m] at hm
    omega
  have hmod : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases hmod with h0 | h1 | h2
  · exact Nat.dvd_iff_mod_eq_zero.mpr h0
  · exfalso
    have hdiv : 3 ∣ n - 1 := by
      rw [Nat.dvd_iff_mod_eq_zero]
      omega
    rcases hdiv with ⟨b, hb⟩
    have hbgt : 3 < b := by omega
    have hge : 4 ≤ ArithmeticFunction.sigma 0 (n - 1) := by
      rw [ArithmeticFunction.sigma_zero_apply]
      have hs : ({1, 3, b, n - 1} : Finset ℕ) ⊆ (n - 1).divisors := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rw [Nat.mem_divisors]
        constructor
        · rcases hx with rfl | rfl | rfl | rfl
          · exact one_dvd (n - 1)
          · use b
          · use 3
            omega
          · exact dvd_rfl
        · omega
      have hba : b ≠ n - 1 := by omega
      have h3b : 3 ≠ b := by omega
      have h1b : 1 ≠ b := by omega
      have h1a : 1 ≠ n - 1 := by omega
      have h3a : 3 ≠ n - 1 := by omega
      have hcard : ({1, 3, b, n - 1} : Finset ℕ).card = 4 := by
        simp [hba, h3b, h1b, h1a, h3a]
      calc
        4 = ({1, 3, b, n - 1} : Finset ℕ).card := hcard.symm
        _ ≤ (n - 1).divisors.card := Finset.card_le_card hs
    have hle := shift 1 (by omega) (by omega)
    omega
  · exfalso
    have hdiv3 : 3 ∣ n - 2 := by
      rw [Nat.dvd_iff_mod_eq_zero]
      omega
    rcases hdiv3 with ⟨b, hb⟩
    have hbEven : Even b := by
      rcases Nat.even_or_odd b with he | ho
      · exact he
      · exfalso
        rcases hfourN with ⟨q, hq⟩
        rcases ho with ⟨r, hr⟩
        omega
    rcases hbEven with ⟨c, hc⟩
    have ha6 : n - 2 = 6 * c := by omega
    have hge : 5 ≤ ArithmeticFunction.sigma 0 (n - 2) := by
      rw [ArithmeticFunction.sigma_zero_apply]
      have hs : ({1, 2, 3, 6, n - 2} : Finset ℕ) ⊆ (n - 2).divisors := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rw [Nat.mem_divisors]
        constructor
        · rcases hx with rfl | rfl | rfl | rfl | rfl
          · exact one_dvd (n - 2)
          · use 3 * c
            omega
          · use 2 * c
            omega
          · use c
          · exact dvd_rfl
        · omega
      have h1a : 1 ≠ n - 2 := by omega
      have h2a : 2 ≠ n - 2 := by omega
      have h3a : 3 ≠ n - 2 := by omega
      have h6a : 6 ≠ n - 2 := by omega
      have hcard : ({1, 2, 3, 6, n - 2} : Finset ℕ).card = 5 := by
        simp [h1a, h2a, h3a, h6a]
      calc
        5 = ({1, 2, 3, 6, n - 2} : Finset ℕ).card := hcard.symm
        _ ≤ (n - 2).divisors.card := Finset.card_le_card hs
    have hle := shift 2 (by omega) (by omega)
    omega

theorem candidate_dvd_five_of_six : ∀ n : ℕ, 54 < n → (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 → 6 ∣ n → 5 ∣ n := by
  intro n hn H hsix
  have shift : ∀ k : ℕ, 0 < k → k < n → ArithmeticFunction.sigma 0 (n - k) ≤ k + 2 := by
    intro k hk hkn
    have hsub : n - k < n := by omega
    let f : Fin n → ℕ := fun x => (x : ℕ) + ArithmeticFunction.sigma 0 x
    have hbdd : BddAbove (Set.range f) := by
      refine ⟨2 * n, ?_⟩
      rintro y ⟨x, rfl⟩
      dsimp [f]
      rw [ArithmeticFunction.sigma_zero_apply]
      have hc := Nat.card_divisors_le_self (x : ℕ)
      have hx : (x : ℕ) < n := x.isLt
      omega
    let m : Fin n := ⟨n - k, hsub⟩
    have hm : f m ≤ n + 2 := le_trans (le_ciSup hbdd m) H
    dsimp [f, m] at hm
    omega
  have hmod : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by omega
  rcases hmod with h0 | h1 | h2 | h3 | h4
  · exact Nat.dvd_iff_mod_eq_zero.mpr h0
  · exfalso
    have hd : 5 ∣ n - 1 := by rw [Nat.dvd_iff_mod_eq_zero]; omega
    rcases hd with ⟨b, hb⟩
    have hbgt : 5 < b := by omega
    have hge : 4 ≤ ArithmeticFunction.sigma 0 (n - 1) := by
      rw [ArithmeticFunction.sigma_zero_apply]
      have hsub : ({1, 5, b, n - 1} : Finset ℕ) ⊆ (n - 1).divisors := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rw [Nat.mem_divisors]
        constructor
        · rcases hx with rfl | rfl | rfl | rfl
          · exact one_dvd (n - 1)
          · use b
          · use 5
            omega
          · exact dvd_rfl
        · omega
      have hba : b ≠ n - 1 := by omega
      have h5b : 5 ≠ b := by omega
      have h1b : 1 ≠ b := by omega
      have h1a : 1 ≠ n - 1 := by omega
      have h5a : 5 ≠ n - 1 := by omega
      have hcard : ({1, 5, b, n - 1} : Finset ℕ).card = 4 := by simp [hba, h5b, h1b, h1a, h5a]
      calc
        4 = ({1, 5, b, n - 1} : Finset ℕ).card := hcard.symm
        _ ≤ (n - 1).divisors.card := Finset.card_le_card hsub
    have hle := shift 1 (by omega) (by omega)
    omega
  · exfalso
    have hd : 5 ∣ n - 2 := by rw [Nat.dvd_iff_mod_eq_zero]; omega
    rcases hd with ⟨b, hb⟩
    have hbEven : Even b := by
      rcases Nat.even_or_odd b with he | ho
      · exact he
      · exfalso
        rcases hsix with ⟨q, hq⟩
        rcases ho with ⟨r, hr⟩
        omega
    rcases hbEven with ⟨c, hc⟩
    have ha : n - 2 = 10 * c := by omega
    have hge : 5 ≤ ArithmeticFunction.sigma 0 (n - 2) := by
      rw [ArithmeticFunction.sigma_zero_apply]
      have hsub : ({1, 2, 5, 10, n - 2} : Finset ℕ) ⊆ (n - 2).divisors := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rw [Nat.mem_divisors]
        constructor
        · rcases hx with rfl | rfl | rfl | rfl | rfl
          · exact one_dvd (n - 2)
          · use 5 * c
            omega
          · use 2 * c
            omega
          · use c
          · exact dvd_rfl
        · omega
      have h1a : 1 ≠ n - 2 := by omega
      have h2a : 2 ≠ n - 2 := by omega
      have h5a : 5 ≠ n - 2 := by omega
      have h10a : 10 ≠ n - 2 := by omega
      have hcard : ({1, 2, 5, 10, n - 2} : Finset ℕ).card = 5 := by simp [h1a, h2a, h5a, h10a]
      calc
        5 = ({1, 2, 5, 10, n - 2} : Finset ℕ).card := hcard.symm
        _ ≤ (n - 2).divisors.card := Finset.card_le_card hsub
    have hle := shift 2 (by omega) (by omega)
    omega
  · exfalso
    have hd : 5 ∣ n - 3 := by rw [Nat.dvd_iff_mod_eq_zero]; omega
    rcases hd with ⟨b, hb⟩
    rcases hsix with ⟨q, hq⟩
    have hbmod : b % 3 = 0 := by omega
    rcases (Nat.dvd_iff_mod_eq_zero.mpr hbmod) with ⟨c, hc⟩
    have ha : n - 3 = 15 * c := by omega
    have hcgt : 3 < c := by omega
    have hge : 6 ≤ ArithmeticFunction.sigma 0 (n - 3) := by
      rw [ArithmeticFunction.sigma_zero_apply]
      have hsub : ({1, 3, 5, 15, 5 * c, n - 3} : Finset ℕ) ⊆ (n - 3).divisors := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rw [Nat.mem_divisors]
        constructor
        · rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
          · exact one_dvd (n - 3)
          · use 5 * c
            omega
          · use 3 * c
            omega
          · use c
          · use 3
            omega
          · exact dvd_rfl
        · omega
      have h1c : 1 ≠ 5 * c := by omega
      have h3c : 3 ≠ 5 * c := by omega
      have h5c : 5 ≠ 5 * c := by omega
      have h15c : 15 ≠ 5 * c := by omega
      have hca : 5 * c ≠ n - 3 := by omega
      have h1a : 1 ≠ n - 3 := by omega
      have h3a : 3 ≠ n - 3 := by omega
      have h5a : 5 ≠ n - 3 := by omega
      have h15a : 15 ≠ n - 3 := by omega
      have hcard : ({1, 3, 5, 15, 5 * c, n - 3} : Finset ℕ).card = 6 := by
        simp [h1c, h3c, h5c, h15c, hca, h1a, h3a, h5a, h15a]
      calc
        6 = ({1, 3, 5, 15, 5 * c, n - 3} : Finset ℕ).card := hcard.symm
        _ ≤ (n - 3).divisors.card := Finset.card_le_card hsub
    have hle := shift 3 (by omega) (by omega)
    omega
  · exfalso
    have hd : 5 ∣ n - 4 := by rw [Nat.dvd_iff_mod_eq_zero]; omega
    rcases hd with ⟨b, hb⟩
    have hbEven : Even b := by
      rcases Nat.even_or_odd b with he | ho
      · exact he
      · exfalso
        rcases hsix with ⟨q, hq⟩
        rcases ho with ⟨r, hr⟩
        omega
    rcases hbEven with ⟨c, hc⟩
    have ha : n - 4 = 10 * c := by omega
    rcases hsix with ⟨q, hq⟩
    have hcgt : 5 < c := by omega
    have hc10 : c ≠ 10 := by omega
    have h10c : 10 ≠ c := Ne.symm hc10
    have hge : 7 ≤ ArithmeticFunction.sigma 0 (n - 4) := by
      rw [ArithmeticFunction.sigma_zero_apply]
      have hsub : ({1, 2, 5, 10, c, 5 * c, n - 4} : Finset ℕ) ⊆ (n - 4).divisors := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rw [Nat.mem_divisors]
        constructor
        · rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · exact one_dvd (n - 4)
          · use 5 * c
            omega
          · use 2 * c
            omega
          · use c
          · use 10
            omega
          · use 2
            omega
          · exact dvd_rfl
        · omega
      have h1c : 1 ≠ c := by omega
      have h2c : 2 ≠ c := by omega
      have h5c : 5 ≠ c := by omega
      have h1d : 1 ≠ 5 * c := by omega
      have h2d : 2 ≠ 5 * c := by omega
      have h5d : 5 ≠ 5 * c := by omega
      have h10d : 10 ≠ 5 * c := by omega
      have hcd : c ≠ 5 * c := by omega
      have hca : c ≠ n - 4 := by omega
      have hda : 5 * c ≠ n - 4 := by omega
      have h1a : 1 ≠ n - 4 := by omega
      have h2a : 2 ≠ n - 4 := by omega
      have h5a : 5 ≠ n - 4 := by omega
      have h10a : 10 ≠ n - 4 := by omega
      have hcard : ({1, 2, 5, 10, c, 5 * c, n - 4} : Finset ℕ).card = 7 := by
        simp [h10c, h1c, h2c, h5c, h1d, h2d, h5d, h10d, hcd, hca, hda, h1a, h2a, h5a, h10a]
      calc
        7 = ({1, 2, 5, 10, c, 5 * c, n - 4} : Finset ℕ).card := hcard.symm
        _ ≤ (n - 4).divisors.card := Finset.card_le_card hsub
    have hle := shift 4 (by omega) (by omega)
    omega

theorem candidate_dvd_eight_of_four : ∀ n : ℕ, 36 < n → (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 → 4 ∣ n → 8 ∣ n := by
  intro n hn H h4
  have shift : ArithmeticFunction.sigma 0 (n - 4) ≤ 6 := by
    have hsub : n - 4 < n := by omega
    let f : Fin n → ℕ := fun x => (x : ℕ) + ArithmeticFunction.sigma 0 x
    have hbdd : BddAbove (Set.range f) := by
      refine ⟨2 * n, ?_⟩
      rintro y ⟨x, rfl⟩
      dsimp [f]
      rw [ArithmeticFunction.sigma_zero_apply]
      have hc := Nat.card_divisors_le_self (x : ℕ)
      have hx : (x : ℕ) < n := x.isLt
      omega
    let m : Fin n := ⟨n - 4, hsub⟩
    have hm : f m ≤ n + 2 := le_trans (le_ciSup hbdd m) H
    dsimp [f, m] at hm
    omega
  rcases h4 with ⟨q, hq⟩
  have hmod : n % 8 = 0 ∨ n % 8 = 4 := by omega
  rcases hmod with h0 | hbad
  · exact Nat.dvd_iff_mod_eq_zero.mpr h0
  · have hd : 8 ∣ n - 4 := by
      apply Nat.dvd_iff_mod_eq_zero.mpr
      omega
    rcases hd with ⟨b, hb⟩
    have hbgt : 4 < b := by omega
    by_cases hb8 : b = 8
    · have hn68 : n = 68 := by omega
      have hge : 7 ≤ ArithmeticFunction.sigma 0 (n - 4) := by
        rw [hn68, ArithmeticFunction.sigma_zero_apply]
        have hsub : ({1, 2, 4, 8, 16, 32, 64} : Finset ℕ) ⊆ (64 : ℕ).divisors := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rw [Nat.mem_divisors]
          constructor
          · rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
          · norm_num
        have hcard : ({1, 2, 4, 8, 16, 32, 64} : Finset ℕ).card = 7 := by norm_num
        calc
          7 = ({1, 2, 4, 8, 16, 32, 64} : Finset ℕ).card := hcard.symm
          _ ≤ (64 : ℕ).divisors.card := Finset.card_le_card hsub
      exact False.elim (Nat.not_succ_le_self 6 (le_trans hge shift))
    · have hge : 7 ≤ ArithmeticFunction.sigma 0 (n - 4) := by
        rw [ArithmeticFunction.sigma_zero_apply]
        have hsub : ({1, 2, 4, 8, b, 2 * b, n - 4} : Finset ℕ) ⊆ (n - 4).divisors := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rw [Nat.mem_divisors]
          constructor
          · rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
            · exact one_dvd (n - 4)
            · use 4 * b
              omega
            · use 2 * b
              omega
            · use b
            · use 8
              omega
            · use 4
              omega
            · exact dvd_rfl
          · omega
        have h1b : 1 ≠ b := by omega
        have h2b : 2 ≠ b := by omega
        have h4b : 4 ≠ b := by omega
        have h8b : 8 ≠ b := Ne.symm hb8
        have h1d : 1 ≠ 2 * b := by omega
        have h2d : 2 ≠ 2 * b := by omega
        have h4d : 4 ≠ 2 * b := by omega
        have h8d : 8 ≠ 2 * b := by omega
        have hbd : b ≠ 2 * b := by omega
        have h1a : 1 ≠ n - 4 := by omega
        have h2a : 2 ≠ n - 4 := by omega
        have h4a : 4 ≠ n - 4 := by omega
        have h8a : 8 ≠ n - 4 := by omega
        have hba : b ≠ n - 4 := by omega
        have hda : 2 * b ≠ n - 4 := by omega
        have hcard : ({1, 2, 4, 8, b, 2 * b, n - 4} : Finset ℕ).card = 7 := by
          simp [h1b, h2b, h4b, h8b, h1d, h2d, h4d, h8d, hbd,
            h1a, h2a, h4a, h8a, hba, hda]
        calc
          7 = ({1, 2, 4, 8, b, 2 * b, n - 4} : Finset ℕ).card := hcard.symm
          _ ≤ (n - 4).divisors.card := Finset.card_le_card hsub
      exact False.elim (Nat.not_succ_le_self 6 (le_trans hge shift))

theorem candidate_dvd_nine_of_six : ∀ n : ℕ, 84 < n → (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 → 6 ∣ n → 9 ∣ n := by
  intro n hn H h6
  have shift : ∀ k : ℕ, 0 < k → k < n →
      ArithmeticFunction.sigma 0 (n - k) ≤ k + 2 := by
    intro k hk hkn
    have hsub : n - k < n := by omega
    let f : Fin n → ℕ := fun x => (x : ℕ) + ArithmeticFunction.sigma 0 x
    have hbdd : BddAbove (Set.range f) := by
      refine ⟨2 * n, ?_⟩
      rintro y ⟨x, rfl⟩
      dsimp [f]
      rw [ArithmeticFunction.sigma_zero_apply]
      have hc := Nat.card_divisors_le_self (x : ℕ)
      have hx : (x : ℕ) < n := x.isLt
      omega
    let m : Fin n := ⟨n - k, hsub⟩
    have hm : f m ≤ n + 2 := le_trans (le_ciSup hbdd m) H
    dsimp [f, m] at hm
    omega
  rcases h6 with ⟨q, hq⟩
  have hmod : n % 9 = 0 ∨ n % 9 = 3 ∨ n % 9 = 6 := by omega
  rcases hmod with h0 | h3 | h6r
  · exact Nat.dvd_iff_mod_eq_zero.mpr h0
  · have hd : 9 ∣ n - 3 := by
      apply Nat.dvd_iff_mod_eq_zero.mpr
      omega
    rcases hd with ⟨b, hb⟩
    have hbgt : 9 < b := by omega
    have hge : 6 ≤ ArithmeticFunction.sigma 0 (n - 3) := by
      rw [ArithmeticFunction.sigma_zero_apply]
      have hsub : ({1, 3, 9, b, 3 * b, n - 3} : Finset ℕ) ⊆ (n - 3).divisors := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rw [Nat.mem_divisors]
        constructor
        · rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
          · exact one_dvd (n - 3)
          · use 3 * b
            omega
          · use b
          · use 9
            omega
          · use 3
            omega
          · exact dvd_rfl
        · omega
      have h1b : 1 ≠ b := by omega
      have h3b : 3 ≠ b := by omega
      have h9b : 9 ≠ b := by omega
      have h1d : 1 ≠ 3 * b := by omega
      have h3d : 3 ≠ 3 * b := by omega
      have h9d : 9 ≠ 3 * b := by omega
      have hbd : b ≠ 3 * b := by omega
      have h1a : 1 ≠ n - 3 := by omega
      have h3a : 3 ≠ n - 3 := by omega
      have h9a : 9 ≠ n - 3 := by omega
      have hba : b ≠ n - 3 := by omega
      have hda : 3 * b ≠ n - 3 := by omega
      have hcard : ({1, 3, 9, b, 3 * b, n - 3} : Finset ℕ).card = 6 := by
        simp [h1b, h3b, h9b, h1d, h3d, h9d, hbd, h1a, h3a, h9a, hba, hda]
      calc
        6 = ({1, 3, 9, b, 3 * b, n - 3} : Finset ℕ).card := hcard.symm
        _ ≤ (n - 3).divisors.card := Finset.card_le_card hsub
    have hle := shift 3 (by omega) (by omega)
    exact False.elim (Nat.not_succ_le_self 5 (le_trans hge hle))
  · have hd : 18 ∣ n - 6 := by
      apply Nat.dvd_iff_mod_eq_zero.mpr
      omega
    rcases hd with ⟨b, hb⟩
    have hbgt : 4 < b := by omega
    by_cases hb6 : b = 6
    · have hn114 : n = 114 := by omega
      have hge : 9 ≤ ArithmeticFunction.sigma 0 (n - 6) := by
        rw [hn114, ArithmeticFunction.sigma_zero_apply]
        have hsub : ({1, 2, 3, 4, 6, 9, 12, 18, 108} : Finset ℕ) ⊆ (108 : ℕ).divisors := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rw [Nat.mem_divisors]
          constructor
          · rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
          · norm_num
        have hcard : ({1, 2, 3, 4, 6, 9, 12, 18, 108} : Finset ℕ).card = 9 := by norm_num
        calc
          9 = ({1, 2, 3, 4, 6, 9, 12, 18, 108} : Finset ℕ).card := hcard.symm
          _ ≤ (108 : ℕ).divisors.card := Finset.card_le_card hsub
      have hle := shift 6 (by omega) (by omega)
      exact False.elim (Nat.not_succ_le_self 8 (le_trans hge hle))
    · by_cases hb9 : b = 9
      · have hn168 : n = 168 := by omega
        have hge : 9 ≤ ArithmeticFunction.sigma 0 (n - 6) := by
          rw [hn168, ArithmeticFunction.sigma_zero_apply]
          have hsub : ({1, 2, 3, 6, 9, 18, 27, 54, 162} : Finset ℕ) ⊆ (162 : ℕ).divisors := by
            intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rw [Nat.mem_divisors]
            constructor
            · rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
            · norm_num
          have hcard : ({1, 2, 3, 6, 9, 18, 27, 54, 162} : Finset ℕ).card = 9 := by norm_num
          calc
            9 = ({1, 2, 3, 6, 9, 18, 27, 54, 162} : Finset ℕ).card := hcard.symm
            _ ≤ (162 : ℕ).divisors.card := Finset.card_le_card hsub
        have hle := shift 6 (by omega) (by omega)
        exact False.elim (Nat.not_succ_le_self 8 (le_trans hge hle))
      · by_cases hb18 : b = 18
        · have hn330 : n = 330 := by omega
          have hge : 9 ≤ ArithmeticFunction.sigma 0 (n - 6) := by
            rw [hn330, ArithmeticFunction.sigma_zero_apply]
            have hsub : ({1, 2, 3, 4, 6, 9, 12, 18, 324} : Finset ℕ) ⊆ (324 : ℕ).divisors := by
              intro x hx
              simp only [Finset.mem_insert, Finset.mem_singleton] at hx
              rw [Nat.mem_divisors]
              constructor
              · rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
              · norm_num
            have hcard : ({1, 2, 3, 4, 6, 9, 12, 18, 324} : Finset ℕ).card = 9 := by norm_num
            calc
              9 = ({1, 2, 3, 4, 6, 9, 12, 18, 324} : Finset ℕ).card := hcard.symm
              _ ≤ (324 : ℕ).divisors.card := Finset.card_le_card hsub
          have hle := shift 6 (by omega) (by omega)
          exact False.elim (Nat.not_succ_le_self 8 (le_trans hge hle))
        · have hge : 9 ≤ ArithmeticFunction.sigma 0 (n - 6) := by
            rw [ArithmeticFunction.sigma_zero_apply]
            have hsub : ({1, 2, 3, 6, 9, 18, b, 2 * b, n - 6} : Finset ℕ) ⊆ (n - 6).divisors := by
              intro x hx
              simp only [Finset.mem_insert, Finset.mem_singleton] at hx
              rw [Nat.mem_divisors]
              constructor
              · rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
                · exact one_dvd (n - 6)
                · use 9 * b
                  omega
                · use 6 * b
                  omega
                · use 3 * b
                  omega
                · use 2 * b
                  omega
                · use b
                · use 18
                  omega
                · use 9
                  omega
                · exact dvd_rfl
              · omega
            have h1b : 1 ≠ b := by omega
            have h2b : 2 ≠ b := by omega
            have h3b : 3 ≠ b := by omega
            have h6b : 6 ≠ b := Ne.symm hb6
            have h9b : 9 ≠ b := Ne.symm hb9
            have h18b : 18 ≠ b := Ne.symm hb18
            have h1d : 1 ≠ 2 * b := by omega
            have h2d : 2 ≠ 2 * b := by omega
            have h3d : 3 ≠ 2 * b := by omega
            have h6d : 6 ≠ 2 * b := by omega
            have h9d : 9 ≠ 2 * b := by omega
            have h18d : 18 ≠ 2 * b := by
              intro hh
              apply hb9
              omega
            have hbd : b ≠ 2 * b := by omega
            have h1a : 1 ≠ n - 6 := by omega
            have h2a : 2 ≠ n - 6 := by omega
            have h3a : 3 ≠ n - 6 := by omega
            have h6a : 6 ≠ n - 6 := by omega
            have h9a : 9 ≠ n - 6 := by omega
            have h18a : 18 ≠ n - 6 := by omega
            have hba : b ≠ n - 6 := by omega
            have hda : 2 * b ≠ n - 6 := by omega
            have hcard : ({1, 2, 3, 6, 9, 18, b, 2 * b, n - 6} : Finset ℕ).card = 9 := by
              simp [h1b, h2b, h3b, h6b, h9b, h18b,
                h1d, h2d, h3d, h6d, h9d, h18d, hbd,
                h1a, h2a, h3a, h6a, h9a, h18a, hba, hda]
            calc
              9 = ({1, 2, 3, 6, 9, 18, b, 2 * b, n - 6} : Finset ℕ).card := hcard.symm
              _ ≤ (n - 6).divisors.card := Finset.card_le_card hsub
          have hle := shift 6 (by omega) (by omega)
          exact False.elim (Nat.not_succ_le_self 8 (le_trans hge hle))

theorem candidate_not_mod_seven_one : ∀ n : ℕ, 54 < n → (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 → n % 7 = 1 → False := by
  intro n hn H h1
  have shift : ArithmeticFunction.sigma 0 (n - 1) ≤ 3 := by
    have hsub : n - 1 < n := by omega
    let f : Fin n → ℕ := fun x => (x : ℕ) + ArithmeticFunction.sigma 0 x
    have hbdd : BddAbove (Set.range f) := by
      refine ⟨2 * n, ?_⟩
      rintro y ⟨x, rfl⟩
      dsimp [f]
      rw [ArithmeticFunction.sigma_zero_apply]
      have hc := Nat.card_divisors_le_self (x : ℕ)
      have hx : (x : ℕ) < n := x.isLt
      omega
    let m : Fin n := ⟨n - 1, hsub⟩
    have hm : f m ≤ n + 2 := le_trans (le_ciSup hbdd m) H
    dsimp [f, m] at hm
    omega
  have hd : 7 ∣ n - 1 := by
    apply Nat.dvd_iff_mod_eq_zero.mpr
    omega
  rcases hd with ⟨b, hb⟩
  have hbgt : 7 < b := by omega
  have hge : 4 ≤ ArithmeticFunction.sigma 0 (n - 1) := by
    rw [ArithmeticFunction.sigma_zero_apply]
    have hsub : ({1, 7, b, n - 1} : Finset ℕ) ⊆ (n - 1).divisors := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [Nat.mem_divisors]
      constructor
      · rcases hx with rfl | rfl | rfl | rfl
        · exact one_dvd (n - 1)
        · use b
        · use 7
          omega
        · exact dvd_rfl
      · omega
    have hba : b ≠ n - 1 := by omega
    have h7b : 7 ≠ b := by omega
    have h1b : 1 ≠ b := by omega
    have h1a : 1 ≠ n - 1 := by omega
    have h7a : 7 ≠ n - 1 := by omega
    have hcard : ({1, 7, b, n - 1} : Finset ℕ).card = 4 := by
      simp [hba, h7b, h1b, h1a, h7a]
    calc
      4 = ({1, 7, b, n - 1} : Finset ℕ).card := hcard.symm
      _ ≤ (n - 1).divisors.card := Finset.card_le_card hsub
  exact Nat.not_succ_le_self 3 (le_trans hge shift)

theorem candidate_not_mod_seven_two : ∀ n : ℕ, 54 < n → (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 → 30 ∣ n → n % 7 = 2 → False := by
  intro n hn H h30 h2
  have shift : ArithmeticFunction.sigma 0 (n - 2) ≤ 4 := by
    have hsub : n - 2 < n := by omega
    let f : Fin n → ℕ := fun x => (x : ℕ) + ArithmeticFunction.sigma 0 x
    have hbdd : BddAbove (Set.range f) := by
      refine ⟨2 * n, ?_⟩
      rintro y ⟨x, rfl⟩
      dsimp [f]
      rw [ArithmeticFunction.sigma_zero_apply]
      have hc := Nat.card_divisors_le_self (x : ℕ)
      have hx : (x : ℕ) < n := x.isLt
      omega
    let m : Fin n := ⟨n - 2, hsub⟩
    have hm : f m ≤ n + 2 := le_trans (le_ciSup hbdd m) H
    dsimp [f, m] at hm
    omega
  rcases h30 with ⟨q, hq⟩
  have hd : 14 ∣ n - 2 := by
    apply Nat.dvd_iff_mod_eq_zero.mpr
    omega
  rcases hd with ⟨b, hb⟩
  have hge : 5 ≤ ArithmeticFunction.sigma 0 (n - 2) := by
    rw [ArithmeticFunction.sigma_zero_apply]
    have hsub : ({1, 2, 7, 14, n - 2} : Finset ℕ) ⊆ (n - 2).divisors := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [Nat.mem_divisors]
      constructor
      · rcases hx with rfl | rfl | rfl | rfl | rfl
        · exact one_dvd (n - 2)
        · use 7 * b
          omega
        · use 2 * b
          omega
        · use b
        · exact dvd_rfl
      · omega
    have h1a : 1 ≠ n - 2 := by omega
    have h2a : 2 ≠ n - 2 := by omega
    have h7a : 7 ≠ n - 2 := by omega
    have h14a : 14 ≠ n - 2 := by omega
    have hcard : ({1, 2, 7, 14, n - 2} : Finset ℕ).card = 5 := by
      simp [h1a, h2a, h7a, h14a]
    calc
      5 = ({1, 2, 7, 14, n - 2} : Finset ℕ).card := hcard.symm
      _ ≤ (n - 2).divisors.card := Finset.card_le_card hsub
  exact Nat.not_succ_le_self 4 (le_trans hge shift)

theorem candidate_not_mod_seven_three : ∀ n : ℕ, 54 < n → (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 → 30 ∣ n → n % 7 = 3 → False := by
  intro n hn H h30 h3
  have shift : ArithmeticFunction.sigma 0 (n - 3) ≤ 5 := by
    have hsub : n - 3 < n := by omega
    let f : Fin n → ℕ := fun x => (x : ℕ) + ArithmeticFunction.sigma 0 x
    have hbdd : BddAbove (Set.range f) := by
      refine ⟨2 * n, ?_⟩
      rintro y ⟨x, rfl⟩
      dsimp [f]
      rw [ArithmeticFunction.sigma_zero_apply]
      have hc := Nat.card_divisors_le_self (x : ℕ)
      have hx : (x : ℕ) < n := x.isLt
      omega
    let m : Fin n := ⟨n - 3, hsub⟩
    have hm : f m ≤ n + 2 := le_trans (le_ciSup hbdd m) H
    dsimp [f, m] at hm
    omega
  rcases h30 with ⟨q, hq⟩
  have hd : 21 ∣ n - 3 := by
    apply Nat.dvd_iff_mod_eq_zero.mpr
    omega
  rcases hd with ⟨b, hb⟩
  have hbgt : 2 < b := by omega
  by_cases hb7 : b = 7
  · have hn150 : n = 150 := by omega
    have hge : 6 ≤ ArithmeticFunction.sigma 0 (n - 3) := by
      rw [hn150, ArithmeticFunction.sigma_zero_apply]
      have hsub : ({1, 3, 7, 21, 49, 147} : Finset ℕ) ⊆ (147 : ℕ).divisors := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rw [Nat.mem_divisors]
        constructor
        · rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
        · norm_num
      have hcard : ({1, 3, 7, 21, 49, 147} : Finset ℕ).card = 6 := by norm_num
      calc
        6 = ({1, 3, 7, 21, 49, 147} : Finset ℕ).card := hcard.symm
        _ ≤ (147 : ℕ).divisors.card := Finset.card_le_card hsub
    exact Nat.not_succ_le_self 5 (le_trans hge shift)
  · have hb3 : b ≠ 3 := by
      intro hh
      omega
    have hb21 : b ≠ 21 := by
      intro hh
      omega
    have hge : 6 ≤ ArithmeticFunction.sigma 0 (n - 3) := by
      rw [ArithmeticFunction.sigma_zero_apply]
      have hsub : ({1, 3, 7, 21, b, n - 3} : Finset ℕ) ⊆ (n - 3).divisors := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rw [Nat.mem_divisors]
        constructor
        · rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
          · exact one_dvd (n - 3)
          · use 7 * b
            omega
          · use 3 * b
            omega
          · use b
          · use 21
            omega
          · exact dvd_rfl
        · omega
      have h1b : 1 ≠ b := by omega
      have h3b : 3 ≠ b := Ne.symm hb3
      have h7b : 7 ≠ b := Ne.symm hb7
      have h21b : 21 ≠ b := Ne.symm hb21
      have h1a : 1 ≠ n - 3 := by omega
      have h3a : 3 ≠ n - 3 := by omega
      have h7a : 7 ≠ n - 3 := by omega
      have h21a : 21 ≠ n - 3 := by omega
      have hba : b ≠ n - 3 := by omega
      have hcard : ({1, 3, 7, 21, b, n - 3} : Finset ℕ).card = 6 := by
        simp [h1b, h3b, h7b, h21b, h1a, h3a, h7a, h21a, hba]
      calc
        6 = ({1, 3, 7, 21, b, n - 3} : Finset ℕ).card := hcard.symm
        _ ≤ (n - 3).divisors.card := Finset.card_le_card hsub
    exact Nat.not_succ_le_self 5 (le_trans hge shift)

theorem candidate_not_mod_seven_four : ∀ n : ℕ, 54 < n → (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 → 30 ∣ n → n % 7 = 4 → False := by
  intro n hn H h30 h4
  have shift : ArithmeticFunction.sigma 0 (n - 4) ≤ 6 := by
    have hsub : n - 4 < n := by omega
    let f : Fin n → ℕ := fun x => (x : ℕ) + ArithmeticFunction.sigma 0 x
    have hbdd : BddAbove (Set.range f) := by
      refine ⟨2 * n, ?_⟩
      rintro y ⟨x, rfl⟩
      dsimp [f]
      rw [ArithmeticFunction.sigma_zero_apply]
      have hc := Nat.card_divisors_le_self (x : ℕ)
      have hx : (x : ℕ) < n := x.isLt
      omega
    let m : Fin n := ⟨n - 4, hsub⟩
    have hm : f m ≤ n + 2 := le_trans (le_ciSup hbdd m) H
    dsimp [f, m] at hm
    omega
  rcases h30 with ⟨q, hq⟩
  have hd : 14 ∣ n - 4 := by
    apply Nat.dvd_iff_mod_eq_zero.mpr
    omega
  rcases hd with ⟨b, hb⟩
  have hbgt : 3 < b := by omega
  have hb7 : b ≠ 7 := by
    intro hh
    omega
  have hb14 : b ≠ 14 := by
    intro hh
    omega
  have hge : 7 ≤ ArithmeticFunction.sigma 0 (n - 4) := by
    rw [ArithmeticFunction.sigma_zero_apply]
    have hsub : ({1, 2, 7, 14, b, 2 * b, n - 4} : Finset ℕ) ⊆ (n - 4).divisors := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [Nat.mem_divisors]
      constructor
      · rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact one_dvd (n - 4)
        · use 7 * b
          omega
        · use 2 * b
          omega
        · use b
        · use 14
          omega
        · use 7
          omega
        · exact dvd_rfl
      · omega
    have h1b : 1 ≠ b := by omega
    have h2b : 2 ≠ b := by omega
    have h7b : 7 ≠ b := Ne.symm hb7
    have h14b : 14 ≠ b := Ne.symm hb14
    have h1d : 1 ≠ 2 * b := by omega
    have h2d : 2 ≠ 2 * b := by omega
    have h7d : 7 ≠ 2 * b := by omega
    have h14d : 14 ≠ 2 * b := by
      intro hh
      apply hb7
      omega
    have hbd : b ≠ 2 * b := by omega
    have h1a : 1 ≠ n - 4 := by omega
    have h2a : 2 ≠ n - 4 := by omega
    have h7a : 7 ≠ n - 4 := by omega
    have h14a : 14 ≠ n - 4 := by omega
    have hba : b ≠ n - 4 := by omega
    have hda : 2 * b ≠ n - 4 := by omega
    have hcard : ({1, 2, 7, 14, b, 2 * b, n - 4} : Finset ℕ).card = 7 := by
      simp [h1b, h2b, h7b, h14b, h1d, h2d, h7d, h14d, hbd,
        h1a, h2a, h7a, h14a, hba, hda]
    calc
      7 = ({1, 2, 7, 14, b, 2 * b, n - 4} : Finset ℕ).card := hcard.symm
      _ ≤ (n - 4).divisors.card := Finset.card_le_card hsub
  exact Nat.not_succ_le_self 6 (le_trans hge shift)

theorem candidate_not_mod_seven_five : ∀ n : ℕ, 54 < n → (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 → 30 ∣ n → n % 7 = 5 → False := by
  intro n hn H h30 h5
  have shift : ∀ k : ℕ, 0 < k → k < n →
      ArithmeticFunction.sigma 0 (n - k) ≤ k + 2 := by
    intro k hk hkn
    have hsub : n - k < n := by omega
    let f : Fin n → ℕ := fun x => (x : ℕ) + ArithmeticFunction.sigma 0 x
    have hbdd : BddAbove (Set.range f) := by
      refine ⟨2 * n, ?_⟩
      rintro y ⟨x, rfl⟩
      dsimp [f]
      rw [ArithmeticFunction.sigma_zero_apply]
      have hc := Nat.card_divisors_le_self (x : ℕ)
      have hx : (x : ℕ) < n := x.isLt
      omega
    let m : Fin n := ⟨n - k, hsub⟩
    have hm : f m ≤ n + 2 := le_trans (le_ciSup hbdd m) H
    dsimp [f, m] at hm
    omega
  rcases h30 with ⟨q, hq⟩
  have hd : 35 ∣ n - 5 := by
    apply Nat.dvd_iff_mod_eq_zero.mpr
    omega
  rcases hd with ⟨b, hb⟩
  have hbge : 5 ≤ b := by omega
  by_cases hb5 : b = 5
  · have hn180 : n = 180 := by omega
    have hge : 7 ≤ ArithmeticFunction.sigma 0 (n - 4) := by
      rw [hn180, ArithmeticFunction.sigma_zero_apply]
      have hsub : ({1, 2, 4, 8, 11, 16, 176} : Finset ℕ) ⊆ (176 : ℕ).divisors := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rw [Nat.mem_divisors]
        constructor
        · rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
        · norm_num
      have hcard : ({1, 2, 4, 8, 11, 16, 176} : Finset ℕ).card = 7 := by norm_num
      calc
        7 = ({1, 2, 4, 8, 11, 16, 176} : Finset ℕ).card := hcard.symm
        _ ≤ (176 : ℕ).divisors.card := Finset.card_le_card hsub
    have hle := shift 4 (by omega) (by omega)
    exact Nat.not_succ_le_self 6 (le_trans hge hle)
  · by_cases hb35 : b = 35
    · have hn1230 : n = 1230 := by omega
      have hge : 8 ≤ ArithmeticFunction.sigma 0 (n - 5) := by
        rw [hn1230, ArithmeticFunction.sigma_zero_apply]
        have hsub : ({1, 5, 7, 25, 35, 49, 175, 1225} : Finset ℕ) ⊆ (1225 : ℕ).divisors := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rw [Nat.mem_divisors]
          constructor
          · rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
          · norm_num
        have hcard : ({1, 5, 7, 25, 35, 49, 175, 1225} : Finset ℕ).card = 8 := by norm_num
        calc
          8 = ({1, 5, 7, 25, 35, 49, 175, 1225} : Finset ℕ).card := hcard.symm
          _ ≤ (1225 : ℕ).divisors.card := Finset.card_le_card hsub
      have hle := shift 5 (by omega) (by omega)
      exact Nat.not_succ_le_self 7 (le_trans hge hle)
    · have hb7 : b ≠ 7 := by
        intro hh
        omega
      have hbgt : 5 < b := by omega
      have hge : 8 ≤ ArithmeticFunction.sigma 0 (n - 5) := by
        rw [ArithmeticFunction.sigma_zero_apply]
        have hsub : ({1, 5, 7, 35, b, 5 * b, 7 * b, n - 5} : Finset ℕ) ⊆ (n - 5).divisors := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rw [Nat.mem_divisors]
          constructor
          · rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
            · exact one_dvd (n - 5)
            · use 7 * b
              omega
            · use 5 * b
              omega
            · use b
            · use 35
              omega
            · use 7
              omega
            · use 5
              omega
            · exact dvd_rfl
          · omega
        have h1b : 1 ≠ b := by omega
        have h5b : 5 ≠ b := by omega
        have h7b : 7 ≠ b := Ne.symm hb7
        have h35b : 35 ≠ b := Ne.symm hb35
        have h1c : 1 ≠ 5 * b := by omega
        have h5c : 5 ≠ 5 * b := by omega
        have h7c : 7 ≠ 5 * b := by omega
        have h35c : 35 ≠ 5 * b := by
          intro hh
          apply hb7
          omega
        have h1d : 1 ≠ 7 * b := by omega
        have h5d : 5 ≠ 7 * b := by omega
        have h7d : 7 ≠ 7 * b := by omega
        have h35d : 35 ≠ 7 * b := by
          intro hh
          apply hb5
          omega
        have hbc : b ≠ 5 * b := by omega
        have hbd : b ≠ 7 * b := by omega
        have hcd : 5 * b ≠ 7 * b := by omega
        have h1a : 1 ≠ n - 5 := by omega
        have h5a : 5 ≠ n - 5 := by omega
        have h7a : 7 ≠ n - 5 := by omega
        have h35a : 35 ≠ n - 5 := by omega
        have hba : b ≠ n - 5 := by omega
        have hca : 5 * b ≠ n - 5 := by omega
        have hda : 7 * b ≠ n - 5 := by omega
        have hcard : ({1, 5, 7, 35, b, 5 * b, 7 * b, n - 5} : Finset ℕ).card = 8 := by
          simp [h1b, h5b, h7b, h35b, h1c, h5c, h7c, h35c,
            h1d, h5d, h7d, h35d, hbc, hbd, hcd,
            h1a, h5a, h7a, h35a, hba, hca, hda]
        calc
          8 = ({1, 5, 7, 35, b, 5 * b, 7 * b, n - 5} : Finset ℕ).card := hcard.symm
          _ ≤ (n - 5).divisors.card := Finset.card_le_card hsub
      have hle := shift 5 (by omega) (by omega)
      exact Nat.not_succ_le_self 7 (le_trans hge hle)

theorem candidate_not_mod_seven_six : ∀ n : ℕ, 54 < n → (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 → 30 ∣ n → n % 7 = 6 → False := by
  intro n hn H h30 h6
  have shift : ArithmeticFunction.sigma 0 (n - 6) ≤ 8 := by
    have hsub : n - 6 < n := by omega
    let f : Fin n → ℕ := fun x => (x : ℕ) + ArithmeticFunction.sigma 0 x
    have hbdd : BddAbove (Set.range f) := by
      refine ⟨2 * n, ?_⟩
      rintro y ⟨x, rfl⟩
      dsimp [f]
      rw [ArithmeticFunction.sigma_zero_apply]
      have hc := Nat.card_divisors_le_self (x : ℕ)
      have hx : (x : ℕ) < n := x.isLt
      omega
    let m : Fin n := ⟨n - 6, hsub⟩
    have hm : f m ≤ n + 2 := le_trans (le_ciSup hbdd m) H
    dsimp [f, m] at hm
    omega
  rcases h30 with ⟨q, hq⟩
  have hd : 42 ∣ n - 6 := by
    apply Nat.dvd_iff_mod_eq_zero.mpr
    omega
  rcases hd with ⟨b, hb⟩
  have hge : 9 ≤ ArithmeticFunction.sigma 0 (n - 6) := by
    rw [ArithmeticFunction.sigma_zero_apply]
    have hsub : ({1, 2, 3, 6, 7, 14, 21, 42, n - 6} : Finset ℕ) ⊆ (n - 6).divisors := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [Nat.mem_divisors]
      constructor
      · rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact one_dvd (n - 6)
        · use 21 * b
          omega
        · use 14 * b
          omega
        · use 7 * b
          omega
        · use 6 * b
          omega
        · use 3 * b
          omega
        · use 2 * b
          omega
        · use b
        · exact dvd_rfl
      · omega
    have h1a : 1 ≠ n - 6 := by omega
    have h2a : 2 ≠ n - 6 := by omega
    have h3a : 3 ≠ n - 6 := by omega
    have h6a : 6 ≠ n - 6 := by omega
    have h7a : 7 ≠ n - 6 := by omega
    have h14a : 14 ≠ n - 6 := by omega
    have h21a : 21 ≠ n - 6 := by omega
    have h42a : 42 ≠ n - 6 := by omega
    have hcard : ({1, 2, 3, 6, 7, 14, 21, 42, n - 6} : Finset ℕ).card = 9 := by
      simp [h1a, h2a, h3a, h6a, h7a, h14a, h21a, h42a]
    calc
      9 = ({1, 2, 3, 6, 7, 14, 21, 42, n - 6} : Finset ℕ).card := hcard.symm
      _ ≤ (n - 6).divisors.card := Finset.card_le_card hsub
  exact Nat.not_succ_le_self 8 (le_trans hge shift)

theorem dvd_seven_of_nonzero_residues : ∀ n : ℕ, (n % 7 = 1 → False) → (n % 7 = 2 → False) → (n % 7 = 3 → False) → (n % 7 = 4 → False) → (n % 7 = 5 → False) → (n % 7 = 6 → False) → 7 ∣ n := by
  intro n h1 h2 h3 h4 h5 h6
  have hmod : n % 7 = 0 ∨ n % 7 = 1 ∨ n % 7 = 2 ∨ n % 7 = 3 ∨
      n % 7 = 4 ∨ n % 7 = 5 ∨ n % 7 = 6 := by omega
  rcases hmod with h0 | h1' | h2' | h3' | h4' | h5' | h6'
  · exact Nat.dvd_iff_mod_eq_zero.mpr h0
  · exact False.elim (h1 h1')
  · exact False.elim (h2 h2')
  · exact False.elim (h3 h3')
  · exact False.elim (h4 h4')
  · exact False.elim (h5 h5')
  · exact False.elim (h6 h6')

theorem dvd_2520_of_dvd_thirty_seven_eight_nine : ∀ n : ℕ, 30 ∣ n → 7 ∣ n → 8 ∣ n → 9 ∣ n → 2520 ∣ n := by
  intro n h30 h7 h8 h9
  have h5 : 5 ∣ n := dvd_trans (by norm_num : 5 ∣ 30) h30
  have h72 : 8 * 9 ∣ n :=
    (show Nat.Coprime 8 9 by norm_num).mul_dvd_of_dvd_of_dvd h8 h9
  have h360 : (8 * 9) * 5 ∣ n :=
    (show Nat.Coprime (8 * 9) 5 by norm_num).mul_dvd_of_dvd_of_dvd h72 h5
  have h2520 : ((8 * 9) * 5) * 7 ∣ n :=
    (show Nat.Coprime ((8 * 9) * 5) 7 by norm_num).mul_dvd_of_dvd_of_dvd h360 h7
  norm_num at h2520 ⊢
  exact h2520


theorem candidate_dvd_six :
    ∀ n : ℕ, 24 < n →
      (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 →
      6 ∣ n := by
  intro n hn H
  have h4 : 4 ∣ n := candidate_dvd_four n (by omega) H
  have h3 : 3 ∣ n := candidate_dvd_three_of_four n hn H h4
  have h2 : 2 ∣ n := dvd_trans (by norm_num : 2 ∣ 4) h4
  have h6 : 2 * 3 ∣ n :=
    (show Nat.Coprime 2 3 by norm_num).mul_dvd_of_dvd_of_dvd h2 h3
  norm_num at h6 ⊢
  exact h6

theorem candidate_dvd_thirty :
    ∀ n : ℕ, 54 < n →
      (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 →
      30 ∣ n := by
  intro n hn H
  have h6 : 6 ∣ n := candidate_dvd_six n (by omega) H
  have h5 : 5 ∣ n := candidate_dvd_five_of_six n hn H h6
  have h30 : 6 * 5 ∣ n :=
    (show Nat.Coprime 6 5 by norm_num).mul_dvd_of_dvd_of_dvd h6 h5
  norm_num at h30 ⊢
  exact h30

theorem candidate_dvd_seven :
    ∀ n : ℕ, 54 < n →
      (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 →
      30 ∣ n → 7 ∣ n := by
  intro n hn H h30
  exact dvd_seven_of_nonzero_residues n
    (candidate_not_mod_seven_one n hn H)
    (candidate_not_mod_seven_two n hn H h30)
    (candidate_not_mod_seven_three n hn H h30)
    (candidate_not_mod_seven_four n hn H h30)
    (candidate_not_mod_seven_five n hn H h30)
    (candidate_not_mod_seven_six n hn H h30)

theorem candidate_dvd_2520 :
    ∀ n : ℕ, 84 < n →
      (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 →
      2520 ∣ n := by
  intro n hn H
  have h4 : 4 ∣ n := candidate_dvd_four n (by omega) H
  have h6 : 6 ∣ n := candidate_dvd_six n (by omega) H
  have h30 : 30 ∣ n := candidate_dvd_thirty n (by omega) H
  have h7 : 7 ∣ n := candidate_dvd_seven n (by omega) H h30
  have h8 : 8 ∣ n := candidate_dvd_eight_of_four n (by omega) H h4
  have h9 : 9 ∣ n := candidate_dvd_nine_of_six n hn H h6
  exact dvd_2520_of_dvd_thirty_seven_eight_nine n h30 h7 h8 h9

end Erdos647
