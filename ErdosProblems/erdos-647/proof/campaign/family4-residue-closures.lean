import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib

/-!
# Erdős #647 — Family 4: residue closures (frontier 45 → 41)

Full Lean proof source, recovered from the tracked pipeline via
`proof_export{episode_id, format: "lean"}` and the reconstructed episode index
([../../dossiers/episode-index.tsv](../../dossiers/episode-index.tsv)). Each is
kernel-verified in the pinned environment
(`environment_hash 9e26d28e…`).

Three of the four are included here as full bodies (they are the substantial,
mathematically-distinct closures). The fourth, `N ≡ 26884` (modulus
14535 = 3²·5·17·19, an 11-leaf case tree, ~400 lines), is
`problem_version_id fa7e0a1f-446a-4d01-8074-e7f12ff43ece`,
`episode_id 75ae2e6e-3081-4d3c-b977-21c52304131f` — export it with
`proof_export{episode_id: "75ae2e6e-…", format: "lean"}`.

| residue N ≡ (mod 46189) | problem_version_id | episode_id | technique |
|---|---|---|---|
| 39325 | `e8e7b8cd-2383-4225-ba89-f96c4534d903` | `abbba24e-42d0-4771-927c-dcdfbbcccfc9` | direct-full-value, M=2584, k=16 |
| 41470 | `15bdd8f4-d89b-49df-a075-4ac84348d87b` | `a70c3c54-04ae-40fe-b6eb-3e5066bb31c6` | single-overlap, M=3553, k=11, ZMod 8 |
| 40612 | `49ae1aa9-8f21-4c23-8f93-f37b447bba05` | `244e8dd3-dfa3-4550-ad85-6e9f67d17317` | single-overlap, M=4199, k=13 |
| 26884 | `fa7e0a1f-446a-4d01-8074-e7f12ff43ece` | `75ae2e6e-3081-4d3c-b977-21c52304131f` | single-overlap, M=14535, k=45 (see note) |
-/

theorem erdos647_residue_39325 :
    ∀ n N : ℕ, 84 < n → (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 → n = 2520 * N → N % 46189 = 39325 → False := by
  intro n N hn H hnN hres
  have shift : ArithmeticFunction.sigma 0 (n - 16) ≤ 18 := by
    have hsub : n - 16 < n := by omega
    let f : Fin n → ℕ := fun x => (x : ℕ) + ArithmeticFunction.sigma 0 x
    have hbdd : BddAbove (Set.range f) := by
      refine ⟨2 * n, ?_⟩
      rintro y ⟨x, rfl⟩
      dsimp [f]
      rw [ArithmeticFunction.sigma_zero_apply]
      have hc := Nat.card_divisors_le_self (x : ℕ)
      have hx : (x : ℕ) < n := x.isLt
      omega
    let mm : Fin n := ⟨n - 16, hsub⟩
    have hm : f mm ≤ n + 2 := le_trans (le_ciSup hbdd mm) H
    dsimp [f, mm] at hm
    omega
  set q := N / 46189 with hq_def
  have hNeq : N = 46189 * q + 39325 := by omega
  have hn16lin : n = 2584 * 45045 * q + 2584 * 38351 + 16 := by rw [hnN, hNeq]; ring
  have hn16 : n - 16 = 2584 * (45045 * q + 38351) := by
    have : n - 16 = 2584 * 45045 * q + 2584 * 38351 := by omega
    rw [this]; ring
  set eval := 45045 * q + 38351 with heval_def
  have heval2 : eval ≠ 1 := by dsimp [eval]; omega
  have hsig2584 : ArithmeticFunction.sigma 0 2584 = 16 := by native_decide
  obtain ⟨p, hpp, hpdvd⟩ := Nat.exists_prime_and_dvd heval2
  have hn16ne : n - 16 ≠ 0 := by omega
  by_cases hp2584 : p ∣ 2584
  · have hp2584fac : p = 2 ∨ p = 17 ∨ p = 19 := by
      have h2584eq : (2584 : ℕ) = 8 * (17 * 19) := by norm_num
      rw [h2584eq] at hp2584
      rcases (hpp.dvd_mul).mp hp2584 with h8 | h1719
      · left
        have h8pow : (8:ℕ) = 2 ^ 3 := by norm_num
        rw [h8pow] at h8
        have hp2 : p ∣ 2 := hpp.dvd_of_dvd_pow h8
        exact (Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp hp2
      · rcases (hpp.dvd_mul).mp h1719 with h17 | h19
        · right; left
          exact (Nat.prime_dvd_prime_iff_eq hpp (by norm_num)).mp h17
        · right; right
          exact (Nat.prime_dvd_prime_iff_eq hpp (by norm_num)).mp h19
    have h2584p_dvd : 2584 * p ∣ (n - 16) := by
      rw [hn16]; exact Nat.mul_dvd_mul_left 2584 hpdvd
    have hsig_ge : 19 ≤ ArithmeticFunction.sigma 0 (2584 * p) := by
      rcases hp2584fac with rfl | rfl | rfl
      · native_decide
      · native_decide
      · native_decide
    have hsub2 : (2584 * p).divisors ⊆ (n - 16).divisors := by
      intro d hd
      rw [Nat.mem_divisors] at hd ⊢
      exact ⟨hd.1.trans h2584p_dvd, hn16ne⟩
    have hcard_le : ArithmeticFunction.sigma 0 (2584 * p) ≤ ArithmeticFunction.sigma 0 (n - 16) := by
      rw [ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_zero_apply]
      exact Finset.card_le_card hsub2
    omega
  · have hcop : Nat.Coprime 2584 p := ((hpp.coprime_iff_not_dvd).mpr hp2584).symm
    have h2584p_dvd : 2584 * p ∣ (n - 16) := by
      rw [hn16]; exact Nat.mul_dvd_mul_left 2584 hpdvd
    have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
      rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hpp]
    have hsig_mul : ArithmeticFunction.sigma 0 (2584 * p) = ArithmeticFunction.sigma 0 2584 * ArithmeticFunction.sigma 0 p :=
      ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop
    have hsig_ge : 19 ≤ ArithmeticFunction.sigma 0 (2584 * p) := by
      rw [hsig_mul, hsig2584, hsigp]; norm_num
    have hsub2 : (2584 * p).divisors ⊆ (n - 16).divisors := by
      intro d hd
      rw [Nat.mem_divisors] at hd ⊢
      exact ⟨hd.1.trans h2584p_dvd, hn16ne⟩
    have hcard_le : ArithmeticFunction.sigma 0 (2584 * p) ≤ ArithmeticFunction.sigma 0 (n - 16) := by
      rw [ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_zero_apply]
      exact Finset.card_le_card hsub2
    omega

theorem erdos647_residue_41470 :
    ∀ n N : ℕ, 84 < n → (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 → n = 2520 * N → N % 46189 = 41470 → False := by
  intro n N hn H hnN hres
  have shift : ArithmeticFunction.sigma 0 (n - 11) ≤ 13 := by
    have hsub : n - 11 < n := by omega
    let f : Fin n → ℕ := fun x => (x : ℕ) + ArithmeticFunction.sigma 0 x
    have hbdd : BddAbove (Set.range f) := by
      refine ⟨2 * n, ?_⟩
      rintro y ⟨x, rfl⟩
      dsimp [f]
      rw [ArithmeticFunction.sigma_zero_apply]
      have hc := Nat.card_divisors_le_self (x : ℕ)
      have hx : (x : ℕ) < n := x.isLt
      omega
    let mm : Fin n := ⟨n - 11, hsub⟩
    have hm : f mm ≤ n + 2 := le_trans (le_ciSup hbdd mm) H
    dsimp [f, mm] at hm
    omega
  set q := N / 46189 with hq_def
  have hNeq : N = 46189 * q + 41470 := by omega
  have hn11lin : n = 3553 * 32760 * q + 3553 * 29413 + 11 := by rw [hnN, hNeq]; ring
  have hn11 : n - 11 = 3553 * (32760 * q + 29413) := by
    have h1 : n - 11 = 3553 * 32760 * q + 3553 * 29413 := by omega
    rw [h1]; ring
  set eval := 32760 * q + 29413 with heval_def
  have heval2 : 2 ≤ eval := by dsimp [eval]; omega
  have hn11ne : n - 11 ≠ 0 := by omega
  have hmono : ∀ a : ℕ, a ∣ (n - 11) → ArithmeticFunction.sigma 0 a ≤ ArithmeticFunction.sigma 0 (n - 11) := by
    intro a hadvd
    have hsub2 : a.divisors ⊆ (n - 11).divisors := by
      intro d hd
      rw [Nat.mem_divisors] at hd ⊢
      exact ⟨hd.1.trans hadvd, hn11ne⟩
    rw [ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_zero_apply]
    exact Finset.card_le_card hsub2
  have hclose : ∀ D : ℕ, D ∣ eval → 13 < ArithmeticFunction.sigma 0 (3553 * D) → False := by
    intro D hDdvd hsig
    have hDm : 3553 * D ∣ (n - 11) := by rw [hn11]; exact Nat.mul_dvd_mul_left 3553 hDdvd
    have := hmono (3553 * D) hDm
    omega
  have hexists_other : ∀ p : ℕ, Nat.Prime p → p ∣ eval → (∀ s, eval ≠ p ^ s) →
      ∃ p' : ℕ, Nat.Prime p' ∧ p' ∣ eval ∧ p' ≠ p := by
    intro p hp hpdvd hnotpow
    by_contra hnone
    push_neg at hnone
    have heval0 : eval ≠ 0 := by omega
    have hpow := Nat.eq_prime_pow_of_unique_prime_dvd heval0 (fun {r} hq hqd => hnone r hq hqd)
    exact hnotpow _ hpow
  have hnopow : ∀ base : ℕ, Nat.Prime base → ((base:ZMod 8)^2 = 1) →
      (((11 + 3553 * base ^ 0 : ℕ) : ZMod 8) ≠ 0) → (((11 + 3553 * base ^ 1 : ℕ) : ZMod 8) ≠ 0) →
      ∀ s : ℕ, eval ≠ base ^ s := by
    intro base hbp hbsq hb0 hb1 s hs
    have hpoweq : 2520 * N = 11 + 3553 * base ^ s := by
      have heq2 : n - 11 = 3553 * base ^ s := by rw [hn11, hs]
      omega
    have hz : (((2520 * N : ℕ) : ZMod 8)) = (((11 + 3553 * base ^ s : ℕ) : ZMod 8)) := by
      exact_mod_cast congrArg (fun x : ℕ => (x : ZMod 8)) hpoweq
    have hsdecomp : s = 2 * (s / 2) + s % 2 := by omega
    rw [hsdecomp, pow_add, pow_mul] at hz
    push_cast at hz
    rw [hbsq, one_pow, one_mul] at hz
    have h2520zero : (2520 : ZMod 8) = 0 := by native_decide
    rw [h2520zero, zero_mul] at hz
    have hmodlt : s % 2 < 2 := Nat.mod_lt _ (by norm_num)
    interval_cases hh : s % 2
    · exact hb0 (by push_cast; push_cast at hz; simpa using hz.symm)
    · exact hb1 (by push_cast; push_cast at hz; simpa using hz.symm)
  have hnopow11 : ∀ s : ℕ, eval ≠ 11 ^ s := by
    apply hnopow 11 (by norm_num) (by native_decide) (by native_decide) (by native_decide)
  have hnopow17 : ∀ s : ℕ, eval ≠ 17 ^ s := by
    apply hnopow 17 (by norm_num) (by native_decide) (by native_decide) (by native_decide)
  have hnopow19 : ∀ s : ℕ, eval ≠ 19 ^ s := by
    apply hnopow 19 (by norm_num) (by native_decide) (by native_decide) (by native_decide)
  by_cases h11 : 11 ∣ eval
  · by_cases h17 : 17 ∣ eval
    · have h187 : (187:ℕ) ∣ eval := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h11 h17
      exact hclose 187 h187 (by native_decide)
    · by_cases h19 : 19 ∣ eval
      · have h209 : (209:ℕ) ∣ eval := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h11 h19
        exact hclose 209 h209 (by native_decide)
      · obtain ⟨p, hp, hpdvd, hpne⟩ := hexists_other 11 (by norm_num) h11 hnopow11
        have hp11cop : Nat.Coprime 11 p := (Nat.coprime_primes (by norm_num) hp).mpr (Ne.symm hpne)
        have h11p : (11 * p) ∣ eval := hp11cop.mul_dvd_of_dvd_of_dvd h11 hpdvd
        have hcop39083 : Nat.Coprime 39083 p := by
          have h39083fac : (39083:ℕ).primeFactors = {11, 17, 19} := by native_decide
          refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
          intro hpdvd39083
          have hpmem : p ∈ (39083:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvd39083, by norm_num⟩
          rw [h39083fac] at hpmem
          simp at hpmem
          rcases hpmem with rfl | rfl | rfl
          · exact hpne rfl
          · exact h17 hpdvd
          · exact h19 hpdvd
        have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
          rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
        have hs39083 : ArithmeticFunction.sigma 0 39083 = 12 := by native_decide
        have hfinal : 13 < ArithmeticFunction.sigma 0 (3553 * (11 * p)) := by
          have heq : 3553 * (11 * p) = 39083 * p := by ring
          rw [heq, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop39083, hs39083, hsigp]
          norm_num
        exact hclose (11 * p) h11p hfinal
  · by_cases h17 : 17 ∣ eval
    · by_cases h19 : 19 ∣ eval
      · have h323 : (323:ℕ) ∣ eval := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h17 h19
        exact hclose 323 h323 (by native_decide)
      · obtain ⟨p, hp, hpdvd, hpne⟩ := hexists_other 17 (by norm_num) h17 hnopow17
        have hp17cop : Nat.Coprime 17 p := (Nat.coprime_primes (by norm_num) hp).mpr (Ne.symm hpne)
        have h17p : (17 * p) ∣ eval := hp17cop.mul_dvd_of_dvd_of_dvd h17 hpdvd
        have hcop60401 : Nat.Coprime 60401 p := by
          have h60401fac : (60401:ℕ).primeFactors = {11, 17, 19} := by native_decide
          refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
          intro hpdvd60401
          have hpmem : p ∈ (60401:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvd60401, by norm_num⟩
          rw [h60401fac] at hpmem
          simp at hpmem
          rcases hpmem with rfl | rfl | rfl
          · exact h11 hpdvd
          · exact hpne rfl
          · exact h19 hpdvd
        have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
          rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
        have hs60401 : ArithmeticFunction.sigma 0 60401 = 12 := by native_decide
        have hfinal : 13 < ArithmeticFunction.sigma 0 (3553 * (17 * p)) := by
          have heq : 3553 * (17 * p) = 60401 * p := by ring
          rw [heq, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop60401, hs60401, hsigp]
          norm_num
        exact hclose (17 * p) h17p hfinal
    · by_cases h19 : 19 ∣ eval
      · obtain ⟨p, hp, hpdvd, hpne⟩ := hexists_other 19 (by norm_num) h19 hnopow19
        have hp19cop : Nat.Coprime 19 p := (Nat.coprime_primes (by norm_num) hp).mpr (Ne.symm hpne)
        have h19p : (19 * p) ∣ eval := hp19cop.mul_dvd_of_dvd_of_dvd h19 hpdvd
        have hcop67507 : Nat.Coprime 67507 p := by
          have h67507fac : (67507:ℕ).primeFactors = {11, 17, 19} := by native_decide
          refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
          intro hpdvd67507
          have hpmem : p ∈ (67507:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvd67507, by norm_num⟩
          rw [h67507fac] at hpmem
          simp at hpmem
          rcases hpmem with rfl | rfl | rfl
          · exact h11 hpdvd
          · exact h17 hpdvd
          · exact hpne rfl
        have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
          rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
        have hs67507 : ArithmeticFunction.sigma 0 67507 = 12 := by native_decide
        have hfinal : 13 < ArithmeticFunction.sigma 0 (3553 * (19 * p)) := by
          have heq : 3553 * (19 * p) = 67507 * p := by ring
          rw [heq, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop67507, hs67507, hsigp]
          norm_num
        exact hclose (19 * p) h19p hfinal
      · obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (show eval ≠ 1 by omega)
        have hcop3553 : Nat.Coprime 3553 p := by
          have h3553fac : (3553:ℕ).primeFactors = {11, 17, 19} := by native_decide
          refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
          intro hpdvd3553
          have hpmem : p ∈ (3553:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvd3553, by norm_num⟩
          rw [h3553fac] at hpmem
          simp at hpmem
          rcases hpmem with rfl | rfl | rfl
          · exact h11 hpdvd
          · exact h17 hpdvd
          · exact h19 hpdvd
        have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
          rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
        have hs3553 : ArithmeticFunction.sigma 0 3553 = 8 := by native_decide
        have hfinal : 13 < ArithmeticFunction.sigma 0 (3553 * p) := by
          rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop3553, hs3553, hsigp]
          norm_num
        exact hclose p hpdvd hfinal

theorem erdos647_residue_40612 :
    ∀ n N : ℕ, 84 < n → (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 → n = 2520 * N → N % 46189 = 40612 → False := by
  intro n N hn H hnN hres
  have shift : ArithmeticFunction.sigma 0 (n - 13) ≤ 15 := by
    have hsub : n - 13 < n := by omega
    let f : Fin n → ℕ := fun x => (x : ℕ) + ArithmeticFunction.sigma 0 x
    have hbdd : BddAbove (Set.range f) := by
      refine ⟨2 * n, ?_⟩
      rintro y ⟨x, rfl⟩
      dsimp [f]
      rw [ArithmeticFunction.sigma_zero_apply]
      have hc := Nat.card_divisors_le_self (x : ℕ)
      have hx : (x : ℕ) < n := x.isLt
      omega
    let mm : Fin n := ⟨n - 13, hsub⟩
    have hm : f mm ≤ n + 2 := le_trans (le_ciSup hbdd mm) H
    dsimp [f, mm] at hm
    omega
  set q := N / 46189 with hq_def
  have hNeq : N = 46189 * q + 40612 := by omega
  have hn13lin : n = 4199 * 27720 * q + 4199 * 24373 + 13 := by rw [hnN, hNeq]; ring
  have hn13 : n - 13 = 4199 * (27720 * q + 24373) := by
    have h1 : n - 13 = 4199 * 27720 * q + 4199 * 24373 := by omega
    rw [h1]; ring
  set eval := 27720 * q + 24373 with heval_def
  have heval2 : 2 ≤ eval := by dsimp [eval]; omega
  have heval_ge : 24373 ≤ eval := by dsimp [eval]; omega
  have hn13ne : n - 13 ≠ 0 := by omega
  have hmono : ∀ a : ℕ, a ∣ (n - 13) → ArithmeticFunction.sigma 0 a ≤ ArithmeticFunction.sigma 0 (n - 13) := by
    intro a hadvd
    have hsub2 : a.divisors ⊆ (n - 13).divisors := by
      intro d hd
      rw [Nat.mem_divisors] at hd ⊢
      exact ⟨hd.1.trans hadvd, hn13ne⟩
    rw [ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_zero_apply]
    exact Finset.card_le_card hsub2
  have hclose : ∀ D : ℕ, D ∣ eval → 15 < ArithmeticFunction.sigma 0 (4199 * D) → False := by
    intro D hDdvd hsig
    have hDm : 4199 * D ∣ (n - 13) := by rw [hn13]; exact Nat.mul_dvd_mul_left 4199 hDdvd
    have := hmono (4199 * D) hDm
    omega
  have hexists_other : ∀ p : ℕ, Nat.Prime p → p ∣ eval → (∀ s, eval ≠ p ^ s) →
      ∃ p' : ℕ, Nat.Prime p' ∧ p' ∣ eval ∧ p' ≠ p := by
    intro p hp hpdvd hnotpow
    by_contra hnone
    push_neg at hnone
    have heval0 : eval ≠ 0 := by omega
    have hpow := Nat.eq_prime_pow_of_unique_prime_dvd heval0 (fun {r} hq hqd => hnone r hq hqd)
    exact hnotpow _ hpow
  have hnopow : ∀ base : ℕ, Nat.Prime base → ((base:ZMod 8)^2 = 1) →
      (((13 + 4199 * base ^ 0 : ℕ) : ZMod 8) ≠ 0) → (((13 + 4199 * base ^ 1 : ℕ) : ZMod 8) ≠ 0) →
      ∀ s : ℕ, eval ≠ base ^ s := by
    intro base hbp hbsq hb0 hb1 s hs
    have hpoweq : 2520 * N = 13 + 4199 * base ^ s := by
      have heq2 : n - 13 = 4199 * base ^ s := by rw [hn13, hs]
      omega
    have hz : (((2520 * N : ℕ) : ZMod 8)) = (((13 + 4199 * base ^ s : ℕ) : ZMod 8)) := by
      exact_mod_cast congrArg (fun x : ℕ => (x : ZMod 8)) hpoweq
    have hsdecomp : s = 2 * (s / 2) + s % 2 := by omega
    rw [hsdecomp, pow_add, pow_mul] at hz
    push_cast at hz
    rw [hbsq, one_pow, one_mul] at hz
    have h2520zero : (2520 : ZMod 8) = 0 := by native_decide
    rw [h2520zero, zero_mul] at hz
    have hmodlt : s % 2 < 2 := Nat.mod_lt _ (by norm_num)
    interval_cases hh : s % 2
    · exact hb0 (by push_cast; push_cast at hz; simpa using hz.symm)
    · exact hb1 (by push_cast; push_cast at hz; simpa using hz.symm)
  have hnopow13 : ∀ s : ℕ, eval ≠ 13 ^ s := by
    intro s hs
    have heq2 : n - 13 = 13 ^ (s + 1) * 323 := by rw [hn13, hs]; ring
    have hcop323 : Nat.Coprime (13 ^ (s + 1)) 323 := by
      have h13_323 : Nat.Coprime 13 323 := by norm_num
      exact h13_323.pow_left (s + 1)
    have hsigeq : ArithmeticFunction.sigma 0 (n - 13) = (s + 2) * ArithmeticFunction.sigma 0 323 := by
      rw [heq2, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop323,
        ArithmeticFunction.sigma_zero_apply_prime_pow (by norm_num : Nat.Prime 13)]
    have hsig323 : ArithmeticFunction.sigma 0 323 = 4 := by native_decide
    rw [hsig323] at hsigeq
    have hsle : (s + 2) * 4 ≤ 15 := by rw [← hsigeq]; exact shift
    have hsbound : s ≤ 1 := by omega
    interval_cases s
    · norm_num at hs; omega
    · norm_num at hs; omega
  have hnopow17 : ∀ s : ℕ, eval ≠ 17 ^ s := by
    apply hnopow 17 (by norm_num) (by native_decide) (by native_decide) (by native_decide)
  have hnopow19 : ∀ s : ℕ, eval ≠ 19 ^ s := by
    apply hnopow 19 (by norm_num) (by native_decide) (by native_decide) (by native_decide)
  by_cases h13 : 13 ∣ eval
  · by_cases h17 : 17 ∣ eval
    · have h221 : (221:ℕ) ∣ eval := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h13 h17
      exact hclose 221 h221 (by native_decide)
    · by_cases h19 : 19 ∣ eval
      · have h247 : (247:ℕ) ∣ eval := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h13 h19
        exact hclose 247 h247 (by native_decide)
      · obtain ⟨p, hp, hpdvd, hpne⟩ := hexists_other 13 (by norm_num) h13 hnopow13
        have hp13cop : Nat.Coprime 13 p := (Nat.coprime_primes (by norm_num) hp).mpr (Ne.symm hpne)
        have h13p : (13 * p) ∣ eval := hp13cop.mul_dvd_of_dvd_of_dvd h13 hpdvd
        have hcop54587 : Nat.Coprime 54587 p := by
          have h54587fac : (54587:ℕ).primeFactors = {13, 17, 19} := by native_decide
          refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
          intro hpdvd54587
          have hpmem : p ∈ (54587:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvd54587, by norm_num⟩
          rw [h54587fac] at hpmem
          simp at hpmem
          rcases hpmem with rfl | rfl | rfl
          · exact hpne rfl
          · exact h17 hpdvd
          · exact h19 hpdvd
        have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
          rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
        have hs54587 : ArithmeticFunction.sigma 0 54587 = 12 := by native_decide
        have hfinal : 15 < ArithmeticFunction.sigma 0 (4199 * (13 * p)) := by
          have heq : 4199 * (13 * p) = 54587 * p := by ring
          rw [heq, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop54587, hs54587, hsigp]
          norm_num
        exact hclose (13 * p) h13p hfinal
  · by_cases h17 : 17 ∣ eval
    · by_cases h19 : 19 ∣ eval
      · have h323 : (323:ℕ) ∣ eval := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h17 h19
        exact hclose 323 h323 (by native_decide)
      · obtain ⟨p, hp, hpdvd, hpne⟩ := hexists_other 17 (by norm_num) h17 hnopow17
        have hp17cop : Nat.Coprime 17 p := (Nat.coprime_primes (by norm_num) hp).mpr (Ne.symm hpne)
        have h17p : (17 * p) ∣ eval := hp17cop.mul_dvd_of_dvd_of_dvd h17 hpdvd
        have hcop71383 : Nat.Coprime 71383 p := by
          have h71383fac : (71383:ℕ).primeFactors = {13, 17, 19} := by native_decide
          refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
          intro hpdvd71383
          have hpmem : p ∈ (71383:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvd71383, by norm_num⟩
          rw [h71383fac] at hpmem
          simp at hpmem
          rcases hpmem with rfl | rfl | rfl
          · exact h13 hpdvd
          · exact hpne rfl
          · exact h19 hpdvd
        have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
          rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
        have hs71383 : ArithmeticFunction.sigma 0 71383 = 12 := by native_decide
        have hfinal : 15 < ArithmeticFunction.sigma 0 (4199 * (17 * p)) := by
          have heq : 4199 * (17 * p) = 71383 * p := by ring
          rw [heq, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop71383, hs71383, hsigp]
          norm_num
        exact hclose (17 * p) h17p hfinal
    · by_cases h19 : 19 ∣ eval
      · obtain ⟨p, hp, hpdvd, hpne⟩ := hexists_other 19 (by norm_num) h19 hnopow19
        have hp19cop : Nat.Coprime 19 p := (Nat.coprime_primes (by norm_num) hp).mpr (Ne.symm hpne)
        have h19p : (19 * p) ∣ eval := hp19cop.mul_dvd_of_dvd_of_dvd h19 hpdvd
        have hcop79781 : Nat.Coprime 79781 p := by
          have h79781fac : (79781:ℕ).primeFactors = {13, 17, 19} := by native_decide
          refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
          intro hpdvd79781
          have hpmem : p ∈ (79781:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvd79781, by norm_num⟩
          rw [h79781fac] at hpmem
          simp at hpmem
          rcases hpmem with rfl | rfl | rfl
          · exact h13 hpdvd
          · exact h17 hpdvd
          · exact hpne rfl
        have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
          rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
        have hs79781 : ArithmeticFunction.sigma 0 79781 = 12 := by native_decide
        have hfinal : 15 < ArithmeticFunction.sigma 0 (4199 * (19 * p)) := by
          have heq : 4199 * (19 * p) = 79781 * p := by ring
          rw [heq, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop79781, hs79781, hsigp]
          norm_num
        exact hclose (19 * p) h19p hfinal
      · obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (show eval ≠ 1 by omega)
        have hcop4199 : Nat.Coprime 4199 p := by
          have h4199fac : (4199:ℕ).primeFactors = {13, 17, 19} := by native_decide
          refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
          intro hpdvd4199
          have hpmem : p ∈ (4199:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvd4199, by norm_num⟩
          rw [h4199fac] at hpmem
          simp at hpmem
          rcases hpmem with rfl | rfl | rfl
          · exact h13 hpdvd
          · exact h17 hpdvd
          · exact h19 hpdvd
        have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
          rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
        have hs4199 : ArithmeticFunction.sigma 0 4199 = 8 := by native_decide
        have hfinal : 15 < ArithmeticFunction.sigma 0 (4199 * p) := by
          rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop4199, hs4199, hsigp]
          norm_num
        exact hclose p hpdvd hfinal
