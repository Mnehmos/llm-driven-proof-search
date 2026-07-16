import Erdos647_CandidateStructuralReduction
import Erdos647_Shift9Refined
import campaign.«family2-classifications»

/-!
# Erdős #647 — the exact shift-9/shift-10 frontier

This source-checked assembly sharpens shift 10, tags the two Hughes
prime-chain families by the parity of the `2520` parameter, and combines those
facts with the previously verified refined shift-9 theorem.

The four new residue/parity lemmas were independently checked by the pinned
proof-search verifier (`kernel_pass` jobs `7b41ecb5-e33d-41a5-a65d-3b82228c58cf`,
`21486d9c-5362-42c3-9874-de7ff8c5f14e`,
`f139e7c5-1c06-408a-8f42-478e4028333c`, and
`7cd52d14-886a-4923-a76d-8e6062aab8e1`).  The final theorem is an assembly of
those lemmas with the already checked campaign modules imported above.

This frontier is deliberately not presented as a contradiction: the exact
consistency witness in `Erdos647_Shift10FrontierWitness.lean` survives every
budget through shift 10 while satisfying all seven prime forms.
-/

/-- A prime shift-10 cofactor excludes the unique residue where it is
divisible by five. -/
theorem erdos647_shift10_prime_residue :
    ∀ N : ℕ, 1 ≤ N → Nat.Prime (252 * N - 1) →
      N % 5 = 0 ∨ N % 5 = 1 ∨ N % 5 = 2 ∨ N % 5 = 4 := by
  intro N hN hr
  have hmodlt : N % 5 < 5 := Nat.mod_lt N (by norm_num)
  by_cases h0 : N % 5 = 0
  · exact Or.inl h0
  by_cases h1 : N % 5 = 1
  · exact Or.inr <| Or.inl h1
  by_cases h2 : N % 5 = 2
  · exact Or.inr <| Or.inr <| Or.inl h2
  by_cases h4 : N % 5 = 4
  · exact Or.inr <| Or.inr <| Or.inr h4
  have h3 : N % 5 = 3 := by omega
  have hdecomp := Nat.mod_add_div N 5
  have hNform : N = 5 * (N / 5) + 3 := by omega
  have hdiv : 5 ∣ 252 * N - 1 := by
    refine ⟨252 * (N / 5) + 151, ?_⟩
    conv_lhs => rw [hNform]
    omega
  have hor := Nat.Prime.eq_one_or_self_of_dvd hr 5 hdiv
  omega

/-- In the `5 * prime` shift-10 branch, primality excludes one of the five
possible lifts modulo 25. -/
theorem erdos647_shift10_five_prime_residue :
    ∀ N p : ℕ, 1 ≤ N → Nat.Prime p → 252 * N - 1 = 5 * p →
      N % 25 = 3 ∨ N % 25 = 8 ∨ N % 25 = 18 ∨ N % 25 = 23 := by
  intro N p hN hp heq
  have hpne5 : p ≠ 5 := by
    intro hp5
    rw [hp5] at heq
    omega
  have h5np : ¬ 5 ∣ p := by
    intro h5p
    have h5prime : Nat.Prime 5 := by norm_num
    have h := (Nat.prime_dvd_prime_iff_eq h5prime hp).mp h5p
    exact hpne5 h.symm
  have hpmod : p % 5 ≠ 0 := by
    intro hzero
    exact h5np (Nat.dvd_of_mod_eq_zero hzero)
  have hNmodlt : N % 25 < 25 := Nat.mod_lt N (by norm_num)
  have hpmodlt : p % 5 < 5 := Nat.mod_lt p (by norm_num)
  have hNdecomp := Nat.mod_add_div N 25
  have hpdecomp := Nat.mod_add_div p 5
  omega

/-- Family A forces the `2520`-parameter to be even. -/
theorem erdos647_familyA_parameter_even :
    ∀ N s : ℕ, 1 ≤ N → Nat.Prime s →
      2520 * N = 8 * s + 8 → N % 2 = 0 := by
  intro N s hN hs heq
  by_cases h0 : N % 2 = 0
  · exact h0
  have hmodlt : N % 2 < 2 := Nat.mod_lt N (by norm_num)
  have h1 : N % 2 = 1 := by omega
  have hNdecomp := Nat.mod_add_div N 2
  rcases hs.eq_two_or_odd' with htwo | hodd
  · rw [htwo] at heq
    omega
  · obtain ⟨r, hr⟩ := hodd
    omega

/-- Family B forces the `2520`-parameter to be odd. -/
theorem erdos647_familyB_parameter_odd :
    ∀ N s : ℕ, 1 ≤ N →
      2520 * N = 16 * s + 8 → N % 2 = 1 := by
  intro N s hN heq
  have hmodlt : N % 2 < 2 := Nat.mod_lt N (by norm_num)
  have hNdecomp := Nat.mod_add_div N 2
  omega

/-- The square branch in the shift-10 classification is impossible, and the
two surviving branches carry their exact residue restrictions. -/
theorem erdos647_shift10_refined :
    ∀ n N : ℕ, 84 < n →
      (⨆ m : Fin n,
        (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 →
      n = 2520 * N →
      (Nat.Prime (252 * N - 1) ∧
        (N % 5 = 0 ∨ N % 5 = 1 ∨ N % 5 = 2 ∨ N % 5 = 4)) ∨
      (∃ p : ℕ, Nat.Prime p ∧ 252 * N - 1 = 5 * p ∧
        (N % 25 = 3 ∨ N % 25 = 8 ∨ N % 25 = 18 ∨ N % 25 = 23)) := by
  intro n N hn H hnN
  have hN : 1 ≤ N := by omega
  have hdvd : 2520 ∣ n := ⟨N, hnN⟩
  have hclass := erdos647_shift10 n hn H hdvd
  have hval : (n - 10) / 10 = 252 * N - 1 := by omega
  rw [hval] at hclass
  rcases hclass with hp | hsquare | hfive
  · exact Or.inl ⟨hp, erdos647_shift10_prime_residue N hN hp⟩
  · obtain ⟨p, hp, heq⟩ := hsquare
    exact (erdos647_no_square_of_four_dvd 252 N p
      (by norm_num) hN (by norm_num) heq).elim
  · obtain ⟨p, hp, heq⟩ := hfive
    exact Or.inr ⟨p, hp, heq,
      erdos647_shift10_five_prime_residue N p hN hp heq⟩

namespace Erdos647

/-- Every hypothetical large candidate simultaneously lies in one of the two
prime-chain families and in the fully refined shift-9 and shift-10 frontiers.
This is a twelve-branch frontier (2 families × 3 shift-9 branches × 2
shift-10 branches), not a contradiction. -/
theorem candidate_shift9_shift10_frontier :
    ∀ n N : ℕ, 84 < n →
      (⨆ m : Fin n,
        (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 →
      n = 2520 * N →
      (∃ s : ℕ, s.Prime ∧
        ((N % 2 = 0 ∧ n = 8 * s + 8 ∧
            (2 * s + 1).Prime ∧
            (4 * s + 3).Prime ∧
            (8 * s + 7).Prime) ∨
          (N % 2 = 1 ∧ n = 16 * s + 8 ∧
            (4 * s + 1).Prime ∧
            (8 * s + 3).Prime ∧
            (16 * s + 7).Prime))) ∧
      ((Nat.Prime (280 * N - 1) ∧
          (N % 3 = 0 ∨ N % 3 = 2)) ∨
        (∃ p : ℕ, Nat.Prime p ∧ 280 * N - 1 = 3 * p ∧
          (N % 9 = 4 ∨ N % 9 = 7)) ∨
        (∃ p : ℕ, Nat.Prime p ∧ 280 * N - 1 = 9 * p ∧
          (N % 27 = 1 ∨ N % 27 = 10))) ∧
      ((Nat.Prime (252 * N - 1) ∧
          (N % 5 = 0 ∨ N % 5 = 1 ∨ N % 5 = 2 ∨ N % 5 = 4)) ∨
        (∃ p : ℕ, Nat.Prime p ∧ 252 * N - 1 = 5 * p ∧
          (N % 25 = 3 ∨ N % 25 = 8 ∨ N % 25 = 18 ∨ N % 25 = 23))) := by
  intro n N hn H hnN
  have hN : 1 ≤ N := by omega
  obtain ⟨s, hs, hA | hB⟩ := candidate_primechain_families n hn H
  · exact ⟨⟨s, hs, Or.inl ⟨
        erdos647_familyA_parameter_even N s hN hs (by omega), hA⟩⟩,
      erdos647_shift9_refined n N hn H hnN,
      erdos647_shift10_refined n N hn H hnN⟩
  · exact ⟨⟨s, hs, Or.inr ⟨
        erdos647_familyB_parameter_odd N s hN (by omega), hB⟩⟩,
      erdos647_shift9_refined n N hn H hnN,
      erdos647_shift10_refined n N hn H hnN⟩

end Erdos647
