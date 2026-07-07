-- Calibration-audit proof (stage 1): the EXACT module the verifier checked,
-- as exported from the tracked ledger (proof_export format=lean, episode
-- 2a9bb264-7eb8-431f-8852-952a3e880fb4). Statement = erdos_1.variants.weaker
-- from google-deepmind/formal-conjectures (IsSumDistinctSet inlined), hash
-- 6d9502df287501ce86c7c99563413736cec446695e5787cb87136dd2c065fcf0.
-- Independently written (C = 1/4, calc-style counting); the corpus's own
-- proof on file (C = 1/3) also compiles in this toolchain — audit verdict
-- MATCH. See ../reasoning/01-calibration-audit.md.
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
noncomputable section

namespace ChatDB.P_4d9792569b684ebd

theorem erdos_1_variants_weaker : ∃ C > (0 : ℝ), ∀ (N : ℕ) (A : Finset ℕ),
    (A ⊆ Finset.Icc 1 N ∧ (fun (⟨S, _⟩ : A.powerset) => S.sum id).Injective) →
    N ≠ 0 → C * 2 ^ A.card / A.card < N := by
  refine ⟨1/4, by norm_num, ?_⟩
  intro N A hSD hN
  obtain ⟨hsub, hinj⟩ := hSD
  have hNpos : 0 < N := Nat.pos_of_ne_zero hN
  have hcount : 2 ^ A.card ≤ A.card * N + 1 := by
    classical
    have hmaps : ∀ S ∈ A.powerset, S.sum id ∈ Finset.range (A.card * N + 1) := by
      intro S hS
      rw [Finset.mem_range, Nat.lt_succ_iff]
      have hSsub : S ⊆ A := Finset.mem_powerset.mp hS
      calc S.sum id ≤ S.card * N := by
            have hle : ∀ i ∈ S, id i ≤ N := fun i hi =>
              (Finset.mem_Icc.mp (hsub (hSsub hi))).2
            simpa [smul_eq_mul] using Finset.sum_le_card_nsmul S id N hle
        _ ≤ A.card * N := Nat.mul_le_mul_right N (Finset.card_le_card hSsub)
    have hinjOn : Set.InjOn (fun S : Finset ℕ => S.sum id) ↑A.powerset := by
      intro a ha b hb hab
      have h : (⟨a, Finset.mem_coe.mp ha⟩ : A.powerset) = ⟨b, Finset.mem_coe.mp hb⟩ :=
        hinj hab
      exact congrArg Subtype.val h
    calc 2 ^ A.card = A.powerset.card := (Finset.card_powerset A).symm
      _ ≤ (Finset.range (A.card * N + 1)).card :=
          Finset.card_le_card_of_injOn _ hmaps hinjOn
      _ = A.card * N + 1 := Finset.card_range _
  rcases Nat.eq_zero_or_pos A.card with hc | hc
  · rw [hc]
    simp only [Nat.cast_zero, div_zero]
    exact_mod_cast hNpos
  · have h2 : (2 : ℝ) ^ A.card ≤ A.card * N + 1 := by exact_mod_cast hcount
    have hn1 : (1 : ℝ) ≤ A.card := by exact_mod_cast hc
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hNpos
    rw [div_lt_iff₀ (by exact_mod_cast hc : (0 : ℝ) < (A.card : ℝ))]
    nlinarith [h2, hn1, hN1]

end ChatDB.P_4d9792569b684ebd
end
