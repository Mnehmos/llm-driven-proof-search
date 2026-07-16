import Erdos647_CandidateBridgeAddZ
import Erdos647_CandidateDivisible2520
import Erdos647_CandidateReindex2520
import Erdos647_ShiftOnePrime
import Erdos647_ShiftOutputsRepairedCoprime
import Erdos647_SiftedSumFieldAudit
import campaign.«family2-classifications»

/-!
# Erdős #647 — concrete bounded candidates to sifted survivors

This module performs the candidate-side bookkeeping that was still missing
from the density assembly.  It defines the bounded candidate set, removes the
fixed interval `25 ≤ n ≤ 84`, reindexes every remaining candidate exactly as
`n = 2520 * N`, invokes the seven verified shift classifications, and feeds
the resulting repaired-modulus coprimality into the generic `siftedSum + z`
bridge.
-/

namespace Erdos647

/-- The divisor-count inequality in the statement of Erdős #647. -/
def CandidateBound (n : ℕ) : Prop :=
  (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2

/-- Candidates up to the original variable bound `X`. -/
noncomputable def boundedCandidates (X : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 X).filter fun n => 24 < n ∧ CandidateBound n

/-- The portion to which the `2520`-divisibility reduction applies. -/
noncomputable def largeCandidates (X : ℕ) : Finset ℕ := by
  classical
  exact (boundedCandidates X).filter (84 < ·)

/-- Exact parameter set obtained from `n = 2520 * N`. -/
noncomputable def candidateParameters (X : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 (X / 2520)).filter fun N =>
    84 < 2520 * N ∧ CandidateBound (2520 * N)

/-- At most 60 candidates lie in the fixed interval before the large slice. -/
theorem card_boundedCandidates_le_add_largeCandidates (X : ℕ) :
    (boundedCandidates X).card ≤ 60 + (largeCandidates X).card := by
  classical
  let small := (boundedCandidates X).filter fun n => ¬84 < n
  have hsmall_subset : small ⊆ Finset.Icc 25 84 := by
    intro n hn
    simp only [small, Finset.mem_filter] at hn
    have hcand := (Finset.mem_filter.mp hn.1).2
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hsmall : small.card ≤ 60 := by
    calc
      small.card ≤ (Finset.Icc 25 84).card :=
        Finset.card_le_card hsmall_subset
      _ = 60 := by norm_num [Nat.card_Icc]
  have hpartition :=
    Finset.card_filter_add_card_filter_not
      (s := boundedCandidates X) (fun n => 84 < n)
  rw [← largeCandidates] at hpartition
  change (largeCandidates X).card + small.card =
    (boundedCandidates X).card at hpartition
  omega

/-- Exact cardinality transport from large candidates to the `N` parameter. -/
theorem card_largeCandidates_eq_candidateParameters (X : ℕ) :
    (largeCandidates X).card = (candidateParameters X).card := by
  classical
  have hlarge : largeCandidates X =
      (Finset.Icc 1 X).filter fun n =>
        2520 ∣ n ∧ (84 < n ∧ CandidateBound n) := by
    ext n
    simp only [largeCandidates, boundedCandidates, Finset.mem_filter,
      Finset.mem_Icc]
    constructor
    · rintro ⟨⟨⟨hn1, hnX⟩, hn24, hbound⟩, hn84⟩
      exact ⟨⟨hn1, hnX⟩,
        candidate_dvd_2520 n hn84 hbound, hn84, hbound⟩
    · rintro ⟨⟨hn1, hnX⟩, hdvd, hn84, hbound⟩
      exact ⟨⟨⟨hn1, hnX⟩, by omega, hbound⟩, hn84⟩
  rw [hlarge]
  simpa [candidateParameters] using
    (erdos647_candidate_reindex_2520 X
      (fun n => 84 < n ∧ CandidateBound n))

/-- Every reindexed candidate survives the repaired active-prime modulus
outside the explicitly bounded small-parameter band. -/
theorem candidateParameter_coprime {X z N : ℕ}
    (hN : N ∈ candidateParameters X) (hz : z < 157 * N) :
    Nat.Coprime
      (∏ p ∈ (Finset.range (z + 1)).filter
        (fun p => p.Prime ∧ p ≠ 2 ∧ p ≠ 3 ∧ p ≠ 5 ∧ p ≠ 7), p)
      ((210 * N - 1) * (315 * N - 1) * (420 * N - 1) *
        (630 * N - 1) * (840 * N - 1) * (1260 * N - 1) *
        (2520 * N - 1)) := by
  classical
  simp only [candidateParameters, Finset.mem_filter, Finset.mem_Icc] at hN
  rcases hN with ⟨⟨hN1, hNX⟩, hn84, hbound⟩
  have hdvd : 2520 ∣ 2520 * N := ⟨N, rfl⟩
  have hp12 := erdos647_shift12 (2520 * N) hn84 hbound hdvd
  have hp8 := erdos647_shift8 (2520 * N) hn84 hbound hdvd
  have hp6 := erdos647_shift6 (2520 * N) hn84 hbound hdvd
  have hp4 := erdos647_shift4 (2520 * N) hn84 hbound hdvd
  have hp3 := erdos647_shift3 (2520 * N) hn84 hbound hdvd
  have hp2 := erdos647_shift2 (2520 * N) hn84 hbound hdvd
  have hp1class := erdos647_shift1 (2520 * N) hn84 hbound
  have hp1 := erdos647_shift_one_prime_of_dvd_2520
    (2520 * N) hn84 hdvd hp1class
  exact erdos647_shift_outputs_repaired_coprime
    (2520 * N) N z hN1 rfl hz hp12 hp8 hp6 hp4 hp3 hp2 hp1

/-- The exact large-candidate count is bounded by the concrete sieve survivor
mass, with only the already-certified additive `z` loss. -/
theorem largeCandidates_card_le_siftedSum_add_z
    (s : BoundingSieve) (X z : ℕ)
    (hprod : s.prodPrimes =
      ∏ p ∈ (Finset.range (z + 1)).filter
        (fun p => p.Prime ∧ p ≠ 2 ∧ p ≠ 3 ∧ p ≠ 5 ∧ p ≠ 7), p)
    (hsupport : s.support = (Finset.Icc 1 (X / 2520)).image
      (fun N => (210 * N - 1) * (315 * N - 1) * (420 * N - 1) *
        (630 * N - 1) * (840 * N - 1) * (1260 * N - 1) *
        (2520 * N - 1)))
    (hweights : s.weights = fun _ : ℕ => (1 : ℝ)) :
    ((largeCandidates X).card : ℝ) ≤ s.siftedSum + z := by
  classical
  rw [card_largeCandidates_eq_candidateParameters]
  apply erdos647_candidate_finset_le_siftedSum_add_z
      s (X / 2520) z (candidateParameters X)
  · intro N hN
    exact (Finset.mem_filter.mp hN).1
  · intro N hN hz
    rw [hprod]
    exact candidateParameter_coprime hN hz
  · exact erdos647_siftedSum_field_audit s (X / 2520)
      hsupport hweights

end Erdos647
