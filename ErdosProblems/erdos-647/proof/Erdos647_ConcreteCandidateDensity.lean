import Erdos647_ConcretePromotedSieve
import Erdos647_DirectCandidateDensityAssembly

/-!
# Erdős #647 — concrete candidate two-parameter density interface

This module is the exact junction between the completed candidate wiring and
the verified analytic package.  It adds back the at most 60 candidates in the
fixed interval and exposes the analytic hypotheses in precisely the form
already supplied by the truncated Selberg machinery.
-/

namespace Erdos647

/-- Once the promoted concrete sieve has its verified truncated main term,
half-denominator, and polynomial error bounds, the full bounded candidate set
obeys the explicit two-parameter inequality. -/
theorem boundedCandidates_density_from_promoted
    (t : SelbergSieve) (X z R : ℕ) (w : ℕ → ℝ) (L LR : ℝ)
    (hmass : t.totalMass = ((X / 2520 : ℕ) : ℝ))
    (hcard : ((largeCandidates X).card : ℝ) ≤ t.siftedSum + z)
    (hw1 : w 1 = 1)
    (hmain : t.mainSum (BoundingSieve.lambdaSquared w) = 1 / LR)
    (hL : 0 < L) (hhalf : L / 2 ≤ LR)
    (herr : t.errSum (BoundingSieve.lambdaSquared w) ≤
      (((R * R + 1 : ℕ) : ℝ) ^ 8)) :
    ((boundedCandidates X).card : ℝ) ≤
      60 + 2 * ((X / 2520 : ℕ) : ℝ) / L +
        (((R * R + 1 : ℕ) : ℝ) ^ 8) + z := by
  have hlarge := erdos647_direct_candidate_density_assembly
    t (largeCandidates X) w (X / 2520) z R L LR
    hmass hcard hw1 hmain hL hhalf herr
  have hsplitNat := card_boundedCandidates_le_add_largeCandidates X
  have hsplit : ((boundedCandidates X).card : ℝ) ≤
      60 + (largeCandidates X).card := by
    exact_mod_cast hsplitNat
  linarith

/-- A concrete promoted sieve exists for every positive `R`, and its verified
analytic fields imply the full bounded-candidate inequality with no remaining
candidate-side assumptions. -/
theorem exists_concrete_candidate_density_interface
    (X z R : ℕ) (hR : 1 ≤ R) :
    ∃ t : SelbergSieve,
      t.level = R ∧
      t.totalMass = ((X / 2520 : ℕ) : ℝ) ∧
      ((largeCandidates X).card : ℝ) ≤ t.siftedSum + z ∧
      ∀ (w : ℕ → ℝ) (L LR : ℝ),
        w 1 = 1 →
        t.mainSum (BoundingSieve.lambdaSquared w) = 1 / LR →
        0 < L → L / 2 ≤ LR →
        t.errSum (BoundingSieve.lambdaSquared w) ≤
          (((R * R + 1 : ℕ) : ℝ) ^ 8) →
        ((boundedCandidates X).card : ℝ) ≤
          60 + 2 * ((X / 2520 : ℕ) : ℝ) / L +
            (((R * R + 1 : ℕ) : ℝ) ^ 8) + z := by
  obtain ⟨t, hsupport, hprod, hweights, hmass, hnu, hlevel, hcard⟩ :=
    exists_promoted_sieve_for_candidates X z R hR
  refine ⟨t, hlevel, hmass, hcard, ?_⟩
  intro w L LR hw1 hmain hL hhalf herr
  exact boundedCandidates_density_from_promoted
    t X z R w L LR hmass hcard hw1 hmain hL hhalf herr

end Erdos647
