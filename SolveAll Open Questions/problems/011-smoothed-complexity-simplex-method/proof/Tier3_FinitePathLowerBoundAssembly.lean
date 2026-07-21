/-
SolveAll #11 — finite charged simplex path to Bach--Huiberts lower bound.

This assembly removes the earlier infinite-chain artifact.  A concrete
`NormalizedSimplexPath a k` contains exactly `k` charged one-basis exchanges;
its natural-index view supplies the bounded basis-cardinality and adjacency
hypotheses of the deterministic Bach--Huiberts capstone.
-/
import Tier3_NormalizedLPBasis
import Tier3_BachHuibertsRoundness

namespace SolveAll011.Tier3

/-- Any finite charged normalized simplex path satisfying the local polar-face
and endpoint estimates has at least the Bach--Huiberts number of pivots. -/
theorem normalizedSimplexPath_bachHuiberts_length_lower
    {ι E : Type} [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (a : ι → E) {k : ℕ} (p : NormalizedSimplexPath a k)
    (zPlus zMinus : E) (R γ : ℝ)
    (hd : 2 ≤ Module.finrank ℝ E) (hR : 0 < R) (hγ : 0 < γ)
    (hfaceDiam : ∀ t ≤ k, ∀ i, i ∈ p.indicesAt t →
      ∀ j, j ∈ p.indicesAt t → ‖a i - a j‖ ≤ γ)
    (hstart : ∀ i ∈ p.indicesAt 0, ‖zPlus - a i‖ ≤ γ)
    (hfinish : ∀ i ∈ p.indicesAt k, ‖a i - zMinus‖ ≤ γ)
    (hfar : 2 / R ≤ ‖zPlus - zMinus‖) :
    (((Module.finrank ℝ E - 1 : ℕ) : ℝ) *
      (2 / (R * γ) - 3) ≤ (k : ℝ)) := by
  apply bachHuiberts_basis_path_length_lower_bounded
    a p.indicesAt (Module.finrank ℝ E) k zPlus zMinus R γ hd hR hγ
  · exact p.indicesAt_card
  · exact p.indicesAt_inter_card
  · exact hfaceDiam
  · exact hstart
  · exact hfinish
  · exact hfar

#print axioms normalizedSimplexPath_bachHuiberts_length_lower

end SolveAll011.Tier3
