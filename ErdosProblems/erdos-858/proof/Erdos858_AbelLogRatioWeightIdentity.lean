/-
Erdős Problem #858 — semiprime uniform Riemann-sum upgrade, atom 2 (Chojecki 2026).

**GENERIC Abel-summation identity for weight `f(t) := g(log t / logN)`**, for
ARBITRARY smooth `g` (not fixed to `1/log t` as `erdos858_abel_log_inverse_identity`
specialized it) — the structural core of a NEW strategic route to the campaign's
sole remaining research-grade wall for Theorem 1.2 (Lemma 5.3's semiprime block
`Q_N(a) → I(u)`, upgraded to hold UNIFORMLY in `u`).

**Why this route, instead of re-deriving Lemma 5.3's mesh/diagonal-squeeze
Riemann-sum discretization tree (`hW`/`hR`/`herr`, ~10 atoms) in explicit-rate
form**: Abel-summing the semiprime integrand `g` DIRECTLY against the prime-
reciprocal partial sums via Mathlib's `sum_mul_eq_sub_sub_integral_mul`
(confirmed GENERIC in the weight, not hardcoded) reuses the ALREADY-uniform
prime block-mass bound (this session's `erdos858_uniform_prime_block_mass_bound`
/ `erdos858_literal_uniform_prime_mertens`) directly, bypassing the mesh/K-grid
construction entirely. The unknown Meissel–Mertens constant `M` is expected to
cancel via the FTC (`∫_a^x f' = f(x) − f(a)` exactly) applied to the CONSTANT
part of `C(t) = Σ_{p≤t}1/p = loglog t + M + E(t)` — the SAME cancellation
mechanism used for the prime-only Mertens-1 chain this session, just verified
(by hand, not yet formalized) to also work when `C(t)` appears inside the Abel
integral, not just at two endpoints. **NEXT ATOM**: formalize that FTC-based
M-cancellation algebra, generically, before specializing to the paper's
semiprime `G`.

Structure mirrors `erdos858_abel_log_inverse_identity` (hderiv/hf_diff/hde/
hderiv_eq/hsubne/hgcont/hf_int/habel chain) with `f` generalized via the
chain-rule fact `erdos858_log_ratio_chain_rule` (atom 1, inlined — problem_versions
can't cross-reference), plus two new pieces: `hmem` (the image-interval
membership `log a/logN ≤ log t/logN ≤ log x/logN`, needed since `gd`'s
continuity/derivative hypotheses are only given on the image, not globally) and
`hgdcomp` (continuity of `gd∘(log ·/logN)` via `ContinuousOn.comp` + `hmem` as
a `Set.MapsTo`).

Kernel-verified via the proofsearch MCP:
  episode e1efcb31-c0c9-48d7-87ac-af09dd100e74,
  problem_version_id 842da4b1-0c4a-4fb0-8786-79538b9cd514.
Outcome: kernel_verified / root_proved (2nd submission — round 1 failed only on
the closing pointwise `rw` step: the goal inside `setIntegral_congr_fun`'s
obligation was left as an UN-BETA-REDUCED `(fun x => ...) t` application, so
`deriv (fun u=>g(logu/logN)) t` didn't appear syntactically for `rw` to match;
fixed with a `dsimp only` immediately before the `rw` to beta-reduce first —
everything else, including the large continuity/differentiability/integrability
chain, kernel_verified on the first attempt).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 39c59943c5ea1fd241a053430bea01483609557d0a0c9b295aab69c1c47a8bdc.
-/
import Mathlib

namespace Erdos858

/-- Generic Abel-summation identity, weight `f(t) := g(log t/logN)` for
arbitrary smooth `g` (derivative `gd` given, continuous, on the image
interval): `Σ_{k∈(⌊a⌋,⌊x⌋]} g(logk/logN)·cw(k) = g(logx/logN)·C(x) −
g(loga/logN)·C(a) − ∫ gd(logt/logN)·(t⁻¹/logN)·C(t) dt`, `C(y)=Σ_{k≤⌊y⌋}cw(k)`.
Built on Mathlib's `sum_mul_eq_sub_sub_integral_mul`. -/
theorem erdos858_abel_log_ratio_weight_identity :
    ∀ (cw : ℕ → ℝ) (g gd : ℝ → ℝ) (logN a x : ℝ),
      0 < logN → 0 < a → a ≤ x →
      (∀ v ∈ Set.Icc (Real.log a / logN) (Real.log x / logN), HasDerivAt g (gd v) v) →
      ContinuousOn gd (Set.Icc (Real.log a / logN) (Real.log x / logN)) →
      ∑ k ∈ Finset.Ioc ⌊a⌋₊ ⌊x⌋₊, g (Real.log (k:ℝ) / logN) * cw k
        = g (Real.log x / logN) * (∑ k ∈ Finset.Icc 0 ⌊x⌋₊, cw k)
          - g (Real.log a / logN) * (∑ k ∈ Finset.Icc 0 ⌊a⌋₊, cw k)
          - ∫ t in Set.Ioc a x, (gd (Real.log t / logN) * ((t:ℝ)⁻¹ / logN)) * (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, cw k) := by
  intro cw g gd logN a x hlogN ha hax hgderiv hgdcont
  have hmem : ∀ t : ℝ, a ≤ t → t ≤ x → Real.log t / logN ∈ Set.Icc (Real.log a / logN) (Real.log x / logN) := by
    intro t ht1 ht2
    have h1 : Real.log a ≤ Real.log t := Real.log_le_log ha ht1
    have h2 : Real.log t ≤ Real.log x := Real.log_le_log (lt_of_lt_of_le ha ht1) ht2
    exact ⟨div_le_div_of_nonneg_right h1 hlogN.le, div_le_div_of_nonneg_right h2 hlogN.le⟩
  have htpos : ∀ t : ℝ, a ≤ t → 0 < t := fun t ht1 => lt_of_lt_of_le ha ht1
  have hderiv : ∀ t ∈ Set.Icc a x, HasDerivAt (fun u : ℝ => g (Real.log u / logN)) (gd (Real.log t / logN) * ((t:ℝ)⁻¹ / logN)) t := by
    intro t ht
    have hf : HasDerivAt (fun u : ℝ => Real.log u / logN) ((t:ℝ)⁻¹ / logN) t := (Real.hasDerivAt_log (ne_of_gt (htpos t ht.1))).div_const logN
    exact (hgderiv (Real.log t / logN) (hmem t ht.1 ht.2)).comp t hf
  have hf_diff : ∀ t ∈ Set.Icc a x, DifferentiableAt ℝ (fun u : ℝ => g (Real.log u / logN)) t := fun t ht => (hderiv t ht).differentiableAt
  have hde : ∀ t ∈ Set.Icc a x, deriv (fun u : ℝ => g (Real.log u / logN)) t = gd (Real.log t / logN) * ((t:ℝ)⁻¹ / logN) := fun t ht => (hderiv t ht).deriv
  have hderiv_eq : Set.EqOn (fun t : ℝ => gd (Real.log t / logN) * ((t:ℝ)⁻¹ / logN)) (deriv (fun u : ℝ => g (Real.log u / logN))) (Set.Icc a x) := fun t ht => (hde t ht).symm
  have hsubne : ∀ t ∈ Set.Icc a x, t ∈ ({0}ᶜ : Set ℝ) := by
    intro t ht
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact ne_of_gt (htpos t ht.1)
  have hlogcont : ContinuousOn (fun t : ℝ => Real.log t / logN) (Set.Icc a x) := ContinuousOn.div_const (Real.continuousOn_log.mono hsubne) logN
  have hmapsto : Set.MapsTo (fun t : ℝ => Real.log t / logN) (Set.Icc a x) (Set.Icc (Real.log a / logN) (Real.log x / logN)) := fun t ht => hmem t ht.1 ht.2
  have hgdcomp : ContinuousOn (fun t : ℝ => gd (Real.log t / logN)) (Set.Icc a x) := hgdcont.comp hlogcont hmapsto
  have htinv : ContinuousOn (fun t : ℝ => (t:ℝ)⁻¹ / logN) (Set.Icc a x) := ContinuousOn.div_const (ContinuousOn.inv₀ continuousOn_id (fun t ht => ne_of_gt (htpos t ht.1))) logN
  have hgcont : ContinuousOn (fun t : ℝ => gd (Real.log t / logN) * ((t:ℝ)⁻¹ / logN)) (Set.Icc a x) := hgdcomp.mul htinv
  have hf_int : MeasureTheory.IntegrableOn (deriv (fun u : ℝ => g (Real.log u / logN))) (Set.Icc a x) MeasureTheory.volume := MeasureTheory.IntegrableOn.congr_fun hgcont.integrableOn_Icc hderiv_eq measurableSet_Icc
  have habel := sum_mul_eq_sub_sub_integral_mul cw ha.le hax hf_diff hf_int
  have hint : (∫ t in Set.Ioc a x, deriv (fun u : ℝ => g (Real.log u / logN)) t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, cw k) = ∫ t in Set.Ioc a x, gd (Real.log t / logN) * ((t:ℝ)⁻¹ / logN) * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, cw k := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    dsimp only
    rw [hde t (Set.mem_Icc.mpr ⟨le_of_lt ht.1, ht.2⟩)]
  rw [hint] at habel
  exact habel

end Erdos858
