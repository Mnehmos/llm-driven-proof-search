/-
Erdős Problem #858 — semiprime uniform Riemann-sum upgrade, atom 3 (Chojecki 2026).

Integration by parts in `t` (`u(t) := log(log t)`, `v(t) := g(log t/logN)`),
converting the semiprime Abel identity's `loglog`-weighted integral term into
the DETERMINISTIC form `∫ g(log t/logN)/(t·log t) dt` — the form a SINGLE
change-of-variables (`v := log t/logN`, next atom) turns into exactly the
paper's `∫ g(v)/v dv`, with NO discrete Riemann-sum/mesh discretization and NO
Meissel–Mertens-constant cancellation trick needed (the corpus's existing
qualitative Mertens-2 bound is already unknown-constant-free — see the
`erdos-858-campaign-state` memory PART 6 for the complete by-hand derivation
this atom is step 2 of).

Built on Mathlib's `intervalIntegral.integral_mul_deriv_eq_deriv_mul`
(`∫u·v' = u(b)v(b) − u(a)v(a) − ∫u'·v`), with `u := loglog` (derivative
`1/(t·log t)`, constructed exactly as `erdos858_mertens2_main_integral`'s
antiderivative) and `v := g(log·/logN)` (derivative via this plan's atom 1's
chain rule, inlined — problem_versions can't cross-reference).

Kernel-verified via the proofsearch MCP:
  episode dd03cebc-942d-41cb-b771-ff84f6372b46,
  problem_version_id 76aaa021-bdf9-4f4d-bc23-ae4d6bd1a6be.
Outcome: kernel_verified / root_proved (4th submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 7aa2606317f32024fc9b64ef73be11014e943bcaa5178c3d693891d1859f7e59.

**Lean lesson (rounds 1-3 all failed on the SAME symptom before this was
correctly diagnosed)**: `apply ContinuousOn.div continuousOn_const (continuousOn_id.mul
(...))` — supplying the first two of `ContinuousOn.div`'s three arguments
INLINE to `apply`, leaving only the third (nonvanishing) as a goal — produces
a THIRD goal whose printed form contains a spurious, unreducible-looking
`id t` that `linarith`/`simp only [id_eq]` cannot connect back to hypotheses
stated with a bare `t` (rounds 1-2 misdiagnosed this as an inline-lambda
`.mono`-argument issue; round 3's `simp only [id_eq]` then failed with "made
no progress", disproving that theory too). The actual fix: match ONE of the
two structures already confirmed to work elsewhere in this codebase exactly —
either `apply ContinuousOn.div` with NO inline arguments, filled by three
separate `·` bullets (as `erdos858_mertens2_main_integral`'s `hcont` does), or
a fully inline PURE TERM with no `apply` at all (as this session's
`erdos858_abel_log_ratio_weight_identity`'s `htinv` does). Do not mix
`apply f a b` (partial inline args) with a residual tactic goal for
`ContinuousOn.div` specifically — it elaborates the residual goal's shape
differently than either confirmed-safe style.
-/
import Mathlib

namespace Erdos858

/-- Integration by parts in `t`: `∫ log(log t)·[gd(logt/logN)·(t⁻¹/logN)] dt =
log(logB)·g(logB/logN) − log(loga)·g(loga/logN) − ∫ [1/(t·logt)]·g(logt/logN) dt`.
`u := loglog` (deriv `1/(t logt)`), `v := g(log·/logN)` (deriv via the chain
rule), via `intervalIntegral.integral_mul_deriv_eq_deriv_mul`. -/
theorem erdos858_loglog_ibp_ratio_weight :
    ∀ (g gd : ℝ → ℝ) (logN a B : ℝ), 0 < logN → 2 ≤ a → a ≤ B →
      (∀ v ∈ Set.Icc (Real.log a / logN) (Real.log B / logN), HasDerivAt g (gd v) v) →
      ContinuousOn gd (Set.Icc (Real.log a / logN) (Real.log B / logN)) →
      (∫ t in a..B, Real.log (Real.log t) * (gd (Real.log t / logN) * ((t:ℝ)⁻¹ / logN)))
        = Real.log (Real.log B) * g (Real.log B / logN) - Real.log (Real.log a) * g (Real.log a / logN)
          - ∫ t in a..B, (1 / (t * Real.log t)) * g (Real.log t / logN) := by
  intro g gd logN a B hlogN ha hab hgderiv hgdcont
  have hmem : ∀ t : ℝ, a ≤ t → t ≤ B → Real.log t / logN ∈ Set.Icc (Real.log a / logN) (Real.log B / logN) := by
    intro t ht1 ht2
    have h1 : Real.log a ≤ Real.log t := Real.log_le_log (by linarith) ht1
    have h2 : Real.log t ≤ Real.log B := Real.log_le_log (by linarith) ht2
    exact ⟨div_le_div_of_nonneg_right h1 hlogN.le, div_le_div_of_nonneg_right h2 hlogN.le⟩
  have hu : ∀ t ∈ Set.uIcc a B, HasDerivAt (fun s => Real.log (Real.log s)) (1 / (t * Real.log t)) t := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    have ht2 : a ≤ t := (Set.mem_Icc.mp ht).1
    have htpos : (0:ℝ) < t := by linarith
    have htne : t ≠ 0 := ne_of_gt htpos
    have hlogtpos : 0 < Real.log t := Real.log_pos (by linarith)
    have hlogtne : Real.log t ≠ 0 := ne_of_gt hlogtpos
    have hlog : HasDerivAt Real.log t⁻¹ t := Real.hasDerivAt_log htne
    have hloglog : HasDerivAt (fun s => Real.log (Real.log s)) ((Real.log t)⁻¹ * t⁻¹) t := (Real.hasDerivAt_log hlogtne).comp t hlog
    have hval : (Real.log t)⁻¹ * t⁻¹ = 1 / (t * Real.log t) := by rw [one_div, mul_inv]; ring
    rw [hval] at hloglog
    exact hloglog
  have hv : ∀ t ∈ Set.uIcc a B, HasDerivAt (fun s => g (Real.log s / logN)) (gd (Real.log t / logN) * ((t:ℝ)⁻¹ / logN)) t := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    have ht2 : a ≤ t := (Set.mem_Icc.mp ht).1
    have htpos : (0:ℝ) < t := by linarith
    have hf : HasDerivAt (fun u : ℝ => Real.log u / logN) ((t:ℝ)⁻¹ / logN) t := (Real.hasDerivAt_log (ne_of_gt htpos)).div_const logN
    exact (hgderiv (Real.log t / logN) (hmem t ht2 (Set.mem_Icc.mp ht).2)).comp t hf
  have hsubset : Set.Icc a B ⊆ {t : ℝ | t ≠ 0} := by
    intro t ht
    have h1 : a ≤ t := (Set.mem_Icc.mp ht).1
    exact ne_of_gt (by linarith)
  have hucont : ContinuousOn (fun t => 1 / (t * Real.log t)) (Set.uIcc a B) := by
    rw [Set.uIcc_of_le hab]
    apply ContinuousOn.div
    · exact continuousOn_const
    · exact continuousOn_id.mul (Real.continuousOn_log.mono hsubset)
    · intro t ht
      have ht2 : a ≤ t := (Set.mem_Icc.mp ht).1
      have htne : t ≠ 0 := ne_of_gt (by linarith)
      have hlogtne : Real.log t ≠ 0 := ne_of_gt (Real.log_pos (by linarith))
      exact mul_ne_zero htne hlogtne
  have hu' : IntervalIntegrable (fun t => 1 / (t * Real.log t)) MeasureTheory.volume a B := hucont.intervalIntegrable
  have hlogcont : ContinuousOn (fun t : ℝ => Real.log t / logN) (Set.Icc a B) := ContinuousOn.div_const (Real.continuousOn_log.mono hsubset) logN
  have hvcont : ContinuousOn (fun t => gd (Real.log t / logN) * ((t:ℝ)⁻¹ / logN)) (Set.uIcc a B) := by
    rw [Set.uIcc_of_le hab]
    have hmapsto : Set.MapsTo (fun t : ℝ => Real.log t / logN) (Set.Icc a B) (Set.Icc (Real.log a / logN) (Real.log B / logN)) := fun t ht => hmem t (Set.mem_Icc.mp ht).1 (Set.mem_Icc.mp ht).2
    have hgdcomp : ContinuousOn (fun t : ℝ => gd (Real.log t / logN)) (Set.Icc a B) := hgdcont.comp hlogcont hmapsto
    have htinv : ContinuousOn (fun t : ℝ => (t:ℝ)⁻¹ / logN) (Set.Icc a B) := ContinuousOn.div_const (ContinuousOn.inv₀ continuousOn_id (fun t ht => ne_of_gt (by linarith [(Set.mem_Icc.mp ht).1] : (0:ℝ) < t))) logN
    exact hgdcomp.mul htinv
  have hv' : IntervalIntegrable (fun t => gd (Real.log t / logN) * ((t:ℝ)⁻¹ / logN)) MeasureTheory.volume a B := hvcont.intervalIntegrable
  exact intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv'

end Erdos858
