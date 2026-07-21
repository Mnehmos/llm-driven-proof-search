/-
Erdős Problem #858 — semiprime uniform Riemann-sum upgrade, atom 4 / FINAL atom
of the "deterministic part" derivation (Chojecki 2026).

**Change of variables**: `∫_a^B g(log t/logN)/(t·log t) dt = ∫_{loga/logN}^{logB/logN}
g(v)/v dv` — via the substitution `t = φ(v) := exp(v·logN)`. Combined with atom
3 (`erdos858_loglog_ibp_ratio_weight`), this shows the Abel identity's
(atom 2, `erdos858_abel_log_ratio_weight_identity`) "deterministic part"
(the `C(t) := Σ_{k≤t}cw(k)` term REPLACED by its known reference `loglog t`)
reduces EXACTLY — no discrete Riemann-sum/mesh discretization, no unknown
constant — to the paper's claimed `I(u) = ∫_u^{u_B} G(v)/v dv` (Lemma 5.3's
value). This closes the hardest, most novel piece of the NEW strategic route
to the campaign's sole remaining research-grade wall for Theorem 1.2 (the
semiprime uniform bound); see the `erdos-858-campaign-state` memory PART 6 for
the complete by-hand derivation and the remaining (lower-risk, assembly-style)
steps: the explicit error bound from the corpus's EXISTING qualitative
Mertens-2 capstone (`|Σ_{p≤x}1/p − loglogx| ≤ [explicit K]`, already
unknown-constant-free — no further "M cancels" step needed anywhere in this
plan), then final assembly + specialization to the paper's actual
`G(u,v) = log((1−u−v)/v)`.

Mirrors `erdos858_prime_transfer_dv_bridge_self_contained`'s (Lemma 5.3's OWN
`#147`/`#148` "geometric change of variables") confirmed-working
`intervalIntegral.integral_comp_mul_deriv''` template (`hcf`/`hderiv`/`hcf'`/
`himg`/`hcg` → `hcov` → endpoint rewrite → `rw[←hcov]` → `integral_congr` →
pointwise `field_simp`), but with a PLAIN EXPONENTIAL substitution
`φ(v):=exp(v·logN)` in place of the template's variable-base `s·(t/s)^x` —
structurally simpler (no base-positivity side conditions anywhere). Since
`a ≥ 2`, `v_a := log a/logN > 0` strictly, so `v > 0` throughout the range —
no `g(v)/v` division-by-zero edge case.

Kernel-verified via the proofsearch MCP:
  episode 2b304e83-85f4-46f3-9ac2-58aac119cb42,
  problem_version_id 1373e4b1-3058-4860-bc89-ca7af9efcdc7.
Outcome: kernel_verified / root_proved (3rd submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash dcfc8a296697e8272f5892351dfc29f02c84e84f4671da52f5cbd45f9192f7fd.

**Lean lessons**: (1) `(Real.hasDerivAt_exp _).comp v (hasDerivAt_mul_const logN)`
initially failed with a metavariable-composition type mismatch (round 1); after
isolating the `1*logN`→`logN` normalization into its own `simpa`-closed `have`
(round 2), a DEEPER issue surfaced — `HasDerivAt.comp` is a GENERIC
normed-space combinator, and composing it with `Real.hasDerivAt_exp` tags the
result with the `NormedAlgebra`-derived `Module`/`AddCommGroup` instance path,
which does not unify (even up to `simp`) against the simpler
`Real.instAddCommGroup`+`Semiring.toModule` path the theorem's own ambient
statement elaborates to — a classic Mathlib instance diamond. **Fix: prefer
the SPECIALIZED `HasDerivAt.exp` corollary over the generic `.comp` whenever
composing with `Real.exp` specifically** — it stays within the concrete
real-instance path and the diamond disappears entirely (round 3, first try
after this fix). (2) the trailing `ring` after a closing `field_simp` hit "no
goals to be solved" in round 1 (field_simp alone already closed it) — dropped.
-/
import Mathlib

namespace Erdos858

/-- Change of variables `t = exp(v·logN)`: `∫_a^B g(logt/logN)/(t·logt)dt =
∫_{loga/logN}^{logB/logN} g(v)/v dv`. Mirrors Lemma 5.3's own geometric
change-of-variables template with a plain exponential substitution. -/
theorem erdos858_ratio_weight_change_of_variables :
    ∀ (g gd : ℝ → ℝ) (logN a B : ℝ), 0 < logN → 2 ≤ a → a ≤ B →
      (∀ v ∈ Set.Icc (Real.log a / logN) (Real.log B / logN), HasDerivAt g (gd v) v) →
      (∫ t in a..B, g (Real.log t / logN) / (t * Real.log t))
        = ∫ v in (Real.log a / logN)..(Real.log B / logN), g v / v := by
  intro g gd logN a B hlogN ha hab hgderiv
  have hapos : (0:ℝ) < a := by linarith
  have hBpos : (0:ℝ) < B := by linarith
  have hva_mul : (Real.log a / logN) * logN = Real.log a := div_mul_cancel₀ (Real.log a) (ne_of_gt hlogN)
  have hvb_mul : (Real.log B / logN) * logN = Real.log B := div_mul_cancel₀ (Real.log B) (ne_of_gt hlogN)
  have hf0 : Real.exp ((Real.log a / logN) * logN) = a := by rw [hva_mul]; exact Real.exp_log hapos
  have hf1 : Real.exp ((Real.log B / logN) * logN) = B := by rw [hvb_mul]; exact Real.exp_log hBpos
  have hab' : Real.log a / logN ≤ Real.log B / logN := by
    have h1 : Real.log a ≤ Real.log B := Real.log_le_log hapos hab
    exact div_le_div_of_nonneg_right h1 hlogN.le
  have hcf : ContinuousOn (fun v : ℝ => Real.exp (v * logN)) (Set.uIcc (Real.log a / logN) (Real.log B / logN)) := (Real.continuous_exp.comp (continuous_id.mul continuous_const)).continuousOn
  have hderiv : ∀ v : ℝ, HasDerivAt (fun w : ℝ => Real.exp (w * logN)) (Real.exp (v * logN) * logN) v := by
    intro v
    have hlin : HasDerivAt (fun x : ℝ => x * logN) logN v := by simpa using (hasDerivAt_id v).mul_const logN
    exact hlin.exp
  have hcf' : ContinuousOn (fun v : ℝ => Real.exp (v * logN) * logN) (Set.uIcc (Real.log a / logN) (Real.log B / logN)) := (Real.continuous_exp.comp (continuous_id.mul continuous_const)).continuousOn.mul continuousOn_const
  have hgcont : ContinuousOn g (Set.Icc (Real.log a / logN) (Real.log B / logN)) := fun v hv => (hgderiv v hv).continuousAt.continuousWithinAt
  have himg : (fun v : ℝ => Real.exp (v * logN)) '' Set.uIcc (Real.log a / logN) (Real.log B / logN) ⊆ Set.Icc a B := by
    rintro w ⟨v, hv, rfl⟩
    rw [Set.uIcc_of_le hab'] at hv
    refine ⟨?_, ?_⟩
    · rw [← hf0]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hv.1 hlogN.le)
    · rw [← hf1]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hv.2 hlogN.le)
  have hsubset : Set.Icc a B ⊆ {t : ℝ | t ≠ 0} := by
    intro t ht
    exact ne_of_gt (by linarith [(Set.mem_Icc.mp ht).1])
  have hlogcont : ContinuousOn (fun t : ℝ => Real.log t / logN) (Set.Icc a B) := ContinuousOn.div_const (Real.continuousOn_log.mono hsubset) logN
  have hmem : ∀ t : ℝ, a ≤ t → t ≤ B → Real.log t / logN ∈ Set.Icc (Real.log a / logN) (Real.log B / logN) := by
    intro t ht1 ht2
    have h1 : Real.log a ≤ Real.log t := Real.log_le_log hapos ht1
    have h2 : Real.log t ≤ Real.log B := Real.log_le_log (by linarith) ht2
    exact ⟨div_le_div_of_nonneg_right h1 hlogN.le, div_le_div_of_nonneg_right h2 hlogN.le⟩
  have hmapsto : Set.MapsTo (fun t : ℝ => Real.log t / logN) (Set.Icc a B) (Set.Icc (Real.log a / logN) (Real.log B / logN)) := fun t ht => hmem t (Set.mem_Icc.mp ht).1 (Set.mem_Icc.mp ht).2
  have hgcomp : ContinuousOn (fun t : ℝ => g (Real.log t / logN)) (Set.Icc a B) := hgcont.comp hlogcont hmapsto
  have hdenomcont : ContinuousOn (fun t : ℝ => t * Real.log t) (Set.Icc a B) := continuousOn_id.mul (Real.continuousOn_log.mono hsubset)
  have hcg : ContinuousOn (fun t : ℝ => g (Real.log t / logN) / (t * Real.log t)) ((fun v : ℝ => Real.exp (v * logN)) '' Set.uIcc (Real.log a / logN) (Real.log B / logN)) := by
    apply ContinuousOn.div
    · exact hgcomp.mono himg
    · exact hdenomcont.mono himg
    · intro t ht
      have ht' : t ∈ Set.Icc a B := himg ht
      have ht1 : a ≤ t := (Set.mem_Icc.mp ht').1
      exact mul_ne_zero (ne_of_gt (by linarith)) (ne_of_gt (Real.log_pos (by linarith)))
  have hcov := intervalIntegral.integral_comp_mul_deriv'' hcf (fun v _ => (hderiv v).hasDerivWithinAt) hcf' hcg
  simp only [Function.comp_apply] at hcov
  rw [hf0, hf1] at hcov
  rw [← hcov]
  apply intervalIntegral.integral_congr
  intro v hv
  dsimp only
  rw [Set.uIcc_of_le hab'] at hv
  have hvapos : (0:ℝ) < Real.log a / logN := div_pos (Real.log_pos (by linarith)) hlogN
  have hvpos : (0:ℝ) < v := lt_of_lt_of_le hvapos hv.1
  have hexppos : (0:ℝ) < Real.exp (v * logN) := Real.exp_pos _
  have hlogexp : Real.log (Real.exp (v * logN)) = v * logN := Real.log_exp _
  have hcancel : (v * logN) / logN = v := mul_div_cancel_right₀ v (ne_of_gt hlogN)
  rw [hlogexp, hcancel]
  have hexpne : Real.exp (v * logN) ≠ 0 := ne_of_gt hexppos
  have hvne : v ≠ 0 := ne_of_gt hvpos
  field_simp

end Erdos858
