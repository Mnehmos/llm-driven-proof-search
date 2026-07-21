/-
Erdős Problem #858 — §5.3 dv/v bridge, SELF-CONTAINED (Chojecki 2026).

`self-contained dv/v change-of-variables bridge`: for `G` continuous on `[s,t]`
(`0 < s ≤ t`),

  `∫₀¹ log(t/s)·G(s·(t/s)^x) dx = ∫_s^t G(v)/v dv`

— the paper's exact Lemma 5.3 form, stated with ONLY the natural hypothesis
(`G` continuous on `[s,t]`). Supersedes the conditional #148 by discharging its
three continuity side-conditions internally:
  - `hcf` (the substitution `x ↦ s·(t/s)^x` continuous) and `hcf'` (its derivative
    `x ↦ s·((t/s)^x·log(t/s))` continuous, rewritten to `(s·log(t/s))·(t/s)^x`
    by `ring`) — both from #150 (rpow exponent continuity);
  - the image `(x ↦ s·(t/s)^x) '' [0,1] ⊆ [s,t]` (`himg`, monotone rpow bounds:
    `s = s·1 ≤ s·(t/s)^x ≤ s·(t/s) = t` via `mul_le_mul_of_nonneg_left`);
  - `hcg` (`G(v)/v` continuous on the image) via `ContinuousOn.div (hG.mono himg)
    continuousOn_id` with `v ≥ s > 0`.
Then the change of variables (`intervalIntegral.integral_comp_mul_deriv''` with the
`#147` derivative as `HasDerivWithinAt`), endpoints `f 0 = s`, `f 1 = t`, and the
pointwise cancellation `(G/v)·(v·log(t/s)) = log(t/s)·G` (`field_simp`).

Takes #147 (rpow derivative) and #150 (rpow continuity) as hypotheses.

Kernel-verified via the proofsearch MCP:
  episode 6f78a95d-8c28-402a-863f-066542f3f158,
  problem_version_id d9d36c37-b931-462d-995a-c627052208aa.
Outcome: kernel_verified / root_kernel_verified (3rd submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 63eb446d3f3a8cdcbb8d8678fec32f59eb0c0d76beaa731b87ae08f1153ddb49.

**Lean lessons**: (1) after `rintro v ⟨x, hx, rfl⟩`, the membership goal carries an
unreduced beta redex `(fun x => …) x` — `nlinarith` treats it as opaque; a `show`
(or explicit term bounds) is needed. (2) even beta-reduced, `nlinarith` won't form
the product `s·((t/s)^x − 1) ≥ 0` from the *derived* linear combo `1 ≤ (t/s)^x`
(it multiplies only ORIGINAL hyps) — use explicit `le_trans` +
`mul_le_mul_of_nonneg_left` term bounds instead. (3) keep `himg`'s `by` body
SINGLE-LINE with parenthesized+ascribed inner `by`s — a multi-line nested
`have := by …` mis-scopes.
-/
import Mathlib

namespace Erdos858

/-- §5.3 dv/v bridge, SELF-CONTAINED: for `G` continuous on `[s,t]`,
`∫₀¹ log(t/s)·G(s·(t/s)^x)dx = ∫_s^t G(v)/v dv` — Lemma 5.3's value with only the
natural hypothesis. Discharges #148's three continuity conditions from #150 + the
monotone image bound. -/
theorem erdos858_prime_transfer_dv_bridge_self_contained :
    ∀ (G : ℝ → ℝ) (s t : ℝ), 0 < s → s ≤ t → ContinuousOn G (Set.Icc s t) →
      (∀ (s' c : ℝ), 0 < c → ∀ x : ℝ, HasDerivAt (fun y : ℝ => s' * c ^ y) (s' * (c ^ x * Real.log c)) x) →
      (∀ (s' c : ℝ), 0 < c → Continuous (fun x : ℝ => s' * c ^ x)) →
      (∫ x in (0:ℝ)..1, Real.log (t/s) * G (s * (t/s) ^ x)) = ∫ v in s..t, G v / v := by
  intro G s t hs hst hG h147 h150
  have hbase : (0:ℝ) < t/s := div_pos (by linarith) hs
  have hts : (1:ℝ) ≤ t/s := (one_le_div hs).mpr hst
  have hst2 : s * (t/s) = t := by field_simp
  have hcf : ContinuousOn (fun x : ℝ => s * (t/s) ^ x) (Set.uIcc 0 1) := (h150 s (t/s) hbase).continuousOn
  have hcf'eq : (fun x : ℝ => s * ((t/s) ^ x * Real.log (t/s))) = (fun x : ℝ => (s * Real.log (t/s)) * (t/s) ^ x) := by funext x; ring
  have hcf' : ContinuousOn (fun x : ℝ => s * ((t/s) ^ x * Real.log (t/s))) (Set.uIcc 0 1) := by rw [hcf'eq]; exact (h150 (s * Real.log (t/s)) (t/s) hbase).continuousOn
  have himg : (fun x : ℝ => s * (t/s) ^ x) '' Set.uIcc 0 1 ⊆ Set.Icc s t := by rintro v ⟨x, hx, rfl⟩; rw [Set.uIcc_of_le zero_le_one] at hx; exact Set.mem_Icc.mpr ⟨le_trans (le_of_eq (mul_one s).symm) (mul_le_mul_of_nonneg_left ((by rw [← Real.rpow_zero (t/s)]; exact Real.rpow_le_rpow_of_exponent_le hts hx.1) : (1:ℝ) ≤ (t/s)^x) hs.le), le_trans (mul_le_mul_of_nonneg_left ((by have h := Real.rpow_le_rpow_of_exponent_le hts hx.2; rwa [Real.rpow_one] at h) : (t/s)^x ≤ t/s) hs.le) (le_of_eq hst2)⟩
  have hcg : ContinuousOn (fun v : ℝ => G v / v) ((fun x : ℝ => s * (t/s) ^ x) '' Set.uIcc 0 1) := ContinuousOn.div (hG.mono himg) continuousOn_id (fun v hv => ne_of_gt (lt_of_lt_of_le hs (Set.mem_Icc.mp (himg hv)).1))
  have hcov := intervalIntegral.integral_comp_mul_deriv'' hcf (fun x _ => (h147 s (t/s) hbase x).hasDerivWithinAt) hcf' hcg
  simp only [Function.comp_apply] at hcov
  have hf0 : s * (t/s) ^ (0:ℝ) = s := by rw [Real.rpow_zero, mul_one]
  have hf1 : s * (t/s) ^ (1:ℝ) = t := by rw [Real.rpow_one]; exact hst2
  rw [hf0, hf1] at hcov
  rw [← hcov]
  apply intervalIntegral.integral_congr
  intro x _
  have hpos : (0:ℝ) < s * (t/s) ^ x := mul_pos hs (Real.rpow_pos_of_pos hbase x)
  have hne : s * (t/s) ^ x ≠ 0 := ne_of_gt hpos
  field_simp

end Erdos858
