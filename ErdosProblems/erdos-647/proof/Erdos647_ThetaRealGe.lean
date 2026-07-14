import Mathlib

/-!
# Erdős #647 — Layer A part 2b: real-valued Chebyshev lower bound

Snapshot of the exact statement + proof term kernel-verified through the
tracked proof-search pipeline on 2026-07-14.

  problem_version_id  e7195e43-dab5-4ee8-85e6-b105d48503b8
  episode_id          c34d5708-40ab-45be-837e-1b5cc54a453a
  root_statement_hash 72cb80ab472e749d02f2ec9507b84f08254d17a1a8d971e0f5ee69028e709531
  outcome             kernel_verified (root_proved)
  import manifest     ["Mathlib.Tactic.Ring", "Mathlib.Tactic.NormNum", "Mathlib"]

Content: bridges Mathlib's `Chebyshev.theta_ge` — which is stated only at
natural-number points `n` (`(n:ℝ)*log2 - log(n+1) - 2√n·log n ≤ θ(n)`) —
to a bound valid for **all real** `t ≥ 2`, the exact form the θ-substitution
in the quantitative-Mertens identity (problem `d584666d`) needs:

  ∀ t ≥ 2, (t−1)·log 2 − log(t+2) − 2√t·log t ≤ θ(t).

Proof: let `n = ⌊t⌋`. `θ` is monotone (`Chebyshev.theta_mono`), so
`θ(n) ≤ θ(t)`; apply `theta_ge` at `n`; then dominate termwise using
`n ≤ t < n+1`: `(t−1)log2 ≤ n·log2`, `log(n+1) ≤ log(t+2)` (so the negated
terms compare the other way), and `√n·log n ≤ √t·log t` by monotonicity of
both factors (`mul_le_mul`). This closes the gap between Mathlib's
integer-indexed effective Chebyshev bound and the real-integral form used
throughout Layer A's error bounds (`erdos647_mertens_error_log`,
`erdos647_mertens_error_sqrt`).
-/

theorem erdos647_theta_real_ge :
    ∀ t : ℝ, 2 ≤ t → (t - 1) * Real.log 2 - Real.log (t + 2) - 2 * Real.sqrt t * Real.log t ≤ Chebyshev.theta t := by
  intro t ht
  set n := ⌊t⌋₊ with hn_def
  have ht0 : (0:ℝ) ≤ t := by linarith
  have hn2 : 2 ≤ n := by
    have h2n : ((2:ℕ):ℝ) ≤ t := by exact_mod_cast ht
    exact_mod_cast Nat.le_floor h2n
  have hnt : (n:ℝ) ≤ t := Nat.floor_le ht0
  have htn1 : t < (n:ℝ) + 1 := Nat.lt_floor_add_one t
  have hthle : Chebyshev.theta (n:ℝ) ≤ Chebyshev.theta t := Chebyshev.theta_mono hnt
  have hnge := Chebyshev.theta_ge n
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hterm1 : (t-1)*Real.log 2 ≤ (n:ℝ)*Real.log 2 := by
    apply mul_le_mul_of_nonneg_right _ (le_of_lt hlog2pos)
    linarith [htn1]
  have hterm2 : -Real.log (t+2) ≤ -Real.log ((n:ℝ)+1) := by
    have hle : Real.log ((n:ℝ)+1) ≤ Real.log (t+2) := Real.log_le_log (by linarith) (by linarith)
    linarith
  have hterm3 : -2*Real.sqrt t*Real.log t ≤ -2*Real.sqrt (n:ℝ)*Real.log (n:ℝ) := by
    have hsqrt_mono : Real.sqrt (n:ℝ) ≤ Real.sqrt t := Real.sqrt_le_sqrt hnt
    have hlog_mono : Real.log (n:ℝ) ≤ Real.log t := Real.log_le_log hnpos hnt
    have hln : 0 ≤ Real.log (n:ℝ) := Real.log_nonneg (by linarith [hn2, hnpos])
    have hsqt : 0 ≤ Real.sqrt t := Real.sqrt_nonneg t
    have hmul : Real.sqrt (n:ℝ) * Real.log (n:ℝ) ≤ Real.sqrt t * Real.log t := mul_le_mul hsqrt_mono hlog_mono hln hsqt
    nlinarith [hmul]
  calc (t-1)*Real.log 2 - Real.log (t+2) - 2*Real.sqrt t*Real.log t
      ≤ (n:ℝ)*Real.log 2 - Real.log ((n:ℝ)+1) - 2*Real.sqrt (n:ℝ)*Real.log (n:ℝ) := by linarith [hterm1, hterm2, hterm3]
    _ ≤ Chebyshev.theta (n:ℝ) := hnge
    _ ≤ Chebyshev.theta t := hthle
