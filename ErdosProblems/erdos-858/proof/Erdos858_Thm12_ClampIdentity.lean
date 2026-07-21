/-
Erdős Problem #858 — Theorem 1.2 assembly, clamp identity (Chojecki 2026).

`clamp is the identity on [s,t]`: `max (min t x) s = x` for `x ∈ [s,t]`. Decouples
"the clamp is identity on the target interval" from any membership/grid machinery,
for reuse in the A6-herr clamp-recovery wiring (composing the clamp modulus #149
with the aggregation core #170: on the actual sum range, `u_a` and `v_j` land in
`[s,t]` by construction, so `f∘clamp = f` pointwise there).

Proof: `min_eq_right hxt` turns `min t x` into `x` (since `x≤t`); `max_eq_left hxs`
turns `max x s` into `x` (since `s≤x`).

Kernel-verified via the proofsearch MCP:
  episode 1669a1bd-67e0-4488-a9bc-341820994c7c,
  problem_version_id 7847e984-24a4-48d2-8ecc-ce36dff96f72.
Outcome: kernel_verified / root_kernel_verified (v2 — v1 tried `max_eq_right`, which
expects the pattern `max s x`; after `min_eq_right` the goal is `max x s = x`
(operands swapped), needing `max_eq_left` instead).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash d04e023589fda8ef2022c136730fd13ecf32ce501b4cda3337f2b71888880739.
-/
import Mathlib

namespace Erdos858

/-- Theorem 1.2 clamp identity: `max (min t x) s = x` for `x ∈ [s,t]`, `s≤t`.
`min_eq_right` + `max_eq_left`. -/
theorem erdos858_thm12_clamp_id :
    ∀ (s t x : ℝ), s ≤ t → x ∈ Set.Icc s t → max (min t x) s = x := by
  intro s t x hst hx
  obtain ⟨hxs, hxt⟩ := hx
  rw [min_eq_right hxt, max_eq_left hxs]

end Erdos858
