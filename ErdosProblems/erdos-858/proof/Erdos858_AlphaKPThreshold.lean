/-
Erdős Problem #858 — §5 constant α (Kinlaw–Pomerance threshold) localization.
(Chojecki 2026, "An exact frontier theorem and the asymptotic constant for
Erdős problem #858", §5.)

Byte-faithful reconstruction of the kernel-verified root theorem from the
proofsearch MCP episode 06e7a434-c3dc-474d-900c-0914ca551bdd,
problem_version_id 918ae6d8-1a62-4cea-b73e-e638fa831f1e.
Outcome: kernel_verified / root_kernel_verified.
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash f68b01b4…

The paper sets α := 1/(e+1) = 0.2689414213…, the threshold governing the
low-layer prime bound (§4.3–§4.4: R_N(a) > 1 down to a > N^{1/4}), and notes
α < α₂ = 0.2804… where α₂ is the root of Φ = 1 (Proposition 5.6). This theorem
localizes α strictly inside (1/4, 1/3):
    1/4 < 1/(e+1) < 1/3,
equivalently 2 < e < 3. Companion to the Prop 5.6 core (Erdos858_Prop56_PhiCore),
which places α₂ < 1/3: both α and α₂ lie in (1/4, 1/3), consistent with α < α₂.

Proof: `one_div_lt_one_div_of_lt` in each direction, with e+1 < 4 and 3 < e+1
from the standard bounds e ∈ (2.7182818283, 2.7182818286)
(`Real.exp_one_lt_d9` / `Real.exp_one_gt_d9`); e+1 > 0 by `positivity`.
-/
import Mathlib

namespace Erdos858

/-- The Kinlaw–Pomerance threshold `α := 1/(e+1)` lies strictly in `(1/4, 1/3)`. -/
theorem erdos858_alpha_kp_threshold :
    (1 : ℝ) / 4 < 1 / (Real.exp 1 + 1) ∧ 1 / (Real.exp 1 + 1) < 1 / 3 := by
  have he1pos : 0 < Real.exp 1 + 1 := by positivity
  refine ⟨?_, ?_⟩
  · exact one_div_lt_one_div_of_lt he1pos (by linarith [Real.exp_one_lt_d9])
  · exact one_div_lt_one_div_of_lt (by norm_num) (by linarith [Real.exp_one_gt_d9])

end Erdos858
