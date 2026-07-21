/-
Erdős Problem #858 — row 5.7 (prime-only ramp), FULL RANGE assembly (Chojecki 2026).

**`S_N(K)` strictly increasing for the WHOLE range `1≤K≤L`** (not just at one
point) — resolves catalog row 5.7 without needing the newly-built uniform
interval Mertens machinery, by realizing that **monotonicity of `P_N`
substitutes for uniformity**: since `P_N` is nonincreasing, checking the
endpoint bound `1+δ≤P_N(L)` at the SINGLE point `a:=L` (where `P_N` is
smallest over the range `[1,L]`) already gives `1+δ≤P_N(a)` for EVERY `a≤L`
simultaneously — no need to bound `P_N` uniformly as `a` ranges, just at the
one worst-case point, which the campaign's existing per-fixed-point interval
Mertens (`erdos858_prime_block_mass_limit`, #129) already supplies asymptotically.

Combines two already-verified pieces: `prop46_PN_monotone`
(`Erdos858_Prop46_PNMonotone.lean`, `P_N` nonincreasing) and
`erdos858_thm12_lemma57_ramp` (`Erdos858_Thm12_A5_Lemma57Ramp.lean`, atom A5,
the per-`a` increment-positivity core) — the latter's exact 4-line proof body
is inlined verbatim (only the final closing step needed adjusting from A5's
own `0<SN a-SN(a-1)` conclusion form to this atom's `SN(a-1)<SN a` form, since
`rw` needs an exact syntactic pattern match and the two forms differ even
though equivalent — fixed by dropping the `rw` and letting `linarith` combine
the equation directly with the derived inequalities).

Produces EXACTLY the "`S_N` strictly increasing on an initial interval" fact
that `erdos858_thm12_kstar_localization`'s own `hinc` hypothesis needs — this
atom is directly reusable for that assembly too, not just row 5.7's own claim.

Kernel-verified via the proofsearch MCP:
  episode 6798182c-e68e-4806-9103-9418560ae9b1,
  problem_version_id d8a6c4ba-19ec-4798-8429-4190f829fbe7.
Outcome: kernel_verified / root_proved (2nd real round — 1st attempted
`rw [hInca]` to rewrite the goal `SN(a-1)<SN a` using the equation
`hInca : SN a - SN(a-1) = CN a - 1/a`, but `rw` needs the LHS pattern
`SN a - SN(a-1)` to appear LITERALLY in the goal, which it doesn't in this
inequality-phrased conclusion; fixed by dropping the `rw` and passing `hInca`
as a `linarith` hint alongside the derived bounds instead — `linarith` closes
an inequality goal directly from an equality hypothesis without needing a
prior rewrite, as long as all the needed atoms appear somewhere in its
hint list).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 5114a3fc2b78182b3ae1efa342a23774de0b038b44166b3f5a3bd025bcacc3a6.
-/
import Mathlib

namespace Erdos858

/-- Row 5.7 full-range ramp: `S_N` strictly increasing on ALL of `[1,L]`,
from `P_N` monotonicity + the endpoint bound `1+δ≤P_N(L)` + the per-`a`
increment/prime-child facts — monotonicity substitutes for uniformity, no
uniform Mertens needed. Also directly usable as K*-localization's `hinc`. -/
theorem erdos858_row57_full_ramp :
    ∀ (SN CN PN : ℕ → ℝ) (L : ℕ) (δ : ℝ), 0 < δ →
      (∀ a b : ℕ, 0 < a → a ≤ b → PN a ≥ PN b) →
      1 + δ ≤ PN L →
      (∀ a : ℕ, 0 < a → PN a / (a:ℝ) ≤ CN a) →
      (∀ a : ℕ, 0 < a → SN a - SN (a-1) = CN a - 1/(a:ℝ)) →
      ∀ a : ℕ, 1 ≤ a → a ≤ L → SN (a-1) < SN a := by
  intro SN CN PN L δ hδ hmono hPNL hCNge hinc a ha1 haL
  have h0 : (0:ℝ) < (a:ℝ) := (by exact_mod_cast ha1)
  have hPNa : 1 + δ ≤ PN a := le_trans hPNL (hmono a L ha1 haL)
  have hCNa := hCNge a ha1
  have hInca := hinc a ha1
  have h1 : (1+δ)/(a:ℝ) ≤ CN a := le_trans (by gcongr) hCNa
  have h2 : 0 < (1+δ)/(a:ℝ) - 1/(a:ℝ) := (by rw [div_sub_div_same]; exact div_pos (by linarith) h0)
  linarith [h1, h2, hInca]

end Erdos858
