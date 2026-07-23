# Proof dossier — Lemma F.2 (prediction-optimal ridge tuning)

**Provenance.** Result: Lemma F.2, Appendix F, pp. 52–54 of *"Optimal Nuisance
Function Tuning for Estimating a Doubly Robust Functional under Proportional
Asymptotics"* by **Sean McGrath** (Yale), **Debarghya Mukherjee** (Boston
University), **Rajarshi Mukherjee** (Harvard), and **Zixiao Jolene Wang**
(Harvard). Formalized as a worked example by Claude (Opus 4.8) via the
proofsearch MCP environment; the lemma and proof are the authors' own. The
source PDF is gitignored and not redistributed.

This dossier is the verbatim `proof_export` (markdown) of the tracked, kernel-
verified episode. Re-verify anytime with the proofsearch `episode_replay` tool.

---

> ⚠️ **KERNEL-VERIFIED FORMAL STATEMENT — FIDELITY NOT YET VERIFIED**

The limiting mean-squared prediction error of the ridge estimator of the nuisance function p, given in Lemma F.1, is minimized (with respect to the ridge parameter λ₁) at λ₁* = c/u², where u = lim‖α₀‖₂ and c is the limiting aspect ratio p/n.

**Proof (the paper's argument).** The limiting risk factors as R(λ) = u² · g(λ), where

    g(λ) = ∫ (λ² + (c/u²) x) / (x + λ)² dF_MP(x)

and F_MP is the Marchenko–Pastur law. Differentiating the integrand,

    d/dλ [ (λ² + (c/u²) x)/(x+λ)² ] = 2 (λ − c/u²) · x/(x+λ)³,

so

    g'(λ) = 2 (λ − c/u²) ∫ x/(x+λ)³ dF_MP(x).

Since ∫ x/(x+λ)³ dF_MP(x) > 0 for every λ ≥ 0, g'(λ) has the sign of (λ − c/u²): it is negative on [0, c/u²) and positive on (c/u², ∞). Hence g, and therefore the risk R = u²·g, is strictly minimized at the unique point λ* = c/u².

**Formalization boundary.** The Marchenko–Pastur integral factor I(λ) = ∫ x/(x+λ)³ dF_MP(x) > 0 and the differentiation-under-the-integral step g'(λ) = 2(λ − c/u²) I(λ) are exactly the facts the paper establishes/uses; they enter as typed hypotheses. We do not formalize the measure-theoretic interchange nor the strict positivity of the MP integral — those are the paper's asserted analytic inputs, represented as hypotheses. A companion helper theorem discharges the paper's pointwise integrand-derivative identity as a Lean `HasDerivAt` fact.

> This proof establishes:
>
> `∀ (c u2 : ℝ) (I g R : ℝ → ℝ), 0 ≤ c → 0 < u2 → (∀ l : ℝ, 0 ≤ l → 0 < I l) → (∀ l : ℝ, 0 ≤ l → HasDerivAt g (2 * (l - c / u2) * I l) l) → (∀ l : ℝ, R l = u2 * g l) → ∀ l : ℝ, 0 ≤ l → l ≠ c / u2 → R (c / u2) < R l`
>
> It does **not yet** certify the source prose claim above (fidelity attested, not independently reviewed).

**Root goal (formal):** `∀ (c u2 : ℝ) (I g R : ℝ → ℝ), 0 ≤ c → 0 < u2 → (∀ l : ℝ, 0 ≤ l → 0 < I l) → (∀ l : ℝ, 0 ≤ l → HasDerivAt g (2 * (l - c / u2) * I l) l) → (∀ l : ℝ, R l = u2 * g l) → ∀ l : ℝ, 0 ≤ l → l ≠ c / u2 → R (c / u2) < R l`

| Proof soundness | Statement fidelity | Canonical promotion | Training eligibility |
|---|---|---|---|
| VERIFIED | ATTESTED (unsafe_dev_attestation — not reviewed) | BLOCKED | QUARANTINED |

| episode | state | steps | started | finished |
|---|---|---|---|---|
| `7e4c63ee-2999-476d-97b8-f92fce5e3d5f` | terminated (root_proved) | 1 | 2026-07-23T17:15:42 | 2026-07-23T17:19:02 |

| problem_version | `6d733c9c-4922-4e89-9b21-a2e9b68a96aa` |
|---|---|
| Verified Artifact Registry (VAR) | `a4670146-9788-4677-8265-13f123ecd73f` v1 (maturity=promoted, review=unreviewed) |

## Verified module

`module_source_hash: 4c2a9b22c158304824378ed0734251ea8fa13508c7a70d44bc376aee6e4910e1`

| # | kind | name |
|---|---|---|
| 0 | theorem | `integrand_hasDerivAt` |
| 1 | root_theorem | `ridge_prediction_risk_minimized_at_c_over_u2` |

```lean
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
noncomputable section

namespace ProofSearch.P_6d733c9c49224e89

theorem integrand_hasDerivAt : ∀ (a x l : ℝ), 0 < x → 0 ≤ l → HasDerivAt (fun t : ℝ => (t ^ 2 + a * x) / (x + t) ^ 2) (2 * (l - a) * (x / (x + l) ^ 3)) l := by
  intro a x l hx hl; have hpos : 0 < x + l := (by positivity); have hxl : x + l ≠ 0 := ne_of_gt hpos; have hne2 : (x + l) ^ 2 ≠ 0 := pow_ne_zero 2 hxl; have h1 : HasDerivAt (fun t : ℝ => x + t) (1 : ℝ) l := (by simpa using (hasDerivAt_id l).const_add x); have hnum : HasDerivAt (fun t : ℝ => t ^ 2 + a * x) (2 * l) l := (by simpa using (hasDerivAt_pow 2 l).add_const (a * x)); have hden := h1.fun_pow 2; have h := hnum.div hden hne2; convert h using 1 <;> first | rfl | (field_simp; ring)

theorem ridge_prediction_risk_minimized_at_c_over_u2 : ∀ (c u2 : ℝ) (I g R : ℝ → ℝ), 0 ≤ c → 0 < u2 → (∀ l : ℝ, 0 ≤ l → 0 < I l) → (∀ l : ℝ, 0 ≤ l → HasDerivAt g (2 * (l - c / u2) * I l) l) → (∀ l : ℝ, R l = u2 * g l) → ∀ l : ℝ, 0 ≤ l → l ≠ c / u2 → R (c / u2) < R l := by
  intro c u2 I g R hc hu hI hg hR; set a := c / u2 with ha_def; have ha : 0 ≤ a := div_nonneg hc (le_of_lt hu); have hanti : StrictAntiOn g (Set.Icc 0 a) := strictAntiOn_of_deriv_neg (convex_Icc 0 a) (fun x hx => (hg x hx.1).continuousAt.continuousWithinAt) (fun x hx => by rw [interior_Icc] at hx; have hx0 : 0 ≤ x := le_of_lt hx.1; rw [(hg x hx0).deriv]; have hIx := hI x hx0; have hlt : x - a < 0 := (by linarith [hx.2]); nlinarith [mul_neg_of_neg_of_pos hlt hIx]); have hmono : StrictMonoOn g (Set.Ici a) := strictMonoOn_of_deriv_pos (convex_Ici a) (fun x hx => (hg x (le_trans ha hx)).continuousAt.continuousWithinAt) (fun x hx => by rw [interior_Ici] at hx; have hxa : a < x := Set.mem_Ioi.mp hx; have hx0 : 0 ≤ x := le_trans ha (le_of_lt hxa); rw [(hg x hx0).deriv]; have hIx := hI x hx0; have hgt : 0 < x - a := (by linarith [hxa]); nlinarith [mul_pos hgt hIx]); intro l hl hne; rw [hR, hR]; have key : g a < g l := (lt_or_gt_of_ne hne).elim (fun hlt => hanti (Set.mem_Icc.mpr ⟨hl, le_of_lt hlt⟩) (Set.mem_Icc.mpr ⟨ha, le_refl a⟩) hlt) (fun hgt => hmono (Set.mem_Ici.mpr (le_refl a)) (Set.mem_Ici.mpr (le_of_lt hgt)) hgt); exact mul_lt_mul_of_pos_left key hu

end ProofSearch.P_6d733c9c49224e89
end
```

## Verification context

- **Environment:** `leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56`
- **Environment hash:** `9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d`
- **Import manifest:** `["Mathlib.Tactic.Ring","Mathlib.Tactic.NormNum","Mathlib"]`
- **Import manifest hash:** `aaf21893d520a78dee0787a1bcaf939ee6b922265ff670c272e2e1d450dd29a7`
- **root_statement_hash:** `6cf64e6d79f5926c39e6da3e430a40ad5e603211a0a8f3e5ea4f8ed9a824c0dc`
- **kernel_result_hash:** `11ef35c6b4b0e3a6b92ad2633c2dd14d079757a8aaf0c058eaedfa0687fd14da`
- **Axioms:** `propext, Classical.choice, Quot.sound` (no `sorry`, no custom axioms)

## Integrity

3 hash-chained trajectory events, `58b4e491d3c7…` → `fb12e0ff1a8d…` (GENESIS-anchored). Re-verify anytime with `episode_replay`.
