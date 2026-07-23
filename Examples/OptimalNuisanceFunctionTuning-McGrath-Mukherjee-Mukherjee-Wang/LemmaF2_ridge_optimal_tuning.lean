/-
  Lemma F.2 — Prediction-optimal ridge tuning parameter.

  ── Provenance ────────────────────────────────────────────────────────────────
  Paper:   "Optimal Nuisance Function Tuning for Estimating a Doubly Robust
            Functional under Proportional Asymptotics"
  Authors: Sean McGrath (Yale University),
           Debarghya Mukherjee (Boston University),
           Rajarshi Mukherjee (Harvard University),
           Zixiao Jolene Wang (Harvard University)
  Result:  Lemma F.2, Appendix F, pp. 52–54.
  Local source PDF (gitignored, not redistributed):
    Examples/Optimal Nuisance Function Tuning for Estimating a Doubly Robust
    Functional under Proportional Asymptotics.pdf
  Formalized by: Claude (Opus 4.8) via the proofsearch MCP environment, at the
                 request of the repository owner, as a worked example. The lemma
                 and its proof are the authors' own; this file only transcribes
                 the analytic core into Lean and checks it with the Lean kernel.
  ──────────────────────────────────────────────────────────────────────────────

  Statement (paper). The limiting mean-squared prediction error of the ridge
  estimator `p̂_{λ₁}` of the nuisance function `p`, given in Lemma F.1, is
  minimized over the ridge parameter λ₁ at

        λ₁* = c / u²,     u = limₙ ‖α₀‖₂,   c = lim (p / n).

  Proof (paper). The limiting risk factors as `R(λ) = u² · g(λ)`, where
        g(λ) = ∫ (λ² + (c/u²) x) / (x + λ)²  dF_MP(x),
  with F_MP the Marchenko–Pastur law. Differentiating the integrand,
        d/dλ [ (λ² + (c/u²) x)/(x+λ)² ] = 2 (λ − c/u²) · x/(x+λ)³,
  hence
        g'(λ) = 2 (λ − c/u²) ∫ x/(x+λ)³ dF_MP(x).
  Because ∫ x/(x+λ)³ dF_MP(x) > 0 for every λ ≥ 0, g'(λ) carries the sign of
  (λ − c/u²): negative on [0, c/u²), positive on (c/u², ∞). So g — and thus the
  risk R = u²·g — is strictly minimized at the unique point λ* = c/u².

  What is formalized here (and the modeling boundary).
  We formalize the analytic core faithfully and self-containedly.
  * `integrand_hasDerivAt` discharges the paper's pointwise differentiation of
    the integrand as a Lean `HasDerivAt` fact — exactly the calculus step above.
  * `ridge_prediction_risk_minimized_at_c_over_u2` is the minimization argument.
    The two facts the paper *establishes and then uses* — that the
    Marchenko–Pastur factor `I(λ) = ∫ x/(x+λ)³ dF_MP(x)` is positive, and that
    differentiation passes under the integral so `g'(λ) = 2(λ − c/u²) I(λ)` —
    enter as typed hypotheses (`I l > 0` on `[0,∞)`; `HasDerivAt g …` on `[0,∞)`).
    Given `c ≥ 0`, `u² > 0` and `R = u²·g`, we prove `R` is *strictly* minimized
    at `c/u²`. We do NOT formalize the measure-theoretic differentiation-under-
    the-integral interchange nor the strict positivity of the MP integral; those
    are the paper's asserted analytic inputs, represented as the hypotheses.

  Kernel-verified via the proofsearch MCP (tracked episode, real Lean kernel):
    environment      leanprover/lean4:v4.32.0-rc1
                       + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56
    problem_version  6d733c9c-4922-4e89-9b21-a2e9b68a96aa
    episode          7e4c63ee-2999-476d-97b8-f92fce5e3d5f
    outcome          kernel_verified   (termination: root_proved)
    axioms           propext, Classical.choice, Quot.sound  (no sorry / no custom axioms)

    Content hashes (see the .dossier.md for the full integrity chain):
      root_statement_hash  6cf64e6d79f5926c39e6da3e430a40ad5e603211a0a8f3e5ea4f8ed9a824c0dc
      module_source_hash   4c2a9b22c158304824378ed0734251ea8fa13508c7a70d44bc376aee6e4910e1
      kernel_result_hash   11ef35c6b4b0e3a6b92ad2633c2dd14d079757a8aaf0c058eaedfa0687fd14da
      environment_hash     9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d
    Verified Artifact Registry (VAR):
      artifact_id a4670146-9788-4677-8265-13f123ecd73f  (v1, maturity=promoted)

    Fidelity status: ATTESTED for dev/exploratory use (unsafe_dev_attestation) —
    the Lean statement is kernel-verified, but its faithfulness to the paper's
    prose has NOT been independently reviewed (never 'certified'). Re-verify the
    episode anytime with the proofsearch `episode_replay` tool.
-/
import Mathlib

open Set

/-- The paper's differentiation of the integrand of `g`.
For `x > 0` and `λ = l ≥ 0`,
`d/dl [ (l² + a·x)/(x+l)² ] = 2·(l − a)·(x/(x+l)³)`. -/
theorem integrand_hasDerivAt :
    ∀ (a x l : ℝ), 0 < x → 0 ≤ l →
      HasDerivAt (fun t : ℝ => (t ^ 2 + a * x) / (x + t) ^ 2)
        (2 * (l - a) * (x / (x + l) ^ 3)) l := by
  intro a x l hx hl
  have hpos : 0 < x + l := by positivity
  have hxl : x + l ≠ 0 := ne_of_gt hpos
  have hne2 : (x + l) ^ 2 ≠ 0 := pow_ne_zero 2 hxl
  -- numerator and denominator derivatives, then the quotient rule
  have hnum : HasDerivAt (fun t : ℝ => t ^ 2 + a * x) (2 * l) l := by
    simpa using (hasDerivAt_pow 2 l).add_const (a * x)
  have h1 : HasDerivAt (fun t : ℝ => x + t) (1 : ℝ) l := by
    simpa using (hasDerivAt_id l).const_add x
  have hden := h1.fun_pow 2
  have h := hnum.div hden hne2
  -- reconcile the quotient-rule derivative with the paper's factored form
  convert h using 1 <;> first | rfl | (field_simp; ring)

/-- Lemma F.2 (analytic core).  If the reduced risk factor `g` has derivative
`2·(l − c/u²)·I l` on `[0,∞)` with the Marchenko–Pastur factor `I l > 0`, and
`u² > 0`, `c ≥ 0`, then the limiting prediction risk `R l = u²·g l` is *strictly*
minimized at `λ* = c/u²`: for every `l ≥ 0` with `l ≠ c/u²`, `R (c/u²) < R l`. -/
theorem ridge_prediction_risk_minimized_at_c_over_u2 :
    ∀ (c u2 : ℝ) (I g R : ℝ → ℝ),
      0 ≤ c → 0 < u2 →
      (∀ l : ℝ, 0 ≤ l → 0 < I l) →
      (∀ l : ℝ, 0 ≤ l → HasDerivAt g (2 * (l - c / u2) * I l) l) →
      (∀ l : ℝ, R l = u2 * g l) →
      ∀ l : ℝ, 0 ≤ l → l ≠ c / u2 → R (c / u2) < R l := by
  intro c u2 I g R hc hu hI hg hR
  set a := c / u2 with ha_def
  have ha : 0 ≤ a := div_nonneg hc (le_of_lt hu)
  -- g is strictly decreasing on [0, a] : there g'(x) = 2(x-a)·I x < 0
  have hanti : StrictAntiOn g (Set.Icc 0 a) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc 0 a)
    · exact fun x hx => (hg x hx.1).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hx0 : 0 ≤ x := le_of_lt hx.1
      rw [(hg x hx0).deriv]
      have hIx := hI x hx0
      have hlt : x - a < 0 := by linarith [hx.2]
      nlinarith [mul_neg_of_neg_of_pos hlt hIx]
  -- g is strictly increasing on [a, ∞) : there g'(x) = 2(x-a)·I x > 0
  have hmono : StrictMonoOn g (Set.Ici a) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici a)
    · exact fun x hx => (hg x (le_trans ha hx)).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      have hxa : a < x := Set.mem_Ioi.mp hx
      have hx0 : 0 ≤ x := le_trans ha (le_of_lt hxa)
      rw [(hg x hx0).deriv]
      have hIx := hI x hx0
      have hgt : 0 < x - a := by linarith [hxa]
      nlinarith [mul_pos hgt hIx]
  intro l hl hne
  rw [hR, hR]
  -- either l < a (use strict antitonicity) or l > a (use strict monotonicity)
  have key : g a < g l :=
    (lt_or_gt_of_ne hne).elim
      (fun hlt => hanti (Set.mem_Icc.mpr ⟨hl, le_of_lt hlt⟩)
        (Set.mem_Icc.mpr ⟨ha, le_refl a⟩) hlt)
      (fun hgt => hmono (Set.mem_Ici.mpr (le_refl a))
        (Set.mem_Ici.mpr (le_of_lt hgt)) hgt)
  exact mul_lt_mul_of_pos_left key hu
