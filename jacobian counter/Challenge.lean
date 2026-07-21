/-
Challenge.lean — The Jacobian Conjecture is false: five formal challenges.
(A sixth certified theorem, the Poisson-bridge computational core, lives in the
environment ledger as problem a4044282 / episode c25405a7; its 15-command Decompose
tree is documented in proof-construction.md §7.)

Source: L. Alpöge, X post, July 19 2026 (https://x.com/__alpoge__/status/2079028340955197566),
and P. Chojecki, "A Counterexample to the Jacobian Conjecture" (ulam.ai research
write-up, July 20 2026; jacobian.pdf).
The counterexample map is

  F(x, y, z) = ( (1+xy)³z + y²(1+xy)(4+3xy),
                 y + 3x(1+xy)²z + 3xy²(4+3xy),
                 2x − 3x²y − x³z )

with constant Jacobian determinant −2 and F(0,0,−1/4) = F(1,−3/2,13/2) = F(−1,3/2,13/2)
= (−1/4, 0, 0).

Every statement below is stated exactly as verified through the LLM-Driven Proof Search
Environment (pinned Lean 4 + Mathlib kernel). Replace each `sorry` to reproduce the results;
the solved counterpart is `ChallengeSolved.lean`.

Challenge statements 2–4 are the negation of the Jacobian Conjecture as formalized in
Google DeepMind's formal-conjectures repository
(FormalConjectures/Wikipedia/JacobianConjecture.lean, theorem `jacobian_conjecture`),
with `RegularFunction`/`Jacobian`/`comp`/`id` unfolded to their definitions
(`σ → MvPolynomial σ k`, `Matrix.of fun i j => pderiv i (F j)`, `bind₁`, `X`),
at the instances k = ℂ, σ = Fin 3 and k = ℂ, σ = Fin 4.
-/
import Mathlib

open MvPolynomial

namespace JacobianChallenge

/-- **Challenge 1** (verified over ℚ; environment problem `29f88fb5`, outcome
`kernel_verified`): the symbolic Jacobian determinant of the counterexample map is the
constant polynomial −2, and the three tweeted points share the image (−1/4, 0, 0). -/
theorem numeric_claims :
    (let x : MvPolynomial (Fin 3) ℚ := X 0
     let y : MvPolynomial (Fin 3) ℚ := X 1
     let z : MvPolynomial (Fin 3) ℚ := X 2
     let F1 : MvPolynomial (Fin 3) ℚ := (1 + x*y)^3*z + y^2*(1+x*y)*(4+3*x*y)
     let F2 : MvPolynomial (Fin 3) ℚ := y + 3*x*(1+x*y)^2*z + 3*x*y^2*(4+3*x*y)
     let F3 : MvPolynomial (Fin 3) ℚ := 2*x - 3*x^2*y - x^3*z
     pderiv 0 F1 * (pderiv 1 F2 * pderiv 2 F3 - pderiv 2 F2 * pderiv 1 F3)
       - pderiv 1 F1 * (pderiv 0 F2 * pderiv 2 F3 - pderiv 2 F2 * pderiv 0 F3)
       + pderiv 2 F1 * (pderiv 0 F2 * pderiv 1 F3 - pderiv 1 F2 * pderiv 0 F3)
     = C (-2 : ℚ))
    ∧
    (let f : ℚ → ℚ → ℚ → ℚ × ℚ × ℚ := fun a b c =>
       ((1+a*b)^3*c + b^2*(1+a*b)*(4+3*a*b),
        b + 3*a*(1+a*b)^2*c + 3*a*b^2*(4+3*a*b),
        2*a - 3*a^2*b - a^3*c)
     f 0 0 (-1/4) = (-1/4, 0, 0) ∧ f 1 (-3/2) (13/2) = (-1/4, 0, 0) ∧
       f (-1) (3/2) (13/2) = (-1/4, 0, 0)) := by
  sorry

/-- **Challenge 2** (verified over ℂ; environment problem `654521be`, outcome
**`certified`**): the Jacobian Conjecture — in the exact shape formalized by
formal-conjectures' `jacobian_conjecture`, instantiated at k = ℂ, σ = Fin 3 — is FALSE.
No Keller condition `IsUnit det(Jacobian)` forces a two-sided compositional polynomial
inverse. -/
theorem jacobian_conjecture_refuted_dim3 :
    ¬ (∀ F : Fin 3 → MvPolynomial (Fin 3) ℂ,
         IsUnit (Matrix.of fun i j => pderiv i (F j)).det →
         ∃ G : Fin 3 → MvPolynomial (Fin 3) ℂ,
           (fun i => bind₁ G (F i)) = X ∧ (fun i => bind₁ F (G i)) = X) := by
  sorry

/-- **Challenge 3** (verified over ℂ; environment problem `f3b97f2c`, outcome
**`certified`**): the counterexample map is not injective as a function ℂ³ → ℂ³. -/
theorem counterexample_map_not_injective :
    ¬ Function.Injective (fun (p : Fin 3 → ℂ) => fun (i : Fin 3) =>
        aeval p ((![(1 + X 0 * X 1)^3 * X 2 + (X 1)^2 * (1 + X 0 * X 1) * (C 4 + C 3 * X 0 * X 1),
                    X 1 + C 3 * X 0 * (1 + X 0 * X 1)^2 * X 2 + C 3 * X 0 * (X 1)^2 * (C 4 + C 3 * X 0 * X 1),
                    C 2 * X 0 - C 3 * (X 0)^2 * X 1 - (X 0)^3 * X 2] :
                  Fin 3 → MvPolynomial (Fin 3) ℂ) i)) := by
  sorry

/-- **Challenge 4** (verified over ℂ; environment problem `7312a555`, outcome
**`certified`**): by stabilization (append the coordinate w as a fourth component), the
Jacobian Conjecture is also FALSE in dimension 4. The paper's construction extends this to
every dimension n ≥ 3. -/
theorem jacobian_conjecture_refuted_dim4 :
    ¬ (∀ F : Fin 4 → MvPolynomial (Fin 4) ℂ,
         IsUnit (Matrix.of fun i j => pderiv i (F j)).det →
         ∃ G : Fin 4 → MvPolynomial (Fin 4) ℂ,
           (fun i => bind₁ G (F i)) = X ∧ (fun i => bind₁ F (G i)) = X) := by
  sorry

/-- **Challenge 5** (verified over ℂ; environment problem `c270a9d2`, outcome
**`certified`**): the normalized form (paper Cor. 3.2). With U = (R/2, Q, P):
det Jac U = 1, Jac U(0) = I, U(0) = 0, and the three witness points all map to
(0, 0, −1/4) — which is itself a fixed point of U. This is the standard input for the
downstream Weyl-algebra (Dixmier), Poisson, and Zhao-machinery constructions. -/
theorem normalized_map_facts :
    (let U : Fin 3 → MvPolynomial (Fin 3) ℂ := ![X 0 - C (3/2) * (X 0)^2 * X 1 - C (1/2) * (X 0)^3 * X 2, X 1 + C 3 * X 0 * (1 + X 0 * X 1)^2 * X 2 + C 3 * X 0 * (X 1)^2 * (C 4 + C 3 * X 0 * X 1), (1 + X 0 * X 1)^3 * X 2 + (X 1)^2 * (1 + X 0 * X 1) * (C 4 + C 3 * X 0 * X 1)]
     (Matrix.of fun i j => pderiv i (U j)).det = C (1 : ℂ)
     ∧ (Matrix.of fun i j => aeval (fun _ => (0:ℂ)) (pderiv i (U j))) = 1
     ∧ (fun i => aeval (fun _ => (0:ℂ)) (U i)) = (fun _ => (0:ℂ))
     ∧ (fun i => aeval (![0, 0, -1/4] : Fin 3 → ℂ) (U i)) = (![0, 0, -1/4] : Fin 3 → ℂ)
     ∧ (fun i => aeval (![1, -3/2, 13/2] : Fin 3 → ℂ) (U i)) = (![0, 0, -1/4] : Fin 3 → ℂ)
     ∧ (fun i => aeval (![-1, 3/2, 13/2] : Fin 3 → ℂ) (U i)) = (![0, 0, -1/4] : Fin 3 → ℂ)) := by
  sorry

end JacobianChallenge
