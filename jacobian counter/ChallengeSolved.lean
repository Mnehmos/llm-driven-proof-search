/-
ChallengeSolved.lean — solved counterpart of Challenge.lean.

Each proof below is the verbatim tactic script that the LLM-Driven Proof Search
Environment's pinned Lean 4 + Mathlib kernel accepted (episodes and outcomes in the
docstrings; see README.md for hashes). The scripts are transcribed unchanged from the
accepted `Solve` submissions; the theorem statements are byte-identical to the registered
root statements whose canonical hashes the environment checked.

Verified claims chain:
  1. `numeric_claims`                       — problem 29f88fb5, episode 0c0afd37, kernel_verified
  2. `jacobian_conjecture_refuted_dim3`     — problem 654521be, episode 1f9dfbee, CERTIFIED
  3. `counterexample_map_not_injective`     — problem f3b97f2c, episode a8a4062d, CERTIFIED
  4. `jacobian_conjecture_refuted_dim4`     — problem 7312a555, episode 591219bc, CERTIFIED
  5. `normalized_map_facts`                 — problem c270a9d2, episode c8d0d87c, CERTIFIED
-/
import Mathlib

open MvPolynomial

namespace JacobianChallenge

/-- Challenge 1, solved (kernel_verified over ℚ). -/
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
  refine ⟨?_, ?_⟩
  · dsimp only
    rw [show (4 : MvPolynomial (Fin 3) ℚ) = C 4 from (map_ofNat C 4).symm]
    rw [show (3 : MvPolynomial (Fin 3) ℚ) = C 3 from (map_ofNat C 3).symm]
    rw [show (2 : MvPolynomial (Fin 3) ℚ) = C 2 from (map_ofNat C 2).symm]
    set_option maxRecDepth 400000 in
    simp [pderiv_mul, pderiv_pow, pderiv_C, pderiv_X_self, pderiv_X_of_ne, pderiv_one,
      Derivation.map_add, Derivation.map_sub]
    set_option maxRecDepth 400000 in
    simp only [map_ofNat, map_one]
    set_option maxRecDepth 400000 in
    all_goals ring
  · dsimp only
    norm_num [Prod.mk.injEq]

/-- Challenge 2, solved (CERTIFIED over ℂ): refutation of the Jacobian Conjecture in the
shape of formal-conjectures' `jacobian_conjecture`, dimension 3. -/
theorem jacobian_conjecture_refuted_dim3 :
    ¬ (∀ F : Fin 3 → MvPolynomial (Fin 3) ℂ,
         IsUnit (Matrix.of fun i j => pderiv i (F j)).det →
         ∃ G : Fin 3 → MvPolynomial (Fin 3) ℂ,
           (fun i => bind₁ G (F i)) = X ∧ (fun i => bind₁ F (G i)) = X) := by
  intro h
  have hdet : (Matrix.of fun i j => pderiv i ((![(1 + X 0 * X 1)^3 * X 2 + (X 1)^2 * (1 + X 0 * X 1) * (C 4 + C 3 * X 0 * X 1), X 1 + C 3 * X 0 * (1 + X 0 * X 1)^2 * X 2 + C 3 * X 0 * (X 1)^2 * (C 4 + C 3 * X 0 * X 1), C 2 * X 0 - C 3 * (X 0)^2 * X 1 - (X 0)^3 * X 2] : Fin 3 → MvPolynomial (Fin 3) ℂ) j)).det = C (-2 : ℂ) := by
    rw [Matrix.det_fin_three]
    set_option maxRecDepth 400000 in
    simp [pderiv_mul, pderiv_pow, pderiv_C, pderiv_X_self, pderiv_X_of_ne, pderiv_one, Derivation.map_add, Derivation.map_sub]
    set_option maxRecDepth 400000 in
    simp only [map_ofNat, map_one]
    set_option maxRecDepth 400000 in
    ring
  obtain ⟨G, -, hFG⟩ := h (![(1 + X 0 * X 1)^3 * X 2 + (X 1)^2 * (1 + X 0 * X 1) * (C 4 + C 3 * X 0 * X 1), X 1 + C 3 * X 0 * (1 + X 0 * X 1)^2 * X 2 + C 3 * X 0 * (X 1)^2 * (C 4 + C 3 * X 0 * X 1), C 2 * X 0 - C 3 * (X 0)^2 * X 1 - (X 0)^3 * X 2] : Fin 3 → MvPolynomial (Fin 3) ℂ) (by rw [hdet]; exact (isUnit_iff_ne_zero.mpr (by norm_num : (-2 : ℂ) ≠ 0)).map (C : ℂ →+* MvPolynomial (Fin 3) ℂ))
  have h1 : ∀ (p : Fin 3 → ℂ) (i : Fin 3), aeval (fun j => aeval p ((![(1 + X 0 * X 1)^3 * X 2 + (X 1)^2 * (1 + X 0 * X 1) * (C 4 + C 3 * X 0 * X 1), X 1 + C 3 * X 0 * (1 + X 0 * X 1)^2 * X 2 + C 3 * X 0 * (X 1)^2 * (C 4 + C 3 * X 0 * X 1), C 2 * X 0 - C 3 * (X 0)^2 * X 1 - (X 0)^3 * X 2] : Fin 3 → MvPolynomial (Fin 3) ℂ) j)) (G i) = p i := by
    intro p i
    have hi := congrArg (fun q => aeval p q) (congrFun hFG i)
    simp only [aeval_bind₁, aeval_X] at hi
    exact hi
  have epts : (fun j => aeval (![0, 0, -1/4] : Fin 3 → ℂ) ((![(1 + X 0 * X 1)^3 * X 2 + (X 1)^2 * (1 + X 0 * X 1) * (C 4 + C 3 * X 0 * X 1), X 1 + C 3 * X 0 * (1 + X 0 * X 1)^2 * X 2 + C 3 * X 0 * (X 1)^2 * (C 4 + C 3 * X 0 * X 1), C 2 * X 0 - C 3 * (X 0)^2 * X 1 - (X 0)^3 * X 2] : Fin 3 → MvPolynomial (Fin 3) ℂ) j)) = (fun j => aeval (![1, -3/2, 13/2] : Fin 3 → ℂ) ((![(1 + X 0 * X 1)^3 * X 2 + (X 1)^2 * (1 + X 0 * X 1) * (C 4 + C 3 * X 0 * X 1), X 1 + C 3 * X 0 * (1 + X 0 * X 1)^2 * X 2 + C 3 * X 0 * (X 1)^2 * (C 4 + C 3 * X 0 * X 1), C 2 * X 0 - C 3 * (X 0)^2 * X 1 - (X 0)^3 * X 2] : Fin 3 → MvPolynomial (Fin 3) ℂ) j)) := by
    funext j
    fin_cases j <;> (set_option maxRecDepth 40000 in simp) <;> norm_num
  have a0 := h1 ![0, 0, -1/4] 0
  have b0 := h1 ![1, -3/2, 13/2] 0
  rw [epts] at a0
  have hcontra : (![0, 0, -1/4] : Fin 3 → ℂ) 0 = (![1, -3/2, 13/2] : Fin 3 → ℂ) 0 := a0.symm.trans b0
  norm_num at hcontra

/-- Challenge 3, solved (CERTIFIED over ℂ): the counterexample map is not injective. -/
theorem counterexample_map_not_injective :
    ¬ Function.Injective (fun (p : Fin 3 → ℂ) => fun (i : Fin 3) =>
        aeval p ((![(1 + X 0 * X 1)^3 * X 2 + (X 1)^2 * (1 + X 0 * X 1) * (C 4 + C 3 * X 0 * X 1),
                    X 1 + C 3 * X 0 * (1 + X 0 * X 1)^2 * X 2 + C 3 * X 0 * (X 1)^2 * (C 4 + C 3 * X 0 * X 1),
                    C 2 * X 0 - C 3 * (X 0)^2 * X 1 - (X 0)^3 * X 2] :
                  Fin 3 → MvPolynomial (Fin 3) ℂ) i)) := by
  intro h
  have himg : (fun (i : Fin 3) => aeval (![0, 0, -1/4] : Fin 3 → ℂ) ((![(1 + X 0 * X 1)^3 * X 2 + (X 1)^2 * (1 + X 0 * X 1) * (C 4 + C 3 * X 0 * X 1), X 1 + C 3 * X 0 * (1 + X 0 * X 1)^2 * X 2 + C 3 * X 0 * (X 1)^2 * (C 4 + C 3 * X 0 * X 1), C 2 * X 0 - C 3 * (X 0)^2 * X 1 - (X 0)^3 * X 2] : Fin 3 → MvPolynomial (Fin 3) ℂ) i)) = (fun (i : Fin 3) => aeval (![1, -3/2, 13/2] : Fin 3 → ℂ) ((![(1 + X 0 * X 1)^3 * X 2 + (X 1)^2 * (1 + X 0 * X 1) * (C 4 + C 3 * X 0 * X 1), X 1 + C 3 * X 0 * (1 + X 0 * X 1)^2 * X 2 + C 3 * X 0 * (X 1)^2 * (C 4 + C 3 * X 0 * X 1), C 2 * X 0 - C 3 * (X 0)^2 * X 1 - (X 0)^3 * X 2] : Fin 3 → MvPolynomial (Fin 3) ℂ) i)) := by
    funext i
    fin_cases i <;> (set_option maxRecDepth 40000 in simp) <;> norm_num
  have heq := h himg
  have h0 := congrFun heq 0
  norm_num at h0

/-- Challenge 4, solved (CERTIFIED over ℂ): stabilized refutation in dimension 4. -/
theorem jacobian_conjecture_refuted_dim4 :
    ¬ (∀ F : Fin 4 → MvPolynomial (Fin 4) ℂ,
         IsUnit (Matrix.of fun i j => pderiv i (F j)).det →
         ∃ G : Fin 4 → MvPolynomial (Fin 4) ℂ,
           (fun i => bind₁ G (F i)) = X ∧ (fun i => bind₁ F (G i)) = X) := by
  intro h
  have hdet : (Matrix.of fun i j => pderiv i ((![(1 + X 0 * X 1)^3 * X 2 + (X 1)^2 * (1 + X 0 * X 1) * (C 4 + C 3 * X 0 * X 1), X 1 + C 3 * X 0 * (1 + X 0 * X 1)^2 * X 2 + C 3 * X 0 * (X 1)^2 * (C 4 + C 3 * X 0 * X 1), C 2 * X 0 - C 3 * (X 0)^2 * X 1 - (X 0)^3 * X 2, X 3] : Fin 4 → MvPolynomial (Fin 4) ℂ) j)).det = C (-2 : ℂ) := by
    rw [Matrix.det_succ_row _ 3]
    set_option maxRecDepth 400000 in
    simp [Fin.sum_univ_four, Matrix.submatrix_apply, Matrix.of_apply, show ((3:Fin 4).succAbove 0) = 0 from rfl, show ((3:Fin 4).succAbove 1) = 1 from rfl, show ((3:Fin 4).succAbove 2) = 2 from rfl, pderiv_mul, pderiv_pow, pderiv_C, pderiv_X_self, pderiv_X_of_ne, pderiv_one, Derivation.map_add, Derivation.map_sub]
    rw [Matrix.det_fin_three]
    set_option maxRecDepth 400000 in
    simp [Matrix.submatrix_apply, Matrix.of_apply, show ((3:Fin 4).succAbove 0) = 0 from rfl, show ((3:Fin 4).succAbove 1) = 1 from rfl, show ((3:Fin 4).succAbove 2) = 2 from rfl, pderiv_mul, pderiv_pow, pderiv_C, pderiv_X_self, pderiv_X_of_ne, pderiv_one, Derivation.map_add, Derivation.map_sub]
    set_option maxRecDepth 400000 in
    simp only [map_ofNat, map_one]
    set_option maxRecDepth 400000 in
    ring
  obtain ⟨G, -, hFG⟩ := h (![(1 + X 0 * X 1)^3 * X 2 + (X 1)^2 * (1 + X 0 * X 1) * (C 4 + C 3 * X 0 * X 1), X 1 + C 3 * X 0 * (1 + X 0 * X 1)^2 * X 2 + C 3 * X 0 * (X 1)^2 * (C 4 + C 3 * X 0 * X 1), C 2 * X 0 - C 3 * (X 0)^2 * X 1 - (X 0)^3 * X 2, X 3] : Fin 4 → MvPolynomial (Fin 4) ℂ) (by rw [hdet]; exact (isUnit_iff_ne_zero.mpr (by norm_num : (-2 : ℂ) ≠ 0)).map (C : ℂ →+* MvPolynomial (Fin 4) ℂ))
  have h1 : ∀ (p : Fin 4 → ℂ) (i : Fin 4), aeval (fun j => aeval p ((![(1 + X 0 * X 1)^3 * X 2 + (X 1)^2 * (1 + X 0 * X 1) * (C 4 + C 3 * X 0 * X 1), X 1 + C 3 * X 0 * (1 + X 0 * X 1)^2 * X 2 + C 3 * X 0 * (X 1)^2 * (C 4 + C 3 * X 0 * X 1), C 2 * X 0 - C 3 * (X 0)^2 * X 1 - (X 0)^3 * X 2, X 3] : Fin 4 → MvPolynomial (Fin 4) ℂ) j)) (G i) = p i := by
    intro p i
    have hi := congrArg (fun q => aeval p q) (congrFun hFG i)
    simp only [aeval_bind₁, aeval_X] at hi
    exact hi
  have epts : (fun j => aeval (![0, 0, -1/4, 0] : Fin 4 → ℂ) ((![(1 + X 0 * X 1)^3 * X 2 + (X 1)^2 * (1 + X 0 * X 1) * (C 4 + C 3 * X 0 * X 1), X 1 + C 3 * X 0 * (1 + X 0 * X 1)^2 * X 2 + C 3 * X 0 * (X 1)^2 * (C 4 + C 3 * X 0 * X 1), C 2 * X 0 - C 3 * (X 0)^2 * X 1 - (X 0)^3 * X 2, X 3] : Fin 4 → MvPolynomial (Fin 4) ℂ) j)) = (fun j => aeval (![1, -3/2, 13/2, 0] : Fin 4 → ℂ) ((![(1 + X 0 * X 1)^3 * X 2 + (X 1)^2 * (1 + X 0 * X 1) * (C 4 + C 3 * X 0 * X 1), X 1 + C 3 * X 0 * (1 + X 0 * X 1)^2 * X 2 + C 3 * X 0 * (X 1)^2 * (C 4 + C 3 * X 0 * X 1), C 2 * X 0 - C 3 * (X 0)^2 * X 1 - (X 0)^3 * X 2, X 3] : Fin 4 → MvPolynomial (Fin 4) ℂ) j)) := by
    funext j
    fin_cases j <;> (set_option maxRecDepth 40000 in simp) <;> norm_num
  have a0 := h1 ![0, 0, -1/4, 0] 0
  have b0 := h1 ![1, -3/2, 13/2, 0] 0
  rw [epts] at a0
  have hcontra : (![0, 0, -1/4, 0] : Fin 4 → ℂ) 0 = (![1, -3/2, 13/2, 0] : Fin 4 → ℂ) 0 := a0.symm.trans b0
  norm_num at hcontra

/-- Challenge 5, solved (CERTIFIED over ℂ): normalized form, paper Cor. 3.2.
Note the two techniques beyond the standard recipe: the statement let-binds U once
(six-fold inlining exceeds the statement-elaboration heartbeat budget), and the
determinant closes with `linear_combination W * h2` where h2 : 2·C 2⁻¹ = 1 supplies the
scalar relation `ring` cannot know, with the cofactor W computed externally by exact
polynomial division. -/
theorem normalized_map_facts :
    (let U : Fin 3 → MvPolynomial (Fin 3) ℂ := ![X 0 - C (3/2) * (X 0)^2 * X 1 - C (1/2) * (X 0)^3 * X 2, X 1 + C 3 * X 0 * (1 + X 0 * X 1)^2 * X 2 + C 3 * X 0 * (X 1)^2 * (C 4 + C 3 * X 0 * X 1), (1 + X 0 * X 1)^3 * X 2 + (X 1)^2 * (1 + X 0 * X 1) * (C 4 + C 3 * X 0 * X 1)]
     (Matrix.of fun i j => pderiv i (U j)).det = C (1 : ℂ)
     ∧ (Matrix.of fun i j => aeval (fun _ => (0:ℂ)) (pderiv i (U j))) = 1
     ∧ (fun i => aeval (fun _ => (0:ℂ)) (U i)) = (fun _ => (0:ℂ))
     ∧ (fun i => aeval (![0, 0, -1/4] : Fin 3 → ℂ) (U i)) = (![0, 0, -1/4] : Fin 3 → ℂ)
     ∧ (fun i => aeval (![1, -3/2, 13/2] : Fin 3 → ℂ) (U i)) = (![0, 0, -1/4] : Fin 3 → ℂ)
     ∧ (fun i => aeval (![-1, 3/2, 13/2] : Fin 3 → ℂ) (U i)) = (![0, 0, -1/4] : Fin 3 → ℂ)) := by
  set_option maxHeartbeats 2000000 in
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.det_fin_three]
    rw [show (C (1 : ℂ) : MvPolynomial (Fin 3) ℂ) = C 2 * C (1/2) from by rw [← C_mul]; norm_num]
    rw [show (C (3/2 : ℂ) : MvPolynomial (Fin 3) ℂ) = C 3 * C (1/2) from by rw [← C_mul]; norm_num]
    set_option maxHeartbeats 2000000 in
    set_option maxRecDepth 400000 in
    simp [pderiv_mul, pderiv_pow, pderiv_C, pderiv_X_self, pderiv_X_of_ne, pderiv_one, Derivation.map_add, Derivation.map_sub]
    set_option maxHeartbeats 2000000 in
    set_option maxRecDepth 400000 in
    simp only [map_ofNat, map_one]
    have h2 : (2 : MvPolynomial (Fin 3) ℂ) * C ((2 : ℂ)⁻¹) = 1 := by rw [show (2 : MvPolynomial (Fin 3) ℂ) = C 2 from (map_ofNat C 2).symm, ← C_mul]; norm_num
    set_option maxHeartbeats 2000000 in
    set_option maxRecDepth 400000 in
    linear_combination ((X 0 * X 1 + 1)^2 * (3 * (X 0)^4 * (X 1)^2 * X 2 + 9 * (X 0)^3 * (X 1)^3 + 6 * (X 0)^3 * X 1 * X 2 + 12 * (X 0)^2 * (X 1)^2 + 3 * (X 0)^2 * X 2 - X 0 * X 1 - 1)) * h2
  · ext i j
    fin_cases i <;> fin_cases j <;> (set_option maxHeartbeats 2000000 in set_option maxRecDepth 40000 in simp [pderiv_mul, pderiv_pow, pderiv_C, pderiv_X_self, pderiv_X_of_ne, pderiv_one, Derivation.map_add, Derivation.map_sub, Matrix.one_apply]) <;> (set_option maxHeartbeats 1000000 in norm_num)
  · funext i
    fin_cases i <;> (set_option maxHeartbeats 1000000 in set_option maxRecDepth 40000 in simp) <;> (set_option maxHeartbeats 1000000 in norm_num)
  · funext i
    fin_cases i <;> (set_option maxHeartbeats 1000000 in set_option maxRecDepth 40000 in simp) <;> (set_option maxHeartbeats 1000000 in norm_num)
  · funext i
    fin_cases i <;> (set_option maxHeartbeats 1000000 in set_option maxRecDepth 40000 in simp) <;> (set_option maxHeartbeats 1000000 in norm_num)
  · funext i
    fin_cases i <;> (set_option maxHeartbeats 1000000 in set_option maxRecDepth 40000 in simp) <;> (set_option maxHeartbeats 1000000 in norm_num)

end JacobianChallenge
