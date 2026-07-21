/-
CollateralDamage.lean — downstream consequences of the Jacobian Conjecture's failure.

STATUS LABELS (read carefully; this file is deliberately honest about what is proved):

  [CERTIFIED]    — verbatim transcription of a proof accepted by the pinned Lean 4 +
                   Mathlib kernel of the LLM-Driven Proof Search Environment, with a
                   verified statement-fidelity review (see README.md for episode IDs).
  [CONDITIONAL]  — fully proved here WITHOUT sorry, but takes a known literature
                   implication (a "bridge") as an explicit hypothesis. The theorem is
                   exactly as strong as the bridge.
  [BRIDGE, OPEN HERE] — the literature implication itself, stated formally with a
                   `sorry`. Proved in the cited paper(s); NOT formalized here. Each is a
                   substantial formalization campaign in its own right.

The implication graph (all bridges are contrapositives of published results):

  ¬JC₃  ──(Dixmier ⟹ Jacobian, van den Essen)──▶  ¬Dixmier for A₃  (hence Aₙ, n ≥ 3)
  ¬JC₃  ──(Mathieu ⟹ Jacobian, Mathieu 1995)──▶  ¬Mathieu conjecture   [not statable in
                                                    current Mathlib: needs Haar/rep theory]
  ¬JC₃  ──(Zhao VC ⟺ Jacobian, Zhao 2007)──▶     ¬Zhao vanishing conjecture
  ¬JC₃  ──(BCW/Drużkowski degree reduction)──▶    cubic-homogeneous counterexamples exist
                                                    in some higher dimension

References:
  [BCW]  H. Bass, E. Connell, D. Wright, "The Jacobian conjecture: reduction of degree
         and formal expansion of the inverse", Bull. AMS 7 (1982) 287–330.
  [vdE]  A. van den Essen, "Polynomial Automorphisms and the Jacobian Conjecture",
         Progress in Math. 190, Birkhäuser 2000 (Dixmier ⟹ Jacobian: Prop. 10.2.7).
  [Tsu]  Y. Tsuchimoto, "Endomorphisms of Weyl algebra and p-curvatures", Osaka J. Math.
         42 (2005); A. Belov-Kanel, M. Kontsevich, "The Jacobian conjecture is stably
         equivalent to the Dixmier conjecture", Mosc. Math. J. 7 (2007). (JC₂ₙ ⟹ DCₙ —
         with our refutation this direction now transmits nothing; the refutation of DC
         flows through [vdE] instead.)
  [Mat]  O. Mathieu, "Some conjectures about invariant theory and their applications",
         Algèbre non commutative, groupes quantiques et invariants (1995).
  [Zhao] W. Zhao, "Hessian nilpotent polynomials and the Jacobian conjecture",
         Trans. AMS 359 (2007) 249–274 (vanishing conjecture ⟺ JC).
  [Alp]  L. Alpöge, X post, July 19 2026 (the counterexample map).
  [Cho]  P. Chojecki, "A Counterexample to the Jacobian Conjecture",
         https://www.ulam.ai/research/jacobian.pdf, July 20 2026 (algebraic
         verification, fibers, families; byte-identical to this release's jacobian.pdf).
  [Omni] "An Explicit Counterexample to the Dixmier Conjecture in A3",
         omniscienceproject.com note, July 2026 — writes up the direct Weyl-algebra
         endomorphism Φ(xᵢ) = Uᵢ, Φ(∂ᵢ) = Σ (adj J)ᵣᵢ ∂ᵣ from the counterexample.
  [Gist] 11-variable degree-3 reduction certificate (ChatGPT-generated sympy script),
         gist.github.com/Spacerat/08b4a43f6b6ca57178efabc220170ce8 — det −2, 52 terms,
         same three-point collision; independently re-verified with sympy (including a
         direct 11×11 Jacobian determinant computation) for this release.
-/
import Mathlib

open MvPolynomial

namespace JacobianCollateral

/-! ## The Jacobian Conjecture statement schema (formal-conjectures shape, unfolded) -/

/-- The Jacobian Conjecture in dimension `n` over ℂ, in the exact shape of
formal-conjectures' `jacobian_conjecture` with `RegularFunction`/`Jacobian`/`comp`/`id`
unfolded: every polynomial self-map with unit Jacobian determinant has a two-sided
compositional polynomial inverse. -/
def JacobianStatement (n : ℕ) : Prop :=
  ∀ F : Fin n → MvPolynomial (Fin n) ℂ,
    IsUnit (Matrix.of fun i j => pderiv i (F j)).det →
    ∃ G : Fin n → MvPolynomial (Fin n) ℂ,
      (fun i => bind₁ G (F i)) = X ∧ (fun i => bind₁ F (G i)) = X

/-- [CERTIFIED] The Jacobian Conjecture is false in dimension 3 (environment problem
`654521be`, episode `1f9dfbee`, outcome `certified`). Witness: the Alpöge map. -/
theorem jacobian_statement_false_dim3 : ¬ JacobianStatement 3 := by
  unfold JacobianStatement
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

/-! ## Dixmier -/

/-- The defining relations of the `n`-th Weyl algebra Aₙ(ℂ) on generators
`Sum.inl i` (position operators qᵢ) and `Sum.inr i` (momentum operators pᵢ):
all pairs commute except `pᵢqᵢ = qᵢpᵢ + 1`. -/
inductive weylRel (n : ℕ) :
    FreeAlgebra ℂ (Fin n ⊕ Fin n) → FreeAlgebra ℂ (Fin n ⊕ Fin n) → Prop
  | q_comm (i j : Fin n) : weylRel n
      (FreeAlgebra.ι ℂ (Sum.inl i) * FreeAlgebra.ι ℂ (Sum.inl j))
      (FreeAlgebra.ι ℂ (Sum.inl j) * FreeAlgebra.ι ℂ (Sum.inl i))
  | p_comm (i j : Fin n) : weylRel n
      (FreeAlgebra.ι ℂ (Sum.inr i) * FreeAlgebra.ι ℂ (Sum.inr j))
      (FreeAlgebra.ι ℂ (Sum.inr j) * FreeAlgebra.ι ℂ (Sum.inr i))
  | pq_comm (i j : Fin n) (h : i ≠ j) : weylRel n
      (FreeAlgebra.ι ℂ (Sum.inr i) * FreeAlgebra.ι ℂ (Sum.inl j))
      (FreeAlgebra.ι ℂ (Sum.inl j) * FreeAlgebra.ι ℂ (Sum.inr i))
  | ccr (i : Fin n) : weylRel n
      (FreeAlgebra.ι ℂ (Sum.inr i) * FreeAlgebra.ι ℂ (Sum.inl i))
      (FreeAlgebra.ι ℂ (Sum.inl i) * FreeAlgebra.ι ℂ (Sum.inr i) + 1)

/-- The `n`-th Weyl algebra Aₙ(ℂ) as a ring quotient of the free algebra. -/
abbrev WeylAlgebra (n : ℕ) := RingQuot (weylRel n)

/-- The Dixmier conjecture for Aₙ(ℂ): every ℂ-algebra endomorphism of the Weyl algebra
is bijective (equivalently, an automorphism). -/
def DixmierStatement (n : ℕ) : Prop :=
  ∀ f : WeylAlgebra n →ₐ[ℂ] WeylAlgebra n, Function.Bijective f

/-- [BRIDGE, OPEN HERE] Dixmier implies Jacobian in the same dimension ([vdE],
Prop. 10.2.7 — the classical "easy direction"). Formalizing this needs the associated
graded/symbol map from Aₙ to the polynomial ring; it is NOT proved in this release. -/
theorem dixmier_implies_jacobian (n : ℕ) :
    DixmierStatement n → JacobianStatement n := by
  sorry

/-- [CONDITIONAL] Granting the [vdE] bridge for n = 3, the Dixmier conjecture is FALSE
for A₃(ℂ). No sorry in this proof: it is the contrapositive of the bridge applied to the
certified refutation above. -/
theorem dixmier_false_of_bridge
    (bridge : DixmierStatement 3 → JacobianStatement 3) :
    ¬ DixmierStatement 3 :=
  fun hd => jacobian_statement_false_dim3 (bridge hd)

/-! ## Zhao's vanishing conjecture -/

/-- The Laplace operator Δ = Σᵢ ∂ᵢ² on ℂ[x₁, …, xₙ]. -/
noncomputable def laplacian (n : ℕ) :
    MvPolynomial (Fin n) ℂ → MvPolynomial (Fin n) ℂ :=
  fun p => ∑ i : Fin n, pderiv i (pderiv i p)

/-- Zhao's vanishing conjecture in dimension `n` ([Zhao]): if Δᵐ(Pᵐ) = 0 for all m ≥ 1,
then Δᵐ(Pᵐ⁺¹) = 0 for all sufficiently large m. -/
def ZhaoVanishingStatement (n : ℕ) : Prop :=
  ∀ P : MvPolynomial (Fin n) ℂ,
    (∀ m : ℕ, 0 < m → (laplacian n)^[m] (P ^ m) = 0) →
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m → (laplacian n)^[m] (P ^ (m + 1)) = 0

/-- [BRIDGE, OPEN HERE] Zhao's equivalence ([Zhao], Thm 1.1 combined with the
Hessian-nilpotency reduction): the vanishing conjecture in all dimensions implies the
Jacobian conjecture in all dimensions — in particular in dimension 3. NOT proved here. -/
theorem zhao_vanishing_implies_jacobian :
    (∀ n : ℕ, ZhaoVanishingStatement n) → JacobianStatement 3 := by
  sorry

/-- [CONDITIONAL] Granting the [Zhao] bridge, the vanishing conjecture fails in some
dimension. Sorry-free contrapositive. -/
theorem zhao_vanishing_false_of_bridge
    (bridge : (∀ n : ℕ, ZhaoVanishingStatement n) → JacobianStatement 3) :
    ¬ (∀ n : ℕ, ZhaoVanishingStatement n) :=
  fun hz => jacobian_statement_false_dim3 (bridge hz)

/-! ## Bass–Connell–Wright / Drużkowski cubic reduction -/

/-- The Jacobian statement restricted to maps of the special form `X i + H i` with each
`H i` homogeneous of degree 3 ([BCW] reduction target). -/
def CubicHomogeneousJacobianStatement (n : ℕ) : Prop :=
  ∀ H : Fin n → MvPolynomial (Fin n) ℂ,
    (∀ i, (H i).IsHomogeneous 3) →
    IsUnit (Matrix.of fun i j => pderiv i (X j + H j)).det →
    ∃ G : Fin n → MvPolynomial (Fin n) ℂ,
      (fun i => bind₁ G (X i + H i)) = X ∧ (fun i => bind₁ (fun k => X k + H k) (G i)) = X

/-- [BRIDGE, OPEN HERE] The [BCW] degree-reduction theorem: if the cubic-homogeneous
Jacobian statement holds in every dimension, the full Jacobian conjecture holds in every
dimension — in particular in dimension 3. NOT proved here. -/
theorem cubic_reduction :
    (∀ N : ℕ, CubicHomogeneousJacobianStatement N) → JacobianStatement 3 := by
  sorry

/-- [CONDITIONAL] Granting [BCW], there EXISTS a dimension in which even the
cubic-homogeneous form of the conjecture fails — i.e., Alpöge's map forces a
cubic-homogeneous counterexample somewhere. Sorry-free contrapositive. -/
theorem cubic_counterexample_exists_of_bridge
    (bridge : (∀ N : ℕ, CubicHomogeneousJacobianStatement N) → JacobianStatement 3) :
    ¬ (∀ N : ℕ, CubicHomogeneousJacobianStatement N) :=
  fun hc => jacobian_statement_false_dim3 (bridge hc)

/-! ## Canonical Poisson conjecture -/

/-- The canonical Poisson bracket on ℂ[x₁,x₂,x₃,p₁,p₂,p₃] (rank 3): position variables
are `Sum.inl i`, momenta `Sum.inr i`, and {f, g} = Σᵢ (∂f/∂xᵢ·∂g/∂pᵢ − ∂f/∂pᵢ·∂g/∂xᵢ). -/
noncomputable def poissonBracket
    (f g : MvPolynomial (Fin 3 ⊕ Fin 3) ℂ) : MvPolynomial (Fin 3 ⊕ Fin 3) ℂ :=
  ∑ i : Fin 3,
    (pderiv (Sum.inl i) f * pderiv (Sum.inr i) g -
     pderiv (Sum.inr i) f * pderiv (Sum.inl i) g)

/-- The canonical (rank-3) Poisson conjecture: every ℂ-algebra endomorphism of the
polynomial algebra that preserves the canonical bracket is bijective. See
Adjamagbo–van den Essen (arXiv:math/0608009) for the stable equivalences among the
Jacobian, Poisson, and Dixmier conjectures. -/
def PoissonStatement : Prop :=
  ∀ φ : MvPolynomial (Fin 3 ⊕ Fin 3) ℂ →ₐ[ℂ] MvPolynomial (Fin 3 ⊕ Fin 3) ℂ,
    (∀ f g, φ (poissonBracket f g) = poissonBracket (φ f) (φ g)) →
    Function.Bijective φ

/-- [CONDITIONAL] Granting the bridge Poisson ⟹ Jacobian (dimension 3) — realized
concretely by the polynomial cotangent lift (x,p) ↦ (U(x), (Jac U)⁻ᵀ p) of any
noninjective Keller map, whose bracket preservation and non-surjectivity are the
content of the construction — the canonical Poisson conjecture is FALSE in rank 3.
Sorry-free contrapositive. -/
theorem poisson_false_of_bridge
    (bridge : PoissonStatement → JacobianStatement 3) :
    ¬ PoissonStatement :=
  fun hp => jacobian_statement_false_dim3 (bridge hp)

/-! ## Mathieu subspaces and Zhao's Image Conjecture -/

/-- Zhao's Mathieu-subspace property for a ℂ-submodule M of a commutative ℂ-algebra:
whenever all powers fᵐ (m ≥ 1) lie in M, every multiple g·fᵐ lies in M for m large. -/
def IsMathieuSubspace {A : Type*} [CommRing A] [Algebra ℂ A]
    (M : Submodule ℂ A) : Prop :=
  ∀ f : A, (∀ m : ℕ, 0 < m → f ^ m ∈ M) →
    ∀ g : A, ∃ N : ℕ, ∀ m : ℕ, N ≤ m → g * f ^ m ∈ M

/-- The image subspace of Zhao's Image Conjecture in 2n variables: the sum of the
ranges of the commuting operators Θᵢ = ∂/∂Zᵢ − ξᵢ (Z variables `Sum.inl`, ξ variables
`Sum.inr`). -/
noncomputable def zhaoImage (n : ℕ) :
    Submodule ℂ (MvPolynomial (Fin n ⊕ Fin n) ℂ) :=
  ⨆ i : Fin n,
    LinearMap.range
      ((pderiv (Sum.inl i)).toLinearMap -
        LinearMap.mulLeft ℂ (X (Sum.inr i)))

/-- Zhao's Image Conjecture in 2n variables (arXiv:0902.0210): `zhaoImage n` is a
Mathieu subspace. -/
def ZhaoImageStatement (n : ℕ) : Prop := IsMathieuSubspace (zhaoImage n)

/-- [CONDITIONAL] Granting the bridge (Image Conjecture in all sizes ⟹ Jacobian in
dimension 3, via Zhao's image/inversion identities applied to a cubic-homogeneous
reduction of the counterexample), the Image Conjecture fails for some n — with the
intended concrete witness M = zhaoImage 23, p = Σ ξᵢHᵢ(Z), g = Z₁ from the
23-variable Yagzhev lift of the 11-variable cubic reduction certificate.
Sorry-free contrapositive. -/
theorem zhao_image_false_of_bridge
    (bridge : (∀ n : ℕ, ZhaoImageStatement n) → JacobianStatement 3) :
    ¬ (∀ n : ℕ, ZhaoImageStatement n) :=
  fun hz => jacobian_statement_false_dim3 (bridge hz)

/-! ## Mathieu's conjecture

Mathieu's conjecture ([Mat]) concerns G-finite functions on compact connected real Lie
groups: if the Haar integral of every power `fⁿ` of a G-finite function `f` vanishes,
then for every G-finite `g` the integrals of `g·fⁿ` vanish for large `n`. Mathieu proved
it implies the Jacobian conjecture, so the counterexample refutes it (given that bridge).
Current Mathlib lacks the representation-theoretic vocabulary (G-finite functions under
both translation actions, Peter–Weyl decomposition) to state it faithfully in a few
lines; rather than formalize a strawman we record it in prose and leave its statement as
future work. -/

end JacobianCollateral
