import Mathlib

/-!
# Erdős #647 — budget-parametric terminal-leaf framework (Engine A, layer 2)

Repository-level module (2026-07-16, revised same day after structural
review): the symbolic data layer of the cross-shift terminal-leaf
incompatibility program. This file is compiled from clean source through
the pinned lean-checker toolchain (`lake env lean`, Lean 4.32.0-rc1,
pinned Mathlib) — repository-level kernel evidence, deliberately NOT
misrepresented as a tracked episode. The standalone theorems it packages
were additionally proved through tracked proof-search episodes as
self-contained statements; see
`Erdos647_AffineDeterminantInteraction.lean`,
`Erdos647_ForcedFactorPrimeBound.lean`,
`Erdos647_Shift16LeafFrontierExclusions.lean`, and
`Erdos647_GenericLeafExclusionEngine.lean` for episode provenance.

Design requirements (locked program, 2026-07-16, plus structural review):
- every terminal leaf carries enough SYMBOLIC data for automatic
  comparison — not a shift number plus prose;
- the candidate implication lives in a separate realization `Prop`
  (`CandidateRealizesLeaf`), never an opaque field;
- everything is BUDGET-PARAMETRIC: `LeafType.excess` and
  `SurvivesWithExcess` carry a variable excess `B` (the main declaration
  is `B = 2`; the limit declaration needs every `B` eventually);
- branch parameterization is WELL-TYPED: `Parameterization` is a sum
  type and `ResidueClass` carries its validity proofs, so malformed
  modulus/residue states are unrepresentable;
- incompatibility is a UNIVERSAL statement (`IncompatibleLeaves`:
  no parameter realizes both), distinct from the trivially-satisfied
  joint-realizability property; the graph layer operates on
  `PairwiseCompatibleSelection` independently of knowing a parameter,
  and `realizes_implies_pairwise_compatible` is the connecting theorem;
- the bridge from exclusion rows to graph edges is
  `forced_residue_conflicts_with_exclusion`: a leaf FORCING a residue
  meets a leaf EXCLUDING that residue and yields an incompatibility
  edge. A unary exclusion row alone draws no edge — the all-avoid
  obstruction warns that avoidance conditions can remain jointly
  satisfiable.
-/

namespace Erdos647

/-- An affine form `coeff · t + const` over ℤ, the host object of every
terminal-leaf demand. -/
structure AffineForm where
  coeff : ℤ
  const : ℤ
  deriving Repr, DecidableEq

/-- Evaluate an affine form at an integer parameter. -/
def AffineForm.eval (L : AffineForm) (t : ℤ) : ℤ :=
  L.coeff * t + L.const

/-- The determinant of two affine forms — the universal pairwise
interaction invariant. -/
def AffineForm.det (L₁ L₂ : AffineForm) : ℤ :=
  L₁.coeff * L₂.const - L₂.coeff * L₁.const

/-- Any common divisor of two affine values divides the determinant
(structure-level restatement of `erdos647_affine_determinant_interaction`,
tracked episode `c31387c9-0f87-40d0-8b0a-fa43451c333a`). -/
theorem AffineForm.dvd_det {L₁ L₂ : AffineForm} {t g : ℤ}
    (h₁ : g ∣ L₁.eval t) (h₂ : g ∣ L₂.eval t) : g ∣ L₁.det L₂ := by
  have ha : g ∣ L₁.coeff * (L₂.coeff * t + L₂.const) := Dvd.dvd.mul_left h₂ L₁.coeff
  have hc : g ∣ L₂.coeff * (L₁.coeff * t + L₁.const) := Dvd.dvd.mul_left h₁ L₂.coeff
  have h3 : g ∣ L₁.coeff * (L₂.coeff * t + L₂.const) -
      L₂.coeff * (L₁.coeff * t + L₁.const) := dvd_sub ha hc
  have h4 : L₁.coeff * (L₂.coeff * t + L₂.const) -
      L₂.coeff * (L₁.coeff * t + L₁.const) = L₁.det L₂ := by
    unfold AffineForm.det; ring
  rwa [h4] at h3

/-- Unit determinant forces coprime values: the pair can be removed from
collision search. -/
theorem AffineForm.dvd_one_of_det_unit {L₁ L₂ : AffineForm} {t g : ℤ}
    (hdet : L₁.det L₂ = 1 ∨ L₁.det L₂ = -1)
    (h₁ : g ∣ L₁.eval t) (h₂ : g ∣ L₂.eval t) : g ∣ 1 := by
  have h := AffineForm.dvd_det h₁ h₂
  rcases hdet with h1 | h1
  · rwa [h1] at h
  · rw [h1] at h
    exact (dvd_neg.mp h)

/-- Arithmetic shape demanded of a cofactor value. Separated from the
form so the catalog stays symbolic. `divisibleBy b e` is raw divisibility
by `b ^ e` for an ARBITRARY base `b` (no primality is implied by the
constructor); `primePower` requires a positive exponent, so `1` does not
qualify. -/
inductive CofactorShape where
  | prime : CofactorShape
  | composite : CofactorShape
  | sigmaLE (B : ℕ) : CofactorShape
  | omegaLE (r : ℕ) : CofactorShape
  | divisibleBy (b e : ℕ) : CofactorShape
  | primeTimesPrime : CofactorShape
  | primePower : CofactorShape
  deriving Repr, DecidableEq

/-- Semantics of a shape demand on a natural cofactor value. -/
def CofactorShape.Holds : CofactorShape → ℕ → Prop
  | .prime, m => Nat.Prime m
  | .composite, m => 1 < m ∧ ¬ Nat.Prime m
  | .sigmaLE B, m => ArithmeticFunction.sigma 0 m ≤ B
  | .omegaLE r, m => m.primeFactors.card ≤ r
  | .divisibleBy b e, m => b ^ e ∣ m
  | .primeTimesPrime, m => ∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ m = p * q
  | .primePower, m => ∃ p e, Nat.Prime p ∧ 0 < e ∧ m = p ^ e

/-- A well-formed residue class: validity is carried in the type, so
mismatched or out-of-range modulus/residue states are unrepresentable. -/
structure ResidueClass where
  modulus : ℕ
  residue : ℕ
  modulus_pos : 0 < modulus
  residue_lt : residue < modulus

/-- How a leaf's own parameter relates to the master parameter `N`
(`n = 2520·N`): either directly (`t = N`) or through a residue class
(`N = modulus·t + residue`). -/
inductive Parameterization where
  | direct : Parameterization
  | residueClass (rc : ResidueClass) : Parameterization

/-- The two Hughes prime-chain families (Stage-2 reduction). -/
inductive PrimeChainFamily where
  | familyA : PrimeChainFamily
  | familyB : PrimeChainFamily
  deriving Repr, DecidableEq

/-- A terminal leaf: one fully symbolic escape branch of a shift's p-adic
classification. `excess` makes the budget variable — the main Erdős #647
declaration is `excess = 2`; the limit declaration quantifies over all
excesses. -/
structure LeafType where
  shift : ℕ
  excess : ℕ
  form : AffineForm
  shape : CofactorShape
  param : Parameterization
  family : Option PrimeChainFamily

/-- Realization: the candidate master parameter `N` satisfies the leaf's
branch parameterization and its shape demand on the evaluated form. Kept
as a separate `Prop` (a certificate obligation), never an opaque field. -/
def CandidateRealizesLeaf (N : ℕ) (leaf : LeafType) : Prop :=
  match leaf.param with
  | .direct =>
      0 < leaf.form.eval N ∧ leaf.shape.Holds (leaf.form.eval N).toNat
  | .residueClass rc =>
      ∃ t : ℕ, N = rc.modulus * t + rc.residue ∧ 0 < leaf.form.eval t ∧
        leaf.shape.Holds (leaf.form.eval t).toNat

/-- Budget-parametric survival through a window of depth `D` with excess
`B`: every shift keeps its budget `B + k`. The main declaration is
`B = 2`; the square-root prefix reduction sets `D = 2·√n`. -/
def SurvivesWithExcess (n D B : ℕ) : Prop :=
  ∀ k, 0 < k → k ≤ D → k < n →
    ArithmeticFunction.sigma 0 (n - k) ≤ B + k

/-! ## The incompatibility graph layer

`IncompatibleLeaves` is the SEMANTIC edge: no master parameter realizes
both leaves. The graph search operates on selections that avoid certified
edges, independently of already knowing a parameter;
`realizes_implies_pairwise_compatible` connects an actual candidate back
to the graph. An absent edge means "not yet certified incompatible",
never "proved compatible". -/

/-- Semantic incompatibility: no master parameter realizes both leaves. -/
def IncompatibleLeaves (A B : LeafType) : Prop :=
  ∀ N : ℕ, ¬ (CandidateRealizesLeaf N A ∧ CandidateRealizesLeaf N B)

/-- A leaf selection with no two members certified incompatible. -/
def PairwiseCompatibleSelection (selected : List LeafType) : Prop :=
  selected.Pairwise fun A B => ¬ IncompatibleLeaves A B

/-- A master parameter realizes every leaf of a selection. -/
def RealizesLeafSelection (N : ℕ) (selected : List LeafType) : Prop :=
  ∀ L ∈ selected, CandidateRealizesLeaf N L

/-- A realized selection is pairwise compatible: the graph constraint is
a genuine necessary condition on candidates. -/
theorem realizes_implies_pairwise_compatible {N : ℕ} {selected : List LeafType}
    (h : RealizesLeafSelection N selected) :
    PairwiseCompatibleSelection selected := by
  induction selected with
  | nil => exact List.Pairwise.nil
  | cons hd tl ih =>
    refine List.Pairwise.cons ?_ (ih ?_)
    · intro B hB hinc
      exact hinc N ⟨h hd List.mem_cons_self, h B (List.mem_cons_of_mem hd hB)⟩
    · intro L hL
      exact h L (List.mem_cons_of_mem hd hL)

/-- A candidate realizes one leaf from every applicable shift of a
prefix. The pairwise-compatibility consequence is NOT restated here (it
follows from `realizes_implies_pairwise_compatible` applied to the list
of chosen leaves); the graph works with selections directly. -/
def RealizesPrefixLeaves (N D : ℕ) (leavesAt : ℕ → List LeafType) : Prop :=
  ∃ choice : ℕ → LeafType,
    ∀ k, 0 < k → k ≤ D → choice k ∈ leavesAt k ∧
      CandidateRealizesLeaf N (choice k)

/-! ## The exclusion-row → edge bridge

A unary exclusion row ("leaf B cannot occur at `N ≡ r (mod p)`") becomes
a pairwise edge only against a leaf that FORCES that residue. -/

/-- Leaf `A` forces the master parameter into residue `r` mod `p`. -/
def ForcesResidue (A : LeafType) (p r : ℕ) : Prop :=
  ∀ N : ℕ, CandidateRealizesLeaf N A → N % p = r

/-- Leaf `B` is unrealizable on residue `r` mod `p`. -/
def ExcludesResidue (B : LeafType) (p r : ℕ) : Prop :=
  ∀ N : ℕ, N % p = r → ¬ CandidateRealizesLeaf N B

/-- The central bridge from the exclusion-row catalog to the graph: a
forced residue meeting an exclusion on the same residue is an
incompatibility edge. -/
theorem forced_residue_conflicts_with_exclusion {A B : LeafType} {p r : ℕ}
    (hf : ForcesResidue A p r) (he : ExcludesResidue B p r) :
    IncompatibleLeaves A B := by
  intro N hAB
  exact he N (hf N hAB.1) hAB.2

/-! ## Concrete catalog: the two shift-16 residual leaves

From `Erdos647_Shift16ResidualTermination.lean` (kernel-verified): the
`M % 8 = 3` branch of the shift-16 classification terminates in exactly
two prime-producing leaves. In the master parameter (family A even
branch, `N = 2M`):

- leaf A: `M = 16Q+11`, so `N = 32Q+22`, forced prime `630Q+433`
  (`= (315N−2)/16`);
- leaf B: `M = 32R+3`, so `N = 64R+6`, forced prime `630R+59`
  (`= (315N−2)/32`).
-/

/-- Shift-16 residual leaf A: `N = 32Q+22`, `630Q+433` prime. -/
def shift16LeafA : LeafType :=
  ⟨16, 2, ⟨630, 433⟩, .prime, .residueClass ⟨32, 22, by norm_num, by norm_num⟩,
    some .familyA⟩

/-- Shift-16 residual leaf B: `N = 64R+6`, `630R+59` prime. -/
def shift16LeafB : LeafType :=
  ⟨16, 2, ⟨630, 59⟩, .prime, .residueClass ⟨64, 6, by norm_num, by norm_num⟩,
    some .familyA⟩

/-! ## Layer-2 frontier exclusions inside the residual branch

Branch-parameter rows (tracked episode `b16a33ea-da54-45a7-9abf-447badd35748`):
leaf A dies at `Q ≡ 6 (11), 8 (13), 9 (17), 14 (19)`; leaf B at
`R ≡ 6 (11), 1 (13), 9 (17), 12 (19)`.

Pushed to the MASTER parameter the two leaves' rows coincide —
`N ≡ 5 (11), 5 (13), 4 (17), 14 (19)` — because both leaf values are
`(315N−2)/2^k`, so the exclusions genuinely attach to the shift-16 HOST
form `315N−2` and are inherited by every leaf of its branch. Master-level
rows are what `ExcludesResidue` (hence the graph) consumes. -/

/-- Leaf A is unrealizable whenever its branch parameter hits any of the
four frontier-prime bad residues. -/
theorem shift16LeafA_frontier_exclusion (N t : ℕ)
    (hN : N = 32 * t + 22)
    (ht : t % 11 = 6 ∨ t % 13 = 8 ∨ t % 17 = 9 ∨ t % 19 = 14) :
    ¬ CandidateRealizesLeaf N shift16LeafA := by
  intro hreal
  have hreal' : ∃ u : ℕ, N = 32 * u + 22 ∧ 0 < ((630:ℤ) * u + 433) ∧
      Nat.Prime (((630:ℤ) * u + 433).toNat) := hreal
  obtain ⟨u, hu, hpos, hprime⟩ := hreal'
  have huu : u = t := by omega
  subst huu
  have heval : (((630:ℤ) * u + 433)).toNat = 630 * u + 433 := by omega
  rw [heval] at hprime
  have key : ∀ (p w : ℕ), 1 < p → 630 * u + 433 = p * w → p < 630 * u + 433 → False := by
    intro p w h1 h2 h3
    have hdvd : p ∣ 630 * u + 433 := ⟨w, h2⟩
    rcases hprime.eq_one_or_self_of_dvd p hdvd with h4 | h4 <;> omega
  rcases ht with h | h | h | h
  · obtain ⟨m, rfl⟩ : ∃ m, u = 11 * m + 6 := ⟨u / 11, by omega⟩
    exact key 11 (630 * m + 383) (by omega) (by ring) (by omega)
  · obtain ⟨m, rfl⟩ : ∃ m, u = 13 * m + 8 := ⟨u / 13, by omega⟩
    exact key 13 (630 * m + 421) (by omega) (by ring) (by omega)
  · obtain ⟨m, rfl⟩ : ∃ m, u = 17 * m + 9 := ⟨u / 17, by omega⟩
    exact key 17 (630 * m + 359) (by omega) (by ring) (by omega)
  · obtain ⟨m, rfl⟩ : ∃ m, u = 19 * m + 14 := ⟨u / 19, by omega⟩
    exact key 19 (630 * m + 487) (by omega) (by ring) (by omega)

/-- Leaf B is unrealizable whenever its branch parameter hits any of the
four frontier-prime bad residues. -/
theorem shift16LeafB_frontier_exclusion (N t : ℕ)
    (hN : N = 64 * t + 6)
    (ht : t % 11 = 6 ∨ t % 13 = 1 ∨ t % 17 = 9 ∨ t % 19 = 12) :
    ¬ CandidateRealizesLeaf N shift16LeafB := by
  intro hreal
  have hreal' : ∃ u : ℕ, N = 64 * u + 6 ∧ 0 < ((630:ℤ) * u + 59) ∧
      Nat.Prime (((630:ℤ) * u + 59).toNat) := hreal
  obtain ⟨u, hu, hpos, hprime⟩ := hreal'
  have huu : u = t := by omega
  subst huu
  have heval : (((630:ℤ) * u + 59)).toNat = 630 * u + 59 := by omega
  rw [heval] at hprime
  have key : ∀ (p w : ℕ), 1 < p → 630 * u + 59 = p * w → p < 630 * u + 59 → False := by
    intro p w h1 h2 h3
    have hdvd : p ∣ 630 * u + 59 := ⟨w, h2⟩
    rcases hprime.eq_one_or_self_of_dvd p hdvd with h4 | h4 <;> omega
  rcases ht with h | h | h | h
  · obtain ⟨m, rfl⟩ : ∃ m, u = 11 * m + 6 := ⟨u / 11, by omega⟩
    exact key 11 (630 * m + 349) (by omega) (by ring) (by omega)
  · obtain ⟨m, rfl⟩ : ∃ m, u = 13 * m + 1 := ⟨u / 13, by omega⟩
    exact key 13 (630 * m + 53) (by omega) (by ring) (by omega)
  · obtain ⟨m, rfl⟩ : ∃ m, u = 17 * m + 9 := ⟨u / 17, by omega⟩
    exact key 17 (630 * m + 337) (by omega) (by ring) (by omega)
  · obtain ⟨m, rfl⟩ : ∃ m, u = 19 * m + 12 := ⟨u / 19, by omega⟩
    exact key 19 (630 * m + 401) (by omega) (by ring) (by omega)

/-- Master-parameter exclusion rows, shared by BOTH shift-16 leaves
(the rows attach to the host form `315N−2`): neither leaf is realizable
at `N ≡ 5 (11), 5 (13), 4 (17), 14 (19)`. -/
theorem shift16_master_exclusions (N : ℕ)
    (h : N % 11 = 5 ∨ N % 13 = 5 ∨ N % 17 = 4 ∨ N % 19 = 14) :
    ¬ CandidateRealizesLeaf N shift16LeafA ∧
    ¬ CandidateRealizesLeaf N shift16LeafB := by
  constructor
  · intro hreal
    have hreal' : ∃ u : ℕ, N = 32 * u + 22 ∧ 0 < ((630:ℤ) * u + 433) ∧
        Nat.Prime (((630:ℤ) * u + 433).toNat) := hreal
    obtain ⟨u, hu, _, _⟩ := hreal'
    have ht : u % 11 = 6 ∨ u % 13 = 8 ∨ u % 17 = 9 ∨ u % 19 = 14 := by
      rcases h with h | h | h | h
      · left; omega
      · right; left; omega
      · right; right; left; omega
      · right; right; right; omega
    exact shift16LeafA_frontier_exclusion N u hu ht hreal
  · intro hreal
    have hreal' : ∃ u : ℕ, N = 64 * u + 6 ∧ 0 < ((630:ℤ) * u + 59) ∧
        Nat.Prime (((630:ℤ) * u + 59).toNat) := hreal
    obtain ⟨u, hu, _, _⟩ := hreal'
    have ht : u % 11 = 6 ∨ u % 13 = 1 ∨ u % 17 = 9 ∨ u % 19 = 12 := by
      rcases h with h | h | h | h
      · left; omega
      · right; left; omega
      · right; right; left; omega
      · right; right; right; omega
    exact shift16LeafB_frontier_exclusion N u hu ht hreal

/-- Graph-facing packaging: leaf A excludes master residue 5 mod 11. -/
theorem shift16LeafA_excludesResidue_11_5 : ExcludesResidue shift16LeafA 11 5 :=
  fun N h5 => (shift16_master_exclusions N (Or.inl h5)).1

/-- Graph-facing packaging: leaf B excludes master residue 5 mod 11. -/
theorem shift16LeafB_excludesResidue_11_5 : ExcludesResidue shift16LeafB 11 5 :=
  fun N h5 => (shift16_master_exclusions N (Or.inl h5)).2

end Erdos647
