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
qualify. `unresolved` is the HONEST marker for residual branches: the
classification proves the candidate enters this residue branch, but no
terminal arithmetic shape has yet been extracted — such leaves are
universal escape vertices, and the audit must report them separately;
a growing-prefix contradiction cannot succeed while every shift can
escape through one. -/
inductive CofactorShape where
  | unresolved : CofactorShape
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
  | .unresolved, _ => True
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

/-! ## The finite leaf catalog (milestone 6)

Executable identity is kept SEPARATE from proof-carrying semantics:
`LeafId` is a proof-free enumeration (stable names for dossier output,
audit tables, and future hyperedges) and `leafOfId` is the lookup into
the typed catalog. The Boolean edge certifier operates on `LeafId`; its
soundness theorem connects back to the semantic `IncompatibleLeaves`.

Shift 8 is included alongside 13–16 because its two leaves parameterize
by the PARITY of `N` — which the shift-16 residual leaves force — giving
the first genuine cross-shift certified edges.

Leaf normalization notes (weakenings are sound for both completeness and
edges — a weaker leaf is realizable in more cases, so the frontier
disjunction still implies realization, and incompatibility of a weaker
leaf implies incompatibility of the stronger one):
- side conditions of the form `t % p ≠ r` are not representable in
  `Parameterization` and are dropped (e.g. shift 15's `M % 5 ≠ 1`);
- shift 14's prime leaf splits into SIX variants, one per `N % 49` class
  `7j+3` (`j = 1..6`), since the class determines the leaf's affine form
  `1260·t + (180j+77)` exactly;
- residual branches carry `CofactorShape.unresolved` and a trivial
  positive form `⟨0, 1⟩` — pure congruence leaves, honest escape
  vertices;
- `LeavesAtShift 16` lists only the two `M % 8 = 3` family-A residual
  leaves currently normalized; NO completeness theorem is claimed for
  shift 16 until the remaining branches of its classification are
  normalized. -/

/-- Proof-free stable identifiers for the finite leaf catalog. -/
inductive LeafId where
  | shift8Prime | shift8SemiPrime
  | shift13Free | shift13Cofactor | shift13Residual
  | shift14Base
  | shift14Prime0 | shift14Prime1 | shift14Prime2
  | shift14Prime3 | shift14Prime4 | shift14Prime5
  | shift14Residual
  | shift15Base | shift15PrimeA | shift15PrimeB | shift15Residual
  | shift16A | shift16B
  deriving Repr, DecidableEq

/-- Lookup from stable identity into the typed catalog. -/
def leafOfId : LeafId → LeafType
  | .shift8Prime =>
      ⟨8, 2, ⟨630, -1⟩, .prime, .residueClass ⟨2, 0, by norm_num, by norm_num⟩, none⟩
  | .shift8SemiPrime =>
      ⟨8, 2, ⟨315, 157⟩, .prime, .residueClass ⟨2, 1, by norm_num, by norm_num⟩, none⟩
  | .shift13Free =>
      ⟨13, 2, ⟨2520, -13⟩, .sigmaLE 15, .direct, none⟩
  | .shift13Cofactor =>
      ⟨13, 2, ⟨2520, -1⟩, .sigmaLE 7, .residueClass ⟨13, 0, by norm_num, by norm_num⟩, none⟩
  | .shift13Residual =>
      ⟨13, 2, ⟨0, 1⟩, .unresolved, .residueClass ⟨169, 78, by norm_num, by norm_num⟩, none⟩
  | .shift14Base =>
      ⟨14, 2, ⟨180, -1⟩, .sigmaLE 4, .direct, none⟩
  | .shift14Prime0 =>
      ⟨14, 2, ⟨1260, 257⟩, .prime, .residueClass ⟨49, 10, by norm_num, by norm_num⟩, none⟩
  | .shift14Prime1 =>
      ⟨14, 2, ⟨1260, 437⟩, .prime, .residueClass ⟨49, 17, by norm_num, by norm_num⟩, none⟩
  | .shift14Prime2 =>
      ⟨14, 2, ⟨1260, 617⟩, .prime, .residueClass ⟨49, 24, by norm_num, by norm_num⟩, none⟩
  | .shift14Prime3 =>
      ⟨14, 2, ⟨1260, 797⟩, .prime, .residueClass ⟨49, 31, by norm_num, by norm_num⟩, none⟩
  | .shift14Prime4 =>
      ⟨14, 2, ⟨1260, 977⟩, .prime, .residueClass ⟨49, 38, by norm_num, by norm_num⟩, none⟩
  | .shift14Prime5 =>
      ⟨14, 2, ⟨1260, 1157⟩, .prime, .residueClass ⟨49, 45, by norm_num, by norm_num⟩, none⟩
  | .shift14Residual =>
      ⟨14, 2, ⟨0, 1⟩, .unresolved, .residueClass ⟨49, 3, by norm_num, by norm_num⟩, none⟩
  | .shift15Base =>
      ⟨15, 2, ⟨168, -1⟩, .sigmaLE 4, .direct, none⟩
  | .shift15PrimeA =>
      ⟨15, 2, ⟨168, 67⟩, .prime, .residueClass ⟨5, 2, by norm_num, by norm_num⟩, none⟩
  | .shift15PrimeB =>
      ⟨15, 2, ⟨168, 47⟩, .prime, .residueClass ⟨25, 7, by norm_num, by norm_num⟩, none⟩
  | .shift15Residual =>
      ⟨15, 2, ⟨0, 1⟩, .unresolved, .residueClass ⟨125, 32, by norm_num, by norm_num⟩, none⟩
  | .shift16A => shift16LeafA
  | .shift16B => shift16LeafB

/-- The catalog, grouped by shift. -/
def LeavesAtShift : ℕ → List LeafId
  | 8 => [.shift8Prime, .shift8SemiPrime]
  | 13 => [.shift13Free, .shift13Cofactor, .shift13Residual]
  | 14 => [.shift14Base, .shift14Prime0, .shift14Prime1, .shift14Prime2,
           .shift14Prime3, .shift14Prime4, .shift14Prime5, .shift14Residual]
  | 15 => [.shift15Base, .shift15PrimeA, .shift15PrimeB, .shift15Residual]
  | 16 => [.shift16A, .shift16B]
  | _ => []

/-! ## The Boolean edge certifier

Certificates carry their reason. An absent edge means "not yet certified
incompatible", never "proved compatible". The first implemented reason is
`impossibleParameterizations`: two residue-class parameterizations with
no common master parameter (CRT solvability failure at the gcd). -/

/-- Why a pair of leaves is certified incompatible. -/
inductive EdgeReason where
  | impossibleParameterizations : EdgeReason
  | forcedExcludedResidue (p r : ℕ) : EdgeReason
  | primeForcedFactor (p : ℕ) : EdgeReason
  | contradictoryShapes : EdgeReason
  deriving Repr, DecidableEq

/-- Two residue classes admit no common value exactly when their residues
disagree modulo the gcd of the moduli. -/
def ResidueClass.conflicts (rc1 rc2 : ResidueClass) : Bool :=
  rc1.residue % Nat.gcd rc1.modulus rc2.modulus !=
    rc2.residue % Nat.gcd rc1.modulus rc2.modulus

/-- Parameterization-level conflict check. -/
def paramConflict : Parameterization → Parameterization → Bool
  | .residueClass rc1, .residueClass rc2 => rc1.conflicts rc2
  | _, _ => false

/-- Edge lookup with reason. Currently only the parameterization channel
is implemented; `forcedExcludedResidue`, `primeForcedFactor`, and
`contradictoryShapes` are reserved for the next catalog passes. -/
def edgeReason (A B : LeafId) : Option EdgeReason :=
  if paramConflict (leafOfId A).param (leafOfId B).param then
    some .impossibleParameterizations
  else none

/-- The executable edge certificate. -/
def certifiedIncompatible (A B : LeafId) : Bool :=
  (edgeReason A B).isSome

/-- A conflicting pair of residue classes shares no value. -/
theorem no_common_value_of_conflicts {rc1 rc2 : ResidueClass}
    (h : rc1.conflicts rc2 = true) (N : ℕ)
    (h1 : ∃ t, N = rc1.modulus * t + rc1.residue)
    (h2 : ∃ t, N = rc2.modulus * t + rc2.residue) : False := by
  obtain ⟨t1, ht1⟩ := h1
  obtain ⟨t2, ht2⟩ := h2
  obtain ⟨w1, hw1⟩ : Nat.gcd rc1.modulus rc2.modulus ∣ rc1.modulus * t1 :=
    dvd_mul_of_dvd_left (Nat.gcd_dvd_left _ _) t1
  obtain ⟨w2, hw2⟩ : Nat.gcd rc1.modulus rc2.modulus ∣ rc2.modulus * t2 :=
    dvd_mul_of_dvd_left (Nat.gcd_dvd_right _ _) t2
  have hN1 : N % Nat.gcd rc1.modulus rc2.modulus =
      rc1.residue % Nat.gcd rc1.modulus rc2.modulus := by
    rw [ht1, hw1]
    exact Nat.mul_add_mod _ _ _
  have hN2 : N % Nat.gcd rc1.modulus rc2.modulus =
      rc2.residue % Nat.gcd rc1.modulus rc2.modulus := by
    rw [ht2, hw2]
    exact Nat.mul_add_mod _ _ _
  have hne : rc1.residue % Nat.gcd rc1.modulus rc2.modulus ≠
      rc2.residue % Nat.gcd rc1.modulus rc2.modulus := by
    simpa [ResidueClass.conflicts] using h
  omega

/-- Project the branch equation out of a residue-class realization. -/
theorem realizes_residueClass_param {N : ℕ} {leaf : LeafType} {rc : ResidueClass}
    (hp : leaf.param = .residueClass rc)
    (h : CandidateRealizesLeaf N leaf) :
    ∃ t, N = rc.modulus * t + rc.residue := by
  unfold CandidateRealizesLeaf at h
  rw [hp] at h
  obtain ⟨t, ht, _, _⟩ := h
  exact ⟨t, ht⟩

/-- Soundness of the executable certificate: a certified edge is a
semantic incompatibility. -/
theorem certifiedIncompatible_sound {A B : LeafId}
    (h : certifiedIncompatible A B = true) :
    IncompatibleLeaves (leafOfId A) (leafOfId B) := by
  intro N hAB
  obtain ⟨hA, hB⟩ := hAB
  unfold certifiedIncompatible edgeReason at h
  by_cases hc : paramConflict (leafOfId A).param (leafOfId B).param = true
  · cases hpa : (leafOfId A).param with
    | direct => rw [hpa] at hc; simp [paramConflict] at hc
    | residueClass rc1 =>
      cases hpb : (leafOfId B).param with
      | direct => rw [hpa, hpb] at hc; simp [paramConflict] at hc
      | residueClass rc2 =>
        rw [hpa, hpb] at hc
        simp only [paramConflict] at hc
        exact no_common_value_of_conflicts hc N
          (realizes_residueClass_param hpa hA)
          (realizes_residueClass_param hpb hB)
  · simp [hc] at h

/-! ## Graph-level avoidance: the computationally usable necessary
condition on candidates. -/

/-- A selection avoiding every certified edge. -/
def AvoidsCertifiedEdges (selected : List LeafId) : Prop :=
  selected.Pairwise fun A B => certifiedIncompatible A B = false

/-- Any selection realized by one master parameter avoids every certified
edge — the graph constraint is a necessary condition on candidates. -/
theorem realized_selection_avoids_certified_edges {N : ℕ} {selected : List LeafId}
    (h : ∀ id ∈ selected, CandidateRealizesLeaf N (leafOfId id)) :
    AvoidsCertifiedEdges selected := by
  induction selected with
  | nil => exact List.Pairwise.nil
  | cons hd tl ih =>
    refine List.Pairwise.cons ?_ (ih fun id hid => h id (List.mem_cons_of_mem hd hid))
    intro B hB
    by_contra hcert
    have hcert' : certifiedIncompatible hd B = true := by
      revert hcert
      cases certifiedIncompatible hd B <;> simp
    exact certifiedIncompatible_sound hcert' N
      ⟨h hd List.mem_cons_self, h B (List.mem_cons_of_mem hd hB)⟩

/-! ## Catalog completeness (mapping form)

Each theorem maps the corresponding shift's kernel-verified frontier
disjunction (`candidate_shift13_adic_frontier`,
`candidate_shift14_seven_adic_frontier`,
`candidate_shift15_five_adic_frontier`, and the shift-8 classification)
onto the catalog: every disjunct realizes some listed leaf. Stated with
the frontier as a hypothesis so each remains self-contained and
composable with the already-verified frontier theorems at final
assembly (cross-file imports are not available to tracked replays). -/

/-- Shift 8: the classification's two branches land in the catalog. -/
theorem shift8_classification_realizes_catalog_leaf (N : ℕ) (hN : 1 ≤ N)
    (h : Nat.Prime (315 * N - 1) ∨ ∃ p, Nat.Prime p ∧ 315 * N - 1 = 2 * p) :
    ∃ id ∈ LeavesAtShift 8, CandidateRealizesLeaf N (leafOfId id) := by
  rcases Nat.even_or_odd N with ⟨t, ht⟩ | ⟨t, ht⟩
  · -- N = 2t: the value 630t−1 is odd, so the semiprime branch is impossible.
    refine ⟨.shift8Prime, by simp [LeavesAtShift], ?_⟩
    have hprime : Nat.Prime (315 * N - 1) := by
      rcases h with hp | ⟨p, hp, heq⟩
      · exact hp
      · exfalso; omega
    show ∃ u : ℕ, N = 2 * u + 0 ∧ 0 < ((630:ℤ) * u + (-1)) ∧
        Nat.Prime (((630:ℤ) * u + (-1)).toNat)
    refine ⟨t, by omega, by push_cast; omega, ?_⟩
    have heval : (((630:ℤ) * t + (-1))).toNat = 315 * N - 1 := by omega
    rwa [heval]
  · -- N = 2t+1: the value 630t+314 is even and exceeds 2, so it is 2·prime.
    refine ⟨.shift8SemiPrime, by simp [LeavesAtShift], ?_⟩
    obtain ⟨p, hp, heq⟩ : ∃ p, Nat.Prime p ∧ 315 * N - 1 = 2 * p := by
      rcases h with hp | hsp
      · exfalso
        have h2 : (2:ℕ) ∣ 315 * N - 1 := ⟨315 * t + 157, by omega⟩
        rcases hp.eq_one_or_self_of_dvd 2 h2 with h1 | h1 <;> omega
      · exact hsp
    show ∃ u : ℕ, N = 2 * u + 1 ∧ 0 < ((315:ℤ) * u + 157) ∧
        Nat.Prime (((315:ℤ) * u + 157).toNat)
    refine ⟨t, by omega, by positivity, ?_⟩
    have heval : (((315:ℤ) * t + 157)).toNat = p := by omega
    rwa [heval]

/-- Shift 13: the adic frontier's branches land in the catalog. -/
theorem shift13_frontier_realizes_catalog_leaf (N : ℕ) (hN : 1 ≤ N)
    (hbudget : ArithmeticFunction.sigma 0 (2520 * N - 13) ≤ 15)
    (h : ¬ 13 ∣ N ∨ ∃ M : ℕ, N = 13 * M ∧
      (M % 13 = 6 ∨ ArithmeticFunction.sigma 0 (2520 * M - 1) ≤ 7)) :
    ∃ id ∈ LeavesAtShift 13, CandidateRealizesLeaf N (leafOfId id) := by
  rcases h with _ | ⟨M, hM, hMres | hMcof⟩
  · refine ⟨.shift13Free, by simp [LeavesAtShift], ?_⟩
    show 0 < ((2520:ℤ) * N + (-13)) ∧
        ArithmeticFunction.sigma 0 (((2520:ℤ) * N + (-13)).toNat) ≤ 15
    have heval : (((2520:ℤ) * N + (-13))).toNat = 2520 * N - 13 := by omega
    exact ⟨by push_cast; omega, by rwa [heval]⟩
  · refine ⟨.shift13Residual, by simp [LeavesAtShift], ?_⟩
    obtain ⟨s, hs⟩ : ∃ s, M = 13 * s + 6 := ⟨M / 13, by omega⟩
    show ∃ u : ℕ, N = 169 * u + 78 ∧ 0 < ((0:ℤ) * u + 1) ∧ True
    exact ⟨s, by omega, by norm_num, trivial⟩
  · refine ⟨.shift13Cofactor, by simp [LeavesAtShift], ?_⟩
    have hMpos : 1 ≤ M := by omega
    show ∃ u : ℕ, N = 13 * u + 0 ∧ 0 < ((2520:ℤ) * u + (-1)) ∧
        ArithmeticFunction.sigma 0 (((2520:ℤ) * u + (-1)).toNat) ≤ 7
    have heval : (((2520:ℤ) * M + (-1))).toNat = 2520 * M - 1 := by omega
    exact ⟨M, by omega, by push_cast; omega, by rwa [heval]⟩

/-- Shift 15: the five-adic frontier's branches land in the catalog. -/
theorem shift15_frontier_realizes_catalog_leaf (N : ℕ) (hN : 1 ≤ N)
    (h : (N % 5 ≠ 2 ∧ ArithmeticFunction.sigma 0 (168 * N - 1) ≤ 4 ∧
          (168 * N - 1).primeFactors.card ≤ 2) ∨
        (∃ M : ℕ, N = 5 * M + 2 ∧ M % 5 ≠ 1 ∧ Nat.Prime (168 * M + 67)) ∨
        (∃ Q : ℕ, N = 25 * Q + 7 ∧ Q % 5 ≠ 1 ∧ Nat.Prime (168 * Q + 47)) ∨
        N % 125 = 32) :
    ∃ id ∈ LeavesAtShift 15, CandidateRealizesLeaf N (leafOfId id) := by
  rcases h with ⟨_, hs, _⟩ | ⟨M, hM, _, hp⟩ | ⟨Q, hQ, _, hp⟩ | hres
  · refine ⟨.shift15Base, by simp [LeavesAtShift], ?_⟩
    show 0 < ((168:ℤ) * N + (-1)) ∧
        ArithmeticFunction.sigma 0 (((168:ℤ) * N + (-1)).toNat) ≤ 4
    have heval : (((168:ℤ) * N + (-1))).toNat = 168 * N - 1 := by omega
    exact ⟨by push_cast; omega, by rwa [heval]⟩
  · refine ⟨.shift15PrimeA, by simp [LeavesAtShift], ?_⟩
    show ∃ u : ℕ, N = 5 * u + 2 ∧ 0 < ((168:ℤ) * u + 67) ∧
        Nat.Prime (((168:ℤ) * u + 67).toNat)
    have heval : (((168:ℤ) * M + 67)).toNat = 168 * M + 67 := by omega
    exact ⟨M, hM, by positivity, by rwa [heval]⟩
  · refine ⟨.shift15PrimeB, by simp [LeavesAtShift], ?_⟩
    show ∃ u : ℕ, N = 25 * u + 7 ∧ 0 < ((168:ℤ) * u + 47) ∧
        Nat.Prime (((168:ℤ) * u + 47).toNat)
    have heval : (((168:ℤ) * Q + 47)).toNat = 168 * Q + 47 := by omega
    exact ⟨Q, hQ, by positivity, by rwa [heval]⟩
  · refine ⟨.shift15Residual, by simp [LeavesAtShift], ?_⟩
    obtain ⟨s, hs⟩ : ∃ s, N = 125 * s + 32 := ⟨N / 125, by omega⟩
    show ∃ u : ℕ, N = 125 * u + 32 ∧ 0 < ((0:ℤ) * u + 1) ∧ True
    exact ⟨s, hs, by norm_num, trivial⟩

/-- Shift 14: the seven-adic frontier's branches land in the catalog,
with the prime branch split across its six `N % 49` classes. -/
theorem shift14_frontier_realizes_catalog_leaf (N : ℕ) (hN : 1 ≤ N)
    (h : (N % 7 ≠ 3 ∧ ArithmeticFunction.sigma 0 (180 * N - 1) ≤ 4 ∧
          (180 * N - 1).primeFactors.card ≤ 2) ∨
        N % 49 = 3 ∨
        ∃ M : ℕ, N = 7 * M + 3 ∧ M % 7 ≠ 0 ∧
          Nat.Prime (180 * M + 77) ∧
          (N % 49 = 10 ∨ N % 49 = 17 ∨ N % 49 = 24 ∨
            N % 49 = 31 ∨ N % 49 = 38 ∨ N % 49 = 45)) :
    ∃ id ∈ LeavesAtShift 14, CandidateRealizesLeaf N (leafOfId id) := by
  rcases h with ⟨_, hs, _⟩ | hres | ⟨M, hM, _, hp, hcls⟩
  · refine ⟨.shift14Base, by simp [LeavesAtShift], ?_⟩
    show 0 < ((180:ℤ) * N + (-1)) ∧
        ArithmeticFunction.sigma 0 (((180:ℤ) * N + (-1)).toNat) ≤ 4
    have heval : (((180:ℤ) * N + (-1))).toNat = 180 * N - 1 := by omega
    exact ⟨by push_cast; omega, by rwa [heval]⟩
  · refine ⟨.shift14Residual, by simp [LeavesAtShift], ?_⟩
    obtain ⟨s, hs⟩ : ∃ s, N = 49 * s + 3 := ⟨N / 49, by omega⟩
    show ∃ u : ℕ, N = 49 * u + 3 ∧ 0 < ((0:ℤ) * u + 1) ∧ True
    exact ⟨s, hs, by norm_num, trivial⟩
  · rcases hcls with hc | hc | hc | hc | hc | hc
    · refine ⟨.shift14Prime0, by simp [LeavesAtShift], ?_⟩
      obtain ⟨s, hs⟩ : ∃ s, M = 7 * s + 1 := ⟨M / 7, by omega⟩
      show ∃ u : ℕ, N = 49 * u + 10 ∧ 0 < ((1260:ℤ) * u + 257) ∧
          Nat.Prime (((1260:ℤ) * u + 257).toNat)
      have heval : (((1260:ℤ) * s + 257)).toNat = 180 * M + 77 := by omega
      exact ⟨s, by omega, by positivity, by rwa [heval]⟩
    · refine ⟨.shift14Prime1, by simp [LeavesAtShift], ?_⟩
      obtain ⟨s, hs⟩ : ∃ s, M = 7 * s + 2 := ⟨M / 7, by omega⟩
      show ∃ u : ℕ, N = 49 * u + 17 ∧ 0 < ((1260:ℤ) * u + 437) ∧
          Nat.Prime (((1260:ℤ) * u + 437).toNat)
      have heval : (((1260:ℤ) * s + 437)).toNat = 180 * M + 77 := by omega
      exact ⟨s, by omega, by positivity, by rwa [heval]⟩
    · refine ⟨.shift14Prime2, by simp [LeavesAtShift], ?_⟩
      obtain ⟨s, hs⟩ : ∃ s, M = 7 * s + 3 := ⟨M / 7, by omega⟩
      show ∃ u : ℕ, N = 49 * u + 24 ∧ 0 < ((1260:ℤ) * u + 617) ∧
          Nat.Prime (((1260:ℤ) * u + 617).toNat)
      have heval : (((1260:ℤ) * s + 617)).toNat = 180 * M + 77 := by omega
      exact ⟨s, by omega, by positivity, by rwa [heval]⟩
    · refine ⟨.shift14Prime3, by simp [LeavesAtShift], ?_⟩
      obtain ⟨s, hs⟩ : ∃ s, M = 7 * s + 4 := ⟨M / 7, by omega⟩
      show ∃ u : ℕ, N = 49 * u + 31 ∧ 0 < ((1260:ℤ) * u + 797) ∧
          Nat.Prime (((1260:ℤ) * u + 797).toNat)
      have heval : (((1260:ℤ) * s + 797)).toNat = 180 * M + 77 := by omega
      exact ⟨s, by omega, by positivity, by rwa [heval]⟩
    · refine ⟨.shift14Prime4, by simp [LeavesAtShift], ?_⟩
      obtain ⟨s, hs⟩ : ∃ s, M = 7 * s + 5 := ⟨M / 7, by omega⟩
      show ∃ u : ℕ, N = 49 * u + 38 ∧ 0 < ((1260:ℤ) * u + 977) ∧
          Nat.Prime (((1260:ℤ) * u + 977).toNat)
      have heval : (((1260:ℤ) * s + 977)).toNat = 180 * M + 77 := by omega
      exact ⟨s, by omega, by positivity, by rwa [heval]⟩
    · refine ⟨.shift14Prime5, by simp [LeavesAtShift], ?_⟩
      obtain ⟨s, hs⟩ : ∃ s, M = 7 * s + 6 := ⟨M / 7, by omega⟩
      show ∃ u : ℕ, N = 49 * u + 45 ∧ 0 < ((1260:ℤ) * u + 1157) ∧
          Nat.Prime (((1260:ℤ) * u + 1157).toNat)
      have heval : (((1260:ℤ) * s + 1157)).toNat = 180 * M + 77 := by omega
      exact ⟨s, by omega, by positivity, by rwa [heval]⟩

/-! ## Compatibility witness audit (milestone 6, step 7)

The known shift-16 compatibility witness `N = 2038` (from
`Erdos647_Shift16ResidualCompatibilityWitness.lean`) selects one leaf
per catalog shift; the framework must NOT falsely declare this known
compatible finite configuration impossible. This is a compatibility
witness, not a candidate. -/

/-- The witness `N = 2038` realizes one leaf per catalog shift and the
selection avoids every certified edge. -/
theorem depth16_witness_selection_audit :
    (∀ id ∈ ([.shift8Prime, .shift13Free, .shift14Base, .shift15Base,
        .shift16A] : List LeafId),
      CandidateRealizesLeaf 2038 (leafOfId id)) ∧
    AvoidsCertifiedEdges
      [.shift8Prime, .shift13Free, .shift14Base, .shift15Base, .shift16A] := by
  constructor
  · intro id hid
    fin_cases hid
    · show ∃ u : ℕ, 2038 = 2 * u + 0 ∧ 0 < ((630:ℤ) * u + (-1)) ∧
          Nat.Prime (((630:ℤ) * u + (-1)).toNat)
      refine ⟨1019, by norm_num, by norm_num, ?_⟩
      norm_num
      native_decide
    · show 0 < ((2520:ℤ) * 2038 + (-13)) ∧
          ArithmeticFunction.sigma 0 (((2520:ℤ) * 2038 + (-13)).toNat) ≤ 15
      refine ⟨by norm_num, ?_⟩
      norm_num
      native_decide
    · show 0 < ((180:ℤ) * 2038 + (-1)) ∧
          ArithmeticFunction.sigma 0 (((180:ℤ) * 2038 + (-1)).toNat) ≤ 4
      refine ⟨by norm_num, ?_⟩
      norm_num
      native_decide
    · show 0 < ((168:ℤ) * 2038 + (-1)) ∧
          ArithmeticFunction.sigma 0 (((168:ℤ) * 2038 + (-1)).toNat) ≤ 4
      refine ⟨by norm_num, ?_⟩
      norm_num
      native_decide
    · show ∃ u : ℕ, 2038 = 32 * u + 22 ∧ 0 < ((630:ℤ) * u + 433) ∧
          Nat.Prime (((630:ℤ) * u + 433).toNat)
      refine ⟨63, by norm_num, by norm_num, ?_⟩
      norm_num
      native_decide
  · unfold AvoidsCertifiedEdges
    decide

/-! ## Candidate-to-catalog bridge (assembly, hypothesis form)

Taking each shift's kernel-verified frontier disjunction as a hypothesis
(the candidate-facing versions — `candidate_shift13_adic_frontier`,
`candidate_shift14_seven_adic_frontier`,
`candidate_shift15_five_adic_frontier`, and the shift-8 classification —
are all tracked kernel-verified; cross-file imports are unavailable to
tracked replays, so the final candidate-facing assembly inlines them in
one submission), the catalog genuinely constrains a candidate: one
realized leaf per shift, and the whole selection avoids every certified
edge. This establishes the reusable pipeline
`candidate ⟹ certificate family ⟹ global restriction`; it is done once,
not extended shift-by-shift. -/

theorem catalog_bridge_8_13_14_15 (N : ℕ) (hN : 1 ≤ N)
    (h8 : Nat.Prime (315 * N - 1) ∨ ∃ p, Nat.Prime p ∧ 315 * N - 1 = 2 * p)
    (hb13 : ArithmeticFunction.sigma 0 (2520 * N - 13) ≤ 15)
    (h13 : ¬ 13 ∣ N ∨ ∃ M : ℕ, N = 13 * M ∧
      (M % 13 = 6 ∨ ArithmeticFunction.sigma 0 (2520 * M - 1) ≤ 7))
    (h14 : (N % 7 ≠ 3 ∧ ArithmeticFunction.sigma 0 (180 * N - 1) ≤ 4 ∧
          (180 * N - 1).primeFactors.card ≤ 2) ∨
        N % 49 = 3 ∨
        ∃ M : ℕ, N = 7 * M + 3 ∧ M % 7 ≠ 0 ∧
          Nat.Prime (180 * M + 77) ∧
          (N % 49 = 10 ∨ N % 49 = 17 ∨ N % 49 = 24 ∨
            N % 49 = 31 ∨ N % 49 = 38 ∨ N % 49 = 45))
    (h15 : (N % 5 ≠ 2 ∧ ArithmeticFunction.sigma 0 (168 * N - 1) ≤ 4 ∧
          (168 * N - 1).primeFactors.card ≤ 2) ∨
        (∃ M : ℕ, N = 5 * M + 2 ∧ M % 5 ≠ 1 ∧ Nat.Prime (168 * M + 67)) ∨
        (∃ Q : ℕ, N = 25 * Q + 7 ∧ Q % 5 ≠ 1 ∧ Nat.Prime (168 * Q + 47)) ∨
        N % 125 = 32) :
    ∃ a b c d : LeafId,
      a ∈ LeavesAtShift 8 ∧ b ∈ LeavesAtShift 13 ∧
      c ∈ LeavesAtShift 14 ∧ d ∈ LeavesAtShift 15 ∧
      (∀ id ∈ ([a, b, c, d] : List LeafId),
        CandidateRealizesLeaf N (leafOfId id)) ∧
      AvoidsCertifiedEdges [a, b, c, d] := by
  obtain ⟨a, ha, hra⟩ := shift8_classification_realizes_catalog_leaf N hN h8
  obtain ⟨b, hb, hrb⟩ := shift13_frontier_realizes_catalog_leaf N hN hb13 h13
  obtain ⟨c, hc, hrc⟩ := shift14_frontier_realizes_catalog_leaf N hN h14
  obtain ⟨d, hd, hrd⟩ := shift15_frontier_realizes_catalog_leaf N hN h15
  have hsel : ∀ id ∈ ([a, b, c, d] : List LeafId),
      CandidateRealizesLeaf N (leafOfId id) := by
    intro id hid
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hid
    rcases hid with rfl | rfl | rfl | rfl
    · exact hra
    · exact hrb
    · exact hrc
    · exact hrd
  exact ⟨a, b, c, d, ha, hb, hc, hd, hsel,
    realized_selection_avoids_certified_edges hsel⟩

end Erdos647
