import Mathlib

/-!
# Erdős #647 — budget-parametric terminal-leaf framework (Engine A, layer 2)

Repository-level module (2026-07-16): the symbolic data layer of the
cross-shift terminal-leaf incompatibility program. This file is compiled
from clean source through the pinned lean-checker toolchain
(`lake env lean`, Lean 4.32.0-rc1, pinned Mathlib) — repository-level
kernel evidence, deliberately NOT misrepresented as a tracked episode.
The standalone theorems it packages (`AffineForm.dvd_det`, the shift-16
leaf frontier exclusions) were additionally proved through tracked
proof-search episodes as self-contained statements; see
`Erdos647_AffineDeterminantInteraction.lean`,
`Erdos647_ForcedFactorPrimeBound.lean`, and
`Erdos647_Shift16LeafFrontierExclusions.lean` for episode provenance.

Design requirements (locked program, 2026-07-16):
- every terminal leaf carries enough SYMBOLIC data for automatic
  comparison (affine form, shape demand, branch congruence, family) —
  not a shift number plus prose;
- the candidate implication lives in a separate realization `Prop`
  (`CandidateRealizesLeaf`), not an opaque field, keeping the catalog
  inspectable and computationally searchable;
- everything is BUDGET-PARAMETRIC from the start: `SurvivesWithExcess`
  carries a variable excess `B` (the main declaration is the case
  `B = 2`; the limit declaration needs every `B` eventually), so the
  same leaf machinery can later attack both;
- pairwise compatibility is a graph (vertices = leaves grouped by shift,
  edges = incompatibility); the interface below deliberately routes
  through `List LeafType` + `Pairwise` so that ≥3-leaf hyperedge
  constraints can be added later without redesign.
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
form so the catalog stays symbolic. -/
inductive CofactorShape where
  | prime : CofactorShape
  | composite : CofactorShape
  | sigmaLE (B : ℕ) : CofactorShape
  | omegaLE (r : ℕ) : CofactorShape
  | divisibleBy (p e : ℕ) : CofactorShape
  | primeTimesPrime : CofactorShape
  | primePower : CofactorShape
  deriving Repr, DecidableEq

/-- Semantics of a shape demand on a natural cofactor value. -/
def CofactorShape.Holds : CofactorShape → ℕ → Prop
  | .prime, m => Nat.Prime m
  | .composite, m => 1 < m ∧ ¬ Nat.Prime m
  | .sigmaLE B, m => ArithmeticFunction.sigma 0 m ≤ B
  | .omegaLE r, m => m.primeFactors.card ≤ r
  | .divisibleBy p e, m => p ^ e ∣ m
  | .primeTimesPrime, m => ∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ m = p * q
  | .primePower, m => ∃ p e, Nat.Prime p ∧ m = p ^ e

/-- The two Hughes prime-chain families (Stage-2 reduction). -/
inductive PrimeChainFamily where
  | familyA : PrimeChainFamily
  | familyB : PrimeChainFamily
  deriving Repr, DecidableEq

/-- A terminal leaf: one fully symbolic escape branch of a shift's p-adic
classification. `excess` makes the budget variable — the main Erdős #647
declaration is `excess = 2`; the limit declaration quantifies over all
excesses. The branch congruence (`modulus`/`residue`) records how the
master parameter `N` (with `n = 2520·N`) reduces to the leaf's own
parameter `t` via `N = modulus·t + residue`. -/
structure LeafType where
  shift : ℕ
  excess : ℕ
  form : AffineForm
  shape : CofactorShape
  modulus : Option ℕ
  residue : Option ℕ
  family : Option PrimeChainFamily
  deriving Repr, DecidableEq

/-- Realization: the candidate master parameter `N` satisfies the leaf's
branch congruence and its shape demand on the evaluated form. Kept as a
separate `Prop` (a certificate obligation), never an opaque field. -/
def CandidateRealizesLeaf (N : ℕ) (leaf : LeafType) : Prop :=
  match leaf.modulus, leaf.residue with
  | some m, some r =>
      ∃ t : ℕ, N = m * t + r ∧ 0 < leaf.form.eval t ∧
        leaf.shape.Holds (leaf.form.eval t).toNat
  | _, _ =>
      0 < leaf.form.eval N ∧ leaf.shape.Holds (leaf.form.eval N).toNat

/-- Budget-parametric survival through a window of depth `D` with excess
`B`: every shift keeps its budget `B + k`. The main declaration is
`B = 2`; the square-root prefix reduction sets `D = 2·√n`. -/
def SurvivesWithExcess (n D B : ℕ) : Prop :=
  ∀ k, 0 < k → k ≤ D → k < n →
    ArithmeticFunction.sigma 0 (n - k) ≤ B + k

/-- Two leaves are jointly realizable: an edge is ABSENT in the
incompatibility graph exactly when this holds for some parameter. -/
def CompatibleLeaves (A B : LeafType) : Prop :=
  ∃ N : ℕ, CandidateRealizesLeaf N A ∧ CandidateRealizesLeaf N B

/-- A candidate realizes one leaf from every applicable shift of a prefix,
pairwise compatibly. Routed through `List` + `Pairwise` so hyperedge
(≥3-leaf) constraints can strengthen this later without redesign. -/
def RealizesPrefixLeaves (N D : ℕ) (leavesAt : ℕ → List LeafType) : Prop :=
  ∃ choice : ℕ → LeafType,
    (∀ k, 0 < k → k ≤ D → choice k ∈ leavesAt k ∧
      CandidateRealizesLeaf N (choice k)) ∧
    ∀ i j, 0 < i → i < j → j ≤ D →
      CompatibleLeaves (choice i) (choice j)

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
  ⟨16, 2, ⟨630, 433⟩, .prime, some 32, some 22, some .familyA⟩

/-- Shift-16 residual leaf B: `N = 64R+6`, `630R+59` prime. -/
def shift16LeafB : LeafType :=
  ⟨16, 2, ⟨630, 59⟩, .prime, some 64, some 6, some .familyA⟩

/-! ## Layer-2 frontier exclusions inside the residual branch

The determinant catalog (`dossiers/tools/det_catalog.py`) shows the leaf
forms interact with the re-parameterized shift cofactors exactly at the
frontier primes. Because both leaves DEMAND primality, divisibility by a
frontier prime at the unique bad residue kills the branch — a NEW layer of
congruence exclusions living one CRT level below the 41-class frontier
(these exclusions are on the BRANCH parameter, over forms that never
appeared in the original 13-coefficient sieve). Tracked-episode versions
of these two theorems live in
`Erdos647_Shift16LeafFrontierExclusions.lean`.
-/

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

end Erdos647
