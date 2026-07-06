import Mathlib

/-!
# Finite-certificate kit (issue #88, maintainer review round)

The certificate machinery UNDERNEATH the domain kits: a kernel-checked CNF
model, solver-model import (rung 3), bounded UNSAT by kernel enumeration
(rung 1), and DIMACS export. Domain kits (ExtremalCombinatoricsKit and future
Ramsey/Schur/EGZ family kits) layer their encodings and encoding-soundness
lemmas on top — they never reimplement certificate handling.

## Two independent proof obligations (the A/B separation)

A certificate closes a mathematical theorem only through BOTH:

- **A. Certificate checking** — the certificate really proves the CNF's
  SAT/UNSAT status. This kit owns A (`cnfSat_of_witness`,
  `cnfUnsat_of_forall_fin`, and the planned general LRAT path).
- **B. Encoding soundness** — the CNF really encodes the mathematical
  claim. Family kits own B, one lemma per encoding (see
  `ExtremalCombinatoricsKit.k5NoMonoCnf_correct` for the worked example).

A checked certificate WITHOUT its encoding lemma does not close the
mathematical theorem — it only establishes a fact about a formula.

## DIMACS is exchange, not authority

The canonical object is always the Lean `Cnf` value. `dimacs` renders it for
an external solver; whatever comes back (model or certificate) is checked
against the ORIGINAL Lean `Cnf`, never against a re-imported DIMACS file.
Mapping: variable `v : ℕ` ↦ DIMACS `v + 1`; polarity ↦ sign; clause lines
end in `0`.
-/

namespace LeanChecker.FiniteCertificateKit

/-- A propositional literal: variable index and polarity. -/
structure Lit where
  var : ℕ
  pos : Bool
deriving DecidableEq, Repr

/-- A clause: disjunction of literals. -/
abbrev Clause := List Lit

/-- A CNF formula: conjunction of clauses. -/
abbrev Cnf := List Clause

/-- Literal evaluation under an assignment. -/
def litEval (a : ℕ → Bool) (l : Lit) : Bool :=
  if l.pos then a l.var else !a l.var

/-- Clause evaluation: any literal true. -/
def clauseEval (a : ℕ → Bool) (c : Clause) : Bool :=
  c.any (litEval a)

/-- CNF evaluation: all clauses true. -/
def cnfEval (a : ℕ → Bool) (f : Cnf) : Bool :=
  f.all (clauseEval a)

/-- The variables mentioned by a formula. -/
def cnfVars (f : Cnf) : List ℕ :=
  f.flatMap (fun c => c.map Lit.var)

/-- Satisfiability. -/
def CnfSat (f : Cnf) : Prop := ∃ a, cnfEval a f = true

/-- Unsatisfiability — the target shape for general LRAT import (rung 4). -/
def CnfUnsat (f : Cnf) : Prop := ¬CnfSat f

/-- **Rung 3 import bridge**: an external solver's SAT model is only a
suggestion — this lemma is where it becomes a theorem, by kernel evaluation
of the model against the original Lean `Cnf`. -/
theorem cnfSat_of_witness (f : Cnf) (a : ℕ → Bool) (h : cnfEval a f = true) :
    CnfSat f := ⟨a, h⟩

theorem litEval_congr {a b : ℕ → Bool} (l : Lit) (h : a l.var = b l.var) :
    litEval a l = litEval b l := by
  simp [litEval, h]

theorem clauseEval_congr {a b : ℕ → Bool} (c : Clause)
    (h : ∀ l ∈ c, a l.var = b l.var) :
    clauseEval a c = clauseEval b c := by
  induction c with
  | nil => rfl
  | cons hd tl ih =>
    have h1 := litEval_congr hd (h hd (by simp))
    have h2 := ih fun l hl => h l (by simp [hl])
    simp only [clauseEval, List.any_cons]
    rw [h1]
    simp only [clauseEval] at h2
    rw [h2]

/-- Evaluation depends only on the variables the formula mentions. -/
theorem cnfEval_congr {a b : ℕ → Bool} (f : Cnf)
    (h : ∀ v ∈ cnfVars f, a v = b v) :
    cnfEval a f = cnfEval b f := by
  induction f with
  | nil => rfl
  | cons hd tl ih =>
    have h1 : clauseEval a hd = clauseEval b hd :=
      clauseEval_congr hd fun l hl =>
        h l.var (by
          simp only [cnfVars, List.flatMap_cons, List.mem_append, List.mem_map]
          exact Or.inl ⟨l, hl, rfl⟩)
    have h2 := ih fun v hv =>
      h v (by
        simp only [cnfVars, List.flatMap_cons, List.mem_append] at hv ⊢
        exact Or.inr hv)
    simp only [cnfEval, List.all_cons]
    rw [h1]
    simp only [cnfEval] at h2
    rw [h2]

/-- **Rung 1 UNSAT for bounded formulas**: with all variables below `n`,
checking the `2^n` assignments on `Fin n → Bool` (a `Fintype`, so `decide`
works) suffices for genuine `CnfUnsat` over unrestricted assignments. -/
theorem cnfUnsat_of_forall_fin {n : ℕ} (f : Cnf)
    (hb : ∀ v ∈ cnfVars f, v < n)
    (h : ∀ a : Fin n → Bool,
      cnfEval (fun v => if hv : v < n then a ⟨v, hv⟩ else false) f = false) :
    CnfUnsat f := by
  rintro ⟨a, ha⟩
  have hcongr : cnfEval a f
      = cnfEval (fun v => if hv : v < n then a v else false) f :=
    cnfEval_congr f fun v hv => by simp [hb v hv]
  have hfalse : cnfEval (fun v => if hv : v < n then a v else false) f = false :=
    h fun i => a i.val
  rw [hcongr, hfalse] at ha
  exact Bool.false_ne_true ha

/-! ## DIMACS export (exchange format, never authority) -/

/-- One DIMACS literal token. -/
def Lit.dimacs (l : Lit) : String :=
  if l.pos then toString (l.var + 1) else "-" ++ toString (l.var + 1)

/-- Render a `Cnf` in DIMACS format for an external solver. The Lean `Cnf`
stays the canonical object; solver responses are checked against IT. -/
def dimacs (f : Cnf) : String :=
  let maxVar := (cnfVars f).foldr Nat.max 0
  let header := s!"p cnf {maxVar + 1} {f.length}"
  let lines := f.map fun c => String.intercalate " " (c.map Lit.dimacs) ++ " 0"
  String.intercalate "\n" (header :: lines) ++ "\n"

/-! ## Fixtures -/

/-- Pigeonhole `PHP(2,1)` as CNF: `x₀ ∧ x₁ ∧ (¬x₀ ∨ ¬x₁)` — two pigeons, one
hole. -/
def phpTwoOne : Cnf :=
  [[⟨0, true⟩], [⟨1, true⟩], [⟨0, false⟩, ⟨1, false⟩]]

/-- Fixture (rung 1): the pigeonhole formula is unsatisfiable, by kernel
enumeration of the 4 bounded assignments. -/
theorem phpTwoOne_unsat : CnfUnsat phpTwoOne :=
  cnfUnsat_of_forall_fin (n := 2) phpTwoOne (by decide) (by decide)

/-- Fixture (rung 3): importing a solver model — `(x₀ ∨ x₁) ∧ ¬x₀` with the
"solver's" assignment `x₁ ↦ true` checked by the kernel. -/
theorem toy_sat : CnfSat [[⟨0, true⟩, ⟨1, true⟩], [⟨0, false⟩]] :=
  cnfSat_of_witness _ (fun v => v == 1) (by decide)

/-- Sanity: the DIMACS rendering of the pigeonhole formula, byte-exact. -/
example : dimacs phpTwoOne = "p cnf 2 3\n1 0\n2 0\n-1 -2 0\n" := by rfl

end LeanChecker.FiniteCertificateKit
