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

/-! ## Rung 4: general UNSAT at CaDiCaL scale via the verified LRAT checker

`cnfUnsat_of_forall_fin` is kernel enumeration — it dies at `2ⁿ`. The rung-4
path routes the SAME `CnfUnsat` conclusion through `bv_decide` instead: a
`Cnf` assignment is a `BitVec n` (bit `v` ↦ variable `v`), and ruling out
every `BitVec n` is a pure BitVec goal CaDiCaL solves and Lean's formally
verified LRAT checker replays — no `2ⁿ` kernel work. `cnfEvalBV` is the
BitVec-indexed evaluator; `cnfUnsat_of_forall_bitvec` is the bridge whose
hypothesis `∀ bv, cnfEvalBV bv f = false` is discharged by `bv_decide`. -/

/-- Evaluate a CNF under a `BitVec` assignment: variable `v` reads bit `v`. -/
def cnfEvalBV {n : ℕ} (bv : BitVec n) (f : Cnf) : Bool :=
  cnfEval (fun v => bv.getLsbD v) f

/-- **Rung-4 bridge**: for a CNF whose variables are all `< n`, ruling out
every `BitVec n` assignment establishes genuine `CnfUnsat` over unrestricted
`ℕ → Bool` assignments. The `∀ bv` hypothesis is a pure BitVec proposition —
discharge it with `bv_decide` (external CaDiCaL + Lean's verified LRAT
checker) to obtain UNSAT at solver scale rather than by `2ⁿ` enumeration. An
arbitrary assignment is transported to a `BitVec n` via `ofBoolListLE`, which
agrees with it on every in-range variable. -/
theorem cnfUnsat_of_forall_bitvec {n : ℕ} (f : Cnf)
    (hb : ∀ v ∈ cnfVars f, v < n)
    (h : ∀ bv : BitVec n, cnfEvalBV bv f = false) : CnfUnsat f := by
  rintro ⟨a, ha⟩
  set bv : BitVec n :=
    (BitVec.ofBoolListLE (List.ofFn (fun i : Fin n => a i.val))).cast List.length_ofFn with hbv
  have hget : ∀ v ∈ cnfVars f, bv.getLsbD v = a v := by
    intro v hv
    have hvn : v < n := hb v hv
    rw [hbv, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD,
      List.getElem?_ofFn]
    simp [hvn]
  have hcongr : cnfEval (fun v => bv.getLsbD v) f = cnfEval a f := cnfEval_congr f hget
  have hbv_false := h bv
  unfold cnfEvalBV at hbv_false
  rw [hcongr, ha] at hbv_false
  exact Bool.false_ne_true hbv_false.symm

/-! ## Structural encoding-soundness helpers (obligation B, issue #110)

Family kits prove their encoding-soundness lemmas (obligation B of the A/B
separation) by INDUCTION over a CNF generator, never by `decide` over the
`2ⁿ` assignment space — that is what keeps obligation B tractable at the
scale where obligation A needs a SAT solver. These are the reusable pieces:
`cnfEval` distributes over `++`, the two-clause "not all the same" gadget
evaluates to a Boolean equality test, and a generator that `flatMap`s that
gadget over a list evaluates to the pointwise `all`. -/

/-- `cnfEval` distributes over clause-list concatenation. -/
theorem cnfEval_append (asn : ℕ → Bool) (f g : Cnf) :
    cnfEval asn (f ++ g) = (cnfEval asn f && cnfEval asn g) := by
  simp [cnfEval, List.all_append]

/-- The "not all three the same colour" gadget: two clauses forbidding
all-true and all-false on variables `a, b, c`. -/
def notAllSame (a b c : ℕ) : Cnf :=
  [[⟨a, false⟩, ⟨b, false⟩, ⟨c, false⟩], [⟨a, true⟩, ⟨b, true⟩, ⟨c, true⟩]]

/-- The gadget evaluates to "the three bits are not all equal" — proved by
the eight-case split on the three Booleans, not by assignment enumeration. -/
theorem notAllSame_correct (asn : ℕ → Bool) (a b c : ℕ) :
    cnfEval asn (notAllSame a b c) = !(asn a == asn b && asn b == asn c) := by
  simp only [notAllSame, cnfEval, clauseEval, litEval, List.all_cons, List.all_nil,
    List.any_cons, List.any_nil]
  cases asn a <;> cases asn b <;> cases asn c <;> rfl

/-- **Structural soundness of a `notAllSame` generator**: a CNF built by
`flatMap`ping the gadget over a list of index triples evaluates to the
pointwise `all` of "not all equal" — by induction on the triple list, with
`asn` held fixed. This is the obligation-B workhorse: the mathematical
predicate is read off the CNF without touching the assignment space. -/
theorem cnfEval_flatMap_notAllSame (asn : ℕ → Bool) (ts : List (ℕ × ℕ × ℕ)) :
    cnfEval asn (ts.flatMap fun t => notAllSame t.1 t.2.1 t.2.2)
      = ts.all fun t => !(asn t.1 == asn t.2.1 && asn t.2.1 == asn t.2.2) := by
  induction ts with
  | nil => rfl
  | cons hd tl ih =>
    rw [List.flatMap_cons, cnfEval_append, notAllSame_correct, ih, List.all_cons]

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

/-! ## Rung-4 scale fixture: pigeonhole at 2²⁰

A generated pigeonhole family — `p` pigeons, `h` holes, variable `i·h + j`
meaning "pigeon `i` in hole `j`": every pigeon is in some hole, and no two
pigeons share a hole. UNSAT whenever `p > h`. `PHP(5,4)` has 20 variables, so
bounded kernel enumeration would be `2²⁰ ≈ 10⁶` cases — out of reach for
`decide`, routine for the rung-4 LRAT path. -/

/-- "Each of the `p` pigeons occupies some hole" — one wide clause per pigeon. -/
def phpVars (p h : ℕ) : List Clause :=
  (List.range p).map fun i => (List.range h).map fun j => (⟨i * h + j, true⟩ : Lit)

/-- "No two pigeons share a hole" — a binary clause per hole and pigeon pair. -/
def phpExcl (p h : ℕ) : List Clause :=
  (List.range h).flatMap fun j =>
    (List.range p).flatMap fun i =>
      (List.range p).filterMap fun i' =>
        if i < i' then some [(⟨i * h + j, false⟩ : Lit), ⟨i' * h + j, false⟩] else none

/-- Pigeonhole CNF for `p` pigeons and `h` holes. -/
def phpCnf (p h : ℕ) : Cnf := phpVars p h ++ phpExcl p h

set_option maxRecDepth 8000 in
/-- Fixture (rung 4 — issue #109 acceptance): `PHP(5,4)` is unsatisfiable.
20 variables ⇒ a `2²⁰` search space, closed NOT by kernel enumeration but by
the rung-4 bridge: the `∀ bv : BitVec 20` obligation is handed to `bv_decide`
(external CaDiCaL + Lean's verified LRAT replay), and `cnfUnsat_of_forall_bitvec`
turns that into genuine `CnfUnsat`. -/
theorem phpFiveFour_unsat : CnfUnsat (phpCnf 5 4) := by
  apply cnfUnsat_of_forall_bitvec (n := 20)
  · decide
  · intro bv
    unfold cnfEvalBV cnfEval phpCnf phpVars phpExcl
    norm_num [List.range_succ, List.range_zero, clauseEval, litEval]
    bv_decide

end LeanChecker.FiniteCertificateKit
