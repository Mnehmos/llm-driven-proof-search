import Mathlib

/-!
# Extremal combinatorics kit (issue #88)

Finite combinatorics infrastructure combining human-readable Lean lemmas with
machine-checkable finite certificates: edge-coloring encodings, Schur- and
Ramsey-style theorems, and a kernel-checked CNF layer that is the import
surface for external SAT solver output.

## The trust ladder (issue #88's core acceptance criterion)

Every claim in the lab sits on exactly one rung, and NO rung grants proof
authority to a bare external solver verdict:

1. **Kernel `decide`** — the whole search runs inside Lean's kernel.
   Everything in this file marked `by decide` (Schur `n = 5`, the `K₅`
   pentagon witness, `edgeIdx` sanity, the CNF fixtures) is on this rung.
2. **Verified-checker certificates** — an EXTERNAL solver (CaDiCaL) produces
   an UNSAT certificate which Lean's formally verified LRAT checker replays;
   the kernel accepts the replay, so the trust is the same as rung 1 even
   though the search happened outside. `ramsey_two_three_le_six` below is on
   this rung via `bv_decide` — a genuine R(3,3) ≤ 6, solved by SAT, checked
   by a verified checker, live in this pinned toolchain.
3. **Kernel-checked imported witnesses** — for SAT (satisfiable) answers the
   solver's model is re-evaluated by the kernel (`cnfSat_of_witness` +
   `decide`/`rfl` on `cnfEval`). The solver only SUGGESTS; the kernel checks.
4. **Planned: general LRAT import** — arbitrary `Cnf` UNSAT certificates
   replayed through `Std.Sat`'s verified checker, plus encoding-soundness
   lemmas connecting problem statements to their CNF encodings. See
   `docs/kits/certificate-interface.md`.
5. **Empirical solver output with NO Lean-side check** — never proof
   authority, never recorded as anything but reporting metadata.

## Route notes / future target classes

Schur numbers and Rado-style equations (rung 1 for tiny `n`, rungs 2/4
beyond), Ramsey numbers on small complete graphs (rung 2 — the R(3,3)
pattern below scales to R(3,4) ≤ 9-style bounds), Erdős–Ginzburg–Ziv small
instances, and extremal set families with SAT-encodable constraints.
-/

namespace LeanChecker.ExtremalCombinatoricsKit

/-! ## Edge-coloring encodings

A 2-coloring of `K_n`'s edges is a bit per unordered pair. We fix the
lexicographic pair order and encode colorings as `BitVec (n·(n−1)/2)`, which
is exactly the shape both kernel `decide` and `bv_decide` consume. -/

/-- Lexicographic index of the edge `{i, j}` (for `i < j`) among the
`n·(n−1)/2` unordered pairs of `{0, …, n−1}`. -/
def edgeIdx (n i j : ℕ) : ℕ :=
  i * n - i * (i + 1) / 2 + (j - i - 1)

/-- Sanity (kernel-checked): for `K₆` the edge index is within the 15 edge
slots. -/
example : ∀ i j : Fin 6, i.val < j.val → edgeIdx 6 i.val j.val < 15 := by decide

/-- Sanity (kernel-checked): for `K₆` the edge index is injective on ordered
pairs — the encoding never aliases two edges. -/
example : ∀ i j i' j' : Fin 6, i.val < j.val → i'.val < j'.val →
    edgeIdx 6 i.val j.val = edgeIdx 6 i'.val j'.val → i = i' ∧ j = j' := by decide

/-- The triangle `{e₁, e₂, e₃}` (three edge indices) is monochromatic under
the coloring `x`. -/
def monoBit {w : ℕ} (x : BitVec w) (e₁ e₂ e₃ : ℕ) : Bool :=
  (x.getLsbD e₁ == x.getLsbD e₂) && (x.getLsbD e₂ == x.getLsbD e₃)

/-! ## Ramsey R(3,3) = 6, both directions

Lower direction: rung 1 (an explicit witness, kernel-checked). Upper
direction: rung 2 (external SAT search, verified LRAT replay). Together they
pin the Ramsey number — a real extremal result, not a toy. -/

/-- **R(3,3) > 5** (kernel-checked witness): the pentagon coloring of `K₅` —
cycle edges one color, chords the other, encoded as `665#10` over the
lexicographic edge order — has no monochromatic triangle. -/
theorem ramsey_two_three_gt_five :
    ∃ x : BitVec 10,
      (!monoBit x 0 1 4 && !monoBit x 0 2 5 && !monoBit x 0 3 6 &&
       !monoBit x 1 2 7 && !monoBit x 1 3 8 && !monoBit x 2 3 9 &&
       !monoBit x 4 5 7 && !monoBit x 4 6 8 && !monoBit x 5 6 9 &&
       !monoBit x 7 8 9) = true :=
  ⟨665#10, by decide⟩

/-- **R(3,3) ≤ 6** (verified-certificate rung): every 2-coloring of `K₆`'s 15
edges contains a monochromatic triangle — all 20 triangles of `K₆` in the
lexicographic edge order. CaDiCaL performs the search; Lean's verified LRAT
checker replays the UNSAT certificate; the kernel accepts the replay. -/
theorem ramsey_two_three_le_six : ∀ x : BitVec 15,
    (monoBit x 0 1 5 || monoBit x 0 2 6 || monoBit x 0 3 7 ||
     monoBit x 0 4 8 || monoBit x 1 2 9 || monoBit x 1 3 10 ||
     monoBit x 1 4 11 || monoBit x 2 3 12 || monoBit x 2 4 13 ||
     monoBit x 3 4 14 || monoBit x 5 6 9 || monoBit x 5 7 10 ||
     monoBit x 5 8 11 || monoBit x 6 7 12 || monoBit x 6 8 13 ||
     monoBit x 7 8 14 || monoBit x 9 10 12 || monoBit x 9 11 13 ||
     monoBit x 10 11 14 || monoBit x 12 13 14) = true := by
  intro x
  unfold monoBit
  bv_decide

/-! ## Schur S(2) = 4, both directions (rung 1) -/

/-- **Schur, upper direction**: every 2-coloring of `{1, …, 5}` (indices
`Fin 5`, value `i + 1`) has a monochromatic solution of `a + b = c`. Whole
search kernel-checked. -/
theorem schur_two_of_five : ∀ c : Fin 5 → Fin 2,
    ∃ a b : Fin 5, ∃ h : a.val + 1 + (b.val + 1) ≤ 5,
      c a = c b ∧ c b = c ⟨a.val + b.val + 1, by omega⟩ := by decide

/-- **Schur, sharpness witness**: `{1, …, 4}` admits a 2-coloring with no
monochromatic `a + b = c` (so `S(2) = 4` exactly). Kernel-checked. -/
theorem schur_two_of_four_witness :
    ∃ c : Fin 4 → Fin 2, ∀ a b : Fin 4, ∀ h : a.val + 1 + (b.val + 1) ≤ 4,
      ¬(c a = c b ∧ c b = c ⟨a.val + b.val + 1, by omega⟩) := by decide

/-! ## The CNF layer (certificate import surface)

A minimal, kernel-checked propositional model: literals, clauses, CNF, and
evaluation. This is the shape external solver interaction goes through —
`cnfSat_of_witness` imports SAT models (rung 3), `cnfUnsat_of_forall_fin`
kernel-checks small UNSAT claims (rung 1), and the planned LRAT import
(rung 4) plugs in at `CnfUnsat` without changing any downstream consumer.
DIMACS mapping: variable `v` ↦ `v + 1`, polarity ↦ sign. -/

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

/-- Unsatisfiability — the target shape for certificate import (rung 4). -/
def CnfUnsat (f : Cnf) : Prop := ¬CnfSat f

/-- **Rung 3 import bridge**: an external solver's SAT model is only a
suggestion — this lemma is where it becomes a theorem, by kernel evaluation
of the model against the formula. -/
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

end LeanChecker.ExtremalCombinatoricsKit
