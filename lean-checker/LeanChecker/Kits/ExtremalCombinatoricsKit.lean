import Mathlib
import LeanChecker.Kits.FiniteCertificateKit

/-!
# Extremal combinatorics kit (issue #88)

Finite combinatorics DOMAIN kit: edge-coloring encodings and Schur/Ramsey
theorems. Certificate machinery (CNF model, solver-model import, bounded
UNSAT, DIMACS export) lives underneath in `FiniteCertificateKit`; this kit
adds the encodings and the ENCODING-SOUNDNESS lemmas that connect CNF facts
to mathematical claims — the "B obligation" of the A/B separation.

## The trust ladder (issue #88's core acceptance criterion)

Every claim sits on exactly one rung; NO rung grants proof authority to a
bare external solver verdict:

1. **Kernel `decide`** — the whole search runs inside Lean's kernel
   (Schur `n = 5`, the `K₅` pentagon witness, `edgeIdx` sanity, the
   encoding-soundness lemma below).
2. **Verified-checker certificates** — external CaDiCaL search, UNSAT
   certificate replayed by Lean's formally verified LRAT checker
   (`ramsey_two_three_le_six` via `bv_decide` — a genuine R(3,3) ≤ 6).
3. **Kernel-checked imported witnesses** — solver models re-evaluated by the
   kernel (`ramsey_two_three_gt_five_via_certificate` below runs the full
   pipeline: encode → import model → kernel-check → apply encoding
   soundness).
4. **Planned: general LRAT import** — see
   `docs/kits/certificate-interface.md`.
5. **Empirical solver output with NO Lean-side check** — never proof
   authority, reporting metadata only.

## Route notes / future target classes

Schur numbers and Rado-style equations (rung 1 for tiny `n`, rungs 2/4
beyond), Ramsey numbers on small complete graphs (rung 2 — the R(3,3)
pattern scales to R(3,4) ≤ 9-style bounds), Erdős–Ginzburg–Ziv small
instances, extremal set families with SAT-encodable constraints.
-/

namespace LeanChecker.ExtremalCombinatoricsKit

open LeanChecker.FiniteCertificateKit

/-! ## Edge-coloring encodings

A 2-coloring of `K_n`'s edges is a bit per unordered pair. We fix the
lexicographic pair order and encode colorings as `BitVec (n·(n−1)/2)`, which
is exactly the shape kernel `decide`, `bv_decide`, and the CNF layer all
consume. -/

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

/-! ## Ramsey R(3,3) = 6, both directions -/

/-- **R(3,3) > 5** (rung 1, direct): the pentagon coloring of `K₅` — cycle
edges one color, chords the other, encoded as `665#10` over the
lexicographic edge order — has no monochromatic triangle. -/
theorem ramsey_two_three_gt_five :
    ∃ x : BitVec 10,
      (!monoBit x 0 1 4 && !monoBit x 0 2 5 && !monoBit x 0 3 6 &&
       !monoBit x 1 2 7 && !monoBit x 1 3 8 && !monoBit x 2 3 9 &&
       !monoBit x 4 5 7 && !monoBit x 4 6 8 && !monoBit x 5 6 9 &&
       !monoBit x 7 8 9) = true :=
  ⟨665#10, by decide⟩

/-- **R(3,3) ≤ 6** (rung 2, verified certificate): every 2-coloring of
`K₆`'s 15 edges contains a monochromatic triangle — all 20 triangles of `K₆`
in the lexicographic edge order. CaDiCaL performs the search; Lean's
verified LRAT checker replays the UNSAT certificate; the kernel accepts the
replay. -/
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

/-! ## The A/B separation, worked end-to-end

The full certificate pipeline on `R(3,3) > 5`:

1. **Encode** the claim as a CNF (`k5NoMonoCnf`): per triangle, one
   not-all-true clause and one not-all-false clause over the 10 edge
   variables.
2. **Encoding soundness (obligation B)**: `k5NoMonoCnf_correct` — the CNF is
   satisfied by an assignment iff the corresponding coloring has no
   monochromatic triangle. Kernel-checked over all 1024 colorings.
3. **Certificate check (obligation A)**: the "solver model" `665#10` is
   re-evaluated by the kernel against the ORIGINAL Lean `Cnf` (never a
   re-imported DIMACS file).
4. **Theorem**: A + B compose into the mathematical claim.

A checked model without step 2 would only prove a fact about a formula. -/

/-- The `K₅` no-monochromatic-triangle claim as CNF over edge variables
`0, …, 9`: for each of the 10 triangles, a not-all-true and a not-all-false
clause. Export with `FiniteCertificateKit.dimacs` for an external solver. -/
def k5NoMonoCnf : Cnf :=
  [[⟨0, false⟩, ⟨1, false⟩, ⟨4, false⟩], [⟨0, true⟩, ⟨1, true⟩, ⟨4, true⟩],
   [⟨0, false⟩, ⟨2, false⟩, ⟨5, false⟩], [⟨0, true⟩, ⟨2, true⟩, ⟨5, true⟩],
   [⟨0, false⟩, ⟨3, false⟩, ⟨6, false⟩], [⟨0, true⟩, ⟨3, true⟩, ⟨6, true⟩],
   [⟨1, false⟩, ⟨2, false⟩, ⟨7, false⟩], [⟨1, true⟩, ⟨2, true⟩, ⟨7, true⟩],
   [⟨1, false⟩, ⟨3, false⟩, ⟨8, false⟩], [⟨1, true⟩, ⟨3, true⟩, ⟨8, true⟩],
   [⟨2, false⟩, ⟨3, false⟩, ⟨9, false⟩], [⟨2, true⟩, ⟨3, true⟩, ⟨9, true⟩],
   [⟨4, false⟩, ⟨5, false⟩, ⟨7, false⟩], [⟨4, true⟩, ⟨5, true⟩, ⟨7, true⟩],
   [⟨4, false⟩, ⟨6, false⟩, ⟨8, false⟩], [⟨4, true⟩, ⟨6, true⟩, ⟨8, true⟩],
   [⟨5, false⟩, ⟨6, false⟩, ⟨9, false⟩], [⟨5, true⟩, ⟨6, true⟩, ⟨9, true⟩],
   [⟨7, false⟩, ⟨8, false⟩, ⟨9, false⟩], [⟨7, true⟩, ⟨8, true⟩, ⟨9, true⟩]]

/-- **Encoding soundness (obligation B)**, kernel-checked over all 1024
colorings: the CNF holds of a coloring's bits iff no `K₅` triangle is
monochromatic. -/
theorem k5NoMonoCnf_correct : ∀ x : BitVec 10,
    cnfEval (fun v => x.getLsbD v) k5NoMonoCnf =
      (!monoBit x 0 1 4 && !monoBit x 0 2 5 && !monoBit x 0 3 6 &&
       !monoBit x 1 2 7 && !monoBit x 1 3 8 && !monoBit x 2 3 9 &&
       !monoBit x 4 5 7 && !monoBit x 4 6 8 && !monoBit x 5 6 9 &&
       !monoBit x 7 8 9) := by decide

/-- **R(3,3) > 5 via the certificate pipeline** (rung 3 + obligation B): the
imported "solver model" `665#10` is kernel-checked against `k5NoMonoCnf`,
then the encoding-soundness lemma turns the CNF fact into the mathematical
claim. -/
theorem ramsey_two_three_gt_five_via_certificate :
    ∃ x : BitVec 10,
      (!monoBit x 0 1 4 && !monoBit x 0 2 5 && !monoBit x 0 3 6 &&
       !monoBit x 1 2 7 && !monoBit x 1 3 8 && !monoBit x 2 3 9 &&
       !monoBit x 4 5 7 && !monoBit x 4 6 8 && !monoBit x 5 6 9 &&
       !monoBit x 7 8 9) = true := by
  refine ⟨665#10, ?_⟩
  rw [← k5NoMonoCnf_correct]
  decide

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

/-! ## Structural encoding soundness at scale (issue #110)

The A/B worked example above (`k5NoMonoCnf_correct`) checks obligation B by
`decide` over all 1024 colorings — that stops working exactly when obligation
A needs a SAT solver. This section does obligation B the way that scales: a
GENERATED Ramsey CNF (`ramseyTriangleCnf n`, using `edgeIdx` indexing) whose
soundness lemma is proved by STRUCTURAL INDUCTION over the triangle list
(`FiniteCertificateKit.cnfEval_flatMap_notAllSame`), never by enumerating
assignments. Composed with the rung-4 bridge + `bv_decide` (obligation A),
this closes a Ramsey theorem at `2³⁶` — a scale where `decide`-based
obligation B is hopeless.

Pattern for the next family (Schur/EGZ): supply a generator producing
`notAllSame`/`atLeastOne`-style gadgets over the family's index set, get its
structural soundness from the `flatMap` lemma, and pair with `bv_decide` or
`cnfUnsat_of_forall_bitvec` for obligation A. -/

/-- Triangles of `Kₙ` as edge-index triples `(edgeIdx i j, edgeIdx i k,
edgeIdx j k)` for `i < j < k`. -/
def triangleEdges (n : ℕ) : List (ℕ × ℕ × ℕ) :=
  (List.range n).flatMap fun i => (List.range n).flatMap fun j =>
    (List.range n).filterMap fun k =>
      if i < j ∧ j < k then some (edgeIdx n i j, edgeIdx n i k, edgeIdx n j k) else none

/-- The "no monochromatic triangle in `Kₙ`" CNF, generated (not hand-listed):
one `notAllSame` gadget per triangle over the edge variables. -/
def ramseyTriangleCnf (n : ℕ) : Cnf :=
  (triangleEdges n).flatMap fun t => FiniteCertificateKit.notAllSame t.1 t.2.1 t.2.2

/-- **Encoding soundness (obligation B), structural**: a coloring satisfies
`ramseyTriangleCnf n` iff every triangle of `Kₙ` is non-monochromatic — read
straight off the generator by induction, with no assignment enumeration. -/
theorem ramseyTriangleCnf_correct (asn : ℕ → Bool) (n : ℕ) :
    cnfEval asn (ramseyTriangleCnf n)
      = (triangleEdges n).all
          fun t => !(asn t.1 == asn t.2.1 && asn t.2.1 == asn t.2.2) :=
  FiniteCertificateKit.cnfEval_flatMap_notAllSame asn (triangleEdges n)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **Obligation A at `2³⁶`**: no `BitVec 36` edge-colouring of `K₉` satisfies
the triangle-free CNF — external CaDiCaL search, Lean's verified LRAT replay.
The generated CNF is concretized with `norm_num [List.range_succ, …]` before
`bv_decide`. -/
theorem ramseyTriangleCnf_nine_unsatBV :
    ∀ bv : BitVec 36, cnfEvalBV bv (ramseyTriangleCnf 9) = false := by
  intro bv
  unfold cnfEvalBV cnfEval ramseyTriangleCnf triangleEdges FiniteCertificateKit.notAllSame edgeIdx
  norm_num [List.range_succ, List.range_zero, clauseEval, litEval]
  bv_decide

set_option maxRecDepth 100000 in
/-- **R(3,3) ≤ 9 at `2³⁶` scale** (structural B + verified-LRAT A): every
edge 2-colouring of `K₉` contains a monochromatic triangle. Obligation B is
`ramseyTriangleCnf_correct` (structural, no enumeration); obligation A is the
`bv_decide` UNSAT above; the rung-4 bridge (`cnfUnsat_of_forall_bitvec`)
composes them. The genuine bound is R(3,3) = 6 — this theorem exists to
demonstrate the encoding-soundness pattern past the `decide` ceiling. -/
theorem k9_edge_coloring_has_mono_triangle (asn : ℕ → Bool) :
    ∃ t ∈ triangleEdges 9, asn t.1 == asn t.2.1 && asn t.2.1 == asn t.2.2 := by
  have hb : ∀ v ∈ cnfVars (ramseyTriangleCnf 9), v < 36 := by decide
  have hunsat : CnfUnsat (ramseyTriangleCnf 9) :=
    cnfUnsat_of_forall_bitvec (ramseyTriangleCnf 9) hb ramseyTriangleCnf_nine_unsatBV
  by_contra hcon
  refine hunsat ⟨asn, ?_⟩
  rw [ramseyTriangleCnf_correct, List.all_eq_true]
  intro t ht
  have hne : ¬((asn t.1 == asn t.2.1 && asn t.2.1 == asn t.2.2) = true) :=
    fun h => hcon ⟨t, ht, h⟩
  cases hb2 : (asn t.1 == asn t.2.1 && asn t.2.1 == asn t.2.2) with
  | false => rfl
  | true => exact absurd hb2 hne

end LeanChecker.ExtremalCombinatoricsKit
