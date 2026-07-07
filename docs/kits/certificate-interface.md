# Finite-certificate interface plan (issue #88)

Design for how the lab combines human-readable Lean lemmas with
machine-checkable finite certificates, without ever granting proof authority
to a bare external solver verdict.

Kit layering (maintainer review round): certificate machinery lives in
**`FiniteCertificateKit`** (CNF model, model import, bounded UNSAT, DIMACS
export, and eventually the LRAT bridge); domain kits
(`ExtremalCombinatoricsKit` today; Ramsey/Schur/EGZ family kits later) layer
encodings and encoding-soundness lemmas ON TOP and never reimplement
certificate handling.

## 1. The trust ladder

Every combinatorial claim sits on exactly one rung. Rungs 1–3 exist and are
exercised today; rung 4 is the planned extension; rung 5 is explicitly *not*
proof authority.

| Rung | Mechanism | Trust | Status | Live example |
|------|-----------|-------|--------|--------------|
| 1 | kernel `decide` — the whole finite search runs in Lean's kernel | kernel | shipped | `schur_two_of_five`, `phpTwoOne_unsat`, `ramsey_two_three_gt_five` |
| 2 | `bv_decide` — external CaDiCaL search, UNSAT certificate replayed by Lean's **formally verified LRAT checker** | kernel (the checker is verified; the solver is untrusted) | shipped, works in the pinned toolchain | `ramsey_two_three_le_six` (a genuine R(3,3) ≤ 6) |
| 3 | imported SAT model, re-evaluated by the kernel (`cnfSat_of_witness` + `decide`) | kernel (the model is untrusted input; evaluation is the check) | shipped | `toy_sat`; end-to-end: `ramsey_two_three_gt_five_via_certificate` |
| 4 | bounded `Cnf` UNSAT routed through `bv_decide` (external CaDiCaL + verified LRAT), no `2ⁿ` kernel enumeration | kernel (verified checker; solver untrusted) | shipped | `phpFiveFour_unsat` (PHP(5,4), a `2²⁰` search space) |
| 5 | solver says UNSAT/SAT, nothing checked in Lean | **none — reporting metadata only** | policy | recorded via issue #92 fields, never as an outcome |

The rung-5 rule restates issue #88's acceptance criterion: *no proof
authority is granted merely by an external solver output.* A rung-5 claim
can motivate work and appear in reports; it can never set `kernel_verified`
or `certified` on anything. This rule is repeated in the kit docblocks, the
registry `epistemic_basis` fields, and here, and must be preserved in any
future export/policy surface that touches certificates.

## 1a. The A/B separation: two independent proof obligations

A certificate closes a mathematical theorem only through BOTH:

- **A. Certificate checking** — the certificate really establishes the CNF's
  SAT/UNSAT status. Owned by `FiniteCertificateKit`
  (`cnfSat_of_witness`, `cnfUnsat_of_forall_fin`, rung-4 LRAT later).
- **B. Encoding soundness** — the CNF really encodes the mathematical claim.
  Owned by the family kits, one lemma per encoding.

A checked SAT/UNSAT certificate **without** its encoding lemma establishes a
fact about a formula, not the theorem. The worked end-to-end example is
`ExtremalCombinatoricsKit.ramsey_two_three_gt_five_via_certificate`:
`k5NoMonoCnf` (encoding) + `k5NoMonoCnf_correct` (obligation B,
kernel-checked over all 1024 colorings) + the kernel-checked model `665#10`
(obligation A) compose into R(3,3) > 5.

Registry entries record both halves per claim:
`certificate_checker` (`kernel_decide | bv_decide_lrat | model_eval | lrat`)
and `encoding_soundness_lemma` (a theorem name, or `stated_directly` when
the claim is phrased over `BitVec`/`Bool` so no encoding gap exists).

## 2. CNF exchange format — DIMACS is exchange, never authority

The canonical object is always the Lean `Cnf` value
(`Lit`/`Clause`/`Cnf` in `LeanChecker.FiniteCertificateKit`).
`FiniteCertificateKit.dimacs` renders it (byte-exactness pinned by an `rfl`
fixture) as:

- variable `v : ℕ` ↦ DIMACS variable `v + 1`
- `⟨v, true⟩` ↦ literal `v + 1`; `⟨v, false⟩` ↦ literal `-(v + 1)`
- clause = one DIMACS line terminated by `0`
- header: `p cnf <maxVar+1> <clauseCount>`

The flow is one-directional:

```
Lean Cnf → DIMACS export → solver → model / certificate → checked against the ORIGINAL Lean Cnf
```

An imported DIMACS file is never the trusted source. If a workflow must
start from external DIMACS, it either reconstructs a Lean `Cnf` and treats
THAT as canonical going forward, or it proves/kernel-checks a round-trip
against an existing canonical `Cnf` — otherwise its claims are rung 5.
Import of a solver **model** is a `ℕ → Bool` assignment plugged into
`cnfSat_of_witness` (rung 3). Import of a solver **UNSAT proof** is rung 4.

## 3. Rung 4: general UNSAT at solver scale (shipped)

Rather than reimplement an LRAT importer against the `Std.Sat` internals, the
shipped rung-4 path reuses `bv_decide` — which already bundles a verified
LRAT checker plus CaDiCaL — by reflecting a bounded `Cnf` UNSAT question into
a BitVec proposition:

1. **Evaluator** `cnfEvalBV : BitVec n → Cnf → Bool` reads variable `v` from
   bit `v` of the assignment.
2. **Bridge** `cnfUnsat_of_forall_bitvec` (kernel-checked): for a CNF with
   every variable `< n`, `(∀ bv : BitVec n, cnfEvalBV bv f = false) →
   CnfUnsat f`. The proof transports an arbitrary `ℕ → Bool` assignment to a
   `BitVec n` via `ofBoolListLE` (agreeing on every in-range variable), so no
   generality is lost.
3. **Discharge**: the `∀ bv` obligation is a pure BitVec goal — `bv_decide`
   hands it to CaDiCaL and replays the UNSAT certificate through the verified
   checker. `phpFiveFour_unsat` (PHP(5,4), 20 vars, a `2²⁰` space) is the
   live example: closed with zero `2ⁿ` kernel enumeration.

Trust is identical to rung 2 (the checker is verified; the solver is
untrusted). This covers **bounded** CNF UNSAT at CaDiCaL scale, which is the
case every finite-combinatorics encoding produces. Non-goals, unchanged:
proof search inside Lean, incremental solving, and — the deliberate trade —
unbounded/streaming certificates that would need the raw `Std.Sat` importer.
Those remain future work; nothing here puts an unverified checker in the
trusted base.

**Encoding soundness** (obligation B) is still per-family Lean work — see
§1a and issue #110. The recommended pattern remains: state finite claims over
`BitVec`/`Bool` when feasible so `bv_decide` (rung 2) or this bridge (rung 4)
applies directly; otherwise supply a structural encoding-soundness lemma.
Certificate artifacts are hashed and referenced, not committed (see §4).

## 4. Public-safe certificate reporting

**Hard invariant: for tracked benchmarks, certificate artifacts ARE
proof-body material.** LRAT/DRAT files, solver models, and CNF encodings of
a tracked benchmark's statement obey exactly the same redaction gates as
Lean proof source — a redacted export that leaked a certificate would leak
the proof.

Public-safe export MAY include, per claim:

```
certificate hash (SHA-256)
certificate type (model | lrat | drat)
checker used (kernel_decide | bv_decide_lrat | model_eval | lrat)
encoding-soundness lemma name (or stated_directly)
problem family
trust rung
```

and MUST NOT include the certificate file, the CNF encoding of a tracked
statement, or the model itself.

Certificate metadata flows through the issue #92 reporting surface —
no new server fields are needed:

- `kit_lemmas_used`: the bridge lemma consumed (e.g.
  `…FiniteCertificateKit.cnfUnsat_of_forall_fin`, or the `bv_decide`
  theorem name) plus the encoding-soundness lemma.
- `proof_artifact_hash`: SHA-256 of the certificate file — the hash is
  public-safe, the file is a private artifact.
- `missing_route_step`: for failures, which rung was unreachable (e.g.
  "rung 4: no Cnf→Std.Sat bridge yet") or which obligation was missing
  ("obligation B: no encoding-soundness lemma for this family").
- Existing gap categories cover the failure taxonomy (`library_missing`,
  `statement_elaborates_but_bridge_missing`).

## 5. Target classes and scaling expectations

- **Schur/Rado equations**: rung 1 to ~`n = 12` (kernel `2^n`); rung 2/4
  beyond. `S(3)` (3-colorings of `{1..13}`) is `3^13 ≈ 1.6M` cases — rung 2
  territory via a two-bit-per-element encoding.
- **Ramsey bounds on small `K_n`**: rung 2. R(3,3) = 6 shipped (15s solve +
  verified replay). R(3,4) ≤ 9 is `2^36` colorings — far past rung 1,
  routine for rung 2. R(4,4) ≤ 18 (`2^153`) is the stress test that likely
  motivates rung 4's streaming certificate handling.
- **Erdős–Ginzburg–Ziv small instances**: rung 1 for `n ≤ 3`, rung 2 beyond.
- **Extremal set families / SAT-encodable extremal claims**: rung 2/4, with
  per-family encoding-soundness lemmas as the recurring Lean cost.

## 6. Epistemic labeling in the registry

Kit registry entries carry `epistemic_basis` describing the rung mix, and —
per the maintainer review — a `certificate_claims` list recording BOTH
halves of the A/B separation per claim: `certificate_checker` and
`encoding_soundness_lemma`. Each theorem's docstring names its rung.
Anything imported through this interface that is *not* rung 1–4 must be
labeled empirical and kept out of proof-bearing paths — the same discipline
the benchmark trust-basis policy (issues #38/#69) applies to statement
fidelity.

## 7. Kit layering and implementation sequence

Dependency shape (so no domain kit reinvents certificate handling):

```
FiniteCertificateKit
  → Cnf/Lit/Clause, eval semantics, DIMACS export,
    model-witness check (rung 3), bounded UNSAT (rung 1),
    LRAT bridge (rung 4, planned)

ExtremalCombinatoricsKit          (shipped: layers on FiniteCertificateKit)
  → generic finite encodings (edgeIdx/monoBit), Ramsey/Schur theorems,
    per-encoding soundness lemmas (obligation B)

Future family kits (RamseyKit / SchurKit / EGZKit / ExtremalSetKit)
  → family-specific encodings + soundness lemmas only
```

Implementation sequence (status):

1. ✅ Policy/design locked (this document, issue #88).
2. ✅ `FiniteCertificateKit` with Cnf / DIMACS export (byte-pinned) /
   model-witness recheck / bounded UNSAT.
3. ✅ Rung-3 SAT-witness path end-to-end, including the A/B worked example
   (`ramsey_two_three_gt_five_via_certificate`).
4. ✅ Rung-4 bridge `cnfUnsat_of_forall_bitvec` (issue #109): bounded `Cnf`
   UNSAT routed through `bv_decide`/verified LRAT, transporting an arbitrary
   assignment to a `BitVec n`. (The raw `Std.Sat.CNF` importer for
   unbounded/streaming certificates is a deliberate non-goal — see §3.)
5. ✅ Rung-4 UNSAT fixture at scale: `phpFiveFour_unsat` (PHP(5,4), `2²⁰`).
6. ⬜ One family encoding-soundness lemma at a scale where rung 1 cannot
   check obligation B by `decide` (issue #110; Ramsey or Schur).
7. ⬜ Then, and only then, harder Erdős examples. R(4,4)-scale is a stress
   test, not an implementation target.
