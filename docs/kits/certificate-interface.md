# Finite-certificate interface plan (issue #88)

Design for how the lab combines human-readable Lean lemmas with
machine-checkable finite certificates, without ever granting proof authority
to a bare external solver verdict.

## 1. The trust ladder

Every combinatorial claim sits on exactly one rung. Rungs 1–3 exist and are
exercised today by `LeanChecker/Kits/ExtremalCombinatoricsKit.lean`; rung 4
is the planned extension; rung 5 is explicitly *not* proof authority.

| Rung | Mechanism | Trust | Status | Live example |
|------|-----------|-------|--------|--------------|
| 1 | kernel `decide` — the whole finite search runs in Lean's kernel | kernel | shipped | `schur_two_of_five`, `phpTwoOne_unsat`, `ramsey_two_three_gt_five` |
| 2 | `bv_decide` — external CaDiCaL search, UNSAT certificate replayed by Lean's **formally verified LRAT checker** | kernel (the checker is verified; the solver is untrusted) | shipped, works in the pinned toolchain | `ramsey_two_three_le_six` (a genuine R(3,3) ≤ 6) |
| 3 | imported SAT model, re-evaluated by the kernel (`cnfSat_of_witness` + `decide`) | kernel (the model is untrusted input; evaluation is the check) | shipped | `toy_sat` |
| 4 | general LRAT import for arbitrary `Cnf` UNSAT claims | kernel, once the bridge exists | planned (below) | — |
| 5 | solver says UNSAT/SAT, nothing checked in Lean | **none — reporting metadata only** | policy | recorded via issue #92 fields, never as an outcome |

The rung-5 rule restates issue #88's acceptance criterion: *no proof
authority is granted merely by an external solver output.* A rung-5 claim
can motivate work and appear in reports; it can never set `kernel_verified`
or `certified` on anything.

## 2. CNF exchange format

The kit's `Cnf` model (`Lit`/`Clause`/`Cnf` in
`LeanChecker.ExtremalCombinatoricsKit`) maps to DIMACS as:

- variable `v : ℕ` ↦ DIMACS variable `v + 1`
- `⟨v, true⟩` ↦ literal `v + 1`; `⟨v, false⟩` ↦ literal `-(v + 1)`
- clause = one DIMACS line terminated by `0`
- header: `p cnf <maxVar+1> <clauseCount>`

Export is mechanical from the `Cnf` value; import of a solver **model** is a
`ℕ → Bool` assignment plugged into `cnfSat_of_witness` (rung 3). Import of a
solver **UNSAT proof** is rung 4.

## 3. Rung-4 plan: general LRAT import

`bv_decide` already ships the hard part in the pinned toolchain: a verified
LRAT proof checker (`Std.Tactic.BVDecide` / `Std.Sat` internals) plus the
CaDiCaL binary. What rung 4 adds:

1. **Bridge**: a translation `Cnf → Std.Sat.CNF` plus the (small) soundness
   lemma that translation preserves satisfiability. Then
   `LRAT.check`-style verification of a solver-produced certificate yields
   `CnfUnsat f` for our `Cnf` values directly, at whatever scale CaDiCaL can
   solve — no `2^n` kernel enumeration.
2. **Encoding soundness**: for each problem family, a lemma of the shape
   "`encode params` UNSAT → theorem". This is per-family Lean work (the
   Ramsey fixture skipped it by *stating* the theorem over `BitVec`, which is
   why `bv_decide` applies directly — the recommended pattern while rung 4 is
   pending: state finite claims over `BitVec`/`Bool` when feasible).
3. **Artifact handling**: certificates are files; they are hashed and
   referenced, not committed (see §4).

Non-goals for rung 4: proof search inside Lean, incremental solving,
anything that would put an unverified checker in the trusted base.

## 4. Public-safe certificate reporting

Certificate metadata flows through the issue #92 reporting surface —
no new server fields are needed:

- `kit_lemmas_used`: the bridge lemma consumed (e.g.
  `…ExtremalCombinatoricsKit.cnfUnsat_of_forall_fin`, or the `bv_decide`
  theorem name).
- `proof_artifact_hash`: SHA-256 of the certificate file (LRAT/DRAT or
  model), which is stored as a private artifact — the hash is public-safe,
  the file need not be published.
- `missing_route_step`: for failures, which rung was unreachable (e.g.
  "rung 4: no Cnf→Std.Sat bridge yet").
- Existing gap categories cover the failure taxonomy (`library_missing`,
  `statement_elaborates_but_bridge_missing`).

Tracked-benchmark proof bodies remain behind the existing export gates;
nothing in this plan publishes them. A certificate for a *tracked benchmark*
problem is part of the proof body for redaction purposes and gets the same
treatment.

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

The kit's registry entry carries `epistemic_basis` describing the rung mix,
and each theorem's docstring names its rung. Anything imported through this
interface that is *not* rung 1–4 must be labeled empirical and kept out of
proof-bearing paths — the same discipline the benchmark trust-basis policy
(issues #38/#69) applies to statement fidelity.
