# IMO 2026 Problem 1 — living formalization campaign

**Problem:** a 2026-entry gcd/lcm blackboard process. Prove that every play
terminates with exactly one entry greater than 1 and that the survivor is
independent of the moves.

**Mathematical status:** SOLVED. A complete human proof is in
[`solution.md`](solution.md).

**Formalization status:** COMPLETE. The faithful board-process root theorem is
kernel-verified in [Final.lean](proof/Final.lean). It includes global
termination, existence of a reachable terminal board, exactly one surviving
non-unit, and equality of the survivor for every reachable terminal play.

**Trust status:** every verified target used development attestation
(fidelity_status=attested), not an independent fidelity review. The complete
root is an honest kernel_verified result, not a certified result.

## Start here

| File | Purpose |
|---|---|
| [problem.md](problem.md) | Faithful contest statement and transcription notes |
| [whitepaper.md](whitepaper.md) | Problem, proof architecture, and formal results |
| [solution.md](solution.md) | Complete human-readable solution |
| [THEOREM-CATALOG.md](THEOREM-CATALOG.md) | Formal theorem DAG and exact status of every target |
| [evidence.md](evidence.md) | Machine records: hashes, problem versions, episodes, attempts, outcomes |
| [attack-plan.md](attack-plan.md) | Ordered remaining formalization work |
| [credit.md](credit.md) | Sources, attribution, AI-assistance disclosure, and limits |
| [proof/Final.lean](proof/Final.lean) | Complete faithful Lean theorem and proof |
| [proof/](proof/) | Complete root plus standalone component exports |
| [trace/trajectory.md](trace/trajectory.md) | Hash-chain index and failure-history summary |

## Headline kernel-verified results

1. The exponent move
   `(a,b) ↦ (min a b, max a b - min a b)` preserves gcd.
2. `Nat.factorization` sends the integer board move to that exponent move.
3. The gcd of an entire exponent multiset is preserved by a local move.
4. The replacement pair has product `lcm(m,n)` and retains a non-unit.
5. A legal move decreases product, or preserves product and decreases the
   number of non-units.
6. On a 2026-entry board this lexicographic decrease is encoded by
   `B.prod * 2027 + nonunitCount(B)`.
7. The resulting reverse-step relation is well-founded; therefore there is no
   infinite legal play in the formal relation.
8. Every initial board reaches a terminal board whose non-unit filter is a
   singleton, and every reachable terminal board has that same survivor.

## Status, plainly

Both parts (a) and (b) are now proved together by one kernel-verified Lean root
theorem. The remaining trust limitation is fidelity attestation versus an
independent formalization review; it is not a missing proof obligation.
