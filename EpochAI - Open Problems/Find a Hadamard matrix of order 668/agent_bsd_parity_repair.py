"""Exact GF(2)+cardinality repair of a dual/quartic BS(84,83) checkpoint.

For a shift d, write each sign as (-1)^b.  Since the number of correlation
terms is even, residual/2 modulo two is a constant plus the XOR of all
(b_i XOR b_{i+d}).  This is linear in the bits: interior occurrences cancel.
We solve all 83 residual == 0 (mod 4) equations exactly.  Equal numbers of
flipped + and - positions in each sequence/residue class modulo four preserve
the ordinary, alternating, and z=i margins exactly.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import time
from pathlib import Path

from ortools.sat.python import cp_model

LENGTHS = (84, 84, 83, 83)


def residual(a: list[list[int]]) -> list[int]:
    return [sum(sum(x[i] * x[i+d] for i in range(len(x)-d)) for x in a)
            for d in range(1, 84)]


def margins(a: list[list[int]]) -> tuple[list[int], list[int], list[int]]:
    rows = [sum(x) for x in a]
    alts = [sum(v if i % 2 == 0 else -v for i, v in enumerate(x)) for x in a]
    z4: list[int] = []
    for x in a:
        z4.extend((sum(v for i, v in enumerate(x) if i % 4 == 0)
                   - sum(v for i, v in enumerate(x) if i % 4 == 2),
                   sum(v for i, v in enumerate(x) if i % 4 == 1)
                   - sum(v for i, v in enumerate(x) if i % 4 == 3)))
    return rows, alts, z4


def main() -> int:
    p = argparse.ArgumentParser()
    p.add_argument("input", type=Path)
    p.add_argument("--seconds", type=float, default=120)
    p.add_argument("--workers", type=int, default=8)
    p.add_argument("--max-changes", type=int)
    p.add_argument("--output", type=Path,
                   default=Path("agent_bsd_repair_pb0.json"))
    args = p.parse_args()
    started = time.time()
    data = json.loads(args.input.read_text(encoding="utf-8"))
    a = [[int(v) for v in x] for x in data["sequences"]]
    if tuple(map(len, a)) != LENGTHS or any(v not in (-1, 1) for x in a for v in x):
        raise ValueError("expected four +/-1 sequences of lengths 84,84,83,83")
    r0 = residual(a)
    before = margins(a)
    if any(sum(v*v for v in z) != 334 for z in before):
        raise ValueError("input does not have all three required margin norms")

    model = cp_model.CpModel()
    f = [[model.new_bool_var(f"f_{k}_{i}") for i in range(n)]
         for k, n in enumerate(LENGTHS)]
    one = model.new_bool_var("one")
    model.add(one == 1)

    # Preserve every mod-4 residue count, hence all z=1,-1,i components.
    for k, x in enumerate(a):
        for c in range(4):
            pos = [f[k][i] for i in range(c, len(x), 4) if x[i] == 1]
            neg = [f[k][i] for i in range(c, len(x), 4) if x[i] == -1]
            model.add(sum(pos) == sum(neg))

    # Delta of residual[d]/2 modulo 2 must equal its current defect bit.
    for d in range(1, 84):
        odd: set[tuple[int, int]] = set()
        for k, n in enumerate(LENGTHS):
            for i in range(n-d):
                for key in ((k, i), (k, i+d)):
                    if key in odd:
                        odd.remove(key)
                    else:
                        odd.add(key)
        lits = [f[k][i] for k, i in sorted(odd)]
        defect = (r0[d-1] // 2) & 1
        # add_bool_xor enforces XOR == true.  Appending fixed true toggles RHS.
        model.add_bool_xor(lits if defect else lits + [one])

    changes = sum(v for row in f for v in row)
    if args.max_changes is not None:
        model.add(changes <= args.max_changes)
    model.minimize(changes)
    for row in f:
        for v in row:
            model.add_hint(v, 0)

    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = args.seconds
    solver.parameters.num_search_workers = args.workers
    solver.parameters.random_seed = 668
    status = solver.solve(model)
    print(json.dumps({"event": "repair_result", "status": solver.status_name(status),
                      "objective": solver.objective_value,
                      "bound": solver.best_objective_bound,
                      "conflicts": solver.num_conflicts,
                      "branches": solver.num_branches,
                      "wall_time": solver.wall_time}), flush=True)
    if status not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        return 2

    b = [[-x if solver.value(f[k][i]) else x for i, x in enumerate(row)]
         for k, row in enumerate(a)]
    rr = residual(b)
    after = margins(b)
    selected = [(k, i) for k, row in enumerate(f) for i, v in enumerate(row)
                if solver.value(v)]
    if before != after or any(x % 4 for x in rr):
        raise RuntimeError({"margin_before": before, "margin_after": after,
                            "residual": rr})
    payload = {
        "construction": "base sequences BS(84,83)",
        "search": "agent exact GF(2)+cardinality parity repair",
        "solved": not any(rr),
        "independently_recomputed": True,
        "energy": sum(x*x for x in rr),
        "l1": sum(abs(x) for x in rr),
        "parity_bad": sum(x % 4 != 0 for x in rr),
        "changes": len(selected),
        "changed_positions": selected,
        "elapsed_s": time.time() - started,
        "row_sums": after[0],
        "alternating_sums": after[1],
        "z4_components": after[2],
        "residual": rr,
        "sequences": b,
    }
    raw = (json.dumps(payload, indent=2) + "\n").encode()
    args.output.write_bytes(raw)
    print(json.dumps({"event": "verified_parity0", "energy": payload["energy"],
                      "l1": payload["l1"], "changes": len(selected),
                      "sha256": hashlib.sha256(raw).hexdigest(),
                      "output": str(args.output)}), flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
