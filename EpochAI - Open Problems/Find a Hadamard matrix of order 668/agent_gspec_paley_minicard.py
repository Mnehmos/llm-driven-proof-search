"""Exact cyclic GS(167) SAT search with the fourth row fixed to Paley."""
from __future__ import annotations

import argparse
import json
import time
from pathlib import Path

from pysat.solvers import Minicard

N, H = 167, 83
ROWS = (19, 15, 9)


def chi(i: int) -> int:
    return 0 if i == 0 else (1 if pow(i, (N - 1) // 2, N) == 1 else -1)


def xv(k: int, i: int) -> int:
    return 1 + k * N + i


def main() -> None:
    p = argparse.ArgumentParser()
    p.add_argument("--hint", required=True)
    p.add_argument("--max-changes", type=int, default=0)
    p.add_argument("--conflicts", type=int, default=2_000_000_000)
    p.add_argument("--output", default="agent_gspec_paley_candidate.json")
    q = p.parse_args()
    hint_all = json.loads(Path(q.hint).read_text(encoding="utf8"))["sequences"]
    if len(hint_all) != 4 or any(len(x) != N for x in hint_all):
        raise ValueError("invalid hint")
    hint = hint_all[:3]
    if tuple(sum(x) for x in hint) != ROWS:
        raise ValueError("hint must begin with row sums (19,15,9)")
    paley = [1 if i == 0 else chi(i) for i in range(N)]
    assert sum(paley) == 1
    assert all(sum(paley[i] * paley[(i + d) % N] for i in range(N)) == -1 for d in range(1, N))

    started = time.time()
    next_var = 3 * N + 1
    clauses = 0
    native = 0
    with Minicard(use_timer=True) as solver:
        for k, row in enumerate(ROWS):
            lits = [xv(k, i) for i in range(N)]
            ones = (N + row) // 2
            solver.add_atmost(lits, ones)
            solver.add_atmost([-x for x in lits], N - ones)
            native += 2
            # Independent cyclic shifts make this normalization lossless.
            solver.add_clause([xv(k, 0)])
            clauses += 1
        solver.add_clause([xv(0, 1)])
        clauses += 1

        for d in range(1, H + 1):
            disagreements = []
            for k in range(3):
                for i in range(N):
                    x = xv(k, i)
                    z = xv(k, (i + d) % N)
                    y = next_var
                    next_var += 1
                    disagreements.append(y)
                    # y <-> (x xor z)
                    solver.add_clause([-x, -z, -y])
                    solver.add_clause([x, z, -y])
                    solver.add_clause([x, -z, y])
                    solver.add_clause([-x, z, y])
                    clauses += 4
            # PAF_1+PAF_2+PAF_3 = 3N - 2*D = 1, hence D=250.
            solver.add_atmost(disagreements, 250)
            solver.add_atmost([-y for y in disagreements], len(disagreements) - 250)
            native += 2

        phases = []
        changes = []
        for k in range(3):
            for i in range(N):
                x = xv(k, i)
                positive = hint[k][i] == 1
                phases.append(x if positive else -x)
                changes.append(-x if positive else x)
        solver.set_phases(phases)
        if q.max_changes:
            solver.add_atmost(changes, q.max_changes)
            native += 1

        print(json.dumps({
            "event": "model",
            "variables": next_var - 1,
            "clauses": clauses,
            "native_atmost": native,
            "max_changes": q.max_changes,
            "conflict_budget": q.conflicts,
            "build_s": time.time() - started,
        }), flush=True)
        solver.conf_budget(q.conflicts)
        sat = solver.solve_limited(expect_interrupt=True)
        event = {
            "event": "result",
            "sat": sat,
            "elapsed_s": time.time() - started,
            "accum_stats": solver.accum_stats(),
        }
        if sat:
            model = {x for x in solver.get_model() if x > 0}
            seq = [[1 if xv(k, i) in model else -1 for i in range(N)] for k in range(3)] + [paley]
            residual = [sum(seq[k][i] * seq[k][(i + d) % N] for k in range(4) for i in range(N)) for d in range(1, H + 1)]
            out = {
                "construction": "cyclic Goethals-Seidel order 167, fourth row Paley",
                "solver": "agent reduced exact MiniCard",
                "solved": not any(residual),
                "independently_recomputed": True,
                "energy": sum(x * x for x in residual),
                "l1": sum(abs(x) for x in residual),
                "nonzero": sum(x != 0 for x in residual),
                "maxabs": max(map(abs, residual), default=0),
                "row_sums": [sum(x) for x in seq],
                "residual": residual,
                "sequences": seq,
            }
            assert out["solved"] and out["row_sums"] == [19, 15, 9, 1]
            Path(q.output).write_text(json.dumps(out, separators=(",", ":")) + "\n", encoding="utf8")
            event["output"] = q.output
        print(json.dumps(event), flush=True)


if __name__ == "__main__":
    main()
