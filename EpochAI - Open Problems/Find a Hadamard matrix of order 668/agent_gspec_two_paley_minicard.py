"""Exact GS(167) SAT search with both row-sum-one blocks fixed to Paley."""
from __future__ import annotations

import argparse
import json
import time
from pathlib import Path

from pysat.solvers import Minicard

N, H = 167, 83
ROWS = (21, 15)


def chi(i: int) -> int:
    return 0 if i == 0 else (1 if pow(i, (N - 1) // 2, N) == 1 else -1)


def xv(k: int, i: int) -> int:
    return 1 + k * N + i


def main() -> None:
    p = argparse.ArgumentParser()
    p.add_argument("--hint", required=True)
    p.add_argument("--max-changes", type=int, default=0)
    p.add_argument("--conflicts", type=int, default=5_000_000)
    p.add_argument("--output", default="agent_gspec_two_paley_candidate.json")
    q = p.parse_args()
    all_hint = json.loads(Path(q.hint).read_text(encoding="utf8"))["sequences"]
    hint = all_hint[:2]
    if len(hint) != 2 or any(len(x) != N for x in hint) or tuple(sum(x) for x in hint) != ROWS:
        raise ValueError("hint must begin with row sums (21,15)")
    hint_shifts = []
    for k in range(2):
        shift = 0 if hint[k][0] == 1 else hint[k].index(1)
        hint_shifts.append(shift)
        if shift:
            hint[k] = hint[k][shift:] + hint[k][:shift]
    paley = [1 if i == 0 else chi(i) for i in range(N)]
    assert sum(paley) == 1
    assert all(sum(paley[i] * paley[(i + d) % N] for i in range(N)) == -1 for d in range(1, N))

    started = time.time()
    next_var = 2 * N + 1
    clauses = 0
    native = 0
    with Minicard(use_timer=True) as solver:
        for k, row in enumerate(ROWS):
            lits = [xv(k, i) for i in range(N)]
            ones = (N + row) // 2
            solver.add_atmost(lits, ones)
            solver.add_atmost([-x for x in lits], N - ones)
            solver.add_clause([xv(k, 0)])
            native += 2
            clauses += 1
        # After independently translating both rows to put a +1 at zero, a
        # common nonzero multiplier can map a second +1 of the first row to 1.
        # This affine normalization is lossless for an exact SDS.
        solver.add_clause([xv(0, 1)])
        clauses += 1
        for d in range(1, H + 1):
            disagreements = []
            for k in range(2):
                for i in range(N):
                    x, z, y = xv(k, i), xv(k, (i + d) % N), next_var
                    next_var += 1
                    disagreements.append(y)
                    solver.add_clause([-x, -z, -y])
                    solver.add_clause([x, z, -y])
                    solver.add_clause([x, -z, y])
                    solver.add_clause([-x, z, y])
                    clauses += 4
            # The two fixed Paley rows contribute -2.  Thus the variable pair
            # needs PAF_A+PAF_B=2 = 2N - 2D, i.e. D=166.
            solver.add_atmost(disagreements, 166)
            solver.add_atmost([-y for y in disagreements], len(disagreements) - 166)
            native += 2
        phases, changes = [], []
        for k in range(2):
            for i in range(N):
                x = xv(k, i)
                pos = hint[k][i] == 1
                phases.append(x if pos else -x)
                changes.append(-x if pos else x)
        solver.set_phases(phases)
        if q.max_changes:
            solver.add_atmost(changes, q.max_changes)
            native += 1
        print(json.dumps({"event":"model","variables":next_var-1,"clauses":clauses,"native_atmost":native,"max_changes":q.max_changes,"hint_cyclic_shifts":hint_shifts,"conflict_budget":q.conflicts,"build_s":time.time()-started}), flush=True)
        solver.conf_budget(q.conflicts)
        sat = solver.solve_limited(expect_interrupt=True)
        event = {"event":"result","sat":sat,"elapsed_s":time.time()-started,"accum_stats":solver.accum_stats()}
        if sat:
            model = {x for x in solver.get_model() if x > 0}
            seq = [[1 if xv(k, i) in model else -1 for i in range(N)] for k in range(2)] + [paley, paley]
            r = [sum(seq[k][i] * seq[k][(i + d) % N] for k in range(4) for i in range(N)) for d in range(1, H + 1)]
            out = {"construction":"cyclic Goethals-Seidel order 167, two Paley rows","solver":"agent reduced exact MiniCard","solved":not any(r),"independently_recomputed":True,"energy":sum(x*x for x in r),"l1":sum(abs(x) for x in r),"nonzero":sum(x!=0 for x in r),"maxabs":max(map(abs,r),default=0),"row_sums":[sum(x) for x in seq],"residual":r,"sequences":seq}
            assert out["solved"] and out["row_sums"] == [21,15,1,1]
            Path(q.output).write_text(json.dumps(out,separators=(",", ":"))+"\n",encoding="utf8")
            event["output"] = q.output
        print(json.dumps(event), flush=True)


if __name__ == "__main__":
    main()
