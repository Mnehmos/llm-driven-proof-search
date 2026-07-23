"""Exact two-Paley GS(167) search with both variable rows symmetric."""
from __future__ import annotations

import argparse
import json
import time
from pathlib import Path

from pysat.solvers import Minicard

N, H, O = 167, 83, 83
ROWS = (21, 15)
ZERO = (False, True)  # symmetry and row parity force A[0]=-1, B[0]=+1


def chi(i: int) -> int:
    return 0 if i == 0 else (1 if pow(i, 83, N) == 1 else -1)


def xv(k: int, orbit: int) -> int:
    assert 1 <= orbit <= O
    return 1 + k * O + orbit - 1


def value_ref(k: int, i: int):
    if i % N == 0:
        return ZERO[k]
    orbit = min(i % N, (-i) % N)
    return xv(k, orbit)


def add_xor(solver, u, v, y: int) -> int:
    """Add y <-> u xor v where u,v are Boolean constants or positive vars."""
    if isinstance(u, bool) and isinstance(v, bool):
        solver.add_clause([y if u != v else -y])
        return 1
    if isinstance(u, bool):
        u, v = v, u
    if isinstance(v, bool):
        if v:  # y = not u
            solver.add_clause([-u, -y]); solver.add_clause([u, y])
        else:  # y = u
            solver.add_clause([-u, y]); solver.add_clause([u, -y])
        return 2
    if u == v:
        solver.add_clause([-y])
        return 1
    solver.add_clause([-u, -v, -y])
    solver.add_clause([u, v, -y])
    solver.add_clause([u, -v, y])
    solver.add_clause([-u, v, y])
    return 4


def main() -> None:
    p = argparse.ArgumentParser()
    p.add_argument("--conflicts", type=int, default=20_000_000)
    p.add_argument("--output", default="agent_gspec_two_paley_symmetric_candidate.json")
    q = p.parse_args()
    paley = [1 if i == 0 else chi(i) for i in range(N)]
    assert all(sum(paley[i] * paley[(i+d) % N] for i in range(N)) == -1 for d in range(1, N))
    started = time.time()
    next_var = 2 * O + 1
    clauses = 0
    native = 0
    with Minicard(use_timer=True) as solver:
        # For A, 47 of the 83 nonzero pairs are +1; for B, 45 are +1.
        for k, plus_pairs in enumerate((47, 45)):
            lits = [xv(k, o) for o in range(1, O + 1)]
            solver.add_atmost(lits, plus_pairs)
            solver.add_atmost([-x for x in lits], O - plus_pairs)
            native += 2
        # A common multiplier preserves centered symmetry and can send any
        # +1 orbit of the first row to orbit 1.
        solver.add_clause([xv(0, 1)])
        clauses += 1
        for d in range(1, H + 1):
            disagreements = []
            for k in range(2):
                for i in range(N):
                    y = next_var
                    next_var += 1
                    disagreements.append(y)
                    clauses += add_xor(solver, value_ref(k, i), value_ref(k, (i + d) % N), y)
            solver.add_atmost(disagreements, 166)
            solver.add_atmost([-y for y in disagreements], len(disagreements) - 166)
            native += 2
        print(json.dumps({"event":"model","primary_variables":2*O,"variables":next_var-1,"clauses":clauses,"native_atmost":native,"conflict_budget":q.conflicts,"build_s":time.time()-started}), flush=True)
        solver.conf_budget(q.conflicts)
        sat = solver.solve_limited(expect_interrupt=True)
        event = {"event":"result","sat":sat,"elapsed_s":time.time()-started,"accum_stats":solver.accum_stats()}
        if sat:
            model = {x for x in solver.get_model() if x > 0}
            seq = []
            for k in range(2):
                row = []
                for i in range(N):
                    ref = value_ref(k, i)
                    bit = ref if isinstance(ref, bool) else ref in model
                    row.append(1 if bit else -1)
                seq.append(row)
            seq += [paley, paley]
            r = [sum(seq[k][i] * seq[k][(i+d) % N] for k in range(4) for i in range(N)) for d in range(1, H+1)]
            out = {"construction":"cyclic Goethals-Seidel order 167, two Paley rows and two symmetric rows","solver":"agent reduced exact MiniCard","solved":not any(r),"independently_recomputed":True,"energy":sum(x*x for x in r),"l1":sum(abs(x) for x in r),"nonzero":sum(x!=0 for x in r),"maxabs":max(map(abs,r),default=0),"row_sums":[sum(x) for x in seq],"residual":r,"sequences":seq}
            assert out["solved"] and out["row_sums"] == [21,15,1,1]
            assert all(seq[k][i] == seq[k][-i % N] for k in range(2) for i in range(N))
            Path(q.output).write_text(json.dumps(out,separators=(",", ":"))+"\n",encoding="utf8")
            event["output"] = q.output
        print(json.dumps(event), flush=True)


if __name__ == "__main__":
    main()
