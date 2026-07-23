"""Direct exact CP-SAT search for a cyclic GS difference family on Z_167."""
import argparse, json, time
from pathlib import Path
from ortools.sat.python import cp_model

N, H = 167, 83


def load_hint(path):
    data = json.loads(Path(path).read_text(encoding="utf8"))
    seq = data.get("sequences")
    if len(seq) != 4 or any(len(a) != N for a in seq):
        raise ValueError("hint must contain four length-167 sequences")
    return seq


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--hint", required=True)
    p.add_argument("--seconds", type=float, default=900)
    p.add_argument("--workers", type=int, default=4)
    p.add_argument("--seed", type=int, default=668167)
    p.add_argument("--max-changes", type=int, default=100)
    p.add_argument("--active", type=int, default=4, choices=(1,2,3,4),
                   help="number of leading sequences allowed to change")
    p.add_argument("--fix-zero", action="store_true",
                   help="break independent cyclic-shift symmetry with x[k,0]=+1")
    p.add_argument("--optimize-l1", action="store_true")
    p.add_argument("--output", default="gs_167_cpsat_candidate.json")
    q = p.parse_args()
    hint = load_hint(q.hint)
    rows = [sum(a) for a in hint]
    if sum(r*r for r in rows) != 4*N:
        raise ValueError("row-sum square identity failed")

    model = cp_model.CpModel()
    x = [[model.NewBoolVar(f"x_{k}_{i}") for i in range(N)] for k in range(4)]
    for k in range(4):
        model.Add(sum(x[k]) == (N + rows[k]) // 2)
        if q.fix_zero:
            model.Add(x[k][0] == 1)
        if k >= q.active:
            for i in range(N):
                model.Add(x[k][i] == (1 if hint[k][i] == 1 else 0))
    deviations = []
    for d in range(1, H+1):
        ys = []
        for k in range(4):
            for i in range(N):
                y = model.NewBoolVar(f"xor_{k}_{d}_{i}")
                model.AddBoolXOr([x[k][i], x[k][(i+d) % N], y.Not()])
                ys.append(y)
        if q.optimize_l1:
            dev = model.NewIntVar(0, 334, f"dev_{d}")
            model.AddAbsEquality(dev, sum(ys) - 334)
            deviations.append(dev)
        else:
            model.Add(sum(ys) == 334)
    if deviations:
        model.Minimize(sum(deviations))

    changes = []
    for k in range(4):
        for i in range(N):
            value = 1 if hint[k][i] == 1 else 0
            model.AddHint(x[k][i], value)
            c = model.NewBoolVar(f"change_{k}_{i}")
            model.Add(x[k][i] != value).OnlyEnforceIf(c)
            model.Add(x[k][i] == value).OnlyEnforceIf(c.Not())
            changes.append(c)
    if q.max_changes:
        model.Add(sum(changes) <= q.max_changes)

    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = q.seconds
    solver.parameters.num_search_workers = q.workers
    solver.parameters.random_seed = q.seed
    started = time.time(); status = solver.Solve(model); elapsed = time.time()-started
    result = {"event":"result", "status":solver.StatusName(status), "elapsed_s":elapsed,
              "max_changes":q.max_changes, "active":q.active, "fix_zero":q.fix_zero, "optimize_l1":q.optimize_l1,
              "conflicts":solver.NumConflicts(), "branches":solver.NumBranches(),
              "wall_time":solver.WallTime()}
    if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        seq = [[1 if solver.Value(x[k][i]) else -1 for i in range(N)] for k in range(4)]
        residual = [sum(seq[k][i] * seq[k][(i+d) % N] for k in range(4) for i in range(N))
                    for d in range(1, H+1)]
        out = {"construction":"cyclic Goethals-Seidel order 167", "solver":"direct CP-SAT",
               "solved":not any(residual), "energy":sum(z*z for z in residual),
               "l1":sum(map(abs, residual)), "nonzero":sum(z != 0 for z in residual),
               "maxabs":max(map(abs, residual)), "row_sums":[sum(a) for a in seq],
               "hamming_from_hint":sum(seq[k][i] != hint[k][i] for k in range(4) for i in range(N)),
               "residual":residual, "sequences":seq}
        assert out["row_sums"] == rows
        if not q.optimize_l1:
            assert out["solved"]
        Path(q.output).write_text(json.dumps(out, separators=(",", ":")) + "\n", encoding="utf8")
        result.update(output=q.output, energy=out["energy"], l1=out["l1"],
                      nonzero=out["nonzero"], hamming_from_hint=out["hamming_from_hint"])
    print(json.dumps(result), flush=True)


if __name__ == "__main__":
    main()
