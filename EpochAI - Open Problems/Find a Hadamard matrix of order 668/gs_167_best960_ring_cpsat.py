#!/usr/bin/env python3
from __future__ import annotations

import json
from pathlib import Path

try:
    from ortools.sat.python import cp_model
except ImportError as exc:
    raise SystemExit("Install ortools to run this model: pip install ortools") from exc


SPEC_PATH = Path(__file__).with_name("gs_167_best960_ring.json")


def load_spec() -> dict:
    with SPEC_PATH.open("r", encoding="utf-8") as handle:
        return json.load(handle)


def build_model(spec: dict, K: int, force_M_le: int | None = None, weighted_cap: int | None = None):
    model = cp_model.CpModel()
    n = int(spec["n"])
    blocks = int(spec["blocks"])
    focus_shifts = [int(t) for t in spec["focus_shifts"]]
    guard_shifts = [int(t) for t in spec.get("guard_shifts", [])]
    monitored_shifts = list(dict.fromkeys(focus_shifts + guard_shifts))
    weights = {int(k): int(v) for k, v in spec["weights"].items()}
    guard_caps = {int(k): int(v) for k, v in spec.get("guard_abs_caps", {}).items()}
    c = spec["occupancy"]
    k = [int(v) for v in spec["block_sizes"]]
    pool = [tuple(item) for item in spec["candidate_pool"]]
    free = [[False] * n for _ in range(blocks)]
    for row_idx, g in pool:
        free[row_idx][g] = True

    x = {}
    for row_idx, g in pool:
        x[(row_idx, g)] = model.NewBoolVar(f"x_{row_idx}_{g}")

    shift_exprs = spec["shift_expressions"]
    p = {}
    for t in monitored_shifts:
        for item in shift_exprs[str(t)]["quadratic_terms"]:
            row_idx = int(item["row"])
            g = int(item["g"])
            g2 = int(item["partner"])
            key = (row_idx, g, g2, t)
            p[key] = model.NewBoolVar(f"p_{row_idx}_{g}_{g2}_{t}")
            model.Add(p[key] <= x[(row_idx, g)])
            model.Add(p[key] <= x[(row_idx, g2)])
            model.Add(p[key] >= x[(row_idx, g)] + x[(row_idx, g2)] - 1)

    # exact block sizes
    for row_idx in range(blocks):
        fixed_total = sum(int(c[row_idx][g]) for g in range(n) if not free[row_idx][g])
        expr = fixed_total + sum(x[(i, g)] for i, g in pool if i == row_idx)
        model.Add(expr == k[row_idx])

    d = {}
    u = {}
    M = model.NewIntVar(0, 1000, "M")
    for t in monitored_shifts:
        d[t] = model.NewIntVar(-1000, 1000, f"d_{t}")
        u[t] = model.NewIntVar(0, 1000, f"u_{t}")

    for t in monitored_shifts:
        shift_expr = shift_exprs[str(t)]
        expr = int(shift_expr["base_minus_lambda"])
        for item in shift_expr["linear_terms"]:
            expr += int(item["coeff"]) * x[(int(item["row"]), int(item["g"]))]
        for item in shift_expr["quadratic_terms"]:
            expr += int(item["coeff"]) * p[(int(item["row"]), int(item["g"]), int(item["partner"]), t)]
        model.Add(d[t] == expr)
        model.Add(d[t] <= u[t])
        model.Add(-d[t] <= u[t])
        if t in focus_shifts:
            model.Add(u[t] <= int(spec["current_abs_deltas"][str(t)]))
            model.Add(u[t] <= M)
        else:
            model.Add(u[t] <= int(guard_caps[t]))

    if force_M_le is not None:
        model.Add(M <= int(force_M_le))

    if weighted_cap is not None:
        model.Add(sum(weights[t] * u[t] for t in focus_shifts) <= int(weighted_cap))

    flip_terms = []
    for row_idx, g in pool:
        if int(c[row_idx][g]) == 0:
            flip_terms.append(x[(row_idx, g)])
        else:
            flip_terms.append(1 - x[(row_idx, g)])
    F = model.NewIntVar(0, len(pool), "F")
    model.Add(F == sum(flip_terms))
    model.Add(F <= int(K))

    return model, M, u, F


def solve_lexicographic(spec: dict):
    # schedule from the exported instance
    for K, force_M_le, weighted_cap in spec["recommended_schedule"]:
        model, M, u, F = build_model(spec, K=K, force_M_le=force_M_le, weighted_cap=weighted_cap)
        model.Minimize(M)
        solver = cp_model.CpSolver()
        status = solver.Solve(model)
        print("tier", (K, force_M_le, weighted_cap), "status", solver.StatusName(status))
        if status not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
            continue
        best_M = int(solver.Value(M))

        model2, M2, u2, F2 = build_model(spec, K=K, force_M_le=best_M, weighted_cap=weighted_cap)
        weighted_expr = sum(int(spec["weights"][str(t)]) * u2[t] for t in spec["focus_shifts"])
        model2.Minimize(weighted_expr)
        solver2 = cp_model.CpSolver()
        status2 = solver2.Solve(model2)
        print("  weighted status", solver2.StatusName(status2))
        if status2 not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
            continue
        best_weighted = int(solver2.Value(weighted_expr))

        model3, M3, u3, F3 = build_model(spec, K=K, force_M_le=best_M, weighted_cap=best_weighted)
        model3.Minimize(F3)
        solver3 = cp_model.CpSolver()
        status3 = solver3.Solve(model3)
        print("  flip status", solver3.StatusName(status3))
        if status3 not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
            continue
        print("  solved tier with M=", best_M, "weighted=", best_weighted, "F=", solver3.Value(F3))
        return

    print("No feasible tier found in recommended schedule.")


if __name__ == "__main__":
    solve_lexicographic(load_spec())
