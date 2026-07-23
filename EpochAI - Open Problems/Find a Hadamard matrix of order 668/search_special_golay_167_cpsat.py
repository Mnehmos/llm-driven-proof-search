"""OR-Tools CP-SAT exact search for the 167-bit special Golay family."""

from __future__ import annotations

import argparse
import json
import time
from pathlib import Path

from ortools.sat.python import cp_model


def expand_runs(runs: list[int]) -> list[int]:
    return [1 if j % 2 == 0 else -1 for j, n in enumerate(runs) for _ in range(n)]


Q = expand_runs([83, 2, 81, 1])
F = [1] * 84 + [-1] * 83


def residual(s: list[int]) -> list[int]:
    seqs = [s, [x*f for x, f in zip(s,F)], [x*q for x,q in zip(s,Q)], [x*q*f for x,q,f in zip(s,Q,F)]]
    return [sum(a[i]*a[i+d] for a in seqs for i in range(167-d)) for d in range(1,167)]


def main() -> int:
    p = argparse.ArgumentParser()
    p.add_argument("--seconds", type=float, default=600)
    p.add_argument("--workers", type=int, default=12)
    p.add_argument("--seed", type=int, default=668)
    p.add_argument("--hint", type=Path, default=Path("Find a Hadamard matrix of order 668/special_golay_167_native_summary.json"))
    p.add_argument("--output", type=Path, default=Path("Find a Hadamard matrix of order 668/special_golay_167_candidate.json"))
    args = p.parse_args()

    started = time.time()
    model = cp_model.CpModel()
    s = [model.new_bool_var(f"s_{i}") for i in range(167)]
    model.add(s[0] == 0)
    model.add(s[84] == 0)  # independent sign normalization of the second half

    # Redundant norm-at-one identity.  Writing s and s*q as left/right
    # halves gives four row sums whose squares must total 2*167 = 334.
    sl = model.new_int_var(-84, 84, "sl")
    sr = model.new_int_var(-83, 83, "sr")
    tl = model.new_int_var(-84, 84, "tl")
    tr = model.new_int_var(-83, 83, "tr")
    model.add(sl == 84 - 2 * sum(s[:84]))
    model.add(sr == 83 - 2 * sum(s[84:]))
    model.add(tl == sum(Q[:84]) - 2 * sum(Q[i] * s[i] for i in range(84)))
    model.add(tr == sum(Q[84:]) - 2 * sum(Q[i] * s[i] for i in range(84, 167)))
    row_tuples = [(a,b,c,d) for a in range(-18,19,2) for b in range(-17,18,2)
                  for c in range(-18,19,2) for d in range(-17,18,2)
                  if a*a+b*b+c*c+d*d == 334
                  and abs(c-a) == 2 and d-b in (-4,0)]
    model.add_allowed_assignments([sl,sr,tl,tr], row_tuples)
    xor_count = 0
    for d in range(1,84):
        ys = []
        for i in range(167-d):
            j = i+d
            if F[i] == F[j] and Q[i] == Q[j]:
                y = model.new_bool_var(f"x_{i}_{j}")
                model.add_bool_xor([s[i], s[j], y.Not()])
                ys.append(y)
        xor_count += len(ys)
        if ys:
            model.add(sum(ys) == len(ys)//2)
            # Make the mod-2 consequence explicit so CP-SAT's XOR Gaussian
            # elimination can reduce the 167 sign variables before CDCL.
            model.add_bool_xor(ys if (len(ys)//2) % 2 else ys + [True])

    if args.hint.exists():
        data = json.loads(args.hint.read_text(encoding="utf-8"))
        hint = data.get("s")
        if hint and len(hint) == 167:
            if hint[0] == -1:
                hint[:84] = [-x for x in hint[:84]]
            if hint[84] == -1:
                hint[84:] = [-x for x in hint[84:]]
            for var, sign in zip(s, hint):
                model.add_hint(var, 0 if sign == 1 else 1)

    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = args.seconds
    solver.parameters.num_workers = args.workers
    solver.parameters.random_seed = args.seed
    solver.parameters.symmetry_level = 3
    solver.parameters.log_search_progress = True
    print(json.dumps({"event":"built","base_variables":167,"xor_variables":xor_count,"row_sum_tuples":len(row_tuples),"elapsed_s":time.time()-started}), flush=True)
    status = solver.solve(model)
    print(json.dumps({"event":"result","status":solver.status_name(status),"elapsed_s":time.time()-started,"conflicts":solver.num_conflicts,"branches":solver.num_branches}), flush=True)
    if status not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        return 2
    signs = [1 if solver.value(x) == 0 else -1 for x in s]
    r = residual(signs)
    if any(r):
        raise RuntimeError(f"CP-SAT model failed independent check: {[(i+1,x) for i,x in enumerate(r) if x]}")
    seqs = [signs, [x*f for x,f in zip(signs,F)], [x*q for x,q in zip(signs,Q)], [x*q*f for x,q,f in zip(signs,Q,F)]]
    payload={"construction":"special Golay quadruple length 167","solver":"OR-Tools CP-SAT","elapsed_s":time.time()-started,"residual":r,"sequences":seqs}
    args.output.write_text(json.dumps(payload,indent=2)+"\n",encoding="utf-8")
    print(json.dumps({"event":"verified_witness","output":str(args.output),"row_sums":[sum(x) for x in seqs]}),flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
