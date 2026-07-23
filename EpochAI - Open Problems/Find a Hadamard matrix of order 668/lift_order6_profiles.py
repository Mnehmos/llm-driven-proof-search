"""Lift-phase: decide the order-6 fiber pair model under each surviving
middle-layer profile. Each profile adds, for every Z_111 orbit, the equation
  sum over its 3 lift K-orbits of (2 x - 1) = c(orbit)
to the validated XOR/disagreement CP-SAT pair model. Chunked for foreground
runs: --start/--end select a profile range; results append to a jsonl.
"""
import argparse, json, time
import numpy as np
from collections import Counter
from pathlib import Path
from ortools.sat.python import cp_model

N3, N1 = 333, 111

def build_fiber(K):
    seen = [False]*N3; orbs = []
    for i in range(N3):
        if seen[i]: continue
        o = sorted({i*g % N3 for g in K})
        for t in o: seen[t] = True
        orbs.append(o)
    own = [0]*N3
    for j, o in enumerate(orbs):
        for i in o: own[i] = j
    return orbs, own

def lift_map(orbs333, own333, orb_reps111, K):
    """for each Z_111 orbit rep y: the 3 lift K-orbit ids on Z_333"""
    out = []
    for y in orb_reps111:
        lifts = [int(own333[(y + 111*j) % N3]) for j in range(3)]
        out.append(lifts)
    return out

def solve_profile(K, ca, cb, lmap, orbs, own, seconds, workers):
    sizes = [len(o) for o in orbs]
    m = cp_model.CpModel()
    X = [[m.NewBoolVar(f"x{s}_{j}") for j in range(len(orbs))] for s in range(2)]
    for s in range(2):
        m.Add(sum(sizes[j]*X[s][j] for j in range(len(orbs))) == 167)
    for s, prof in ((0, ca), (1, cb)):
        for oi, lifts in enumerate(lmap):
            m.Add(sum(2*X[s][j] - 1 for j in lifts) == int(prof[oi]))
    y = {}
    sseen = set()
    for d in range(1, N3):
        if d in sseen: continue
        sseen.update({d*g % N3 for g in K})
        terms = []
        for s in range(2):
            cnt = Counter()
            for i in range(N3):
                u, v = own[i], own[(i+d) % N3]
                if u == v: continue
                cnt[(min(u, v), max(u, v))] += 1
            for (u, v), w in cnt.items():
                key = (s, u, v)
                if key not in y:
                    z = m.NewBoolVar(f"y{s}_{u}_{v}")
                    m.AddBoolXOr([X[s][u], X[s][v], z.Not()])
                    y[key] = z
                terms.append(w * y[key])
        m.Add(sum(terms) == 334)
    slv = cp_model.CpSolver()
    slv.parameters.max_time_in_seconds = seconds
    slv.parameters.num_search_workers = workers
    t0 = time.time(); st = slv.Solve(m)
    res = {"status": slv.StatusName(st), "elapsed_s": round(time.time()-t0, 2),
           "conflicts": slv.NumConflicts()}
    if st in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        seq = [[1 if slv.Value(X[s][own[i]]) else -1 for i in range(N3)] for s in range(2)]
        bad = [d for d in range(1, N3)
               if sum(seq[s][i]*seq[s][(i+d) % N3] for s in range(2) for i in range(N3)) != -2]
        res["verified_paf"] = not bad
        res["sequences"] = seq
    return res

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--K", type=int, nargs="+", required=True)
    ap.add_argument("--start", type=int, default=0)
    ap.add_argument("--end", type=int, default=10**9)
    ap.add_argument("--seconds", type=float, default=20)
    ap.add_argument("--workers", type=int, default=8)
    ap.add_argument("--out", required=True)
    a = ap.parse_args()
    dat = np.load("middle_layer_survivors_order6.npz")
    PA, PB, orb_reps = dat["PA"], dat["PB"], list(dat["orb_reps"])
    K = a.K
    orbs, own = build_fiber(K)
    lmap = lift_map(orbs, own, orb_reps, K)
    out = Path(a.out); done = set()
    if out.exists():
        for line in out.read_text().splitlines():
            try: done.add(json.loads(line)["i"])
            except Exception: pass
    stats = Counter()
    for i in range(max(0, a.start), min(len(PA), a.end)):
        if i in done: continue
        r = solve_profile(K, PA[i], PB[i], lmap, orbs, own, a.seconds, a.workers)
        stats[r["status"]] += 1
        rec = {"i": i, **{k2: v for k2, v in r.items() if k2 != "sequences"}}
        if "sequences" in r: rec["sequences"] = r["sequences"]
        with out.open("a") as f: f.write(json.dumps(rec) + "\n")
        if r.get("verified_paf"):
            Path("lp333_order6_WITNESS.json").write_text(json.dumps({"K": K, **rec}))
            print("WITNESS FOUND at profile", i, flush=True)
            return
    print(json.dumps({"range": [a.start, min(len(PA), a.end)], "stats": dict(stats)}), flush=True)

if __name__ == "__main__":
    main()
