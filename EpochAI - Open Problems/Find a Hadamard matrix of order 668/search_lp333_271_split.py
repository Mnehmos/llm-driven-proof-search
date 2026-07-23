"""Divide-and-conquer decision of the <271> LP(333) fiber.

The fiber's 9 fixed points per sequence (multiples of 37, indexed by Z_9)
must carry exactly 5 ones; the 36 nine-orbits carry exactly 18 ones. Fixing
both fixed-point patterns (F_a, F_b) leaves 72 free bits per sub-fiber.
Decimation by units v of Z_333^* normalizes K=<271>, acting on the fixed
points through v mod 9 (units of Z_9 = Z_6) simultaneously on both
sequences; (a,b) swap is also a symmetry. Sub-fibers are enumerated up to
this group of order 12, so a complete pass decides the whole fiber.
Each sub-fiber: CP-SAT with the validated XOR/disagreement encoding.
"""
import argparse, itertools, json, time
from collections import Counter
from pathlib import Path
from ortools.sat.python import cp_model

N = 333
K = []
x = 1
while True:
    K.append(x); x = x*271 % N
    if x == 1: break
K = sorted(K); assert len(K) == 9

seen = [False]*N; orbs = []
for i in range(N):
    if seen[i]: continue
    o = sorted({i*g % N for g in K})
    for t in o: seen[t] = True
    orbs.append(o)
own = [0]*N
for j, o in enumerate(orbs):
    for i in o: own[i] = j
sizes = [len(o) for o in orbs]
fixed = [j for j, s in enumerate(sizes) if s == 1]     # orbit ids of fixed pts
nines = [j for j, s in enumerate(sizes) if s == 9]
# map fixed orbit id -> its Z_9 index (fixed points are 37*m)
fix_by_m = {}
for j in fixed:
    (pt,) = orbs[j]
    assert pt % 37 == 0
    fix_by_m[pt // 37] = j

UNITS9 = [1, 2, 4, 5, 7, 8]

def canon(pa, pb):
    """canonical form of (frozenset,frozenset) under m->v*m and swap"""
    best = None
    for v in UNITS9:
        qa = frozenset((v*m) % 9 for m in pa)
        qb = frozenset((v*m) % 9 for m in pb)
        for cand in ((tuple(sorted(qa)), tuple(sorted(qb))),
                     (tuple(sorted(qb)), tuple(sorted(qa)))):
            if best is None or cand < best: best = cand
    return best

def sub_fibers():
    reps = {}
    fives = [frozenset(c) for c in itertools.combinations(range(9), 5)]
    for pa in fives:
        for pb in fives:
            c = canon(pa, pb)
            if c not in reps: reps[c] = (sorted(pa), sorted(pb))
    return sorted(reps.values())

def solve_sub(pa, pb, seconds, workers):
    m = cp_model.CpModel()
    X = [[m.NewBoolVar(f"x{s}_{j}") for j in range(len(orbs))] for s in range(2)]
    for s, pat in ((0, pa), (1, pb)):
        for mm in range(9):
            v = X[s][fix_by_m[mm]]
            m.Add(v == (1 if mm in pat else 0))
        m.Add(sum(X[s][j] for j in nines) == 18)
    y = {}
    # deduplicated shift constraints (PAF K-invariant in shift)
    shift_seen = set()
    for d in range(1, N):
        if d in shift_seen: continue
        shift_seen.update({d*g % N for g in K})
        terms = []
        for s in range(2):
            cnt = Counter()
            for i in range(N):
                u, v = own[i], own[(i+d) % N]
                if u == v: continue
                cnt[(min(u, v), max(u, v))] += 1
            for (u, v), coef in cnt.items():
                key = (s, u, v)
                if key not in y:
                    z = m.NewBoolVar(f"y{s}_{u}_{v}")
                    m.AddBoolXOr([X[s][u], X[s][v], z.Not()])
                    y[key] = z
                terms.append(coef * y[key])
        m.Add(sum(terms) == 334)
    slv = cp_model.CpSolver()
    slv.parameters.max_time_in_seconds = seconds
    slv.parameters.num_search_workers = workers
    t0 = time.time(); st = slv.Solve(m)
    res = {"status": slv.StatusName(st), "elapsed_s": round(time.time()-t0, 2),
           "conflicts": slv.NumConflicts()}
    if st in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        seq = [[1 if slv.Value(X[s][own[i]]) else -1 for i in range(N)] for s in range(2)]
        bad = [d for d in range(1, N)
               if sum(seq[s][i]*seq[s][(i+d) % N] for s in range(2) for i in range(N)) != -2]
        res["verified_paf"] = not bad
        res["sequences"] = seq
    return res

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seconds", type=float, default=60)
    ap.add_argument("--workers", type=int, default=2)
    ap.add_argument("--out", default="lp333_271_split.jsonl")
    ap.add_argument("--start", type=int, default=0)
    ap.add_argument("--end", type=int, default=10**9)
    a = ap.parse_args()
    subs = sub_fibers()
    print(json.dumps({"event": "subfibers", "count": len(subs)}), flush=True)
    out = Path(a.out); done = set()
    if out.exists():
        for line in out.read_text().splitlines():
            try:
                r = json.loads(line); done.add((tuple(r["pa"]), tuple(r["pb"])))
            except Exception: pass
    unknowns = 0
    for i, (pa, pb) in enumerate(subs):
        if not (a.start <= i < a.end): continue
        if (tuple(pa), tuple(pb)) in done: continue
        r = solve_sub(pa, pb, a.seconds, a.workers)
        rec = {"i": i, "pa": pa, "pb": pb, **{k: v for k, v in r.items() if k != "sequences"}}
        if "sequences" in r: rec["sequences"] = r["sequences"]
        print(json.dumps({k: v for k, v in rec.items() if k != "sequences"}), flush=True)
        with out.open("a") as f: f.write(json.dumps(rec) + "\n")
        if r["status"] == "UNKNOWN": unknowns += 1
        if r.get("verified_paf"):
            Path("lp333_271_WITNESS.json").write_text(json.dumps(rec))
            print("WITNESS FOUND", flush=True)
            return
    print(json.dumps({"event": "done", "unknown_subfibers": unknowns}), flush=True)

if __name__ == "__main__":
    main()
