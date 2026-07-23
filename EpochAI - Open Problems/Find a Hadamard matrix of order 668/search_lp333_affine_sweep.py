"""Decisive sweep: LP(333) pairs invariant under fixed-point-free AFFINE maps.

phi(x) = u*x + t on Z_333 with gcd(u-1,333) not dividing t (no fixed point).
Such phi is NOT conjugate to a multiplication, so these orbit partitions are
new symmetry classes beyond every multiplier sweep. The XOR/disagreement
CP-SAT encoding only needs the orbit partition, so it applies verbatim.
Partitions are deduped exactly (as frozensets of orbits) and attacked in
order of increasing free bits.
"""
import argparse, json, math, time
from collections import Counter
from pathlib import Path
from ortools.sat.python import cp_model

N = 333

def affine_partitions(max_orbits):
    seen = {}
    units = [u for u in range(2, N) if math.gcd(u, N) == 1]
    for u in units:
        g = math.gcd(u - 1, N)
        if g == 1:
            continue  # always has a fixed point -> conjugate to multiplier class
        for t in range(1, N):
            if t % g == 0:
                continue  # fixed point exists
            # build orbit partition of <phi>
            unvisited = set(range(N)); orbs = []
            while unvisited:
                x0 = min(unvisited); o = []
                x = x0
                while True:
                    o.append(x); unvisited.discard(x)
                    x = (u * x + t) % N
                    if x == x0: break
                orbs.append(tuple(sorted(o)))
            key = frozenset(orbs)
            if len(orbs) <= max_orbits and key not in seen:
                seen[key] = (u, t, [list(o) for o in orbs])
    return sorted(seen.values(), key=lambda z: len(z[2]))

def solve_partition(orbs, seconds, workers):
    own = [0]*N
    for j, o in enumerate(orbs):
        for i in o: own[i] = j
    sizes = [len(o) for o in orbs]
    m = cp_model.CpModel()
    x = [[m.NewBoolVar(f"x{s}_{j}") for j in range(len(orbs))] for s in range(2)]
    for s in range(2):
        m.Add(sum(sizes[j]*x[s][j] for j in range(len(orbs))) == 167)
    y = {}
    for d in range(1, N):
        terms = []
        for s in range(2):
            cnt = Counter()
            for i in range(N):
                a, b = own[i], own[(i+d) % N]
                if a == b: continue
                cnt[(min(a, b), max(a, b))] += 1
            for (a, b), coef in cnt.items():
                key = (s, a, b)
                if key not in y:
                    z = m.NewBoolVar(f"y{s}_{a}_{b}")
                    m.AddBoolXOr([x[s][a], x[s][b], z.Not()])
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
        seq = [[1 if slv.Value(x[s][own[i]]) else -1 for i in range(N)] for s in range(2)]
        bad = [d for d in range(1, N)
               if sum(seq[s][i]*seq[s][(i+d) % N] for s in range(2) for i in range(N)) != -2]
        res["verified_paf"] = not bad
        res["sequences"] = seq
    return res

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seconds", type=float, default=600)
    ap.add_argument("--workers", type=int, default=8)
    ap.add_argument("--max-orbits", type=int, default=60)
    ap.add_argument("--out", default="lp333_affine_sweep.jsonl")
    a = ap.parse_args()
    parts = affine_partitions(a.max_orbits)
    print(json.dumps({"event": "classes", "count": len(parts),
                      "orbit_counts": sorted(len(p[2]) for p in parts)}), flush=True)
    out = Path(a.out)
    done = set()
    if out.exists():
        for line in out.read_text().splitlines():
            try:
                r = json.loads(line); done.add((r["u"], r["t"]))
            except Exception: pass
    for u, t, orbs in parts:
        if (u, t) in done: continue
        r = solve_partition([tuple(o) for o in orbs], a.seconds, a.workers)
        rec = {"u": u, "t": t, "orbits": len(orbs), "total_bits": 2*len(orbs), **{k: v for k, v in r.items() if k != "sequences"}}
        if "sequences" in r: rec["sequences"] = r["sequences"]
        print(json.dumps({k: v for k, v in rec.items() if k != "sequences"}), flush=True)
        with out.open("a") as f: f.write(json.dumps(rec) + "\n")
        if r["status"] in ("OPTIMAL", "FEASIBLE") and r.get("verified_paf"):
            print("WITNESS FOUND — stopping", flush=True)
            Path("lp333_affine_WITNESS.json").write_text(json.dumps(rec))
            return

if __name__ == "__main__":
    main()
