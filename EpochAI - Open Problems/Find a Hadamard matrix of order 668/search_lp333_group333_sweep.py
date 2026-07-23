"""Decisive sweep: 'Legendre pairs' over the NON-CYCLIC group G = Z_3 x Z_3 x Z_37.

A pair a,b: G -> {+-1} with sum(a)=sum(b)=+-1 and PAF_a(d)+PAF_b(d) = -2 for
all d != 0 yields a Hadamard matrix of order 2|G|+2 = 668 by the bordered
two-block array (validated end-to-end at G = Z_3 x Z_3 -> H(20) Gram check).
This group admits Aut(G) = GL(2,3) x Z_37^* of order 1728, far richer than
Z_333^*, so cyclic automorphism subgroups give many small decidable fibers.
Fibers are attacked by the generic orbit-partition CP-SAT encoding.
"""
import argparse, json, math, time
from collections import Counter
from pathlib import Path
from ortools.sat.python import cp_model

# ---- group G = Z_3 x Z_3 x Z_37 ----
ELEMS = [(i, j, k) for i in range(3) for j in range(3) for k in range(37)]
IDX = {g: n for n, g in enumerate(ELEMS)}
NG = 333

def g_add(g, h): return ((g[0]+h[0]) % 3, (g[1]+h[1]) % 3, (g[2]+h[2]) % 37)

# ---- automorphisms: (M in GL(2,3), u in Z_37^*) ----
def gl23():
    mats = []
    for a in range(3):
        for b in range(3):
            for c in range(3):
                for d in range(3):
                    if (a*d - b*c) % 3 != 0:
                        mats.append((a, b, c, d))
    return mats

def apply_aut(M, u, g):
    a, b, c, d = M
    return ((a*g[0] + b*g[1]) % 3, (c*g[0] + d*g[1]) % 3, (u*g[2]) % 37)

def partitions(max_orbits):
    seen = {}
    mats = gl23()
    units = [u for u in range(1, 37)]
    for M in mats:
        for u in units:
            if M == (1, 0, 0, 1) and u == 1:
                continue
            unvis = set(range(NG)); orbs = []
            while unvis:
                s0 = min(unvis); o = []
                g = ELEMS[s0]
                while True:
                    n = IDX[g]
                    if n not in unvis: break
                    o.append(n); unvis.discard(n)
                    g = apply_aut(M, u, g)
                orbs.append(tuple(sorted(o)))
            if len(orbs) > max_orbits: continue
            key = frozenset(orbs)
            if key not in seen:
                seen[key] = (M, u, [list(o) for o in orbs])
    return sorted(seen.values(), key=lambda z: len(z[2]))

def solve_partition(orbs, seconds, workers):
    own = [0]*NG
    for j, o in enumerate(orbs):
        for i in o: own[i] = j
    sizes = [len(o) for o in orbs]
    m = cp_model.CpModel()
    x = [[m.NewBoolVar(f"x{s}_{j}") for j in range(len(orbs))] for s in range(2)]
    for s in range(2):
        m.Add(sum(sizes[j]*x[s][j] for j in range(len(orbs))) == 167)
    y = {}
    for dn in range(1, NG):
        d = ELEMS[dn]
        terms = []
        for s in range(2):
            cnt = Counter()
            for i in range(NG):
                jn = IDX[g_add(ELEMS[i], d)]
                a, b = own[i], own[jn]
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
        seq = [[1 if slv.Value(x[s][own[i]]) else -1 for i in range(NG)] for s in range(2)]
        bad = []
        for dn in range(1, NG):
            d = ELEMS[dn]
            v = sum(seq[s][i]*seq[s][IDX[g_add(ELEMS[i], d)]] for s in range(2) for i in range(NG))
            if v != -2: bad.append(dn)
        res["verified_paf"] = not bad
        res["sequences"] = seq
    return res

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seconds", type=float, default=600)
    ap.add_argument("--workers", type=int, default=8)
    ap.add_argument("--max-orbits", type=int, default=60)
    ap.add_argument("--out", default="lp333_group333_sweep.jsonl")
    a = ap.parse_args()
    parts = partitions(a.max_orbits)
    print(json.dumps({"event": "classes", "count": len(parts),
                      "orbit_counts": sorted(len(p[2]) for p in parts)[:50]}), flush=True)
    out = Path(a.out); done = set()
    if out.exists():
        for line in out.read_text().splitlines():
            try:
                r = json.loads(line); done.add((tuple(r["M"]), r["u"]))
            except Exception: pass
    for M, u, orbs in parts:
        if (tuple(M), u) in done: continue
        r = solve_partition(orbs, a.seconds, a.workers)
        rec = {"M": list(M), "u": u, "orbits": len(orbs), "total_bits": 2*len(orbs),
               **{k: v for k, v in r.items() if k != "sequences"}}
        if "sequences" in r: rec["sequences"] = r["sequences"]
        print(json.dumps({k: v for k, v in rec.items() if k != "sequences"}), flush=True)
        with out.open("a") as f: f.write(json.dumps(rec) + "\n")
        if r.get("verified_paf"):
            Path("lp333_group333_WITNESS.json").write_text(json.dumps(rec))
            print("WITNESS FOUND", flush=True)
            return

if __name__ == "__main__":
    main()
