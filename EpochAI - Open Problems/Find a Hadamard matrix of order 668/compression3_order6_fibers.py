"""3-compression layers of the six resistant order-6 LP(333) pair fibers.

For each order-6 subgroup K = <g> with an UNKNOWN pair fiber, any K-invariant
LP(333) pair compresses (x -> x mod 111, summing the three lifts) to a pair
of <g mod 111>-invariant sequences on Z_111 with entries in {-3,-1,1,3},
row sums 1, and PAF_ca(d)+PAF_cb(d) = -6 for d != 0. The compressed layer is
decided by CP-SAT over integer variables with domain {-3,-1,1,3} (via 2-bit
channeling). EMPTY layer => the original fiber is closed unconditionally.
The compression identity is re-verified numerically per subgroup first.
"""
import json, math, time
import numpy as np
from collections import Counter
from ortools.sat.python import cp_model
from pathlib import Path

N3, N1 = 333, 111

RESISTANT = [
    [1, 10, 26, 100, 260, 269],
    [1, 121, 137, 158, 260, 322],
    [1, 73, 85, 211, 232, 286],
    [1, 47, 211, 232, 248, 260],
    [1, 10, 64, 73, 100, 307],
    [1, 73, 121, 175, 196, 322],
]

def orbits_on_z111(Kimg):
    seen = [False]*N1; orbs = []
    for i in range(N1):
        if seen[i]: continue
        o = sorted({i*g % N1 for g in Kimg})
        for t in o: seen[t] = True
        orbs.append(o)
    own = [0]*N1
    for j, o in enumerate(orbs):
        for i in o: own[i] = j
    return orbs, own

def decide_layer(K, seconds=600, workers=8):
    Kimg = sorted({g % N1 for g in K})
    # closure of image (should already be a group)
    img = {1}
    for g in Kimg:
        x = 1
        while True:
            x = x*g % N1
            if x in img: break
            img.add(x)
    img = sorted(img)
    orbs, own = orbits_on_z111(img)
    k = len(orbs)
    sizes = [len(o) for o in orbs]
    # numeric identity check: random K-invariant a on Z_333 -> compressed
    # sequence must be constant on img-orbits of Z_111
    rng = np.random.default_rng(1)
    # build K-orbits on Z_333
    seen3 = [False]*N3; orbs3 = []
    for i in range(N3):
        if seen3[i]: continue
        o = sorted({i*g % N3 for g in K})
        for t in o: seen3[t] = True
        orbs3.append(o)
    vals = rng.choice([1, -1], size=len(orbs3))
    a = np.empty(N3, dtype=np.int64)
    for j, o in enumerate(orbs3):
        for i in o: a[i] = vals[j]
    c = np.array([a[x] + a[(x+111) % N3] + a[(x+222) % N3] for x in range(N1)])
    for o in orbs:
        assert len(set(int(c[i]) for i in o)) == 1, "compressed not orbit-constant!"
    # CP-SAT over domains {-3,-1,1,3}
    m = cp_model.CpModel()
    V = [[m.NewIntVar(-3, 3, f"c{s}_{j}") for j in range(k)] for s in range(2)]
    for s in range(2):
        for j in range(k):
            m.AddForbiddenAssignments([V[s][j]], [(-2,), (0,), (2,)])
        m.Add(sum(sizes[j]*V[s][j] for j in range(k)) == 1)
    # PAF products: introduce products p_{s,u,v} = V_u * V_v via AddMultiplicationEquality
    prod = {}
    def pv(s, u, v):
        key = (s, min(u, v), max(u, v))
        if key not in prod:
            p = m.NewIntVar(-9, 9, f"p{key}")
            m.AddMultiplicationEquality(p, [V[s][key[1]], V[s][key[2]]])
            prod[key] = p
        return prod[key]
    sseen = set()
    nrep = 0
    for d in range(1, N1):
        if d in sseen: continue
        sseen.update({d*g % N1 for g in img})
        nrep += 1
        terms = []
        for s in range(2):
            cnt = Counter()
            for i in range(N1):
                cnt[(s, own[i], own[(i+d) % N1])] += 1
            for (s_, u, v), w in cnt.items():
                terms.append(w * pv(s_, u, v))
        m.Add(sum(terms) == -6)
    slv = cp_model.CpSolver()
    slv.parameters.max_time_in_seconds = seconds
    slv.parameters.num_search_workers = workers
    t0 = time.time(); st = slv.Solve(m)
    res = {"K": K, "img_order": len(img), "orbits": k, "shift_reps": nrep,
           "status": slv.StatusName(st), "elapsed_s": round(time.time()-t0, 1),
           "conflicts": slv.NumConflicts()}
    if st in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        cvals = [[slv.Value(V[s][j]) for j in range(k)] for s in range(2)]
        res["compressed_pair"] = cvals
        # independent verification
        cseq = [[cvals[s][own[i]] for i in range(N1)] for s in range(2)]
        bad = [d for d in range(1, N1)
               if sum(cseq[s][i]*cseq[s][(i+d) % N1] for s in range(2) for i in range(N1)) != -6]
        res["verified"] = not bad
    return res

if __name__ == "__main__":
    out = Path("lp333_order6_compression3.jsonl")
    done = set()
    if out.exists():
        for line in out.read_text().splitlines():
            try:
                r = json.loads(line); done.add(tuple(r["K"]))
            except Exception: pass
    for K in RESISTANT:
        if tuple(K) in done: continue
        r = decide_layer(K)
        print(json.dumps(r), flush=True)
        with out.open("a") as f: f.write(json.dumps(r) + "\n")
