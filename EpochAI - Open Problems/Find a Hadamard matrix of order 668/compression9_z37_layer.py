"""Z_37 (9-fold) compression layer of LP(333) fibers - pure exhaustion.

For K-invariant a on Z_333, define d_a(y) = sum of a over the 9 lifts of
y in Z_37 (x with x = y mod 37). Entries are odd integers in [-9, 9];
sum(d_a) = 1; d_a is invariant under the image of K in Z_37^*; and
PAF_da(s) + PAF_db(s) = -2*9 = -18 for every nonzero s in Z_37
(PAF_d(s) = sum over lifts identity, verified numerically here first).

For an order-6 image <w> in Z_37^*: orbits on Z_37 = {0} + six 6-orbits
= 7 orbit values -> at most 10^7 candidates per side before filters.
EMPTY layer => the original LP(333) fiber is closed unconditionally.
"""
import itertools, json, sys, time
import numpy as np

N3, P = 333, 37

def check_identity(K):
    rng = np.random.default_rng(2)
    seen = [False]*N3; orbs3 = []
    for i in range(N3):
        if seen[i]: continue
        o = sorted({i*g % N3 for g in K})
        for t in o: seen[t] = True
        orbs3.append(o)
    vals = rng.choice([1, -1], size=len(orbs3))
    a = np.empty(N3, dtype=np.int64)
    for j, o in enumerate(orbs3):
        for i in o: a[i] = vals[j]
    d = np.array([a[[x for x in range(N3) if x % P == y]].sum() for y in range(P)])
    # invariance under image
    img = sorted({g % P for g in K})
    for w in img:
        assert all(d[(w*y) % P] == d[y] for y in range(P)), "image invariance FAILED"
    s = int(rng.integers(1, P))
    lhs = int(np.dot(d, np.roll(d, -s)))
    rhs = sum(int(np.dot(a, np.roll(a, -(s + P*k)))) for k in range(9))
    assert lhs == rhs, "compression identity FAILED"
    return True

def cpsat_z37_layer(sizes, own, C, reps, seconds=180, workers=8):
    """Small quadratic CP-SAT for 13-orbit layers: two odd-domain vectors,
    products via AddMultiplicationEquality, PAF sum -18 per rep."""
    from ortools.sat.python import cp_model
    k = len(sizes)
    m = cp_model.CpModel()
    V = [[m.NewIntVar(-9, 9, f"d{s}_{j}") for j in range(k)] for s in range(2)]
    for s in range(2):
        for j in range(k):
            m.AddForbiddenAssignments([V[s][j]], [(v,) for v in range(-8, 9, 2)])
        m.Add(sum(sizes[j]*V[s][j] for j in range(k)) == 1)
    prod = {}
    def pv(s, u, v):
        key = (s, min(u, v), max(u, v))
        if key not in prod:
            p = m.NewIntVar(-81, 81, f"p{key}")
            m.AddMultiplicationEquality(p, [V[s][key[1]], V[s][key[2]]])
            prod[key] = p
        return prod[key]
    R = len(reps)
    for ri in range(R):
        terms = []
        for s in range(2):
            for u in range(k):
                for v in range(k):
                    w = int(C[ri, u, v])
                    if w: terms.append(w * pv(s, u, v))
        m.Add(sum(terms) == -18)
    slv = cp_model.CpSolver()
    slv.parameters.max_time_in_seconds = seconds
    slv.parameters.num_search_workers = workers
    st = slv.Solve(m)
    out = {"orbits": k, "reps": R, "status": slv.StatusName(st),
           "conflicts": slv.NumConflicts(), "engine": "cpsat-quadratic"}
    if st in (2, 4):  # OPTIMAL/FEASIBLE
        out["example"] = [[slv.Value(V[s][j]) for j in range(k)] for s in range(2)]
        out["status"] = "NONEMPTY"
    elif out["status"] == "INFEASIBLE":
        out["status"] = "EMPTY_CPSAT"
    return out

def decide_z37_layer(K):
    check_identity(K)
    img = {1}
    for g in {g % P for g in K}:
        x = 1
        while True:
            x = x*g % P
            if x in img: break
            img.add(x)
    img = sorted(img)
    seen = [False]*P; orbs = []
    for i in range(P):
        if seen[i]: continue
        o = sorted({i*g % P for g in img})
        for t in o: seen[t] = True
        orbs.append(o)
    own = [0]*P
    for j, o in enumerate(orbs):
        for i in o: own[i] = j
    sizes = [len(o) for o in orbs]
    k = len(orbs)
    # shift reps under img
    sseen = set(); reps = []
    for s in range(1, P):
        if s in sseen: continue
        sseen.update({s*g % P for g in img}); reps.append(s)
    C = np.zeros((len(reps), k, k), dtype=np.int64)
    for ri, s in enumerate(reps):
        for i in range(P):
            C[ri, own[i], own[(i+s) % P]] += 1
    # enumerate all odd-entry vectors in [-9,9]^k with weighted sum 1
    ALPH = np.arange(-9, 10, 2, dtype=np.int64)   # 10 odd values
    tot = len(ALPH)**k
    if tot > 20_000_000:
        return cpsat_z37_layer(sizes, own, C, reps)
    combos = np.array(list(itertools.product(ALPH, repeat=k)), dtype=np.int64)
    w = np.array(sizes, dtype=np.int64)
    valid = combos[(combos @ w) == 1]
    # PAF vectors
    f = valid.astype(np.float64)
    V = np.empty((len(valid), len(reps)), dtype=np.int64)
    for r in range(len(reps)):
        V[:, r] = np.round(((f @ C[r]) * f).sum(1)).astype(np.int64)
    rng = np.random.default_rng(9)
    rvec = rng.integers(1, 1 << 62, size=len(reps), dtype=np.int64)
    h = V @ rvec; t = (-18 - V) @ rvec
    common = np.intersect1d(h, t)
    pairs = 0; witness = None
    for val in common:
        I = np.where(h == val)[0]; J = np.where(t == val)[0]
        for i in I:
            for j in J:
                if np.array_equal(V[i] + V[j], -18*np.ones(len(reps), dtype=np.int64)):
                    pairs += 1
                    if witness is None:
                        witness = (valid[i].tolist(), valid[j].tolist())
    return {"img_order": len(img), "orbits": k, "reps": len(reps),
            "candidates": int(len(valid)),
            "status": "EMPTY_EXHAUSTIVE" if pairs == 0 else "NONEMPTY",
            "surviving_pairs": pairs, "example": witness}

if __name__ == "__main__":
    RESISTANT = [
        [1, 10, 26, 100, 260, 269],
        [1, 121, 137, 158, 260, 322],
        [1, 73, 85, 211, 232, 286],
        [1, 47, 211, 232, 248, 260],
        [1, 10, 64, 73, 100, 307],
        [1, 73, 121, 175, 196, 322],
    ]
    which = int(sys.argv[1]) if len(sys.argv) > 1 else None
    todo = [RESISTANT[which]] if which is not None else RESISTANT
    for K in todo:
        t0 = time.time()
        r = decide_z37_layer(K)
        r["K"] = K; r["elapsed_s"] = round(time.time()-t0, 1)
        print(json.dumps(r), flush=True)
        with open("lp333_order6_z37_layer.jsonl", "a") as fjson:
            fjson.write(json.dumps(r) + "\n")
