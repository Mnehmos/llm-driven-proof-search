"""Exhaustive meet-in-the-middle decision of small group-333 LP fibers.

For a fiber given by automorphism phi=(M,u) of G = Z_3 x Z_3 x Z_37 with k
orbits (k <= ~27), enumerate ALL p in {+-1}^k with weighted sum(a) = +1
(negation symmetry makes +1 WLOG for both sequences), compute the exact PAF
vector over the deduplicated shift-orbit representatives, and hash-join
pairs with V_a + V_b = -2 componentwise. UNSAT cannot be returned as
UNKNOWN: the pass is a complete decision.

Positive control: --self-test runs the same machinery on LP(9) over Z_3xZ_3
(trivial partition, 9 orbits) where witnesses are known to exist.
"""
import argparse, json, time
import numpy as np

# ---- group G = Z_3 x Z_3 x Z_37 (as in the sweep script) ----
ELEMS = [(i, j, k) for i in range(3) for j in range(3) for k in range(37)]
IDX = {g: n for n, g in enumerate(ELEMS)}
NG = 333

def g_add(g, h): return ((g[0]+h[0]) % 3, (g[1]+h[1]) % 3, (g[2]+h[2]) % 37)
def apply_aut(M, u, g):
    a, b, c, d = M
    return ((a*g[0]+b*g[1]) % 3, (c*g[0]+d*g[1]) % 3, (u*g[2]) % 37)

def fiber_structure(M, u):
    unvis = set(range(NG)); orbs = []
    while unvis:
        s0 = min(unvis); o = []
        g = ELEMS[s0]
        while True:
            n = IDX[g]
            if n not in unvis: break
            o.append(n); unvis.discard(n)
            g = apply_aut(M, u, g)
        orbs.append(sorted(o))
    own = [0]*NG
    for j, o in enumerate(orbs):
        for i in o: own[i] = j
    return orbs, own

def shift_reps_and_C(orbs, own, M, u):
    """dedup shifts under phi; C[r][a,b] ordered-pair crossing counts"""
    k = len(orbs)
    seen = set(); reps = []
    for dn in range(1, NG):
        if dn in seen: continue
        # orbit of shift dn under phi
        o = set(); g = ELEMS[dn]
        while True:
            n = IDX[g]
            if n in o: break
            o.add(n); g = apply_aut(M, u, g)
        seen |= o; reps.append(dn)
    C = np.zeros((len(reps), k, k), dtype=np.int64)
    for ri, dn in enumerate(reps):
        d = ELEMS[dn]
        for i in range(NG):
            jn = IDX[g_add(ELEMS[i], d)]
            C[ri, own[i], own[jn]] += 1
    return reps, C

def enumerate_valid(sizes, target=1, chunk=1 << 20):
    """yield batches of +-1 matrices (m x k) with weighted sum == target"""
    k = len(sizes)
    w = np.array(sizes, dtype=np.int64)
    total = 1 << k
    for start in range(0, total, chunk):
        n = min(chunk, total - start)
        ints = np.arange(start, start + n, dtype=np.uint64)
        bits = ((ints[:, None] >> np.arange(k, dtype=np.uint64)) & 1).astype(np.int8)
        P = (2*bits - 1).astype(np.int8)
        sums = P.astype(np.int64) @ w
        yield P[sums == target]

def paf_batch(P, C):
    """P: (m,k) int8; C: (R,k,k) -> (m,R) int32 PAF values"""
    m, k = P.shape
    Pf = P.astype(np.float32)
    out = np.empty((m, C.shape[0]), dtype=np.int32)
    for r in range(C.shape[0]):
        p_c = Pf @ C[r].astype(np.float32)          # (m,k)
        out[:, r] = np.round((p_c * Pf).sum(1)).astype(np.int32)
    return out

def decide(M, u, verbose=True):
    orbs, own = fiber_structure(M, u)
    sizes = [len(o) for o in orbs]
    k = len(orbs)
    reps, C = shift_reps_and_C(orbs, own, M, u)
    if verbose:
        print(json.dumps({"event": "fiber", "M": M, "u": u, "orbits": k,
                          "reps": len(reps)}), flush=True)
    # pass 1: index all valid a-side PAF vectors
    table = {}
    count = 0
    for P in enumerate_valid(sizes):
        if len(P) == 0: continue
        V = paf_batch(P, C)
        for i in range(len(P)):
            key = V[i].tobytes()
            if key not in table:
                table[key] = P[i].copy()
        count += len(P)
    if verbose:
        print(json.dumps({"event": "indexed", "valid": count,
                          "distinct_paf": len(table)}), flush=True)
    # pass 2: look for complement -2 - V
    for P in enumerate_valid(sizes):
        if len(P) == 0: continue
        V = paf_batch(P, C)
        W = (-2 - V).astype(np.int32)
        for i in range(len(P)):
            hit = table.get(W[i].tobytes())
            if hit is not None:
                pa, pb = hit, P[i]
                a = [int(pa[own[t]]) for t in range(NG)]
                b = [int(pb[own[t]]) for t in range(NG)]
                bad = []
                for dn in range(1, NG):
                    d = ELEMS[dn]
                    v = sum(a[t]*a[IDX[g_add(ELEMS[t], d)]] +
                            b[t]*b[IDX[g_add(ELEMS[t], d)]] for t in range(NG))
                    if v != -2: bad.append(dn)
                return {"status": "SAT", "verified_paf": not bad,
                        "sequences": [a, b]}
    return {"status": "UNSAT_EXHAUSTIVE", "a_candidates": count}

def self_test():
    """LP(9) over Z_3 x Z_3 with trivial partition — witness known to exist."""
    import itertools
    G9 = [(i, j) for i in range(3) for j in range(3)]
    I9 = {g: t for t, g in enumerate(G9)}
    def add9(g, h): return ((g[0]+h[0]) % 3, (g[1]+h[1]) % 3)
    C = np.zeros((8, 9, 9), dtype=np.int64)
    for ri, d in enumerate([g for g in G9 if g != (0, 0)]):
        for i, g in enumerate(G9):
            C[ri, i, I9[add9(g, d)]] += 1
    table = {}
    found = None
    for bits in itertools.product([1, -1], repeat=9):
        if sum(bits) != 1: continue
        p = np.array(bits, dtype=np.int8)
        V = paf_batch(p[None, :], C)[0]
        table.setdefault(V.tobytes(), p.copy())
    for key, pa in table.items():
        Va = np.frombuffer(key, dtype=np.int32)
        W = (-2 - Va).astype(np.int32)
        hit = table.get(W.tobytes())
        if hit is not None:
            found = (hit, pa); break
    print("self-test LP(9)/Z3xZ3 witness found:", found is not None)
    return found is not None

if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--M", type=int, nargs=4)
    ap.add_argument("--u", type=int)
    ap.add_argument("--self-test", action="store_true")
    ap.add_argument("--out", default="lp333_group333_exhaustive.jsonl")
    args = ap.parse_args()
    if args.self_test:
        import sys
        sys.exit(0 if self_test() else 1)
    t0 = time.time()
    r = decide(list(args.M), args.u)
    rec = {"M": list(args.M), "u": args.u,
           "elapsed_s": round(time.time()-t0, 1),
           **{kk: vv for kk, vv in r.items() if kk != "sequences"}}
    if "sequences" in r: rec["sequences"] = r["sequences"]
    print(json.dumps({kk: vv for kk, vv in rec.items() if kk != "sequences"}), flush=True)
    from pathlib import Path
    with Path(args.out).open("a") as f:
        f.write(json.dumps(rec) + "\n")
    if r.get("verified_paf"):
        Path("lp333_group333_WITNESS.json").write_text(json.dumps(rec))
        print("WITNESS FOUND", flush=True)
