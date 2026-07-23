"""Negaperiodic Golay pairs of length 334 (=> Hadamard 668 via Ito) under
multiplier invariance in Z_668^*.

Model: anti-periodic +-1 function ahat on Z_668 (ahat(x+334) = -ahat(x)).
Odd units u preserve anti-periodicity (334u = 334 mod 668) and permute the
odd spectral lines, so K-invariant fibers are well defined for K <= Z_668^*.
Orbits of K pair under sigma: x -> x+334; if sigma fixes an orbit the fiber
is empty (ahat = -ahat). Otherwise one bool per orbit-pair with fixed signs.
NGP condition: D_a(d) + D_b(d) = 668 disagreements (full Z_668 circle) for
every d = 1..333.
"""
import argparse, json, math, time
from collections import Counter
from pathlib import Path
from ortools.sat.python import cp_model

def subgroups(M):
    units = [x for x in range(1, M) if math.gcd(x, M) == 1]
    def closure(gens):
        s = {1}; fr = {1}
        while fr:
            nx = set()
            for a in fr:
                for g in gens:
                    v = a*g % M
                    if v not in s: s.add(v); nx.add(v)
            fr = nx
        return frozenset(s)
    subs = set()
    for a in units:
        subs.add(closure((a,)))
        for b in units:
            if b > a: subs.add(closure((a, b)))
    return sorted(subs, key=len, reverse=True)

def fiber_structure(M, K):
    """Return (pairs, sign, owner) or None if some orbit is sigma-fixed."""
    half = M // 2
    seen = [False]*M; orbs = []
    for i in range(M):
        if seen[i]: continue
        o = sorted({i*g % M for g in K})
        for x in o: seen[x] = True
        orbs.append(o)
    omap = {}
    for j, o in enumerate(orbs):
        for x in o: omap[x] = j
    paired = [None]*len(orbs)
    for j, o in enumerate(orbs):
        k = omap[(o[0] + half) % M]
        if k == j: return None          # sigma-fixed orbit -> empty fiber
        paired[j] = k
    # choose representative orbit of each pair
    pair_id = {}; sign = {}; nxt = 0
    for j, o in enumerate(orbs):
        k = paired[j]
        rep = min(j, k)
        if rep not in pair_id and rep == j:
            pair_id[j] = nxt; nxt += 1
    owner = [0]*M; sgn = [0]*M
    for j, o in enumerate(orbs):
        rep = min(j, paired[j])
        pid = pair_id[rep]
        s = 0 if rep == j else 1
        for x in o:
            owner[x] = pid; sgn[x] = s
    return nxt, sgn, owner

def solve(M, K, seconds, workers):
    st_ = fiber_structure(M, K)
    if st_ is None:
        return {"status": "EMPTY_SIGMA_FIXED"}
    npair, sgn, own = st_
    m = cp_model.CpModel()
    half = M//2
    x = [[m.NewBoolVar(f"x{s}_{j}") for j in range(npair)] for s in range(2)]
    y = {}
    for d in range(1, half):
        terms = []; const = 0
        for s in range(2):
            cnt = Counter()
            for i in range(M):
                j = (i + d) % M
                a, b = own[i], own[j]
                flip = sgn[i] ^ sgn[j]
                if a == b:
                    const += flip     # fixed (dis)agreement
                    continue
                cnt[(min(a, b), max(a, b), flip, s)] += 1
            for (a, b, flip, ss), coef in cnt.items():
                key = (ss, a, b)
                if key not in y:
                    z = m.NewBoolVar(f"y{ss}_{a}_{b}")
                    m.AddBoolXOr([x[ss][a], x[ss][b], z.Not()])
                    y[key] = z
                # disagreement = z XOR flip
                if flip == 0:
                    terms.append(coef * y[key])
                else:
                    terms.append(coef * (1 - y[key]))
        m.Add(sum(terms) + const == M)
    slv = cp_model.CpSolver()
    slv.parameters.max_time_in_seconds = seconds
    slv.parameters.num_search_workers = workers
    t0 = time.time(); st = slv.Solve(m)
    res = {"status": slv.StatusName(st), "bits": 2*npair,
           "elapsed_s": round(time.time()-t0, 2), "conflicts": slv.NumConflicts()}
    if st in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        seqs = []
        for s in range(2):
            ah = [(1 if slv.Value(x[s][own[i]]) else -1) * (-1 if sgn[i] else 1)
                  for i in range(M)]
            seqs.append(ah[:half])
        # independent NAF verification
        def naf(a, d):
            n = len(a); t = 0
            for i in range(n):
                j = i + d
                t += a[i] * (a[j % n] * (-1 if (j//n) % 2 else 1))
            return t
        bad = [d for d in range(1, half) if naf(seqs[0], d) + naf(seqs[1], d) != 0]
        res["verified_naf"] = not bad
        res["sequences"] = seqs
    return res

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--M", type=int, default=668)
    ap.add_argument("--seconds", type=float, default=600)
    ap.add_argument("--workers", type=int, default=8)
    ap.add_argument("--max-bits", type=int, default=200)
    ap.add_argument("--out", default="ngp334_multiplier_sweep.jsonl")
    a = ap.parse_args()
    out = Path(a.out)
    for K in subgroups(a.M):
        if len(K) == 1: continue
        stc = fiber_structure(a.M, K)
        bits = 2*stc[0] if stc else 0
        if stc and bits > a.max_bits: continue
        r = solve(a.M, K, a.seconds, a.workers)
        rec = {"subgroup_order": len(K), "members_sample": sorted(K)[:8], **{k: v for k, v in r.items() if k != "sequences"}}
        if "sequences" in r: rec["sequences"] = r["sequences"]
        print(json.dumps({k: v for k, v in rec.items() if k != "sequences"}), flush=True)
        with out.open("a") as f: f.write(json.dumps(rec) + "\n")
        if r.get("verified_naf"):
            Path("ngp334_WITNESS.json").write_text(json.dumps(rec))
            print("WITNESS FOUND", flush=True)
            return

if __name__ == "__main__":
    main()
