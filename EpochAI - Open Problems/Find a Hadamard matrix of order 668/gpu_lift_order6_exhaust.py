"""Complete GPU exhaustion of order-6 fiber lifts, one middle-layer class at
a time.

For a profile (ca, cb): each of the 21 lift-triples with |c|=3 pins its three
binary orbit values; each with |c|=1 has exactly 3 configurations (which slot
holds the minority sign). A candidate is a base-3 digit vector over the free
triples. The PAF vector V is quadratic, so V(candidate) = V0 + sum_i S_i[d_i]
+ sum_{i<j} P_ij[d_i,d_j]; for the join only the scalar hash h = V.rvec is
needed, with the same table decomposition pre-dotted by rvec. Exact
verification re-computes full integer V for every hash collision, so a false
positive is impossible and a false negative cannot occur (wrap-consistent
int64 hashing). Per class: enumerate both sides, sort-join hashes, verify.
Planted-pair self-test included (--self-test i).
"""
import argparse, json, time
import numpy as np
import torch

N3, N1 = 333, 111

def build(K):
    seen = [False]*N3; orbs = []
    for i in range(N3):
        if seen[i]: continue
        o = sorted({i*g % N3 for g in K})
        for t in o: seen[t] = True
        orbs.append(o)
    own = [0]*N3
    for j, o in enumerate(orbs):
        for i in o: own[i] = j
    sseen = set(); reps = []
    for d in range(1, N3):
        if d in sseen: continue
        sseen.update({d*g % N3 for g in K}); reps.append(d)
    C = np.zeros((len(reps), len(orbs), len(orbs)), dtype=np.int64)
    for ri, d in enumerate(reps):
        for i in range(N3):
            C[ri, own[i], own[(i+d) % N3]] += 1
    return orbs, own, reps, C

def side_tables(profile, lmap, C, rvec):
    """returns (free_triples, base_p, h0, S_h, P_h, V0) for one side"""
    k = C.shape[1]
    p0 = np.zeros(k, dtype=np.int64)
    free = []
    for oi, lifts in enumerate(lmap):
        c = int(profile[oi])
        if abs(c) == 3:
            for j in lifts: p0[j] = 1 if c > 0 else -1
        else:
            free.append((oi, lifts, c))
            # config 0: minority at slot 0
            maj = 1 if c > 0 else -1
            p0[lifts[0]] = -maj
            p0[lifts[1]] = maj
            p0[lifts[2]] = maj
    R = C.shape[0]
    def paf(p):
        return np.einsum("ruv,u,v->r", C, p, p)
    V0 = paf(p0)
    t = len(free)
    # config d for triple i: minority at slot d. Represent as flip set vs config 0.
    S = np.zeros((t, 3, R), dtype=np.int64)
    flips = []  # per triple per config: list of coordinates flipped vs p0
    for i, (oi, lifts, c) in enumerate(free):
        fl = {0: []}
        for d in (1, 2):
            fl[d] = [lifts[0], lifts[d]]
        flips.append(fl)
    # delta for flipping a set F from base p0 (exact): V(p') - V(p0)
    def delta(F):
        p = p0.copy()
        for f in F: p[f] = -p[f]
        return paf(p) - V0
    for i in range(t):
        for d in (1, 2):
            S[i, d] = delta(flips[i][d])
    # pair corrections: delta(F_i u F_j) - delta(F_i) - delta(F_j)
    P = np.zeros((t, t, 9, R), dtype=np.int64)
    for i in range(t):
        for j in range(i+1, t):
            for di in (0, 1, 2):
                for dj in (0, 1, 2):
                    if di == 0 or dj == 0: continue
                    F = flips[i][di] + flips[j][dj]
                    P[i, j, 3*di+dj] = delta(F) - S[i, di] - S[j, dj]
    S_h = S @ rvec
    P_h = P @ rvec
    return free, p0, V0, S, P, S_h, P_h, flips

def enumerate_hashes(t, S_h, P_h, base_h, device, chunk=1 << 21):
    """stream candidate scalar hashes as torch tensors on GPU"""
    total = 3**t
    Sh = torch.tensor(S_h, device=device)            # (t,3)
    pairs = [(i, j) for i in range(t) for j in range(i+1, t)]
    Ph = torch.tensor(P_h, device=device)            # (t,t,9)
    pows = torch.tensor([3**i for i in range(t)], device=device, dtype=torch.long)
    for start in range(0, total, chunk):
        n = min(chunk, total - start)
        ints = torch.arange(start, start+n, device=device, dtype=torch.long)
        D = (ints[:, None] // pows[None, :]) % 3     # (n,t)
        h = torch.full((n,), int(base_h), device=device, dtype=torch.long)
        for i in range(t):
            h += Sh[i][D[:, i]]
        for (i, j) in pairs:
            h += Ph[i, j][3*D[:, i] + D[:, j]]
        yield start, h

def candidate_p(idx, free, flips, p0):
    p = p0.copy()
    rem = idx
    for i in range(len(free)):
        d = rem % 3; rem //= 3
        if d:
            for f in flips[i][d]: p[f] = -p[f]
    return p

def decide_class(K, ca, cb, lmap, orbs, own, reps, C, device="cuda"):
    R = len(reps)
    rng = np.random.default_rng(0xBEEF)
    rvec = rng.integers(1, 1 << 62, size=R, dtype=np.int64)
    fa, p0a, V0a, Sa, Pa, Sha, Pha, fla = side_tables(ca, lmap, C, rvec)
    fb, p0b, V0b, Sb, Pb, Shb, Phb, flb = side_tables(cb, lmap, C, rvec)
    ta, tb = len(fa), len(fb)
    h0a = int(V0a @ rvec); h0b = int(V0b @ rvec)
    target = int((-2*np.ones(R, dtype=np.int64)) @ rvec)
    # enumerate a-side hashes, sort on GPU
    parts = []
    for start, h in enumerate_hashes(ta, Sha, Pha, h0a, device):
        parts.append(h)
    ha = torch.cat(parts); del parts
    sa, idxa = torch.sort(ha)
    hits = []
    for startb, hb in enumerate_hashes(tb, Shb, Phb, h0b, device):
        need = target - hb
        pos = torch.searchsorted(sa, need)
        pos = torch.clamp(pos, max=len(sa)-1)
        eq = sa[pos] == need
        if eq.any():
            bi = torch.nonzero(eq).flatten()
            for b_ in bi.tolist():
                jb = startb + b_
                # all matching a-side positions
                v = need[b_]
                lo = torch.searchsorted(sa, v).item()
                hi = torch.searchsorted(sa, v, right=True).item()
                for q in range(lo, hi):
                    hits.append((int(idxa[q].item()), int(jb)))
    # exact verification of hits
    def paf(p): return np.einsum("ruv,u,v->r", C, p, p)
    for ia_, ib_ in hits:
        pa_ = candidate_p(ia_, fa, fla, p0a)
        pb_ = candidate_p(ib_, fb, flb, p0b)
        if np.array_equal(paf(pa_) + paf(pb_), -2*np.ones(R, dtype=np.int64)):
            a = [int(pa_[own[i]]) for i in range(N3)]
            b = [int(pb_[own[i]]) for i in range(N3)]
            bad = [d for d in range(1, N3)
                   if sum(a[i]*a[(i+d) % N3] + b[i]*b[(i+d) % N3] for i in range(N3)) != -2]
            return {"status": "SAT", "verified_paf": not bad, "sequences": [a, b]}
    return {"status": "UNSAT_EXHAUSTIVE", "a_configs": 3**ta, "b_configs": 3**tb,
            "hash_hits_checked": len(hits)}

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--K", type=int, nargs="+", required=True)
    ap.add_argument("--classes", type=int, nargs="*", help="class rep indices")
    ap.add_argument("--range", type=int, nargs=2, help="range into class rep list")
    ap.add_argument("--out", required=True)
    ap.add_argument("--self-test", action="store_true")
    a = ap.parse_args()
    dat = np.load("middle_layer_survivors_order6.npz")
    PA, PB, orb_reps = dat["PA"], dat["PB"], [int(x) for x in dat["orb_reps"]]
    reps_cls = [int(x) for x in np.load("middle_layer_class_reps.npy")]
    K = a.K
    orbs, own, sreps, C = build(K)
    lmap = [[int(own[(y + 111*j) % N3]) for j in range(3)] for y in orb_reps]
    device = "cuda" if torch.cuda.is_available() else "cpu"
    if a.self_test:
        # planted pair inside class 0's config space with synthetic target
        i0 = reps_cls[0]
        R = len(sreps)
        rng = np.random.default_rng(1)
        rvec = rng.integers(1, 1 << 62, size=R, dtype=np.int64)
        fa, p0a, V0a, Sa, Pa, Sha, Pha, fla = side_tables(PA[i0], lmap, C, rvec)
        # random candidate exact check: table-reconstructed V equals direct V
        def paf(p): return np.einsum("ruv,u,v->r", C, p, p)
        ok = True
        for trial in range(20):
            idx = int(rng.integers(0, 3**len(fa)))
            p = candidate_p(idx, fa, fla, p0a)
            V_direct = paf(p)
            # reconstruct via tables
            rem = idx; V = V0a.copy()
            ds = []
            for i in range(len(fa)):
                ds.append(rem % 3); rem //= 3
            for i, d in enumerate(ds):
                V = V + Sa[i, d]
            for i in range(len(fa)):
                for j in range(i+1, len(fa)):
                    if ds[i] and ds[j]:
                        V = V + Pa[i, j, 3*ds[i]+ds[j]]
            if not np.array_equal(V, V_direct):
                ok = False; break
        print(json.dumps({"self_test_table_decomposition": "PASS" if ok else "FAIL"}))
        return
    if a.classes:
        cls = a.classes
    elif a.range:
        cls = reps_cls[a.range[0]:a.range[1]]
    else:
        cls = reps_cls
    from pathlib import Path
    outp = Path(a.out); done = set()
    if outp.exists():
        for line in outp.read_text().splitlines():
            try: done.add(json.loads(line)["class_rep"])
            except Exception: pass
    for ci in cls:
        if ci in done: continue
        t0 = time.time()
        r = decide_class(K, PA[ci], PB[ci], lmap, orbs, own, sreps, C, device)
        rec = {"class_rep": int(ci), "K": K,
               "elapsed_s": round(time.time()-t0, 1),
               **{k2: v for k2, v in r.items() if k2 != "sequences"}}
        if "sequences" in r: rec["sequences"] = r["sequences"]
        print(json.dumps({k2: v for k2, v in rec.items() if k2 != "sequences"}), flush=True)
        with outp.open("a") as f: f.write(json.dumps(rec) + "\n")
        if r.get("verified_paf"):
            Path("lp333_order6_WITNESS.json").write_text(json.dumps(rec))
            print("WITNESS FOUND", flush=True)
            return

if __name__ == "__main__":
    main()
