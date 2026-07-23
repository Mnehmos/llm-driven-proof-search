"""GPU lift of the shared middle-layer classes into the 8 remaining group-333
fibers (M unipotent, u in {11,27}).

The eigen-quotient G -> G/W = Z_3 x Z_37 = Z_111 carries the (M,u)-invariant
pair to a <(1,u)>-invariant quaternary pair on Z_111 -- exactly the layer
whose 1,944 survivors (162 canonical classes) are stored in
middle_layer_survivors_order6.npz. For each class rep, each Z_111 orbit's
value pins the sum of its 3 W-lift G-orbit values; |c|=3 pins all three,
|c|=1 leaves 3 configurations (or, when the W-lifts coincide in one G-orbit,
|c|=1 is impossible and the class dies immediately). Scalar-hash pair-table
GPU exhaustion identical to gpu_lift_order6_exhaust.
"""
import argparse, json, time
import numpy as np
import torch

ELEMS = [(i, j, k) for i in range(3) for j in range(3) for k in range(37)]
IDX = {g: n for n, g in enumerate(ELEMS)}
NG = 333

def eig_w_v(M):
    for w in [(0, 1), (1, 0), (1, 1), (1, 2)]:
        Mw = ((M[0]*w[0]+M[1]*w[1]) % 3, (M[2]*w[0]+M[3]*w[1]) % 3)
        if Mw == w:
            for v in [(0, 1), (1, 0), (1, 1), (1, 2)]:
                if (w[0]*v[1]-w[1]*v[0]) % 3 != 0:
                    return w, v
    raise ValueError

def build(M, u):
    unvis = set(range(NG)); orbs = []
    while unvis:
        s0 = min(unvis); o = []
        g = ELEMS[s0]
        while True:
            n = IDX[g]
            if n not in unvis: break
            o.append(n); unvis.discard(n)
            g = ((M[0]*g[0]+M[1]*g[1]) % 3, (M[2]*g[0]+M[3]*g[1]) % 3, (u*g[2]) % 37)
        orbs.append(o)
    own = [0]*NG
    for j, o in enumerate(orbs):
        for i in o: own[i] = j
    # shift orbit reps under phi (acting on shift by the same map)
    sseen = set(); reps = []
    for dn in range(1, NG):
        if dn in sseen: continue
        o = set(); g = ELEMS[dn]
        while True:
            n = IDX[g]
            if n in o: break
            o.add(n)
            g = ((M[0]*g[0]+M[1]*g[1]) % 3, (M[2]*g[0]+M[3]*g[1]) % 3, (u*g[2]) % 37)
        sseen |= o; reps.append(dn)
    C = np.zeros((len(reps), len(orbs), len(orbs)), dtype=np.int64)
    for ri, dn in enumerate(reps):
        d = ELEMS[dn]
        for i in range(NG):
            g = ELEMS[i]
            jn = IDX[((g[0]+d[0]) % 3, (g[1]+d[1]) % 3, (g[2]+d[2]) % 37)]
            C[ri, own[i], own[jn]] += 1
    return orbs, own, reps, C

def lift_map(M, own, orb_reps111):
    """Z_111 orbit rep y -> (beta,k) -> its 3 W-lift G-orbit ids"""
    w, v = eig_w_v(M)
    out = []
    for y in orb_reps111:
        beta, k = y % 3, y % 37
        lifts = []
        for alpha in range(3):
            i = (alpha*w[0] + beta*v[0]) % 3
            j = (alpha*w[1] + beta*v[1]) % 3
            lifts.append(own[IDX[(i, j, k)]])
        out.append(lifts)
    return out

def side_tables(profile, lmap, C, rvec):
    k = C.shape[1]
    p0 = np.zeros(k, dtype=np.int64)
    free = []; dead = False
    for oi, lifts in enumerate(lmap):
        c = int(profile[oi])
        distinct = len(set(lifts))
        if distinct == 1:
            # all three lifts in one orbit: value 3v = c
            if abs(c) != 3: return None, None, None, None, None, True
            p0[lifts[0]] = 1 if c > 0 else -1
        elif distinct == 3:
            if abs(c) == 3:
                for j in lifts: p0[j] = 1 if c > 0 else -1
            else:
                maj = 1 if c > 0 else -1
                p0[lifts[0]] = -maj; p0[lifts[1]] = maj; p0[lifts[2]] = maj
                free.append((oi, lifts, c))
        else:
            # two orbits (sizes 1+2 among lifts): value = v1 + 2v2 in {-3,-1,1,3}
            a_, b_ = lifts[0], None
            from collections import Counter as Ct
            cnt = Ct(lifts)
            single = [x for x, n in cnt.items() if n == 1][0]
            double = [x for x, n in cnt.items() if n == 2][0]
            # c = v_single + 2*v_double: solutions: (1,1)=3,(1,-1)=-1,(-1,1)=1,(-1,-1)=-3
            if c == 3: p0[single] = 1; p0[double] = 1
            elif c == -3: p0[single] = -1; p0[double] = -1
            elif c == 1: p0[single] = -1; p0[double] = 1
            elif c == -1: p0[single] = 1; p0[double] = -1
            # unique solution each -> pinned, no freedom
    R = C.shape[0]
    def paf(p): return np.einsum("ruv,u,v->r", C, p, p)
    V0 = paf(p0)
    t = len(free)
    flips = []
    for i, (oi, lifts, c) in enumerate(free):
        fl = {0: []}
        for d in (1, 2):
            fl[d] = [lifts[0], lifts[d]]
        flips.append(fl)
    S = np.zeros((t, 3, R), dtype=np.int64)
    def delta(F):
        p = p0.copy()
        for f in F: p[f] = -p[f]
        return paf(p) - V0
    for i in range(t):
        for d in (1, 2):
            S[i, d] = delta(flips[i][d])
    Pt = np.zeros((t, t, 9, R), dtype=np.int64)
    for i in range(t):
        for j in range(i+1, t):
            for di in (1, 2):
                for dj in (1, 2):
                    F = flips[i][di] + flips[j][dj]
                    Pt[i, j, 3*di+dj] = delta(F) - S[i, di] - S[j, dj]
    return p0, V0, S @ rvec, Pt @ rvec, flips, False

def enumerate_hashes(t, S_h, P_h, base_h, device, chunk=1 << 21):
    total = 3**t
    Sh = torch.tensor(S_h, device=device)
    Ph = torch.tensor(P_h, device=device)
    pairs = [(i, j) for i in range(t) for j in range(i+1, t)]
    pows = torch.tensor([3**i for i in range(t)], device=device, dtype=torch.long)
    for start in range(0, total, chunk):
        n = min(chunk, total - start)
        ints = torch.arange(start, start+n, device=device, dtype=torch.long)
        D = (ints[:, None] // pows[None, :]) % 3
        h = torch.full((n,), int(base_h), device=device, dtype=torch.long)
        for i in range(t):
            h += Sh[i][D[:, i]]
        for (i, j) in pairs:
            h += Ph[i, j][3*D[:, i] + D[:, j]]
        yield start, h

def candidate_p(idx, flips, p0):
    p = p0.copy()
    rem = idx
    for i in range(len(flips)):
        d = rem % 3; rem //= 3
        if d:
            for f in flips[i][d]: p[f] = -p[f]
    return p

def decide_class(ca, cb, lmap, C, rvec, device="cuda"):
    R = C.shape[0]
    ra = side_tables(ca, lmap, C, rvec)
    if ra[5]: return {"status": "DEAD_LIFT_A"}
    rb = side_tables(cb, lmap, C, rvec)
    if rb[5]: return {"status": "DEAD_LIFT_B"}
    p0a, V0a, Sha, Pha, fla, _ = ra
    p0b, V0b, Shb, Phb, flb, _ = rb
    ta, tb = len(fla), len(flb)
    h0a = int(V0a @ rvec); h0b = int(V0b @ rvec)
    target = int((-2*np.ones(R, dtype=np.int64)) @ rvec)
    parts = []
    for start, h in enumerate_hashes(ta, Sha, Pha, h0a, device):
        parts.append(h)
    ha = torch.cat(parts)
    sa, idxa = torch.sort(ha)
    hits = []
    for startb, hb in enumerate_hashes(tb, Shb, Phb, h0b, device):
        need = target - hb
        pos = torch.clamp(torch.searchsorted(sa, need), max=len(sa)-1)
        eq = sa[pos] == need
        if eq.any():
            for b_ in torch.nonzero(eq).flatten().tolist():
                v = need[b_]
                lo = torch.searchsorted(sa, v).item()
                hi = torch.searchsorted(sa, v, right=True).item()
                for q in range(lo, hi):
                    hits.append((int(idxa[q].item()), startb + b_))
    def paf(p): return np.einsum("ruv,u,v->r", C, p, p)
    for ia_, ib_ in hits:
        pa_ = candidate_p(ia_, fla, p0a)
        pb_ = candidate_p(ib_, flb, p0b)
        if np.array_equal(paf(pa_) + paf(pb_), -2*np.ones(R, dtype=np.int64)):
            return {"status": "SAT", "pa": pa_.tolist(), "pb": pb_.tolist()}
    return {"status": "UNSAT_EXHAUSTIVE", "a_configs": 3**ta, "b_configs": 3**tb,
            "hits": len(hits)}

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--M", type=int, nargs=4, required=True)
    ap.add_argument("--u", type=int, required=True)
    ap.add_argument("--range", type=int, nargs=2, default=[0, 162])
    ap.add_argument("--out", required=True)
    a = ap.parse_args()
    dat = np.load("middle_layer_survivors_order6.npz")
    PA, PB, orb_reps = dat["PA"], dat["PB"], [int(x) for x in dat["orb_reps"]]
    reps_cls = [int(x) for x in np.load("middle_layer_class_reps.npy")]
    M, u = list(a.M), a.u
    orbs, own, sreps, C = build(M, u)
    lmap = lift_map(M, own, orb_reps)
    rng = np.random.default_rng(0xBEEF)
    rvec = rng.integers(1, 1 << 62, size=C.shape[0], dtype=np.int64)
    from pathlib import Path
    outp = Path(a.out); done = set()
    if outp.exists():
        for line in outp.read_text().splitlines():
            try:
                r = json.loads(line)
                if r.get("M") == M and r.get("u") == u:
                    done.add(r["class_rep"])
            except Exception: pass
    for ci in reps_cls[a.range[0]:a.range[1]]:
        if ci in done: continue
        t0 = time.time()
        r = decide_class(PA[ci], PB[ci], lmap, C, rvec)
        rec = {"M": M, "u": u, "class_rep": int(ci),
               "elapsed_s": round(time.time()-t0, 1), **r}
        print(json.dumps(rec), flush=True)
        with outp.open("a") as f: f.write(json.dumps(rec) + "\n")
        if r["status"] == "SAT":
            Path("group333_eigen_WITNESS.json").write_text(json.dumps(rec))
            print("WITNESS CANDIDATE FOUND", flush=True)
            return

if __name__ == "__main__":
    main()
