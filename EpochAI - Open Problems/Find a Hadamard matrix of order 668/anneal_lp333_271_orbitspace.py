"""Stochastic SAT-side search over the surviving <271> sub-fibers.

Works directly in orbit space: p in {+-1}^45 per sequence (9 fixed-point
values pinned by the sub-fiber pattern, 36 free nine-orbit values with sum
constraint). Energy = sum over the 44 shift-orbit representatives, weighted
by shift-orbit size, of (PAF_a(d)+PAF_b(d)+2)^2 computed via precomputed
bilinear coefficient tables. Exact zero -> full-sequence integer PAF verify.
Complements the exact engines: finds witnesses fast if any sub-fiber is SAT.
"""
import json, time
import numpy as np
from pathlib import Path

import importlib.util
spec = importlib.util.spec_from_file_location("sp", "search_lp333_271_split.py")
sp = importlib.util.module_from_spec(spec)
spec.loader.exec_module(sp)

N = 333
K, orbs, own = sp.K, sp.orbs, sp.own
fixed, nines, fix_by_m = sp.fixed, sp.nines, sp.fix_by_m
NO = len(orbs)

# shift-orbit reps and weights
shift_seen = set(); reps = []; wts = []
for d in range(1, N):
    if d in shift_seen: continue
    so = {d*g % N for g in K}
    shift_seen |= so; reps.append(d); wts.append(len(so))
wts = np.array(wts, dtype=np.int64)

# per-rep coefficient matrices C[r][u,v] (symmetric, diagonal = same-orbit count)
C = np.zeros((len(reps), NO, NO), dtype=np.int64)
diagc = np.zeros((len(reps),), dtype=np.int64)
for ri, d in enumerate(reps):
    for i in range(N):
        u, v = own[i], own[(i+d) % N]
        C[ri, u, v] += 1
# PAF_a(d) = sum_{u,v} C[u,v] p_u p_v (careful: counts ordered pairs (i,i+d))

def paf_all(p):
    # p: (45,) +-1 ; returns (44,) PAF values
    return np.einsum("ruv,u,v->r", C, p, p)

def energy(pa_vec, pb_vec):
    r = paf_all(pa_vec) + paf_all(pb_vec) + 2
    return int(np.sum(wts * r * r))

def verify_full(pa_vec, pb_vec):
    seq = [[int(pa_vec[own[i]]) for i in range(N)], [int(pb_vec[own[i]]) for i in range(N)]]
    for d in range(1, N):
        if sum(seq[s][i]*seq[s][(i+d) % N] for s in range(2) for i in range(N)) != -2:
            return False, None
    return True, seq

def survivors():
    decided = set()
    for f in ("lp333_271_split_retry.jsonl", "lp333_271_z3.jsonl"):
        p = Path(f)
        if p.exists():
            for line in p.read_text().splitlines():
                try:
                    r = json.loads(line)
                    if r.get("status", "UNKNOWN") not in ("UNKNOWN",):
                        decided.add((tuple(r["pa"]), tuple(r["pb"])))
                except Exception: pass
    out = []
    for line in Path("lp333_271_split.jsonl").read_text().splitlines():
        try: r = json.loads(line)
        except Exception: continue
        if r.get("status") == "UNKNOWN" and (tuple(r["pa"]), tuple(r["pb"])) not in decided:
            out.append((r["i"], r["pa"], r["pb"]))
    return out

def run(seconds_total=7200, seed=1):
    rng = np.random.default_rng(seed)
    subs = survivors()
    print(json.dumps({"event": "start", "survivors": len(subs)}), flush=True)
    nine_idx = np.array(nines)
    best_global = None
    t_end = time.time() + seconds_total
    round_no = 0
    while time.time() < t_end:
        round_no += 1
        for i, pa, pb in subs:
            if time.time() > t_end: break
            vecs = []
            for pat in (pa, pb):
                p = np.zeros(NO, dtype=np.int64)
                for mm in range(9):
                    p[fix_by_m[mm]] = 1 if mm in pat else -1
                ones = rng.choice(36, size=18, replace=False)
                vals = -np.ones(36, dtype=np.int64); vals[ones] = 1
                p[nine_idx] = vals
                vecs.append(p)
            pa_v, pb_v = vecs
            e = energy(pa_v, pb_v)
            # pairwise-swap tabu descent preserving sums
            for it in range(4000):
                if e == 0: break
                s = it & 1
                p = pa_v if s == 0 else pb_v
                pos = nine_idx[p[nine_idx] == 1]; neg = nine_idx[p[nine_idx] == -1]
                u = rng.choice(pos); v = rng.choice(neg)
                p[u], p[v] = -1, 1
                e2 = energy(pa_v, pb_v)
                if e2 <= e or rng.random() < np.exp((e - e2) / max(8.0, e/40)):
                    e = e2
                else:
                    p[u], p[v] = 1, -1
            if best_global is None or e < best_global[0]:
                best_global = (e, i, pa, pb)
                print(json.dumps({"event": "best", "energy": e, "i": i}), flush=True)
            if e == 0:
                ok, seq = verify_full(pa_v, pb_v)
                rec = {"i": i, "pa": pa, "pb": pb, "verified_paf": ok, "sequences": seq}
                Path("lp333_271_WITNESS.json").write_text(json.dumps(rec))
                print(json.dumps({"event": "WITNESS", "i": i, "verified": ok}), flush=True)
                return
        print(json.dumps({"event": "round", "n": round_no,
                          "best": best_global[0] if best_global else None}), flush=True)

if __name__ == "__main__":
    import sys
    run(seconds_total=float(sys.argv[1]) if len(sys.argv) > 1 else 7200,
        seed=int(sys.argv[2]) if len(sys.argv) > 2 else 1)
