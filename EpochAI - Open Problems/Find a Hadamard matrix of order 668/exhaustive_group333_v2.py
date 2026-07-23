"""Sort-merge exhaustive decision of group-333 LP fibers up to ~33 orbits.

Both sequences range over the SAME candidate set (weighted sum +1 WLOG), so
the pair condition V_a + V_b = -2 is a self-join: compute h_i = H(V_i) and
t_i = H(-2 - V_i) with a random-vector hash H, intersect {h} with {t}, and
exact-verify every hash collision. Complete decision; hash collisions can
only cause extra exact checks, never a missed pair, because H is applied to
the exact integer vectors and every candidate pair surfaced by the
intersection is re-verified against the true PAF vectors.
"""
import argparse, json, time
import numpy as np
from pathlib import Path

from exhaustive_group333_fiber import (ELEMS, IDX, NG, g_add, fiber_structure,
                                       shift_reps_and_C, enumerate_valid, paf_batch)

def decide_sorted(M, u, chunk=1 << 21, verbose=True):
    orbs, own = fiber_structure(M, u)
    sizes = [len(o) for o in orbs]
    k = len(orbs)
    reps, C = shift_reps_and_C(orbs, own, M, u)
    R = len(reps)
    if verbose:
        print(json.dumps({"event": "fiber", "M": M, "u": u, "orbits": k,
                          "reps": R}), flush=True)
    rng = np.random.default_rng(0xC0FFEE)
    rvec = rng.integers(1, 1 << 62, size=R, dtype=np.int64)
    hs, ts, Ps = [], [], []
    count = 0
    t0 = time.time()
    for P in enumerate_valid(sizes, chunk=chunk):
        if len(P) == 0: continue
        V = paf_batch(P, C).astype(np.int64)
        hs.append(V @ rvec)
        ts.append((-2 - V) @ rvec)
        Ps.append(P.copy())
        count += len(P)
    h = np.concatenate(hs); t = np.concatenate(ts)
    P_all = np.concatenate(Ps)
    del hs, ts, Ps
    if verbose:
        print(json.dumps({"event": "enumerated", "valid": int(count),
                          "elapsed_s": round(time.time()-t0, 1)}), flush=True)
    common, ia, ib = np.intersect1d(h, t, return_indices=True)
    # intersect1d dedups; gather ALL indices for each common value
    if len(common):
        order_h = np.argsort(h); order_t = np.argsort(t)
        hh = h[order_h]; tt = t[order_t]
        for val in common:
            i0, i1 = np.searchsorted(hh, val), np.searchsorted(hh, val, side="right")
            j0, j1 = np.searchsorted(tt, val), np.searchsorted(tt, val, side="right")
            for i in order_h[i0:i1]:
                Vi = paf_batch(P_all[i][None, :], C)[0].astype(np.int64)
                for j in order_t[j0:j1]:
                    Vj = paf_batch(P_all[j][None, :], C)[0].astype(np.int64)
                    if np.array_equal(Vi + Vj, -2*np.ones(R, dtype=np.int64)):
                        a = [int(P_all[i][own[x]]) for x in range(NG)]
                        b = [int(P_all[j][own[x]]) for x in range(NG)]
                        bad = []
                        for dn in range(1, NG):
                            d = ELEMS[dn]
                            v = sum(a[x]*a[IDX[g_add(ELEMS[x], d)]] +
                                    b[x]*b[IDX[g_add(ELEMS[x], d)]]
                                    for x in range(NG))
                            if v != -2: bad.append(dn)
                        return {"status": "SAT", "verified_paf": not bad,
                                "sequences": [a, b]}
    return {"status": "UNSAT_EXHAUSTIVE", "a_candidates": int(count),
            "hash_collisions": int(len(common))}

if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--fibers-json", help="JSON list of [M(4), u] entries")
    ap.add_argument("--M", type=int, nargs=4)
    ap.add_argument("--u", type=int)
    ap.add_argument("--out", default="lp333_group333_exhaustive.jsonl")
    args = ap.parse_args()
    jobs = []
    if args.fibers_json:
        for e in json.loads(Path(args.fibers_json).read_text()):
            jobs.append((e[0], e[1]))
    else:
        jobs.append((list(args.M), args.u))
    outp = Path(args.out)
    done = set()
    if outp.exists():
        for line in outp.read_text().splitlines():
            try:
                r = json.loads(line); done.add((tuple(r["M"]), r["u"]))
            except Exception: pass
    for M, u in jobs:
        if (tuple(M), u) in done:
            continue
        t0 = time.time()
        r = decide_sorted(M, u)
        rec = {"M": M, "u": u, "elapsed_s": round(time.time()-t0, 1),
               **{kk: vv for kk, vv in r.items() if kk != "sequences"}}
        if "sequences" in r: rec["sequences"] = r["sequences"]
        print(json.dumps({kk: vv for kk, vv in rec.items() if kk != "sequences"}), flush=True)
        with outp.open("a") as f:
            f.write(json.dumps(rec) + "\n")
        if r.get("verified_paf"):
            Path("lp333_group333_WITNESS.json").write_text(json.dumps(rec))
            print("WITNESS FOUND", flush=True)
            break
