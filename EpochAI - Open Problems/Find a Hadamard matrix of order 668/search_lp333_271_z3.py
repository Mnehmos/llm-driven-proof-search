"""Z3 PB-theory wave over the surviving <271> sub-fibers.

No CNF expansion: each of the 44 deduplicated shift equalities becomes a
native PbEq over Xor(x_u, x_v) pseudo-literals with integer weights; the
fixed-point patterns become unit assertions; the nine-orbit sums are PbEq
cardinalities. Any SAT model is re-verified with integer PAF arithmetic.
"""
import argparse, json, time
from collections import Counter
from pathlib import Path

import importlib.util
spec = importlib.util.spec_from_file_location("sp", "search_lp333_271_split.py")
sp = importlib.util.module_from_spec(spec)
spec.loader.exec_module(sp)

import z3

N = 333
K, orbs, own = sp.K, sp.orbs, sp.own
fixed, nines, fix_by_m = sp.fixed, sp.nines, sp.fix_by_m

def survivors(split_file, retry_file, extra_files=()):
    decided = set()
    for f in (retry_file,) + tuple(extra_files):
        p = Path(f)
        if p.exists():
            for line in p.read_text().splitlines():
                try:
                    r = json.loads(line)
                    if r.get("status", "UNKNOWN") != "UNKNOWN" or r.get("sat") is False:
                        decided.add((tuple(r["pa"]), tuple(r["pb"])))
                except Exception: pass
    out = []
    for line in Path(split_file).read_text().splitlines():
        try: r = json.loads(line)
        except Exception: continue
        if r.get("status") == "UNKNOWN" and (tuple(r["pa"]), tuple(r["pb"])) not in decided:
            out.append((r["i"], r["pa"], r["pb"]))
    return out

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seconds", type=float, default=900)
    ap.add_argument("--out", default="lp333_271_z3.jsonl")
    a = ap.parse_args()
    X = [[z3.Bool(f"x{s}_{j}") for j in range(len(orbs))] for s in range(2)]
    base = []
    for s in range(2):
        base.append(z3.PbEq([(X[s][j], 1) for j in nines], 18))
    shift_seen = set()
    for d in range(1, N):
        if d in shift_seen: continue
        shift_seen.update({d*g % N for g in K})
        wl = Counter()
        for s in range(2):
            for i in range(N):
                u, v = own[i], own[(i+d) % N]
                if u == v: continue
                wl[(s, min(u, v), max(u, v))] += 1
        base.append(z3.PbEq([(z3.Xor(X[s][u], X[s][v]), w)
                             for (s, u, v), w in wl.items()], 334))
    subs = survivors("lp333_271_split.jsonl", "lp333_271_split_retry.jsonl")
    print(json.dumps({"event": "survivors", "count": len(subs)}), flush=True)
    outp = Path(a.out); done = set()
    if outp.exists():
        for line in outp.read_text().splitlines():
            try:
                r = json.loads(line); done.add((tuple(r["pa"]), tuple(r["pb"])))
            except Exception: pass
    for i, pa, pb in subs:
        if (tuple(pa), tuple(pb)) in done: continue
        slv = z3.Solver()
        slv.set("timeout", int(a.seconds*1000))
        for c in base: slv.add(c)
        for s, pat in ((0, pa), (1, pb)):
            for mm in range(9):
                v = X[s][fix_by_m[mm]]
                slv.add(v if mm in pat else z3.Not(v))
        t0 = time.time(); res = slv.check(); el = round(time.time()-t0, 1)
        rec = {"i": i, "pa": pa, "pb": pb, "engine": "z3-pb",
               "status": str(res).upper(), "elapsed_s": el}
        if res == z3.sat:
            m = slv.model()
            seq = [[1 if z3.is_true(m.eval(X[s][own[t]], model_completion=True)) else -1
                    for t in range(N)] for s in range(2)]
            bad = [d for d in range(1, N)
                   if sum(seq[s][t]*seq[s][(t+d) % N] for s in range(2) for t in range(N)) != -2]
            rec["verified_paf"] = not bad
            rec["sequences"] = seq
        print(json.dumps({k: v for k, v in rec.items() if k != "sequences"}), flush=True)
        with outp.open("a") as f: f.write(json.dumps(rec) + "\n")
        if rec.get("verified_paf"):
            Path("lp333_271_WITNESS.json").write_text(json.dumps(rec))
            print("WITNESS FOUND", flush=True)
            return
    print(json.dumps({"event": "done"}), flush=True)

if __name__ == "__main__":
    main()
