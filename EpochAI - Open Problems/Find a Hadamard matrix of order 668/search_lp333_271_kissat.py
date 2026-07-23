"""Kissat wave over the surviving <271> sub-fibers.

Builds one base CNF for the <271> fiber (validated BDD PB encoder for the 44
deduplicated shift equalities + totalizer cardinalities for the nine-orbit
sums; XORs expanded to 4-clause CNF) and decides each surviving sub-fiber by
adding 18 unit clauses for the fixed-point patterns. Independent integer PAF
verification on any SAT model before it is reported.
"""
import argparse, json, time
from collections import Counter
from pathlib import Path

import importlib.util
spec = importlib.util.spec_from_file_location("sp", "search_lp333_271_split.py")
sp = importlib.util.module_from_spec(spec)
spec.loader.exec_module(sp)

from pysat.formula import IDPool
from pysat.card import CardEnc, EncType
from pysat.solvers import Solver
from pb_bdd_encoder import encode_pb_equals

N = 333
K, orbs, own = sp.K, sp.orbs, sp.own
fixed, nines, fix_by_m = sp.fixed, sp.nines, sp.fix_by_m

def build_base():
    pool = IDPool()
    X = [[pool.id(f"x{s}_{j}") for j in range(len(orbs))] for s in range(2)]
    cnf = []
    # nine-orbit cardinalities (18 of 36) per sequence
    for s in range(2):
        enc = CardEnc.equals(lits=[X[s][j] for j in nines], bound=18,
                             vpool=pool, encoding=EncType.totalizer)
        cnf.extend(enc.clauses)
    # deduplicated PB shift equalities with XOR defs as CNF
    Z = {}
    def zvar(s, u, v):
        key = (s, min(u, v), max(u, v))
        if key not in Z:
            z = pool.id(f"z{key}")
            a, b = X[s][key[1]], X[s][key[2]]
            cnf.extend([[-z, a, b], [-z or 1, 0]][:0])  # placeholder no-op
            cnf.extend([[-a, b, z], [a, -b, z], [-a, -b, -z], [a, b, -z]])
            Z[key] = z
        return Z[key]
    shift_seen = set()
    nshift = 0
    for d in range(1, N):
        if d in shift_seen: continue
        shift_seen.update({d * g % N for g in K})
        nshift += 1
        wl = Counter()
        for s in range(2):
            for i in range(N):
                u, v = own[i], own[(i + d) % N]
                if u == v: continue
                wl[zvar(s, u, v)] += 1
        lits = list(wl.keys()); weights = [wl[l] for l in lits]
        cnf.extend(encode_pb_equals(lits, weights, 334, pool))
    assert nshift == 44
    return pool, X, cnf

def survivors(split_file, retry_file):
    decided = set()
    rp = Path(retry_file)
    if rp.exists():
        for line in rp.read_text().splitlines():
            try:
                r = json.loads(line)
                if r["status"] != "UNKNOWN":
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
    ap.add_argument("--engine", default="kissat404")
    ap.add_argument("--out", default="lp333_271_kissat.jsonl")
    ap.add_argument("--split", default="lp333_271_split.jsonl")
    ap.add_argument("--retry", default="lp333_271_split_retry.jsonl")
    a = ap.parse_args()
    pool, X, base = build_base()
    print(json.dumps({"event": "base_cnf", "vars": pool.top, "clauses": len(base)}), flush=True)
    subs = survivors(a.split, a.retry)
    print(json.dumps({"event": "survivors", "count": len(subs)}), flush=True)
    outp = Path(a.out); done = set()
    if outp.exists():
        for line in outp.read_text().splitlines():
            try:
                r = json.loads(line); done.add((tuple(r["pa"]), tuple(r["pb"])))
            except Exception: pass
    for i, pa, pb in subs:
        if (tuple(pa), tuple(pb)) in done: continue
        units = []
        for s, pat in ((0, pa), (1, pb)):
            for mm in range(9):
                v = X[s][fix_by_m[mm]]
                units.append([v] if mm in pat else [-v])
        t0 = time.time()
        with Solver(name=a.engine, bootstrap_with=base + units) as slv:
            sat = slv.solve()
            model = slv.get_model() if sat else None
        el = round(time.time() - t0, 1)
        rec = {"i": i, "pa": pa, "pb": pb, "engine": a.engine,
               "sat": sat, "elapsed_s": el}
        if sat:
            mset = set(l for l in model if l > 0)
            seq = [[1 if X[s][own[t]] in mset else -1 for t in range(N)] for s in range(2)]
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
