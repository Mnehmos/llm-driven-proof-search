"""Dedicated SAT attack on the last resistant LP(333) multiplier fiber <271>.

K = <271> = Z_9 acting on Z_333 (trivial on the 9-part, order-9 cyclotomy on
the 37-part). Structure exploited:
  - 45 orbits/sequence: 9 fixed points (multiples of 37) + 36 nine-orbits.
  - Row sum +1  =>  exactly 5/9 fixed and 18/36 nine-orbit variables true.
  - PAF of a K-invariant sequence is K-invariant in the shift, so only 44
    distinct shift constraints (8 nonzero fixed-shift orbits + 36 nine-orbits).
Encodings: weighted PB equalities via pysat PBEnc; XOR defs either as native
CryptoMiniSat xor clauses or 4-clause CNF for CDCL solvers.
"""
import argparse, json, math, time
from collections import Counter
from pathlib import Path

N = 333
K = []
x = 1
while True:
    K.append(x); x = x*271 % N
    if x == 1: break
K = sorted(K)
assert len(K) == 9

# orbits
seen = [False]*N; orbs = []
for i in range(N):
    if seen[i]: continue
    o = sorted({i*g % N for g in K})
    for t in o: seen[t] = True
    orbs.append(o)
own = [0]*N
for j, o in enumerate(orbs):
    for i in o: own[i] = j
sizes = [len(o) for o in orbs]
fixed = [j for j, s in enumerate(sizes) if s == 1]
nines = [j for j, s in enumerate(sizes) if s == 9]
assert len(fixed) == 9 and len(nines) == 36

# distinct shift-orbit representatives
shift_seen = set(); shift_reps = []
for d in range(1, N):
    if d in shift_seen: continue
    so = {d*g % N for g in K}
    shift_seen.update(so); shift_reps.append(d)
assert len(shift_reps) == 44

def build_cnf():
    from pysat.formula import IDPool
    from pysat.card import CardEnc, EncType
    from pb_bdd_encoder import encode_pb_equals
    pool = IDPool()
    X = [[pool.id(f"x{s}_{j}") for j in range(len(orbs))] for s in range(2)]
    clauses = []
    xors = []          # (lits, rhs) native xor: z = xu ^ xv  <->  z^xu^xv = 0
    Z = {}
    def zvar(s, u, v):
        key = (s, min(u, v), max(u, v))
        if key not in Z:
            z = pool.id(f"z{key}")
            Z[key] = z
            xors.append(([z, X[s][key[1]], X[s][key[2]]], False))
        return Z[key]
    # cardinalities
    for s in range(2):
        for lits, k in ((([X[s][j] for j in fixed]), 5), (([X[s][j] for j in nines]), 18)):
            enc = CardEnc.equals(lits=lits, bound=k, vpool=pool, encoding=EncType.totalizer)
            clauses.extend(enc.clauses)
    # 44 distinct PB equalities
    for d in shift_reps:
        wl = Counter()
        for s in range(2):
            for i in range(N):
                u, v = own[i], own[(i+d) % N]
                if u == v: continue
                wl[zvar(s, u, v)] += 1
        lits = list(wl.keys()); weights = [wl[l] for l in lits]
        clauses.extend(encode_pb_equals(lits, weights, 334, pool))
    return pool, X, clauses, xors

def run_cms(seconds):
    from pycryptosat import Solver
    pool, X, clauses, xors = build_cnf()
    s = Solver(threads=4)
    for c in clauses: s.add_clause(c)
    for lits, rhs in xors: s.add_xor_clause(lits, rhs)
    t0 = time.time()
    sat, sol = s.solve()  # no timeout param in older pycryptosat; rely on external
    el = time.time() - t0
    return sat, sol, X, el

def run_cdcl(name, seconds):
    from pysat.solvers import Solver
    pool, X, clauses, xors = build_cnf()
    cnf = list(clauses)
    for lits, rhs in xors:
        a, b, c = lits
        if rhs is False:
            cnf += [[-a, b, c], [a, -b, c], [a, b, -c], [-a, -b, -c]]
    with Solver(name=name, bootstrap_with=cnf, use_timer=True) as s:
        ok = s.solve_limited(expect_interrupt=False) if False else s.solve()
        model = s.get_model() if ok else None
        return ok, model, X, s.time()

def verify_and_dump(model_get, X, tag):
    a_seqs = []
    for s in range(2):
        vals = [1 if model_get(X[s][own[i]]) else -1 for i in range(N)]
        a_seqs.append(vals)
    bad = [d for d in range(1, N)
           if sum(a_seqs[s][i]*a_seqs[s][(i+d) % N] for s in range(2) for i in range(N)) != -2]
    out = {"fiber": "<271>", "tag": tag, "verified": not bad,
           "row_sums": [sum(q) for q in a_seqs], "sequences": a_seqs}
    Path("lp333_271_WITNESS.json").write_text(json.dumps(out))
    return not bad

if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--engine", default="cms")
    ap.add_argument("--seconds", type=float, default=3600)
    a = ap.parse_args()
    t0 = time.time()
    if a.engine == "cms":
        sat, sol, X, el = run_cms(a.seconds)
        print(json.dumps({"engine": "cryptominisat", "sat": sat, "elapsed_s": round(el, 1)}), flush=True)
        if sat:
            ok = verify_and_dump(lambda v: sol[v], X, "cms")
            print("verified:", ok)
    else:
        ok, model, X, el = run_cdcl(a.engine, a.seconds)
        print(json.dumps({"engine": a.engine, "sat": ok, "elapsed_s": round(el, 1)}), flush=True)
        if ok:
            mset = set(l for l in model if l > 0)
            okv = verify_and_dump(lambda v: v in mset, X, a.engine)
            print("verified:", okv)
