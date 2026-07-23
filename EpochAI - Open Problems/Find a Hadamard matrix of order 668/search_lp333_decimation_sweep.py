"""Decisive sweep: decimation-paired LP(333), b(x) = a(u*x), a K-invariant.

If b is a decimation of a, the Legendre-pair condition collapses to
  D(d) + D(u*d) = 334  for all d != 0,
where D(d) is the disagreement count of a at shift d. Only the orbits of K
carry free bits, so subgroup orders 6..9 (whose free-pair fibers are still
undecided at ~100+ bits) drop to ~41-60 bits and become CP-SAT-decidable.
Subgroups of order >= 12 are skipped: their full pair fibers are already
proven INFEASIBLE unconditionally, which subsumes all decimation pairs.
WLOG sum(a) = +1. u ranges over nontrivial cosets of K, deduped by u ~ u^-1
(same unordered pair) and u ~ K u.
"""
import argparse, json, math, time
from collections import Counter
from pathlib import Path
from ortools.sat.python import cp_model

N = 333

def all_subgroups():
    units = [x for x in range(1, N) if math.gcd(x, N) == 1]
    def closure(gens):
        s = {1}; frontier = {1}
        while frontier:
            nxt = set()
            for a in frontier:
                for g in gens:
                    v = a * g % N
                    if v not in s: s.add(v); nxt.add(v)
            frontier = nxt
        return frozenset(s)
    subs = set()
    for g1 in units: subs.add(closure((g1,)))
    for a in units:
        for b in units:
            if b > a: subs.add(closure((a, b)))
    return subs

def orbits_of(K):
    seen = [False]*N; orbs = []
    for i in range(N):
        if seen[i]: continue
        o = sorted({i*g % N for g in K})
        for x in o: seen[x] = True
        orbs.append(o)
    own = [0]*N
    for j, o in enumerate(orbs):
        for i in o: own[i] = j
    return orbs, own

def inv_mod(u): return pow(u, -1, N)

def solve_fiber(K, u, seconds, workers):
    orbs, own = orbits_of(K)
    sizes = [len(o) for o in orbs]
    m = cp_model.CpModel()
    x = [m.NewBoolVar(f"x_{j}") for j in range(len(orbs))]
    m.Add(sum(sizes[j]*x[j] for j in range(len(orbs))) == 167)
    y = {}
    def dis_terms(d):
        terms = []
        cnt = Counter()
        for i in range(N):
            a, b = own[i], own[(i+d) % N]
            if a == b: continue
            cnt[(min(a, b), max(a, b))] += 1
        for (a, b), coef in cnt.items():
            if (a, b) not in y:
                z = m.NewBoolVar(f"y_{a}_{b}")
                m.AddBoolXOr([x[a], x[b], z.Not()])
                y[(a, b)] = z
            terms.append(coef * y[(a, b)])
        return terms
    for d in range(1, N):
        ud = (u * d) % N
        m.Add(sum(dis_terms(d)) + sum(dis_terms(ud)) == 334)
    slv = cp_model.CpSolver()
    slv.parameters.max_time_in_seconds = seconds
    slv.parameters.num_search_workers = workers
    t0 = time.time(); st = slv.Solve(m)
    res = {"order": len(K), "u": u, "orbits": len(orbs), "bits": len(orbs),
           "status": slv.StatusName(st), "elapsed_s": round(time.time()-t0, 2),
           "conflicts": slv.NumConflicts(), "members_sample": sorted(K)[:8]}
    if st in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        a = [1 if slv.Value(x[own[i]]) else -1 for i in range(N)]
        b = [a[(u*i) % N] for i in range(N)]
        bad = [d for d in range(1, N)
               if sum(a[i]*a[(i+d) % N] + b[i]*b[(i+d) % N] for i in range(N)) != -2]
        res["verified_paf"] = not bad
        res["row_sums"] = [sum(a), sum(b)]
        res["sequences"] = [a, b]
    return res

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seconds", type=float, default=600)
    ap.add_argument("--workers", type=int, default=10)
    ap.add_argument("--min-order", type=int, default=4)
    ap.add_argument("--max-order", type=int, default=9)
    ap.add_argument("--out", default="lp333_decimation_sweep.jsonl")
    a = ap.parse_args()
    out = Path(a.out)
    done = set()
    if out.exists():
        for line in out.read_text().splitlines():
            try:
                r = json.loads(line); done.add((r["order"], tuple(r["members_sample"]), r["u"]))
            except Exception: pass
    subs = [K for K in all_subgroups() if a.min_order <= len(K) <= a.max_order]
    subs.sort(key=len, reverse=True)  # fewest bits first
    for K in subs:
        # coset reps of K in Z_N^*, dedup u ~ K u and u ~ K u^{-1}
        units = [x for x in range(1, N) if math.gcd(x, N) == 1]
        seen_cosets = set(); reps = []
        for u in units:
            cu = frozenset((u*k) % N for k in K)
            if 1 in cu: continue            # u in K: b=a, impossible (lambda non-integer)
            ci = frozenset((inv_mod(u)*k) % N for k in K)
            key = min(tuple(sorted(cu)), tuple(sorted(ci)))
            if key in seen_cosets: continue
            seen_cosets.add(key); reps.append(u)
        for u in reps:
            k3 = (len(K), tuple(sorted(K)[:8]), u)
            if k3 in done: continue
            r = solve_fiber(K, u, a.seconds, a.workers)
            print(json.dumps({k: v for k, v in r.items() if k != "sequences"}), flush=True)
            with out.open("a") as f: f.write(json.dumps(r) + "\n")
            if r["status"] in ("OPTIMAL", "FEASIBLE") and r.get("verified_paf"):
                print("WITNESS FOUND — stopping", flush=True)
                Path("lp333_decimation_WITNESS.json").write_text(json.dumps(r))
                return

if __name__ == "__main__":
    main()
