"""Decisive sweep: LP(333) fibers invariant under EVERY subgroup of Z_333^*.

Unlike search_lp333_multiplier_cpsat.py this does NOT prescribe the chi_37
compression and does not restrict to h=1 mod 3 or orders 6..18. It enumerates
all 80 subgroups of Z_333^* (rank <= 2, so closures of pairs suffice), then
decides each K-invariant Legendre-pair fiber with CP-SAT:

  a,b in {+-1}^333 K-invariant, sum(a)=sum(b)=1,
  PAF_a(d)+PAF_b(d) = -2 for all d != 0.

WLOG both row sums are +1 (negation preserves PAF). A FEASIBLE result is an
exact Legendre pair and hence a Hadamard matrix of order 668; INFEASIBLE
closes that symmetry class rigorously. Results are streamed as JSON lines.
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
                    if v not in s:
                        s.add(v); nxt.add(v)
            frontier = nxt
        return frozenset(s)
    subs = set()
    for g1 in units:
        subs.add(closure((g1,)))
    for a in units:
        for b in units:
            if b > a:
                subs.add(closure((a, b)))
    return sorted(subs, key=len, reverse=True)

def orbits_of(K):
    seen = [False]*N; orbs = []
    for i in range(N):
        if seen[i]: continue
        o = sorted({i*g % N for g in K})
        for x in o: seen[x] = True
        orbs.append(o)
    owner = [0]*N
    for j, o in enumerate(orbs):
        for i in o: owner[i] = j
    return orbs, owner

def solve_fiber(K, seconds, workers):
    orbs, own = orbits_of(K)
    sizes = [len(o) for o in orbs]
    m = cp_model.CpModel()
    x = [[m.NewBoolVar(f"x{s}_{j}") for j in range(len(orbs))] for s in range(2)]
    # row sums: number of +1 entries = 167 in each sequence
    for s in range(2):
        m.Add(sum(sizes[j]*x[s][j] for j in range(len(orbs))) == 167)
    # PAF sum condition via XOR counting: for each shift d, the number of
    # disagreeing pairs (over both sequences) equals (666+2)/2 = 334.
    y = {}
    added = 0
    for d in range(1, N):
        terms = []
        const = 0
        for s in range(2):
            cnt = Counter()
            for i in range(N):
                u, v = own[i], own[(i+d) % N]
                if u == v:
                    continue  # agreeing (same orbit value): contributes 0 disagreements
                cnt[(min(u, v), max(u, v))] += 1
            for (u, v), coef in cnt.items():
                key = (s, u, v)
                if key not in y:
                    z = m.NewBoolVar(f"y{s}_{u}_{v}")
                    m.AddBoolXOr([x[s][u], x[s][v], z.Not()])
                    y[key] = z
                terms.append(coef * y[key])
        m.Add(sum(terms) == 334)
        added += 1
    slv = cp_model.CpSolver()
    slv.parameters.max_time_in_seconds = seconds
    slv.parameters.num_search_workers = workers
    t0 = time.time()
    st = slv.Solve(m)
    name = slv.StatusName(st)
    res = {"order": len(K), "orbits": len(orbs), "total_bits": 2*len(orbs),
           "contains_minus1": (N-1) in K, "status": name,
           "elapsed_s": round(time.time()-t0, 2), "conflicts": slv.NumConflicts(),
           "members_sample": sorted(K)[:8]}
    if st in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        seq = [[1 if slv.Value(x[s][own[i]]) else -1 for i in range(N)] for s in range(2)]
        # independent integer verification
        bad = []
        for d in range(1, N):
            v = sum(seq[s][i]*seq[s][(i+d) % N] for s in range(2) for i in range(N))
            if v != -2: bad.append((d, v))
        res["verified_paf"] = not bad
        res["row_sums"] = [sum(q) for q in seq]
        res["sequences"] = seq
        if bad: res["bad_shifts"] = bad[:10]
    return res

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seconds", type=float, default=120)
    ap.add_argument("--workers", type=int, default=8)
    ap.add_argument("--max-bits", type=int, default=80)
    ap.add_argument("--out", default="lp333_full_multiplier_sweep.jsonl")
    a = ap.parse_args()
    subs = all_subgroups()
    out = Path(a.out)
    done_keys = set()
    if out.exists():
        for line in out.read_text().splitlines():
            try:
                r = json.loads(line)
                done_keys.add(tuple(r["members_sample"]) + (r["order"],))
            except Exception:
                pass
    unsat_subgroups = []  # if K unsat, any supergroup of K is unsat too
    for K in subs:
        orbs, _ = orbits_of(K)
        bits = 2*len(orbs)
        if bits > a.max_bits:
            continue
        key = tuple(sorted(K)[:8]) + (len(K),)
        if key in done_keys:
            continue
        # lattice propagation: skip if a known-UNSAT subgroup is contained in K
        implied = next((frozenset(U) for U in unsat_subgroups if U <= K), None)
        if implied is not None:
            r = {"order": len(K), "orbits": len(orbs), "total_bits": bits,
                 "contains_minus1": (N-1) in K, "status": "INFEASIBLE_IMPLIED",
                 "implied_by_order": len(implied), "members_sample": sorted(K)[:8]}
            print(json.dumps(r), flush=True)
            with out.open("a") as f: f.write(json.dumps(r) + "\n")
            continue
        r = solve_fiber(K, a.seconds, a.workers)
        print(json.dumps({k: v for k, v in r.items() if k != "sequences"}), flush=True)
        with out.open("a") as f: f.write(json.dumps(r) + "\n")
        if r["status"] == "INFEASIBLE":
            unsat_subgroups.append(frozenset(K))
        if r["status"] in ("OPTIMAL", "FEASIBLE") and r.get("verified_paf"):
            print("WITNESS FOUND — stopping sweep", flush=True)
            Path("lp333_multiplier_WITNESS.json").write_text(json.dumps(r))
            break

if __name__ == "__main__":
    main()
