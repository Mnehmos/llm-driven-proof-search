"""Minimal BDD (interval) encoder for weighted PB equality over booleans.

encode_pb_equals(lits, weights, bound, pool) -> list of clauses whose
satisfying assignments are exactly those with sum(w_i * lit_i) == bound.
Standard ROBDD construction over partial sums with unit-propagation-friendly
Tseitin translation: node variable n <-> (x ? hi : lo).
"""
def encode_pb_equals(lits, weights, bound, pool):
    order = sorted(range(len(lits)), key=lambda i: -weights[i])
    ls = [lits[i] for i in order]
    ws = [weights[i] for i in order]
    n = len(ls)
    suffix = [0]*(n+1)
    for i in range(n-1, -1, -1):
        suffix[i] = suffix[i+1] + ws[i]
    TRUE, FALSE = "T", "F"
    cache = {}
    clauses = []
    def node(i, s):
        # returns literal representing "assignment of ls[i:] can reach bound from partial sum s"
        if s > bound or s + suffix[i] < bound:
            return FALSE
        if i == n:
            return TRUE if s == bound else FALSE
        key = (i, s)
        if key in cache: return cache[key]
        hi = node(i+1, s + ws[i])
        lo = node(i+1, s)
        if hi == lo:
            cache[key] = hi
            return hi
        v = pool.id(("pb", id(lits), i, s))
        x = ls[i]
        # v <-> (x -> hi) & (~x -> lo)
        if hi == TRUE:   clauses.append([-v, x] if lo == FALSE else [-v, x, _l(lo)])
        elif hi == FALSE: clauses.append([-v, -x] if lo == TRUE else None)
        # general Tseitin (covers all cases uniformly):
        def lit_of(t):
            return None if t in (TRUE, FALSE) else t
        # v -> (x -> hi)
        if hi == FALSE: clauses.append([-v, -x])
        elif hi != TRUE: clauses.append([-v, -x, hi])
        # v -> (~x -> lo)
        if lo == FALSE: clauses.append([-v, x])
        elif lo != TRUE: clauses.append([-v, x, lo])
        # (x & hi) -> v ; (~x & lo) -> v
        if hi == TRUE: clauses.append([v, -x])
        elif hi != FALSE: clauses.append([v, -x, -hi])
        if lo == TRUE: clauses.append([v, x])
        elif lo != FALSE: clauses.append([v, x, -lo])
        cache[key] = v
        return v
    def _l(t): return t
    root = node(0, 0)
    # clean Nones from the early ad-hoc branch (kept for structure; general covers)
    clauses = [c for c in clauses if c is not None]
    if root == TRUE: return clauses
    if root == FALSE: return [[]]  # unsatisfiable
    clauses.append([root])
    return clauses

if __name__ == "__main__":
    # self-test vs brute force
    import itertools
    class Pool:
        def __init__(self, start): self.top = start; self.map = {}
        def id(self, key):
            if key not in self.map:
                self.top += 1; self.map[key] = self.top
            return self.map[key]
    import random
    random.seed(7)
    for trial in range(200):
        k = random.randint(1, 7)
        lits = list(range(1, k+1))
        weights = [random.randint(1, 6) for _ in range(k)]
        bound = random.randint(0, sum(weights))
        pool = Pool(k)
        cls = encode_pb_equals(lits, weights, bound, pool)
        if cls == [[]]:
            sat_sets = None
        # brute force check
        ok = True
        for bits in itertools.product([0,1], repeat=k):
            target = (sum(w*b for w, b in zip(weights, bits)) == bound)
            # check whether exists extension of aux vars satisfying clauses
            n_aux = pool.top - k
            found = False
            if cls == [[]]:
                found = False
            else:
                for aux in itertools.product([0,1], repeat=n_aux):
                    assign = {}
                    for i, b in enumerate(bits): assign[i+1] = b
                    for i, b in enumerate(aux): assign[k+1+i] = b
                    if all(any((assign[abs(l)] == 1) == (l > 0) for l in c) for c in cls):
                        found = True; break
            if found != target:
                ok = False
                print("MISMATCH", trial, k, weights, bound, bits, "enc:", found, "want:", target)
                break
        if not ok: break
    else:
        print("PB-BDD encoder: 200 randomized trials passed")
