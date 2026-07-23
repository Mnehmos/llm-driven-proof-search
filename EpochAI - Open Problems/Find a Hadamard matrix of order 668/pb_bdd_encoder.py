"""Minimal BDD (interval) encoder for weighted PB equality over booleans.

encode_pb_equals(lits, weights, bound, pool) -> list of clauses whose
satisfying assignments are exactly those with sum(w_i * lit_i) == bound.
Standard ROBDD construction over partial sums with unit-propagation-friendly
Tseitin translation: node variable n <-> (x ? hi : lo).

Auxiliary-variable namespacing: every call takes a fresh value from a
module-level monotonic counter, so two encodings can NEVER share auxiliary
variables even when they target the same pool. (The original implementation
keyed on id(lits) — a temporary CPython memory address that can be reused
after garbage collection, which could alias BDD nodes of *different*
constraints encoded into one persistent pool and corrupt the conjunction,
risking false UNSAT. See PR #265 review, blocker 2.)
"""
import itertools as _itertools

_ENCODING_SEQ = _itertools.count()

def encode_pb_equals(lits, weights, bound, pool):
    encoding_id = next(_ENCODING_SEQ)
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
        v = pool.id(("pb", encoding_id, i, s))
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

    def dpll(cls, assign):
        # tiny DPLL with unit propagation; cls are lists of ints, assign maps var->0/1
        cls = [c for c in cls]
        while True:
            unit = None
            new_cls = []
            for c in cls:
                vals = [(assign.get(abs(l)), l) for l in c]
                if any(v == (1 if l > 0 else 0) for v, l in vals):
                    continue  # satisfied
                rem = [l for v, l in vals if v is None]
                if not rem:
                    return False  # falsified clause
                if len(rem) == 1:
                    unit = rem[0]
                new_cls.append(rem)
            cls = new_cls
            if not cls:
                return True
            if unit is None:
                break
            assign = dict(assign)
            assign[abs(unit)] = 1 if unit > 0 else 0
        v = abs(cls[0][0])
        for b in (0, 1):
            a2 = dict(assign)
            a2[v] = b
            if dpll(cls, a2):
                return True
        return False

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
            if cls == [[]]:
                found = False
            else:
                found = dpll(cls, {i+1: b for i, b in enumerate(bits)})
            if found != target:
                ok = False
                print("MISMATCH", trial, k, weights, bound, bits, "enc:", found, "want:", target)
                break
        if not ok: break
    else:
        print("PB-BDD encoder: 200 randomized trials passed")

    # Regression (PR #265 review, blocker 2): several DIFFERENT PB equalities
    # encoded into the SAME persistent pool, whole-conjunction brute force.
    # Under the old id(lits) namespacing, freed-list address reuse could alias
    # aux vars across constraints; this test drives many constraints through
    # one pool (with lists going out of scope between calls) and checks the
    # conjunction exactly.
    random.seed(11)
    all_ok = True
    for trial in range(60):
        k = random.randint(2, 5)
        n_cons = random.randint(2, 4)
        cons = []
        pool = Pool(k)
        clauses = []
        for _ in range(n_cons):
            weights = [random.randint(1, 5) for _ in range(k)]
            bound = random.randint(0, sum(weights))
            cons.append((weights, bound))
            lits = list(range(1, k + 1))  # fresh list each call; goes out of scope
            cls = encode_pb_equals(lits, weights, bound, pool)
            del lits
            if cls == [[]]:
                clauses = [[]]
                break
            clauses.extend(cls)
        for bits in itertools.product([0, 1], repeat=k):
            target = all(sum(w * b for w, b in zip(ws, bits)) == bd for ws, bd in cons)
            if clauses == [[]]:
                found = False
            else:
                found = dpll(clauses, {i + 1: b for i, b in enumerate(bits)})
            if found != target:
                all_ok = False
                print("MULTI-CONSTRAINT MISMATCH", trial, cons, bits, "enc:", found, "want:", target)
                break
        if not all_ok:
            break
    if all_ok:
        print("PB-BDD encoder: 60 multi-constraint same-pool conjunction trials passed")
