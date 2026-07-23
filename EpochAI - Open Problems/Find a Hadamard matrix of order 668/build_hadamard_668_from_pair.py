"""Strict witness gate for pair-type Hadamard-668 constructions.

Accepts either:
  --kind lp-cyclic   : Legendre pair over Z_333 (two length-333 +-1 lists)
  --kind lp-z3z3z37  : pair over Z_3 x Z_3 x Z_37 (two length-333 lists in
                       lexicographic (i,j,k) order as in the sweep script)
  --kind ngp334      : negaperiodic Golay pair of length 334 (Ito route)

For lp-* kinds the bordered two-block array of order 668 is constructed
(row sums are normalized to -1 by negation, which preserves PAF); for ngp334
the dicyclic development of order 668 is used. In every case the FULL integer
Gram matrix H H^T = 668 I is checked entry by entry before any CSV is
written; on success hadamard_668.csv and its SHA-256 are emitted.

Self-test: python build_hadamard_668_from_pair.py --self-test
runs both builders at small orders (H(20) from a Z3xZ3 pair and from Z_9;
H(20) from NGP(10)) and requires exact Gram passes.
"""
import argparse, hashlib, itertools, json, sys
import numpy as np


def bordered_two_block(a, b, add):
    """Bordered array from group-developed blocks. add: (i,j)->index of g_i+g_j
    is not needed; we need sub: (g,h)->index of h-g. Pass sub function."""
    n = len(a)
    if sum(a) == 1: a = [-v for v in a]
    if sum(b) == 1: b = [-v for v in b]
    assert sum(a) == -1 and sum(b) == -1, "row sums must be +-1"
    A = np.array([[a[add(g, h)] for h in range(n)] for g in range(n)])
    B = np.array([[b[add(g, h)] for h in range(n)] for g in range(n)])
    m = 2*n + 2
    H = np.zeros((m, m), dtype=np.int64)
    H[0, 0] = 1; H[0, 1] = 1; H[1, 0] = 1; H[1, 1] = -1
    H[0, 2:] = 1
    H[1, 2:2+n] = 1; H[1, 2+n:] = -1
    H[2:2+n, 0] = 1; H[2+n:, 0] = 1
    H[2:2+n, 1] = 1; H[2+n:, 1] = -1
    H[2:2+n, 2:2+n] = A;   H[2:2+n, 2+n:] = B
    H[2+n:, 2:2+n] = B.T;  H[2+n:, 2+n:] = -A.T
    return H


def sub_cyclic(n):
    return lambda g, h: (h - g) % n


def sub_z3z3z37():
    elems = [(i, j, k) for i in range(3) for j in range(3) for k in range(37)]
    idx = {g: t for t, g in enumerate(elems)}
    def sub(g, h):
        G, Hh = elems[g], elems[h]
        return idx[((Hh[0]-G[0]) % 3, (Hh[1]-G[1]) % 3, (Hh[2]-G[2]) % 37)]
    return sub


def ito_from_ngp(a, b):
    """Dicyclic development: NGP length n (even) -> Hadamard order 2n.
    Uses the standard block form H = [[A, B], [-B^T', A^T']] over the
    negacyclic algebra, realized concretely: N(x)_{ij} = x~_{j-i} with
    x~_{k+n} = -x~_k extended over Z_2n; blocks are the n x n negacyclic
    developments."""
    n = len(a)
    def nega(x):
        M = np.zeros((n, n), dtype=np.int64)
        for i in range(n):
            for j in range(n):
                d = j - i
                v = x[d % n] * (-1 if (d % (2*n)) >= n or d < 0 and (d % (2*n)) >= n else 1)
                # careful extension: x~_d for d in Z: x~_(d mod 2n), sign by block
                dd = d % (2*n)
                v = x[dd % n] * (-1 if dd >= n else 1)
                M[i, j] = v
        return M
    A = nega(a); B = nega(b)
    H = np.block([[A, B], [-B.T, A.T]]).astype(np.int64)
    return H


def gram_ok(H):
    n = H.shape[0]
    return np.array_equal(H @ H.T, n * np.eye(n, dtype=np.int64))


def self_test():
    ok_all = True
    # 1) Z3xZ3 pair -> H(20)
    G = [(i, j) for i in range(3) for j in range(3)]
    idx = {g: k for k, g in enumerate(G)}
    def paf(s, d):
        return sum(s[idx[g]]*s[idx[((g[0]+d[0]) % 3, (g[1]+d[1]) % 3)]] for g in G)
    cands = [c for c in itertools.product([1, -1], repeat=9) if sum(c) == 1]
    pair = None
    for a in cands:
        pa = {d: paf(a, d) for d in G if d != (0, 0)}
        for b in cands:
            if all(pa[d] + paf(b, d) == -2 for d in G if d != (0, 0)):
                pair = (list(a), list(b)); break
        if pair: break
    def subg(g, h):
        A_, B_ = G[g], G[h]
        return idx[((B_[0]-A_[0]) % 3, (B_[1]-A_[1]) % 3)]
    H = bordered_two_block(pair[0], pair[1], subg)
    t1 = gram_ok(H); ok_all &= t1
    print("self-test Z3xZ3 -> H(20):", "PASS" if t1 else "FAIL")
    # 2) Z9 cyclic pair -> H(20)
    def paf9(s, d): return sum(s[i]*s[(i+d) % 9] for i in range(9))
    pair = None
    for a in cands:
        pa = [paf9(a, d) for d in range(1, 9)]
        for b in cands:
            if all(pa[d-1] + paf9(b, d) == -2 for d in range(1, 9)):
                pair = (list(a), list(b)); break
        if pair: break
    H = bordered_two_block(pair[0], pair[1], sub_cyclic(9))
    t2 = gram_ok(H); ok_all &= t2
    print("self-test Z9 -> H(20):", "PASS" if t2 else "FAIL")
    # 3) NGP(10) -> H(20)
    def naf(x, d):
        n = len(x); t = 0
        for i in range(n):
            j = i + d
            t += x[i] * (x[j % n] * (-1 if (j//n) % 2 else 1))
        return t
    ngp = None
    for a in itertools.product([1, -1], repeat=10):
        if a[0] != 1: continue
        na = [naf(a, d) for d in range(1, 10)]
        for b in itertools.product([1, -1], repeat=10):
            if b[0] != 1: continue
            if all(naf(b, d) == -na[d-1] for d in range(1, 10)):
                ngp = (list(a), list(b)); break
        if ngp: break
    H = ito_from_ngp(ngp[0], ngp[1])
    t3 = gram_ok(H); ok_all &= t3
    print("self-test NGP(10) -> H(20):", "PASS" if t3 else "FAIL")
    return ok_all


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--kind", choices=["lp-cyclic", "lp-z3z3z37", "ngp334"])
    ap.add_argument("--witness-json", help="JSON file with key 'sequences' = [a, b]")
    ap.add_argument("--out", default="hadamard_668.csv")
    ap.add_argument("--self-test", action="store_true")
    args = ap.parse_args()
    if args.self_test:
        sys.exit(0 if self_test() else 1)
    data = json.loads(open(args.witness_json).read())
    a, b = data["sequences"]
    if args.kind == "lp-cyclic":
        assert len(a) == len(b) == 333
        H = bordered_two_block(a, b, sub_cyclic(333))
    elif args.kind == "lp-z3z3z37":
        assert len(a) == len(b) == 333
        H = bordered_two_block(a, b, sub_z3z3z37())
    else:
        assert len(a) == len(b) == 334
        H = ito_from_ngp(a, b)
    assert H.shape == (668, 668)
    assert set(np.unique(H)) <= {1, -1}
    if not gram_ok(H):
        print("GRAM CHECK FAILED - witness rejected, no CSV written")
        sys.exit(2)
    lines = "\n".join(",".join(str(int(v)) for v in row) for row in H)
    open(args.out, "w").write(lines + "\n")
    sha = hashlib.sha256(lines.encode()).hexdigest()
    print(json.dumps({"csv": args.out, "sha256": sha, "gram": "PASS 668I"}))


if __name__ == "__main__":
    main()
