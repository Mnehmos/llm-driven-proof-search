"""Complete decision of the 3-compression layer of the <271> LP(333) fiber.

If a is <271>-invariant on Z_333, its 3-compression c_a(x) = a(x) + a(x+111)
+ a(x+222) is <49>-invariant on Z_111 with entries in {-3,-1,1,3}; the pair
condition compresses to PAF_ca(d) + PAF_cb(d) = -6 for d != 0. Row sums give
sum(c) = 1, and mod-9 arithmetic forces the three fixed-point values (at
0, 37, 74) to sum to exactly 1 and the twelve nine-orbit values to sum to 0.
This layer is a NECESSARY condition: if it is empty, the entire <271> fiber
(all 81 surviving sub-fibers) is closed in one stroke.
Derivation checks included: PAF_c(d) = sum_k PAF_a(d + 111k) verified
numerically on random sequences before the sweep.
"""
import itertools, json, time
import numpy as np

N3, N1 = 333, 111
# --- derivation self-check on random data ---
rng = np.random.default_rng(5)
for _ in range(3):
    a = rng.choice([1, -1], size=N3)
    c = np.array([a[x] + a[(x+111) % N3] + a[(x+222) % N3] for x in range(N1)])
    d = int(rng.integers(1, N1))
    paf_c = int(np.dot(c, np.roll(c, -d)))
    paf_sum = sum(int(np.dot(a, np.roll(a, -(d + 111*k)))) for k in range(3))
    assert paf_c == paf_sum, "compression identity FAILED"
print("compression identity verified on random data", flush=True)

# --- <49> orbits on Z_111 ---
K = []
x = 1
while True:
    K.append(x); x = x*49 % N1
    if x == 1: break
assert len(K) == 9
seen = [False]*N1; orbs = []
for i in range(N1):
    if seen[i]: continue
    o = sorted({i*g % N1 for g in K})
    for t in o: seen[t] = True
    orbs.append(o)
own = [0]*N1
for j, o in enumerate(orbs):
    for i in o: own[i] = j
sizes = [len(o) for o in orbs]
fixed = [j for j, s in enumerate(sizes) if s == 1]
nine = [j for j, s in enumerate(sizes) if s == 9]
print(json.dumps({"orbits": len(orbs), "fixed": len(fixed), "nine": len(nine)}), flush=True)
assert len(fixed) == 3 and len(nine) == 12

# shift reps under <49>
sseen = set(); reps = []
for d in range(1, N1):
    if d in sseen: continue
    so = {d*g % N1 for g in K}
    sseen |= so; reps.append(d)
R = len(reps)
C = np.zeros((R, 15, 15), dtype=np.int64)
for ri, d in enumerate(reps):
    for i in range(N1):
        C[ri, own[i], own[(i+d) % N1]] += 1

ALPH = np.array([-3, -1, 1, 3], dtype=np.int64)
# fixed triples with sum exactly 1
fixed_opts = [t for t in itertools.product(ALPH, repeat=3) if sum(t) == 1]
# nine-orbit 12-tuples with sum 0: enumerate 4^12 = 16.7M via mixed radix in chunks
print(json.dumps({"fixed_options": len(fixed_opts)}), flush=True)

def nine_batches(chunk=1 << 20):
    total = 4**12
    digs = np.arange(12)
    for start in range(0, total, chunk):
        n = min(chunk, total - start)
        ints = np.arange(start, start+n, dtype=np.int64)
        idx = (ints[:, None] // (4**digs)[None, :]) % 4
        vals = ALPH[idx]
        yield vals[vals.sum(1) == 0]

# enumerate all c = (fixed triple, nine 12-tuple); PAF via bilinear forms
def paf_all(Cmat, full):  # full: (m,15)
    out = np.empty((len(full), R), dtype=np.int64)
    f = full.astype(np.float64)
    for r in range(R):
        out[:, r] = np.round(((f @ Cmat[r]) * f).sum(1)).astype(np.int64)
    return out

t0 = time.time()
hs, ts, store = [], [], []
rvec = rng.integers(1, 1 << 62, size=R, dtype=np.int64)
count = 0
for nine_vals in nine_batches():
    if len(nine_vals) == 0: continue
    for ft in fixed_opts:
        m = len(nine_vals)
        full = np.empty((m, 15), dtype=np.int64)
        for fi, j in enumerate(fixed):
            full[:, j] = ft[fi]
        full[:, nine] = nine_vals
        V = paf_all(C, full)
        hs.append(V @ rvec)
        ts.append((-6 - V) @ rvec)
        store.append(full)
        count += m
print(json.dumps({"event": "enumerated", "valid": count,
                  "elapsed_s": round(time.time()-t0, 1)}), flush=True)
h = np.concatenate(hs); t = np.concatenate(ts); P = np.concatenate(store)
del hs, ts, store
common = np.intersect1d(h, t)
print(json.dumps({"hash_matches": len(common)}), flush=True)
wit = None
if len(common):
    oh = np.argsort(h); ot = np.argsort(t)
    hh = h[oh]; tt = t[ot]
    for val in common:
        i0, i1 = np.searchsorted(hh, val), np.searchsorted(hh, val, side="right")
        j0, j1 = np.searchsorted(tt, val), np.searchsorted(tt, val, side="right")
        for i in oh[i0:i1]:
            Vi = paf_all(C, P[i][None, :])[0]
            for j in ot[j0:j1]:
                Vj = paf_all(C, P[j][None, :])[0]
                if np.array_equal(Vi + Vj, -6*np.ones(R, dtype=np.int64)):
                    wit = (P[i].tolist(), P[j].tolist())
                    break
            if wit: break
        if wit: break
print(json.dumps({"compression_layer": "NONEMPTY" if wit else "EMPTY_EXHAUSTIVE",
                  "witness": wit}), flush=True)
