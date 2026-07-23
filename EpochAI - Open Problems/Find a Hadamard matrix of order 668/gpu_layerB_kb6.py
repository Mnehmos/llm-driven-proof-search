"""GPU exhaustion of kB=6 layer-B (Z_3^2 quotient) classes for the group-333
tail. Space per M: 38^6 = 3.01e9 six-tuples over odd |<=37| entries with
weighted sum 1; PAF pair condition -74 over the 8 nonzero Z_3^2 shifts.
Complete decision per M; EMPTY closes every tail fiber with that M.
"""
import argparse, json, time
import numpy as np
import torch

def structure(M):
    Mm = tuple(M)
    seen = [[False]*3 for _ in range(3)]; orbs = []
    for i in range(3):
        for j in range(3):
            if seen[i][j]: continue
            o = set(); g = (i, j)
            while g not in o:
                o.add(g)
                g = ((Mm[0]*g[0]+Mm[1]*g[1]) % 3, (Mm[2]*g[0]+Mm[3]*g[1]) % 3)
            for t in o: seen[t[0]][t[1]] = True
            orbs.append(sorted(o))
    own = {}
    for j, o in enumerate(orbs):
        for t in o: own[t] = j
    return orbs, own

def decide(M, dev="cuda", max_verify=None):
    """Complete decision for one M.

    max_verify: optional resource guard on the number of hash-hit candidates
    exact-verified. When the guard trips, the verdict is
    INCONCLUSIVE_RESOURCE_CAP — never EMPTY_EXHAUSTIVE. (PR #265 review,
    blocker 3: the previous implementation silently checked only the first
    100,000 hash hits and could still report EMPTY_EXHAUSTIVE.) Every verdict
    records hash_hits_total and hash_hits_checked.
    """
    orbs, own = structure(M)
    k = len(orbs)
    assert k == 6, f"kB={k}"
    sizes = torch.tensor([len(o) for o in orbs], device=dev, dtype=torch.long)
    pos = [(i, j) for i in range(3) for j in range(3)]
    ownv = torch.tensor([own[p] for p in pos], device=dev, dtype=torch.long)
    perms = []
    for (di, dj) in [(x, y) for x in range(3) for y in range(3) if (x, y) != (0, 0)]:
        perms.append(torch.tensor([pos.index(((p[0]+di) % 3, (p[1]+dj) % 3))
                                   for p in pos], device=dev, dtype=torch.long))
    pows = torch.tensor([38**i for i in range(6)], device=dev, dtype=torch.long)
    rng = np.random.default_rng(21)
    rvec = torch.tensor(rng.integers(1, 1 << 62, size=8, dtype=np.int64), device=dev)
    hs = []; vals_keep = []
    total = 38**6
    chunk = 1 << 24
    t0 = time.time()
    for start in range(0, total, chunk):
        n = min(chunk, total - start)
        ints = torch.arange(start, start+n, device=dev, dtype=torch.long)
        D = (ints[:, None] // pows[None, :]) % 38
        vals = 2*D - 37
        m = (vals * sizes[None, :]).sum(1) == 1
        if not m.any(): continue
        vm = vals[m]
        seq = vm[:, ownv]                      # (b,9)
        V = torch.stack([(seq * seq[:, p]).sum(1) for p in perms], dim=1)
        hs.append((V * rvec[None, :]).sum(1))
        vals_keep.append(vm.to(torch.int8))
    h = torch.cat(hs)
    VK = torch.cat(vals_keep)
    # self-join: V_i + V_j = -74 <=> h_j = target - h_i with exact verify
    target = int((-74*torch.ones(8, dtype=torch.long)) @ rvec.cpu())
    sa, order = torch.sort(h)
    need = target - h
    ppos = torch.clamp(torch.searchsorted(sa, need), max=len(sa)-1)
    eq = sa[ppos] == need
    pairs = 0; example = None
    hash_hits_total = 0
    hash_hits_checked = 0
    if eq.any():
        idx = torch.nonzero(eq).flatten()
        hash_hits_total = int(idx.numel())
        for j in idx.tolist():
            if max_verify is not None and hash_hits_checked >= max_verify:
                break
            hash_hits_checked += 1
            vj = VK[j].to(torch.long)
            seqj = vj[ownv.cpu()]
            Vj = torch.stack([(seqj * seqj[p.cpu()]).sum() for p in perms])
            lo = torch.searchsorted(sa, need[j]).item()
            hi = torch.searchsorted(sa, need[j], right=True).item()
            for q in range(lo, hi):
                i_ = order[q].item()
                vi = VK[i_].to(torch.long)
                seqi = vi[ownv.cpu()]
                Vi = torch.stack([(seqi * seqi[p.cpu()]).sum() for p in perms])
                if torch.equal(Vi + Vj, -74*torch.ones(8, dtype=torch.long)):
                    pairs += 1
                    if example is None:
                        example = (vi.tolist(), vj.tolist())
    if pairs > 0:
        verdict = "NONEMPTY"
    elif hash_hits_checked < hash_hits_total:
        verdict = "INCONCLUSIVE_RESOURCE_CAP"
    else:
        verdict = "EMPTY_EXHAUSTIVE"
    return {"M": list(M), "kB6_layer": verdict,
            "candidates": int(len(h)), "pairs": pairs, "example": example,
            "hash_hits_total": hash_hits_total, "hash_hits_checked": hash_hits_checked,
            "elapsed_s": round(time.time()-t0, 1)}

if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--Ms", type=str, required=True,
                    help="semicolon-separated M quadruples, e.g. '0,1,1,0;0,2,2,0'")
    ap.add_argument("--out", default="group333_kb6_layerB.jsonl")
    ap.add_argument("--max-verify", type=int, default=None,
                    help="optional resource guard; exceeding it forces INCONCLUSIVE_RESOURCE_CAP")
    a = ap.parse_args()
    from pathlib import Path
    for mstr in a.Ms.split(";"):
        M = [int(x) for x in mstr.split(",")]
        r = decide(M, max_verify=a.max_verify)
        print(json.dumps(r), flush=True)
        with Path(a.out).open("a") as f:
            f.write(json.dumps(r) + "\n")
