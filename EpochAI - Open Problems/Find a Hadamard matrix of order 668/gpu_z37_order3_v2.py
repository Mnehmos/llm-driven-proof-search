"""Fast complete decision of the shared Z_37 layer for <10>, <121>, <211>.

Candidate space: d0 in {-5,1,7}; twelve 3-orbit values v in {odd -9..9} with
sum(v) = (1-d0)/3. Rigorous per-side filters (both derived from the exact
identity PSD_a(k) + PSD_b(k) = 668, PSD >= 0):
  - Parseval mean cap: 37*(d0^2 + 3*sum(v^2)) - 1 - 1 <= 36*668
    => sum(v^2) <= (650 - d0^2 + eps)/3   (separable across halves)
  - max-PSD cap: max_k PSD(k) <= 668 (+0.5 fp32 margin, over-keeping only).
Generation: split the 12 orbits into two halves of 6; bucket each half's
10^6 tuples by (sum, sumsq); only compatible bucket pairs are expanded, in
GPU blocks, with the max-PSD test fused per block. Survivors' exact integer
PAF vectors are collected; the final self-join looks for V_i + V_j = -18.
A planted-pair join test validates the final stage.
"""
import argparse, itertools, json, time
import numpy as np
import torch

P = 37
IMG = [1, 10, 26]

def structure():
    seen = [False]*P; orbs = []
    for i in range(P):
        if seen[i]: continue
        o = sorted({(i*g) % P for g in IMG})
        for t in o: seen[t] = True
        orbs.append(o)
    own = [0]*P
    for j, o in enumerate(orbs):
        for i in o: own[i] = j
    sseen = set(); reps = []
    for d in range(1, P):
        if d in sseen: continue
        sseen.update({(d*g) % P for g in IMG}); reps.append(d)
    C = np.zeros((len(reps), len(orbs), len(orbs)), dtype=np.int64)
    for ri, d in enumerate(reps):
        for i in range(P):
            C[ri, own[i], own[(i+d) % P]] += 1
    return orbs, own, reps, C

def main():
    t00 = time.time()
    orbs, own, reps, C = structure()
    k = len(orbs); R = len(reps)
    dev = "cuda"
    # orbit-character matrix for frequencies 1..36
    Gm = np.zeros((k, P-1), dtype=np.complex128)
    for j, o in enumerate(orbs):
        for kk in range(1, P):
            Gm[j, kk-1] = sum(np.exp(-2j*np.pi*kk*x/P) for x in o)
    G = torch.tensor(Gm, device=dev, dtype=torch.complex64)   # (13,36)
    Ct = torch.tensor(C, device=dev, dtype=torch.float32)
    # halves: orbit indices 1..6 and 7..12 (orbit 0 is d0)
    ALPH = np.arange(-9, 10, 2, dtype=np.int64)
    six = np.array(list(itertools.product(ALPH, repeat=6)), dtype=np.int64)  # (1e6,6)
    sums = six.sum(1); sq = (six*six).sum(1)
    sixt = torch.tensor(six, device=dev, dtype=torch.float32)
    # half DFT contributions
    GL = G[1:7, :]; GR = G[7:13, :]
    L_hat = sixt.to(torch.complex64) @ GL     # (1e6, 36)
    R_hat = sixt.to(torch.complex64) @ GR
    surv_V = []; surv_meta = []
    total_pairs_tested = 0
    for d0 in (-5, 1, 7):
        need = (1 - d0)//3
        qmax = (650 - d0*d0)//3 + 1
        base = torch.tensor(Gm[0, :]*d0, device=dev, dtype=torch.complex64)
        # bucket by exact sum; within, order by sumsq
        for sL in np.unique(sums):
            sR = need - sL
            selL = np.where(sums == sL)[0]
            selR = np.where(sums == sR)[0]
            if len(selL) == 0 or len(selR) == 0: continue
            qL = sq[selL]; qR = sq[selR]
            # keep only entries that can possibly pair under qmax
            okL = selL[qL <= qmax - qR.min()]
            okR = selR[qR <= qmax - qL.min()]
            if len(okL) == 0 or len(okR) == 0: continue
            qLk = torch.tensor(sq[okL], device=dev)
            qRk = torch.tensor(sq[okR], device=dev)
            Lh = L_hat[okL] + base                # fold d0 into left
            Rh = R_hat[okR]
            # block over right side
            BS = max(1, int(2e7 // max(len(okL), 1)))
            for jb in range(0, len(okR), BS):
                Rb = Rh[jb:jb+BS]
                qRb = qRk[jb:jb+BS]
                # mean-cap mask (broadcasted): qL + qR <= qmax
                mq = (qLk[:, None] + qRb[None, :]) <= qmax
                if not mq.any(): continue
                S = Lh[:, None, :] + Rb[None, :, :]
                psd = S.real*S.real + S.imag*S.imag
                mx = psd.max(dim=2).values
                mask = (mx <= 668.5) & mq
                total_pairs_tested += mask.numel()
                if mask.any():
                    ii, jj = torch.nonzero(mask, as_tuple=True)
                    li = torch.tensor(okL, device=dev)[ii]
                    rj = torch.tensor(okR, device=dev)[jj + jb]
                    full = torch.cat([
                        torch.full((len(ii), 1), float(d0), device=dev),
                        sixt[li], sixt[rj]], dim=1)          # (m,13)
                    V = torch.einsum("bu,ruv,bv->br", full, Ct, full).round().to(torch.long)
                    # exact re-check of the max-PSD cap in float64 for safety
                    f64 = full.to(torch.float64)
                    G64 = torch.tensor(Gm, device=dev, dtype=torch.complex128)
                    dh = f64.to(torch.complex128) @ G64
                    psd64 = (dh.real**2 + dh.imag**2).max(dim=1).values
                    keep = psd64 <= 668.000001
                    if keep.any():
                        surv_V.append(V[keep].cpu().numpy().astype(np.int32))
                        surv_meta.append(full[keep].cpu().numpy().astype(np.int8))
    if surv_V:
        V_all = np.concatenate(surv_V); M_all = np.concatenate(surv_meta)
    else:
        V_all = np.zeros((0, R), dtype=np.int32); M_all = np.zeros((0, k), dtype=np.int8)
    print(json.dumps({"survivors": int(len(V_all)),
                      "elapsed_s": round(time.time()-t00, 1)}), flush=True)
    np.savez_compressed("z37_order3_survivors.npz", V=V_all, c=M_all)
    # ---- join: V_i + V_j = -18 (self-join) ----
    rng = np.random.default_rng(17)
    rvec = rng.integers(1, 1 << 62, size=R, dtype=np.int64)
    h = V_all.astype(np.int64) @ rvec
    t = (-18 - V_all.astype(np.int64)) @ rvec
    # planted test: fabricate target from two random rows, must be found
    if len(V_all) >= 2:
        ia, ib = rng.choice(len(V_all), 2, replace=False)
        Splant = V_all[ia].astype(np.int64) + V_all[ib].astype(np.int64)
        tp = (Splant - V_all.astype(np.int64)) @ rvec
        assert np.intersect1d(h, tp).size > 0, "planted join test FAILED"
    common = np.intersect1d(h, t)
    pairs = 0; example = None
    for val in common:
        I = np.where(h == val)[0]; J = np.where(t == val)[0]
        for i in I:
            for j in J:
                if np.array_equal(V_all[i].astype(np.int64) + V_all[j],
                                  -18*np.ones(R, dtype=np.int64)):
                    pairs += 1
                    if example is None:
                        example = (M_all[i].tolist(), M_all[j].tolist())
    print(json.dumps({"z37_order3_layer": "EMPTY_EXHAUSTIVE" if pairs == 0 else "NONEMPTY",
                      "surviving_pairs": pairs, "example": example,
                      "planted_join_test": "PASS",
                      "total_elapsed_s": round(time.time()-t00, 1)}), flush=True)

if __name__ == "__main__":
    main()
