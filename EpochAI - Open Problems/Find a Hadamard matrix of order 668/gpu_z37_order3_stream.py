"""Chunked GPU exhaustion of the shared Z_37 layer of the order-3 multiplier
subgroups <10>, <121>, <211> (image {1,10,26} on Z_37).

Space: 13 orbit values (1 fixed + 12 three-orbits) over the 10 odd values
[-9,9]; sum condition d0 + 3*sum(rest) = 1 (so d0 in {-5,1,7}); rigorous
PSD cap: PSD_a(k) <= 668 for every k != 0 (since PSD_a + PSD_b = 668 exactly
and PSD_b >= 0 - the compressed PSD identity, frequency-subsampling of the
LP condition). Survivors (indices + exact integer PAF vectors over the 12
shift representatives) are checkpointed to disk per super-chunk; the final
join scans V_i + V_j = -18. Complete decision, resumable, foreground-sized
chunks (--from-chunk/--n-chunks).
"""
import argparse, json, time
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
    sizes = [len(o) for o in orbs]
    sseen = set(); reps = []
    for d in range(1, P):
        if d in sseen: continue
        sseen.update({(d*g) % P for g in IMG}); reps.append(d)
    C = np.zeros((len(reps), len(orbs), len(orbs)), dtype=np.int64)
    for ri, d in enumerate(reps):
        for i in range(P):
            C[ri, own[i], own[(i+d) % P]] += 1
    return orbs, own, sizes, reps, C

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--from-chunk", type=int, default=0)
    ap.add_argument("--n-chunks", type=int, default=200)
    ap.add_argument("--chunk-bits", type=int, default=26)
    ap.add_argument("--outdir", default="z37_order3_stream")
    a = ap.parse_args()
    from pathlib import Path
    outdir = Path(a.outdir); outdir.mkdir(exist_ok=True)
    orbs, own, sizes, reps, C = structure()
    k = len(orbs)          # 13
    R = len(reps)          # 12
    dev = "cuda"
    ALPH = torch.arange(-9, 10, 2, device=dev, dtype=torch.long)   # 10 values
    D0S = torch.tensor([-5, 1, 7], device=dev, dtype=torch.long)
    # DFT magnitudes for PSD: orbit-character matrix G (13 x 36) complex
    Gm = np.zeros((k, P-1), dtype=np.complex128)
    for j, o in enumerate(orbs):
        for kk in range(1, P):
            Gm[j, kk-1] = sum(np.exp(-2j*np.pi*kk*x/P) for x in o)
    Gre = torch.tensor(Gm.real, device=dev, dtype=torch.float64)
    Gim = torch.tensor(Gm.imag, device=dev, dtype=torch.float64)
    Ct = torch.tensor(C, device=dev, dtype=torch.float64)
    pows = torch.tensor([10**i for i in range(12)], device=dev, dtype=torch.long)
    chunk = 1 << a.chunk_bits
    total_rest = 10**12
    n_chunks_total = (total_rest + chunk - 1)//chunk
    t0 = time.time()
    for ci in range(a.from_chunk, min(a.from_chunk + a.n_chunks, n_chunks_total)):
        fout = outdir / f"chunk_{ci:07d}.npz"
        if fout.exists(): continue
        start = ci * chunk
        n = min(chunk, total_rest - start)
        ints = torch.arange(start, start+n, device=dev, dtype=torch.long)
        D = (ints[:, None] // pows[None, :]) % 10          # (n,12)
        vals = ALPH[D]                                      # rest values
        s = vals.sum(1)
        keep_idx = []; keep_v = []; keep_d0 = []
        for d0i, d0 in enumerate((-5, 1, 7)):
            need = (1 - d0)//3
            m = s == need
            if not m.any(): continue
            vm = vals[m]
            full = torch.cat([torch.full((vm.shape[0], 1), d0, device=dev,
                                         dtype=torch.long), vm], dim=1)
            f = full.to(torch.float64)
            re = f @ Gre; im = f @ Gim
            psd = re*re + im*im
            ok = psd.max(dim=1).values <= 668.0001
            if not ok.any(): continue
            fo = f[ok]
            # exact PAF vectors
            V = torch.einsum("bu,ruv,bv->br", fo, Ct, fo).round().to(torch.long)
            keep_idx.append(ints[m][ok] )
            keep_v.append(V)
            keep_d0.append(torch.full((int(ok.sum()),), d0, device=dev,
                                      dtype=torch.long))
        if keep_idx:
            np.savez_compressed(fout,
                idx=torch.cat(keep_idx).cpu().numpy(),
                d0=torch.cat(keep_d0).cpu().numpy().astype(np.int8),
                V=torch.cat(keep_v).cpu().numpy().astype(np.int32))
        else:
            np.savez_compressed(fout, idx=np.array([], dtype=np.int64),
                                d0=np.array([], dtype=np.int8),
                                V=np.zeros((0, R), dtype=np.int32))
    done = a.from_chunk + a.n_chunks
    print(json.dumps({"chunks_done_through": min(done, n_chunks_total),
                      "total_chunks": n_chunks_total,
                      "elapsed_s": round(time.time()-t0, 1)}), flush=True)

if __name__ == "__main__":
    main()
