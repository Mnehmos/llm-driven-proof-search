"""Fourier/Douglas--Rachford alternating projections for cyclic GS(167)."""
from __future__ import annotations

import argparse
import json
import math
import time
from pathlib import Path

import numpy as np
import torch

N, H = 167, 83


def exact(a: np.ndarray, elapsed: float, projections: int, restarts: int) -> dict:
    a = np.asarray(a, dtype=np.int8)
    r = [sum(sum(int(x[i]) * int(x[(i + d) % N]) for i in range(N)) for x in a) for d in range(1, H + 1)]
    return {
        "construction": "cyclic Goethals-Seidel order 167",
        "search": "agent Fourier Douglas-Rachford alternating projection",
        "solved": not any(r),
        "independently_recomputed": True,
        "energy": sum(z * z for z in r),
        "l1": sum(abs(z) for z in r),
        "nonzero": sum(z != 0 for z in r),
        "maxabs": max(map(abs, r), default=0),
        "row_sums": [int(x.sum()) for x in a],
        "residual": r,
        "elapsed_s": elapsed,
        "projections": projections,
        "restarts": restarts,
        "sequences": a.astype(int).tolist(),
    }


def binary_project(z: torch.Tensor, counts: list[int]) -> torch.Tensor:
    out = torch.full_like(z, -1.0)
    for k, count in enumerate(counts):
        ids = z[:, k].topk(count, dim=1).indices
        out[:, k].scatter_(1, ids, 1.0)
    return out


def spectral_project(z: torch.Tensor, row_sums: torch.Tensor) -> torch.Tensor:
    f = torch.fft.fft(z, dim=2)
    norm2 = (f.real.square() + f.imag.square()).sum(1, keepdim=True).clamp_min(1e-12)
    f = f * torch.sqrt(torch.tensor(float(4 * N), device=z.device) / norm2)
    # The zero-frequency vector is fixed componentwise by the chosen row-sum
    # fibre, whose squared norm is already 668.
    f[:, :, 0] = row_sums
    return torch.fft.ifft(f, dim=2).real


def discrete_metrics(x: torch.Tensor):
    f = torch.fft.rfft(x, dim=2)
    ac = torch.fft.irfft((f.real.square() + f.imag.square()).sum(1), n=N, dim=1)
    r = torch.round(ac[:, 1 : H + 1]).long()
    return r, (r * r).sum(1), r.abs().sum(1)


def balanced_perturb(x: torch.Tensor, swaps: int) -> torch.Tensor:
    b = x.shape[0]
    dev = x.device
    ids = torch.arange(b, device=dev)
    for _ in range(swaps):
        k = torch.randint(4, (b,), device=dev)
        p = torch.randint(N, (b,), device=dev)
        bad = x[ids, k, p] != 1
        while bool(bad.any()):
            p[bad] = torch.randint(N, (int(bad.sum()),), device=dev)
            bad = x[ids, k, p] != 1
        q = torch.randint(N, (b,), device=dev)
        bad = x[ids, k, q] != -1
        while bool(bad.any()):
            q[bad] = torch.randint(N, (int(bad.sum()),), device=dev)
            bad = x[ids, k, q] != -1
        x[ids, k, p] = -1
        x[ids, k, q] = 1
    return x


def main() -> None:
    p = argparse.ArgumentParser()
    p.add_argument("input")
    p.add_argument("--seconds", type=float, default=300)
    p.add_argument("--batch", type=int, default=2048)
    p.add_argument("--steps", type=int, default=1000)
    p.add_argument("--beta", type=float, default=0.85)
    p.add_argument("--noise", type=float, default=0.35)
    p.add_argument("--seed", type=int, default=668167)
    p.add_argument("--prefix", default="agent_gspec_altproj")
    q = p.parse_args()
    if not torch.cuda.is_available():
        raise SystemExit("CUDA unavailable")
    torch.manual_seed(q.seed)
    dev = torch.device("cuda")
    base = np.asarray(json.loads(Path(q.input).read_text(encoding="utf8"))["sequences"], dtype=np.int8)
    if base.shape != (4, N):
        raise ValueError("expected four length-167 rows")
    rows = base.sum(1).astype(int).tolist()
    if sum(z * z for z in rows) != 4 * N:
        raise ValueError("row-sum square identity failed")
    counts = [(N + z) // 2 for z in rows]
    row_tensor = torch.tensor(rows, device=dev, dtype=torch.complex64)[None, :]
    base_t = torch.from_numpy(base).to(dev).float()

    started = time.time()
    best = base.copy()
    report = exact(best, 0.0, 0, 0)
    best_key = (report["energy"], report["l1"], report["nonzero"])
    projections = 0
    restarts = 0
    print(json.dumps({"event": "seed", "key": best_key, "rows": rows, "batch": q.batch}), flush=True)

    while best_key[0] and time.time() - started < q.seconds:
        restarts += 1
        seed = torch.from_numpy(best).to(dev).float()[None].expand(q.batch, -1, -1).clone()
        seed = balanced_perturb(seed, 3 + restarts % 29)
        z = seed + q.noise * torch.randn_like(seed)
        # Half use plain alternating projections, half use DR reflections.
        split = q.batch // 2
        for step in range(q.steps):
            if step % 16 == 0 and time.time() - started >= q.seconds:
                break
            bproj = spectral_project(z, row_tensor)
            reflected = binary_project(2.0 * bproj - z, counts)
            z[:split] = binary_project(bproj[:split], counts)
            z[split:] += q.beta * (reflected[split:] - bproj[split:])
            projections += q.batch
            if step % 5:
                continue
            disc = binary_project(z, counts)
            r, e, l1 = discrete_metrics(disc)
            cur_e = int(e.min())
            if cur_e <= best_key[0]:
                ids = torch.nonzero(e == cur_e, as_tuple=False).flatten()
                j = int(ids[int(l1[ids].argmin())])
                cand = disc[j].cpu().numpy().astype(np.int8)
                chk = exact(cand, time.time() - started, projections, restarts)
                key = (chk["energy"], chk["l1"], chk["nonzero"])
                assert chk["row_sums"] == rows and key[0] == cur_e
                if key < best_key:
                    best, best_key, report = cand, key, chk
                    Path(q.prefix + "_live.json").write_text(json.dumps(chk, separators=(",", ":")) + "\n", encoding="utf8")
                    print(json.dumps({"event": "best", "key": key, "maxabs": chk["maxabs"], "restart": restarts, "step": step, "projections": projections, "elapsed_s": chk["elapsed_s"]}), flush=True)
                    if not key[0]:
                        break

    out = exact(best, time.time() - started, projections, restarts)
    name = q.prefix + ("_candidate.json" if out["solved"] else "_summary.json")
    Path(name).write_text(json.dumps(out, separators=(",", ":")) + "\n", encoding="utf8")
    print(json.dumps({"event": "result", "solved": out["solved"], "key": (out["energy"], out["l1"], out["nonzero"]), "maxabs": out["maxabs"], "projections": projections, "restarts": restarts, "output": name}), flush=True)


if __name__ == "__main__":
    main()
