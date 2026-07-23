"""Spectrally weighted population search for cyclic GS(167).

This deliberately uses a different landscape from the usual squared summed-PAF
energy.  Replica groups receive independently tilted shift weights and mixed
L1/L2 penalties, then periodically exchange their best states.  Heavy-tailed
balanced multi-swap proposals let the population cross strict one-swap basins.
Every published state is recomputed with integer arithmetic.
"""
from __future__ import annotations

import argparse
import json
import math
import time
from pathlib import Path

import numpy as np
import torch

N, H = 167, 83


def exact(a: np.ndarray, elapsed: float, proposals: int, cycles: int) -> dict:
    a = np.asarray(a, dtype=np.int8)
    residual = [
        sum(
            sum(int(x[i]) * int(x[(i + d) % N]) for i in range(N))
            for x in a
        )
        for d in range(1, H + 1)
    ]
    return {
        "construction": "cyclic Goethals-Seidel order 167",
        "search": "agent spectral-weight replica exchange with multi-swap proposals",
        "solved": not any(residual),
        "independently_recomputed": True,
        "energy": sum(x * x for x in residual),
        "l1": sum(abs(x) for x in residual),
        "nonzero": sum(x != 0 for x in residual),
        "maxabs": max(map(abs, residual), default=0),
        "row_sums": [int(x.sum()) for x in a],
        "residual": residual,
        "elapsed_s": elapsed,
        "proposals": proposals,
        "cycles": cycles,
        "sequences": a.astype(int).tolist(),
    }


def residual_and_energy(x: torch.Tensor) -> tuple[torch.Tensor, torch.Tensor]:
    f = torch.fft.rfft(x, dim=2)
    ac = torch.fft.irfft((f.real * f.real + f.imag * f.imag).sum(1), n=N, dim=1)
    residual = torch.round(ac[:, 1 : H + 1]).long()
    return residual, (residual * residual).sum(1)


def balanced_swap(x: torch.Tensor, active: int) -> torch.Tensor:
    """Apply one independently sampled row-sum-preserving swap per replica."""
    b = x.shape[0]
    device = x.device
    rows = torch.arange(b, device=device)
    k = torch.randint(active, (b,), device=device)
    p = torch.randint(N, (b,), device=device)
    bad = x[rows, k, p] != 1
    while bool(bad.any()):
        p[bad] = torch.randint(N, (int(bad.sum()),), device=device)
        bad = x[rows, k, p] != 1
    q = torch.randint(N, (b,), device=device)
    bad = x[rows, k, q] != -1
    while bool(bad.any()):
        q[bad] = torch.randint(N, (int(bad.sum()),), device=device)
        bad = x[rows, k, q] != -1
    y = x.clone()
    y[rows, k, p] = -1
    y[rows, k, q] = 1
    return y


def perturb(x: torch.Tensor, swaps: int, active: int) -> torch.Tensor:
    for _ in range(swaps):
        x = balanced_swap(x, active)
    return x


def make_profiles(batch: int, device: torch.device, profile_count: int = 64):
    # Lognormal tilts retain every constraint but give each group a distinct
    # descent direction.  Several groups strongly focus on random 8-20-shift
    # subsets.  Profiles are normalized so temperatures remain comparable.
    w = torch.exp(0.85 * torch.randn(profile_count, H, device=device))
    for j in range(profile_count // 2):
        keep = torch.randperm(H, device=device)[: 8 + j % 13]
        w[j, keep] *= 5.0
    w /= w.mean(1, keepdim=True)
    ids = torch.arange(batch, device=device) % profile_count
    weights = w[ids]
    # L1 coefficients span zero through a value comparable to one residual
    # square; max coefficients make some groups attack the worst shift first.
    alpha_base = torch.tensor([0.0, 1.0, 2.0, 4.0, 8.0, 12.0, 20.0, 32.0], device=device)
    beta_base = torch.tensor([0.0, 0.0, 0.0, 1.0, 2.0, 4.0, 8.0, 16.0], device=device)
    alpha = alpha_base[torch.arange(batch, device=device) % len(alpha_base)]
    beta = beta_base[(torch.arange(batch, device=device) // len(alpha_base)) % len(beta_base)]
    return weights, alpha, beta


def objective(r: torch.Tensor, weights: torch.Tensor, alpha: torch.Tensor, beta: torch.Tensor):
    rf = r.float()
    return (
        (weights * rf.square()).sum(1)
        + alpha * (weights * rf.abs()).sum(1)
        + beta * rf.abs().amax(1).square()
    )


def main() -> None:
    p = argparse.ArgumentParser()
    p.add_argument("input")
    p.add_argument("--seconds", type=float, default=300)
    p.add_argument("--batch", type=int, default=8192)
    p.add_argument("--cycle-steps", type=int, default=1200)
    p.add_argument("--cross-rounds", type=int, default=24)
    p.add_argument("--active", type=int, choices=(1, 2, 3, 4), default=4)
    p.add_argument("--seed", type=int, default=668167)
    p.add_argument("--temp-high", type=float, default=5000.0)
    p.add_argument("--temp-low", type=float, default=0.2)
    p.add_argument("--prefix", default="agent_gspec_weighted")
    q = p.parse_args()
    if not torch.cuda.is_available():
        raise SystemExit("CUDA unavailable")

    torch.manual_seed(q.seed)
    np.random.seed(q.seed & 0xFFFFFFFF)
    device = torch.device("cuda")
    base = np.asarray(json.loads(Path(q.input).read_text(encoding="utf8"))["sequences"], dtype=np.int8)
    if base.shape != (4, N):
        raise ValueError("input must contain four length-167 sequences")
    rows = base.sum(1).astype(int).tolist()
    if sum(z * z for z in rows) != 4 * N:
        raise ValueError("row-sum square identity failed")

    started = time.time()
    best = base.copy()
    report = exact(best, 0.0, 0, 0)
    best_key = (report["energy"], report["l1"], report["nonzero"])
    proposals = 0
    cycles = 0
    print(json.dumps({"event": "seed", "key": best_key, "rows": rows, "batch": q.batch}), flush=True)

    seed_tensor = torch.from_numpy(base).to(device).float()[None].expand(q.batch, -1, -1).clone()
    # Broad Hamming shells, unlike a fixed-radius repair, seed several basins.
    shell = 4 + (torch.arange(q.batch, device=device) % 45)
    x = seed_tensor
    for depth in range(1, int(shell.max()) + 1):
        mask = shell >= depth
        if bool(mask.any()):
            x[mask] = balanced_swap(x[mask], q.active)

    while best_key[0] and time.time() - started < q.seconds:
        cycles += 1
        weights, alpha, beta = make_profiles(q.batch, device)
        r, e = residual_and_energy(x)
        score = objective(r, weights, alpha, beta)
        # Each weighted profile contains a ladder of temperatures.  Population
        # exchange happens at the end of the cycle through elite replication.
        ladder = torch.logspace(math.log10(q.temp_low), math.log10(q.temp_high), q.batch, device=device)
        ladder = ladder[torch.randperm(q.batch, device=device)]

        for step in range(q.cycle_steps):
            if step % 32 == 0 and time.time() - started >= q.seconds:
                break
            roll = int(torch.randint(1000, (1,), device=device))
            arity = 1 if roll < 650 else 2 if roll < 875 else 4 if roll < 970 else 8
            y = x
            for _ in range(arity):
                y = balanced_swap(y, q.active)
            nr, ne = residual_and_energy(y)
            ns = objective(nr, weights, alpha, beta)
            delta = ns - score
            accept = (delta <= 0) | (torch.rand(q.batch, device=device) < torch.exp(-delta / ladder))
            x[accept] = y[accept]
            r[accept] = nr[accept]
            e[accept] = ne[accept]
            score[accept] = ns[accept]
            proposals += q.batch

            cur_e = int(e.min())
            if cur_e <= best_key[0]:
                ids = torch.nonzero(e == cur_e, as_tuple=False).flatten()
                l1s = r[ids].abs().sum(1)
                j = int(ids[int(l1s.argmin())])
                cand = x[j].cpu().numpy().astype(np.int8)
                chk = exact(cand, time.time() - started, proposals, cycles)
                key = (chk["energy"], chk["l1"], chk["nonzero"])
                assert chk["row_sums"] == rows and key[0] == cur_e
                if key < best_key:
                    best, best_key, report = cand, key, chk
                    Path(q.prefix + "_live.json").write_text(json.dumps(chk, separators=(",", ":")) + "\n", encoding="utf8")
                    print(json.dumps({"event": "best", "key": key, "maxabs": chk["maxabs"], "cycle": cycles, "step": step, "proposals": proposals, "elapsed_s": chk["elapsed_s"]}), flush=True)
                    if not key[0]:
                        break

        if not best_key[0]:
            break
        # Cooperative spectral recombination: a row contributes only its own
        # PAF vector, so whole rows can be exchanged without interaction or
        # loss of the row-sum identity.  This is a direct randomized search for
        # four PAF vectors whose sum cancels, not a coordinate crossover.
        for _ in range(q.cross_rounds):
            y = torch.empty_like(x)
            for k in range(4):
                donor = torch.randint(q.batch, (q.batch,), device=device)
                y[:, k] = x[donor, k]
            nr, ne = residual_and_energy(y)
            improve = ne < e
            x[improve] = y[improve]
            r[improve] = nr[improve]
            e[improve] = ne[improve]
            proposals += q.batch
        cur_e = int(e.min())
        if cur_e <= best_key[0]:
            ids = torch.nonzero(e == cur_e, as_tuple=False).flatten()
            l1s = r[ids].abs().sum(1)
            j = int(ids[int(l1s.argmin())])
            cand = x[j].cpu().numpy().astype(np.int8)
            chk = exact(cand, time.time() - started, proposals, cycles)
            key = (chk["energy"], chk["l1"], chk["nonzero"])
            assert chk["row_sums"] == rows and key[0] == cur_e
            if key < best_key:
                best, best_key, report = cand, key, chk
                Path(q.prefix + "_live.json").write_text(json.dumps(chk, separators=(",", ":")) + "\n", encoding="utf8")
                print(json.dumps({"event": "best", "key": key, "maxabs": chk["maxabs"], "cycle": cycles, "stage": "row_recombination", "proposals": proposals, "elapsed_s": chk["elapsed_s"]}), flush=True)
                if not key[0]:
                    break
        if not best_key[0]:
            break
        score = objective(r, weights, alpha, beta)
        # Replica exchange: retain elites under both the canonical energy and
        # the tilted objectives, replicate them, then apply varying reheats.
        elite_n = min(256, q.batch // 4)
        canon_ids = torch.topk(e, elite_n, largest=False).indices
        tilted_ids = torch.topk(score, elite_n, largest=False).indices
        elite_ids = torch.cat((canon_ids, tilted_ids))
        pick = elite_ids[torch.randint(len(elite_ids), (q.batch,), device=device)]
        x = x[pick].clone()
        # Inject the globally best state into one eighth of the population.
        best_gpu = torch.from_numpy(best).to(device).float()
        x[: q.batch // 8] = best_gpu
        depth = torch.arange(q.batch, device=device) % 24
        for d in range(1, 24):
            mask = depth >= d
            if bool(mask.any()):
                x[mask] = balanced_swap(x[mask], q.active)

    out = exact(best, time.time() - started, proposals, cycles)
    name = q.prefix + ("_candidate.json" if out["solved"] else "_summary.json")
    Path(name).write_text(json.dumps(out, separators=(",", ":")) + "\n", encoding="utf8")
    print(json.dumps({"event": "result", "solved": out["solved"], "key": (out["energy"], out["l1"], out["nonzero"]), "maxabs": out["maxabs"], "cycles": cycles, "proposals": proposals, "output": name}), flush=True)


if __name__ == "__main__":
    main()
