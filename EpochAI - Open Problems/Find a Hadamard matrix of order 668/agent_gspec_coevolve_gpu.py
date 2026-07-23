"""Cooperative row-pool evolution for a cyclic GS(167) family.

The four periodic autocorrelation vectors add without cross terms.  This search
therefore evolves four independent sequence pools and repeatedly matches rows
drawn from different parents, instead of evolving only linked 4-row states.
"""
from __future__ import annotations

import argparse
import json
import time
from pathlib import Path

import numpy as np
import torch

N, H = 167, 83


def exact(a: np.ndarray, elapsed: float, combinations: int, generations: int) -> dict:
    a = np.asarray(a, dtype=np.int8)
    r = [
        sum(sum(int(x[i]) * int(x[(i + d) % N]) for i in range(N)) for x in a)
        for d in range(1, H + 1)
    ]
    return {
        "construction": "cyclic Goethals-Seidel order 167",
        "search": "agent cooperative independent-row spectral pools",
        "solved": not any(r),
        "independently_recomputed": True,
        "energy": sum(z * z for z in r),
        "l1": sum(abs(z) for z in r),
        "nonzero": sum(z != 0 for z in r),
        "maxabs": max(map(abs, r), default=0),
        "row_sums": [int(x.sum()) for x in a],
        "residual": r,
        "elapsed_s": elapsed,
        "combinations": combinations,
        "generations": generations,
        "sequences": a.astype(int).tolist(),
    }


def evaluate(x: torch.Tensor):
    f = torch.fft.rfft(x, dim=2)
    ac = torch.fft.irfft((f.real.square() + f.imag.square()).sum(1), n=N, dim=1)
    r = torch.round(ac[:, 1 : H + 1]).long()
    return r, (r * r).sum(1), r.abs().sum(1)


def swap_rows(x: torch.Tensor) -> torch.Tensor:
    """One balanced swap in every row object in a [pool,N] tensor."""
    b = x.shape[0]
    dev = x.device
    ids = torch.arange(b, device=dev)
    p = torch.randint(N, (b,), device=dev)
    bad = x[ids, p] != 1
    while bool(bad.any()):
        p[bad] = torch.randint(N, (int(bad.sum()),), device=dev)
        bad = x[ids, p] != 1
    q = torch.randint(N, (b,), device=dev)
    bad = x[ids, q] != -1
    while bool(bad.any()):
        q[bad] = torch.randint(N, (int(bad.sum()),), device=dev)
        bad = x[ids, q] != -1
    y = x.clone()
    y[ids, p] = -1
    y[ids, q] = 1
    return y


def main() -> None:
    p = argparse.ArgumentParser()
    p.add_argument("input")
    p.add_argument("--seconds", type=float, default=300)
    p.add_argument("--pool", type=int, default=8192)
    p.add_argument("--batch", type=int, default=32768)
    p.add_argument("--batches", type=int, default=8)
    p.add_argument("--elite", type=int, default=512)
    p.add_argument("--active", type=int, choices=(1, 2, 3, 4), default=4)
    p.add_argument("--seed", type=int, default=668167)
    p.add_argument("--prefix", default="agent_gspec_coevolve")
    q = p.parse_args()
    if not torch.cuda.is_available():
        raise SystemExit("CUDA unavailable")
    if q.elite > q.pool or q.elite > q.batch:
        raise ValueError("elite must not exceed pool or batch")

    torch.manual_seed(q.seed)
    dev = torch.device("cuda")
    base = np.asarray(json.loads(Path(q.input).read_text(encoding="utf8"))["sequences"], dtype=np.int8)
    if base.shape != (4, N):
        raise ValueError("expected four length-167 sequences")
    rows = base.sum(1).astype(int).tolist()
    if sum(x * x for x in rows) != 4 * N:
        raise ValueError("row-sum square identity failed")

    started = time.time()
    best = base.copy()
    rep = exact(best, 0.0, 0, 0)
    best_key = (rep["energy"], rep["l1"], rep["nonzero"])
    combinations = 0
    generations = 0
    print(json.dumps({"event": "seed", "key": best_key, "rows": rows}), flush=True)

    base_t = torch.from_numpy(base).to(dev).float()
    pools = base_t[:, None, :].expand(-1, q.pool, -1).clone()
    # Populate independent Hamming shells while retaining the exact seed row.
    depth = torch.arange(q.pool, device=dev) % 32
    for d in range(1, 32):
        mask = depth >= d
        for k in range(q.active):
            pools[k, mask] = swap_rows(pools[k, mask])

    while best_key[0] and time.time() - started < q.seconds:
        generations += 1
        contenders = []
        for batch_no in range(q.batches):
            x = torch.empty((q.batch, 4, N), device=dev)
            for k in range(q.active):
                ids = torch.randint(q.pool, (q.batch,), device=dev)
                x[:, k] = pools[k, ids]
            for k in range(q.active, 4):
                x[:, k] = base_t[k]
            if batch_no == 0:
                x[0] = base_t
                x[1] = torch.from_numpy(best).to(dev).float()
            r, e, l1 = evaluate(x)
            combinations += q.batch
            # Preserve elites under E, L1, and a mixed sparsity surrogate.
            take_e = torch.topk(e, q.elite // 2, largest=False).indices
            take_l = torch.topk(l1, q.elite // 4, largest=False).indices
            mixed = e + 8 * l1 + 32 * (r != 0).sum(1)
            take_m = torch.topk(mixed, q.elite - len(take_e) - len(take_l), largest=False).indices
            contenders.append(x[torch.cat((take_e, take_l, take_m))])

            cur_e = int(e.min())
            if cur_e <= best_key[0]:
                ids = torch.nonzero(e == cur_e, as_tuple=False).flatten()
                jj = int(ids[int(l1[ids].argmin())])
                cand = x[jj].cpu().numpy().astype(np.int8)
                chk = exact(cand, time.time() - started, combinations, generations)
                key = (chk["energy"], chk["l1"], chk["nonzero"])
                assert chk["row_sums"] == rows and key[0] == cur_e
                if key < best_key:
                    best, best_key, rep = cand, key, chk
                    Path(q.prefix + "_live.json").write_text(json.dumps(chk, separators=(",", ":")) + "\n", encoding="utf8")
                    print(json.dumps({"event": "best", "key": key, "maxabs": chk["maxabs"], "generation": generations, "batch": batch_no, "combinations": combinations, "elapsed_s": chk["elapsed_s"]}), flush=True)
                    if not key[0]:
                        break
        if not best_key[0]:
            break

        elite_states = torch.cat(contenders)
        _, ee, ll = evaluate(elite_states)
        order = torch.argsort(ee + 2 * ll)[: q.elite]
        elite_states = elite_states[order]
        # Rebuild each row pool independently from rows occurring in good
        # contexts.  The first elite block is unmutated; the remainder uses a
        # heavy-tailed 1..24-swap mutation depth.
        for k in range(q.active):
            parent = elite_states[torch.randint(q.elite, (q.pool,), device=dev), k].clone()
            parent[: q.elite] = elite_states[:, k]
            parent[0] = torch.from_numpy(best[k]).to(dev).float()
            depth = 1 + (torch.arange(q.pool, device=dev) % 24)
            depth[: q.elite] = 0
            for d in range(1, 25):
                mask = depth >= d
                if bool(mask.any()):
                    parent[mask] = swap_rows(parent[mask])
            pools[k] = parent

    out = exact(best, time.time() - started, combinations, generations)
    name = q.prefix + ("_candidate.json" if out["solved"] else "_summary.json")
    Path(name).write_text(json.dumps(out, separators=(",", ":")) + "\n", encoding="utf8")
    print(json.dumps({"event": "result", "solved": out["solved"], "key": (out["energy"], out["l1"], out["nonzero"]), "maxabs": out["maxabs"], "generations": generations, "combinations": combinations, "output": name}), flush=True)


if __name__ == "__main__":
    main()
