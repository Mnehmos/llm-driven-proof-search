"""GPU batched exact-row-sum perturbation search for cyclic GS(167)."""
import argparse, json, time
from pathlib import Path

import numpy as np
import torch

N, H = 167, 83


def exact(a, elapsed, samples):
    a = np.asarray(a, dtype=np.int8)
    residual = [sum(int(np.dot(x.astype(np.int32), np.roll(x, -d).astype(np.int32))) for x in a)
                for d in range(1, H + 1)]
    rows = [int(x.sum()) for x in a]
    return {
        "construction": "cyclic Goethals-Seidel order 167",
        "search": "GPU batched exact-row-sum perturbations",
        "solved": not any(residual),
        "energy": sum(x*x for x in residual),
        "l1": sum(map(abs, residual)),
        "nonzero": sum(x != 0 for x in residual),
        "maxabs": max(map(abs, residual)),
        "row_sums": rows,
        "residual": residual,
        "elapsed_s": elapsed,
        "samples": samples,
        "sequences": a.astype(int).tolist(),
    }


def main():
    p = argparse.ArgumentParser()
    p.add_argument("input", type=Path)
    p.add_argument("--seconds", type=float, default=300)
    p.add_argument("--batch", type=int, default=32768)
    p.add_argument("--max-swaps", type=int, default=8)
    p.add_argument("--active", type=int, default=4, choices=(1,2,3,4))
    p.add_argument("--samples", type=int, default=50_000_000)
    p.add_argument("--seed", type=int, default=668167)
    p.add_argument("--prefix", default="gs_167_gpu")
    q = p.parse_args()
    if not torch.cuda.is_available():
        raise SystemExit("CUDA unavailable")
    torch.manual_seed(q.seed)
    dev = torch.device("cuda")
    data = json.loads(q.input.read_text(encoding="utf8"))
    best = np.asarray(data["sequences"], dtype=np.int8)
    if best.shape != (4, N) or np.any(np.abs(best) != 1):
        raise ValueError("expected four length-167 sign sequences")
    initial_rows = best.sum(axis=1).tolist()
    if sum(x*x for x in initial_rows) != 4*N:
        raise ValueError("GS row-sum square identity failed")
    start = time.time(); samples = 0
    report = exact(best, 0, 0); best_e = report["energy"]
    print(json.dumps({"event": "seed", "energy": best_e, "l1": report["l1"], "rows": initial_rows}), flush=True)
    while best_e and time.time() - start < q.seconds and samples < q.samples:
        k = 1 + int(torch.randint(q.max_swaps, (1,), device=dev))
        # Each child modifies a nonempty random subset of the four sequences.
        active = torch.randint(2, (q.batch, 4), device=dev, dtype=torch.bool)
        active[:, q.active:] = False
        empty = ~active.any(dim=1)
        active[empty, torch.randint(q.active, (int(empty.sum()),), device=dev)] = True
        x = torch.from_numpy(best).to(dev).float().expand(q.batch, -1, -1).clone()
        for s in range(4):
            plus = torch.tensor(np.flatnonzero(best[s] == 1), device=dev)
            minus = torch.tensor(np.flatnonzero(best[s] == -1), device=dev)
            kk = min(k, len(plus), len(minus))
            rp = torch.rand((q.batch, len(plus)), device=dev).topk(kk, dim=1).indices
            rm = torch.rand((q.batch, len(minus)), device=dev).topk(kk, dim=1).indices
            chosen_p = plus[rp]; chosen_m = minus[rm]
            rows = torch.arange(q.batch, device=dev)[:, None].expand(-1, kk)
            mask = active[:, s][:, None].expand(-1, kk)
            x[rows[mask], s, chosen_p[mask]] = -1
            x[rows[mask], s, chosen_m[mask]] = 1
        f = torch.fft.rfft(x, dim=2)
        ac = torch.fft.irfft((f.real*f.real + f.imag*f.imag).sum(dim=1), n=N, dim=1)
        residual = torch.round(ac[:, 1:H+1]).long()
        energy = (residual*residual).sum(dim=1)
        samples += q.batch
        cur = int(energy.min())
        if cur < best_e:
            j = int(energy.argmin())
            candidate = x[j].cpu().numpy().astype(np.int8)
            check = exact(candidate, time.time()-start, samples)
            assert check["energy"] == cur and check["row_sums"] == initial_rows
            best, best_e, report = candidate, cur, check
            Path(q.prefix + "_live.json").write_text(json.dumps(check, separators=(",", ":")) + "\n", encoding="utf8")
            print(json.dumps({"event": "best", "energy": cur, "l1": check["l1"], "nonzero": check["nonzero"],
                              "maxabs": check["maxabs"], "swaps_per_active_sequence": k,
                              "samples": samples, "elapsed_s": check["elapsed_s"]}), flush=True)
    out = exact(best, time.time()-start, samples)
    name = q.prefix + ("_candidate.json" if out["solved"] else "_summary.json")
    Path(name).write_text(json.dumps(out, separators=(",", ":")) + "\n", encoding="utf8")
    print(json.dumps({"event": "result", "solved": out["solved"], "energy": out["energy"],
                      "samples": samples, "output": name}), flush=True)


if __name__ == "__main__":
    main()
