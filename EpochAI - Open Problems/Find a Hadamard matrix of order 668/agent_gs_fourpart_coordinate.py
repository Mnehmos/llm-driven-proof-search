"""GPU best-response search over four row-separated balanced swaps.

For a fixed cyclic GS center, choose zero or one balanced swap independently in
each of its four rows.  The resulting 83-dimensional PAF defect is exactly

    r + D0[i0] + D1[i1] + D2[i2] + D3[i3].

Thousands of random starts are optimized in parallel by exact categorical
best responses: holding three row choices fixed, scan *every* balanced swap in
the fourth row.  A strict improvement is then used as a new center, allowing
the bounded four-part neighborhood to be chained without approximating scores.
"""
from __future__ import annotations

import argparse
import json
import time
from pathlib import Path

import numpy as np
import torch

from agent_gs_crossrow_mitm import (
    H,
    N,
    apply_move,
    enumerate_balanced_swaps,
    exact_report,
)


@torch.no_grad()
def best_response_round(
    center: np.ndarray,
    batch: int,
    sweeps: int,
    candidate_block: int,
    seed: int,
    device: torch.device,
) -> tuple[np.ndarray, dict]:
    report = exact_report(center)
    r = torch.tensor(np.asarray(report["residual"], dtype=np.float32) / 4.0, device=device)
    data = [enumerate_balanced_swaps(row, include_zero=True) for row in center]
    moves = [item[0] for item in data]
    d = [torch.tensor(item[1].astype(np.float32), device=device) for item in data]
    dn = [(x * x).sum(dim=1) for x in d]

    generator = torch.Generator(device=device)
    generator.manual_seed(seed)
    choice = [torch.randint(len(moves[k]), (batch,), device=device, generator=generator) for k in range(4)]
    # Keep one trajectory at the center as an exact non-regression sentinel.
    for k in range(4):
        choice[k][0] = 0
    total = sum((d[k][choice[k]] for k in range(4)), torch.zeros((batch, H), device=device))
    evaluated = 0
    best_energy4 = int(((r + total) ** 2).sum(dim=1).min().item())
    best_choices = None
    sweeps_done = 0

    for sweep in range(sweeps):
        changed = False
        # Rotate the update order between restarts to avoid a fixed row bias.
        order = [(seed + sweep + j) % 4 for j in range(4)]
        for row in order:
            old = d[row][choice[row]]
            q = r[None, :] + total - old
            qn = (q * q).sum(dim=1)
            best_values = torch.full((batch,), float("inf"), device=device)
            best_indices = torch.zeros((batch,), dtype=torch.long, device=device)
            for lo in range(0, len(moves[row]), candidate_block):
                hi = min(len(moves[row]), lo + candidate_block)
                scores = qn[:, None] + dn[row][lo:hi][None, :] + 2.0 * (q @ d[row][lo:hi].T)
                values, indices = scores.min(dim=1)
                improve = values < best_values
                best_values[improve] = values[improve]
                best_indices[improve] = lo + indices[improve]
                evaluated += int(scores.numel())
            new = best_indices
            if bool((new != choice[row]).any()):
                changed = True
            total += d[row][new] - old
            choice[row] = new

        sweeps_done += 1
        energies = ((r[None, :] + total) ** 2).sum(dim=1)
        value, at = energies.min(dim=0)
        value_i = int(round(float(value.item())))
        if value_i < best_energy4 or best_choices is None:
            best_energy4 = value_i
            idx = int(at.item())
            best_choices = np.asarray([int(choice[k][idx].item()) for k in range(4)], dtype=np.int32)
        if not changed:
            break

    assert best_choices is not None
    candidate = center.copy()
    selected_moves = []
    for row, idx in enumerate(best_choices):
        move = moves[row][idx]
        apply_move(candidate, row, move)
        selected_moves.append(move.astype(int).tolist())
    direct = exact_report(candidate)
    if direct["energy"] != 16 * best_energy4:
        raise AssertionError(f"best-response score drift: GPU={16 * best_energy4}, exact={direct['energy']}")
    return candidate, {
        "energy": direct["energy"],
        "l1": direct["l1"],
        "nonzero": direct["nonzero"],
        "maxabs": direct["maxabs"],
        "selected_indices": best_choices.astype(int).tolist(),
        "selected_moves": selected_moves,
        "sweeps": sweeps_done,
        "states": batch,
        "categorical_scores_evaluated": int(evaluated),
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("--seconds", type=float, default=180)
    parser.add_argument("--batch", type=int, default=2048)
    parser.add_argument("--sweeps", type=int, default=8)
    parser.add_argument("--candidate-block", type=int, default=1024)
    parser.add_argument("--seed", type=int, default=66820260722)
    parser.add_argument("--output-prefix", default="agent_gs_fourpart")
    args = parser.parse_args()
    if not torch.cuda.is_available():
        raise SystemExit("CUDA is required")

    payload = json.loads(args.input.read_text(encoding="utf-8"))
    center = np.asarray(payload["sequences"], dtype=np.int8)
    if center.shape != (4, N) or np.any(np.abs(center) != 1):
        raise ValueError("expected four length-167 sign sequences")
    initial = exact_report(center)
    rows = initial["row_sums"]
    if sum(x * x for x in rows) != 4 * N:
        raise ValueError("GS row-sum square identity failed")

    device = torch.device("cuda")
    started = time.time()
    deadline = started + args.seconds
    best = center.copy()
    best_report = initial
    history = []
    restart = 0
    total_scores = 0
    print(json.dumps({"event": "seed", "energy": initial["energy"], "l1": initial["l1"], "rows": rows}), flush=True)

    while time.time() < deadline and not best_report["solved"]:
        candidate, stats = best_response_round(
            center,
            batch=args.batch,
            sweeps=args.sweeps,
            candidate_block=args.candidate_block,
            seed=args.seed + restart,
            device=device,
        )
        restart += 1
        total_scores += stats["categorical_scores_evaluated"]
        item = {"restart": restart, "center_energy": exact_report(center)["energy"], **stats}
        history.append(item)
        if stats["energy"] < best_report["energy"]:
            best = candidate.copy()
            best_report = exact_report(best)
            best_report["elapsed_s"] = time.time() - started
            best_report["history"] = history
            best_report["categorical_scores_evaluated"] = int(total_scores)
            Path(args.output_prefix + "_live.json").write_text(
                json.dumps(best_report, separators=(",", ":")) + "\n", encoding="utf-8"
            )
            print(json.dumps({"event": "best", **item, "elapsed_s": time.time() - started}, separators=(",", ":")), flush=True)
            # Recenter only on a strict global improvement.  This chains exact
            # one-swap-per-row neighborhoods while preserving row signatures.
            center = best.copy()
            if best_report["row_sums"] != rows:
                raise AssertionError("row signature drift")
        elif restart <= 3 or restart % 10 == 0:
            print(json.dumps({"event": "restart", **item, "elapsed_s": time.time() - started}, separators=(",", ":")), flush=True)

    final = exact_report(best)
    final.update(
        source=str(args.input),
        initial_energy=initial["energy"],
        restarts=restart,
        categorical_scores_evaluated=int(total_scores),
        elapsed_s=time.time() - started,
        history=history,
    )
    output = Path(args.output_prefix + ("_candidate.json" if final["solved"] else "_summary.json"))
    output.write_text(json.dumps(final, separators=(",", ":")) + "\n", encoding="utf-8")
    print(json.dumps({"event": "result", "solved": final["solved"], "energy": final["energy"], "restarts": restart, "scores": total_scores, "elapsed_s": final["elapsed_s"], "output": str(output)}), flush=True)
    return 0 if final["solved"] else 2


if __name__ == "__main__":
    raise SystemExit(main())
