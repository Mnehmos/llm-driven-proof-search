"""Row-factorized bounded repair of a cyclic GS(167) checkpoint.

This attack uses a property which is lost in a generic bit-level model: periodic
autocorrelation changes in distinct GS rows add without interaction.  It does
two things.

1. Exhaust all pairs consisting of one balanced swap in each of two distinct
   rows, and repeatedly take a strict steepest descent step.
2. Hash all sums of one (optional) balanced swap in rows 0/1 and rows 2/3.
   A sorted meet-in-the-middle join then decides the complete neighborhood with
   at most one balanced swap per row.  Hash hits are always checked against all
   83 exact integer autocorrelation equations, so hashing cannot create a false
   witness (and an exact solution cannot be missed by the hash filter).

All reported scores are independently recomputed from the modified sign rows.
"""
from __future__ import annotations

import argparse
import gc
import json
import time
from pathlib import Path

import numpy as np
import torch


N = 167
H = 83


def exact_report(a: np.ndarray) -> dict:
    a = np.asarray(a, dtype=np.int8)
    residual = []
    for d in range(1, H + 1):
        value = 0
        for row in a:
            x = row.astype(np.int32, copy=False)
            value += int(x @ np.roll(x, -d))
        residual.append(value)
    return {
        "construction": "cyclic Goethals-Seidel order 167",
        "search": "agent row-factorized cross-pair plus exact MITM",
        "solved": not any(residual),
        "energy": int(sum(x * x for x in residual)),
        "l1": int(sum(abs(x) for x in residual)),
        "nonzero": int(sum(x != 0 for x in residual)),
        "maxabs": int(max(map(abs, residual))),
        "row_sums": [int(row.sum()) for row in a],
        "residual": residual,
        "sequences": a.astype(int).tolist(),
    }


def row_corr(row: np.ndarray) -> np.ndarray:
    x = np.asarray(row, dtype=np.int32)
    return np.asarray([int(x @ np.roll(x, -d)) for d in range(1, H + 1)], dtype=np.int16)


def enumerate_balanced_swaps(row: np.ndarray, include_zero: bool = False) -> tuple[np.ndarray, np.ndarray]:
    """Return (plus_index, minus_index) moves and exact PAF deltas divided by 4."""
    row = np.asarray(row, dtype=np.int8)
    plus = np.flatnonzero(row == 1).astype(np.int16)
    minus = np.flatnonzero(row == -1).astype(np.int16)
    p = np.repeat(plus, len(minus))
    q = np.tile(minus, len(plus))
    moves = np.column_stack((p, q)).astype(np.int16, copy=False)
    deltas = np.empty((len(moves), H), dtype=np.int8)
    pi = p.astype(np.int32)
    qi = q.astype(np.int32)
    gap0 = (qi - pi) % N
    gap = np.minimum(gap0, N - gap0)
    for col, d in enumerate(range(1, H + 1)):
        # p currently contains +1 and q contains -1.
        dr = (
            -2 * (row[(pi + d) % N].astype(np.int16) + row[(pi - d) % N].astype(np.int16))
            + 2 * (row[(qi + d) % N].astype(np.int16) + row[(qi - d) % N].astype(np.int16))
            - 4 * (gap == d).astype(np.int16)
        )
        if np.any(dr % 4):
            raise AssertionError("balanced-swap PAF delta is not divisible by four")
        deltas[:, col] = (dr // 4).astype(np.int8)

    # Self-test the closed form against direct cyclic correlations.
    base = row_corr(row)
    probes = np.linspace(0, len(moves) - 1, num=min(7, len(moves)), dtype=int)
    for idx in probes:
        changed = row.copy()
        changed[moves[idx]] *= -1
        direct = (row_corr(changed).astype(np.int16) - base.astype(np.int16)) // 4
        if not np.array_equal(direct.astype(np.int8), deltas[idx]):
            raise AssertionError(f"delta self-test failed at move {idx}")

    if include_zero:
        moves = np.vstack((np.asarray([[-1, -1]], dtype=np.int16), moves))
        deltas = np.vstack((np.zeros((1, H), dtype=np.int8), deltas))
    return moves, deltas


def apply_move(a: np.ndarray, row: int, move: np.ndarray) -> None:
    p, q = map(int, move)
    if p >= 0:
        if a[row, p] != 1 or a[row, q] != -1:
            raise AssertionError("move endpoints do not have the expected signs")
        a[row, p] = -1
        a[row, q] = 1


def exhaustive_best_cross_pair(a: np.ndarray, block: int, device: torch.device, keep: int = 64) -> tuple[list[dict], int]:
    """Exhaust every one-swap/one-swap move in every distinct pair of rows."""
    report = exact_report(a)
    if any(x % 4 for x in report["residual"]):
        raise AssertionError("GS residuals must be divisible by four")
    r = np.asarray(report["residual"], dtype=np.int16) // 4
    move_data = [enumerate_balanced_swaps(row, include_zero=False) for row in a]
    tr = torch.from_numpy(r.astype(np.float32)).to(device)
    retained: list[dict] = []
    evaluated = 0
    for ra in range(4):
        ma, da = move_data[ra]
        for rb in range(ra + 1, 4):
            mb, db = move_data[rb]
            tb = torch.from_numpy(db.astype(np.float32)).to(device)
            nb = (tb * tb).sum(dim=1)
            local: list[tuple[int, int, int]] = []
            for lo in range(0, len(da), block):
                hi = min(len(da), lo + block)
                ta = torch.from_numpy(da[lo:hi].astype(np.float32)).to(device)
                ar = ta + tr
                energies = (ar * ar).sum(dim=1)[:, None] + nb[None, :] + 2.0 * (ar @ tb.T)
                flat = energies.reshape(-1)
                k = min(keep, flat.numel())
                values, indices = torch.topk(flat, k=k, largest=False, sorted=True)
                width = len(db)
                local.extend(
                    (int(values[j].item()), lo + int(indices[j].item()) // width, int(indices[j].item()) % width)
                    for j in range(k)
                )
                evaluated += int(flat.numel())
            local.sort(key=lambda item: item[0])
            for energy4, ia, ib in local[:keep]:
                retained.append(
                    {
                        "energy": int(16 * energy4),
                        "rows": [ra, rb],
                        "indices": [ia, ib],
                        "moves": [ma[ia].astype(int).tolist(), mb[ib].astype(int).tolist()],
                    }
                )
            del tb, nb
    retained.sort(key=lambda item: item["energy"])
    # Exact direct verification of all candidates retained for possible use.
    verified: list[dict] = []
    seen = set()
    for item in retained:
        key = (tuple(item["rows"]), tuple(map(tuple, item["moves"])))
        if key in seen:
            continue
        seen.add(key)
        b = a.copy()
        for row, move in zip(item["rows"], item["moves"]):
            apply_move(b, row, np.asarray(move, dtype=np.int16))
        direct = exact_report(b)
        if direct["energy"] != item["energy"]:
            raise AssertionError("GPU pair energy disagrees with direct integer verification")
        item = dict(item)
        item.update(l1=direct["l1"], nonzero=direct["nonzero"], maxabs=direct["maxabs"])
        verified.append(item)
    verified.sort(key=lambda item: item["energy"])
    return verified[:keep], evaluated


def modular_hashes(deltas: np.ndarray, weights: np.ndarray) -> np.ndarray:
    # uint64 matrix multiplication is arithmetic modulo 2^64.
    return deltas.astype(np.uint64) @ weights.astype(np.uint64)


def exact_optional_one_swap_per_row_mitm(a: np.ndarray, seed: int) -> dict:
    """Decide all (zero-or-one balanced swap)^4 states by exact hash-filtered join."""
    started = time.time()
    report = exact_report(a)
    r = np.asarray(report["residual"], dtype=np.int16) // 4
    data = [enumerate_balanced_swaps(row, include_zero=True) for row in a]
    moves = [item[0] for item in data]
    deltas = [item[1] for item in data]
    rng = np.random.default_rng(seed)
    weights = rng.integers(0, np.iinfo(np.uint64).max, size=H, dtype=np.uint64)
    hashes = [modular_hashes(d, weights) for d in deltas]
    target_hash = modular_hashes((-r)[None, :], weights)[0]

    # Materialize and sort the row-2/row-3 half.  Only the lossless 64-bit
    # modular fingerprint is stored; every collision is checked in 83D below.
    h23 = np.add(hashes[2][:, None], hashes[3][None, :], dtype=np.uint64).reshape(-1)
    order = np.argsort(h23, kind="quicksort")
    sorted_h23 = h23[order]
    del h23
    gc.collect()

    hash_hits = 0
    vector_checks = 0
    solution = None
    for i0, h0 in enumerate(hashes[0]):
        h01 = np.add(h0, hashes[1], dtype=np.uint64)
        needles = np.subtract(target_hash, h01, dtype=np.uint64)
        left = np.searchsorted(sorted_h23, needles, side="left")
        right = np.searchsorted(sorted_h23, needles, side="right")
        hit_js = np.flatnonzero(left != right)
        for i1 in hit_js:
            lo = int(left[i1])
            hi = int(right[i1])
            hash_hits += hi - lo
            for at in range(lo, hi):
                flat = int(order[at])
                i2, i3 = divmod(flat, len(moves[3]))
                vector_checks += 1
                total = deltas[0][i0].astype(np.int16)
                total += deltas[1][i1].astype(np.int16)
                total += deltas[2][i2].astype(np.int16)
                total += deltas[3][i3].astype(np.int16)
                if np.array_equal(total, -r):
                    solution = [i0, int(i1), int(i2), int(i3)]
                    break
            if solution is not None:
                break
        if solution is not None:
            break

    result = {
        "complete": True,
        "neighborhood": "at most one balanced swap in each of four rows",
        "move_counts_including_zero": [int(len(x)) for x in moves],
        "half_pair_counts": [int(len(moves[0]) * len(moves[1])), int(len(moves[2]) * len(moves[3]))],
        "hash_bits": 64,
        "hash_hits": int(hash_hits),
        "exact_vector_checks": int(vector_checks),
        "elapsed_s": time.time() - started,
        "solved": solution is not None,
    }
    if solution is not None:
        b = a.copy()
        selected = []
        for row, idx in enumerate(solution):
            move = moves[row][idx]
            apply_move(b, row, move)
            selected.append(move.astype(int).tolist())
        direct = exact_report(b)
        if not direct["solved"] or direct["energy"] != 0:
            raise AssertionError("MITM vector equality did not produce an exact GS solution")
        result.update(selected_moves=selected, witness=direct)
    return result


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("--output-prefix", default="agent_gs_crossrow")
    parser.add_argument("--gpu-block", type=int, default=1024)
    parser.add_argument("--pair-descent-steps", type=int, default=8)
    parser.add_argument("--pair-keep", type=int, default=64)
    parser.add_argument("--seed", type=int, default=66820260721)
    parser.add_argument("--skip-mitm", action="store_true")
    args = parser.parse_args()
    if not torch.cuda.is_available():
        raise SystemExit("CUDA is required for the exhaustive cross-row pair scan")

    payload = json.loads(args.input.read_text(encoding="utf-8"))
    a = np.asarray(payload["sequences"], dtype=np.int8)
    if a.shape != (4, N) or np.any(np.abs(a) != 1):
        raise ValueError("expected four length-167 sign sequences")
    initial = exact_report(a)
    if sum(x * x for x in initial["row_sums"]) != 4 * N:
        raise ValueError("GS row-sum square identity failed")
    rows = initial["row_sums"]
    device = torch.device("cuda")
    history = []
    total_pairs = 0
    started = time.time()
    print(json.dumps({"event": "seed", "energy": initial["energy"], "l1": initial["l1"], "rows": rows}), flush=True)

    for step in range(args.pair_descent_steps):
        candidates, evaluated = exhaustive_best_cross_pair(a, args.gpu_block, device, keep=args.pair_keep)
        total_pairs += evaluated
        best = candidates[0]
        current = exact_report(a)
        event = {
            "step": step,
            "current_energy": current["energy"],
            "best_cross_pair_energy": best["energy"],
            "evaluated": evaluated,
            "best_move": best,
        }
        history.append(event)
        print(json.dumps({"event": "cross_pair_scan", **event}, separators=(",", ":")), flush=True)
        if best["energy"] >= current["energy"]:
            break
        for row, move in zip(best["rows"], best["moves"]):
            apply_move(a, row, np.asarray(move, dtype=np.int16))
        changed = exact_report(a)
        if changed["energy"] != best["energy"] or changed["row_sums"] != rows:
            raise AssertionError("descent step failed independent exact verification")
        live = dict(changed)
        live.update(pair_history=history, cross_pairs_evaluated=total_pairs, elapsed_s=time.time() - started)
        Path(args.output_prefix + "_live.json").write_text(json.dumps(live, separators=(",", ":")) + "\n", encoding="utf-8")

    best_report = exact_report(a)
    mitm = None
    if not args.skip_mitm and not best_report["solved"]:
        print(json.dumps({"event": "mitm_start", "energy": best_report["energy"]}), flush=True)
        mitm = exact_optional_one_swap_per_row_mitm(a, args.seed)
        print(json.dumps({"event": "mitm_result", **{k: v for k, v in mitm.items() if k != "witness"}}, separators=(",", ":")), flush=True)
        if mitm["solved"]:
            best_report = mitm["witness"]

    result = dict(best_report)
    result.update(
        source=str(args.input),
        initial_energy=initial["energy"],
        pair_history=history,
        cross_pairs_evaluated=int(total_pairs),
        mitm=mitm,
        elapsed_s=time.time() - started,
    )
    suffix = "_candidate.json" if result["solved"] else "_summary.json"
    output = Path(args.output_prefix + suffix)
    output.write_text(json.dumps(result, separators=(",", ":")) + "\n", encoding="utf-8")
    print(json.dumps({"event": "result", "solved": result["solved"], "energy": result["energy"], "output": str(output), "elapsed_s": result["elapsed_s"]}), flush=True)
    return 0 if result["solved"] else 2


if __name__ == "__main__":
    raise SystemExit(main())
