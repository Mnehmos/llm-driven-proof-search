"""Rank every GF(2)-compatible E2144 order-7 radius-12 fiber by projection."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from ortools.sat.python import cp_model

from agent_bp2_gf2_spectral_shells import (
    LENS,
    base_basis,
    compression,
    enumerate_allocations,
    exact_cost_groups,
    septimal_value,
    target_compatible,
)


def residual(sequences):
    return [
        sum(
            sum(sequence[i] * sequence[i + shift] for i in range(len(sequence) - shift))
            for sequence in sequences
        )
        for shift in range(1, 84)
    ]


def solve_target(seed, target7, seconds, workers, target_index):
    rows = [sum(sequence) for sequence in seed]
    alts = [
        sum(value if i % 2 == 0 else -value for i, value in enumerate(sequence))
        for sequence in seed
    ]
    z4 = [
        (
            sum(sequence[0::4]) - sum(sequence[2::4]),
            sum(sequence[1::4]) - sum(sequence[3::4]),
        )
        for sequence in seed
    ]
    target3 = [compression(sequence, 3) for sequence in seed]
    target5 = [compression(sequence, 5) for sequence in seed]

    model = cp_model.CpModel()
    bits = [
        [model.new_bool_var(f"x_{k}_{i}") for i in range(length)]
        for k, length in enumerate(LENS)
    ]
    signs = [[1 - 2 * bit for bit in row] for row in bits]
    for row, sequence in zip(bits, seed):
        for bit, value in zip(row, sequence):
            model.add_hint(bit, int(value == -1))

    for k in range(4):
        model.add(sum(signs[k]) == rows[k])
        model.add(
            sum((1 if i % 2 == 0 else -1) * signs[k][i] for i in range(LENS[k]))
            == alts[k]
        )
        model.add(
            sum(
                (1 if i % 4 == 0 else -1) * signs[k][i]
                for i in range(LENS[k])
                if i % 2 == 0
            )
            == z4[k][0]
        )
        model.add(
            sum(
                (1 if i % 4 == 1 else -1) * signs[k][i]
                for i in range(LENS[k])
                if i % 2 == 1
            )
            == z4[k][1]
        )
        for modulus, targets in ((3, target3[k]), (5, target5[k]), (7, target7[k])):
            for residue, target_sum in enumerate(targets):
                model.add(
                    sum(signs[k][i] for i in range(residue, LENS[k], modulus))
                    == target_sum
                )

    for shift in range(1, 84):
        odd = []
        for row in bits:
            incidence = [0] * len(row)
            for i in range(len(row) - shift):
                incidence[i] ^= 1
                incidence[i + shift] ^= 1
            odd.extend(bit for bit, flag in zip(row, incidence) if flag)
        model.add_bool_xor(odd)

    changed = [
        bit if value == 1 else bit.Not()
        for row, sequence in zip(bits, seed)
        for bit, value in zip(row, sequence)
    ]
    model.minimize(sum(changed))
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = seconds
    solver.parameters.num_search_workers = workers
    solver.parameters.random_seed = 6681200 + target_index
    status = solver.solve(model)
    result = {
        "target_index": target_index,
        "status": solver.status_name(status),
        "order7": target7,
        "best_bound": int(solver.best_objective_bound),
    }
    if status not in (cp_model.FEASIBLE, cp_model.OPTIMAL):
        return result

    sequences = [[-1 if solver.value(bit) else 1 for bit in row] for row in bits]
    r = residual(sequences)
    assert all(value % 4 == 0 for value in r)
    assert [compression(sequence, 3) for sequence in sequences] == target3
    assert [compression(sequence, 5) for sequence in sequences] == target5
    assert [compression(sequence, 7) for sequence in sequences] == list(target7)
    result.update(
        {
            "independently_recomputed": True,
            "hamming_changes": int(solver.objective_value),
            "energy": sum(value * value for value in r),
            "l1": sum(abs(value) for value in r),
            "parity_bad": sum(value % 4 != 0 for value in r),
            "residual": r,
            "sequences": sequences,
        }
    )
    return result


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("--seconds", type=float, default=30)
    parser.add_argument("--workers", type=int, default=4)
    parser.add_argument(
        "--output", type=Path, default=Path("agent_bp2_ranked_o7_radius12.json")
    )
    args = parser.parse_args()
    seed = json.loads(args.input.read_text(encoding="utf-8"))["sequences"]

    groups = exact_cost_groups(seed, 7, 12, septimal_value)
    targets, patterns = enumerate_allocations(groups, 12, (0, 4, 8, 12), (334, 0, 0))
    basis = base_basis(seed, (1, 2, 3, 4, 5))
    survivors = [target for target in sorted(targets) if target_compatible(basis, 7, target)]
    assert len(targets) == 69 and len(survivors) == 13

    results = []
    for index, target in enumerate(survivors):
        result = solve_target(seed, target, args.seconds, args.workers, index)
        results.append(result)
        print(
            json.dumps(
                {
                    key: result.get(key)
                    for key in (
                        "target_index",
                        "status",
                        "best_bound",
                        "hamming_changes",
                        "energy",
                        "l1",
                    )
                }
            ),
            flush=True,
        )
    results.sort(
        key=lambda result: (
            "hamming_changes" not in result,
            result.get("hamming_changes", 10**9),
            result.get("energy", 10**9),
            result["target_index"],
        )
    )
    payload = {
        "source": str(args.input),
        "total_radius12_targets": len(targets),
        "gf2_compatible_targets": len(survivors),
        "ranking": results,
    }
    args.output.write_text(json.dumps(payload, separators=(",", ":")) + "\n", encoding="utf-8")
    print("RANKING", flush=True)
    for rank, result in enumerate(results, 1):
        print(
            rank,
            result["target_index"],
            result["status"],
            result.get("hamming_changes"),
            result.get("best_bound"),
            result.get("energy"),
            result.get("l1"),
            flush=True,
        )


if __name__ == "__main__":
    main()
