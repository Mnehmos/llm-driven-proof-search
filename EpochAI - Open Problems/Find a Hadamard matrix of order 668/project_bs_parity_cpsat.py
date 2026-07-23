"""Project a BS(84,83) near-state into the exact autocorrelation parity fibre.

The base-sequence equations require every nonperiodic residual to be zero.
Modulo four this is equivalent to an odd number of disagreeing pairs at each
shift.  Those 83 conditions are linear over GF(2), so CP-SAT can find the
minimum-Hamming projection while preserving all four row sums exactly.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import numpy as np
from ortools.sat.python import cp_model


LENGTHS = (84, 84, 83, 83)


def residual(sequences: list[list[int]]) -> list[int]:
    return [
        sum(
            sum(seq[i] * seq[i + d] for i in range(len(seq) - d))
            for seq in sequences
        )
        for d in range(1, 84)
    ]


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("--seconds", type=float, default=120.0)
    parser.add_argument(
        "--target-rows",
        help="optional comma-separated exact row tuple; defaults to preserving the seed",
    )
    parser.add_argument("--preserve-alt", action="store_true")
    parser.add_argument("--preserve-quartic", action="store_true")
    parser.add_argument("--target-alt",
                        help="optional comma-separated alternating-sum tuple")
    parser.add_argument("--target-quartic",
                        help="optional eight comma-separated z=i real/imaginary sums")
    parser.add_argument("--workers", type=int, default=8)
    parser.add_argument("--seed", type=int, default=668)
    parser.add_argument(
        "--output", type=Path, default=Path("bs_84_83_parity_projection.json")
    )
    args = parser.parse_args()

    payload = json.loads(args.input.read_text(encoding="utf-8"))
    seed = payload["sequences"]
    # The variable-q special-Golay representation stores four length-167
    # sequences, but its underlying base sequences are (s_left, (s*q)_left,
    # s_right, (s*q)_right).
    if tuple(map(len, seed)) == (167, 167, 167, 167) and "s" in payload and "q" in payload:
        s = payload["s"]
        t = [x * y for x, y in zip(payload["s"], payload["q"])]
        seed = [s[:84], t[:84], s[84:], t[84:]]
    if tuple(map(len, seed)) != LENGTHS:
        raise ValueError("input must contain BS(84,83) sequences")
    if any(value not in (-1, 1) for seq in seed for value in seq):
        raise ValueError("input entries must be +/-1")

    model = cp_model.CpModel()
    # A true bit represents -1.
    bits = [
        [model.new_bool_var(f"x_{k}_{i}") for i in range(length)]
        for k, length in enumerate(LENGTHS)
    ]
    for seq_bits, seq_seed in zip(bits, seed):
        for bit, value in zip(seq_bits, seq_seed):
            model.add_hint(bit, int(value == -1))

    seed_rows = list(map(sum, seed))
    target_rows = seed_rows
    if args.target_rows:
        target_rows = [int(value) for value in args.target_rows.split(",")]
        if len(target_rows) != 4 or sum(value * value for value in target_rows) != 334:
            raise ValueError("target row tuple must have four entries with square sum 334")
        if any((length - row) % 2 for length, row in zip(LENGTHS, target_rows)):
            raise ValueError("target rows have the wrong parity")

    for seq_bits, length, target_row in zip(bits, LENGTHS, target_rows):
        model.add(sum(seq_bits) == (length - target_row) // 2)
    if args.preserve_alt and args.target_alt:
        raise ValueError("choose either --preserve-alt or --target-alt")
    if args.preserve_quartic and args.target_quartic:
        raise ValueError("choose either --preserve-quartic or --target-quartic")
    if args.preserve_alt or args.target_alt:
        alt_targets = [
            sum((1 if i % 2 == 0 else -1) * value for i, value in enumerate(seq))
            for seq in seed
        ]
        if args.target_alt:
            alt_targets = [int(value) for value in args.target_alt.split(",")]
            if len(alt_targets) != 4 or sum(value * value for value in alt_targets) != 334:
                raise ValueError("target alternating tuple must have square norm 334")
            if any((length - row) % 2 for length, row in zip(LENGTHS, alt_targets)):
                raise ValueError("target alternating tuple has the wrong parity")
        for seq_bits, target in zip(bits, alt_targets):
            model.add(sum((1 if i % 2 == 0 else -1) * (1 - 2 * bit)
                          for i, bit in enumerate(seq_bits)) == target)
    if args.preserve_quartic or args.target_quartic:
        quartic_targets = []
        for seq in seed:
            sums = [sum(seq[r::4]) for r in range(4)]
            quartic_targets.append((sums[0] - sums[2], sums[1] - sums[3]))
        if args.target_quartic:
            flat = [int(value) for value in args.target_quartic.split(",")]
            if len(flat) != 8 or sum(value * value for value in flat) != 334:
                raise ValueError("target quartic tuple must have square norm 334")
            quartic_targets = list(zip(flat[0::2], flat[1::2]))
        for seq_bits, (real_target, imag_target) in zip(bits, quartic_targets):
            model.add(sum((1 if i % 4 == 0 else -1) * (1 - 2 * bit)
                          for i, bit in enumerate(seq_bits) if i % 2 == 0) == real_target)
            model.add(sum((1 if i % 4 == 1 else -1) * (1 - 2 * bit)
                          for i, bit in enumerate(seq_bits) if i % 2 == 1) == imag_target)

    # At shift d, the parity of the disagreement count is the XOR of vertices
    # having odd degree in the union of the four distance-d path graphs.
    # The required disagreement count is 167-2d, always odd.
    for d in range(1, 84):
        odd_vertices: list[cp_model.IntVar] = []
        for seq_bits in bits:
            incidence = [0] * len(seq_bits)
            for i in range(len(seq_bits) - d):
                incidence[i] ^= 1
                incidence[i + d] ^= 1
            odd_vertices.extend(
                bit for bit, degree in zip(seq_bits, incidence) if degree
            )
        if not odd_vertices:
            raise RuntimeError(f"empty parity equation at shift {d}")
        model.add_bool_xor(odd_vertices)

    changed = []
    for seq_bits, seq_seed in zip(bits, seed):
        for bit, value in zip(seq_bits, seq_seed):
            changed.append(bit if value == 1 else bit.Not())
    model.minimize(sum(changed))

    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = args.seconds
    solver.parameters.num_search_workers = args.workers
    solver.parameters.random_seed = args.seed
    status = solver.solve(model)
    if status not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        print(json.dumps({"status": solver.status_name(status)}))
        return 2

    sequences = [
        [-1 if solver.value(bit) else 1 for bit in seq_bits] for seq_bits in bits
    ]
    result_residual = residual(sequences)
    rows = list(map(sum, sequences))
    if rows != target_rows:
        raise RuntimeError("row sums drifted")
    if any(value % 4 for value in result_residual):
        raise RuntimeError("parity projection failed")

    result = {
        "construction": "base sequences BS(84,83)",
        "solver": "minimum-Hamming CP-SAT parity projection",
        "solved": not any(result_residual),
        "status": solver.status_name(status),
        "hamming_changes": int(solver.objective_value),
        "energy": int(np.dot(result_residual, result_residual)),
        "l1": int(sum(map(abs, result_residual))),
        "parity_bad": 0,
        "row_sums": rows,
        "alternating_sums": [
            sum((1 if i % 2 == 0 else -1) * value
                for i, value in enumerate(seq)) for seq in sequences
        ],
        "z4_components": [value for seq in sequences
            for value in (sum(seq[0::4]) - sum(seq[2::4]),
                          sum(seq[1::4]) - sum(seq[3::4]))],
        "residual": result_residual,
        "sequences": sequences,
    }
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: result[key] for key in (
        "status", "hamming_changes", "energy", "l1", "row_sums", "solved"
    )}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
