"""Direct CP-SAT optimization/search for base sequences BS(84,83).

The model searches all four binary sequences in a chosen exact row-sum fibre.
Every nonperiodic correlation is represented by disagreement booleans.  The
necessary mod-four condition is imposed explicitly and the sum of absolute
residuals is minimized; objective zero is an exact BS(84,83) witness.
"""

from __future__ import annotations

import argparse
import json
import time
from pathlib import Path

from ortools.sat.python import cp_model


LENGTHS = (84, 84, 83, 83)


def add_xor_equivalence(model: cp_model.CpModel, a, b, y) -> None:
    # y = a xor b.
    model.add_bool_or([a, b, y.Not()])
    model.add_bool_or([a.Not(), b.Not(), y.Not()])
    model.add_bool_or([a, b.Not(), y])
    model.add_bool_or([a.Not(), b, y])


def correlations(sequences: list[list[int]]) -> list[int]:
    return [
        sum(
            sum(seq[i] * seq[i + d] for i in range(len(seq) - d))
            for seq in sequences
        )
        for d in range(1, 84)
    ]


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--row-tuple", default="10,8,-1,-13")
    parser.add_argument(
        "--alt-tuple",
        help="optional alternating row-sum tuple, also required to have square norm 334",
    )
    parser.add_argument(
        "--quartic-tuple",
        help="optional eight comma-separated real/imaginary sums at z=i",
    )
    parser.add_argument("--hint", type=Path)
    parser.add_argument("--seconds", type=float, default=900.0)
    parser.add_argument("--workers", type=int, default=8)
    parser.add_argument("--seed", type=int, default=668)
    parser.add_argument("--max-changes", type=int)
    parser.add_argument("--exact", action="store_true", help="solve residual=0 as satisfaction")
    parser.add_argument(
        "--output", type=Path, default=Path("bs_84_83_cpsat_candidate.json")
    )
    args = parser.parse_args()
    rows = [int(value) for value in args.row_tuple.split(",")]
    if len(rows) != 4 or sum(value * value for value in rows) != 334:
        raise ValueError("row tuple must contain four entries with square sum 334")
    if any((length - row) % 2 for length, row in zip(LENGTHS, rows)):
        raise ValueError("row tuple parity mismatch")
    alt_rows = None
    if args.alt_tuple:
        alt_rows = [int(value) for value in args.alt_tuple.split(",")]
        if len(alt_rows) != 4 or sum(value * value for value in alt_rows) != 334:
            raise ValueError("alternating tuple must have four entries with square sum 334")
        # Alternating sums have the same parity as sequence lengths.
        if any((length - row) % 2 for length, row in zip(LENGTHS, alt_rows)):
            raise ValueError("alternating tuple parity mismatch")
    quartic_rows = None
    if args.quartic_tuple:
        quartic_rows = [int(value) for value in args.quartic_tuple.split(",")]
        if len(quartic_rows) != 8 or sum(value * value for value in quartic_rows) != 334:
            raise ValueError("quartic tuple must have eight entries with square norm 334")

    hint = None
    if args.hint:
        hint = json.loads(args.hint.read_text(encoding="utf-8"))["sequences"]
        if tuple(map(len, hint)) != LENGTHS or list(map(sum, hint)) != rows:
            raise ValueError("hint does not lie in requested row fibre")

    started = time.time()
    model = cp_model.CpModel()
    # True represents -1.
    bits = [
        [model.new_bool_var(f"x_{k}_{i}") for i in range(length)]
        for k, length in enumerate(LENGTHS)
    ]
    for seq_bits, length, row in zip(bits, LENGTHS, rows):
        model.add(sum(seq_bits) == (length - row) // 2)
    if alt_rows is not None:
        for seq_bits, target in zip(bits, alt_rows):
            model.add(
                sum((1 if i % 2 == 0 else -1) * (1 - 2 * bit)
                    for i, bit in enumerate(seq_bits)) == target
            )
    if quartic_rows is not None:
        for k, seq_bits in enumerate(bits):
            real_target, imag_target = quartic_rows[2 * k:2 * k + 2]
            model.add(
                sum((1 if i % 4 == 0 else -1) * (1 - 2 * bit)
                    for i, bit in enumerate(seq_bits) if i % 2 == 0) == real_target
            )
            model.add(
                sum((1 if i % 4 == 1 else -1) * (1 - 2 * bit)
                    for i, bit in enumerate(seq_bits) if i % 2 == 1) == imag_target
            )

    abs_residuals = []
    xor_count = 0
    for d in range(1, 84):
        disagreements = []
        for k, seq_bits in enumerate(bits):
            for i in range(len(seq_bits) - d):
                y = model.new_bool_var(f"y_{k}_{i}_{d}")
                add_xor_equivalence(model, seq_bits[i], seq_bits[i + d], y)
                disagreements.append(y)
                xor_count += 1
        pair_count = len(disagreements)
        residual = model.new_int_var(-pair_count, pair_count, f"r_{d}")
        model.add(residual == pair_count - 2 * sum(disagreements))
        # Any exact residual is zero, hence divisible by four.  Restricting to
        # this necessary fibre greatly reduces the optimization search.
        quarter = model.new_int_var(-pair_count // 4 - 1, pair_count // 4 + 1, f"q_{d}")
        model.add(residual == 4 * quarter)
        absolute = model.new_int_var(0, pair_count, f"a_{d}")
        model.add_abs_equality(absolute, residual)
        abs_residuals.append(absolute)
        if args.exact:
            model.add(residual == 0)

    changes = []
    if hint is not None:
        for seq_bits, seq_hint in zip(bits, hint):
            for bit, sign in zip(seq_bits, seq_hint):
                model.add_hint(bit, int(sign == -1))
                changes.append(bit if sign == 1 else bit.Not())
        if args.max_changes is not None:
            model.add(sum(changes) <= args.max_changes)
    if not args.exact:
        model.minimize(sum(abs_residuals))

    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = args.seconds
    solver.parameters.num_search_workers = args.workers
    solver.parameters.random_seed = args.seed
    solver.parameters.cp_model_presolve = True
    status = solver.solve(model)
    status_name = solver.status_name(status)
    summary = {
        "event": "result",
        "status": status_name,
        "elapsed_s": time.time() - started,
        "xor_variables": xor_count,
        "conflicts": solver.num_conflicts,
        "branches": solver.num_branches,
        "objective": solver.objective_value
        if not args.exact and status in (cp_model.OPTIMAL, cp_model.FEASIBLE)
        else None,
        "best_bound": solver.best_objective_bound,
    }
    print(json.dumps(summary), flush=True)
    if status not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        return 2

    sequences = [
        [-1 if solver.value(bit) else 1 for bit in seq_bits] for seq_bits in bits
    ]
    residual = correlations(sequences)
    if list(map(sum, sequences)) != rows or any(value % 4 for value in residual):
        raise RuntimeError("independent model check failed")
    energy = sum(value * value for value in residual)
    result = {
        "construction": "base sequences BS(84,83)",
        "solver": "direct CP-SAT L1 optimization",
        "solved": not any(residual),
        "status": status_name,
        "energy": energy,
        "l1": sum(map(abs, residual)),
        "row_sums": rows,
        "residual": residual,
        "solver_summary": summary,
        "sequences": sequences,
    }
    output = args.output if result["solved"] else args.output.with_name(
        args.output.stem + "_best.json"
    )
    output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"event": "candidate", "solved": result["solved"],
                      "energy": energy, "l1": result["l1"],
                      "output": str(output)}), flush=True)
    return 0 if result["solved"] else 2


if __name__ == "__main__":
    raise SystemExit(main())
