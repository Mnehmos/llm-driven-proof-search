"""Exact bounded search for BS(84,83) in a coupled signature neighbourhood.

The parity-good seed fixes, at each reversal orbit, the XOR of the two
equal-length rows' antisymmetric signatures.  Cross-fibre moves may change
each row's signature but preserve that coupled XOR.  This model searches the
whole resulting fibre (not merely combinations of selected local moves), with
an optional Hamming-radius bound around the incumbent.
"""

from __future__ import annotations

import argparse
import json
import time
from pathlib import Path

from ortools.sat.python import cp_model


LENGTHS = (84, 84, 83, 83)
TARGET_ROWS = (14, -8, -7, -5)


def correlations(sequences: list[list[int]]) -> list[int]:
    return [
        sum(
            sum(row[i] * row[i + d] for i in range(len(row) - d))
            for row in sequences
        )
        for d in range(1, 84)
    ]


def add_xor_equivalence(model: cp_model.CpModel, a, b, y) -> None:
    # y == a xor b.
    model.add_bool_or([a, b, y.Not()])
    model.add_bool_or([a.Not(), b.Not(), y.Not()])
    model.add_bool_or([a, b.Not(), y])
    model.add_bool_or([a.Not(), b, y])


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("--seconds", type=float, default=300.0)
    parser.add_argument("--workers", type=int, default=4)
    parser.add_argument("--seed", type=int, default=668)
    parser.add_argument("--max-changes", type=int, default=80)
    parser.add_argument(
        "--output", type=Path, default=Path("agent_bs_signature_candidate.json")
    )
    args = parser.parse_args()

    payload = json.loads(args.input.read_text(encoding="utf-8"))
    hint = payload["sequences"]
    if tuple(map(len, hint)) != LENGTHS:
        raise ValueError("expected four sequences of lengths 84,84,83,83")
    if tuple(map(sum, hint)) != TARGET_ROWS:
        raise ValueError("seed is outside target row tuple")
    seed_residual = correlations(hint)
    if any(value % 4 for value in seed_residual):
        raise ValueError("seed is outside the parity-good fibre")

    started = time.time()
    model = cp_model.CpModel()
    # True represents -1.
    bits = [
        [model.new_bool_var(f"x_{k}_{i}") for i in range(length)]
        for k, length in enumerate(LENGTHS)
    ]
    for row_bits, length, target in zip(bits, LENGTHS, TARGET_ROWS):
        model.add(sum(row_bits) == (length - target) // 2)

    # Fix the coupled reversal signatures to those of the checkpoint.  Adding
    # a true literal converts CP-SAT's required odd XOR into an even XOR.
    true_literal = model.new_bool_var("constant_true")
    model.add(true_literal == 1)
    for k, l in ((0, 1), (2, 3)):
        n = LENGTHS[k]
        for p in range(n // 2):
            q = n - 1 - p
            signature = (
                int(hint[k][p] == -1)
                ^ int(hint[k][q] == -1)
                ^ int(hint[l][p] == -1)
                ^ int(hint[l][q] == -1)
            )
            literals = [bits[k][p], bits[k][q], bits[l][p], bits[l][q]]
            if signature == 0:
                literals.append(true_literal)
            model.add_bool_xor(literals)

    changes = []
    for row_bits, row_hint in zip(bits, hint):
        for bit, sign in zip(row_bits, row_hint):
            model.add_hint(bit, int(sign == -1))
            changes.append(bit if sign == 1 else bit.Not())
    if args.max_changes >= 0:
        model.add(sum(changes) <= args.max_changes)

    xor_variables = 0
    # At shift d there are 334-4d products.  Requiring exactly half of them to
    # be disagreements is precisely zero total nonperiodic autocorrelation.
    for d in range(1, 84):
        disagreements = []
        for row_bits in bits:
            for i in range(len(row_bits) - d):
                y = model.new_bool_var(f"y_{d}_{len(disagreements)}")
                add_xor_equivalence(model, row_bits[i], row_bits[i + d], y)
                disagreements.append(y)
                xor_variables += 1
        model.add(sum(disagreements) == len(disagreements) // 2)

    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = args.seconds
    solver.parameters.num_search_workers = args.workers
    solver.parameters.random_seed = args.seed
    solver.parameters.cp_model_presolve = True
    solver.parameters.search_branching = cp_model.PORTFOLIO_WITH_QUICK_RESTART_SEARCH
    status = solver.solve(model)
    status_name = solver.status_name(status)
    summary = {
        "status": status_name,
        "elapsed_s": time.time() - started,
        "max_changes": args.max_changes,
        "xor_variables": xor_variables,
        "conflicts": solver.num_conflicts,
        "branches": solver.num_branches,
    }
    Path("agent_bs_signature_cpsat_summary.json").write_text(
        json.dumps(summary, indent=2) + "\n", encoding="utf-8"
    )
    print(json.dumps(summary), flush=True)
    if status not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        return 2

    sequences = [
        [-1 if solver.value(bit) else 1 for bit in row_bits] for row_bits in bits
    ]
    residual = correlations(sequences)
    rows = tuple(map(sum, sequences))
    hamming = sum(
        a != b
        for row, seed_row in zip(sequences, hint)
        for a, b in zip(row, seed_row)
    )
    if rows != TARGET_ROWS or any(residual) or hamming > args.max_changes:
        raise RuntimeError("independent exact verification failed")
    result = {
        "construction": "base sequences BS(84,83)",
        "solver": "agent exact CP-SAT coupled-signature neighbourhood",
        "solved": True,
        "energy": 0,
        "hamming_changes": hamming,
        "row_sums": list(rows),
        "residual": residual,
        "solver_summary": summary,
        "sequences": sequences,
    }
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"event": "verified_witness", "output": str(args.output)}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
