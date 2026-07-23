"""Exact SAT/PB search for Turyn-type sequences TT(56).

For a +/-1 sequence X, let bit x_i be 0 for +1 and 1 for -1.
Then X_i X_{i+s} = 1 - 2 (x_i xor x_{i+s}).  Consequently

  N_A(s) + N_B(s) + 2 N_C(s) + 2 N_D(s) = 0

is exactly the weighted pseudo-Boolean equation

  sum(x_i xor x_{i+s}) = 167 - 3s,

where A,B,C have length 56, D has length 55, and C,D terms have
weight two.  There is no floating-point or heuristic acceptance here: SAT
means an exact TT(56) witness, which yields a Hadamard matrix of order 668.
"""

from __future__ import annotations

import argparse
import json
import time
from pathlib import Path

import z3


LENGTHS = (56, 56, 56, 55)
WEIGHTS = (1, 1, 2, 2)


def possible_row_sums() -> list[tuple[int, int, int, int]]:
    """All signed row-sum tuples satisfying the TT square identity."""
    even = range(-56, 57, 2)
    odd = range(-55, 56, 2)
    out: list[tuple[int, int, int, int]] = []
    for a in even:
        for b in even:
            ab = a * a + b * b
            if ab > 334:
                continue
            for c in even:
                rem = 334 - ab - 2 * c * c
                if rem < 0:
                    continue
                for d in odd:
                    if 2 * d * d == rem:
                        out.append((a, b, c, d))
    return out


def build_solver(seed: int, timeout_ms: int, threads: int) -> tuple[z3.Solver, list[list[z3.BoolRef]]]:
    solver = z3.Solver()
    solver.set("timeout", timeout_ms)
    solver.set("random_seed", seed)
    solver.set("threads", threads)
    solver.set("phase_selection", 5)
    solver.set("restart_strategy", 1)

    names = "ABCD"
    bits = [[z3.Bool(f"{names[k]}_{i}") for i in range(n)] for k, n in enumerate(LENGTHS)]

    # Canonical endpoint normalization from the TT search literature.
    # False denotes +1, True denotes -1.
    solver.add(z3.Not(bits[0][0]), z3.Not(bits[0][-1]))
    solver.add(z3.Not(bits[1][0]), z3.Not(bits[1][-1]))
    solver.add(z3.Not(bits[2][0]), bits[2][-1])
    solver.add(z3.Not(bits[3][0]))

    # Exact weighted nonperiodic autocorrelation equations.
    for shift in range(1, 56):
        terms: list[tuple[z3.BoolRef, int]] = []
        for seq, weight in zip(bits, WEIGHTS):
            for i in range(len(seq) - shift):
                terms.append((z3.Xor(seq[i], seq[i + shift]), weight))
        solver.add(z3.PbEq(terms, 167 - 3 * shift))

    # Redundant but powerful global pruning: evaluating the norm identity at 1
    # forces a^2+b^2+2c^2+2d^2=334. Enumerating its finite solutions keeps the
    # Boolean problem linear instead of introducing nonlinear integer arithmetic.
    row_exprs = [n - 2 * z3.Sum([z3.If(x, 1, 0) for x in seq]) for n, seq in zip(LENGTHS, bits)]
    solver.add(z3.Or([z3.And([row_exprs[i] == row[i] for i in range(4)]) for row in possible_row_sums()]))

    return solver, bits


def verify(sequences: list[list[int]]) -> tuple[bool, list[int]]:
    residual = []
    for shift in range(1, 56):
        value = 0
        for seq, weight in zip(sequences, WEIGHTS):
            value += weight * sum(seq[i] * seq[i + shift] for i in range(len(seq) - shift))
        residual.append(value)
    return all(x == 0 for x in residual), residual


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--timeout-ms", type=int, default=600_000)
    parser.add_argument("--seed", type=int, default=1)
    parser.add_argument("--threads", type=int, default=16)
    parser.add_argument("--output", type=Path, default=Path("Find a Hadamard matrix of order 668/tt56_z3_candidate.json"))
    args = parser.parse_args()

    started = time.time()
    solver, bits = build_solver(args.seed, args.timeout_ms, args.threads)
    print(json.dumps({"event": "built", "seed": args.seed, "assertions": len(solver.assertions()), "row_sum_cases": len(possible_row_sums()), "elapsed_s": time.time() - started}), flush=True)
    result = solver.check()
    elapsed = time.time() - started
    print(json.dumps({"event": "result", "result": str(result), "seed": args.seed, "elapsed_s": elapsed, "reason_unknown": solver.reason_unknown() if result == z3.unknown else None}), flush=True)

    if result != z3.sat:
        return 2 if result == z3.unknown else 1

    model = solver.model()
    sequences = [[-1 if z3.is_true(model.eval(x, model_completion=True)) else 1 for x in seq] for seq in bits]
    valid, residual = verify(sequences)
    if not valid:
        raise RuntimeError(f"SAT model failed independent autocorrelation check: {residual}")
    payload = {
        "construction": "Turyn-type sequences TT(56)",
        "solver": z3.get_version_string(),
        "seed": args.seed,
        "elapsed_s": elapsed,
        "row_sums": [sum(seq) for seq in sequences],
        "residual": residual,
        "sequences": sequences,
    }
    args.output.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"event": "verified_witness", "output": str(args.output), "row_sums": payload["row_sums"]}), flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
