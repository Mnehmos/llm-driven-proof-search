"""Exact search in Eliahou's special Golay-quadruple family at length 167.

Let f be +1 on the first 84 coordinates and -1 on the last 83, and
q have run-length encoding (83,2,81,1).  We search for s such that

    (s, s*f, s*q, s*q*f)

is a true Golay quadruple.  Correlations at shifts >=84 vanish identically.
At each smaller shift, only pairs in the same f-half with equal q signs
remain, each with multiplicity four.  Thus every condition is exactly one
cardinality equation on XORs of the 167 unknown signs of s.
"""

from __future__ import annotations

import argparse
import json
import time
from pathlib import Path

import z3


def expand_runs(runs: list[int]) -> list[int]:
    return [1 if j % 2 == 0 else -1 for j, n in enumerate(runs) for _ in range(n)]


Q = expand_runs([83, 2, 81, 1])
F = [1] * 84 + [-1] * 83


def verify(s: list[int]) -> list[int]:
    sequences = [s, [x * f for x, f in zip(s, F)], [x * q for x, q in zip(s, Q)], [x * q * f for x, q, f in zip(s, Q, F)]]
    return [sum(seq[i] * seq[i + shift] for seq in sequences for i in range(167 - shift)) for shift in range(1, 167)]


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--timeout-ms", type=int, default=600_000)
    parser.add_argument("--threads", type=int, default=8)
    parser.add_argument("--seed", type=int, default=668)
    parser.add_argument("--output", type=Path, default=Path("Find a Hadamard matrix of order 668/special_golay_167_candidate.json"))
    args = parser.parse_args()

    started = time.time()
    bits = [z3.Bool(f"s_{i}") for i in range(167)]
    solver = z3.Solver()
    solver.set("timeout", args.timeout_ms)
    solver.set("threads", args.threads)
    solver.set("random_seed", args.seed)
    solver.set("phase_selection", 5)
    solver.add(z3.Not(bits[0]))  # negate s if necessary
    edge_counts = []
    for shift in range(1, 84):
        terms = [z3.Xor(bits[i], bits[i + shift]) for i in range(167 - shift) if F[i] == F[i + shift] and Q[i] == Q[i + shift]]
        edge_counts.append(len(terms))
        if terms:
            solver.add(z3.PbEq([(term, 1) for term in terms], len(terms) // 2))
    print(json.dumps({"event": "built", "base_variables": 167, "constraints": len(solver.assertions()), "edge_terms": sum(edge_counts), "elapsed_s": time.time() - started}), flush=True)
    result = solver.check()
    print(json.dumps({"event": "result", "result": str(result), "elapsed_s": time.time() - started, "reason_unknown": solver.reason_unknown() if result == z3.unknown else None}), flush=True)
    if result != z3.sat:
        return 2 if result == z3.unknown else 1

    model = solver.model()
    s = [-1 if z3.is_true(model.eval(x, model_completion=True)) else 1 for x in bits]
    residual = verify(s)
    if any(residual):
        raise RuntimeError(f"model failed independent Golay check: {[(i + 1, x) for i, x in enumerate(residual) if x]}")
    sequences = [s, [x * f for x, f in zip(s, F)], [x * q for x, q in zip(s, Q)], [x * q * f for x, q, f in zip(s, Q, F)]]
    payload = {"construction": "special Golay quadruple length 167", "q_runs": [83, 2, 81, 1], "elapsed_s": time.time() - started, "residual": residual, "sequences": sequences}
    args.output.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"event": "verified_witness", "output": str(args.output), "row_sums": [sum(x) for x in sequences]}), flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
