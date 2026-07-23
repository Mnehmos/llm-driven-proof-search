"""Test whether selected radius-12 order-7 fibers beat a Hamming cap."""

from __future__ import annotations

import argparse
import json

from ortools.sat.python import cp_model

import agent_bp2_rank_o7_radius12 as ranker
from agent_bp2_gf2_spectral_shells import (
    base_basis,
    enumerate_allocations,
    exact_cost_groups,
    septimal_value,
    target_compatible,
)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("input")
    parser.add_argument("--indices", required=True)
    parser.add_argument("--cap", type=int, default=13)
    parser.add_argument("--seconds", type=float, default=180)
    parser.add_argument("--workers", type=int, default=1)
    args = parser.parse_args()
    seed = json.load(open(args.input, "r", encoding="utf-8"))["sequences"]
    groups = exact_cost_groups(seed, 7, 12, septimal_value)
    targets, _ = enumerate_allocations(groups, 12, (0, 4, 8, 12), (334, 0, 0))
    basis = base_basis(seed, (1, 2, 3, 4, 5))
    survivors = [target for target in sorted(targets) if target_compatible(basis, 7, target)]
    assert len(survivors) == 13

    original_minimize = cp_model.CpModel.minimize

    def impose_cap(model, expression):
        model.add(expression <= args.cap)

    cp_model.CpModel.minimize = impose_cap
    try:
        for index in (int(value) for value in args.indices.split(",")):
            result = ranker.solve_target(
                seed, survivors[index], args.seconds, args.workers, index
            )
            if "sequences" in result:
                result["hamming_changes"] = sum(
                    a != b
                    for old, new in zip(seed, result["sequences"])
                    for a, b in zip(old, new)
                )
            print(
                json.dumps(
                    {
                        key: result.get(key)
                        for key in (
                            "target_index",
                            "status",
                            "hamming_changes",
                            "energy",
                            "l1",
                        )
                    }
                ),
                flush=True,
            )
    finally:
        cp_model.CpModel.minimize = original_minimize


if __name__ == "__main__":
    main()
