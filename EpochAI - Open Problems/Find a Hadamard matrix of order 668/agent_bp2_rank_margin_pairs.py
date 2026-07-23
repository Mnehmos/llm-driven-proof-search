"""Rank the 12 E896 cubic-L1=8 x quintic-L1=8 spectral fibres."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from ortools.sat.python import cp_model


LENS = (84, 84, 83, 83)
CUBIC = (
    ((0, 2, 10), (-2, 6, 6), (-4, 4, 3), (4, -4, 9)),
    ((0, 2, 10), (-2, 6, 6), (-4, 6, 1), (6, -4, 7)),
    ((0, 2, 10), (2, 4, 4), (-4, 8, -1), (4, -4, 9)),
    ((2, 0, 10), (-2, 6, 6), (-2, 6, -1), (4, -4, 9)),
)
QUINTIC = (
    ((5, 1, -5, 7, 4), (3, -3, -1, 3, 8), (5, -3, 5, -6, 2), (3, -1, 3, 2, 2)),
    ((5, 1, -5, 7, 4), (3, -1, -3, 3, 8), (3, -3, 5, -6, 4), (1, -1, 3, 2, 4)),
    ((5, 1, -5, 7, 4), (3, -1, -3, 3, 8), (3, -3, 5, -6, 4), (3, -1, 1, 4, 2)),
)


def residual(sequences):
    return [sum(sum(seq[i] * seq[i + d] for i in range(len(seq) - d)) for seq in sequences)
            for d in range(1, 84)]


def compression(seq, modulus):
    return tuple(sum(seq[r::modulus]) for r in range(modulus))


def solve_pair(seed, cubic, quintic, seconds, workers, pair_id):
    rows = [sum(seq) for seq in seed]
    alts = [sum(x if i % 2 == 0 else -x for i, x in enumerate(seq)) for seq in seed]
    z4 = [(sum(seq[0::4]) - sum(seq[2::4]), sum(seq[1::4]) - sum(seq[3::4])) for seq in seed]
    model = cp_model.CpModel()
    bits = [[model.new_bool_var(f"x_{k}_{i}") for i in range(length)]
            for k, length in enumerate(LENS)]
    signs = [[1 - 2 * bit for bit in row] for row in bits]
    for row, seq in zip(bits, seed):
        for bit, value in zip(row, seq):
            model.add_hint(bit, int(value == -1))
    for k in range(4):
        model.add(sum(signs[k]) == rows[k])
        model.add(sum((1 if i % 2 == 0 else -1) * signs[k][i] for i in range(LENS[k])) == alts[k])
        model.add(sum((1 if i % 4 == 0 else -1) * signs[k][i]
                      for i in range(LENS[k]) if i % 2 == 0) == z4[k][0])
        model.add(sum((1 if i % 4 == 1 else -1) * signs[k][i]
                      for i in range(LENS[k]) if i % 2 == 1) == z4[k][1])
        for r, target in enumerate(cubic[k]):
            model.add(sum(signs[k][i] for i in range(r, LENS[k], 3)) == target)
        for r, target in enumerate(quintic[k]):
            model.add(sum(signs[k][i] for i in range(r, LENS[k], 5)) == target)
    for d in range(1, 84):
        odd = []
        for row in bits:
            incidence = [0] * len(row)
            for i in range(len(row) - d):
                incidence[i] ^= 1
                incidence[i + d] ^= 1
            odd.extend(bit for bit, flag in zip(row, incidence) if flag)
        model.add_bool_xor(odd)
    changed = [bit if value == 1 else bit.Not()
               for row, seq in zip(bits, seed) for bit, value in zip(row, seq)]
    model.minimize(sum(changed))
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = seconds
    solver.parameters.num_search_workers = workers
    solver.parameters.random_seed = 668000 + pair_id
    status = solver.solve(model)
    result = {
        "pair": pair_id,
        "cubic_index": pair_id // 3 + 1,
        "quintic_index": pair_id % 3 + 1,
        "status": solver.status_name(status),
        "cubic": cubic,
        "quintic": quintic,
    }
    if status not in (cp_model.FEASIBLE, cp_model.OPTIMAL):
        return result
    sequences = [[-1 if solver.value(bit) else 1 for bit in row] for row in bits]
    r = residual(sequences)
    assert all(x % 4 == 0 for x in r)
    assert [compression(seq, 3) for seq in sequences] == list(cubic)
    assert [compression(seq, 5) for seq in sequences] == list(quintic)
    assert [sum(seq) for seq in sequences] == rows
    result.update({
        "independently_recomputed": True,
        "hamming_changes": int(solver.objective_value),
        "best_bound": int(solver.best_objective_bound),
        "energy": sum(x * x for x in r),
        "l1": sum(abs(x) for x in r),
        "parity_bad": sum(x % 4 != 0 for x in r),
        "residual": r,
        "sequences": sequences,
    })
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("--seconds", type=float, default=30)
    parser.add_argument("--workers", type=int, default=4)
    parser.add_argument("--output", type=Path, default=Path("agent_bp2_ranked_c8q8.json"))
    args = parser.parse_args()
    seed = json.loads(args.input.read_text(encoding="utf-8"))["sequences"]
    results = []
    for ci, cubic in enumerate(CUBIC):
        for qi, quintic in enumerate(QUINTIC):
            pair_id = ci * 3 + qi
            result = solve_pair(seed, cubic, quintic, args.seconds, args.workers, pair_id)
            results.append(result)
            print(json.dumps({k: result.get(k) for k in
                              ("pair", "cubic_index", "quintic_index", "status",
                               "hamming_changes", "energy", "l1")}))
    results.sort(key=lambda x: (
        "hamming_changes" not in x,
        x.get("hamming_changes", 10**9),
        x.get("energy", 10**9),
        x["pair"],
    ))
    args.output.write_text(json.dumps({"source": str(args.input), "ranking": results},
                                      separators=(",", ":")) + "\n", encoding="utf-8")
    print("RANKING")
    for rank, result in enumerate(results, 1):
        print(rank, result["cubic_index"], result["quintic_index"], result["status"],
              result.get("hamming_changes"), result.get("energy"), result.get("l1"))


if __name__ == "__main__":
    main()
