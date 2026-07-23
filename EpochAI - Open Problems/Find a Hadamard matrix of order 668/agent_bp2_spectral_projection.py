"""Project the E1056 BS seed into simultaneous exact low-order spectral margins.

All 83 autocorrelation mod-4 equations, the seed's exact row/alternating/z=i
components, and the independently derived nearest exact order-3/order-5
compression tuples are imposed as hard linear constraints.  The objective is
minimum Hamming distance from the verified seed.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from ortools.sat.python import cp_model


LENS = (84, 84, 83, 83)
TARGET3_E1056 = (
    (0, 0, -10),
    (0, 4, 8),
    (2, -6, -5),
    (-8, 0, 5),
)
TARGET5_E1056 = (
    (-7, 5, -1, -3, -4),
    (9, 5, 1, 1, -4),
    (-3, -3, 1, 0, -4),
    (-3, 5, -1, -6, 2),
)
TARGET3_E896 = (
    (0, 2, 10),
    (-2, 6, 6),
    (-2, 6, -1),
    (4, -4, 9),
)
TARGET5_E896 = (
    (5, 1, -5, 7, 4),
    (3, -3, -1, 3, 8),
    (3, -3, 5, -6, 4),
    (1, -1, 3, 2, 4),
)
TARGET7_E896 = (
    (-2, -2, 8, 0, 6, 0, 2),
    (4, 2, 4, 4, 2, -2, -4),
    (2, -2, -4, 2, 6, -2, 1),
    (2, -6, 4, 2, 2, 2, 3),
)
TARGET3_E2784 = (
    (0, 0, 6),
    (4, 0, -4),
    (-4, -4, -9),
    (-6, -6, 9),
)
TARGET5_E2784 = (
    (-3, -1, 7, -1, 4),
    (1, 7, -1, -7, 0),
    (-9, -1, -5, -2, 0),
    (3, -3, -5, 2, 0),
)
TARGET7_E2784 = (
    (-4, 0, 2, 2, 8, -2, 0),
    (-2, -4, 2, -4, 6, 0, 2),
    (2, 2, -6, -4, 0, -6, -5),
    (2, 0, -4, -2, 2, 2, -3),
)
TARGET11_E3648 = (
    (-2, 2, 4, -2, -2, -2, 6, 1, -1, 3, -1),
    (4, 0, 0, -6, 2, 0, -2, -3, -1, 3, 3),
    (-2, 0, 0, -4, -2, -4, 3, -5, 1, -1, -3),
    (-4, -2, -2, -2, 4, -2, 1, 5, -1, 1, -1),
)
TARGET7_E2144 = (
    (-2, 0, -2, 0, 0, 2, 2),
    (4, -4, -4, 6, 2, 2, 0),
    (-6, 2, 4, 0, -2, -2, 1),
    (-4, -4, -10, 2, -4, 0, 3),
)


def residual(sequences: list[list[int]]) -> list[int]:
    return [
        sum(sum(seq[i] * seq[i + d] for i in range(len(seq) - d)) for seq in sequences)
        for d in range(1, 84)
    ]


def compression(seq: list[int], modulus: int) -> tuple[int, ...]:
    return tuple(sum(seq[r::modulus]) for r in range(modulus))


def residue_counts(length: int, modulus: int) -> tuple[int, ...]:
    return tuple(len(range(r, length, modulus)) for r in range(modulus))


def local_tuples(base: tuple[int, ...], caps: tuple[int, ...], radius: int):
    prefix: list[int] = []

    def visit(index: int, used: int, total_delta: int):
        if index == len(base) - 1:
            last = -total_delta
            if last % 2 or used + abs(last) > radius:
                return
            value = base[index] + last
            if -caps[index] <= value <= caps[index] and (value - caps[index]) % 2 == 0:
                out = tuple(base[i] + (prefix + [last])[i] for i in range(len(base)))
                yield used + abs(last), out
            return
        remaining = radius - used
        for change in range(-remaining, remaining + 1, 2):
            value = base[index] + change
            if not (-caps[index] <= value <= caps[index]) or (value - caps[index]) % 2:
                continue
            prefix.append(change)
            yield from visit(index + 1, used + abs(change), total_delta + change)
            prefix.pop()

    yield from visit(0, 0, 0)


def spectral5(values: tuple[int, ...]) -> tuple[int, int]:
    s0 = sum(x * x for x in values)
    s1 = sum(values[i] * values[(i + 1) % 5] for i in range(5))
    s2 = sum(values[i] * values[(i + 2) % 5] for i in range(5))
    return s0 - s1, s1 - s2


def spectral7(values: tuple[int, ...]) -> tuple[int, int, int]:
    s = [sum(values[i] * values[(i + d) % 7] for i in range(7)) for d in range(4)]
    return s[0] - s[1], s[1] - s[2], s[2] - s[3]


def spectral11(values: tuple[int, ...]) -> tuple[int, ...]:
    s = [sum(values[i] * values[(i + d) % 11] for i in range(11)) for d in range(7)]
    return tuple(s[d] - s[d + 1] for d in range(6))


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("--seconds", type=float, default=300)
    parser.add_argument("--workers", type=int, default=4)
    parser.add_argument("--profile", choices=("e1056", "e896", "e2144", "e2784", "e3648"), default="e1056")
    parser.add_argument("--order7", action="store_true",
                        help="also impose the nearest exact order-7 tuple (e896 profile only)")
    parser.add_argument("--order7-flex-radius", type=int, default=0,
                        help="choose any fixed-row/parity order-7 tuple in this total L1 radius")
    parser.add_argument("--order11", action="store_true",
                        help="impose the proved-nearest exact order-11 tuple (e3648 profile only)")
    parser.add_argument("--order11-flex-local4", action="store_true",
                        help="choose any exact order-11 tuple with local L1 at most 4 per sequence")
    parser.add_argument("--output", type=Path, default=Path("agent_bp2_spectral_projection.json"))
    args = parser.parse_args()
    payload = json.loads(args.input.read_text(encoding="utf-8"))
    seed = payload["sequences"]
    if tuple(map(len, seed)) != LENS or any(x not in (-1, 1) for seq in seed for x in seq):
        raise ValueError("expected four +/-1 sequences of lengths 84,84,83,83")

    rows = [sum(seq) for seq in seed]
    alts = [sum(x if i % 2 == 0 else -x for i, x in enumerate(seq)) for seq in seed]
    z4 = [
        (sum(seq[0::4]) - sum(seq[2::4]), sum(seq[1::4]) - sum(seq[3::4]))
        for seq in seed
    ]
    target11 = None
    if args.profile == "e896":
        target3, target5, target7 = TARGET3_E896, TARGET5_E896, TARGET7_E896
    elif args.profile == "e2144":
        target3 = tuple(compression(seq, 3) for seq in seed)
        target5 = tuple(compression(seq, 5) for seq in seed)
        target7 = TARGET7_E2144
    elif args.profile == "e3648":
        target3, target5 = TARGET3_E2784, TARGET5_E2784
        target7 = tuple(compression(seq, 7) for seq in seed)
        target11 = TARGET11_E3648
    elif args.profile == "e2784":
        target3, target5, target7 = TARGET3_E2784, TARGET5_E2784, TARGET7_E2784
    else:
        target3, target5, target7 = TARGET3_E1056, TARGET5_E1056, None
    if args.order7 and target7 is None:
        raise ValueError("the order-7 target is not defined for this profile")
    if args.order7 and args.order7_flex_radius:
        raise ValueError("choose hard --order7 or --order7-flex-radius, not both")
    if args.order11 and target11 is None:
        raise ValueError("the order-11 target is defined only for the e3648 profile")
    if args.order11_flex_local4 and args.profile != "e3648":
        raise ValueError("flexible order-11 projection is defined only for the e3648 profile")
    if args.order11 and args.order11_flex_local4:
        raise ValueError("choose hard --order11 or --order11-flex-local4, not both")
    assert sum(x * x for x in rows) == 334
    assert sum(x * x for x in alts) == 334
    assert sum(x * x + y * y for x, y in z4) == 334
    assert sum(sum(x * x for x in v) - v[0] * v[1] - v[1] * v[2] - v[2] * v[0]
               for v in target3) == 334
    assert tuple(sum(spectral5(v)[j] for v in target5) for j in range(2)) == (334, 0)
    if args.order7:
        assert tuple(sum(spectral7(v)[j] for v in target7) for j in range(3)) == (334, 0, 0)
    if args.order11:
        assert tuple(sum(spectral11(v)[j] for v in target11) for j in range(6)) == (334, 0, 0, 0, 0, 0)

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
        for r, target in enumerate(target3[k]):
            model.add(sum(signs[k][i] for i in range(r, LENS[k], 3)) == target)
        for r, target in enumerate(target5[k]):
            model.add(sum(signs[k][i] for i in range(r, LENS[k], 5)) == target)
        if args.order7:
            for r, target in enumerate(target7[k]):
                model.add(sum(signs[k][i] for i in range(r, LENS[k], 7)) == target)
        if args.order11:
            for r, target in enumerate(target11[k]):
                model.add(sum(signs[k][i] for i in range(r, LENS[k], 11)) == target)

    if args.order7_flex_radius:
        base7 = [compression(seq, 7) for seq in seed]
        cap7 = [residue_counts(length, 7) for length in LENS]
        selected_costs = []
        candidate_sets = []
        selector_sets = []
        for k in range(4):
            candidates = list(local_tuples(base7[k], cap7[k], args.order7_flex_radius))
            selectors = [model.new_bool_var(f"o7_{k}_{j}") for j in range(len(candidates))]
            candidate_sets.append(candidates)
            selector_sets.append(selectors)
            model.add_exactly_one(selectors)
            for r in range(7):
                model.add(sum(signs[k][i] for i in range(r, LENS[k], 7)) ==
                          sum(selectors[j] * candidates[j][1][r] for j in range(len(candidates))))
            for j, (cost, _) in enumerate(candidates):
                selected_costs.append(cost * selectors[j])
        for invariant in range(3):
            target = 334 if invariant == 0 else 0
            model.add(sum(
                selector_sets[k][j] * spectral7(candidate_sets[k][j][1])[invariant]
                for k in range(4)
                for j in range(len(candidate_sets[k]))
            ) == target)
        model.add(sum(selected_costs) <= args.order7_flex_radius)

    if args.order11_flex_local4:
        base11 = [compression(seq, 11) for seq in seed]
        cap11 = [residue_counts(length, 11) for length in LENS]
        selected_costs11 = []
        candidate_sets11 = []
        selector_sets11 = []
        for k in range(4):
            candidates = list(local_tuples(base11[k], cap11[k], 4))
            selectors = [model.new_bool_var(f"o11_{k}_{j}") for j in range(len(candidates))]
            candidate_sets11.append(candidates)
            selector_sets11.append(selectors)
            model.add_exactly_one(selectors)
            for r in range(11):
                model.add(sum(signs[k][i] for i in range(r, LENS[k], 11)) ==
                          sum(selectors[j] * candidates[j][1][r] for j in range(len(candidates))))
            for j, (cost, _) in enumerate(candidates):
                selected_costs11.append(cost * selectors[j])
        for invariant in range(6):
            target = 334 if invariant == 0 else 0
            model.add(sum(
                selector_sets11[k][j] * spectral11(candidate_sets11[k][j][1])[invariant]
                for k in range(4)
                for j in range(len(candidate_sets11[k]))
            ) == target)
        model.add(sum(selected_costs11) <= 16)

    for d in range(1, 84):
        odd_vertices = []
        for row in bits:
            incidence = [0] * len(row)
            for i in range(len(row) - d):
                incidence[i] ^= 1
                incidence[i + d] ^= 1
            odd_vertices.extend(bit for bit, odd in zip(row, incidence) if odd)
        model.add_bool_xor(odd_vertices)

    changed = [bit if value == 1 else bit.Not()
               for row, seq in zip(bits, seed) for bit, value in zip(row, seq)]
    model.minimize(sum(changed))
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = args.seconds
    solver.parameters.num_search_workers = args.workers
    solver.parameters.random_seed = 6681056
    solver.parameters.log_search_progress = True
    status = solver.solve(model)
    if status not in (cp_model.FEASIBLE, cp_model.OPTIMAL):
        print(json.dumps({"status": solver.status_name(status)}))
        return 2

    sequences = [[-1 if solver.value(bit) else 1 for bit in row] for row in bits]
    r = residual(sequences)
    assert all(x % 4 == 0 for x in r)
    assert [compression(seq, 3) for seq in sequences] == list(target3)
    assert [compression(seq, 5) for seq in sequences] == list(target5)
    if args.order7:
        assert [compression(seq, 7) for seq in sequences] == list(target7)
    if args.order11:
        assert [compression(seq, 11) for seq in sequences] == list(target11)
    actual7 = [compression(seq, 7) for seq in sequences]
    if args.order7_flex_radius:
        assert tuple(sum(spectral7(v)[j] for v in actual7) for j in range(3)) == (334, 0, 0)
        assert sum(sum(abs(a - b) for a, b in zip(x, y)) for x, y in zip(actual7, base7)) <= args.order7_flex_radius
    actual11 = [compression(seq, 11) for seq in sequences]
    if args.order11_flex_local4:
        assert tuple(sum(spectral11(v)[j] for v in actual11) for j in range(6)) == (334, 0, 0, 0, 0, 0)
        assert all(sum(abs(a - b) for a, b in zip(x, y)) <= 4 for x, y in zip(actual11, base11))
    assert [sum(seq) for seq in sequences] == rows
    assert [sum(x if i % 2 == 0 else -x for i, x in enumerate(seq)) for seq in sequences] == alts
    result = {
        "construction": "base sequences BS(84,83)",
        "search": "agent_bp2 simultaneous spectral-margin CP-SAT projection",
        "status": solver.status_name(status),
        "solved": not any(r),
        "independently_recomputed": True,
        "hamming_changes": int(solver.objective_value),
        "energy": sum(x * x for x in r),
        "l1": sum(abs(x) for x in r),
        "parity_bad": sum(x % 4 != 0 for x in r),
        "row_sums": rows,
        "alternating_sums": alts,
        "z4_components": [x for pair in z4 for x in pair],
        "order3_compression": target3,
        "order5_compression": target5,
        "order7_compression": actual7 if (args.order7 or args.order7_flex_radius) else None,
        "order11_compression": actual11 if (args.order11 or args.order11_flex_local4) else None,
        "residual": r,
        "sequences": sequences,
    }
    args.output.write_text(json.dumps(result, separators=(",", ":")) + "\n", encoding="utf-8")
    print(json.dumps({key: result[key] for key in ("status", "hamming_changes", "energy", "l1", "solved")}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
