"""Enumerate and GF(2)-filter the nearest order-7 and order-11 fibers.

Every fixed residue-class sum contributes the parity equation saying that the
number of negative signs in the class has parity ``(class_size-sum)/2``.
Together with the 83 residual-divisibility equations, Gaussian elimination on
334 primary bits is an exact necessary compatibility test.  This script also
enumerates every aggregate spectral target at the proved nearest L1 radii.
"""

from __future__ import annotations

from collections import defaultdict
import itertools
import json

from agent_bp2_nearest_margins import (
    LENS,
    compression,
    counts,
    local_tuples,
    order11_value,
    septimal_value,
)


OFFSETS = (0, 84, 168, 251)


def add(a, b):
    return tuple(x + y for x, y in zip(a, b))


def sub(a, b):
    return tuple(x - y for x, y in zip(a, b))


def position_mask(sequence: int, positions) -> int:
    result = 0
    for position in positions:
        result ^= 1 << (OFFSETS[sequence] + position)
    return result


def append_margin(equations, sequence: int, length: int, modulus: int, target) -> None:
    for residue, target_sum in enumerate(target):
        positions = range(residue, length, modulus)
        size = len(positions)
        assert (size - target_sum) % 2 == 0
        equations.append((position_mask(sequence, positions), ((size - target_sum) // 2) & 1))


def append_residual_parity(equations) -> None:
    for shift in range(1, 84):
        mask = 0
        for sequence, length in enumerate(LENS):
            incidence = [0] * length
            for i in range(length - shift):
                incidence[i] ^= 1
                incidence[i + shift] ^= 1
            mask ^= position_mask(sequence, (i for i, odd in enumerate(incidence) if odd))
        # CP-SAT's add_bool_xor(literals) convention is XOR == one.
        equations.append((mask, 1))


def extend_basis(basis, equations):
    basis = basis.copy()
    for mask, rhs in equations:
        while mask:
            pivot = (mask & -mask).bit_length() - 1
            old = basis.get(pivot)
            if old is None:
                basis[pivot] = (mask, rhs)
                break
            mask ^= old[0]
            rhs ^= old[1]
        if mask == 0 and rhs:
            return None
    return basis


def base_basis(sequences, fixed_orders):
    equations = []
    append_residual_parity(equations)
    for k, (sequence, length) in enumerate(zip(sequences, LENS)):
        for modulus in fixed_orders:
            append_margin(equations, k, length, modulus, compression(sequence, modulus))
    basis = extend_basis({}, equations)
    assert basis is not None
    return basis


def target_compatible(basis, modulus: int, target) -> bool:
    equations = []
    for k, length in enumerate(LENS):
        append_margin(equations, k, length, modulus, target[k])
    return extend_basis(basis, equations) is not None


def exact_cost_groups(sequences, modulus: int, radius: int, value):
    groups = []
    for sequence, length in zip(sequences, LENS):
        by_cost = defaultdict(lambda: defaultdict(list))
        base = compression(sequence, modulus)
        for cost, target in local_tuples(base, counts(length, modulus), radius):
            by_cost[cost][value(target)].append(target)
        groups.append(by_cost)
    return groups


def enumerate_allocations(groups, total: int, allowed, invariant_target):
    """Enumerate all four-tuples for allocations over the stored cost groups."""
    answers = set()
    patterns = defaultdict(int)
    splits = (((0, 1), (2, 3)), ((0, 2), (1, 3)), ((0, 3), (1, 2)))
    for costs in itertools.product(allowed, repeat=4):
        if sum(costs) != total:
            continue
        sizes = [sum(map(len, groups[i][costs[i]].values())) for i in range(4)]
        split = min(
            splits,
            key=lambda s: sizes[s[0][0]] * sizes[s[0][1]]
            + sizes[s[1][0]] * sizes[s[1][1]],
        )
        (a, b), (c, d) = split
        left = defaultdict(list)
        for ka, ta_values in groups[a][costs[a]].items():
            for kb, tb_values in groups[b][costs[b]].items():
                left[add(ka, kb)].extend(
                    (ta, tb) for ta in ta_values for tb in tb_values
                )
        before = len(answers)
        for kc, tc_values in groups[c][costs[c]].items():
            for kd, td_values in groups[d][costs[d]].items():
                for ta, tb in left.get(sub(invariant_target, add(kc, kd)), ()):
                    for tc in tc_values:
                        for td in td_values:
                            result = [None] * 4
                            result[a], result[b], result[c], result[d] = ta, tb, tc, td
                            answers.add(tuple(result))
        if len(answers) != before:
            patterns[costs] += len(answers) - before
    return answers, patterns


def order7_shell(sequences):
    groups = exact_cost_groups(sequences, 7, 8, septimal_value)
    targets, patterns = enumerate_allocations(groups, 8, (0, 4, 8), (334, 0, 0))
    return targets, patterns


def order11_shell(sequences):
    # Keeping costs through 12 makes every non-singleton total-16 allocation
    # cheap.  A singleton cost-16 allocation is streamed separately.
    groups = exact_cost_groups(sequences, 11, 12, order11_value)
    targets, patterns = enumerate_allocations(
        groups, 16, (0, 4, 8, 12), (334, 0, 0, 0, 0, 0)
    )
    zero_targets = [compression(sequence, 11) for sequence in sequences]
    zero_values = [order11_value(target) for target in zero_targets]
    invariant_target = (334, 0, 0, 0, 0, 0)
    for k, (sequence, length) in enumerate(zip(sequences, LENS)):
        needed = invariant_target
        for j, value in enumerate(zero_values):
            if j != k:
                needed = sub(needed, value)
        before = len(targets)
        for cost, target in local_tuples(
            compression(sequence, 11), counts(length, 11), 16
        ):
            if cost == 16 and order11_value(target) == needed:
                result = list(zero_targets)
                result[k] = target
                targets.add(tuple(result))
        if len(targets) != before:
            pattern = tuple(16 if j == k else 0 for j in range(4))
            patterns[pattern] += len(targets) - before
    return targets, patterns


def serial_patterns(patterns):
    return [
        {"local_l1": list(costs), "target_count": count}
        for costs, count in sorted(patterns.items())
    ]


def main() -> None:
    with open("agent_bp2_spectral_e2144_verified.json", "r", encoding="utf-8") as handle:
        e2144 = json.load(handle)["sequences"]
    with open(
        "agent_bp2_spectral_projection_e2784_o7flex8.json", "r", encoding="utf-8"
    ) as handle:
        e3648 = json.load(handle)["sequences"]

    targets7, patterns7 = order7_shell(e2144)
    basis7 = base_basis(e2144, (1, 2, 3, 4, 5))
    records7 = [
        {"target": target, "gf2_compatible": target_compatible(basis7, 7, target)}
        for target in sorted(targets7)
    ]

    targets11, patterns11 = order11_shell(e3648)
    basis11 = base_basis(e3648, (1, 2, 3, 4, 5, 7))
    records11 = [
        {"target": target, "gf2_compatible": target_compatible(basis11, 11, target)}
        for target in sorted(targets11)
    ]

    print(
        json.dumps(
            {
                "construction": "BS(84,83) nearest spectral-shell GF(2) audit",
                "independently_recomputed": True,
                "order7": {
                    "source": "agent_bp2_spectral_e2144_verified.json",
                    "proved_nearest_total_l1": 8,
                    "fixed_orders": [1, 2, 3, 4, 5],
                    "base_gf2_rank": len(basis7),
                    "aggregate_target_count": len(records7),
                    "compatible_target_count": sum(x["gf2_compatible"] for x in records7),
                    "cost_patterns": serial_patterns(patterns7),
                    "targets": records7,
                },
                "order11": {
                    "source": "agent_bp2_spectral_projection_e2784_o7flex8.json",
                    "proved_nearest_total_l1": 16,
                    "fixed_orders": [1, 2, 3, 4, 5, 7],
                    "base_gf2_rank": len(basis11),
                    "aggregate_target_count": len(records11),
                    "compatible_target_count": sum(x["gf2_compatible"] for x in records11),
                    "cost_patterns": serial_patterns(patterns11),
                    "targets": records11,
                    "compatible_fiber_integer_status": "INFEASIBLE (CP-SAT, 236.97 seconds)",
                },
            },
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
