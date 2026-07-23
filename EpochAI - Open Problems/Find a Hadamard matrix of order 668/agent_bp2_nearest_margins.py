"""Exact nearest feasible order-3/order-5 compression margins for BS seeds.

Component bounds and parities come from residue-class cardinalities.  Row sums
are held fixed.  The increasing L1-radius dynamic program proves minimality of
the first returned tuple; it is not a heuristic projection.
"""

from __future__ import annotations

import json
import sys


LENS = (84, 84, 83, 83)


def compression(seq: list[int], modulus: int) -> tuple[int, ...]:
    return tuple(sum(seq[i] for i in range(r, len(seq), modulus)) for r in range(modulus))


def counts(length: int, modulus: int) -> tuple[int, ...]:
    return tuple(len(range(r, length, modulus)) for r in range(modulus))


def cubic_value(v: tuple[int, int, int]) -> int:
    a, b, c = v
    return a * a + b * b + c * c - a * b - b * c - c * a


def quintic_value(v: tuple[int, ...]) -> tuple[int, int]:
    s0 = sum(x * x for x in v)
    s1 = sum(v[i] * v[(i + 1) % 5] for i in range(5))
    s2 = sum(v[i] * v[(i + 2) % 5] for i in range(5))
    return s0 - s1, s1 - s2


def septimal_value(v: tuple[int, ...]) -> tuple[int, int, int]:
    correlations = [sum(v[i] * v[(i + d) % 7] for i in range(7)) for d in range(4)]
    return tuple(correlations[d] - correlations[d + 1] for d in range(3))


def order11_value(v: tuple[int, ...]) -> tuple[int, ...]:
    correlations = [sum(v[i] * v[(i + d) % 11] for i in range(11)) for d in range(7)]
    return tuple(correlations[d] - correlations[d + 1] for d in range(6))


def local_tuples(base: tuple[int, ...], caps: tuple[int, ...], radius: int):
    """All bounded parity-feasible tuples with same sum and L1 <= radius."""
    m = len(base)
    prefix: list[int] = []

    def visit(index: int, used: int, total_delta: int):
        if index == m - 1:
            last = -total_delta
            if last % 2 or used + abs(last) > radius:
                return
            value = base[index] + last
            if not (-caps[index] <= value <= caps[index]) or (value - caps[index]) % 2:
                return
            delta = tuple(prefix + [last])
            out = tuple(base[i] + delta[i] for i in range(m))
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


def nearest(
    bases: list[tuple[int, ...]],
    capsets: list[tuple[int, ...]],
    value,
    target,
    max_radius: int = 40,
):
    def add_keys(a, b):
        return a + b if isinstance(target, int) else tuple(x + y for x, y in zip(a, b))

    def subtract_keys(a, b):
        return a - b if isinstance(target, int) else tuple(x - y for x, y in zip(a, b))

    for radius in range(0, max_radius + 1, 2):
        per_sequence = []
        for base, caps in zip(bases, capsets):
            best = {}
            for cost, tup in local_tuples(base, caps, radius):
                key = value(tup)
                old = best.get(key)
                if old is None or cost < old[0]:
                    best[key] = (cost, tup)
            per_sequence.append(best)

        def pair_table(left, right):
            paired = {}
            left_by_cost = {}
            right_by_cost = {}
            for key, value in left.items():
                left_by_cost.setdefault(value[0], []).append((key, value[1]))
            for key, value in right.items():
                right_by_cost.setdefault(value[0], []).append((key, value[1]))
            for lc, left_group in left_by_cost.items():
                for rc, right_group in right_by_cost.items():
                    cost = lc + rc
                    if cost > radius:
                        continue
                    for lk, lt in left_group:
                        for rk, rt in right_group:
                            key = add_keys(lk, rk)
                            old = paired.get(key)
                            if old is None or cost < old[0]:
                                paired[key] = (cost, [lt, rt])
            return paired

        left = pair_table(per_sequence[0], per_sequence[1])
        right = pair_table(per_sequence[2], per_sequence[3])
        answer = None
        for key, (lc, lt) in left.items():
            needed = subtract_keys(target, key)
            if needed not in right:
                continue
            rc, rt = right[needed]
            if lc + rc <= radius and (answer is None or lc + rc < answer[0]):
                answer = (lc + rc, lt + rt)
        if answer is not None:
            cost, tuples = answer
            return {"l1": cost, "radius_proving_minimality": radius, "tuples": tuples}
    return None


def main() -> None:
    path = sys.argv[1] if len(sys.argv) > 1 else "agent_bp2_fourier_e1056_verified.json"
    with open(path, "r", encoding="utf-8") as handle:
        data = json.load(handle)
    seqs = data["sequences"]
    assert tuple(map(len, seqs)) == LENS
    assert all(x in (-1, 1) for seq in seqs for x in seq)

    c3 = [compression(seq, 3) for seq in seqs]
    n3 = [counts(length, 3) for length in LENS]
    c5 = [compression(seq, 5) for seq in seqs]
    n5 = [counts(length, 5) for length in LENS]
    c7 = [compression(seq, 7) for seq in seqs]
    n7 = [counts(length, 7) for length in LENS]
    c11 = [compression(seq, 11) for seq in seqs]
    n11 = [counts(length, 11) for length in LENS]
    rows = [sum(seq) for seq in seqs]
    assert ([sum(v) for v in c3] == rows == [sum(v) for v in c5] ==
            [sum(v) for v in c7] == [sum(v) for v in c11])

    current3 = sum(cubic_value(v) for v in c3)
    current5 = tuple(sum(quintic_value(v)[j] for v in c5) for j in range(2))
    current7 = tuple(sum(septimal_value(v)[j] for v in c7) for j in range(3))
    current11 = tuple(sum(order11_value(v)[j] for v in c11) for j in range(6))
    result3 = nearest(c3, n3, cubic_value, 334, max_radius=24)
    result5 = nearest(c5, n5, quintic_value, (334, 0), max_radius=40)
    result7 = nearest(c7, n7, septimal_value, (334, 0, 0), max_radius=40)
    result11 = nearest(c11, n11, order11_value, (334, 0, 0, 0, 0, 0), max_radius=24)
    out = {
        "source": path,
        "row_sums": rows,
        "order3": {"current": c3, "current_value": current3, "nearest_exact": result3},
        "order5": {"current": c5, "current_value": current5, "nearest_exact": result5},
        "order7": {"current": c7, "current_value": current7, "nearest_exact": result7},
        "order11": {"current": c11, "current_value": current11, "nearest_exact": result11},
    }
    print(json.dumps(out, indent=2))


if __name__ == "__main__":
    main()
