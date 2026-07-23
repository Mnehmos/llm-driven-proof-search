"""Exact order-11 margin search through total L1 radius 16.

The four compressed sequences retain their row sums, coordinate parities, and
coordinate bounds.  Since those constraints force every local L1 cost to be a
multiple of four, radius 16 has only a handful of cost-allocation patterns.
Matching those patterns separately avoids constructing the huge unrestricted
pair table while remaining exhaustive.
"""

from __future__ import annotations

import itertools
import json
import sys
import time

from agent_bp2_nearest_margins import (
    LENS,
    compression,
    counts,
    local_tuples,
    order11_value,
)


TARGET = (334, 0, 0, 0, 0, 0)


def add(a: tuple[int, ...], b: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(x + y for x, y in zip(a, b))


def sub(a: tuple[int, ...], b: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(x - y for x, y in zip(a, b))


def allocations(total: int, allowed: tuple[int, ...]):
    for costs in itertools.product(allowed, repeat=4):
        if sum(costs) == total:
            yield costs


def match_allocation(groups, costs):
    """Meet four exact-cost groups using the cheapest of three 2+2 splits."""
    if any(cost not in groups[i] for i, cost in enumerate(costs)):
        return None
    tables = [groups[i][costs[i]] for i in range(4)]
    splits = [((0, 1), (2, 3)), ((0, 2), (1, 3)), ((0, 3), (1, 2))]
    split = min(
        splits,
        key=lambda s: len(tables[s[0][0]]) * len(tables[s[0][1]])
        + len(tables[s[1][0]]) * len(tables[s[1][1]]),
    )
    (a, b), (c, d) = split
    left = {}
    for ka, ta in tables[a].items():
        for kb, tb in tables[b].items():
            left.setdefault(add(ka, kb), (ta, tb))
    for kc, tc in tables[c].items():
        for kd, td in tables[d].items():
            hit = left.get(sub(TARGET, add(kc, kd)))
            if hit is None:
                continue
            out = [None] * 4
            out[a], out[b] = hit
            out[c], out[d] = tc, td
            return out
    return None


def main() -> None:
    source = (
        sys.argv[1]
        if len(sys.argv) > 1
        else "agent_bp2_spectral_projection_e2784_o7flex8.json"
    )
    with open(source, "r", encoding="utf-8") as handle:
        data = json.load(handle)
    seqs = data["sequences"]
    assert tuple(map(len, seqs)) == LENS
    bases = [compression(seq, 11) for seq in seqs]
    capsets = [counts(length, 11) for length in LENS]
    current = tuple(sum(order11_value(v)[j] for v in bases) for j in range(6))
    print(json.dumps({"source": source, "bases": bases, "current": current}), flush=True)

    # Keep one minimum-cost tuple per invariant vector through local radius 12.
    groups = []
    for i, (base, caps) in enumerate(zip(bases, capsets)):
        started = time.time()
        best = {}
        for cost, tup in local_tuples(base, caps, 12):
            key = order11_value(tup)
            old = best.get(key)
            if old is None or cost < old[0]:
                best[key] = (cost, tup)
        by_cost = {}
        for key, (cost, tup) in best.items():
            by_cost.setdefault(cost, {})[key] = tup
        groups.append(by_cost)
        print(
            json.dumps(
                {
                    "sequence": i,
                    "seconds": time.time() - started,
                    "unique_by_min_cost": {str(k): len(v) for k, v in by_cost.items()},
                }
            ),
            flush=True,
        )

    # These calls independently re-establish that no total below 16 works.
    for total in (0, 4, 8, 12, 16):
        started = time.time()
        tested = 0
        for costs in allocations(total, (0, 4, 8, 12)):
            tested += 1
            answer = match_allocation(groups, costs)
            if answer is not None:
                print(
                    json.dumps(
                        {
                            "l1": total,
                            "costs": costs,
                            "tuples": answer,
                            "allocation_patterns_tested": tested,
                        },
                        indent=2,
                    )
                )
                return
        print(
            json.dumps(
                {"excluded_total_l1": total, "patterns": tested, "seconds": time.time() - started}
            ),
            flush=True,
        )

    # The remaining total-16 patterns have one local cost 16 and three zeros.
    zero_values = [order11_value(base) for base in bases]
    for i, (base, caps) in enumerate(zip(bases, capsets)):
        needed = TARGET
        for j, value in enumerate(zero_values):
            if i != j:
                needed = sub(needed, value)
        started = time.time()
        tested = 0
        for cost, tup in local_tuples(base, caps, 16):
            if cost != 16:
                continue
            tested += 1
            if order11_value(tup) != needed:
                continue
            answer = list(bases)
            answer[i] = tup
            print(
                json.dumps(
                    {
                        "l1": 16,
                        "costs": [16 if j == i else 0 for j in range(4)],
                        "tuples": answer,
                        "streamed_cost16": tested,
                    },
                    indent=2,
                )
            )
            return
        print(
            json.dumps(
                {"excluded_cost16_sequence": i, "tuples": tested, "seconds": time.time() - started}
            ),
            flush=True,
        )
    print(json.dumps({"nearest_exact": None, "proved_through_l1": 16}), flush=True)


if __name__ == "__main__":
    main()
