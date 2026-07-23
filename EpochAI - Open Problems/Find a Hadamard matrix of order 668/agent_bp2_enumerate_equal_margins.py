"""Enumerate all equal-minimum cubic/quintic margins around a BS seed."""

from __future__ import annotations

import itertools
import json
import sys

from agent_bp2_nearest_margins import (
    LENS,
    compression,
    counts,
    cubic_value,
    local_tuples,
    quintic_value,
)


def enumerate_targets(bases, capsets, value, target, radius):
    candidates = [list(local_tuples(base, caps, radius)) for base, caps in zip(bases, capsets)]
    answers = set()

    def visit(k, used, choice, values):
        if k == 4:
            if used != radius:
                return
            total = (sum(values) if isinstance(target, int)
                     else tuple(sum(v[j] for v in values) for j in range(len(target))))
            if total == target:
                answers.add(tuple(choice))
            return
        for cost, tup in candidates[k]:
            if used + cost > radius:
                continue
            choice.append(tup)
            values.append(value(tup))
            visit(k + 1, used + cost, choice, values)
            values.pop()
            choice.pop()

    visit(0, 0, [], [])
    return sorted(answers)


def main() -> None:
    path = sys.argv[1] if len(sys.argv) > 1 else "agent_bp2_fourier_e896_verified.json"
    data = json.load(open(path, "r", encoding="utf-8"))
    seqs = data["sequences"]
    cubic = enumerate_targets(
        [compression(seq, 3) for seq in seqs],
        [counts(length, 3) for length in LENS],
        cubic_value,
        334,
        4,
    )
    quintic = enumerate_targets(
        [compression(seq, 5) for seq in seqs],
        [counts(length, 5) for length in LENS],
        quintic_value,
        (334, 0),
        4,
    )
    cubic8 = enumerate_targets(
        [compression(seq, 3) for seq in seqs],
        [counts(length, 3) for length in LENS],
        cubic_value,
        334,
        8,
    )
    quintic8 = enumerate_targets(
        [compression(seq, 5) for seq in seqs],
        [counts(length, 5) for length in LENS],
        quintic_value,
        (334, 0),
        8,
    )
    print(json.dumps({
        "source": path,
        "proved_equal_minimum_l1": 4,
        "cubic_count": len(cubic),
        "cubic_targets": cubic,
        "quintic_count": len(quintic),
        "quintic_targets": quintic,
        "next_shell_l1": 8,
        "cubic_l1_8_count": len(cubic8),
        "cubic_l1_8_first20": cubic8[:20],
        "quintic_l1_8_count": len(quintic8),
        "quintic_l1_8_first20": quintic8[:20],
    }, indent=2))


if __name__ == "__main__":
    main()
