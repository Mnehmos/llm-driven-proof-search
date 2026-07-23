"""Exact CDCL search in the reduced 85-generator special-Golay family.

The parity equations are built into the parameterization.  Pair products are
shared XOR variables and every remaining correlation/row-sum equation is an
exact pseudo-Boolean constraint.  The output is independently rechecked.
"""

from __future__ import annotations

import argparse
import json
import threading
import time
from pathlib import Path

from pysat.card import CardEnc, EncType
from pysat.formula import CNF, CNFPlus, IDPool
from pysat.solvers import Solver


def expand(runs: list[int]) -> list[int]:
    return [1 if j % 2 == 0 else -1 for j, n in enumerate(runs) for _ in range(n)]


Q = expand([83, 2, 81, 1])
F = [1] * 84 + [-1] * 83
ROW_TUPLES = [
    (-10, -7, -8, -11), (-10, 11, -8, 7),
    (-8, -7, -10, -11), (-8, 11, -10, 7),
    (8, -7, 10, -11), (8, 11, 10, 7),
    (10, -7, 8, -11), (10, 11, 8, 7),
]


def exact(s: list[int]) -> list[int]:
    return [
        sum(s[i] * s[i + d] for i in range(167 - d)
            if F[i] == F[i + d] and Q[i] == Q[i + d])
        for d in range(1, 84)
    ]


def add_xor(cnf: CNF, a: int, b: int, y: int) -> None:
    """y <-> (a xor b)."""
    cnf.extend([[a, b, -y], [-a, -b, -y], [a, -b, y], [-a, b, y]])


def add_weighted_equals(cnf: CNF | CNFPlus, pool: IDPool, literals: list[int], bound: int) -> None:
    # Cancel x + (1-x) = 1 before encoding.  In this parity quotient all odd
    # shifts disappear this way, leaving only 40 active correlations.
    signs: dict[int, list[int]] = {}
    for literal in literals:
        counts = signs.setdefault(abs(literal), [0, 0])
        counts[0 if literal > 0 else 1] += 1
    simplified = []
    for variable, (positive, negative) in signs.items():
        cancelled = min(positive, negative)
        bound -= cancelled
        simplified.extend([variable] * (positive - cancelled))
        simplified.extend([-variable] * (negative - cancelled))
    literals = simplified
    if bound < 0 or bound > len(literals):
        cnf.append([])
        return
    if not literals:
        return
    if bound == 0:
        cnf.extend([[-literal] for literal in literals])
        return
    if bound == len(literals):
        cnf.extend([[literal] for literal in literals])
        return
    # Cardinality encoders expect distinct inputs.  Repeated literals carry
    # genuine multiplicity here, so link each occurrence to a fresh proxy.
    proxies = []
    for literal in literals:
        proxy = pool.id()
        cnf.extend([[-proxy, literal], [proxy, -literal]])
        proxies.append(proxy)
    if isinstance(cnf, CNFPlus):
        cnf.append([proxies, bound], is_atmost=True)
        cnf.append([[-x for x in proxies], len(proxies) - bound], is_atmost=True)
    else:
        encoded = CardEnc.equals(
            lits=proxies, bound=bound, vpool=pool, encoding=EncType.cardnetwrk,
        )
        cnf.extend(encoded.clauses)


def build(base: list[int], row_tuple: tuple[int, int, int, int], native: bool = False) -> tuple[CNF | CNFPlus, list[int], list[int], IDPool]:
    group = [-1] * 167
    g = 0
    for i in range(41):
        group[i] = group[82 - i] = g
        g += 1
    for i in range(41):
        group[84 + i] = group[166 - i] = g
        g += 1
    for i in (41, 83, 125):
        group[i] = g
        g += 1
    assert g == 85 and min(group) >= 0

    pool = IDPool()
    u = [pool.id(f"u_{i}") for i in range(85)]
    cnf = CNFPlus() if native else CNF()
    cnf.extend([[-u[group[0]]], [-u[group[84]]]])
    pair: dict[tuple[int, int], int] = {}

    def pair_xor(x: int, y: int) -> int:
        if x > y:
            x, y = y, x
        if (x, y) not in pair:
            v = pool.id(f"p_{x}_{y}")
            add_xor(cnf, u[x], u[y], v)
            pair[x, y] = v
        return pair[x, y]

    nontrivial = 0
    for d in range(1, 84):
        terms: list[int] = []
        fixed = 0
        count = 0
        for i in range(167 - d):
            j = i + d
            if F[i] != F[j] or Q[i] != Q[j]:
                continue
            count += 1
            complemented = base[i] != base[j]
            x, y = group[i], group[j]
            if x == y:
                fixed += int(complemented)
            else:
                v = pair_xor(x, y)
                terms.append(-v if complemented else v)
        if terms:
            add_weighted_equals(cnf, pool, terms, count // 2 - fixed)
            nontrivial += 1

    def add_row(indices: range, extra: list[int] | None, target: int) -> None:
        # Count negative contributions: sum(signs) = len(indices) - 2*count.
        literals = []
        for i in indices:
            coefficient = base[i] * (1 if extra is None else extra[i])
            literals.append(u[group[i]] if coefficient == 1 else -u[group[i]])
        add_weighted_equals(cnf, pool, literals, (len(indices) - target) // 2)

    add_row(range(84), None, row_tuple[0])
    add_row(range(84, 167), None, row_tuple[1])
    add_row(range(84), Q, row_tuple[2])
    add_row(range(84, 167), Q, row_tuple[3])
    return cnf, u, group, pool


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--seconds", type=float, default=900)
    parser.add_argument("--solver", default="cadical195")
    parser.add_argument("--tuple", type=int, default=0, dest="tuple_index")
    parser.add_argument("--input", type=Path, default=Path(
        "Find a Hadamard matrix of order 668/special_golay_167_live.json"))
    parser.add_argument("--output", type=Path, default=Path(
        "Find a Hadamard matrix of order 668/special_golay_167_pysat_candidate.json"))
    args = parser.parse_args()
    started = time.time()
    base = json.loads(args.input.read_text(encoding="utf-8"))["s"]
    if base[0] == -1:
        base[:84] = [-x for x in base[:84]]
    if base[84] == -1:
        base[84:] = [-x for x in base[84:]]
    row_tuple = ROW_TUPLES[args.tuple_index]
    native = args.solver.lower() in ("minicard", "mc", "mcard")
    cnf, u, group, pool = build(base, row_tuple, native=native)
    print(json.dumps({"event": "built", "solver": args.solver,
        "row_tuple": row_tuple, "variables": pool.top,
        "clauses": len(cnf.clauses), "native_atmost": len(cnf.atmosts) if native else 0,
        "elapsed_s": time.time() - started}), flush=True)

    with Solver(name=args.solver, use_timer=True) as solver:
        solver.append_formula(cnf.clauses)
        if native:
            for literals, bound in cnf.atmosts:
                solver.add_atmost(literals, bound)
        # Incumbent is u=0 because base is the incumbent itself.
        if hasattr(solver, "set_phases"):
            solver.set_phases([-v for v in u])
        timer = threading.Timer(args.seconds, solver.interrupt)
        timer.start()
        try:
            sat = solver.solve_limited(expect_interrupt=True)
        finally:
            timer.cancel()
        print(json.dumps({"event": "result", "sat": sat, "solver": args.solver,
            "row_tuple": row_tuple, "elapsed_s": time.time() - started,
            "stats": solver.accum_stats()}), flush=True)
        if sat is not True:
            return 2 if sat is None else 1
        model = set(solver.get_model())

    s = [base[i] * (-1 if u[group[i]] in model else 1) for i in range(167)]
    residual = exact(s)
    if any(residual):
        raise RuntimeError(f"SAT witness failed independent check: {residual}")
    sequences = [s, [x*f for x, f in zip(s, F)],
                 [x*q for x, q in zip(s, Q)],
                 [x*q*f for x, q, f in zip(s, Q, F)]]
    payload = {"construction": "special Golay quadruple length 167",
        "solver": args.solver, "row_tuple": row_tuple,
        "variables": pool.top, "clauses": len(cnf.clauses),
        "elapsed_s": time.time() - started, "residual": [0] * 166,
        "sequences": sequences}
    args.output.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"event": "verified_witness", "output": str(args.output),
        "row_sums": [sum(x) for x in sequences]}), flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
