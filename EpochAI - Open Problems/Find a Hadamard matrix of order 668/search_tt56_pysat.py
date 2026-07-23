"""Exact CNF search for TT(56), using a modern CDCL SAT solver.

Each sign is one Boolean.  Pair products are represented by XOR variables,
and each of the 55 autocorrelation equations is encoded as an exact
cardinality constraint.  Weight-two C/D terms use equality-linked proxy
literals, so the encoding remains ordinary CNF and requires no trust in a
numerical optimizer.
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


LENGTHS = (56, 56, 56, 55)
WEIGHTS = (1, 1, 2, 2)


def verify(sequences: list[list[int]]) -> list[int]:
    return [
        sum(w * sum(seq[i] * seq[i + s] for i in range(len(seq) - s)) for seq, w in zip(sequences, WEIGHTS))
        for s in range(1, 56)
    ]


def xor_equiv(cnf: CNF, a: int, b: int, y: int) -> None:
    cnf.extend([[a, b, -y], [-a, -b, -y], [a, -b, y], [-a, b, y]])


def add_equals(cnf: CNF | CNFPlus, pool: IDPool, literals: list[int],
               bound: int, native: bool) -> None:
    if bound < 0 or bound > len(literals):
        cnf.append([])
    elif bound == 0:
        cnf.extend([[-x] for x in literals])
    elif bound == len(literals):
        cnf.extend([[x] for x in literals])
    elif native:
        assert isinstance(cnf, CNFPlus)
        cnf.append([literals, bound], is_atmost=True)
        cnf.append([[-x for x in literals], len(literals) - bound], is_atmost=True)
    else:
        cnf.extend(CardEnc.equals(
            literals, bound=bound, vpool=pool,
            encoding=EncType.kmtotalizer).clauses)


def build(native: bool, rows: tuple[int, ...] | None,
          alt_rows: tuple[int, ...] | None,
          quartic: tuple[int, ...] | None,
          normalize_first: bool) -> tuple[CNF | CNFPlus, list[list[int]], IDPool]:
    pool = IDPool()
    bits = [[pool.id(f"{'ABCD'[k]}_{i}") for i in range(n)] for k, n in enumerate(LENGTHS)]
    cnf: CNF | CNFPlus = CNFPlus() if native else CNF()

    # Independent sequence negations preserve every autocorrelation equation.
    if normalize_first:
        cnf.extend([[-seq[0]] for seq in bits])

    for shift in range(1, 56):
        weighted_literals: list[int] = []
        for k, (seq, weight) in enumerate(zip(bits, WEIGHTS)):
            for i in range(len(seq) - shift):
                y = pool.id(f"xor_{k}_{i}_{shift}")
                xor_equiv(cnf, seq[i], seq[i + shift], y)
                weighted_literals.append(y)
                if weight == 2:
                    proxy = pool.id(f"proxy_{k}_{i}_{shift}")
                    cnf.extend([[-y, proxy], [y, -proxy]])
                    weighted_literals.append(proxy)
        rhs = 167 - 3 * shift
        add_equals(cnf, pool, weighted_literals, rhs, native)

    if rows is not None:
        for seq, n, target in zip(bits, LENGTHS, rows):
            add_equals(cnf, pool, seq, (n - target) // 2, native)
    if alt_rows is not None:
        if rows is None:
            raise ValueError("--alt-tuple requires --row-tuple")
        for seq, n, row, alt in zip(bits, LENGTHS, rows, alt_rows):
            even_count, odd_count = (n + 1) // 2, n // 2
            even_sum, odd_sum = (row + alt) // 2, (row - alt) // 2
            add_equals(cnf, pool, seq[0::2], (even_count - even_sum) // 2, native)
            add_equals(cnf, pool, seq[1::2], (odd_count - odd_sum) // 2, native)
    if quartic is not None:
        if rows is None or alt_rows is None:
            raise ValueError("--quartic-tuple requires row and alternating tuples")
        for k, (seq, n, row, alt) in enumerate(zip(bits, LENGTHS, rows, alt_rows)):
            real, imag = quartic[2*k:2*k+2]
            even_sum, odd_sum = (row + alt) // 2, (row - alt) // 2
            residue_sums = ((even_sum + real) // 2, (odd_sum + imag) // 2,
                            (even_sum - real) // 2, (odd_sum - imag) // 2)
            for residue, target in enumerate(residue_sums):
                positions = seq[residue::4]
                if (len(positions) - target) % 2:
                    raise ValueError("incompatible quartic margin")
                add_equals(cnf, pool, positions, (len(positions) - target) // 2, native)
    return cnf, bits, pool


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--seconds", type=int, default=900)
    parser.add_argument("--solver", default="cadical195")
    parser.add_argument("--row-tuple")
    parser.add_argument("--alt-tuple")
    parser.add_argument("--quartic-tuple")
    parser.add_argument("--input", type=Path)
    parser.add_argument("--max-changes", type=int)
    parser.add_argument("--normalize-first", action="store_true")
    parser.add_argument("--output", type=Path, default=Path("Find a Hadamard matrix of order 668/tt56_pysat_candidate.json"))
    args = parser.parse_args()

    started = time.time()
    rows = tuple(map(int, args.row_tuple.split(","))) if args.row_tuple else None
    alt_rows = tuple(map(int, args.alt_tuple.split(","))) if args.alt_tuple else None
    quartic = tuple(map(int, args.quartic_tuple.split(","))) if args.quartic_tuple else None
    weighted_norm = lambda values: sum(w*x*x for w, x in zip(WEIGHTS, values))
    if rows is not None and (len(rows) != 4 or weighted_norm(rows) != 334):
        raise ValueError("row tuple must have weighted square norm 334")
    if alt_rows is not None and (len(alt_rows) != 4 or weighted_norm(alt_rows) != 334):
        raise ValueError("alternating tuple must have weighted square norm 334")
    if quartic is not None:
        if len(quartic) != 8:
            raise ValueError("quartic tuple must have eight entries")
        qnorm = sum(WEIGHTS[k] * (quartic[2*k]**2 + quartic[2*k+1]**2)
                    for k in range(4))
        if qnorm != 334:
            raise ValueError("quartic tuple must have weighted square norm 334")
    native = args.solver.lower() in ("minicard", "mc", "mcard")
    cnf, bits, pool = build(native, rows, alt_rows, quartic, args.normalize_first)
    seed = None
    if args.input:
        seed = json.loads(args.input.read_text(encoding="utf-8"))["sequences"]
        if args.normalize_first:
            seed = [[v * seq[0] for v in seq] for seq in seed]
        if tuple(map(len, seed)) != LENGTHS:
            raise ValueError("input sequence lengths do not match TT(56)")
        if rows is not None and tuple(map(sum, seed)) != rows:
            raise ValueError("input does not match the selected row tuple")
        if args.max_changes is not None:
            changes = [v if sign == 1 else -v
                       for seq_bits, seq_signs in zip(bits, seed)
                       for v, sign in zip(seq_bits, seq_signs)]
            if native:
                assert isinstance(cnf, CNFPlus)
                cnf.append([changes, args.max_changes], is_atmost=True)
            else:
                cnf.extend(CardEnc.atmost(changes, bound=args.max_changes,
                    vpool=pool, encoding=EncType.kmtotalizer).clauses)
    print(json.dumps({"event": "built", "variables": pool.top, "clauses": len(cnf.clauses), "elapsed_s": time.time() - started}), flush=True)
    with Solver(name=args.solver, bootstrap_with=cnf.clauses, use_timer=True) as solver:
        if native:
            assert isinstance(cnf, CNFPlus)
            for literals, bound in cnf.atmosts:
                solver.add_atmost(literals, bound)
        if seed is not None:
            phases = [v if sign == -1 else -v
                      for seq_bits, seq_signs in zip(bits, seed)
                      for v, sign in zip(seq_bits, seq_signs)]
            solver.set_phases(phases)
        timer = threading.Timer(args.seconds, solver.interrupt)
        timer.start()
        try:
            sat = solver.solve_limited(expect_interrupt=True)
        finally:
            timer.cancel()
        print(json.dumps({"event": "result", "sat": sat, "solver": args.solver, "elapsed_s": time.time() - started, "stats": solver.accum_stats()}), flush=True)
        if sat is not True:
            return 2 if sat is None else 1
        model = set(solver.get_model())

    sequences = [[-1 if variable in model else 1 for variable in seq] for seq in bits]
    residual = verify(sequences)
    if any(residual):
        raise RuntimeError(f"SAT model failed independent check: {residual}")
    payload = {
        "construction": "Turyn-type sequences TT(56)",
        "solver": args.solver,
        "variables": pool.top,
        "clauses": len(cnf.clauses),
        "elapsed_s": time.time() - started,
        "row_sums": [sum(seq) for seq in sequences],
        "alternating_sums": [sum((1 if i % 2 == 0 else -1) * v
                                  for i, v in enumerate(seq)) for seq in sequences],
        "residual": residual,
        "sequences": sequences,
    }
    args.output.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"event": "verified_witness", "output": str(args.output), "row_sums": payload["row_sums"]}), flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
