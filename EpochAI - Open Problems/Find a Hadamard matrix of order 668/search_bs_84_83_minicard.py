"""Exact MiniCard search for a fixed-row BS(84,83) fiber."""

from __future__ import annotations

import argparse
import json
import threading
import time
from pathlib import Path

from pysat.card import CardEnc, EncType
from pysat.formula import CNFPlus, IDPool
from pysat.solvers import Solver


LENGTHS = (84, 84, 83, 83)


def xor_equiv(cnf: CNFPlus, a: int, b: int, y: int,
              native_xors: list[tuple[int, int, int]] | None = None) -> None:
    cnf.extend([[a, b, -y], [-a, -b, -y], [a, -b, y], [-a, b, y]])
    if native_xors is not None:
        native_xors.append((a, b, y))


def add_equals(cnf: CNFPlus, literals: list[int], bound: int,
               equality_xors: list[tuple[tuple[int, ...], bool]] | None = None) -> None:
    if equality_xors is not None:
        equality_xors.append((tuple(literals), bool(bound & 1)))
    if bound == 0:
        cnf.extend([[-x] for x in literals])
    elif bound == len(literals):
        cnf.extend([[x] for x in literals])
    else:
        cnf.append([literals, bound], is_atmost=True)
        cnf.append([[-x for x in literals], len(literals) - bound], is_atmost=True)


def residual(sequences: list[list[int]]) -> list[int]:
    return [sum(sum(a[i] * a[i+d] for i in range(len(a)-d)) for a in sequences)
            for d in range(1, 84)]


def main() -> int:
    p = argparse.ArgumentParser()
    p.add_argument("--seconds", type=float, default=900)
    p.add_argument("--solver", default="minicard",
                   help="PySAT solver name; non-MiniCard solvers receive a CNF cardinality encoding")
    p.add_argument("--threads", type=int, default=1,
                   help="thread count for the pycryptosat backend")
    p.add_argument("--encoding", default="kmtotalizer",
                   choices=("seqcounter", "sortnetwrk", "cardnetwrk", "totalizer",
                            "mtotalizer", "kmtotalizer"),
                   help="cardinality encoding used when --solver is not minicard")
    p.add_argument("--row-tuple", default="-8,-6,-3,15")
    p.add_argument("--alt-tuple")
    p.add_argument("--quartic-tuple")
    p.add_argument("--cubic-tuple")
    p.add_argument("--quintic-tuple")
    p.add_argument("--septimal-tuple")
    p.add_argument("--undecimal-tuple")
    p.add_argument("--input", type=Path)
    p.add_argument("--max-changes", type=int)
    p.add_argument("--normalize-first", action="store_true",
                   help="fix every first sequence entry to +1 (negation symmetry)")
    p.add_argument("--output", type=Path, default=Path(
        "Find a Hadamard matrix of order 668/bs_84_83_minicard_candidate.json"))
    a = p.parse_args()
    rows = tuple(int(x) for x in a.row_tuple.split(","))
    if len(rows) != 4 or sum(x*x for x in rows) != 334:
        raise ValueError("row tuple must have four entries with square sum 334")
    alt_rows = tuple(int(x) for x in a.alt_tuple.split(",")) if a.alt_tuple else None
    if alt_rows is not None and (len(alt_rows) != 4 or sum(x*x for x in alt_rows) != 334):
        raise ValueError("alternating tuple must have four entries with square sum 334")
    quartic = tuple(int(x) for x in a.quartic_tuple.split(",")) if a.quartic_tuple else None
    if quartic is not None and (len(quartic) != 8 or sum(x*x for x in quartic) != 334):
        raise ValueError("quartic tuple must have eight entries with square sum 334")
    cubic = tuple(int(x) for x in a.cubic_tuple.split(",")) if a.cubic_tuple else None
    if cubic is not None:
        if len(cubic) != 12:
            raise ValueError("cubic tuple must have twelve entries")
        cubic_norm = sum(
            sum(v*v for v in cubic[3*k:3*k+3])
            - sum(cubic[3*k+i]*cubic[3*k+(i+1)%3] for i in range(3))
            for k in range(4)
        )
        if cubic_norm != 334:
            raise ValueError("cubic tuple must have root-of-unity norm 334")
    quintic = tuple(int(x) for x in a.quintic_tuple.split(",")) if a.quintic_tuple else None
    if quintic is not None:
        if len(quintic) != 20:
            raise ValueError("quintic tuple must have twenty entries")
        inv0 = inv1 = 0
        for k in range(4):
            values = quintic[5*k:5*k+5]
            s0 = sum(x*x for x in values)
            s1 = sum(values[i]*values[(i+1)%5] for i in range(5))
            s2 = sum(values[i]*values[(i+2)%5] for i in range(5))
            inv0 += s0-s1; inv1 += s1-s2
        if (inv0,inv1) != (334,0):
            raise ValueError("quintic tuple must have fifth-root invariants (334,0)")
    septimal = tuple(int(x) for x in a.septimal_tuple.split(",")) if a.septimal_tuple else None
    if septimal is not None:
        if len(septimal) != 28:
            raise ValueError("septimal tuple must have twenty-eight entries")
        invariants = [0, 0, 0]
        for k in range(4):
            values = septimal[7*k:7*k+7]
            products = [sum(values[i]*values[(i+j)%7] for i in range(7))
                        for j in range(4)]
            invariants[0] += products[0]-products[1]
            invariants[1] += products[1]-products[2]
            invariants[2] += products[2]-products[3]
        if tuple(invariants) != (334,0,0):
            raise ValueError("septimal tuple must have seventh-root invariants (334,0,0)")
    undecimal = tuple(int(x) for x in a.undecimal_tuple.split(",")) if a.undecimal_tuple else None
    if undecimal is not None:
        if len(undecimal) != 44:
            raise ValueError("undecimal tuple must have forty-four entries")
        invariants = [0] * 6
        for k in range(4):
            values = undecimal[11*k:11*k+11]
            products = [sum(values[i]*values[(i+j)%11] for i in range(11))
                        for j in range(7)]
            for j in range(6):
                invariants[j] += products[j]-products[j+1]
        if tuple(invariants) != (334,0,0,0,0,0):
            raise ValueError("undecimal tuple must have eleventh-root invariants")
    started = time.time()
    pool = IDPool()
    bits = [[pool.id(f"x_{k}_{i}") for i in range(n)] for k, n in enumerate(LENGTHS)]
    cnf = CNFPlus()
    native_xors: list[tuple[int, int, int]] = []
    equality_xors: list[tuple[tuple[int, ...], bool]] = []
    primary_parity_xors: list[tuple[int, ...]] = []

    for d in range(1, 84):
        xors = []
        for k, seq in enumerate(bits):
            for i in range(len(seq) - d):
                y = pool.id(f"p_{k}_{i}_{d}")
                xor_equiv(cnf, seq[i], seq[i+d], y, native_xors)
                xors.append(y)
        # Sum of products is zero iff exactly half the pair signs disagree.
        add_equals(cnf, xors, len(xors)//2, equality_xors)
        odd_vertices = []
        for seq in bits:
            incidence = [0] * len(seq)
            for i in range(len(seq)-d):
                incidence[i] ^= 1
                incidence[i+d] ^= 1
            odd_vertices.extend(v for v, odd in zip(seq, incidence) if odd)
        primary_parity_xors.append(tuple(odd_vertices))
    for seq, n, target in zip(bits, LENGTHS, rows):
        add_equals(cnf, seq, (n-target)//2, equality_xors)
    if alt_rows is not None:
        for seq, n, row, alt in zip(bits, LENGTHS, rows, alt_rows):
            # Row and alternating sums fix negative counts on even and odd positions.
            even_count=(n+1)//2; odd_count=n//2
            even_sum=(row+alt)//2; odd_sum=(row-alt)//2
            add_equals(cnf, seq[0::2], (even_count-even_sum)//2, equality_xors)
            add_equals(cnf, seq[1::2], (odd_count-odd_sum)//2, equality_xors)
    if quartic is not None:
        for k,(seq,n,row) in enumerate(zip(bits,LENGTHS,rows)):
            alt = alt_rows[k] if alt_rows is not None else None
            if alt is None:
                raise ValueError("quartic tuple currently requires --alt-tuple")
            real,imag=quartic[2*k:2*k+2]
            even_sum=(row+alt)//2; odd_sum=(row-alt)//2
            residue_sums=((even_sum+real)//2,(odd_sum+imag)//2,
                          (even_sum-real)//2,(odd_sum-imag)//2)
            for residue,target_sum in enumerate(residue_sums):
                positions=seq[residue::4]
                if (len(positions)-target_sum)%2:
                    raise ValueError("incompatible quartic margin")
                add_equals(cnf,positions,(len(positions)-target_sum)//2,equality_xors)
    if cubic is not None:
        for k,seq in enumerate(bits):
            targets=cubic[3*k:3*k+3]
            if sum(targets)!=rows[k]:
                raise ValueError("cubic margins do not match row tuple")
            for residue,target_sum in enumerate(targets):
                positions=seq[residue::3]
                if (len(positions)-target_sum)%2:
                    raise ValueError("incompatible cubic margin")
                add_equals(cnf,positions,(len(positions)-target_sum)//2,equality_xors)
    if quintic is not None:
        for k,seq in enumerate(bits):
            targets=quintic[5*k:5*k+5]
            if sum(targets)!=rows[k]:
                raise ValueError("quintic margins do not match row tuple")
            for residue,target_sum in enumerate(targets):
                positions=seq[residue::5]
                if (len(positions)-target_sum)%2:
                    raise ValueError("incompatible quintic margin")
                add_equals(cnf,positions,(len(positions)-target_sum)//2,equality_xors)
    if septimal is not None:
        for k,seq in enumerate(bits):
            targets=septimal[7*k:7*k+7]
            if sum(targets)!=rows[k]:
                raise ValueError("septimal margins do not match row tuple")
            for residue,target_sum in enumerate(targets):
                positions=seq[residue::7]
                if (len(positions)-target_sum)%2:
                    raise ValueError("incompatible septimal margin")
                add_equals(cnf,positions,(len(positions)-target_sum)//2,equality_xors)
    if undecimal is not None:
        for k,seq in enumerate(bits):
            targets=undecimal[11*k:11*k+11]
            if sum(targets)!=rows[k]:
                raise ValueError("undecimal margins do not match row tuple")
            for residue,target_sum in enumerate(targets):
                positions=seq[residue::11]
                if (len(positions)-target_sum)%2:
                    raise ValueError("incompatible undecimal margin")
                add_equals(cnf,positions,(len(positions)-target_sum)//2,equality_xors)
    if a.normalize_first:
        # A true bit denotes -1, so these units normalize x[k][0] = +1.
        cnf.extend([[-seq[0]] for seq in bits])

    solver_name = a.solver.lower()
    native_minicard = solver_name in ("mc", "mcard", "minicard")
    native_crypto = solver_name in ("cms", "cryptominisat", "pycryptosat")
    encoded_clauses = list(cnf.clauses)
    if not native_minicard:
        encoding = getattr(EncType, a.encoding)
        for literals, bound in cnf.atmosts:
            encoded_clauses.extend(CardEnc.atmost(
                lits=list(literals), bound=bound, vpool=pool,
                encoding=encoding).clauses)

    print(json.dumps({"event":"built", "row_tuple":rows, "alt_tuple":alt_rows,
        "quartic_tuple":quartic, "cubic_tuple":cubic,
        "quintic_tuple":quintic, "septimal_tuple":septimal,
        "undecimal_tuple":undecimal, "variables":pool.top,
        "clauses":len(encoded_clauses),
        "native_atmost":len(cnf.atmosts) if native_minicard else 0,
        "encoded_atmost":0 if native_minicard else len(cnf.atmosts),
        "solver":a.solver, "encoding":None if native_minicard else a.encoding,
        "native_xors":len(native_xors)+len(equality_xors)+len(primary_parity_xors)
            if native_crypto else 0,
        "elapsed_s":time.time()-started}), flush=True)
    seed = None
    if a.input:
        seed_payload = json.loads(a.input.read_text(encoding="utf-8"))
        seed = (seed_payload["sequences"] if "sequences" in seed_payload
                else seed_payload["ranking"][0]["sequences"])
        if a.normalize_first:
            seed = [[x * seq[0] for x in seq] for seq in seed]
        if tuple(map(sum, seed)) != rows or tuple(map(len, seed)) != LENGTHS:
            raise ValueError("input sequences do not match the selected row fiber")
        if a.max_changes is not None:
            change_literals = [v if sign == 1 else -v
                               for seq_bits, seq_signs in zip(bits, seed)
                               for v, sign in zip(seq_bits, seq_signs)]
            cnf.append([change_literals, a.max_changes], is_atmost=True)
            if not native_minicard:
                encoded_clauses.extend(CardEnc.atmost(
                    lits=change_literals, bound=a.max_changes, vpool=pool,
                    encoding=getattr(EncType, a.encoding)).clauses)

    if native_crypto:
        import pycryptosat
        parity_solver = pycryptosat.Solver(time_limit=min(30.0, a.seconds), threads=1)
        for literals in primary_parity_xors:
            parity_solver.add_xor_clause(list(literals), True)
        # The first 83 equalities are lag counts on auxiliary product bits.
        # All later equalities are primary-bit row/residue counts.
        for literals, rhs in equality_xors[83:]:
            parity_solver.add_xor_clause(list(literals), rhs)
        parity_sat, _ = parity_solver.solve()
        if parity_sat is False:
            print(json.dumps({"event":"result", "sat":False, "row_tuple":rows,
                "elapsed_s":time.time()-started, "solver":a.solver,
                "reason":"primary parity/margin subsystem inconsistent"}), flush=True)
            return 1
        solver = pycryptosat.Solver(time_limit=a.seconds, threads=a.threads)
        for literals in native_xors:
            solver.add_xor_clause(list(literals), False)
        for literals, rhs in equality_xors:
            solver.add_xor_clause(list(literals), rhs)
        for literals in primary_parity_xors:
            solver.add_xor_clause(list(literals), True)
        solver.add_clauses(encoded_clauses)
        sat, assignment = solver.solve()
        print(json.dumps({"event":"result", "sat":sat, "row_tuple":rows,
            "elapsed_s":time.time()-started, "solver":a.solver}), flush=True)
        if sat is not True:
            return 2 if sat is None else 1
        model = {index for index, value in enumerate(assignment) if value}
    else:
      with Solver(name=a.solver, use_timer=True) as solver:
        solver.append_formula(encoded_clauses)
        if native_minicard:
            for literals, bound in cnf.atmosts:
                solver.add_atmost(literals, bound)
        if seed is not None:
            phases = [v if sign == -1 else -v
                      for seq_bits, seq_signs in zip(bits, seed)
                      for v, sign in zip(seq_bits, seq_signs)]
            try:
                solver.set_phases(phases)
            except NotImplementedError:
                print(json.dumps({"event":"phases_unsupported",
                                  "solver":a.solver}), flush=True)
        timer = threading.Timer(a.seconds, solver.interrupt)
        timer.start()
        try:
            sat = solver.solve_limited(expect_interrupt=True)
        finally:
            timer.cancel()
        print(json.dumps({"event":"result", "sat":sat, "row_tuple":rows,
            "elapsed_s":time.time()-started, "stats":solver.accum_stats()}), flush=True)
        if sat is not True:
            return 2 if sat is None else 1
        model = set(solver.get_model())

    sequences = [[-1 if v in model else 1 for v in seq] for seq in bits]
    r = residual(sequences)
    if any(r) or tuple(map(sum, sequences)) != rows:
        raise RuntimeError((r, tuple(map(sum, sequences))))
    payload = {"construction":"base sequences BS(84,83)", "solver":a.solver,
        "row_sums":rows, "residual":r, "elapsed_s":time.time()-started,
        "sequences":sequences}
    a.output.write_text(json.dumps(payload, indent=2)+"\n", encoding="utf-8")
    print(json.dumps({"event":"verified_witness", "output":str(a.output)}), flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
