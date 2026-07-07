#!/usr/bin/env python3
"""Generate locally preflighted IGP24 discovery batches.

This is intentionally separate from igp24_gate.py.  The gate is for candidate
lists that already have expected 24T labels.  This script is for discovery:
it builds structurally varied monic degree-24 polynomials, filters out local
syntax/reducibility problems with SymPy, and writes coefficient-only batches
for the official SAIR verifier to label.
"""

from __future__ import annotations

import argparse
import json
import math
import random
import sys
import time
from dataclasses import dataclass, field
from functools import reduce
from math import gcd
from pathlib import Path
from typing import Iterable

import sympy as sp


DEGREE = 24
x = sp.symbols("x")


@dataclass
class Candidate:
    coeffs: tuple[int, ...]
    family: str
    params: dict[str, int | str] = field(default_factory=dict)
    real_roots: int | None = None
    score: tuple[int, ...] = field(default_factory=tuple)

    @property
    def line(self) -> str:
        return ",".join(str(c) for c in self.coeffs)


def coefficient_tuple(poly: sp.Expr) -> tuple[int, ...] | None:
    p = sp.Poly(sp.expand(poly), x, domain=sp.ZZ)
    if p.degree() != DEGREE:
        return None
    coeffs_high = p.all_coeffs()
    coeffs = tuple(int(c) for c in reversed(coeffs_high))
    if len(coeffs) != DEGREE + 1:
        return None
    if coeffs[0] == 0 or coeffs[-1] != 1:
        return None
    coefficient_gcd = reduce(gcd, (abs(c) for c in coeffs), 0)
    if coefficient_gcd != 1:
        return None
    return coeffs


def max_abs_coeff(coeffs: tuple[int, ...]) -> int:
    return max(abs(c) for c in coeffs)


def is_irreducible(coeffs: tuple[int, ...]) -> bool:
    expr = sum(c * x**i for i, c in enumerate(coeffs))
    return bool(sp.Poly(expr, x, domain=sp.QQ).is_irreducible)


def is_irreducible_modular(coeffs: tuple[int, ...]) -> bool:
    expr = sum(c * x**i for i, c in enumerate(coeffs))
    for prime in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41):
        try:
            if sp.Poly(expr, x, modulus=prime).is_irreducible:
                return True
        except Exception:
            continue
    return False


def real_root_count(coeffs: tuple[int, ...]) -> int:
    expr = sum(c * x**i for i, c in enumerate(coeffs))
    return int(sp.Poly(expr, x, domain=sp.QQ).count_roots(sp.S.NegativeInfinity, sp.S.Infinity))


def numeric_real_root_count(coeffs: tuple[int, ...]) -> int:
    expr = sum(c * x**i for i, c in enumerate(coeffs))
    roots = sp.Poly(expr, x, domain=sp.QQ).nroots(n=30, maxsteps=200)
    return sum(1 for root in roots if abs(float(sp.im(root))) < 1e-18)


def sparse_trinomials() -> Iterable[Candidate]:
    constants = [-13, -11, -7, -5, -3, -2, -1, 1, 2, 3, 5, 7, 11, 13]
    middle_coeffs = [-9, -7, -5, -3, -2, -1, 1, 2, 3, 5, 7, 9]
    for k in range(1, DEGREE):
        for a in middle_coeffs:
            for b in constants:
                coeffs = [0] * (DEGREE + 1)
                coeffs[0] = b
                coeffs[k] = a
                coeffs[DEGREE] = 1
                yield Candidate(tuple(coeffs), "trinomial", {"k": k, "a": a, "b": b})


def sparse_fournomials() -> Iterable[Candidate]:
    constants = [-11, -7, -5, -3, -2, -1, 1, 2, 3, 5, 7, 11]
    coeffs_pool = [-5, -3, -2, -1, 1, 2, 3, 5]
    for k1 in range(1, DEGREE):
        for k2 in range(k1 + 1, DEGREE):
            if math.gcd(math.gcd(k1, k2), DEGREE) != 1:
                continue
            for a in coeffs_pool:
                for b in coeffs_pool:
                    if a == b:
                        continue
                    for c in constants:
                        coeffs = [0] * (DEGREE + 1)
                        coeffs[0] = c
                        coeffs[k1] = a
                        coeffs[k2] = b
                        coeffs[DEGREE] = 1
                        yield Candidate(
                            tuple(coeffs),
                            "four-nomial",
                            {"k1": k1, "k2": k2, "a": a, "b": b, "c": c},
                        )


def composed_polynomials() -> Iterable[Candidate]:
    # Factorizations 24 = outer_degree * inner_degree.  Using x^m + c keeps
    # the construction imprimitive enough to find groups away from generic S24.
    constants = [-5, -3, -2, -1, 1, 2, 3, 5]
    linear_coeffs = [-5, -3, -2, -1, 1, 2, 3, 5]
    for inner_degree in (2, 3, 4, 6, 8, 12):
        outer_degree = DEGREE // inner_degree
        for shift in (-2, -1, 0, 1, 2):
            inner = x**inner_degree + shift
            for a in linear_coeffs:
                for b in constants:
                    outer = x**outer_degree + a * x + b
                    coeffs = coefficient_tuple(outer.as_expr().subs(x, inner))
                    if coeffs is not None:
                        yield Candidate(
                            coeffs,
                            "composition-linear",
                            {
                                "outer_degree": outer_degree,
                                "inner_degree": inner_degree,
                                "shift": shift,
                                "a": a,
                                "b": b,
                            },
                        )
            if outer_degree >= 3:
                for a in (-3, -2, -1, 1, 2, 3):
                    for b in (-3, -2, -1, 1, 2, 3):
                        for c in constants:
                            outer = x**outer_degree + a * x ** (outer_degree - 1) + b * x + c
                            coeffs = coefficient_tuple(outer.as_expr().subs(x, inner))
                            if coeffs is not None:
                                yield Candidate(
                                    coeffs,
                                    "composition-edge",
                                    {
                                        "outer_degree": outer_degree,
                                        "inner_degree": inner_degree,
                                        "shift": shift,
                                        "a": a,
                                        "b": b,
                                        "c": c,
                                    },
                                )


def shifted_powers() -> Iterable[Candidate]:
    constants = [-7, -5, -3, -2, -1, 1, 2, 3, 5, 7]
    for shift in (-3, -2, -1, 1, 2, 3):
        base = x + shift
        for k in range(1, DEGREE):
            for a in (-5, -3, -2, -1, 1, 2, 3, 5):
                for b in constants:
                    coeffs = coefficient_tuple(base**DEGREE + a * base**k + b)
                    if coeffs is not None:
                        yield Candidate(coeffs, "translated-trinomial", {"shift": shift, "k": k, "a": a, "b": b})


def random_sparse(seed: int, count: int) -> Iterable[Candidate]:
    rng = random.Random(seed)
    for index in range(count):
        terms = rng.randint(3, 6)
        powers = sorted(rng.sample(range(1, DEGREE), terms - 1))
        coeffs = [0] * (DEGREE + 1)
        coeffs[0] = rng.choice([-17, -13, -11, -7, -5, -3, -2, -1, 1, 2, 3, 5, 7, 11, 13, 17])
        for power in powers:
            coeffs[power] = rng.choice([-9, -7, -5, -3, -2, -1, 1, 2, 3, 5, 7, 9])
        coeffs[DEGREE] = 1
        yield Candidate(tuple(coeffs), "random-sparse", {"seed": seed, "index": index, "terms": terms})


def select_candidates(args: argparse.Namespace) -> tuple[list[Candidate], dict[str, object]]:
    selected: list[Candidate] = []
    seen: set[tuple[int, ...]] = set()
    rejected: dict[str, int] = {
        "duplicate": 0,
        "too_large": 0,
        "reducible": 0,
        "root_count_failed": 0,
    }
    family_counts: dict[str, int] = {}
    root_counts: dict[str, int] = {}

    def accept_from(stream: Iterable[Candidate], quota: int) -> None:
        nonlocal selected
        accepted_here = 0
        for candidate in stream:
            if accepted_here >= quota or len(selected) >= args.count:
                return
            if candidate.coeffs in seen:
                rejected["duplicate"] += 1
                continue
            seen.add(candidate.coeffs)

            if max_abs_coeff(candidate.coeffs) > args.max_abs_coeff:
                rejected["too_large"] += 1
                continue
            try:
                if args.irreducibility_mode == "exact":
                    irreducible = is_irreducible(candidate.coeffs)
                elif args.irreducibility_mode == "modular":
                    irreducible = is_irreducible_modular(candidate.coeffs)
                else:
                    irreducible = True
                if not irreducible:
                    rejected["reducible"] += 1
                    continue
                if args.root_count_mode == "exact":
                    candidate.real_roots = real_root_count(candidate.coeffs)
                elif args.root_count_mode == "numeric":
                    candidate.real_roots = numeric_real_root_count(candidate.coeffs)
                else:
                    candidate.real_roots = -1
            except Exception:
                rejected["root_count_failed"] += 1
                continue

            selected.append(candidate)
            accepted_here += 1

    quotas = {
        "composition": max(1, round(args.count * 0.35)),
        "trinomial": max(1, round(args.count * 0.25)),
        "four-nomial": max(1, round(args.count * 0.25)),
    }
    quotas["random-sparse"] = max(1, args.count - sum(quotas.values()))
    groups: list[tuple[str, Iterable[Candidate], int]] = [
        ("composition", composed_polynomials(), quotas["composition"]),
        ("trinomial", sparse_trinomials(), quotas["trinomial"]),
        ("four-nomial", sparse_fournomials(), quotas["four-nomial"]),
        ("random-sparse", random_sparse(args.seed, args.random_candidates), quotas["random-sparse"]),
    ]

    for _name, stream, quota in groups:
        accept_from(stream, quota)
        if len(selected) >= args.count:
            break
    if len(selected) < args.count:
        accept_from(random_sparse(args.seed + 1, args.random_candidates * 2), args.count - len(selected))

    for candidate in selected:
        family_counts[candidate.family] = family_counts.get(candidate.family, 0) + 1
        root_key = str(candidate.real_roots)
        root_counts[root_key] = root_counts.get(root_key, 0) + 1

    running_family_counts: dict[str, int] = {}
    running_root_counts: dict[str, int] = {}
    for candidate in selected:
        root_key = str(candidate.real_roots)
        running_family_counts[candidate.family] = running_family_counts.get(candidate.family, 0) + 1
        running_root_counts[root_key] = running_root_counts.get(root_key, 0) + 1
        coeff_size = max_abs_coeff(candidate.coeffs)
        candidate.score = (
            root_counts[root_key],
            family_counts[candidate.family],
            coeff_size,
            running_root_counts[root_key],
            running_family_counts[candidate.family],
            len([c for c in candidate.coeffs if c]),
        )

    selected.sort(key=lambda item: item.score)
    report = {
        "generated_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "requested_count": args.count,
        "selected_count": len(selected),
        "seed": args.seed,
        "max_abs_coeff": args.max_abs_coeff,
        "irreducibility_mode": args.irreducibility_mode,
        "root_count_mode": args.root_count_mode,
        "quotas": quotas,
        "family_counts": family_counts,
        "real_root_counts": root_counts,
        "rejected": rejected,
    }
    return selected, report


def write_outputs(selected: list[Candidate], report: dict[str, object], output: Path, manifest: Path) -> None:
    output.parent.mkdir(parents=True, exist_ok=True)
    manifest.parent.mkdir(parents=True, exist_ok=True)
    output.write_text("\n".join(candidate.line for candidate in selected) + ("\n" if selected else ""), encoding="utf-8")
    payload = dict(report)
    payload["selected"] = [
        {
            "line_number": index + 1,
            "family": candidate.family,
            "params": candidate.params,
            "real_roots_local": candidate.real_roots,
            "max_abs_coeff": max_abs_coeff(candidate.coeffs),
            "nonzero_terms": len([c for c in candidate.coeffs if c]),
        }
        for index, candidate in enumerate(selected)
    ]
    manifest.write_text(json.dumps(payload, indent=2), encoding="utf-8")


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--count", type=int, default=1000, help="number of polynomials to write")
    parser.add_argument("--seed", type=int, default=20260706)
    parser.add_argument("--random-candidates", type=int, default=5000)
    parser.add_argument("--max-abs-coeff", type=int, default=250000)
    parser.add_argument("--irreducibility-mode", choices=("modular", "exact", "none"), default="modular")
    parser.add_argument("--root-count-mode", choices=("numeric", "exact", "none"), default="numeric")
    parser.add_argument("--output", type=Path, default=Path("igp24/discovery_batch.txt"))
    parser.add_argument("--manifest", type=Path, default=Path("igp24/discovery_manifest.json"))
    args = parser.parse_args(argv)

    if args.count < 1 or args.count > 1000:
        parser.error("--count must be between 1 and 1000")

    selected, report = select_candidates(args)
    write_outputs(selected, report, args.output, args.manifest)
    print(f"selected={len(selected)}")
    print(f"output={args.output}")
    print(f"manifest={args.manifest}")
    print(f"family_counts={json.dumps(report['family_counts'], sort_keys=True)}")
    print(f"real_root_counts={json.dumps(report['real_root_counts'], sort_keys=True)}")
    if len(selected) < args.count:
        print("warning: selected fewer candidates than requested", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
