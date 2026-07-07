#!/usr/bin/env python3
"""Source IGP24 candidates from Mueller's M24 one-parameter family.

This script uses the compact s=0 specialization displayed in:

Peter Mueller, "A one-parameter family of polynomials with Galois group
M24 over Q(t)", arXiv:1204.1328.

For integer t-values it builds

    (t - A0(X))^2 + (X^2 + 1) B0(X)^2

and applies the small linear scaling X = Y/8 that makes the polynomial
monic with integer coefficients. The resulting rows are candidate
specializations; the official verifier remains the authority for the exact
24T label of each specialization.
"""

from __future__ import annotations

import argparse
import csv
import json
import math
import sys
import time
from pathlib import Path
from typing import Any

import sympy as sp


LABEL = "24T24680"
SOURCE = "Mueller M24 family, s=0"
PROVENANCE = "https://arxiv.org/abs/1204.1328"
SCALE = 8


def polynomial_coefficients(t_value: int) -> list[int]:
    x = sp.Symbol("x")
    a0 = (
        4194304 * x**12
        - 72351744 * x**10
        + 1572864 * x**9
        + 154443776 * x**8
        - 34062336 * x**7
        + 46684160 * x**6
        + 16098816 * x**5
        - 156060348 * x**4
        + 30667728 * x**3
        - 5330757 * x**2
        - 3462498 * x
        + 9958791
    )
    b0 = (
        -25165824 * x**10
        - 1572864 * x**9
        + 145227776 * x**8
        - 16515072 * x**7
        - 164757504 * x**6
        + 48453120 * x**5
        - 56207872 * x**4
        - 6865152 * x**3
        + 71415384 * x**2
        - 8906760 * x
        + 224829
    )

    f = sp.Poly((sp.Integer(t_value) - a0) ** 2 + (x**2 + 1) * b0**2, x)
    coeffs_low = [int(c) for c in reversed(f.all_coeffs())]
    leading = coeffs_low[-1]
    scaled: list[int] = []
    for degree, coeff in enumerate(coeffs_low):
        if degree == 24:
            scaled.append(1)
            continue
        numerator = coeff * SCALE ** (24 - degree)
        if numerator % leading != 0:
            raise ValueError(f"scale {SCALE} does not clear denominator at degree {degree}")
        scaled.append(numerator // leading)
    return scaled


def coefficient_gcd(coeffs: list[int]) -> int:
    value = 0
    for coeff in coeffs:
        value = math.gcd(value, abs(coeff))
    return value


def real_root_count(coeffs: list[int]) -> int:
    x = sp.Symbol("x")
    poly = sp.Poly.from_list(list(reversed(coeffs)), gens=x)
    return int(poly.count_roots(sp.S.NegativeInfinity, sp.S.Infinity))


def iter_t_values(start: int, stop: int) -> list[int]:
    if start > stop:
        raise ValueError("--t-min must be <= --t-max")
    return list(range(start, stop + 1))


def write_candidates(rows: list[dict[str, Any]], output: Path, report: Path) -> None:
    output.parent.mkdir(parents=True, exist_ok=True)
    fieldnames = ["label", "r", "polynomial", "source", "provenance", "t_value", "note"]
    with output.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(rows)

    report.parent.mkdir(parents=True, exist_ok=True)
    report.write_text(
        json.dumps(
            {
                "generated_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
                "source": SOURCE,
                "provenance": PROVENANCE,
                "label": LABEL,
                "scale": SCALE,
                "row_count": len(rows),
                "r_counts": {
                    str(r): sum(1 for row in rows if row["r"] == r)
                    for r in sorted({row["r"] for row in rows})
                },
            },
            indent=2,
        ),
        encoding="utf-8",
    )


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--t-min", type=int, default=-25)
    parser.add_argument("--t-max", type=int, default=25)
    parser.add_argument("--output", type=Path, default=Path("data/igp24/m24_muller_candidates.csv"))
    parser.add_argument("--report", type=Path, default=Path("data/igp24/m24_muller_candidates_report.json"))
    args = parser.parse_args(argv)

    rows: list[dict[str, Any]] = []
    for t_value in iter_t_values(args.t_min, args.t_max):
        coeffs = polynomial_coefficients(t_value)
        if len(coeffs) != 25 or coeffs[-1] != 1 or coeffs[0] == 0 or coefficient_gcd(coeffs) != 1:
            continue
        rows.append(
            {
                "label": LABEL,
                "r": real_root_count(coeffs),
                "polynomial": ",".join(str(coeff) for coeff in coeffs),
                "source": SOURCE,
                "provenance": PROVENANCE,
                "t_value": t_value,
                "note": "s=0, X=Y/8 monic integral scaling",
            }
        )

    write_candidates(rows, args.output, args.report)
    print(f"rows={len(rows)}")
    print(f"output={args.output}")
    print(f"report={args.report}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
