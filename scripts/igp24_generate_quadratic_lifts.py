#!/usr/bin/env python3
"""Generate IGP24 discovery candidates from quadratic lifts of degree-12 fields.

For a totally real degree-12 polynomial f(y), choose an integer M such that all
roots of f(y) shifted by M are positive. Then f(x^2 - M) has 24 real roots.
This gives a structured imprimitive discovery batch aimed at high-r IGP24
targets without needing a local Magma label first.
"""

from __future__ import annotations

import argparse
import ast
import csv
import json
import math
import sys
import time
import urllib.parse
import urllib.request
from pathlib import Path
from typing import Any

import sympy as sp


LMFDB_DOWNLOAD_URL = "https://www.lmfdb.org/NumberField/"
USER_AGENT = "igp24-quadratic-lifts/0.1 (+https://competition.sair.foundation/competitions/igp24)"


class LiftError(RuntimeError):
    pass


def label_number(label: str) -> int:
    if label.startswith("12T"):
        try:
            return int(label[3:])
        except ValueError:
            pass
    return 10**9


def fetch_lmfdb_degree12(path: Path) -> str:
    query = {
        "download": "1",
        "query": "{'degree': 12, 'r2': 0}",
        "degree": "12",
        "r2": "0",
        "count": "100",
    }
    url = f"{LMFDB_DOWNLOAD_URL}?{urllib.parse.urlencode(query)}"
    request = urllib.request.Request(url, headers={"User-Agent": USER_AGENT, "Accept": "text/plain,*/*"})
    with urllib.request.urlopen(request, timeout=180) as response:
        text = response.read().decode("utf-8")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")
    return url


def parse_lmfdb_text(text: str, source_url: str) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for line_number, line in enumerate(text.splitlines(), start=1):
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        parts = line.split("\t")
        if len(parts) < 4:
            continue
        try:
            field_label = ast.literal_eval(parts[0])
            coeffs = ast.literal_eval(parts[1])
            discriminant = int(parts[2])
            galois_label = ast.literal_eval(parts[3])
        except Exception as exc:
            raise LiftError(f"could not parse LMFDB line {line_number}: {line[:160]}") from exc
        if not str(field_label).startswith("12.12."):
            continue
        if not isinstance(coeffs, list) or len(coeffs) != 13:
            continue
        rows.append({
            "field_label": field_label,
            "coeffs": [int(c) for c in coeffs],
            "discriminant": abs(discriminant),
            "galois_label": str(galois_label),
            "source_url": source_url,
        })
    rows.sort(key=lambda row: (label_number(row["galois_label"]), row["discriminant"], row["field_label"]))
    return rows


def coefficient_gcd(coeffs: list[int]) -> int:
    value = 0
    for coeff in coeffs:
        value = math.gcd(value, abs(coeff))
    return value


def max_shift_for_positive_roots(poly: sp.Poly, extra_shift: int) -> int | None:
    try:
        roots = poly.nroots(n=40, maxsteps=200)
    except Exception:
        return None
    real_parts: list[float] = []
    for root in roots:
        if abs(float(sp.im(root))) > 1e-20:
            return None
        real_parts.append(float(sp.re(root)))
    min_root = min(real_parts)
    return max(0, math.floor(-min_root) + 1 + extra_shift)


def lift_row(row: dict[str, Any], extra_shift: int) -> dict[str, Any] | None:
    x = sp.Symbol("x")
    y = sp.Symbol("y")
    f = sp.Poly.from_list(list(reversed(row["coeffs"])), gens=y, domain=sp.ZZ)
    if f.degree() != 12 or not f.is_irreducible:
        return None
    shift = max_shift_for_positive_roots(f, extra_shift)
    if shift is None:
        return None
    h = sp.Poly(f.as_expr().subs(y, x**2 - shift), x, domain=sp.ZZ)
    coeffs = [int(c) for c in reversed(h.all_coeffs())]
    if h.degree() != 24 or coeffs[-1] != 1 or coeffs[0] == 0 or coefficient_gcd(coeffs) != 1:
        return None
    if not h.is_irreducible:
        return None
    real_roots = int(h.count_roots(sp.S.NegativeInfinity, sp.S.Infinity))
    if real_roots != 24:
        return None
    return {
        "polynomial": ",".join(str(c) for c in coeffs),
        "degree12_label": row["galois_label"],
        "field_label": row["field_label"],
        "degree12_disc_abs": row["discriminant"],
        "shift": shift,
        "max_abs_coeff": max(abs(c) for c in coeffs),
        "nonzero_terms": sum(1 for c in coeffs if c),
        "source": "LMFDB degree-12 totally real quadratic lift",
        "provenance": row["source_url"],
    }


def select_lifts(
    rows: list[dict[str, Any]],
    limit: int,
    max_abs_coeff: int,
    extra_shift: int,
    source_label_min: int | None,
    source_label_max: int | None,
) -> list[dict[str, Any]]:
    selected: list[dict[str, Any]] = []
    seen_degree12_labels: set[str] = set()
    seen_polynomials: set[str] = set()
    filtered_rows = [
        row
        for row in rows
        if (source_label_min is None or label_number(row["galois_label"]) >= source_label_min)
        and (source_label_max is None or label_number(row["galois_label"]) <= source_label_max)
    ]

    # First pass: maximize source-label diversity.
    for row in filtered_rows:
        if len(selected) >= limit:
            break
        if row["galois_label"] in seen_degree12_labels:
            continue
        lifted = lift_row(row, extra_shift)
        if lifted is None or lifted["max_abs_coeff"] > max_abs_coeff:
            continue
        seen_degree12_labels.add(row["galois_label"])
        seen_polynomials.add(lifted["polynomial"])
        selected.append(lifted)

    # Second pass: fill remaining slots with additional low-discriminant fields.
    for row in filtered_rows:
        if len(selected) >= limit:
            break
        lifted = lift_row(row, extra_shift)
        if lifted is None or lifted["max_abs_coeff"] > max_abs_coeff:
            continue
        if lifted["polynomial"] in seen_polynomials:
            continue
        seen_polynomials.add(lifted["polynomial"])
        selected.append(lifted)

    selected.sort(key=lambda row: (label_number(row["degree12_label"]), int(row["degree12_disc_abs"]), int(row["max_abs_coeff"])))
    return selected


def write_outputs(
    selected: list[dict[str, Any]],
    output: Path,
    manifest: Path,
    source_url: str,
    source_count: int,
    skipped_selected: int,
) -> None:
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text("\n".join(row["polynomial"] for row in selected) + ("\n" if selected else ""), encoding="utf-8")

    manifest.parent.mkdir(parents=True, exist_ok=True)
    manifest.write_text(
        json.dumps(
            {
                "generated_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
                "source_url": source_url,
                "source_count": source_count,
                "skipped_selected": skipped_selected,
                "selected_count": len(selected),
                "selected": selected,
            },
            indent=2,
        ),
        encoding="utf-8",
    )


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--download", type=Path, default=Path("data/igp24/lmfdb_degree12_totally_real.txt"))
    parser.add_argument("--input", type=Path)
    parser.add_argument("--output", type=Path, default=Path("igp24/quadratic_lift_r24_batch.txt"))
    parser.add_argument("--manifest", type=Path, default=Path("igp24/quadratic_lift_r24_manifest.json"))
    parser.add_argument("--limit", type=int, default=25)
    parser.add_argument("--skip", type=int, default=0, help="skip this many selected lifts before writing output")
    parser.add_argument("--max-abs-coeff", type=int, default=10**12)
    parser.add_argument("--extra-shift", type=int, default=0)
    parser.add_argument("--source-label-min", type=int, help="keep only source labels 12Tn with n at least this value")
    parser.add_argument("--source-label-max", type=int, help="keep only source labels 12Tn with n at most this value")
    args = parser.parse_args(argv)

    if args.input:
        source_url = f"local:{args.input}"
        text = args.input.read_text(encoding="utf-8")
    else:
        source_url = fetch_lmfdb_degree12(args.download)
        text = args.download.read_text(encoding="utf-8")
    rows = parse_lmfdb_text(text, source_url)
    selected_pool = select_lifts(
        rows,
        args.skip + args.limit,
        args.max_abs_coeff,
        args.extra_shift,
        args.source_label_min,
        args.source_label_max,
    )
    selected = selected_pool[args.skip : args.skip + args.limit]
    write_outputs(selected, args.output, args.manifest, source_url, len(rows), args.skip)
    print(f"source_rows={len(rows)}")
    print(f"selected={len(selected)}")
    print(f"output={args.output}")
    print(f"manifest={args.manifest}")
    if len(selected) < args.limit:
        print("warning: selected fewer rows than requested", file=sys.stderr)
    return 0 if selected else 1


if __name__ == "__main__":
    try:
        raise SystemExit(main(sys.argv[1:]))
    except LiftError as exc:
        print(f"error: {exc}", file=sys.stderr)
        raise SystemExit(2)
