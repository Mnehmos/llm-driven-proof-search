#!/usr/bin/env python3
"""Generate small high-real-root IGP24 probe batches from lower-degree fields.

Modes:

* cubic8:  f(x^3 - 3 M x), where f is totally real degree 8.
  If all roots of f lie in (-2 M^(3/2), 2 M^(3/2)), each root has three real
  preimages, so the degree-24 lift has 24 real roots.

* quartic6: f((x^2 - M)^2 - N), where f is totally real degree 6.
  N and M are chosen so 0 < alpha + N < M^2 for every root alpha of f, giving
  four real preimages per root.

* sextic4: f((x^3 - 3 M x)^2 - N), where f is totally real degree 4.
  N and M are chosen so 0 < alpha + N and sqrt(alpha + N) lies in the
  three-real-root range of x^3 - 3 M x, giving six real preimages per root.

These are intentionally small probe generators. Use SAIR as the exact 24T
label oracle, then expand only modes/slices that hit low-team labels.
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
USER_AGENT = "igp24-lift-probes/0.1 (+https://competition.sair.foundation/competitions/igp24)"


class ProbeError(RuntimeError):
    pass


def fetch_lmfdb_degree(path: Path, degree: int) -> str:
    query = {
        "download": "1",
        "query": f"{{'degree': {degree}, 'r2': 0}}",
        "degree": str(degree),
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


def parse_lmfdb_text(text: str, source_url: str, degree: int) -> list[dict[str, Any]]:
    prefix = f"{degree}.{degree}."
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
            raise ProbeError(f"could not parse LMFDB line {line_number}: {line[:160]}") from exc
        if not str(field_label).startswith(prefix):
            continue
        if not isinstance(coeffs, list) or len(coeffs) != degree + 1:
            continue
        rows.append(
            {
                "field_label": field_label,
                "coeffs": [int(c) for c in coeffs],
                "discriminant": abs(discriminant),
                "galois_label": str(galois_label),
                "source_url": source_url,
            }
        )
    rows.sort(key=lambda row: (row["galois_label"], row["discriminant"], row["field_label"]))
    return rows


def coefficient_gcd(coeffs: list[int]) -> int:
    value = 0
    for coeff in coeffs:
        value = math.gcd(value, abs(coeff))
    return value


def real_roots(poly: sp.Poly) -> list[float] | None:
    try:
        roots = poly.nroots(n=50, maxsteps=300)
    except Exception:
        return None
    values: list[float] = []
    for root in roots:
        if abs(float(sp.im(root))) > 1e-18:
            return None
        values.append(float(sp.re(root)))
    return values


def cubic_parameter(roots: list[float], extra: int) -> int:
    bound = max(abs(root) for root in roots)
    m = max(1, math.ceil((bound / 2) ** (2 / 3)) + 1 + extra)
    while 2 * (m ** 1.5) <= bound:
        m += 1
    return m


def quartic_parameters(roots: list[float], extra: int) -> tuple[int, int]:
    min_root = min(roots)
    max_root = max(roots)
    n = max(1, math.floor(-min_root) + 1 + extra)
    upper = max_root + n
    if upper <= 0:
        upper = 1
    m = max(1, math.floor(math.sqrt(upper)) + 1 + extra)
    while m * m <= upper:
        m += 1
    return m, n


def lift_row(row: dict[str, Any], mode: str, extra: int) -> dict[str, Any] | None:
    x = sp.Symbol("x")
    y = sp.Symbol("y")
    source_degree = {"cubic8": 8, "quartic6": 6, "sextic4": 4}[mode]
    f = sp.Poly.from_list(list(reversed(row["coeffs"])), gens=y, domain=sp.ZZ)
    if f.degree() != source_degree or not f.is_irreducible:
        return None
    roots = real_roots(f)
    if roots is None:
        return None

    params: dict[str, int] = {}
    if mode == "cubic8":
        m = cubic_parameter(roots, extra)
        inner = x**3 - 3 * m * x
        params["M"] = m
    elif mode == "quartic6":
        m, n = quartic_parameters(roots, extra)
        inner = (x**2 - m) ** 2 - n
        params["M"] = m
        params["N"] = n
    elif mode == "sextic4":
        n = max(1, math.floor(-min(roots)) + 1 + extra)
        upper = max(root + n for root in roots)
        m = cubic_parameter([math.sqrt(upper)], extra)
        inner_cubic = x**3 - 3 * m * x
        inner = inner_cubic**2 - n
        params["M"] = m
        params["N"] = n
    else:
        raise ValueError(f"unknown mode {mode}")

    h = sp.Poly(f.as_expr().subs(y, inner), x, domain=sp.ZZ)
    coeffs = [int(c) for c in reversed(h.all_coeffs())]
    if h.degree() != 24 or coeffs[-1] != 1 or coeffs[0] == 0 or coefficient_gcd(coeffs) != 1:
        return None
    if not h.is_irreducible:
        return None
    root_count = int(h.count_roots(sp.S.NegativeInfinity, sp.S.Infinity))
    if root_count != 24:
        return None
    return {
        "polynomial": ",".join(str(c) for c in coeffs),
        "mode": mode,
        "source_degree": source_degree,
        "source_label": row["galois_label"],
        "field_label": row["field_label"],
        "source_disc_abs": row["discriminant"],
        "params": params,
        "max_abs_coeff": max(abs(c) for c in coeffs),
        "nonzero_terms": sum(1 for c in coeffs if c),
        "source": f"LMFDB degree-{source_degree} totally real {mode} lift",
        "provenance": row["source_url"],
    }


def select_lifts(rows: list[dict[str, Any]], mode: str, limit: int, skip: int, max_abs_coeff: int, extra: int) -> list[dict[str, Any]]:
    selected: list[dict[str, Any]] = []
    seen_source_labels: set[str] = set()
    seen_polynomials: set[str] = set()

    for row in rows:
        if len(selected) >= skip + limit:
            break
        if row["galois_label"] in seen_source_labels:
            continue
        lifted = lift_row(row, mode, extra)
        if lifted is None or lifted["max_abs_coeff"] > max_abs_coeff:
            continue
        seen_source_labels.add(row["galois_label"])
        seen_polynomials.add(lifted["polynomial"])
        selected.append(lifted)

    for row in rows:
        if len(selected) >= skip + limit:
            break
        lifted = lift_row(row, mode, extra)
        if lifted is None or lifted["max_abs_coeff"] > max_abs_coeff:
            continue
        if lifted["polynomial"] in seen_polynomials:
            continue
        seen_polynomials.add(lifted["polynomial"])
        selected.append(lifted)

    selected.sort(key=lambda row: (row["source_label"], int(row["source_disc_abs"]), int(row["max_abs_coeff"])))
    return selected[skip : skip + limit]


def write_outputs(selected: list[dict[str, Any]], output: Path, manifest: Path, source_url: str, source_count: int, args: argparse.Namespace) -> None:
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text("\n".join(row["polynomial"] for row in selected) + ("\n" if selected else ""), encoding="utf-8")

    manifest.parent.mkdir(parents=True, exist_ok=True)
    manifest.write_text(
        json.dumps(
            {
                "generated_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
                "mode": args.mode,
                "skip": args.skip,
                "limit": args.limit,
                "extra": args.extra,
                "max_abs_coeff": args.max_abs_coeff,
                "source_url": source_url,
                "source_count": source_count,
                "selected_count": len(selected),
                "selected": selected,
            },
            indent=2,
        ),
        encoding="utf-8",
    )


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mode", choices=("cubic8", "quartic6", "sextic4"), required=True)
    parser.add_argument("--input", type=Path)
    parser.add_argument("--download", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--limit", type=int, default=12)
    parser.add_argument("--skip", type=int, default=0)
    parser.add_argument("--max-abs-coeff", type=int, default=10**14)
    parser.add_argument("--extra", type=int, default=0)
    args = parser.parse_args(argv)

    degree = {"cubic8": 8, "quartic6": 6, "sextic4": 4}[args.mode]
    if args.input:
        source_url = f"local:{args.input}"
        text = args.input.read_text(encoding="utf-8")
    else:
        download = args.download or Path(f"data/igp24/lmfdb_degree{degree}_totally_real.txt")
        source_url = fetch_lmfdb_degree(download, degree)
        text = download.read_text(encoding="utf-8")
    rows = parse_lmfdb_text(text, source_url, degree)
    selected = select_lifts(rows, args.mode, args.limit, args.skip, args.max_abs_coeff, args.extra)
    write_outputs(selected, args.output, args.manifest, source_url, len(rows), args)
    print(f"source_rows={len(rows)}")
    print(f"selected={len(selected)}")
    print(f"output={args.output}")
    print(f"manifest={args.manifest}")
    return 0 if selected else 1


if __name__ == "__main__":
    try:
        raise SystemExit(main(sys.argv[1:]))
    except ProbeError as exc:
        print(f"error: {exc}", file=sys.stderr)
        raise SystemExit(2)
