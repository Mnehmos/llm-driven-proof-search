#!/usr/bin/env python3
"""Verify labeled IGP24 candidates with Magma before running the SAIR gate.

The input format is the same labeled CSV/JSON/JSONL accepted by
`igp24_gate.py`. The script writes a Magma batch file, runs `magma` when it is
available, parses transitive-group identifications, and emits a candidate CSV
containing only rows whose Magma label matches the expected label.

Magma's `GaloisGroup` documentation says the direct result may contain
conditional steps; pass `--require-proof` to keep only rows for which
`GaloisProof` succeeds.
"""

from __future__ import annotations

import argparse
import csv
import json
import os
import shutil
import subprocess
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any

import sympy as sp

from igp24_gate import Candidate, GateError, parse_polynomial, read_candidates


RESULT_PREFIX = "IGP24_MAGMA"
MAGMA_FIELDS = [
    "magma_status",
    "magma_irreducible",
    "magma_degree",
    "magma_index",
    "magma_label",
    "magma_group_order",
    "magma_seconds",
    "magma_galois_proof",
    "computed_r",
    "magma_keep_reason",
]


@dataclass
class MagmaResult:
    row: int
    expected_label: str
    expected_r: int
    status: str
    polynomial_degree: int
    irreducible: bool
    magma_degree: int
    magma_index: int
    magma_label: str
    group_order: str
    seconds: str
    proof: bool


def parse_bool(value: str) -> bool:
    return value.strip().lower() in {"true", "1", "yes"}


def parse_int_field(value: str, default: int = 0) -> int:
    try:
        return int(value.strip())
    except ValueError:
        return default


def candidate_coefficients(candidate: Candidate) -> list[int]:
    coeffs, errors = parse_polynomial(candidate.polynomial)
    if errors or coeffs is None:
        raise GateError(f"row {candidate.row_number}: invalid polynomial: {'; '.join(errors)}")
    return coeffs


def real_root_count(coeffs: list[int]) -> int:
    x = sp.Symbol("x")
    poly = sp.Poly.from_list(list(reversed(coeffs)), gens=x)
    return int(poly.count_roots(sp.S.NegativeInfinity, sp.S.Infinity))


def magma_string(value: str) -> str:
    return '"' + value.replace("\\", "\\\\").replace('"', '\\"') + '"'


def magma_coeff_sequence(coeffs: list[int]) -> str:
    return "[" + ",".join(str(coeff) for coeff in coeffs) + "]"


def write_magma_script(
    candidates: list[Candidate],
    script_path: Path,
    short_ok: bool,
    run_galois_proof: bool,
) -> None:
    script_path.parent.mkdir(parents=True, exist_ok=True)
    lines = [
        "SetColumns(0);",
        'SetVerbose("GaloisGroup", 0);',
        'SetVerbose("Invariant", 0);',
        "Zx<x> := PolynomialRing(Integers());",
        "",
        "procedure IGP24Check(row, expected_label, expected_r, coeffs)",
        "    f := Zx!coeffs;",
        '    status := "ok";',
        "    is_irreducible := false;",
        "    magma_degree := 0;",
        "    magma_index := 0;",
        '    magma_label := "";',
        "    group_order := 0;",
        "    elapsed := 0;",
        "    proof := false;",
        "    try",
        "        is_irreducible := IsIrreducible(f);",
        "        if is_irreducible then",
        "            start_time := Cputime();",
        f"            G, roots, data := GaloisGroup(f : ShortOK := {'true' if short_ok else 'false'});",
        "            elapsed := Cputime(start_time);",
        "            magma_index, magma_degree := TransitiveGroupIdentification(G);",
        '            magma_label := Sprint(magma_degree) cat "T" cat Sprint(magma_index);',
        "            group_order := #G;",
    ]
    if run_galois_proof:
        lines.append("            proof := GaloisProof(f, data);")
    lines.extend(
        [
            "        else",
            '            status := "reducible";',
            "        end if;",
            (
                f'        printf "{RESULT_PREFIX}\\t%o\\t%o\\t%o\\t%o\\t%o\\t%o\\t%o\\t%o\\t%o\\t%o\\t%o\\t%o\\n", '
                "row, expected_label, expected_r, status, Degree(f), is_irreducible, magma_degree, "
                "magma_index, magma_label, group_order, elapsed, proof;"
            ),
            "    catch e",
            (
                f'        printf "{RESULT_PREFIX}\\t%o\\t%o\\t%o\\terror\\t%o\\tfalse\\t0\\t0\\t\\t0\\t0\\tfalse\\n", '
                "row, expected_label, expected_r, Degree(f);"
            ),
            "    end try;",
            "end procedure;",
            "",
        ]
    )

    for candidate in candidates:
        coeffs = candidate_coefficients(candidate)
        lines.append(
            "IGP24Check("
            f"{candidate.row_number}, "
            f"{magma_string(candidate.label)}, "
            f"{candidate.r}, "
            f"{magma_coeff_sequence(coeffs)}"
            ");"
        )
    lines.append("quit;")
    script_path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def resolve_magma_binary(value: str) -> str | None:
    expanded = os.path.expandvars(os.path.expanduser(value))
    if Path(expanded).exists():
        return expanded
    return shutil.which(expanded)


def parse_magma_results(stdout: str) -> dict[int, MagmaResult]:
    results: dict[int, MagmaResult] = {}
    for line in stdout.splitlines():
        if not line.startswith(RESULT_PREFIX + "\t"):
            continue
        parts = line.split("\t")
        if len(parts) < 13:
            continue
        result = MagmaResult(
            row=parse_int_field(parts[1], -1),
            expected_label=parts[2],
            expected_r=parse_int_field(parts[3], -1),
            status=parts[4],
            polynomial_degree=parse_int_field(parts[5]),
            irreducible=parse_bool(parts[6]),
            magma_degree=parse_int_field(parts[7]),
            magma_index=parse_int_field(parts[8]),
            magma_label=parts[9],
            group_order=parts[10],
            seconds=parts[11],
            proof=parse_bool(parts[12]),
        )
        if result.row >= 0:
            results[result.row] = result
    return results


def write_report(
    report_path: Path,
    *,
    input_path: Path,
    output_path: Path,
    script_path: Path,
    magma_bin: str | None,
    candidates: list[Candidate],
    results: dict[int, MagmaResult],
    selected_rows: list[int],
    skipped: list[dict[str, Any]],
    stdout: str = "",
    stderr: str = "",
    returncode: int | None = None,
    status: str = "ok",
) -> None:
    report_path.parent.mkdir(parents=True, exist_ok=True)
    report_path.write_text(
        json.dumps(
            {
                "generated_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
                "status": status,
                "input": str(input_path),
                "output": str(output_path),
                "magma_script": str(script_path),
                "magma_bin": magma_bin,
                "magma_returncode": returncode,
                "candidate_count": len(candidates),
                "result_count": len(results),
                "selected_count": len(selected_rows),
                "skipped_count": len(skipped),
                "selected_rows": selected_rows,
                "skipped": skipped,
                "stdout_tail": stdout[-20000:],
                "stderr_tail": stderr[-20000:],
            },
            indent=2,
        ),
        encoding="utf-8",
    )


def write_verified_csv(
    candidates: list[Candidate],
    results: dict[int, MagmaResult],
    output_path: Path,
    require_proof: bool,
    skip_real_root_check: bool,
) -> tuple[list[int], list[dict[str, Any]]]:
    output_path.parent.mkdir(parents=True, exist_ok=True)
    rows: list[dict[str, Any]] = []
    skipped: list[dict[str, Any]] = []

    fieldnames: list[str] = []
    for candidate in candidates:
        for key in candidate.fields:
            if key not in fieldnames:
                fieldnames.append(key)
    for key in MAGMA_FIELDS:
        if key not in fieldnames:
            fieldnames.append(key)

    selected_rows: list[int] = []
    for candidate in candidates:
        row = dict(candidate.fields)
        result = results.get(candidate.row_number)
        computed_r: int | None = None
        if not skip_real_root_check:
            computed_r = real_root_count(candidate_coefficients(candidate))

        if result is None:
            reason = "missing Magma result"
            row.update({"computed_r": computed_r, "magma_keep_reason": reason})
            skipped.append({"row": candidate.row_number, "label": candidate.label, "r": candidate.r, "reason": reason})
            continue

        keep_reasons: list[str] = []
        reject_reasons: list[str] = []
        if result.status != "ok":
            reject_reasons.append(f"Magma status {result.status}")
        if not result.irreducible:
            reject_reasons.append("Magma says reducible")
        if result.magma_label != candidate.label:
            reject_reasons.append(f"Magma label {result.magma_label or '<none>'} != expected {candidate.label}")
        if require_proof and not result.proof:
            reject_reasons.append("GaloisProof did not succeed")
        if computed_r is not None and computed_r != candidate.r:
            reject_reasons.append(f"computed r={computed_r} != expected r={candidate.r}")
        if not reject_reasons:
            keep_reasons.append("Magma label and local r match")

        row.update(
            {
                "magma_status": result.status,
                "magma_irreducible": str(result.irreducible).lower(),
                "magma_degree": result.magma_degree,
                "magma_index": result.magma_index,
                "magma_label": result.magma_label,
                "magma_group_order": result.group_order,
                "magma_seconds": result.seconds,
                "magma_galois_proof": str(result.proof).lower(),
                "computed_r": computed_r if computed_r is not None else "",
                "magma_keep_reason": "; ".join(keep_reasons or reject_reasons),
            }
        )

        if reject_reasons:
            skipped.append({
                "row": candidate.row_number,
                "label": candidate.label,
                "r": candidate.r,
                "reason": "; ".join(reject_reasons),
            })
            continue

        selected_rows.append(candidate.row_number)
        rows.append(row)

    with output_path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(rows)
    return selected_rows, skipped


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("candidates", type=Path)
    parser.add_argument("--output", type=Path, default=Path("data/igp24/magma_verified_candidates.csv"))
    parser.add_argument("--report", type=Path, default=Path("igp24/magma_verify_report.json"))
    parser.add_argument("--magma-script", type=Path, default=Path("igp24/magma_verify.m"))
    parser.add_argument("--magma-bin", default=os.environ.get("MAGMA_BIN", "magma"))
    parser.add_argument("--timeout-seconds", type=int, default=3600)
    parser.add_argument("--short-ok", action="store_true", help="pass ShortOK:=true to Magma GaloisGroup")
    parser.add_argument("--run-galois-proof", action="store_true", help="call Magma GaloisProof for each successful row")
    parser.add_argument("--require-proof", action="store_true", help="keep only rows whose GaloisProof result is true")
    parser.add_argument("--skip-real-root-check", action="store_true")
    parser.add_argument("--write-script-only", action="store_true")
    args = parser.parse_args(argv)

    candidates = read_candidates(args.candidates)
    write_magma_script(
        candidates,
        args.magma_script,
        short_ok=args.short_ok,
        run_galois_proof=args.run_galois_proof or args.require_proof,
    )

    magma_bin = resolve_magma_binary(args.magma_bin)
    if args.write_script_only:
        write_report(
            args.report,
            input_path=args.candidates,
            output_path=args.output,
            script_path=args.magma_script,
            magma_bin=magma_bin,
            candidates=candidates,
            results={},
            selected_rows=[],
            skipped=[],
            status="script_only",
        )
        print(f"magma_script={args.magma_script}")
        print(f"report={args.report}")
        return 0

    if magma_bin is None:
        write_report(
            args.report,
            input_path=args.candidates,
            output_path=args.output,
            script_path=args.magma_script,
            magma_bin=None,
            candidates=candidates,
            results={},
            selected_rows=[],
            skipped=[],
            status="missing_magma",
        )
        print(f"magma executable not found: {args.magma_bin}", file=sys.stderr)
        print(f"wrote Magma script: {args.magma_script}", file=sys.stderr)
        return 3

    completed = subprocess.run(
        [magma_bin, str(args.magma_script)],
        cwd=str(Path.cwd()),
        text=True,
        capture_output=True,
        timeout=args.timeout_seconds,
        check=False,
    )
    results = parse_magma_results(completed.stdout)
    selected_rows, skipped = write_verified_csv(
        candidates,
        results,
        args.output,
        require_proof=args.require_proof,
        skip_real_root_check=args.skip_real_root_check,
    )
    write_report(
        args.report,
        input_path=args.candidates,
        output_path=args.output,
        script_path=args.magma_script,
        magma_bin=magma_bin,
        candidates=candidates,
        results=results,
        selected_rows=selected_rows,
        skipped=skipped,
        stdout=completed.stdout,
        stderr=completed.stderr,
        returncode=completed.returncode,
        status="ok" if completed.returncode == 0 else "magma_failed",
    )
    print(f"loaded_candidates={len(candidates)}")
    print(f"magma_results={len(results)}")
    print(f"selected={len(selected_rows)}")
    print(f"skipped={len(skipped)}")
    print(f"output={args.output}")
    print(f"report={args.report}")
    if completed.returncode != 0:
        return completed.returncode
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main(sys.argv[1:]))
    except GateError as exc:
        print(f"error: {exc}", file=sys.stderr)
        raise SystemExit(2)
