#!/usr/bin/env python3
"""Source labeled IGP24 candidates from LMFDB number-field downloads."""

from __future__ import annotations

import argparse
import ast
import csv
import json
import re
import sys
import time
import urllib.parse
import urllib.request
from pathlib import Path
from typing import Any


LMFDB_DOWNLOAD_URL = "https://www.lmfdb.org/NumberField/"
USER_AGENT = "igp24-source-lmfdb/0.1 (+https://competition.sair.foundation/competitions/igp24)"


class SourceError(RuntimeError):
    pass


def fetch_lmfdb_degree24(path: Path) -> str:
    query = {
        "download": "1",
        "query": "{'degree': 24}",
        "degree": "24",
        "count": "50",
    }
    url = f"{LMFDB_DOWNLOAD_URL}?{urllib.parse.urlencode(query)}"
    request = urllib.request.Request(url, headers={"User-Agent": USER_AGENT, "Accept": "text/plain,*/*"})
    with urllib.request.urlopen(request, timeout=120) as response:
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
            raise SourceError(f"could not parse LMFDB line {line_number}: {line[:160]}") from exc

        match = re.fullmatch(r"24\.([0-9]+)\..+?\.[0-9]+", field_label)
        if not match:
            continue
        r = int(match.group(1))
        if not isinstance(coeffs, list) or len(coeffs) != 25:
            continue
        if not re.fullmatch(r"24T[1-9][0-9]{0,4}", str(galois_label)):
            continue
        rows.append({
            "label": galois_label,
            "r": r,
            "polynomial": ",".join(str(int(c)) for c in coeffs),
            "source": "LMFDB NumberField download",
            "provenance": source_url,
            "field_label": field_label,
            "nfdisc_abs": abs(discriminant),
        })
    return rows


def write_candidates(rows: list[dict[str, Any]], output: Path, report: Path, source_url: str) -> None:
    output.parent.mkdir(parents=True, exist_ok=True)
    fieldnames = ["label", "r", "polynomial", "source", "provenance", "field_label", "nfdisc_abs"]
    with output.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(rows)

    labels = sorted({row["label"] for row in rows}, key=lambda label: int(label[3:]))
    report.parent.mkdir(parents=True, exist_ok=True)
    report.write_text(
        json.dumps(
            {
                "generated_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
                "source_url": source_url,
                "row_count": len(rows),
                "distinct_labels": len(labels),
                "labels": labels,
            },
            indent=2,
        ),
        encoding="utf-8",
    )


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--download", type=Path, default=Path("data/igp24/lmfdb_degree24.txt"))
    parser.add_argument("--input", type=Path, help="parse an existing LMFDB download instead of fetching")
    parser.add_argument("--output", type=Path, default=Path("data/igp24/lmfdb_degree24_candidates.csv"))
    parser.add_argument("--report", type=Path, default=Path("data/igp24/lmfdb_degree24_candidates_report.json"))
    args = parser.parse_args(argv)

    if args.input:
        text = args.input.read_text(encoding="utf-8")
        source_url = f"local:{args.input}"
    else:
        source_url = fetch_lmfdb_degree24(args.download)
        text = args.download.read_text(encoding="utf-8")
    rows = parse_lmfdb_text(text, source_url)
    write_candidates(rows, args.output, args.report, source_url)
    print(f"rows={len(rows)}")
    print(f"output={args.output}")
    print(f"report={args.report}")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main(sys.argv[1:]))
    except SourceError as exc:
        print(f"error: {exc}", file=sys.stderr)
        raise SystemExit(2)
