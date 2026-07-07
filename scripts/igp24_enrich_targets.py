#!/usr/bin/env python3
"""Enrich IGP24 target CSV rows with LMFDB transitive-group metadata."""

from __future__ import annotations

import argparse
import csv
import json
import sys
import time
import urllib.parse
import urllib.request
from pathlib import Path
from typing import Any


LMFDB_API = "https://www.lmfdb.org/api/gps_transitive/"
USER_AGENT = "igp24-enrich-targets/0.1 (+https://competition.sair.foundation/competitions/igp24)"


def fetch_group(label: str, retries: int = 4) -> dict[str, Any]:
    params = {"label": label, "_format": "json"}
    url = f"{LMFDB_API}?{urllib.parse.urlencode(params)}"
    last_error: Exception | None = None
    for attempt in range(retries):
        request = urllib.request.Request(
            url,
            headers={
                "Accept": "application/json",
                "User-Agent": USER_AGENT,
            },
        )
        try:
            with urllib.request.urlopen(request, timeout=60) as response:
                text = response.read().decode("utf-8")
            payload = json.loads(text)
            data = payload.get("data") or []
            return data[0] if data else {}
        except Exception as exc:
            last_error = exc
            time.sleep(1.5 * (attempt + 1))
    return {"_error": str(last_error) if last_error else "unknown error"}


def group_summary(row: dict[str, str], group: dict[str, Any]) -> dict[str, str]:
    enriched = dict(row)
    enriched.update(
        {
            "group_order": str(group.get("order", "")),
            "solvable": str(group.get("solv", "")),
            "abelian": str(group.get("ab", "")),
            "cyclic": str(group.get("cyc", "")),
            "primitive": str(group.get("prim", "")),
            "parity": str(group.get("parity", "")),
            "transitivity": str(group.get("transitivity", "")),
            "pretty": str(group.get("pretty", "") or ""),
            "gapidfull": str(group.get("gapidfull", "") or ""),
            "abstract_label": str(group.get("abstract_label", "") or ""),
            "subfield_count": str(len(group.get("subfields") or [])),
            "quotient_count": str(len(group.get("quotients") or [])),
            "lmfdb_error": str(group.get("_error", "") or ""),
        }
    )
    return enriched


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("targets", type=Path)
    parser.add_argument("--output", type=Path, default=Path("igp24/targets_enriched.csv"))
    parser.add_argument("--summary", type=Path, default=Path("igp24/targets_enriched_summary.json"))
    parser.add_argument("--limit", type=int, default=100)
    parser.add_argument("--sleep", type=float, default=0.15)
    args = parser.parse_args(argv)

    with args.targets.open(newline="", encoding="utf-8") as handle:
        rows = list(csv.DictReader(handle))
    rows = rows[: args.limit] if args.limit else rows

    cache: dict[str, dict[str, Any]] = {}
    enriched: list[dict[str, str]] = []
    for row in rows:
        label = row["label"]
        if label not in cache:
            cache[label] = fetch_group(label)
            time.sleep(args.sleep)
        enriched.append(group_summary(row, cache[label]))

    fieldnames: list[str] = []
    for row in enriched:
        for key in row:
            if key not in fieldnames:
                fieldnames.append(key)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(enriched)

    summary = {
        "input": str(args.targets),
        "output": str(args.output),
        "rows": len(enriched),
        "errors": sum(1 for row in enriched if row.get("lmfdb_error")),
        "solvable": sum(1 for row in enriched if row.get("solvable") == "1"),
        "primitive": sum(1 for row in enriched if row.get("primitive") == "1"),
        "abelian": sum(1 for row in enriched if row.get("abelian") == "1"),
    }
    args.summary.parent.mkdir(parents=True, exist_ok=True)
    args.summary.write_text(json.dumps(summary, indent=2), encoding="utf-8")
    print(json.dumps(summary, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
