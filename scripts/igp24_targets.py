#!/usr/bin/env python3
"""Write a live CSV of open IGP24 target signatures."""

from __future__ import annotations

import argparse
import csv
import json
import os
import sys
import urllib.parse
import urllib.request
from collections import Counter
from pathlib import Path
from typing import Any


API_BASE = "https://api.sair.foundation"
DISCOVERY_URL = "https://server-9527.sair.foundation/api/igp24/discoveries"
COMPETITION_ID = "igp24"
USER_AGENT = "igp24-targets/0.1 (+https://competition.sair.foundation/competitions/igp24)"


class TargetError(RuntimeError):
    pass


def http_json(path: str, api_key: str, params: dict[str, str]) -> Any:
    url = f"{API_BASE}/api/public/v1/competitions/{COMPETITION_ID}{path}?{urllib.parse.urlencode(params)}"
    request = urllib.request.Request(
        url,
        headers={
            "Accept": "application/json",
            "Authorization": f"Bearer {api_key}",
            "User-Agent": USER_AGENT,
        },
    )
    with urllib.request.urlopen(request, timeout=120) as response:
        return json.loads(response.read().decode("utf-8"))


def http_public_json(url: str) -> Any:
    request = urllib.request.Request(
        url,
        headers={
            "Accept": "application/json",
            "User-Agent": USER_AGENT,
        },
    )
    with urllib.request.urlopen(request, timeout=120) as response:
        return json.loads(response.read().decode("utf-8"))


def fetch_baseline_pairs() -> set[tuple[int, int]]:
    payload = http_public_json(DISCOVERY_URL)
    data = payload.get("data", payload)
    pairs: set[tuple[int, int]] = set()
    for group in data.get("grid", []):
        t = int(group.get("t"))
        for r in group.get("baselineR") or []:
            pairs.add((t, int(r)))
    return pairs


def fetch_progress(api_key: str) -> tuple[list[dict[str, Any]], str | None]:
    labels: list[dict[str, Any]] = []
    cursor: str | None = None
    generated_at: str | None = None
    while True:
        params = {"limit": "5000", "includeEmpty": "true"}
        if cursor:
            params["cursor"] = cursor
        payload = http_json("/labels/progress", api_key, params)
        data = payload.get("data", payload)
        generated_at = generated_at or data.get("generatedAt")
        labels.extend(data.get("labels") or [])
        cursor = data.get("nextCursor")
        if not cursor:
            return labels, generated_at


def build_rows(labels: list[dict[str, Any]], baseline_pairs: set[tuple[int, int]]) -> list[dict[str, Any]]:
    valid_by_r = Counter()
    for label in labels:
        for r in label.get("allowedR") or []:
            valid_by_r[int(r)] += 1

    rows: list[dict[str, Any]] = []
    for label in labels:
        signatures = label.get("signatures") or []
        discovered_count = sum(1 for signature in signatures if signature.get("discovered"))
        remaining = [signature for signature in signatures if not signature.get("discovered")]
        for signature in remaining:
            r = int(signature["r"])
            t = int(label["t"])
            rows.append({
                "label": label["label"],
                "t": t,
                "r": r,
                "baseline": (t, r) in baseline_pairs,
                "label_team_count": int(label.get("teamCount") or 0),
                "signature_team_count": int(signature.get("teamCount") or 0),
                "allowed_signature_count": len(signatures),
                "discovered_signature_count": discovered_count,
                "remaining_signature_count": len(remaining),
                "global_valid_count_for_r": valid_by_r[r],
                "label_minimum_disc_abs": label.get("minimumDiscAbs"),
                "signature_minimum_disc_abs": signature.get("minimumDiscAbs"),
            })
    return rows


def filter_rows(rows: list[dict[str, Any]], args: argparse.Namespace) -> list[dict[str, Any]]:
    max_label_team_count = 0 if args.uncovered_labels_only else args.max_label_team_count
    filtered = rows
    if max_label_team_count is not None:
        filtered = [row for row in filtered if row["label_team_count"] <= max_label_team_count]
    if args.max_signature_team_count is not None:
        filtered = [row for row in filtered if row["signature_team_count"] <= args.max_signature_team_count]
    if args.min_r is not None:
        filtered = [row for row in filtered if row["r"] >= args.min_r]
    if args.max_r is not None:
        filtered = [row for row in filtered if row["r"] <= args.max_r]
    if args.exclude_baseline:
        filtered = [row for row in filtered if not row["baseline"]]

    if args.priority == "high-r":
        filtered.sort(
            key=lambda row: (
                row["label_team_count"] != 0,
                -row["r"],
                row["signature_team_count"],
                row["global_valid_count_for_r"],
                row["remaining_signature_count"],
                row["allowed_signature_count"],
                row["t"],
            )
        )
    else:
        filtered.sort(
            key=lambda row: (
                row["label_team_count"] != 0,
                row["signature_team_count"],
                row["global_valid_count_for_r"],
                -row["r"],
                row["remaining_signature_count"],
                row["allowed_signature_count"],
                row["t"],
            )
        )
    return filtered


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--api-key-env", default="SAIR_API_KEY")
    parser.add_argument("--output", type=Path, default=Path("igp24/open_targets.csv"))
    parser.add_argument("--summary", type=Path, default=Path("igp24/open_targets_summary.json"))
    parser.add_argument("--limit", type=int, default=0, help="write only the first N rows; 0 means all")
    parser.add_argument("--uncovered-labels-only", action="store_true", help="keep only labels with zero public team coverage")
    parser.add_argument("--max-label-team-count", type=int, help="keep labels with at most this many public teams")
    parser.add_argument("--max-signature-team-count", type=int, help="keep signatures with at most this many public teams")
    parser.add_argument("--min-r", type=int, help="keep signatures with at least this many real roots")
    parser.add_argument("--max-r", type=int, help="keep signatures with at most this many real roots")
    parser.add_argument("--exclude-baseline", action="store_true", help="skip pairs already present in the LMFDB baseline")
    parser.add_argument("--priority", choices=("high-r", "rare-r"), default="high-r")
    args = parser.parse_args(argv)

    api_key = os.environ.get(args.api_key_env, "").strip()
    if not api_key:
        raise TargetError(f"set {args.api_key_env} before running")

    labels, generated_at = fetch_progress(api_key)
    baseline_pairs = fetch_baseline_pairs()
    all_rows = build_rows(labels, baseline_pairs)
    rows = filter_rows(all_rows, args)
    output_rows = rows[: args.limit] if args.limit else rows

    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0].keys()) if rows else ["label", "t", "r"])
        writer.writeheader()
        writer.writerows(output_rows)

    summary = {
        "progress_generated_at": generated_at,
        "labels": len(labels),
        "open_targets": len(all_rows),
        "baseline_open_targets": sum(1 for row in all_rows if row["baseline"]),
        "filtered_open_targets": len(rows),
        "written_targets": len(output_rows),
        "labels_with_no_team_coverage": sum(1 for label in labels if int(label.get("teamCount") or 0) == 0),
        "filters": {
            "uncovered_labels_only": args.uncovered_labels_only,
            "max_label_team_count": 0 if args.uncovered_labels_only else args.max_label_team_count,
            "max_signature_team_count": args.max_signature_team_count,
            "min_r": args.min_r,
            "max_r": args.max_r,
            "exclude_baseline": args.exclude_baseline,
            "priority": args.priority,
        },
        "first_targets": output_rows[:25],
    }
    args.summary.parent.mkdir(parents=True, exist_ok=True)
    args.summary.write_text(json.dumps(summary, indent=2), encoding="utf-8")
    print(json.dumps({k: v for k, v in summary.items() if k != "first_targets"}, indent=2))
    print(f"output={args.output}")
    print(f"summary={args.summary}")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main(sys.argv[1:]))
    except TargetError as exc:
        print(f"error: {exc}", file=sys.stderr)
        raise SystemExit(2)
