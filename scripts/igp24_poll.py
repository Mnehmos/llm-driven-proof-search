#!/usr/bin/env python3
"""Poll SAIR IGP24 submissions and summarize verifier/scoring status."""

from __future__ import annotations

import argparse
import json
import os
import sys
import urllib.parse
import urllib.request
from collections import Counter
from pathlib import Path
from typing import Any


API_BASE = "https://api.sair.foundation"
COMPETITION_ID = "igp24"
USER_AGENT = "igp24-poll/0.1 (+https://competition.sair.foundation/competitions/igp24)"


class PollError(RuntimeError):
    pass


def http_json(path: str, api_key: str, params: dict[str, str] | None = None) -> Any:
    url = f"{API_BASE}/api/public/v1/competitions/{COMPETITION_ID}{path}"
    if params:
        url = f"{url}?{urllib.parse.urlencode(params)}"
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


def summarize(items: list[dict[str, Any]]) -> dict[str, Any]:
    verified_rows: list[dict[str, Any]] = []
    failed_rows: list[dict[str, Any]] = []
    for item in items:
        for row in item.get("verifiedPolynomials") or []:
            verified_rows.append(row)
        for row in item.get("failedPolynomials") or []:
            failed_rows.append(row)

    pairs = [(row.get("label"), row.get("r")) for row in verified_rows if row.get("label") and row.get("r") is not None]
    scoreable_pairs = {
        (row.get("label"), row.get("r"))
        for row in verified_rows
        if row.get("scoreable") and row.get("label") and row.get("r") is not None
    }
    return {
        "submission_count": len(items),
        "verified_rows": len(verified_rows),
        "failed_rows": len(failed_rows),
        "distinct_verified_pairs": len(set(pairs)),
        "distinct_scoreable_pairs": len(scoreable_pairs),
        "labels": dict(Counter(label for label, _r in pairs)),
        "real_roots": dict(Counter(str(r) for _label, r in pairs)),
        "status": dict(Counter(str(row.get("status")) for row in verified_rows)),
        "scoring_status": dict(Counter(str(row.get("scoringStatus")) for row in verified_rows)),
        "scoring_reasons": dict(Counter(str(row.get("scoringReason")) for row in verified_rows)),
    }


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--api-key-env", default="SAIR_API_KEY")
    parser.add_argument("--limit", type=int, default=20)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args(argv)

    api_key = os.environ.get(args.api_key_env, "").strip()
    if not api_key:
        raise PollError(f"set {args.api_key_env} before running")

    payload = http_json("/submissions/me", api_key, {"limit": str(args.limit)})
    data = payload.get("data", payload)
    items = data.get("items") or []
    summary = summarize(items)
    print(json.dumps(summary, indent=2, sort_keys=True))
    print("recent_submissions=" + ",".join(str(item.get("submissionId")) for item in items[:5]))
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps({"summary": summary, "items": items}, indent=2), encoding="utf-8")
        print(f"output={args.output}")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main(sys.argv[1:]))
    except PollError as exc:
        print(f"error: {exc}", file=sys.stderr)
        raise SystemExit(2)
