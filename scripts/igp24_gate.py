#!/usr/bin/env python3
"""Gate IGP24 polynomial candidates before using a SAIR submission slot.

The script deliberately requires an expected (24Tt, r) for every candidate.
It fetches live progress, skips occupied or baseline pairs by default, dedupes
within the candidate set, and writes a coefficient-only batch suitable for the
web form or the public API.
"""

from __future__ import annotations

import argparse
import csv
import json
import math
import os
import re
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
from dataclasses import dataclass, field
from functools import reduce
from math import gcd
from pathlib import Path
from typing import Any


API_BASE = "https://api.sair.foundation"
DISCOVERY_URL = "https://server-9527.sair.foundation/api/igp24/discoveries"
COMPETITION_ID = "igp24"
USER_AGENT = "igp24-gate/0.1 (+https://competition.sair.foundation/competitions/igp24)"


class GateError(RuntimeError):
    pass


def http_json(url: str, api_key: str | None = None, method: str = "GET", body: Any = None) -> Any:
    data = None
    headers = {
        "Accept": "application/json",
        "User-Agent": USER_AGENT,
    }
    if api_key:
        headers["Authorization"] = f"Bearer {api_key}"
    if body is not None:
        data = json.dumps(body, separators=(",", ":")).encode("utf-8")
        headers["Content-Type"] = "application/json"

    request = urllib.request.Request(url, data=data, headers=headers, method=method)
    try:
        with urllib.request.urlopen(request, timeout=60) as response:
            return json.loads(response.read().decode("utf-8"))
    except urllib.error.HTTPError as exc:
        detail = exc.read().decode("utf-8", errors="replace")
        raise GateError(f"HTTP {exc.code} for {url}: {detail}") from exc
    except urllib.error.URLError as exc:
        raise GateError(f"request failed for {url}: {exc}") from exc


def normalize_label(value: str | int) -> tuple[str, int]:
    text = str(value).strip()
    match = re.fullmatch(r"(?:24T)?([1-9][0-9]{0,4})", text)
    if not match:
        raise ValueError(f"invalid label/t value: {value!r}")
    t = int(match.group(1))
    if not 1 <= t <= 25000:
        raise ValueError(f"24T index outside 1..25000: {t}")
    return f"24T{t}", t


def parse_int(value: Any, name: str) -> int:
    try:
        return int(str(value).strip())
    except Exception as exc:
        raise ValueError(f"invalid {name}: {value!r}") from exc


def parse_polynomial(line: str) -> tuple[list[int] | None, list[str]]:
    parts = [p.strip() for p in line.strip().split(",")]
    errors: list[str] = []
    if len(parts) != 25:
        return None, [f"expected 25 coefficients, got {len(parts)}"]
    coeffs: list[int] = []
    for index, part in enumerate(parts):
        if not re.fullmatch(r"[+-]?[0-9]+", part):
            errors.append(f"a_{index} is not an integer")
            continue
        coeffs.append(int(part))
    if errors:
        return None, errors
    if coeffs[0] == 0:
        errors.append("constant coefficient a_0 is zero")
    if coeffs[-1] != 1:
        errors.append("leading coefficient a_24 is not 1")
    coefficient_gcd = reduce(gcd, (abs(c) for c in coeffs), 0)
    if coefficient_gcd != 1:
        errors.append(f"coefficient gcd is {coefficient_gcd}, not 1")
    return coeffs, errors


def canonical_polynomial(coeffs: list[int]) -> str:
    return ",".join(str(c) for c in coeffs)


def int_or_none(value: Any) -> int | None:
    if value is None:
        return None
    text = str(value).strip()
    if text == "":
        return None
    try:
        return int(text)
    except ValueError:
        return None


@dataclass
class Candidate:
    row_number: int
    label: str
    t: int
    r: int
    polynomial: str
    source: str = ""
    note: str = ""
    rank_disc_abs: int | None = None
    fields: dict[str, Any] = field(default_factory=dict)

    @property
    def pair(self) -> tuple[int, int]:
        return (self.t, self.r)


def row_to_candidate(row: dict[str, Any], row_number: int) -> Candidate:
    label_value = (
        row.get("label")
        or row.get("expected_label")
        or row.get("t")
        or row.get("expected_t")
        or row.get("24Tt")
    )
    if label_value is None:
        raise ValueError("missing label/expected_label/t/expected_t")
    label, t = normalize_label(label_value)

    r_value = row.get("r") if "r" in row else row.get("expected_r")
    if r_value is None:
        raise ValueError("missing r/expected_r")
    r = parse_int(r_value, "r")
    if r < 0 or r > 24 or r % 2 != 0:
        raise ValueError(f"invalid r for degree 24: {r}")

    polynomial = str(row.get("polynomial") or row.get("coefficients") or row.get("coeffs") or "").strip()
    if not polynomial:
        raise ValueError("missing polynomial/coefficients")

    rank_disc_abs = None
    for key in ("nfdisc_abs", "field_disc_abs", "scoring_disc_abs", "poly_disc_abs", "disc_abs"):
        rank_disc_abs = int_or_none(row.get(key))
        if rank_disc_abs is not None:
            break

    return Candidate(
        row_number=row_number,
        label=label,
        t=t,
        r=r,
        polynomial=polynomial,
        source=str(row.get("source") or row.get("provenance") or "").strip(),
        note=str(row.get("note") or row.get("notes") or "").strip(),
        rank_disc_abs=rank_disc_abs,
        fields=dict(row),
    )


def read_candidates(path: Path) -> list[Candidate]:
    text = path.read_text(encoding="utf-8-sig")
    candidates: list[Candidate] = []
    errors: list[str] = []

    if path.suffix.lower() in {".jsonl", ".ndjson"}:
        for row_number, line in enumerate(text.splitlines(), start=1):
            if not line.strip() or line.lstrip().startswith("#"):
                continue
            try:
                candidates.append(row_to_candidate(json.loads(line), row_number))
            except Exception as exc:
                errors.append(f"{path}:{row_number}: {exc}")
    elif path.suffix.lower() == ".json":
        raw = json.loads(text)
        if isinstance(raw, dict):
            rows = raw.get("candidates", raw.get("items", []))
        else:
            rows = raw
        if not isinstance(rows, list):
            raise GateError("JSON input must be a list or an object with candidates/items")
        for row_number, row in enumerate(rows, start=1):
            try:
                candidates.append(row_to_candidate(row, row_number))
            except Exception as exc:
                errors.append(f"{path}:{row_number}: {exc}")
    else:
        reader = csv.DictReader(line for line in text.splitlines() if not line.lstrip().startswith("#"))
        for row_number, row in enumerate(reader, start=2):
            try:
                candidates.append(row_to_candidate(row, row_number))
            except Exception as exc:
                errors.append(f"{path}:{row_number}: {exc}")

    if errors:
        raise GateError("candidate input errors:\n" + "\n".join(errors))
    return candidates


@dataclass
class PairState:
    label: str
    t: int
    r: int
    valid: bool = False
    baseline: bool = False
    player_discovered: bool = False
    team_count: int = 0
    label_team_count: int = 0
    minimum_disc_abs: str | None = None
    solvable: bool | None = None


@dataclass
class Coverage:
    pair_states: dict[tuple[int, int], PairState]
    valid_pairs_by_r: dict[int, int]
    generated_at: str | None = None

    def state_for(self, candidate: Candidate) -> PairState:
        return self.pair_states.get(
            candidate.pair,
            PairState(label=candidate.label, t=candidate.t, r=candidate.r),
        )


def fetch_discovery_snapshot() -> tuple[dict[tuple[int, int], PairState], dict[int, int]]:
    payload = http_json(DISCOVERY_URL)
    data = payload.get("data", payload)
    pair_states: dict[tuple[int, int], PairState] = {}
    valid_pairs_by_r = {
        int(item["r"]): int(item["count"])
        for item in data.get("validPairsByRealRoots", [])
        if "r" in item and "count" in item
    }
    for group in data.get("grid", []):
        label, t = normalize_label(group.get("label") or group.get("t"))
        baseline_r = {int(r) for r in group.get("baselineR", [])}
        player_r = {int(r) for r in group.get("playerR", [])}
        for r_raw in group.get("validR", []):
            r = int(r_raw)
            pair_states[(t, r)] = PairState(
                label=label,
                t=t,
                r=r,
                valid=True,
                baseline=r in baseline_r,
                player_discovered=r in player_r,
                solvable=bool(group.get("solvable")) if group.get("solvable") is not None else None,
            )
    return pair_states, valid_pairs_by_r


def fetch_progress(api_key: str) -> tuple[dict[tuple[int, int], PairState], str | None]:
    pair_states: dict[tuple[int, int], PairState] = {}
    cursor: str | None = None
    generated_at = None
    while True:
        params = {"limit": "5000", "includeEmpty": "true"}
        if cursor:
            params["cursor"] = cursor
        url = f"{API_BASE}/api/public/v1/competitions/{COMPETITION_ID}/labels/progress?{urllib.parse.urlencode(params)}"
        payload = http_json(url, api_key=api_key)
        data = payload.get("data", payload)
        generated_at = generated_at or data.get("generatedAt")
        for label_row in data.get("labels", []):
            label, t = normalize_label(label_row["label"])
            label_team_count = int(label_row.get("teamCount") or 0)
            for signature in label_row.get("signatures", []):
                r = int(signature["r"])
                pair_states[(t, r)] = PairState(
                    label=label,
                    t=t,
                    r=r,
                    valid=True,
                    player_discovered=bool(signature.get("discovered")),
                    team_count=int(signature.get("teamCount") or 0),
                    label_team_count=label_team_count,
                    minimum_disc_abs=signature.get("minimumDiscAbs"),
                )
        cursor = data.get("nextCursor")
        if not cursor:
            break
    return pair_states, generated_at


def fetch_own_pairs(api_key: str, limit_pages: int = 20) -> set[tuple[int, int]]:
    pairs: set[tuple[int, int]] = set()
    cursor: str | None = None
    for _ in range(limit_pages):
        params = {"limit": "100"}
        if cursor:
            params["cursor"] = cursor
        url = f"{API_BASE}/api/public/v1/competitions/{COMPETITION_ID}/submissions/me?{urllib.parse.urlencode(params)}"
        payload = http_json(url, api_key=api_key)
        data = payload.get("data", payload)
        for item in data.get("items", []):
            for row in item.get("verifiedPolynomials", []):
                t = row.get("t")
                r = row.get("r")
                if isinstance(t, int) and isinstance(r, int):
                    pairs.add((t, r))
        cursor = data.get("nextCursor")
        if not cursor:
            break
    return pairs


def build_coverage(api_key: str) -> Coverage:
    discovery_states, valid_pairs_by_r = fetch_discovery_snapshot()
    progress_states, generated_at = fetch_progress(api_key)

    for pair, progress in progress_states.items():
        state = discovery_states.get(pair)
        if state is None:
            discovery_states[pair] = progress
        else:
            state.player_discovered = state.player_discovered or progress.player_discovered
            state.team_count = progress.team_count
            state.label_team_count = progress.label_team_count
            state.minimum_disc_abs = progress.minimum_disc_abs

    return Coverage(
        pair_states=discovery_states,
        valid_pairs_by_r=valid_pairs_by_r,
        generated_at=generated_at,
    )


def candidate_sort_key(candidate: Candidate, coverage: Coverage) -> tuple[Any, ...]:
    state = coverage.state_for(candidate)
    r_rarity = coverage.valid_pairs_by_r.get(candidate.r, 10**9)
    # Non-solvable and rarer real-root signatures first, then smaller known
    # local discriminant estimate if provided.
    solvability_rank = 0 if state.solvable is False else 1
    disc_rank = candidate.rank_disc_abs if candidate.rank_disc_abs is not None else 10**999
    return (
        state.label_team_count,
        r_rarity,
        solvability_rank,
        state.team_count,
        disc_rank,
        candidate.t,
        candidate.r,
        candidate.row_number,
    )


def filter_candidates(
    candidates: list[Candidate],
    coverage: Coverage,
    own_pairs: set[tuple[int, int]],
    include_baseline: bool,
    include_player_discovered: bool,
    include_own_submitted: bool,
    min_r: int | None,
    max_label_team_count: int | None,
    max_signature_team_count: int | None,
) -> tuple[list[Candidate], list[dict[str, Any]]]:
    selected_by_pair: dict[tuple[int, int], Candidate] = {}
    skipped: list[dict[str, Any]] = []

    for candidate in candidates:
        reasons: list[str] = []
        coeffs, parse_errors = parse_polynomial(candidate.polynomial)
        if parse_errors:
            reasons.extend(parse_errors)
        elif coeffs is not None:
            candidate.polynomial = canonical_polynomial(coeffs)

        state = coverage.state_for(candidate)
        if not state.valid:
            reasons.append("expected pair is not a valid IGP24 signature")
        if state.player_discovered and not include_player_discovered:
            reasons.append("pair already has a participant discovery")
        if state.baseline and not include_baseline:
            reasons.append("pair is in the LMFDB baseline")
        if candidate.pair in own_pairs and not include_own_submitted:
            reasons.append("pair already appears in this team's submissions")
        if min_r is not None and candidate.r < min_r:
            reasons.append(f"r={candidate.r} is below --min-r={min_r}")
        if max_label_team_count is not None and state.label_team_count > max_label_team_count:
            reasons.append(
                f"label already has {state.label_team_count} public teams; cap is {max_label_team_count}"
            )
        if max_signature_team_count is not None and state.team_count > max_signature_team_count:
            reasons.append(
                f"signature already has {state.team_count} public teams; cap is {max_signature_team_count}"
            )

        if reasons:
            skipped.append({
                "row": candidate.row_number,
                "label": candidate.label,
                "r": candidate.r,
                "reasons": reasons,
            })
            continue

        incumbent = selected_by_pair.get(candidate.pair)
        if incumbent is None:
            selected_by_pair[candidate.pair] = candidate
            continue

        current_rank = candidate.rank_disc_abs if candidate.rank_disc_abs is not None else math.inf
        incumbent_rank = incumbent.rank_disc_abs if incumbent.rank_disc_abs is not None else math.inf
        if (current_rank, candidate.row_number) < (incumbent_rank, incumbent.row_number):
            skipped.append({
                "row": incumbent.row_number,
                "label": incumbent.label,
                "r": incumbent.r,
                "reasons": ["duplicate expected pair; replaced by smaller discriminant estimate"],
            })
            selected_by_pair[candidate.pair] = candidate
        else:
            skipped.append({
                "row": candidate.row_number,
                "label": candidate.label,
                "r": candidate.r,
                "reasons": ["duplicate expected pair; kept earlier/smaller discriminant estimate"],
            })

    selected = list(selected_by_pair.values())
    selected.sort(key=lambda candidate: candidate_sort_key(candidate, coverage))
    return selected, skipped


def submit_batch(api_key: str, selected: list[Candidate], description: str) -> Any:
    polynomials = [candidate.polynomial for candidate in selected]
    body = {
        "payload": {"polynomials": polynomials},
        "meta": {"description": description[:500]},
    }
    url = f"{API_BASE}/api/public/v1/competitions/{COMPETITION_ID}/submissions"
    return http_json(url, api_key=api_key, method="POST", body=body)


def write_outputs(output: Path, report: Path, selected: list[Candidate], skipped: list[dict[str, Any]], coverage: Coverage) -> None:
    output.parent.mkdir(parents=True, exist_ok=True)
    report.parent.mkdir(parents=True, exist_ok=True)
    output.write_text("\n".join(candidate.polynomial for candidate in selected) + ("\n" if selected else ""), encoding="utf-8")

    report_payload = {
        "generated_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "progress_generated_at": coverage.generated_at,
        "selected_count": len(selected),
        "skipped_count": len(skipped),
        "selected": [
            {
                "row": candidate.row_number,
                "label": candidate.label,
                "t": candidate.t,
                "r": candidate.r,
                "source": candidate.source,
                "rank_disc_abs": str(candidate.rank_disc_abs) if candidate.rank_disc_abs is not None else None,
                "label_team_count": coverage.state_for(candidate).label_team_count,
                "signature_team_count": coverage.state_for(candidate).team_count,
            }
            for candidate in selected
        ],
        "skipped": skipped,
    }
    report.write_text(json.dumps(report_payload, indent=2), encoding="utf-8")


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("candidates", type=Path, help="CSV, JSON, or JSONL candidate file")
    parser.add_argument("--output", type=Path, default=Path("igp24/filtered_submission.txt"))
    parser.add_argument("--report", type=Path, default=Path("igp24/gate_report.json"))
    parser.add_argument("--api-key-env", default="SAIR_API_KEY")
    parser.add_argument("--include-baseline", action="store_true", help="allow baseline pairs through")
    parser.add_argument("--include-player-discovered", action="store_true", help="allow pairs already discovered by any participant")
    parser.add_argument("--include-own-submitted", action="store_true", help="allow pairs already seen in this team's submissions")
    parser.add_argument("--uncovered-labels-only", action="store_true", help="skip labels that already have public team coverage")
    parser.add_argument("--max-label-team-count", type=int, help="skip labels with more than this many public teams")
    parser.add_argument("--max-signature-team-count", type=int, help="skip signatures with more than this many public teams")
    parser.add_argument("--min-r", type=int, help="skip candidates with fewer than this many real roots")
    parser.add_argument("--max-polynomials", type=int, default=1000)
    parser.add_argument("--submit", action="store_true", help="submit the filtered batch through the SAIR API")
    parser.add_argument("--yes", action="store_true", help="do not ask for confirmation with --submit")
    parser.add_argument("--description", default="IGP24 gated batch: expected labels prefiltered against live progress.")
    args = parser.parse_args(argv)

    api_key = os.environ.get(args.api_key_env, "").strip()
    if not api_key:
        raise GateError(f"set {args.api_key_env} before running")

    candidates = read_candidates(args.candidates)
    coverage = build_coverage(api_key)
    own_pairs = fetch_own_pairs(api_key)
    max_label_team_count = 0 if args.uncovered_labels_only else args.max_label_team_count
    selected, skipped = filter_candidates(
        candidates,
        coverage,
        own_pairs=own_pairs,
        include_baseline=args.include_baseline,
        include_player_discovered=args.include_player_discovered,
        include_own_submitted=args.include_own_submitted,
        min_r=args.min_r,
        max_label_team_count=max_label_team_count,
        max_signature_team_count=args.max_signature_team_count,
    )
    if len(selected) > args.max_polynomials:
        selected = selected[: args.max_polynomials]

    write_outputs(args.output, args.report, selected, skipped, coverage)

    print(f"loaded_candidates={len(candidates)}")
    print(f"selected={len(selected)}")
    print(f"skipped={len(skipped)}")
    print(f"output={args.output}")
    print(f"report={args.report}")
    if selected:
        preview = ", ".join(f"{candidate.label},r={candidate.r}" for candidate in selected[:10])
        print(f"first_selected={preview}")

    if not args.submit:
        return 0
    if not selected:
        raise GateError("nothing selected; refusing to submit empty batch")
    if not args.yes:
        answer = input(f"Submit {len(selected)} polynomials to SAIR now? Type 'submit' to continue: ")
        if answer.strip() != "submit":
            print("submission cancelled")
            return 0
    response = submit_batch(api_key, selected, args.description)
    print(json.dumps(response, indent=2))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main(sys.argv[1:]))
    except GateError as exc:
        print(f"error: {exc}", file=sys.stderr)
        raise SystemExit(2)
