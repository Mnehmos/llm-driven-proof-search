#!/usr/bin/env python3
"""MCIP v1 conformance evidence (#230/#232/#233/#234/#235/#238).

Validates the MCIP records emitted by `proofsearch_core::mcip` (written to
target/mcip_conformance/ by the `emit_mcip_records_for_schema_validation` test)
against the REAL MathCorpus MCIP v1 JSON schemas, using jsonschema.

Run:
    cargo test -p proofsearch_core --lib -- mcip::tests::emit
    python crates/proofsearch-core/tests/mcip_conformance.py

Exits non-zero if any record fails to conform.
"""
import glob
import json
import os
import sys

from jsonschema import Draft202012Validator
from referencing import Registry, Resource

# Shared-workspace path to the canonical MCIP v1 schemas.
SCHEMA_DIR = os.environ.get(
    "MCIP_SCHEMA_DIR",
    r"F:/Github/mnehmos.llm-math-corpus.training/schema/mcip/v1",
)
RECORDS_DIR = os.environ.get(
    "MCIP_RECORDS_DIR",
    os.path.join(os.path.dirname(__file__), "..", "..", "..", "target", "mcip_conformance"),
)

RECORD_TYPE_TO_SCHEMA = {
    "packet_identity": "packet_identity.schema.json",
    "proof_profile": "proof_profile.schema.json",
    "restriction_profile": "restriction_profile.schema.json",
    "dependency_manifest": "dependency_manifest.schema.json",
    "negative_example": "negative_example.schema.json",
    "rl_transition": "rl_transition.schema.json",
}


def build_registry(schema_dir):
    """Load every schema, keyed by $id and by relative filename, so the
    per-record schemas' `_defs.schema.json#/...` refs resolve."""
    resources = []
    for path in glob.glob(os.path.join(schema_dir, "*.schema.json")):
        with open(path, encoding="utf-8") as fh:
            doc = json.load(fh)
        res = Resource.from_contents(doc)
        resources.append((os.path.basename(path), res))
        if "$id" in doc:
            resources.append((doc["$id"], res))
    return Registry().with_resources(resources)


def main():
    if not os.path.isdir(SCHEMA_DIR):
        print(f"SKIP: MCIP schema dir not found: {SCHEMA_DIR}")
        return 0
    records = sorted(glob.glob(os.path.join(RECORDS_DIR, "*.json")))
    if not records:
        print(f"FAIL: no emitted records in {RECORDS_DIR} (run the emit test first)")
        return 1

    registry = build_registry(SCHEMA_DIR)
    ok = True

    def validate(obj, schema_name, label):
        nonlocal ok
        with open(os.path.join(SCHEMA_DIR, schema_name), encoding="utf-8") as fh:
            schema = json.load(fh)
        errors = sorted(Draft202012Validator(schema, registry=registry).iter_errors(obj), key=lambda e: list(e.path))
        if errors:
            ok = False
            print(f"FAIL {label}: {len(errors)} error(s)")
            for e in errors[:5]:
                loc = "/".join(str(p) for p in e.path) or "(root)"
                print(f"    - at {loc}: {e.message}")
        else:
            extra = f" (record_hash={obj['record_hash'][:12]}...)" if "record_hash" in obj else ""
            print(f"PASS {label} conforms to MCIP {schema_name}{extra}")

    for rec_path in records:
        with open(rec_path, encoding="utf-8") as fh:
            rec = json.load(fh)
        # A bundle: validate the envelope, then dispatch each record.
        if "records" in rec and "mcip_version" in rec:
            validate(rec, "bundle.schema.json", f"bundle {rec.get('bundle_id','')}")
            for sub in rec["records"]:
                srt = sub.get("record_type")
                sname = RECORD_TYPE_TO_SCHEMA.get(srt)
                if sname:
                    validate(sub, sname, f"  bundle.record {srt}")
                else:
                    print(f"  SKIP bundle.record: unmapped {srt!r}")
            continue
        rt = rec.get("record_type")
        schema_name = RECORD_TYPE_TO_SCHEMA.get(rt)
        if not schema_name:
            print(f"SKIP {os.path.basename(rec_path)}: unmapped record_type {rt!r}")
            continue
        validate(rec, schema_name, rt)

    print("\nALL MCIP RECORDS + BUNDLE CONFORM" if ok else "\nSOME RECORDS FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
