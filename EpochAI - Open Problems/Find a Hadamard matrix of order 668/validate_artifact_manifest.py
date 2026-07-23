"""Validate ARTIFACT_MANIFEST.json (CI gate, PR #265 review blocker 7).

- Every 'committed' entry must exist and match its SHA-256 and byte size.
- Every 'excluded' entry must NOT be tracked by git; when present on disk with
  a recorded hash, it must match byte-identically.
Exit 1 on any violation.
"""
import hashlib, json, subprocess, sys
from pathlib import Path

HERE = Path(__file__).resolve().parent


# Text artifacts are hashed over LF-normalized bytes so pins are identical on
# CRLF (Windows) and LF (CI) checkouts; binary artifacts use raw bytes.
TEXT_SUFFIXES = {".json", ".jsonl", ".md", ".csv"}


def _norm(p: Path) -> bytes:
    data = p.read_bytes()
    if p.suffix in TEXT_SUFFIXES:
        data = data.replace(b"\r\n", b"\n")
    return data


def sha256(p: Path) -> str:
    return hashlib.sha256(_norm(p)).hexdigest()


def main():
    manifest = json.loads((HERE / "ARTIFACT_MANIFEST.json").read_text(encoding="utf-8"))
    bad = 0
    for name, rec in manifest["committed"].items():
        p = HERE / name
        if not p.exists():
            print("FAIL missing committed artifact:", name); bad += 1; continue
        data = _norm(p)
        if hashlib.sha256(data).hexdigest() != rec["sha256"] or len(data) != rec["bytes"]:
            print("FAIL hash/size mismatch:", name); bad += 1
    tracked = subprocess.run(["git", "ls-files", "--", "."], capture_output=True,
                             text=True, cwd=HERE).stdout.splitlines()
    tracked_names = {Path(t).name for t in tracked}
    for name, rec in manifest["excluded"].items():
        if name in tracked_names:
            print("FAIL excluded artifact is tracked by git:", name); bad += 1
        p = HERE / name
        if p.exists() and rec.get("sha256") not in (None, "ABSENT_AT_MANIFEST_BUILD"):
            if sha256(p) != rec["sha256"]:
                print("FAIL excluded artifact present but hash-mismatched:", name); bad += 1
    if bad:
        print(f"{bad} manifest violation(s)"); sys.exit(1)
    print("ARTIFACT_MANIFEST.json: all pins verified "
          f"({len(manifest['committed'])} committed, {len(manifest['excluded'])} excluded)")


if __name__ == "__main__":
    main()
