"""Build/refresh ARTIFACT_MANIFEST.json (PR #265 review, blockers 5/8).

Pins every decisive committed verdict file and every excluded/removed bulky
artifact with SHA-256, byte size, generation command, seeds, and the software/
hardware environment. `validate_artifact_manifest.py` re-checks the pins.
"""
import hashlib, json, os, platform, sys
from pathlib import Path

HERE = Path(__file__).resolve().parent

COMMITTED = [
    "group333_kb6_layerB.jsonl",
    "group333_tail_layer_verdicts.jsonl",
    "lp333_271_split.jsonl",
    "lp333_271_split_retry.jsonl",
    "lp333_full_multiplier_sweep.jsonl",
    "lp333_decimation_sweep.jsonl",
    "ngp334_multiplier_sweep.jsonl",
    "lp333_affine_sweep.jsonl",
    "gpu_lift_group333.jsonl",
    "agent_btt_e800_verified.json",
]

EXCLUDED = {
    "z37_order3_survivors.npz": {
        "generator": "python gpu_z37_order3_v2.py  (deterministic; numpy default_rng(17) hash vector)",
        "why_excluded": "1.1 GB complete shadow catalog exceeds GitHub limits",
    },
    "agent_bsd_gf2_compatibility.json": {
        "generator": "python agent_bsd_gf2_compatibility.py",
        "why_excluded": "bulky derived compatibility table (review blocker 8); regenerable",
    },
    "agent_bsd_plus2_compatibility.json": {
        "generator": "python agent_bsd_gf2_compatibility.py (plus2 mode)",
        "why_excluded": "bulky derived compatibility table (review blocker 8); regenerable",
    },
    "agent_btt_fourier_compatibility.json": {
        "generator": "python agent_btt_fourier_compatibility.py",
        "why_excluded": "bulky derived compatibility table (review blocker 8); regenerable",
    },
}


def sha256(p: Path) -> str:
    h = hashlib.sha256()
    with p.open("rb") as f:
        for chunk in iter(lambda: f.read(1 << 22), b""):
            h.update(chunk)
    return h.hexdigest()


def main():
    manifest = {
        "note": ("Hash manifest for the Hadamard-668 campaign. 'committed' files must match "
                 "these pins exactly (CI-enforced). 'excluded' files are deliberately not "
                 "committed; anyone regenerating them can verify byte-identity here."),
        "environment": {
            "python": sys.version.split()[0],
            "platform": platform.platform(),
            "gpu": "NVIDIA GeForce RTX 4070",
            "torch": "2.6.0+cu124",
            "numpy": "2.3.5",
            "numeric_assumptions": ("all decisive joins/verdicts use exact int64/int8 integer "
                                    "arithmetic; no floating-point result is load-bearing"),
        },
        "seeds": {
            "gpu_layerB_kb6.py": "numpy default_rng(21) hash vector (join hashing only; exact verify follows)",
            "gpu_z37_order3_v2.py": "numpy default_rng(17) hash vector (join hashing only; exact verify follows)",
        },
        "committed": {},
        "excluded": {},
    }
    for name in COMMITTED:
        p = HERE / name
        if not p.exists():
            print("WARN committed artifact missing:", name)
            continue
        manifest["committed"][name] = {"sha256": sha256(p), "bytes": p.stat().st_size}
    for name, meta in EXCLUDED.items():
        p = HERE / name
        rec = dict(meta)
        if p.exists():
            rec["sha256"] = sha256(p)
            rec["bytes"] = p.stat().st_size
        else:
            rec["sha256"] = "ABSENT_AT_MANIFEST_BUILD"
        manifest["excluded"][name] = rec
    out = HERE / "ARTIFACT_MANIFEST.json"
    out.write_text(json.dumps(manifest, indent=1) + "\n", encoding="utf-8", newline="\n")
    print("wrote", out.name, "| committed:", len(manifest["committed"]),
          "| excluded:", len(manifest["excluded"]))


if __name__ == "__main__":
    main()
