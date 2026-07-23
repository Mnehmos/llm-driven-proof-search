"""Exact-Fourier BS(84,83) CUDA search with an incremental PSD cap.

Every chain uses the 500 parity-class generators from
``agent_bgpu_parity_classes`` and rejects moves outside the exact z=1,-1,i
margin manifold.  Fourier amplitudes at all 167th roots are maintained by a
rank-one update after each sign flip.  Half the population hard-enforces the
necessary per-sequence bound PSD <= 334; the other half uses heterogeneous
PSD excess penalties to move between cap-feasible components.
"""

from __future__ import annotations

import argparse
import glob
import json
import math
import time
from pathlib import Path

import numpy as np
import torch

import agent_bgpu_parity_classes as core


PSD_N = 167
PSD_K = PSD_N // 2 + 1
PSD_CAP = 334.0
PSD_EPS = 0.02


def psd_report(padded: np.ndarray, **kwargs) -> dict:
    report = core.scalar_report(padded, **kwargs)
    spectrum = np.fft.rfft(padded.astype(np.float64), n=PSD_N, axis=1)
    psd = spectrum.real * spectrum.real + spectrum.imag * spectrum.imag
    excess = np.maximum(psd - PSD_CAP, 0.0)
    report.update(
        {
            "psd_grid_order": PSD_N,
            "psd_cap": PSD_CAP,
            "psd_max": float(psd.max()),
            "psd_max_by_sequence": [float(x) for x in psd.max(axis=1)],
            "psd_cap_violations": int((psd > PSD_CAP + 1e-9).sum()),
            "psd_excess_l2": float(np.square(excess).sum()),
        }
    )
    return report


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed-glob", default="agent_bgpu_run1_fourier_class_*_live.json")
    ap.add_argument("--strict-seed", type=Path, default=Path("agent_bp2_fourier_e896_verified.json"))
    ap.add_argument("--seconds", type=float, default=300.0)
    ap.add_argument("--batch", type=int, default=8192)
    ap.add_argument("--cycle", type=int, default=1536)
    ap.add_argument("--progress-every", type=int, default=256)
    ap.add_argument("--archive-every", type=int, default=32)
    ap.add_argument("--temp-high", type=float, default=1600.0)
    ap.add_argument("--temp-low", type=float, default=0.03)
    ap.add_argument("--seed", type=int, default=334167668)
    ap.add_argument("--prefix", default="agent_bgpu_psd_run1")
    args = ap.parse_args()
    if not torch.cuda.is_available():
        raise SystemExit("CUDA required")
    if args.batch < 384:
        raise SystemExit("batch must be at least 384")
    torch.manual_seed(args.seed)
    torch.cuda.manual_seed_all(args.seed)
    np.random.seed(args.seed & 0xFFFFFFFF)
    dev = torch.device("cuda")
    prefix = Path(args.prefix)

    seed_paths = [args.strict_seed] + [Path(x) for x in sorted(glob.glob(args.seed_glob))]
    seed_data: list[tuple[Path, np.ndarray, dict]] = []
    seen_hashes: set[str] = set()
    for path in seed_paths:
        padded = core.load_sequences(path)
        report = psd_report(
            padded,
            elapsed_s=0.0,
            proposals=0,
            generation=0,
            search="agent_bgpu PSD seed audit",
        )
        if not report["fourier_exact"] or report["parity_bad"]:
            continue
        if report["psd_max"] > PSD_CAP + PSD_EPS:
            continue
        if report["sequence_sha256"] in seen_hashes:
            continue
        seen_hashes.add(report["sequence_sha256"])
        seed_data.append((path, padded, report))
    if not seed_data:
        raise ValueError("no exact-Fourier PSD-cap seed")
    strict_best_seed = min(seed_data, key=lambda x: x[2]["energy"])

    m1_np, m2_np, class_np = core.build_moves()
    left_np, right_np, left_ok_np, right_ok_np = core.build_neighbor_tables()
    m1 = torch.as_tensor(m1_np, dtype=torch.int64, device=dev)
    m2 = torch.as_tensor(m2_np, dtype=torch.int64, device=dev)
    chain = torch.arange(args.batch, dtype=torch.int64, device=dev)
    table = {
        "move1": m1,
        "move2": m2,
        "move_class": torch.as_tensor(class_np, dtype=torch.int64, device=dev),
        "left": torch.as_tensor(left_np, dtype=torch.int64, device=dev),
        "right": torch.as_tensor(right_np, dtype=torch.int64, device=dev),
        "left_ok": torch.as_tensor(left_ok_np, dtype=torch.int16, device=dev),
        "right_ok": torch.as_tensor(right_ok_np, dtype=torch.int16, device=dev),
        "chain": chain,
    }
    row_types = torch.as_tensor(core.ROW_TYPES, dtype=torch.int16, device=dev)

    bank = torch.as_tensor(np.stack([x[1] for x in seed_data]), dtype=torch.int8, device=dev).view(len(seed_data), -1)
    seed_ids = torch.arange(args.batch, device=dev) % len(seed_data)
    pop = bank[seed_ids].clone()
    r, rows, alts, z4, c3, c5 = core.initial_metrics(pop)
    rn, an, zn = core.norm2(rows), core.norm2(alts), core.norm2(z4)
    if not bool(((rn == 334) & (an == 334) & (zn == 334)).all().item()):
        raise AssertionError("PSD population did not start Fourier-exact")
    if bool((r.remainder(4) != 0).any().item()):
        raise AssertionError("PSD population did not start parity-zero")

    amps = torch.fft.rfft(pop.view(args.batch, 4, core.PAD).to(torch.float32), n=PSD_N, dim=2)
    freq = torch.arange(PSD_K, device=dev, dtype=torch.float32)
    pos = torch.arange(core.PAD, device=dev, dtype=torch.float32)
    angle = -2.0 * math.pi * pos[:, None] * freq[None, :] / PSD_N
    phase = torch.complex(torch.cos(angle), torch.sin(angle))

    profile_id = torch.arange(args.batch, device=dev) % 64
    profiles = torch.empty((64, core.H), device=dev)
    l1_bank = torch.tensor((0.0, 0.5, 1.0, 2.0, 4.0, 8.0, 12.0, 16.0), device=dev)
    l1_alpha = l1_bank[torch.arange(args.batch, device=dev) % len(l1_bank)]
    psd_bank = torch.tensor((0.01, 0.03, 0.1, 0.3, 1.0, 3.0, 10.0, 30.0), device=dev)
    psd_weight = psd_bank[torch.arange(args.batch, device=dev) % len(psd_bank)]
    spectral_bank = torch.tensor((0.0, 0.0, 0.0, 0.5, 1.0, 2.0, 4.0, 8.0), device=dev)
    spectral_weight = spectral_bank[torch.arange(args.batch, device=dev) % len(spectral_bank)]
    hard_cap = torch.arange(args.batch, device=dev) % 2 == 0
    temp_factor = torch.exp(torch.linspace(math.log(0.35), math.log(2.5), args.batch, device=dev))

    def refresh_profiles() -> None:
        profiles.copy_(torch.exp(0.6 * torch.randn_like(profiles)))
        profiles.div_(profiles.mean(dim=1, keepdim=True))

    def score(rr: torch.Tensor, aa: torch.Tensor, cc3: torch.Tensor, cc5: torch.Tensor):
        rf = rr.to(torch.float32)
        w = profiles[profile_id]
        base = (w * rf.square()).sum(dim=1) + l1_alpha * (w * rf.abs()).sum(dim=1)
        psd = aa.real.square() + aa.imag.square()
        excess = torch.relu(psd - PSD_CAP)
        psd_penalty = excess.square().sum(dim=(1, 2))
        psd_max = psd.amax(dim=(1, 2))
        q3, a5, b5 = core.spectral_values(cc3, cc5)
        spectral_penalty = (
            ((q3 - 334).to(torch.float32) / 4.0).square()
            + ((a5 - 334).to(torch.float32) / 4.0).square()
            + (b5.to(torch.float32) / 4.0).square()
        )
        return base + psd_weight * psd_penalty + spectral_weight * spectral_penalty, psd_max, psd_penalty, q3, a5, b5

    refresh_profiles()
    current_score, psd_max, psd_penalty, q3, a5, b5 = score(r, amps, c3, c5)
    if not bool((psd_max <= PSD_CAP + PSD_EPS).all().item()):
        raise AssertionError("seed FFT disagrees with scalar PSD audit")

    strict_best = strict_best_seed[2]
    core.compact_json(prefix.with_name(prefix.name + "_live.json"), strict_best)
    class_best: dict[int, dict] = {}
    for _, _, report in seed_data:
        cid = core.ROW_TYPES.index(tuple(report["row_magnitude_type"]))
        if cid not in class_best or report["energy"] < class_best[cid]["energy"]:
            class_best[cid] = report
            core.compact_json(prefix.with_name(prefix.name + f"_class_{cid:02d}_live.json"), report)

    print(
        json.dumps(
            {
                "event": "start",
                "device": torch.cuda.get_device_name(0),
                "batch": args.batch,
                "cap": PSD_CAP,
                "grid": PSD_N,
                "cap_valid_seeds": len(seed_data),
                "seed_classes": sorted(class_best),
                "best_energy": strict_best["energy"],
                "best_psd_max": strict_best["psd_max"],
            }
        ),
        flush=True,
    )

    # Independent delta/FFT audit for one random proposal.
    mids = torch.randint(500, (args.batch,), device=dev)
    cand = core.proposal(pop, r, rows, alts, z4, c3, c5, mids, table)
    _, _, _, _, _, _, _, bb1, bb2 = cand
    old1 = pop[chain, bb1].to(torch.float32)
    safe2 = bb2.clamp_min(0)
    old2 = pop[chain, safe2].to(torch.float32)
    nf = amps.clone()
    k1, p1 = torch.div(bb1, core.PAD, rounding_mode="floor"), bb1 % core.PAD
    k2, p2 = torch.div(safe2, core.PAD, rounding_mode="floor"), safe2 % core.PAD
    nf[chain, k1] += (-2.0 * old1)[:, None] * phase[p1]
    valid2 = bb2 >= 0
    nf[chain[valid2], k2[valid2]] += (-2.0 * old2[valid2])[:, None] * phase[p2[valid2]]
    ai = min(11, args.batch - 1)
    audit_state = core.extract_candidate(pop, ai, bb1, bb2)
    audit_fft = np.fft.rfft(audit_state.astype(np.float64), n=PSD_N, axis=1)
    if not np.allclose(audit_fft, nf[ai].cpu().numpy(), atol=2e-4, rtol=2e-5):
        raise AssertionError("incremental Fourier amplitude update failed")

    torch.cuda.synchronize()
    started = time.time()
    generation = 0
    proposals = 0
    solved = False
    while time.time() - started < args.seconds and not solved:
        if generation and generation % args.cycle == 0:
            refresh_profiles()
            current_score, psd_max, psd_penalty, q3, a5, b5 = score(r, amps, c3, c5)

        mids = torch.randint(500, (args.batch,), device=dev)
        cand = core.proposal(pop, r, rows, alts, z4, c3, c5, mids, table)
        nr, energy, nrows, nalts, nz4, nc3, nc5, bb1, bb2 = cand
        old1 = pop[chain, bb1].to(torch.float32)
        safe2 = bb2.clamp_min(0)
        old2 = pop[chain, safe2].to(torch.float32)
        nf = amps.clone()
        k1, p1 = torch.div(bb1, core.PAD, rounding_mode="floor"), bb1 % core.PAD
        k2, p2 = torch.div(safe2, core.PAD, rounding_mode="floor"), safe2 % core.PAD
        nf[chain, k1] += (-2.0 * old1)[:, None] * phase[p1]
        valid2 = bb2 >= 0
        nf[chain[valid2], k2[valid2]] += (-2.0 * old2[valid2])[:, None] * phase[p2[valid2]]

        nscore, npsd_max, npsd_penalty, nq3, na5, nb5 = score(nr, nf, nc3, nc5)
        nrn, nan, nzn = core.norm2(nrows), core.norm2(nalts), core.norm2(nz4)
        strict = (nrn == 334) & (nan == 334) & (nzn == 334)
        cap_ok = npsd_max <= PSD_CAP + PSD_EPS
        phase_t = (generation % args.cycle) / max(1, args.cycle - 1)
        base_temp = args.temp_high * (args.temp_low / args.temp_high) ** phase_t
        temperature = base_temp * temp_factor
        delta = nscore - current_score
        accepted = (delta <= 0) | (torch.rand(args.batch, device=dev) < torch.exp((-delta / temperature).clamp(max=0)))
        accepted &= strict
        accepted &= (~hard_cap) | cap_ok

        if generation % 4 == 0:
            feasible = strict & cap_ok
            masked = torch.where(feasible, energy, torch.full_like(energy, core.INF))
            value, index = masked.min(dim=0)
            ev = int(value.item())
            if ev < strict_best["energy"]:
                idx = int(index.item())
                report = psd_report(
                    core.extract_candidate(pop, idx, bb1, bb2),
                    elapsed_s=time.time() - started,
                    proposals=proposals + args.batch,
                    generation=generation,
                    search="agent_bgpu exact-Fourier PSD-cap CUDA population",
                )
                if report["energy"] != ev or not report["fourier_exact"] or report["psd_max"] > PSD_CAP + PSD_EPS:
                    raise AssertionError("PSD frontier scalar/GPU mismatch")
                strict_best = report
                core.compact_json(prefix.with_name(prefix.name + "_live.json"), report)
                print(
                    json.dumps(
                        {
                            "event": "strict_psd_frontier",
                            "energy": report["energy"],
                            "l1": report["l1"],
                            "row_type": report["row_magnitude_type"],
                            "psd_max": report["psd_max"],
                            "order3": report["order3_value"],
                            "order5": report["order5_values"],
                            "elapsed_s": report["elapsed_s"],
                        }
                    ),
                    flush=True,
                )
                if report["solved"]:
                    core.compact_json(prefix.with_name(prefix.name + "_candidate.json"), report)
                    solved = True

        if solved:
            break
        core.apply_candidate(pop, accepted, bb1, bb2, [r, rows, alts, z4, c3, c5], (nr, nrows, nalts, nz4, nc3, nc5))
        amps[accepted] = nf[accepted]
        current_score[accepted] = nscore[accepted]
        psd_max[accepted], psd_penalty[accepted] = npsd_max[accepted], npsd_penalty[accepted]
        q3[accepted], a5[accepted], b5[accepted] = nq3[accepted], na5[accepted], nb5[accepted]
        rn[accepted], an[accepted], zn[accepted] = nrn[accepted], nan[accepted], nzn[accepted]
        generation += 1
        proposals += args.batch

        if generation % args.archive_every == 0:
            type_ids = core.exact_row_type_ids(rows, row_types)
            cap_state = psd_max <= PSD_CAP + PSD_EPS
            state_energy = r.to(torch.int32).square().sum(dim=1, dtype=torch.int32)
            for cid in range(len(core.ROW_TYPES)):
                mask = cap_state & (type_ids == cid)
                if not bool(mask.any().item()):
                    continue
                vals = torch.where(mask, state_energy, torch.full_like(state_energy, core.INF))
                value, index = vals.min(dim=0)
                ev = int(value.item())
                if cid not in class_best or ev < class_best[cid]["energy"]:
                    idx = int(index.item())
                    report = psd_report(
                        core.extract_candidate(pop, idx),
                        elapsed_s=time.time() - started,
                        proposals=proposals,
                        generation=generation,
                        search="agent_bgpu exact-Fourier PSD-cap class archive",
                    )
                    if report["energy"] != ev or not report["fourier_exact"] or report["psd_max"] > PSD_CAP + PSD_EPS:
                        raise AssertionError("PSD class archive mismatch")
                    class_best[cid] = report
                    core.compact_json(prefix.with_name(prefix.name + f"_class_{cid:02d}_live.json"), report)
                    print(
                        json.dumps(
                            {
                                "event": "class_frontier",
                                "class": cid,
                                "energy": ev,
                                "l1": report["l1"],
                                "psd_max": report["psd_max"],
                                "elapsed_s": report["elapsed_s"],
                            }
                        ),
                        flush=True,
                    )

        if generation % args.progress_every == 0:
            torch.cuda.synchronize()
            elapsed = time.time() - started
            state_energy = r.to(torch.int32).square().sum(dim=1, dtype=torch.int32)
            cap_state = psd_max <= PSD_CAP + PSD_EPS
            spectral_state = cap_state & (q3 == 334) & (a5 == 334) & (b5 == 0)
            print(
                json.dumps(
                    {
                        "event": "progress",
                        "generation": generation,
                        "proposals": proposals,
                        "moves_per_s": proposals / max(elapsed, 1e-9),
                        "best": strict_best["energy"],
                        "classes": len(class_best),
                        "cap_population": int(cap_state.sum().item()),
                        "spectral_3_5_cap_population": int(spectral_state.sum().item()),
                        "population_min": int(state_energy.min().item()),
                        "elapsed_s": elapsed,
                    }
                ),
                flush=True,
            )
            idx = (generation // args.progress_every) % args.batch
            audit = psd_report(
                core.extract_candidate(pop, idx),
                elapsed_s=elapsed,
                proposals=proposals,
                generation=generation,
                search="agent_bgpu PSD drift audit",
            )
            if audit["residual"] != list(map(int, r[idx].cpu().tolist())):
                raise AssertionError("PSD accepted residual drift")
            amp_np = amps[idx].cpu().numpy()
            padded = np.zeros((4, core.PAD), dtype=np.int8)
            for k, n in enumerate(core.LENGTHS):
                padded[k, :n] = audit["sequences"][k]
            amp_exact = np.fft.rfft(padded.astype(np.float64), n=PSD_N, axis=1)
            if not np.allclose(amp_np, amp_exact, atol=2e-3, rtol=5e-5):
                raise AssertionError("PSD accepted amplitude drift")

    torch.cuda.synchronize()
    elapsed = time.time() - started
    strict_best["elapsed_s"] = elapsed
    strict_best["proposals"] = proposals
    core.compact_json(prefix.with_name(prefix.name + "_summary.json"), strict_best)
    archive = {
        "construction": "BS(84,83) exact-Fourier PSD-cap archive",
        "solved": solved,
        "independently_recomputed": True,
        "psd_grid_order": PSD_N,
        "psd_cap": PSD_CAP,
        "elapsed_s": elapsed,
        "proposals": proposals,
        "moves_per_s": proposals / max(elapsed, 1e-9),
        "classes_seen": len(class_best),
        "frontier": [
            {
                "class": cid,
                "row_type": list(core.ROW_TYPES[cid]),
                "energy": class_best[cid]["energy"],
                "l1": class_best[cid]["l1"],
                "psd_max": class_best[cid]["psd_max"],
                "checkpoint": prefix.name + f"_class_{cid:02d}_live.json",
            }
            for cid in sorted(class_best)
        ],
    }
    core.compact_json(prefix.with_name(prefix.name + "_classes_summary.json"), archive)
    print(
        json.dumps(
            {
                "event": "result",
                "solved": solved,
                "best": strict_best["energy"],
                "classes": len(class_best),
                "proposals": proposals,
                "moves_per_s": proposals / max(elapsed, 1e-9),
                "elapsed_s": elapsed,
            }
        ),
        flush=True,
    )
    return 0 if solved else 2


if __name__ == "__main__":
    raise SystemExit(main())
