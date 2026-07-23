"""CUDA population search in the exact parity space of BS(84,83).

The 334 signs split into 83 independent four-bit boundary-signature classes
and two zero-signature centre bits.  A proposal flips a pair in one class, or
one centre bit.  Thus every CUDA chain remains in the residual-mod-4-zero
affine space without a repair or penalty.

The search mixes three populations:

* raw residual-energy chains;
* soft Fourier/spectral chains spread over all 12 feasible row-magnitude
  types; and
* hard Fourier chains that reject every proposal outside the exact
  z=1,-1,i margin manifold.

All published checkpoints are rebuilt by a separate scalar CPU evaluator.
Output names deliberately use the private ``agent_bgpu_*`` prefix.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import math
import time
from pathlib import Path

import numpy as np
import torch


LENGTHS = (84, 84, 83, 83)
PAD = 84
H = 83
INF = 2_000_000_000

# Exact solutions have one of these absolute row-margin types.  The first two
# entries belong to the even-length sequences and the final two to the odd.
ROW_TYPES = (
    (0, 6, 3, 17),
    (0, 10, 3, 15),
    (0, 18, 1, 3),
    (2, 4, 5, 17),
    (2, 16, 5, 7),
    (4, 10, 7, 13),
    (4, 14, 1, 11),
    (6, 8, 3, 15),
    (8, 10, 1, 13),
    (8, 10, 7, 11),
    (8, 14, 5, 7),
    (10, 12, 3, 9),
)


def load_sequences(path: Path) -> np.ndarray:
    data = json.loads(path.read_text(encoding="utf-8"))
    seq = data["sequences"]
    if tuple(map(len, seq)) != LENGTHS:
        raise ValueError(f"{path}: expected sequence lengths {LENGTHS}")
    if any(v not in (-1, 1) for row in seq for v in row):
        raise ValueError(f"{path}: entries must be +/-1")
    out = np.zeros((4, PAD), dtype=np.int8)
    for k, n in enumerate(LENGTHS):
        out[k, :n] = np.asarray(seq[k], dtype=np.int8)
    return out


def scalar_report(
    padded: np.ndarray,
    *,
    elapsed_s: float,
    proposals: int,
    generation: int,
    search: str,
) -> dict:
    """Independent scalar recomputation used for every published state."""
    seq = [list(map(int, padded[k, :n])) for k, n in enumerate(LENGTHS)]
    if tuple(map(len, seq)) != LENGTHS or any(v not in (-1, 1) for s in seq for v in s):
        raise AssertionError("invalid sequence payload")
    residual = [
        sum(
            sum(s[i] * s[i + d] for i in range(len(s) - d))
            for s in seq
        )
        for d in range(1, 84)
    ]
    energy = sum(x * x for x in residual)
    rows = [sum(s) for s in seq]
    alts = [
        sum((1 if i % 2 == 0 else -1) * x for i, x in enumerate(s))
        for s in seq
    ]
    z4 = []
    for s in seq:
        z4.extend((sum(s[0::4]) - sum(s[2::4]), sum(s[1::4]) - sum(s[3::4])))
    cubic = []
    quintic = []
    q3 = 0
    a5 = 0
    b5 = 0
    for s in seq:
        v3 = [sum(s[r::3]) for r in range(3)]
        v5 = [sum(s[r::5]) for r in range(5)]
        cubic.append(v3)
        quintic.append(v5)
        q3 += sum(x * x for x in v3) - (v3[0] * v3[1] + v3[1] * v3[2] + v3[2] * v3[0])
        s0 = sum(x * x for x in v5)
        s1 = sum(v5[i] * v5[(i + 1) % 5] for i in range(5))
        s2 = sum(v5[i] * v5[(i + 2) % 5] for i in range(5))
        a5 += s0 - s1
        b5 += s1 - s2
    row_norm = sum(x * x for x in rows)
    alt_norm = sum(x * x for x in alts)
    z4_norm = sum(x * x for x in z4)
    row_type = tuple(sorted(map(abs, rows[:2])) + sorted(map(abs, rows[2:])))
    raw = b"".join(np.asarray(s, dtype=np.int8).tobytes() for s in seq)
    report = {
        "construction": "base sequences BS(84,83)",
        "search": search,
        "solved": energy == 0,
        "independently_recomputed": True,
        "residual_mod4_exact": all(x % 4 == 0 for x in residual),
        "energy": energy,
        "l1": sum(map(abs, residual)),
        "nonzero": sum(x != 0 for x in residual),
        "parity_bad": sum(x % 4 != 0 for x in residual),
        "elapsed_s": elapsed_s,
        "proposals": proposals,
        "generation": generation,
        "row_sums": rows,
        "row_norm": row_norm,
        "row_magnitude_type": list(row_type),
        "alternating_sums": alts,
        "alternating_norm": alt_norm,
        "z4_components": z4,
        "z4_norm": z4_norm,
        "cubic_components": cubic,
        "order3_value": q3,
        "quintic_components": quintic,
        "order5_values": [a5, b5],
        "fourier_exact": row_norm == alt_norm == z4_norm == 334,
        "spectral_3_5_exact": (q3, a5, b5) == (334, 334, 0),
        "sequence_sha256": hashlib.sha256(raw).hexdigest(),
        "residual": residual,
        "sequences": seq,
    }
    if report["parity_bad"]:
        raise AssertionError("GPU search left the parity-zero affine space")
    if energy == 0 and any(residual):
        raise AssertionError("false zero energy")
    return report


def compact_json(path: Path, value: dict) -> None:
    path.write_text(json.dumps(value, separators=(",", ":")) + "\n", encoding="utf-8")


def build_moves() -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    classes: list[list[int]] = []
    for j in range(42):
        p, q = j, 83 - j
        classes.append([0 * PAD + p, 0 * PAD + q, 1 * PAD + p, 1 * PAD + q])
    for j in range(41):
        p, q = j, 82 - j
        classes.append([2 * PAD + p, 2 * PAD + q, 3 * PAD + p, 3 * PAD + q])
    if len(classes) != H:
        raise AssertionError("wrong boundary-class count")
    first: list[int] = []
    second: list[int] = []
    move_class: list[int] = []
    for j, bits in enumerate(classes):
        for p, q in itertools.combinations(bits, 2):
            first.append(p)
            second.append(q)
            move_class.append(j)
    first.extend((2 * PAD + 41, 3 * PAD + 41))
    second.extend((-1, -1))
    move_class.extend((83, 84))
    if len(first) != 500:
        raise AssertionError("expected 500 parity generators")
    return np.asarray(first, np.int64), np.asarray(second, np.int64), np.asarray(move_class, np.int64)


def build_neighbor_tables() -> tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray]:
    left = np.zeros((4 * PAD, H), dtype=np.int64)
    right = np.zeros((4 * PAD, H), dtype=np.int64)
    left_ok = np.zeros((4 * PAD, H), dtype=np.int8)
    right_ok = np.zeros((4 * PAD, H), dtype=np.int8)
    for k, n in enumerate(LENGTHS):
        for p in range(PAD):
            g = k * PAD + p
            for dd, d in enumerate(range(1, 84)):
                if p - d >= 0 and p < n:
                    left[g, dd] = k * PAD + p - d
                    left_ok[g, dd] = 1
                else:
                    left[g, dd] = k * PAD
                if p + d < n:
                    right[g, dd] = k * PAD + p + d
                    right_ok[g, dd] = 1
                else:
                    right[g, dd] = k * PAD
    return left, right, left_ok, right_ok


def initial_metrics(pop: torch.Tensor) -> tuple[torch.Tensor, ...]:
    """Exact batched state rebuild; padded positions of odd rows are zero."""
    batch = pop.shape[0]
    x = pop.view(batch, 4, PAD)
    r = torch.empty((batch, H), dtype=torch.int16, device=pop.device)
    for dd, d in enumerate(range(1, 84)):
        r[:, dd] = (x[:, :, :-d].to(torch.int16) * x[:, :, d:].to(torch.int16)).sum(
            dim=(1, 2), dtype=torch.int32
        ).to(torch.int16)
    rows = x.sum(dim=2, dtype=torch.int16)
    alt_coeff = torch.where(
        torch.arange(PAD, device=pop.device) % 2 == 0,
        torch.ones(PAD, dtype=torch.int16, device=pop.device),
        -torch.ones(PAD, dtype=torch.int16, device=pop.device),
    )
    alts = (x.to(torch.int16) * alt_coeff).sum(dim=2, dtype=torch.int16)
    z4 = torch.zeros((batch, 8), dtype=torch.int16, device=pop.device)
    c3 = torch.zeros((batch, 4, 3), dtype=torch.int16, device=pop.device)
    c5 = torch.zeros((batch, 4, 5), dtype=torch.int16, device=pop.device)
    for k in range(4):
        for p in range(LENGTHS[k]):
            values = x[:, k, p].to(torch.int16)
            zidx = 2 * k + (p & 1)
            zcoef = 1 if p % 4 < 2 else -1
            z4[:, zidx] += zcoef * values
            c3[:, k, p % 3] += values
            c5[:, k, p % 5] += values
    return r, rows, alts, z4, c3, c5


def norm2(x: torch.Tensor) -> torch.Tensor:
    return x.to(torch.int32).square().sum(dim=tuple(range(1, x.ndim)), dtype=torch.int32)


def spectral_values(c3: torch.Tensor, c5: torch.Tensor) -> tuple[torch.Tensor, ...]:
    u = c3.to(torch.int32)
    q3 = (
        u.square().sum(dim=(1, 2), dtype=torch.int32)
        - (u[:, :, 0] * u[:, :, 1] + u[:, :, 1] * u[:, :, 2] + u[:, :, 2] * u[:, :, 0]).sum(
            dim=1, dtype=torch.int32
        )
    )
    v = c5.to(torch.int32)
    s0 = v.square().sum(dim=(1, 2), dtype=torch.int32)
    s1 = (v * torch.roll(v, -1, dims=2)).sum(dim=(1, 2), dtype=torch.int32)
    s2 = (v * torch.roll(v, -2, dims=2)).sum(dim=(1, 2), dtype=torch.int32)
    return q3, s0 - s1, s1 - s2


def exact_row_type_ids(rows: torch.Tensor, row_types: torch.Tensor) -> torch.Tensor:
    even = rows[:, :2].abs().sort(dim=1).values
    odd = rows[:, 2:].abs().sort(dim=1).values
    sig = torch.cat((even, odd), dim=1)
    eq = (sig[:, None, :] == row_types[None, :, :]).all(dim=2)
    ids = eq.to(torch.int8).argmax(dim=1).to(torch.int64)
    return torch.where(eq.any(dim=1), ids, torch.full_like(ids, -1))


def proposal(
    pop: torch.Tensor,
    r: torch.Tensor,
    rows: torch.Tensor,
    alts: torch.Tensor,
    z4: torch.Tensor,
    c3: torch.Tensor,
    c5: torch.Tensor,
    move_ids: torch.Tensor,
    table: dict[str, torch.Tensor],
) -> tuple[torch.Tensor, ...]:
    """Compute one exact legal proposal per chain without mutating the state."""
    batch = pop.shape[0]
    chain = table["chain"]
    b1 = table["move1"][move_ids]
    b2 = table["move2"][move_ids]
    valid2 = b2 >= 0
    safe2 = b2.clamp_min(0)
    old1 = pop[chain, b1].to(torch.int16)
    old2 = pop[chain, safe2].to(torch.int16)

    li1 = table["left"][b1]
    ri1 = table["right"][b1]
    n1 = (
        pop.gather(1, li1).to(torch.int16) * table["left_ok"][b1]
        + pop.gather(1, ri1).to(torch.int16) * table["right_ok"][b1]
    )
    dr = -2 * old1[:, None] * n1
    li2 = table["left"][safe2]
    ri2 = table["right"][safe2]
    n2 = (
        pop.gather(1, li2).to(torch.int16) * table["left_ok"][safe2]
        + pop.gather(1, ri2).to(torch.int16) * table["right_ok"][safe2]
    )
    dr += (-2 * old2[:, None] * n2) * valid2[:, None]

    k1, p1 = torch.div(b1, PAD, rounding_mode="floor"), b1 % PAD
    k2, p2 = torch.div(safe2, PAD, rounding_mode="floor"), safe2 % PAD
    same = valid2 & (k1 == k2)
    shift = (p1 - p2).abs()
    correction = (4 * old1 * old2 * same).to(torch.int16)
    dr.scatter_add_(1, (shift - 1).clamp(0, H - 1)[:, None], correction[:, None])
    nr = r + dr
    energy = nr.to(torch.int32).square().sum(dim=1, dtype=torch.int32)

    nrows = rows.clone()
    nalts = alts.clone()
    nz4 = z4.clone()
    nc3 = c3.clone()
    nc5 = c5.clone()

    def update(bit: torch.Tensor, old: torch.Tensor, valid: torch.Tensor) -> None:
        kk = torch.div(bit, PAD, rounding_mode="floor")
        pp = bit % PAD
        delta = (-2 * old * valid).to(torch.int16)
        nrows[chain, kk] += delta
        nalts[chain, kk] += delta * torch.where(pp % 2 == 0, 1, -1).to(torch.int16)
        zi = 2 * kk + (pp & 1)
        zcoef = torch.where(pp % 4 < 2, 1, -1).to(torch.int16)
        nz4[chain, zi] += delta * zcoef
        nc3[chain, kk, pp % 3] += delta
        nc5[chain, kk, pp % 5] += delta

    update(b1, old1, torch.ones(batch, dtype=torch.int16, device=pop.device))
    update(safe2, old2, valid2.to(torch.int16))
    return nr, energy, nrows, nalts, nz4, nc3, nc5, b1, b2


def apply_candidate(
    pop: torch.Tensor,
    accepted: torch.Tensor,
    b1: torch.Tensor,
    b2: torch.Tensor,
    current: list[torch.Tensor],
    candidate: tuple[torch.Tensor, ...],
) -> None:
    chain = torch.arange(pop.shape[0], device=pop.device)
    ids = chain[accepted]
    pop[ids, b1[accepted]] *= -1
    valid = accepted & (b2 >= 0)
    ids2 = chain[valid]
    pop[ids2, b2[valid]] *= -1
    for dst, src in zip(current, candidate):
        dst[accepted] = src[accepted]


def extract_candidate(pop: torch.Tensor, index: int, b1: torch.Tensor | None = None, b2: torch.Tensor | None = None) -> np.ndarray:
    out = pop[index].view(4, PAD).detach().cpu().numpy().astype(np.int8, copy=True)
    if b1 is not None:
        g1 = int(b1[index].item())
        out[g1 // PAD, g1 % PAD] *= -1
        g2 = int(b2[index].item())
        if g2 >= 0:
            out[g2 // PAD, g2 % PAD] *= -1
    return out


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--strict", type=Path, default=Path("agent_bp2_fourier_e896_verified.json"))
    ap.add_argument("--raw", type=Path, default=Path("agent_bp2_e736_verified.json"))
    ap.add_argument("--seconds", type=float, default=600.0)
    ap.add_argument("--batch", type=int, default=8192)
    ap.add_argument("--seed", type=int, default=668428)
    ap.add_argument("--cycle", type=int, default=2048)
    ap.add_argument("--archive-every", type=int, default=32)
    ap.add_argument("--progress-every", type=int, default=256)
    ap.add_argument("--initial-moves", type=int, default=48)
    ap.add_argument("--temp-high", type=float, default=1800.0)
    ap.add_argument("--temp-low", type=float, default=0.05)
    ap.add_argument("--prefix", default="agent_bgpu")
    args = ap.parse_args()
    if not torch.cuda.is_available():
        raise SystemExit("CUDA is required")
    if args.batch < 384:
        raise SystemExit("batch should be at least 384")

    torch.manual_seed(args.seed)
    torch.cuda.manual_seed_all(args.seed)
    np.random.seed(args.seed & 0xFFFFFFFF)
    device = torch.device("cuda")
    strict_seed = load_sequences(args.strict)
    raw_seed = load_sequences(args.raw)
    strict_check = scalar_report(strict_seed, elapsed_s=0.0, proposals=0, generation=0, search="agent_bgpu seed audit")
    raw_check = scalar_report(raw_seed, elapsed_s=0.0, proposals=0, generation=0, search="agent_bgpu seed audit")
    if not strict_check["fourier_exact"] or strict_check["parity_bad"]:
        raise ValueError("strict seed must be exact-Fourier and parity-zero")
    if raw_check["parity_bad"]:
        raise ValueError("raw seed must be parity-zero")

    m1_np, m2_np, class_np = build_moves()
    left_np, right_np, left_ok_np, right_ok_np = build_neighbor_tables()
    m1 = torch.as_tensor(m1_np, dtype=torch.int64, device=device)
    m2 = torch.as_tensor(m2_np, dtype=torch.int64, device=device)
    move_class = torch.as_tensor(class_np, dtype=torch.int64, device=device)
    chain = torch.arange(args.batch, dtype=torch.int64, device=device)
    table = {
        "move1": m1,
        "move2": m2,
        "move_class": move_class,
        "left": torch.as_tensor(left_np, dtype=torch.int64, device=device),
        "right": torch.as_tensor(right_np, dtype=torch.int64, device=device),
        "left_ok": torch.as_tensor(left_ok_np, dtype=torch.int16, device=device),
        "right_ok": torch.as_tensor(right_ok_np, dtype=torch.int16, device=device),
        "chain": chain,
    }
    row_types = torch.as_tensor(ROW_TYPES, dtype=torch.int16, device=device)

    # Modes: raw, soft target-class, hard exact-Fourier.
    mode = torch.arange(args.batch, device=device) * 3 // args.batch
    raw_mask = mode == 0
    soft_mask = mode == 1
    hard_mask = mode == 2
    target_type = torch.arange(args.batch, device=device) % len(ROW_TYPES)

    s0 = torch.as_tensor(strict_seed.reshape(-1), dtype=torch.int8, device=device)
    s1 = torch.as_tensor(raw_seed.reshape(-1), dtype=torch.int8, device=device)
    pop = s0[None, :].expand(args.batch, -1).clone()
    # Raw and soft populations begin with classwise children of the two seeds.
    class_of_bit = np.empty(4 * PAD, dtype=np.int64)
    for g in range(4 * PAD):
        k, p = divmod(g, PAD)
        if k < 2:
            class_of_bit[g] = min(p, 83 - p)
        elif p == 41:
            class_of_bit[g] = 83 + (k - 2)
        elif p < 83:
            class_of_bit[g] = 42 + min(p, 82 - p)
        else:
            class_of_bit[g] = 83 + (k - 2)
    class_of_bit_t = torch.as_tensor(class_of_bit, dtype=torch.int64, device=device)
    choices = torch.rand((args.batch, 85), device=device) < 0.5
    take_raw = choices[:, class_of_bit_t] & (~hard_mask[:, None])
    pop = torch.where(take_raw, s1[None, :], pop)
    # Reassert the two padded positions: they are not variables.
    pop[:, 2 * PAD + 83] = 0
    pop[:, 3 * PAD + 83] = 0
    # Additional legal perturbations diversify raw/soft chains.
    depths = torch.randint(0, args.initial_moves + 1, (args.batch,), device=device)
    depths[hard_mask] = 0
    depths[0] = 0
    for j in range(args.initial_moves):
        mids = torch.randint(500, (args.batch,), device=device)
        active = depths > j
        bb1, bb2 = m1[mids], m2[mids]
        ids = chain[active]
        pop[ids, bb1[active]] *= -1
        valid = active & (bb2 >= 0)
        ids2 = chain[valid]
        pop[ids2, bb2[valid]] *= -1
    # Keep one literal representative of each source frontier in the live
    # population (all other chains remain diversified).
    pop[0] = s1
    pop[args.batch // 3] = s0

    r, rows, alts, z4, c3, c5 = initial_metrics(pop)
    if bool((r.remainder(4) != 0).any().item()):
        raise AssertionError("classwise initialization broke parity")

    # Fixed residual profiles make equal-energy chains follow distinct basins.
    profiles = torch.exp(0.55 * torch.randn((64, H), device=device))
    profiles /= profiles.mean(dim=1, keepdim=True)
    profile_id = torch.arange(args.batch, device=device) % profiles.shape[0]
    l1_alpha_bank = torch.tensor((0.0, 0.5, 1.0, 2.0, 4.0, 8.0, 12.0, 16.0), device=device)
    l1_alpha = l1_alpha_bank[torch.arange(args.batch, device=device) % len(l1_alpha_bank)]
    margin_bank = torch.tensor((4.0, 8.0, 16.0, 24.0, 32.0, 48.0, 64.0, 96.0), device=device)
    margin_weight = margin_bank[torch.arange(args.batch, device=device) % len(margin_bank)]
    margin_weight = torch.where(soft_mask, margin_weight, torch.zeros_like(margin_weight))
    spectral_bank = torch.tensor((0.0, 0.0, 0.0, 1.0, 2.0, 4.0, 8.0, 16.0), device=device)
    spectral_weight = spectral_bank[torch.arange(args.batch, device=device) % len(spectral_bank)]
    spectral_weight = torch.where(soft_mask, spectral_weight, torch.zeros_like(spectral_weight))
    target_weight = torch.where(soft_mask, torch.full_like(margin_weight, 2.0), torch.zeros_like(margin_weight))

    def score(
        rr: torch.Tensor,
        rrows: torch.Tensor,
        aalts: torch.Tensor,
        zz4: torch.Tensor,
        cc3: torch.Tensor,
        cc5: torch.Tensor,
    ) -> tuple[torch.Tensor, ...]:
        rf = rr.to(torch.float32)
        w = profiles[profile_id]
        base = (w * rf.square()).sum(dim=1) + l1_alpha * (w * rf.abs()).sum(dim=1)
        rn, an, zn = norm2(rrows), norm2(aalts), norm2(zz4)
        dm = (
            ((rn - 334).to(torch.float32) / 8.0).square()
            + ((an - 334).to(torch.float32) / 8.0).square()
            + ((zn - 334).to(torch.float32) / 8.0).square()
        )
        q3, a5, b5 = spectral_values(cc3, cc5)
        ds = (
            ((q3 - 334).to(torch.float32) / 4.0).square()
            + ((a5 - 334).to(torch.float32) / 4.0).square()
            + (b5.to(torch.float32) / 4.0).square()
        )
        even = rrows[:, :2].abs().sort(dim=1).values
        odd = rrows[:, 2:].abs().sort(dim=1).values
        sig = torch.cat((even, odd), dim=1).to(torch.float32)
        td = (sig - row_types[target_type].to(torch.float32)).square().sum(dim=1)
        return base + margin_weight * dm + spectral_weight * ds + target_weight * td, rn, an, zn, q3, a5, b5

    current_score, rn, an, zn, q3, a5, b5 = score(r, rows, alts, z4, c3, c5)
    if not bool(((rn[hard_mask] == 334) & (an[hard_mask] == 334) & (zn[hard_mask] == 334)).all().item()):
        raise AssertionError("hard population did not start Fourier-exact")

    prefix = Path(args.prefix)
    raw_best = raw_check
    strict_best = strict_check
    compact_json(prefix.with_name(prefix.name + "_parity_live.json"), raw_best)
    compact_json(prefix.with_name(prefix.name + "_fourier_live.json"), strict_best)
    class_best: dict[int, dict] = {}
    signature_best: dict[tuple[int, ...], int] = {}

    def register(report: dict, *, force: bool = False) -> bool:
        nonlocal strict_best
        if not report["fourier_exact"]:
            return False
        rt = tuple(report["row_magnitude_type"])
        try:
            cid = ROW_TYPES.index(rt)
        except ValueError as exc:
            raise AssertionError(f"unknown exact row type {rt}") from exc
        signature = tuple(report["row_sums"] + report["alternating_sums"] + report["z4_components"])
        old_sig = signature_best.get(signature, INF)
        signature_best[signature] = min(old_sig, report["energy"])
        old = class_best.get(cid)
        improved = old is None or report["energy"] < old["energy"]
        if improved or force:
            if improved:
                class_best[cid] = report
            target = prefix.with_name(prefix.name + f"_fourier_class_{cid:02d}_live.json")
            if improved:
                compact_json(target, report)
                print(
                    json.dumps(
                        {
                            "event": "class_frontier",
                            "class": cid,
                            "row_type": ROW_TYPES[cid],
                            "energy": report["energy"],
                            "l1": report["l1"],
                            "rows": report["row_sums"],
                            "alts": report["alternating_sums"],
                            "z4": report["z4_components"],
                            "elapsed_s": report["elapsed_s"],
                        }
                    ),
                    flush=True,
                )
        if report["energy"] < strict_best["energy"]:
            strict_best = report
            compact_json(prefix.with_name(prefix.name + "_fourier_live.json"), report)
            print(
                json.dumps(
                    {
                        "event": "strict_frontier",
                        "energy": report["energy"],
                        "l1": report["l1"],
                        "class": cid,
                        "rows": report["row_sums"],
                        "alts": report["alternating_sums"],
                        "z4": report["z4_components"],
                        "order3": report["order3_value"],
                        "order5": report["order5_values"],
                        "elapsed_s": report["elapsed_s"],
                    }
                ),
                flush=True,
            )
            return True
        return improved

    register(strict_check, force=True)
    print(
        json.dumps(
            {
                "event": "start",
                "device": torch.cuda.get_device_name(0),
                "batch": args.batch,
                "moves": 500,
                "raw_seed_energy": raw_check["energy"],
                "strict_seed_energy": strict_check["energy"],
                "row_types": len(ROW_TYPES),
                "mode_counts": [int(raw_mask.sum()), int(soft_mask.sum()), int(hard_mask.sum())],
            }
        ),
        flush=True,
    )

    # Audit one incremental proposal before entering the timed campaign.
    audit_mids = torch.randint(500, (args.batch,), device=device)
    audit = proposal(pop, r, rows, alts, z4, c3, c5, audit_mids, table)
    audit_index = min(7, args.batch - 1)
    audit_state = extract_candidate(pop, audit_index, audit[-2], audit[-1])
    audit_report = scalar_report(audit_state, elapsed_s=0.0, proposals=0, generation=0, search="agent_bgpu delta audit")
    if audit_report["residual"] != list(map(int, audit[0][audit_index].cpu().tolist())):
        raise AssertionError("incremental residual update failed scalar audit")
    if audit_report["row_sums"] != list(map(int, audit[2][audit_index].cpu().tolist())):
        raise AssertionError("incremental row update failed scalar audit")
    if audit_report["alternating_sums"] != list(map(int, audit[3][audit_index].cpu().tolist())):
        raise AssertionError("incremental alternating update failed scalar audit")
    if audit_report["z4_components"] != list(map(int, audit[4][audit_index].cpu().tolist())):
        raise AssertionError("incremental z4 update failed scalar audit")

    torch.cuda.synchronize()
    started = time.time()
    generation = 0
    proposals_done = 0
    solved = False

    while time.time() - started < args.seconds and not solved:
        move_ids = torch.randint(500, (args.batch,), device=device)
        cand = proposal(pop, r, rows, alts, z4, c3, c5, move_ids, table)
        nr, energy, nrows, nalts, nz4, nc3, nc5, bb1, bb2 = cand
        nscore, nrn, nan, nzn, nq3, na5, nb5 = score(nr, nrows, nalts, nz4, nc3, nc5)
        strict = (nrn == 334) & (nan == 334) & (nzn == 334)

        phase = (generation % args.cycle) / max(1, args.cycle - 1)
        temp = args.temp_high * (args.temp_low / args.temp_high) ** phase
        delta = nscore - current_score
        accepted = (delta <= 0) | (torch.rand(args.batch, device=device) < torch.exp((-delta / temp).clamp(max=0)))
        accepted &= (~hard_mask) | strict

        # Check raw and strict frontiers before acceptance can discard them.
        if generation % 8 == 0:
            emin, ei = energy.min(dim=0)
            if int(emin.item()) < raw_best["energy"]:
                idx = int(ei.item())
                report = scalar_report(
                    extract_candidate(pop, idx, bb1, bb2),
                    elapsed_s=time.time() - started,
                    proposals=proposals_done + args.batch,
                    generation=generation,
                    search="agent_bgpu CUDA parity-class population",
                )
                if report["energy"] != int(emin.item()):
                    raise AssertionError("raw candidate GPU/scalar mismatch")
                raw_best = report
                compact_json(prefix.with_name(prefix.name + "_parity_live.json"), report)
                print(
                    json.dumps(
                        {
                            "event": "raw_frontier",
                            "energy": report["energy"],
                            "l1": report["l1"],
                            "nonzero": report["nonzero"],
                            "fourier_exact": report["fourier_exact"],
                            "elapsed_s": report["elapsed_s"],
                        }
                    ),
                    flush=True,
                )
                if report["solved"]:
                    compact_json(prefix.with_name(prefix.name + "_candidate.json"), report)
                    solved = True
            masked = torch.where(strict, energy, torch.full_like(energy, INF))
            se, si = masked.min(dim=0)
            if int(se.item()) < strict_best["energy"]:
                idx = int(si.item())
                report = scalar_report(
                    extract_candidate(pop, idx, bb1, bb2),
                    elapsed_s=time.time() - started,
                    proposals=proposals_done + args.batch,
                    generation=generation,
                    search="agent_bgpu CUDA exact-Fourier parity-class population",
                )
                if report["energy"] != int(se.item()) or not report["fourier_exact"]:
                    raise AssertionError("strict candidate GPU/scalar mismatch")
                register(report)
                if report["solved"]:
                    compact_json(prefix.with_name(prefix.name + "_candidate.json"), report)
                    solved = True

        if solved:
            break
        apply_candidate(pop, accepted, bb1, bb2, [r, rows, alts, z4, c3, c5], (nr, nrows, nalts, nz4, nc3, nc5))
        current_score[accepted] = nscore[accepted]
        rn[accepted], an[accepted], zn[accepted] = nrn[accepted], nan[accepted], nzn[accepted]
        q3[accepted], a5[accepted], b5[accepted] = nq3[accepted], na5[accepted], nb5[accepted]
        generation += 1
        proposals_done += args.batch

        # Populate all row-margin classes from accepted exact-Fourier states.
        if generation % args.archive_every == 0:
            is_strict = (rn == 334) & (an == 334) & (zn == 334)
            type_ids = exact_row_type_ids(rows, row_types)
            state_energy = r.to(torch.int32).square().sum(dim=1, dtype=torch.int32)
            for cid in range(len(ROW_TYPES)):
                mask = is_strict & (type_ids == cid)
                if not bool(mask.any().item()):
                    continue
                values = torch.where(mask, state_energy, torch.full_like(state_energy, INF))
                value, index = values.min(dim=0)
                ev = int(value.item())
                if cid not in class_best or ev < class_best[cid]["energy"]:
                    idx = int(index.item())
                    report = scalar_report(
                        extract_candidate(pop, idx),
                        elapsed_s=time.time() - started,
                        proposals=proposals_done,
                        generation=generation,
                        search="agent_bgpu CUDA Fourier-class archive",
                    )
                    if report["energy"] != ev or not report["fourier_exact"]:
                        raise AssertionError("class archive GPU/scalar mismatch")
                    register(report)

        if generation % args.progress_every == 0:
            torch.cuda.synchronize()
            elapsed = time.time() - started
            current_energy = r.to(torch.int32).square().sum(dim=1, dtype=torch.int32)
            strict_now = (rn == 334) & (an == 334) & (zn == 334)
            spectral_now = strict_now & (q3 == 334) & (a5 == 334) & (b5 == 0)
            summary = {
                "event": "progress",
                "generation": generation,
                "proposals": proposals_done,
                "moves_per_s": proposals_done / max(elapsed, 1e-9),
                "raw_best": raw_best["energy"],
                "strict_best": strict_best["energy"],
                "classes_seen": len(class_best),
                "signed_signatures_seen": len(signature_best),
                "strict_population": int(strict_now.sum().item()),
                "spectral_3_5_population": int(spectral_now.sum().item()),
                "population_min": int(current_energy.min().item()),
                "elapsed_s": elapsed,
            }
            print(json.dumps(summary), flush=True)

            # Periodic scalar drift audit of an accepted chain.
            idx = (generation // args.progress_every) % args.batch
            check = scalar_report(
                extract_candidate(pop, idx),
                elapsed_s=elapsed,
                proposals=proposals_done,
                generation=generation,
                search="agent_bgpu periodic drift audit",
            )
            if check["residual"] != list(map(int, r[idx].cpu().tolist())):
                raise AssertionError("accepted residual state drift")

            archive_index = {
                "construction": "BS(84,83) exact-Fourier parity-class archive",
                "independently_recomputed": True,
                "elapsed_s": elapsed,
                "proposals": proposals_done,
                "moves_per_s": proposals_done / max(elapsed, 1e-9),
                "classes_seen": len(class_best),
                "signed_signatures_seen": len(signature_best),
                "row_types": [list(x) for x in ROW_TYPES],
                "frontier": [
                    {
                        "class": cid,
                        "row_type": list(ROW_TYPES[cid]),
                        "energy": class_best[cid]["energy"],
                        "l1": class_best[cid]["l1"],
                        "rows": class_best[cid]["row_sums"],
                        "alts": class_best[cid]["alternating_sums"],
                        "z4": class_best[cid]["z4_components"],
                        "checkpoint": prefix.name + f"_fourier_class_{cid:02d}_live.json",
                    }
                    for cid in sorted(class_best)
                ],
            }
            compact_json(prefix.with_name(prefix.name + "_fourier_classes_live.json"), archive_index)

    torch.cuda.synchronize()
    elapsed = time.time() - started
    raw_best["elapsed_s"] = elapsed
    raw_best["proposals"] = proposals_done
    strict_best["elapsed_s"] = elapsed
    strict_best["proposals"] = proposals_done
    compact_json(prefix.with_name(prefix.name + "_parity_summary.json"), raw_best)
    compact_json(prefix.with_name(prefix.name + "_fourier_summary.json"), strict_best)
    archive_summary = {
        "construction": "BS(84,83) exact-Fourier parity-class archive",
        "solved": solved,
        "independently_recomputed": True,
        "elapsed_s": elapsed,
        "proposals": proposals_done,
        "moves_per_s": proposals_done / max(elapsed, 1e-9),
        "classes_seen": len(class_best),
        "signed_signatures_seen": len(signature_best),
        "frontier": [
            {
                "class": cid,
                "row_type": list(ROW_TYPES[cid]),
                "energy": class_best[cid]["energy"],
                "l1": class_best[cid]["l1"],
                "rows": class_best[cid]["row_sums"],
                "alts": class_best[cid]["alternating_sums"],
                "z4": class_best[cid]["z4_components"],
                "checkpoint": prefix.name + f"_fourier_class_{cid:02d}_live.json",
            }
            for cid in sorted(class_best)
        ],
    }
    compact_json(prefix.with_name(prefix.name + "_fourier_classes_summary.json"), archive_summary)
    print(
        json.dumps(
            {
                "event": "result",
                "solved": solved,
                "raw_best": raw_best["energy"],
                "strict_best": strict_best["energy"],
                "classes_seen": len(class_best),
                "signed_signatures_seen": len(signature_best),
                "generations": generation,
                "proposals": proposals_done,
                "moves_per_s": proposals_done / max(elapsed, 1e-9),
                "elapsed_s": elapsed,
            }
        ),
        flush=True,
    )
    return 0 if solved else 2


if __name__ == "__main__":
    raise SystemExit(main())
