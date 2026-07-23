"""CUDA genetic search over the exact 85-bit special-Golay quotient.

The GPU evaluates integer-valued quadratic correlations in float32 (all values
are far below the exact-integer limit).  Every improving candidate is rebuilt
and checked with Python integer arithmetic before it is persisted.
"""

from __future__ import annotations

import argparse
import json
import time
from pathlib import Path

import torch


def expand(runs: list[int]) -> list[int]:
    return [1 if j % 2 == 0 else -1 for j, n in enumerate(runs) for _ in range(n)]


Q = expand([83, 2, 81, 1])
F = [1] * 84 + [-1] * 83


def exact(s: list[int]) -> list[int]:
    return [sum(s[i] * s[i + d] for i in range(167 - d)
                if F[i] == F[i + d] and Q[i] == Q[i + d])
            for d in range(1, 84)]


def main() -> int:
    p = argparse.ArgumentParser()
    p.add_argument("--seconds", type=float, default=900)
    p.add_argument("--batch", type=int, default=8192)
    p.add_argument("--elite", type=int, default=256)
    p.add_argument("--seed", type=int, default=668)
    p.add_argument("--input", type=Path, default=Path(
        "Find a Hadamard matrix of order 668/special_golay_167_live.json"))
    p.add_argument("--output", type=Path, default=Path(
        "Find a Hadamard matrix of order 668/special_golay_167_genetic_live.json"))
    a = p.parse_args()
    if not torch.cuda.is_available():
        raise RuntimeError("CUDA unavailable")
    torch.manual_seed(a.seed)
    torch.cuda.manual_seed_all(a.seed)
    base = json.loads(a.input.read_text(encoding="utf-8"))["s"]

    group = [-1] * 167
    g = 0
    for i in range(41):
        group[i] = group[82 - i] = g; g += 1
    for i in range(41):
        group[84 + i] = group[166 - i] = g; g += 1
    for i in (41, 83, 125):
        group[i] = g; g += 1
    assert g == 85

    # r_d = fixed_d + sum_(g<h) coefficient[g,h,d] x_g*x_h.
    coefficients: dict[tuple[int, int], list[int]] = {}
    fixed = [0] * 83
    for d in range(1, 84):
        for i in range(167 - d):
            j = i + d
            if F[i] != F[j] or Q[i] != Q[j]:
                continue
            c = base[i] * base[j]
            x, y = group[i], group[j]
            if x == y:
                fixed[d - 1] += c
            else:
                if x > y: x, y = y, x
                coefficients.setdefault((x, y), [0] * 83)[d - 1] += c
    pairs = list(coefficients)
    device = "cuda"
    left = torch.tensor([x for x, _ in pairs], device=device, dtype=torch.long)
    right = torch.tensor([y for _, y in pairs], device=device, dtype=torch.long)
    matrix = torch.tensor([coefficients[p] for p in pairs], device=device, dtype=torch.float32)
    fixed_t = torch.tensor(fixed, device=device, dtype=torch.float32)
    base_t = torch.tensor(base, device=device, dtype=torch.int8)
    group_t = torch.tensor(group, device=device, dtype=torch.long)

    pop = torch.where(torch.rand((a.batch, 85), device=device) < .5, -1, 1).to(torch.int8)
    pop[0].fill_(1)
    best_valid_energy = sum(x*x for x in exact(base))
    best = base[:]
    started = time.time()
    generation = 0

    def evaluate(x: torch.Tensor) -> tuple[torch.Tensor, torch.Tensor, torch.Tensor]:
        products = (x[:, left] * x[:, right]).float()
        residual = products @ matrix + fixed_t
        energy = (residual * residual).sum(dim=1)
        total = residual.sum(dim=1)
        # total=0 is exactly the necessary row-norm identity.
        fitness = energy + 4.0 * total * total
        return fitness, energy, residual

    while time.time() - started < a.seconds:
        fitness, energy, residual = evaluate(pop)
        values, indices = torch.topk(fitness, k=a.elite, largest=False, sorted=True)
        elites = pop[indices].clone()
        totals = residual[indices].sum(dim=1)
        valid_mask = totals == 0
        if bool(valid_mask.any()):
            valid_positions = torch.nonzero(valid_mask, as_tuple=False).flatten()
            valid_energies = energy[indices][valid_positions]
            value, local_index = valid_energies.min(dim=0)
            candidate_energy = int(value.item())
            if candidate_energy < best_valid_energy:
                candidate = elites[valid_positions[int(local_index.item())]]
                signs = (base_t * candidate[group_t]).cpu().tolist()
                rr = exact(signs)
                checked = sum(x*x for x in rr)
                if checked != candidate_energy or sum(rr) != 0:
                    raise RuntimeError((checked, candidate_energy, sum(rr)))
                best_valid_energy, best = checked, signs
                payload = {"construction": "special Golay quadruple length 167",
                    "solver": "CUDA discrete genetic search", "solved": checked == 0,
                    "energy_normalized": checked, "generation": generation,
                    "elapsed_s": time.time() - started,
                    "residual_divided_by_4": rr, "s": signs}
                a.output.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
                print(json.dumps({"event": "best", "energy": checked,
                    "generation": generation, "elapsed_s": time.time() - started}), flush=True)
                if checked == 0:
                    return 0

        # Massively parallel annealing.  Each chain proposes a nearby state and
        # can accept uphill moves; cyclic reheating prevents the whole GPU batch
        # from collapsing into the incumbent's strict local basin.
        proposal = pop.clone()
        quarter = a.batch // 4
        rates = (1.0/85, 2.0/85, 4.0/85, 8.0/85)
        for block, rate in enumerate(rates):
            lo = block * quarter
            hi = a.batch if block == 3 else (block + 1) * quarter
            mutate = torch.rand((hi - lo, 85), device=device) < rate
            proposal[lo:hi] = torch.where(mutate, -proposal[lo:hi], proposal[lo:hi])
        # Sparse cross-chain exchanges make coordinated jumps.
        cross = torch.rand((a.batch, 85), device=device) < 0.02
        mates = pop[torch.randperm(a.batch, device=device)]
        proposal = torch.where(cross, mates, proposal)
        proposed_fitness, _, _ = evaluate(proposal)
        phase = (generation % 2000) / 2000.0
        temperature = 1600.0 * (0.001 ** phase) + 0.5
        delta = proposed_fitness - fitness
        accept = (delta <= 0) | (torch.rand(a.batch, device=device) < torch.exp(-delta / temperature))
        pop = torch.where(accept[:, None], proposal, pop)
        # Periodic immigrants and kicked incumbents preserve global diversity.
        if generation % 500 == 499:
            n = a.batch // 8
            pop[-n:] = torch.where(torch.rand((n, 85), device=device) < .5, -1, 1).to(torch.int8)
            kicks = torch.rand((n, 85), device=device) < 0.12
            pop[-2*n:-n] = torch.where(kicks, -torch.ones_like(pop[-2*n:-n]), torch.ones_like(pop[-2*n:-n]))
        generation += 1
        if generation % 500 == 0:
            torch.cuda.synchronize()
            print(json.dumps({"event": "progress", "generation": generation,
                "best_fitness": int(values[0].item()),
                "best_valid_energy": best_valid_energy,
                "elapsed_s": time.time() - started}), flush=True)

    print(json.dumps({"event": "result", "solved": best_valid_energy == 0,
        "energy": best_valid_energy, "generations": generation,
        "elapsed_s": time.time() - started, "output": str(a.output)}), flush=True)
    return 0 if best_valid_energy == 0 else 2


if __name__ == "__main__":
    raise SystemExit(main())
