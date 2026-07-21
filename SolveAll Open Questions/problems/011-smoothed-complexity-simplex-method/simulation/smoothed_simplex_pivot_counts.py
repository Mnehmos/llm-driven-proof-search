#!/usr/bin/env python3
"""Monte Carlo pivot-count experiment for smoothed simplex (SolveAll #11).

NON-RIGOROUS. This is illustrative simulation evidence only -- it proves
nothing and is entirely separate from the kernel-verified Lean layer in
../proof/. See ../whitepaper.md and README.md in this directory for the
evidence-layering rationale (mirrors the three-layer convention used in
F:\\Github\\Benjamini-Hochberg Procedure: rigorous certificate / Monte Carlo
simulation / Lean formalization, each labeled by what it actually establishes).

Modeling choices / deviations from the problem's literal setup (documented,
not hidden):

  1. The problem's Sm_R sup is over an ADVERSARIAL choice of (Abar,bbar,cbar)
     with norm <= 1. Brute-force worst-case search over that adversarial
     choice is intractable; this script instead samples "typical" random
     base instances (a standard practice in this literature's own
     experimental sections), so it CANNOT and does not claim to approximate
     the actual Sm_R(m,n,sigma) supremum -- only illustrates how pivot
     counts behave under Gaussian smoothing on typical instances.
  2. The problem allows a general polyhedron {x : Ax <= b} with no
     nonnegativity constraint on x. This script uses the standard textbook
     restriction x >= 0 (max c^T x s.t. Ax <= b, x >= 0) for a clean,
     well-defined slack-variable simplex tableau. This is the most common
     convention in pedagogical and experimental treatments of pivot
     counting, but it is a real restriction of the problem's actual scope.
  3. Pivot rule R is fixed and fully specified: entering variable by
     Dantzig's rule (most positive reduced cost, first index on ties),
     leaving variable by the standard min-ratio test (first index on ties --
     Bland's-rule-style tie-break, which prevents cycling on ties but does
     NOT by itself give a full anti-cycling guarantee under Dantzig entering
     -- an iteration cap catches any non-terminating run and reports it
     honestly rather than hanging).
  4. Phase 1 (infeasible start) is not implemented. b is constructed as
     bbar = ones(m) (so x=0 is feasible for the *unperturbed* instance);
     trials where Gaussian noise pushes some b_i < 0 (origin infeasible)
     are skipped and counted separately, not silently dropped.
"""
import numpy as np
import csv
import sys

ITER_CAP = 20_000


def make_base_instance(rng, m, n):
    """Sample the base instance (Abar, bbar, cbar).

    DEVIATION (documented): the problem's adversary constraint is
    ||(Abar,bbar,cbar)|| <= 1 on the whole stacked triple. Normalizing the
    triple that way crushes bbar to ~1/||.|| (tiny for large m), so ANY
    non-tiny Gaussian noise pushes some b_i < 0 and the origin becomes
    infeasible -- an artifact of the norm ball, not of the pivot-count
    phenomenon we want to see. To keep the origin feasible with a real
    margin (so a phase-1 is unnecessary and more sigma values yield data),
    we instead:
      - normalize Abar to Frobenius norm 1 and cbar to Euclidean norm 1
        (each individually within the unit ball), and
      - anchor bbar = ones(m) (margin 1 per constraint).
    This does NOT satisfy ||(Abar,bbar,cbar)|| <= 1 literally (||bbar|| = sqrt(m)),
    so the numbers here are illustrative of typical-instance behavior only and
    are explicitly NOT an estimate of the problem's Sm_R supremum. The
    kernel-verified Lean layer (../proof/) is the rigorous content; this is not.
    """
    A = rng.standard_normal((m, n))
    A = A / np.sqrt(np.sum(A ** 2))
    b = np.ones(m)
    c = rng.standard_normal(n)
    c = c / np.sqrt(np.sum(c ** 2))
    return A, b, c


def simplex_pivot_count(A, b, c, iter_cap=ITER_CAP):
    """Textbook dense primal simplex, standard form max c^T x s.t. Ax + s = b,
    x,s >= 0, starting basis = slacks (requires b >= 0 -- caller must check).
    Dantzig entering rule, min-ratio leaving rule, first-index tie-breaks.
    Returns (pivot_count, status) with status in
    {"optimal", "unbounded", "iter_cap_exceeded"}.
    """
    m, n = A.shape
    # Tableau: rows = constraints, columns = [x_1..x_n, s_1..s_m, RHS]
    T = np.zeros((m + 1, n + m + 1))
    T[:m, :n] = A
    T[:m, n:n + m] = np.eye(m)
    T[:m, -1] = b
    T[-1, :n] = -c  # objective row: maximize c^T x  <=>  minimize -c^T x
    basis = list(range(n, n + m))

    pivots = 0
    while pivots < iter_cap:
        obj_row = T[-1, :-1]
        entering_candidates = np.where(obj_row < -1e-10)[0]
        if entering_candidates.size == 0:
            return pivots, "optimal"
        # Dantzig entering rule: most negative reduced cost (argmin over
        # candidates returns the first index on ties).
        entering = entering_candidates[np.argmin(obj_row[entering_candidates])]

        col = T[:m, entering]
        ratios = np.full(m, np.inf)
        positive = col > 1e-10
        ratios[positive] = T[:m, -1][positive] / col[positive]
        if not np.any(positive):
            return pivots, "unbounded"
        leaving_row = int(np.argmin(ratios))

        pivot_val = T[leaving_row, entering]
        T[leaving_row, :] /= pivot_val
        for r in range(m + 1):
            if r != leaving_row and abs(T[r, entering]) > 1e-14:
                T[r, :] -= T[r, entering] * T[leaving_row, :]
        basis[leaving_row] = entering
        pivots += 1

    return pivots, "iter_cap_exceeded"


def run_experiment(sizes, sigmas, trials_per_cell, seed=20260717):
    rng = np.random.default_rng(seed)
    rows = []
    for (n, m) in sizes:
        for sigma in sigmas:
            counts = []
            infeasible_skips = 0
            anomalies = 0
            for _ in range(trials_per_cell):
                Abar, bbar, cbar = make_base_instance(rng, m, n)
                G = rng.normal(0.0, sigma, size=(m, n))
                h = rng.normal(0.0, sigma, size=m)
                g = rng.normal(0.0, sigma, size=n)
                A, b, c = Abar + G, bbar + h, cbar + g
                if np.any(b < 0):
                    infeasible_skips += 1
                    continue
                pivots, status = simplex_pivot_count(A, b, c)
                if status == "iter_cap_exceeded":
                    anomalies += 1
                    continue
                counts.append(pivots)
            if counts:
                mean_pivots = float(np.mean(counts))
                std_pivots = float(np.std(counts))
            else:
                mean_pivots = float("nan")
                std_pivots = float("nan")
            rows.append({
                "n": n, "m": m, "sigma": sigma,
                "trials": trials_per_cell,
                "feasible_trials": len(counts),
                "infeasible_skips": infeasible_skips,
                "iter_cap_anomalies": anomalies,
                "mean_pivots": mean_pivots,
                "std_pivots": std_pivots,
            })
            print(f"n={n:3d} m={m:3d} sigma={sigma:<8g} "
                  f"mean_pivots={mean_pivots:8.3f} std={std_pivots:7.3f} "
                  f"feasible={len(counts)}/{trials_per_cell} "
                  f"anomalies={anomalies}", file=sys.stderr)
    return rows


if __name__ == "__main__":
    sizes = [(5, 10), (10, 20), (20, 40)]
    sigmas = [1.0, 0.3, 0.1, 0.03, 0.01]
    trials = 200

    rows = run_experiment(sizes, sigmas, trials)

    out_path = "smoothed_simplex_pivot_counts_results.csv"
    with open(out_path, "w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)
    print(f"wrote {out_path}", file=sys.stderr)
