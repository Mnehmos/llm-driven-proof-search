# Agent GS/spectral campaign summary

No exact cyclic GS(167) family was found.  Every retained candidate was
independently recomputed over all 83 nonzero shifts; all have four length-167
rows, alphabet `{+1,-1}`, and row-sum-square total 668.

## General GS frontiers

- The existing `(19,17,3,3)` frontier remains `E=960, L1=200, nz=45,
  maxabs=8`.  Weighted spectral replica exchange (45,940,736 proposals),
  Douglas--Rachford projection (91,783,168 projections), and independent-row
  coevolution (72,351,744 combinations) did not improve it.
- Previously omitted row-sum fibre `(21,13,7,3)` reached `E=1664, L1=280,
  nz=55, maxabs=12` after 210,804,736 GPU states.
- Previously omitted row-sum fibre `(21,11,9,5)` reached `E=1856, L1=304,
  nz=58, maxabs=12` after 93,208,576 GPU states.
- Seven exact randomized disjoint-swap quadratic CP-SAT neighborhoods around
  the 960 state were bounded `UNKNOWN` (313 move variables and 12,118
  quadratic auxiliaries per round; 420.075 solver-seconds; 1,777,987
  branches).  This is empirical only, not an infeasibility result.

## Two-Paley / D-optimal reduction

The fibre `(21,15,1,1)` reduces, after fixing both sum-one rows to Paley, to
the open cyclic SDS parameter set `(167;73,76;66)`.  See
`agent_gspec_two_paley_reduction.md` for the derivation and literature source.

- Best unconstrained two-block state: `E=1664, L1=272, nz=53, maxabs=12`,
  but it violates the necessary individual PSD cap at 9 positive frequencies.
- PSD-aware annealing found a fully cap-feasible state and hard-cap annealing
  reduced it to `E=2144, L1=336, nz=61, maxabs=12`.  Both variable sequences
  satisfy `PSD(j) <= 332` at every nonzero frequency.  SHA-256 of
  `agent_gspec_pair_hardcap_summary.json`:
  `a2e9714507dc1590eede2d08ae6b93a852e2f8fdc1f7ebdf5d9ce6edacb285f8`.
- Exhaustive evaluation found only 53 cap-feasible balanced single swaps from
  this state; the best has energy 2176.  All compatible pairs among those 53
  and 2,000,000 sampled compatible triples gave no improvement.
- The mixed symmetric/skew restriction (two symmetric variable rows and two
  Paley rows) reached only `E=6144` heuristically.

## Exact SAT handoff

The following MiniCard jobs were left active for the root campaign:

- reduced one-Paley 3-row model: 501 primary bits, 41,583 XOR auxiliaries,
  conflict budget 5,000,000;
- unrestricted two-Paley SDS model: 334 primary bits, 27,722 XOR auxiliaries,
  conflict budget 5,000,000;
- two-Paley mixed-symmetry model: 166 primary bits, conflict budget 20,000,000;
- radius-120 two-Paley repair around the cap-feasible state, conflict budget
  3,000,000.

No `agent_gspec_*candidate.json` existed at the time of this audit.
