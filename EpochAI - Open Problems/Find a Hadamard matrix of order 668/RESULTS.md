# Order-668 search status

No exact Hadamard matrix of order 668 has yet been found, so no CSV witness has
been emitted. Near-miss arrays are deliberately not represented as solutions.
The only success condition is exact residual zero followed by an independent
`H H^T = 668 I` integer check.

## Decisive symmetry-class closures (2026-07-22 session)

These are exact eliminations (CP-SAT INFEASIBLE or arithmetic impossibility),
not heuristic near-misses. Every encoder was validated on known-positive small
cases before its negatives were trusted.

- **GS/Z_167, QR-invariant class: empty.** 167 = 3 mod 4 makes QR(167) a
  (167,83,41) difference set, so all 8 QR-multiplier-invariant sequences have
  flat off-peak PAF in {167,-1,163}; none of the 330 quadruples sums to zero.
  Proof Search: `39f7a141-986a-4178-9909-671ae96dd01b`.
- **GS/Z_167, decimation-linked blocks: impossible.** Decimation preserves row
  sums, and 4s^2=668, 3s^2+t^2=668, s^2+t^2=334 have no odd solutions
  (334 = 6 mod 8), so no GS quadruple has 4, 3, or 2+2 decimation-equivalent
  blocks.
- **LP(333) multiplier pair fibers: all subgroups of order >= 12 are empty,**
  without any compression assumption. All 80 subgroups of Z_333^* enumerated;
  every fiber with <= 130 total bits decided INFEASIBLE (52+ fibers, incl. all
  order-12 classes up to 114 bits). Encoder validated by finding LP(9), LP(11)
  (QR-invariant), LP(13) and rejecting the flat full-group fiber. Artifact:
  `lp333_full_multiplier_sweep.jsonl`. Proof Search:
  `3fbbaaed-3f63-4952-9a26-00b3d499e31a`.
- **LP(333) decimation-paired fibers (b = a decimated), subgroup orders 6-9:
  all 285 (K,u) fibers INFEASIBLE.** Validated against exhaustive brute force
  at N=13 (witnesses matched for u=2,5,8). Artifact:
  `lp333_decimation_sweep.jsonl`. Proof Search:
  `be26c432-b4a5-457d-a103-9f85e106d752`.
- **NGP(334)/Ito route (negaperiodic Golay pair -> H(668)): all multiplier
  fibers of Z_668^* with <= 200 bits are empty** (six sigma-fixed classes die
  structurally; order-166 cyclic and order-83 fibers are INFEASIBLE). Encoder
  validated at M=20 (found NAF-verified NGP(10), free and {1,9}-invariant).
  Artifact: `ngp334_multiplier_sweep.jsonl`. Proof Search:
  `ba410a42-85fd-40fb-a0a6-099c63f3cb2c`.
- **<271> = Z_9 fiber: CLOSED via its 3-compression layer (2026-07-23).** Any
  <271>-invariant pair compresses to a <49>-invariant quaternary pair on Z_111
  with PAF sum -6; all 20,443,632 valid compressed candidates were enumerated
  and hash-joined: zero matches, layer EMPTY, fiber empty. Identity verified
  numerically; join machinery validated by planted-witness test and LP(9)
  positive control. Earlier: 1274/1355 sub-fibers INFEASIBLE by CP-SAT, 81
  resisted CP-SAT/Z3/annealer before the compression closure. Proof Search:
  `b45d4966-9bd7-489f-b96c-bf0fae36a7e8`. **Hence no LP(333) admits any
  multiplier subgroup of order 8, 9, or >= 12.**
- **Adversarial audits (2026-07-23):** the smallest 19 multiplier fibers were
  re-verified by direct enumeration independent of CP-SAT (including two
  nontrivial fibers with 768 and 840 valid candidates) - all agree INFEASIBLE;
  the exhaustive join recovered a planted witness pair; Z3 cross-checks of
  sampled affine INFEASIBLEs are running.
- **Group-LP over Z_3xZ_3xZ_37 (non-cyclic, new family):** 210 automorphism
  classes; 166 INFEASIBLE (all up to 114 bits outside the stall set); the 44
  UNKNOWN classes all have 37-part of order 9 or 6 - the same GF(37) cyclotomy
  hardness. Exhaustive meet-in-the-middle closed the smallest stalled fiber
  (25 orbits, 600,600 candidates, UNSAT in 31s after CP-SAT stalled at 4.8M
  conflicts); the <= 33-orbit stall set is being exhausted the same way.
  Construction validated end-to-end at H(20) (`build_hadamard_668_from_pair.py`
  self-test). Proof Search: `45328b0c-6879-41aa-95c9-463e83edae1f`.
- **ALL multiplier subgroups of order >= 4 CLOSED (2026-07-23).** The six
  order-6 fibers: <286>-type via CP-SAT lift of all 1,944 middle-layer
  profiles; <307>-type and <196>-type via complete GPU exhaustion of all 162
  profile classes each (scalar-hash pair-table decomposition, ~43M x 43M
  configs/class, 4-7 s/class, zero hits in 324 class-instances); the three
  order-3-image fibers via EMPTY Z_9 compression layers. Both order-4
  subgroups: {1,73,80,179} empty Z_9 layer; {1,73,154,253} GPU exhaustion of
  its Z_37 layer (90.9M candidates, 31 s). Proof Search:
  `af6366eb-35c0-4eb6-b687-70fbc07dbc02`. **Computational theorem: no LP(333)
  admits any multiplier subgroup of Z_333^* of order >= 4.**
- **No both-symmetric LP(333) exists (2026-07-23).** The Z_9 layer of the
  {1,332} (classical symmetric) class - symmetric sum-1 vectors, odd entries
  |<=37|, PAF pair -74 - is EMPTY: all 675,606 candidates exhausted, zero
  pairs, verified by two independent implementations with identity checks and
  planted-target controls. The {1,260} class dies by the same layer. Proof
  Search: `327ebb09-dccc-4380-a1b5-eddc78b2be26`.
- **Shared Z_37 layer of <10>/<121>/<211> completely enumerated (2026-07-23):
  NONEMPTY.** Under rigorous PSD caps (exact identity PSD_a+PSD_b=668):
  79,783,252 survivors from ~1.2e11 valid candidates, ~6.7M exact
  complementary pairs (21,454/21,454 sampled matches verified). The 1.1 GB
  shadow catalog `z37_order3_survivors.npz` is the complete constraint set
  any order-3-invariant witness must project into; the fibers stay open.
- **Group-333 family: ALL 210 classes CLOSED (2026-07-23).** 166 CP-SAT + 16
  MITM exhaustions + 10 empty Z_3^2 quotient layers + 12 GPU kB=6 layer
  exhaustions + the (M=I,u=7) fiber via its empty eigen-quotient middle layer
  (20.4M candidates - the structural twin of the <271> closure) + the final 8
  unipotent-M fibers via the unipotency obstruction (W-compression forces
  |c|=3 at the two degenerate orbits; zero of the 1,944 middle-layer profiles
  comply). No group-Legendre pair over Z_3 x Z_3 x Z_37 has any nontrivial
  cyclic automorphism symmetry with <= 60 orbits. Proof Search: `45328b0c`
  (completed).
- Remaining structured-open for LP(333): order-3 subgroups <10>, <121>,
  <211> (rich Z_37 layer), <112>, order-2 {1,73}, trivial class. NGP {1,333}
  class open (UNKNOWN at 900s CP-SAT).

## Proof Search provenance

- Problem version: `6bc65347-95ee-4649-acae-cb810b94fe96`
- Active frontier episode: `063b1204-2928-42ce-8a68-5cb29e6666ed`
- Active hybrid TT(56) search: `75bbf00b-eed3-4ceb-8b4a-47b8741a4ef8`
- Fixed-q special-Golay search: `0f01a072-50a6-44a7-8c1c-64de3c08226e`
- Variable-q / BS(84,83) search: `1c9ec6c1-64f4-4d98-8802-370b59bcd19e`
- BP2 higher-spectral search: `bc806aee-c272-4dd2-82fd-b041af16108b`
- Cyclic Goethals-Seidel search: `aeb5a99a-a02b-493d-92f0-d695611d7ffe`
- Williamson row-fiber search: `3083c807-853d-44e1-85c1-5acac165682a`
- LP(333) compression/uncompression search: `1aa1e29d-15f8-49f2-948d-a9777071a8fa`
- LP(333) literature lineages: `deb93bc6-aed5-4370-a703-3b96fd128e57`,
  `680f19a7-4c87-4125-bc64-8d735fb0a478`
- Earlier literature lineage: `fe4cda81-df5a-46d0-aa30-d8d962121219`

## Best reproducible bounds

- Cyclic Goethals-Seidel order 167, exact row tuple `[19,17,3,3]`:
  squared periodic residual `960`, L1 residual `200`, with 38 of 83 shifts
  already exact. Direct 55,444-XOR-variable CP-SAT searches at Hamming radii
  60, 100, and 200 returned `UNKNOWN`; a 56,112-variable native-cardinality
  SAT model is being tested around this checkpoint. An independent exhaustive
  repair audit checked 288,187,780 cross-row two-swap states and then used a
  lossless meet-in-the-middle hash to rule out an exact repair among about
  `2.308e15` zero-or-one-swap-per-row combinations.
- TT(56), original fixed-row-sum annealing: squared residual `320`.
- TT(56), unrestricted v3 search: squared residual `228`; its row-norm is
  `330`, versus the necessary `334`.
- TT(56), simultaneous exact `z=1` and `z=-1` margins: squared residual
  `360`. Exact native-cardinality SAT has ruled out every completion within
  ten bit changes of this checkpoint. Projecting to a compatible exact
  `z=i` fibre and enforcing all residual parities produced a stronger strict
  TT(56) checkpoint at energy `800`, L1 `144`, with 25 of 55 lags exact and
  all three weighted Fourier norms exactly `334`. Its artifact is
  `agent_btt_e800_verified.json` (SHA-256
  `4f15e7cf90f842be494da98d2e835dfc291d69213e78be5e9d2298060fde4a13`).
  Exact MiniCard has ruled out every completion within six bit changes of
  this strict checkpoint.
- Fixed-q special Golay length 167 with Eliahou's `q=(83,2,81,1)`:
  normalized squared residual `320`, exact necessary row sums, normalized L1
  residual `64`, and 14 nonzero even shifts.
- Variable-q special Golay, equivalently unrestricted BS(84,83): normalized
  squared residual `142`. This raw near-witness has total residual `2` and 50
  odd normalized residuals, so it is not represented as a solution.
- Exact-row BS(84,83), tuple `[-8,-6,-3,15]`: unscaled squared residual `568`.
- Exact-row-and-parity BS(84,83), tuple `[10,8,-1,-13]`: unscaled squared
  residual `928`, L1 residual `184`, with all 83 residuals divisible by four.
- Dual/Fourier-margin BS(84,83), same row tuple: unscaled squared residual
  `552`, L1 residual `164`, while the necessary norms at `z=1`, `z=-1`, and
  `z=i` are all exactly `334`. This stronger raw near-state still has 34
  residuals congruent to two modulo four, so it is not an exact-parity witness.
- Free parity-manifold BS(84,83): unscaled squared residual `736`, L1 residual
  `160`, and all 83 residuals divisible by four. Its row and alternating
  square norms are both `366` rather than `334`, so this is a search frontier,
  not a witness.
- Strict Fourier/parity BS(84,83), row tuple `[12,10,3,9]`: unscaled squared
  residual `896`, L1 residual `184`, all 83 residuals divisible by four, and
  the necessary square norms at `z=1`, `z=-1`, and `z=i` all exactly `334`.
  Its exact order-3 and order-5 compression targets are each only L1 distance
  four away. Exact native-cardinality SAT has ruled out every completion
  within six bit changes of this checkpoint; the radius-eight shell is active.
  At the E2144 exact-order-1-through-5 checkpoint, all six aggregate order-7
  targets in the exhaustive nearest L1-radius-8 shell fail the exact GF(2)
  parity/margin subsystem. At the E3648 exact-order-1-through-7 checkpoint,
  the nearest order-11 L1-radius-16 shell has five aggregate targets: four
  fail GF(2), and the sole survivor is integer-infeasible by CP-SAT. These are
  finite-shell exclusions only, not nonexistence results for BS(84,83).
- Alternate exact-row-and-parity BS(84,83), tuple `[6,8,-3,-15]`: unscaled
  squared residual `1056`.
- Williamson order 167, exact row tuple `[-5,3,-25,-3]`: squared periodic
  residual `4896`.
- Repeated-block cyclic GS `[A,B,B,D]`, row sums `[3,17,17,9]`: squared
  periodic residual `1344`.
- LP(333) quadratic-character 37-compression: exact residual `0`. Its two
  compressed sequences are `d_A(0)=d_B(0)=1`, `d_A(r)=3 chi_37(r)`, and
  `d_B(r)=-3 chi_37(r)` for nonzero `r`. This is an exact compression only,
  not yet a binary LP(333) or Hadamard witness. Fixed-compression native
  uncompression has reached squared full PAF residual `6496`.
- LP(333) length-9 compression: exact residual `0`, combined squared norm
  `594`, and combined periodic PAF `-74` at all eight nonzero shifts. Eight
  distinct exact length-9 compression pairs have been generated. With both
  the length-37 and length-9 CRT margins fixed, native uncompression has
  reached squared full PAF residual `9376`. These are still compressed or
  near-miss objects, not a full Legendre pair.

## Fixed-q structural reduction

The published 64-modular approximation has the form `(s, s*f, s*q, s*q*f)`.
Its exact search initially has 167 signs and 82 nontrivial shifts. Gaussian
analysis gives a rank-82 parity system with a complete local nullspace basis:
82 mirrored-pair flips and three center flips. Inside this affine space all 41
odd shifts vanish automatically. Cancelling complementary XOR terms leaves 40
exact correlation equations on 85 generator bits. The norm identity and the
three negative positions of `q` reduce the possible half-row-sum tuples to
eight.

Independent 900-second Z3, CP-SAT satisfaction, and CP-SAT L1-optimization
runs terminated without a zero-residual witness or an impossibility proof. A
compact CDCL model uses 5,134 variables, 13,464 ordinary clauses, and 86 native
cardinality constraints. Three 900-second MiniCard fibers each processed
15–17 million conflicts and returned UNKNOWN. Native fixed-q campaigns tested
more than 1.6 billion row-valid moves without improving `320`.

## Broader variable-q / base-sequence route

Allowing `q` to vary makes `t=s*q` independent, so `(s,s*f,s*q,s*q*f)` is
exactly a reparameterization of base sequences BS(84,83). Incremental native
updates reduced normalized energy from `320` to `187` in a five-second smoke
run and then to `142`. A companion rank objective explicitly penalizes the
row-identity defect and every odd normalized residual; a strengthened
parity-kernel BS search uses L1 breakout and direct reversal-orbit moves that
preserve both the row tuple and all residuals modulo four.

## Additional periodic routes

A native cyclic Goethals-Seidel search covers arbitrary four-sequence
supplementary difference families on `Z_167`, not just aperiodic Golay or
Williamson quadruples. A separate Williamson engine fixes the necessary odd
row-sum square decomposition before searching. Mixed skew/symmetric families
are also represented, including a product-theorem fiber with one skew and
three symmetric sequences; after normalization it enforces
`a_k b_k c_k d_k = -a_(2k)` and derives the fourth sequence from the first
three. These are experimental construction searches, not proofs.

A July 2026 audit of the public `renaissancefieldlite/Hadamard_Proof` worktree
found no exact witness. Its reported GS floor has doubled-shift score `2496`,
equivalent to squared half-shift energy `1248`; the incumbent here has scores
`1920` and `960` respectively. Re-running that repository's bounded PB/ILP
ring on the stronger incumbent reduced selected focus defects but leaked to a
worse global score (`3456`). Recent one-seed social-media claims were also
rejected structurally: making all four circulant blocks reversal/sign
transforms of a single block forces an impossible odd-order Hadamard condition.

## Legendre-pair uncompression route

A binary Legendre pair of length 333 yields a Hadamard matrix of order
`2*(333+1)=668`. The quadratic character modulo 37 gives an exact prescribed
37-compression:

```
d_A(0)=d_B(0)=1,
d_A(r)= 3 chi_37(r),
d_B(r)=-3 chi_37(r)  (r != 0).
```

The identity `sum_r chi(r) chi(r+h) = -1` makes the combined compressed PAF
exactly `-18` at all 18 independent nonzero shifts. This construction was
independently derived here and then identified with the 2026 `q^2`-uncompression
conjecture for `(p,q)=(37,3)` in Kotsireas--Gallardo-Cava--Gomez--Gomez-Perez.
An exact length-9 compression was also found. The first pair is
`[-5,1,-3,-7,3,-7,17,5,-3]` and
`[-1,-3,3,5,-1,-3,7,-1,-5]`; its combined square norm is `594` and combined
periodic PAF is exactly `-74` at every nonzero shift. The remaining problem is
therefore searched as two binary `37 x 9` CRT arrays with both their row and
column sums fixed and combined full PAF `-2` at all 166 shifts. A 2-by-2 switch
preserves all of these margins.

Three independent searches cover that remaining layer: native dual-margin
annealing with 2-by-2 and compound switches, a 111,222-variable MiniCard model
with 516 native cardinality constraints, and a CP-SAT exact local-neighborhood
model with the same 92 row/column equalities. All persisted states are
recomputed with integer periodic correlations.

An additional exact model imposes cyclic multiplier invariance under the
order-6, 9, 12, or 18 subgroups of the mod-3 kernel in `Z_333^*`. It enumerates
14 distinct cyclic subgroup classes. Ten classes were proved infeasible by
CP-SAT; the remaining four (represented by generators 271, 307, 286, and 196)
were still `UNKNOWN` after 120 seconds per class. This eliminates structured
fibers only and is not a nonexistence proof for LP(333).

The two best strict BS checkpoints also feed exact CP-SAT large-neighborhood
models. Reversal-orbit flips preserve residual parity; four linear row-balance
equations describe every row-preserving subset of 166 orbit flips. Since the
correlations are quadratic, only 1,649 within-sequence interaction variables
are needed, versus 14,112 variables in the global MiniCard model.

`build_hadamard_668.py` is the final strict gate: given a zero-residual Golay,
BS(84,83), Williamson, or cyclic Goethals-Seidel quadruple, it independently
checks the defining correlations, constructs the matrix, verifies every entry
and the complete 668-by-668 Gram matrix, then writes and hashes
`hadamard_668.csv`.
