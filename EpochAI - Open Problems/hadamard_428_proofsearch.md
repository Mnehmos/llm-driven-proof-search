# Hadamard matrix of order 428

- CSV: `hadamard_428.csv`
- CSV SHA-256: `079a2609735a218cdbccfed5070d524f9163a59f8557633f4fe8e864d57b3f87`
- Proof Search problem version: `e796befa-440d-44e2-a07e-1442abe25a4e`
- Proof Search episode: `5fdccf50-ce15-417a-95c7-26d4c7926721`
- Proof Search outcome: `kernel_verified`
- Lean environment: `9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d`

The tracked theorem proves that an explicitly defined function
`H : Fin 428 → Fin 428 → Int` has only entries `-1` and `1`, and that
every row inner product is `428` on the diagonal and `0` off the diagonal.


## Seed provenance and attribution (PR #265 review, blocker 6)

The generator's `TURYN_HEX` constant packs a ±1 quadruple X, Y, Z, W of
lengths (36, 36, 36, 35). This is the Turyn-type sequence family used in the
first published Hadamard matrix of order 428:

> H. Kharaghani and B. Tayfeh-Rezaie, *A Hadamard matrix of order 428*,
> Journal of Combinatorial Designs **13** (2005), no. 6, 435–440.

Their construction runs Turyn-type T(36,36,36,35) → T-sequences of length
107 → Goethals–Seidel array → H(428), which is exactly the pipeline
implemented in `generate_hadamard_428.js`. The sequence data itself is
mathematical fact (not subject to copyright); attribution for the discovery
of this sequence family and the order-428 construction belongs to the paper
above.

**The certificate chain does not rely on trusting the transcription.**
`verify_turyn_seed.py` independently checks the defining Turyn-type
identity N_X(s) + N_Y(s) + 2N_Z(s) + 2N_W(s) = 0 at every shift
(PASS), the generator verifies the full 428×428 Gram matrix before writing
the CSV, and the tracked Proof Search episode kernel-verifies the matrix
property from the committed entries. A transcription differing from the
published table could therefore only produce a *different valid* Turyn-type
quadruple, never a false certificate.
