# The Jacobian Conjecture Is False: A Machine-Certified Refutation

**Release date:** July 20, 2026
**Verification environment:** LLM-Driven Proof Search Environment (pinned Lean 4 + Mathlib kernel, environment hash `9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d`)
**Status of the mathematics:** the counterexample was announced by Levent Alpöge on July 19, 2026; its algebraic verification, global geometry, and families are developed in P. Chojecki, *A Counterexample to the Jacobian Conjecture* (ulam.ai research write-up, July 20, 2026; `jacobian.pdf`), with the families generalization credited therein to GPT-5.6 Pro. Community peer review is ongoing. Every formal claim in this release is machine-checked; the *informal* claims of the paper beyond them are not.

---

## 1. What happened

The Jacobian Conjecture (Keller, 1939) asserts that every polynomial map F : ℂⁿ → ℂⁿ whose Jacobian determinant is a nonzero constant — a *Keller map* — is a polynomial automorphism. It has been open for 87 years, was listed by Smale among his problems for the 21st century, and has an enormous literature of partial results and reductions.

On July 19, 2026, Levent Alpöge posted an explicit map (crediting Akhil Mathew for the question and the AI model Fable for the work leading to the example):

```
F(x, y, z) = ( (1+xy)³·z + y²(1+xy)(4+3xy),
               y + 3x(1+xy)²·z + 3xy²(4+3xy),
               2x − 3x²y − x³z )
```

The claim: **det Jac F ≡ −2** (a nonzero constant, so F is a Keller map), yet F sends the three distinct points

```
(0, 0, −1/4),   (1, −3/2, 13/2),   (−1, 3/2, 13/2)
```

to the *same* image (−1/4, 0, 0). A Keller map with a collapsed fiber cannot be an automorphism — or injective at all. If correct, the Jacobian Conjecture is false in dimension 3, and by stabilization in every dimension n ≥ 3.

This release contains a **formal, kernel-checked verification** of the counterexample's defining properties *and* a formal refutation of the Jacobian Conjecture exactly as it had been formalized — before this event — in Google DeepMind's `formal-conjectures` benchmark repository.

## 2. What is formally proved

Six theorems were verified through the LLM-Driven Proof Search Environment, a verifier-backed proof environment in which the only path to a "proved" status runs through a pinned Lean 4 + Mathlib kernel, and in which statement fidelity is tracked by hash-checked review records. Five of the six carry the environment's highest trust level, `certified` (kernel-verified proof **and** verified statement-fidelity review); the first carries `kernel_verified` (its review used the environment's dev-attestation path).

| # | Statement | Field | Outcome |
|---|-----------|-------|---------|
| 1 | det Jac F = C(−2) as a symbolic `MvPolynomial` identity, **and** F's evaluation collapses all three points to (−1/4, 0, 0) | ℚ | `kernel_verified` |
| 2 | ¬(every Keller map `Fin 3 → MvPolynomial (Fin 3) ℂ` has a two-sided compositional polynomial inverse) — the negation of `formal-conjectures`' `jacobian_conjecture` at k = ℂ, σ = Fin 3 | ℂ | **`certified`** |
| 3 | The evaluation map of F on ℂ³ is not injective | ℂ | **`certified`** |
| 4 | The dimension-4 statement is also false (stabilization: append w as a fourth component) | ℂ | **`certified`** |
| 5 | The normalized map U = (R/2, Q, P) has det = 1, U(0) = 0, JU(0) = I, and a three-point fiber over its fixed point (0,0,−1/4) (paper Cor. 3.2) | ℂ | **`certified`** |
| 6 | The Poisson-bridge core: J·B = −2·I plus all 27 commuting-derivation identities for the explicit inverse Jacobian B — the complete polynomial content of the rank-3 canonical Poisson counterexample | ℂ | **`certified`** |

Precise statements are in `Challenge.lean`; kernel-accepted proofs are transcribed verbatim in `ChallengeSolved.lean`; episode identifiers and hashes are in `README.md`.

Theorem 2 deserves emphasis. It is not a paraphrase: the refuted statement is the ∀-body of the theorem `jacobian_conjecture` in `FormalConjectures/Wikipedia/JacobianConjecture.lean` (tagged `research open`, AMS 14), with that file's four definitions (`RegularFunction`, `Jacobian`, `comp`, `id`) unfolded definitionally and the type parameters instantiated at ℂ and `Fin 3`. Since their theorem quantifies over every characteristic-zero field and every finite index type, a single refuted instance refutes the formalized conjecture. The definitional mapping is recorded line-by-line in the fidelity review (`1505a59d`).

## 3. How the refutation works

The mathematical mechanism (following the paper, §3): write A = 1 + xy and B = A²z + y²(4+3xy). Then F = (AB, y + 3xB, 2x − 3x²y − x³z), and in the coordinates (P, y, s) with s = x/A the map factors through a triangular change of variables with Jacobian factors −A and 2/A, whose product is the constant −2. The fiber over (p, q, r) is governed by the binary cubic 2pS³ − qS²T + 2ST² − rT³: affine preimages are exactly its *simple* projective roots. Over the target (−1/4, 0, 0) the cubic factors as −s(s−2)(s+2)/2, whose three simple roots pull back to the three witness points. The map has generic degree 3, image ℂ³ ∖ Γ for an explicit smooth curve Γ ≅ ℂ*, and nonproperness set the discriminant hypersurface — it is a *nonproper* Keller map, which is precisely the global behavior the conjecture forbade.

The formal proof needs none of that geometry — only its two computable consequences:

1. **Determinant.** The 3×3 Jacobian matrix of formal partial derivatives (`MvPolynomial.pderiv`) has determinant the constant polynomial −2. In Lean this is a finite symbolic computation: expand `Matrix.det_fin_three`, eliminate every `pderiv` node with the derivation rules (Leibniz, power rule, `pderiv_X`), fold constants, close with `ring`. The kernel checks every step; there is no numerical approximation anywhere.
2. **Collision.** Two of the witness points already refute injectivity. If G were a two-sided compositional inverse (`bind₁ F (G i) = X i`), evaluating at any point p and rewriting with `aeval_bind₁` yields the retraction identity `aeval (F(p)) (G i) = p i`. Applying it at both witness points — whose F-images are *equal*, by a rational-arithmetic check `norm_num` performs exactly — forces 0 = 1 in ℂ. Contradiction. Note the proof *consumes* the distinctness of the points (their first coordinates 0 and 1); nothing about distinctness is assumed.

Dimension 4 (theorem 4) stabilizes the witness to (F₁, F₂, F₃, w): the Jacobian becomes block-triangular with determinant (−2)·1, computed by cofactor expansion along the appended row, and the same collision argument applies with fourth coordinates 0. The paper's stabilization extends this to every n ≥ 3; the formal release certifies n = 3 and n = 4.

## 4. Collateral damage

A conjecture open for 87 years accumulates a web of implications. Refuting it snaps every thread that pointed *toward* it. Known consequences, with their bridge theorems:

- **Dixmier conjecture, Aₙ for n ≥ 3.** The Dixmier conjecture (every endomorphism of the Weyl algebra Aₙ(ℂ) is an automorphism) *implies* the Jacobian conjecture in the same dimension (van den Essen, Prop. 10.2.7). Contrapositive: the Dixmier conjecture is false for A₃ — and for every Aₙ, n ≥ 3. (The celebrated Tsuchimoto / Belov-Kanel–Kontsevich direction JC₂ₙ ⟹ DCₙ now transmits nothing; the damage flows through the easy direction.)
- **Mathieu's conjecture** (1995) on G-finite functions on compact connected Lie groups implies the Jacobian conjecture; it is therefore false.
- **Zhao's vanishing conjecture** (2007) for the Laplace operator is equivalent to the Jacobian conjecture; it is therefore false.
- **Cubic-homogeneous reduction** (Bass–Connell–Wright 1982, Drużkowski): the Jacobian conjecture in all dimensions reduces to maps of the form X + H with H cubic homogeneous. Contrapositive: some higher dimension contains a cubic-homogeneous Keller counterexample.

`CollateralDamage.lean` formalizes this graph honestly: the Weyl algebra, the Dixmier statement, Zhao's vanishing statement, and the cubic-homogeneous statement are *defined*; the certified dimension-3 refutation is included in full; and each collateral refutation is proved **sorry-free as a conditional theorem** taking its literature bridge as an explicit hypothesis. The bridges themselves are stated with `sorry` and full citations — each is a serious formalization project (the associated-graded argument for Dixmier⟹Jacobian, Zhao's Hessian-nilpotency equivalence, the BCW degree reduction), and this release does not pretend otherwise. Mathieu's conjecture is documented in prose only: current Mathlib lacks the representation-theoretic vocabulary to state it faithfully.

## 5. What "certified" does and does not mean

**It means:** the pinned Lean 4 kernel accepted a complete proof term for the exact stated proposition, through a tracked attempt path that recorded every failed attempt and diagnostic; and a hash-checked fidelity review attests that the formal statement represents its source. The full attempt ledger (5 failures, 4 successes across the campaign) is replayable inside the environment.

**It does not mean:** that the informal Jacobian Conjecture of the literature is settled by machine. Three honest gaps remain. (a) The identification of Keller's 1939 conjecture with the `formal-conjectures` statement is that repository's formalization decision — a widely reviewed one, but a human decision. (b) The paper's broader geometry (fiber structure, image, nonproperness set, families of every generic degree) is *not* formalized here; only the counterexample's defining computations and their contradiction with polynomial invertibility are. (c) Peer review of the announcement is, as of this writing, one day old. The arithmetic core, however, is now checked four independent ways: exact rational arithmetic in a CAS, a kernel-verified ℚ-theorem, and certified ℂ-refutations in two dimensions.

## 6. Reproducing

- `Challenge.lean` — the four statements with `sorry`. Solve them yourself against any recent Mathlib.
- `ChallengeSolved.lean` — the kernel-accepted scripts, transcribed verbatim.
- `CollateralDamage.lean` — the implication graph: certified core + conditional collateral + cited open bridges.
- `proof-construction.md` — the full technical construction: mathematical mechanism, formal architecture, engineering pitfalls (recursion depth, `C`-numeral atoms, `Fin.succAbove` reduction), and the complete episode ledger.
- `jacobian.pdf` — the source paper.

The environment replays: each episode's proof source, diagnostics, and outcomes are content-addressed in the environment's SQLite ledger under the problem/episode IDs listed in `README.md`.

---

*Formalization: Claude (Anthropic), driving the LLM-Driven Proof Search Environment's tracked attempt path; kernel verdicts by Lean 4 with Mathlib. The environment's design principle — advisory metadata never marks a theorem proved; only the pinned verifier does — is what makes a release like this meaningful.*
