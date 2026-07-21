# Proof Construction: Formalizing the Jacobian Counterexample

Technical companion to `whitepaper.md`. This documents the mathematical mechanism, the
formal architecture, every engineering pitfall encountered, and the complete verification
ledger, so that the campaign is reproducible and auditable end to end.

## 1. The map and its two computable facts

With A = 1 + xy, B = A²z + y²(4 + 3xy):

```
F₁ = A·B                    = (1+xy)³z + y²(1+xy)(4+3xy)
F₂ = y + 3x·B               = y + 3x(1+xy)²z + 3xy²(4+3xy)
F₃ = 2x − 3x²y − x³z
```

**Fact D (determinant).** det ∂(F₁,F₂,F₃)/∂(x,y,z) = −2, identically. The paper computes
this by factoring through coordinates (P, y, s), s = x/A, with Jacobian factors −A and
2/A; the formal proof instead expands the determinant symbolically and lets `ring` verify
the resulting polynomial identity — no coordinate change needed.

**Fact C (collision).** F(0,0,−1/4) = F(1,−3/2,13/2) = F(−1,3/2,13/2) = (−1/4,0,0).
Underlying geometry: the fiber over (p,q,r) consists of the simple projective roots of
the binary cubic 2pS³ − qS²T + 2ST² − rT³; over (−1/4,0,0) it is −s(s−2)(s+2)/2 with
simple roots {0, 2, −2}. The formal proof only needs the three evaluations, which
`norm_num` checks in exact rational arithmetic.

**Why D + C refute the conjecture.** Suppose G were a compositional inverse:
`bind₁ F (G i) = X i` for all i. Apply the algebra evaluation `aeval p` at any point p.
By `MvPolynomial.aeval_bind₁`, `aeval p (bind₁ F φ) = aeval (fun j => aeval p (F j)) φ`,
so `aeval (F(p)) (G i) = p i` — G's evaluation is a retraction of F's. Fact C gives two
points with equal F-image; the retraction then forces their coordinates to agree, but
their first coordinates are 0 and 1. So 0 = 1 in ℂ — contradiction. Note this consumes
distinctness rather than assuming it, and needs only TWO of the three points.

## 2. The four verified statements

All verified through the tracked attempt path (problem → fidelity review → episode →
claim → step) of the LLM-Driven Proof Search Environment, environment hash
`9e26d28e…`, import manifest `["Mathlib.Tactic.Ring", "Mathlib.Tactic.NormNum",
"Mathlib", "open MvPolynomial"]` (hash `aed308b6…`).

| Thm | Problem | Episode | Fidelity | Outcome | Attempts |
|-----|---------|---------|----------|---------|----------|
| ℚ numeric claims (det ∧ 3-point collision) | `29f88fb5-3fe5-4976-954c-f8659f7bb45e` | `0c0afd37-90a0-47c6-8f74-e27846db9cd2` | attested (dev) | `kernel_verified` | 3 |
| ¬JC (ℂ, Fin 3), formal-conjectures shape | `654521be-0c8f-441e-bf6f-9b0d2f396afc` | `1f9dfbee-aa77-4741-8775-5e2d9c00eef6` | **verified** (`1505a59d`) | **`certified`** | 2* |
| ¬Injective (ℂ evaluation map) | `f3b97f2c-21b8-4286-87c8-e77d21095492` | `a8a4062d-c8b9-49d4-88a9-12f1b41e36df` | **verified** (`a06918f0`) | **`certified`** | 1 |
| ¬JC (ℂ, Fin 4), stabilized | `7312a555-fe11-4789-84cd-00ef0b1486d9` | `591219bc-d37c-4c19-8b24-a0202077e801` | **verified** (`343b9c10`) | **`certified`** | 3 |

\* attempt 1 was a policy rejection (`set_option` banned in SubmitModule), not a kernel failure.

Root statement hashes: `51fa27b7…` (ℚ), `b2e2cf32…` (dim 3), `1e8dcada…` (noninj),
`67395090…` (dim 4). The environment recomputes these server-side; a submitted module
cannot silently prove a different goal.

## 3. Formal architecture of the certified refutation (dimension 3)

```
¬ (∀ F : Fin 3 → MvPolynomial (Fin 3) ℂ,
     IsUnit (Matrix.of fun i j => pderiv i (F j)).det →
     ∃ G, (fun i => bind₁ G (F i)) = X ∧ (fun i => bind₁ F (G i)) = X)
```

Proof skeleton (single `Solve`, `raw_lean_block`):

1. `intro h`, then `hdet :` det of the witness's Jacobian `= C (-2)`:
   - `rw [Matrix.det_fin_three]` — cofactor expansion to a 9-entry expression;
   - mega-`simp` with `[pderiv_mul, pderiv_pow, pderiv_C, pderiv_X_self,
     pderiv_X_of_ne, pderiv_one, Derivation.map_add, Derivation.map_sub]` under
     `set_option maxRecDepth 400000 in` — eliminates every `pderiv` node;
   - `simp only [map_ofNat, map_one]` — folds `C 4/C 3/C 2` atoms into numerals;
   - `ring` — closes the polynomial identity.
2. Instantiate `h` at the witness; discharge `IsUnit` via
   `(isUnit_iff_ne_zero.mpr …).map C` after rewriting with `hdet`.
3. `h1 : ∀ p i, aeval (fun j => aeval p (F j)) (G i) = p i` — the retraction — from the
   inverse component via `congrFun`/`congrArg` + `simp only [aeval_bind₁, aeval_X]`.
4. `epts` — equal images of the two witness points — by
   `funext; fin_cases <;> simp <;> norm_num`.
5. Retraction at both points + `epts` → `(0 : ℂ) = 1` → `norm_num`.

Dimension 4 inserts one extra determinant stage before step 1's `det_fin_three`:
`rw [Matrix.det_succ_row _ 3]`, expand `Fin.sum_univ_four`, reduce the three
`(3 : Fin 4).succAbove k` index terms with `show … from rfl` lemmas, and let the pderiv
simp zero the appended row so `mul_zero` kills the dead cofactors **before** any 3×3
minor is expanded; the surviving minor is then the dimension-3 computation verbatim.

## 4. Engineering pitfalls (all hit, all resolved)

These cost the campaign its five failed attempts; they are recorded so nobody pays for
them twice.

1. **Flattened bullets don't scope.** `refine ⟨?_, ?_⟩; · tac; · tac` in a
   semicolon-flattened line leaves the second goal untouched. Multi-goal tactic proofs
   must ship as `raw_lean_block` with real indentation.
2. **`ring` sees `C 3` and `3` as different atoms.** After eliminating `pderiv`,
   residuals mix `C`-constants with numerals (the power rule introduces bare numeral
   coefficients). Fold with `simp only [map_ofNat, map_one]` before `ring`, or `ring`
   will leave a "true but unclosable" residue.
3. **`maxRecDepth`.** The pderiv elimination on a fully-expanded 3×3 determinant
   overflows the default recursion depth; `set_option maxRecDepth 400000 in` per tactic.
4. **`set_option` is banned in `SubmitModule` items** (server owns scope) but allowed in
   `Solve` proof terms. Large computations therefore go in one `Solve` with `have`
   blocks rather than a structured module.
5. **`Fin.succAbove` on literals must be reduced by `rfl`-lemmas, not unfolded.**
   Cofactor expansion introduces `(3 : Fin 4).succAbove 1`-type terms. Passing
   `Fin.succAbove, Fin.lt_def` to `simp` on the big goal caused a deterministic
   200000-heartbeat `whnf` timeout; `show ((3:Fin 4).succAbove k) = k from rfl` rewrites
   are free (the kernel computes them).
6. **Kill rows before expanding minors.** Zero the stabilized row first so dead
   cofactors vanish by `mul_zero` before their 3×3 determinants are ever expanded;
   otherwise the simp does ~4× the work and times out.
7. **`aeval`'s `algebraMap ℂ ℂ` noise self-cleans** — `algebraMap_self` is `@[simp]` in
   the pinned Mathlib; no manual handling needed after `aeval_C` fires.

## 5. Fidelity chain

Statement fidelity is a separate claim from proof soundness, and the environment tracks
it separately. The three certified problems carry review records
(`1505a59d`, `a06918f0`, `343b9c10`) binding the exact statement hashes to:

- the `formal-conjectures` source (`FormalConjectures/Wikipedia/JacobianConjecture.lean`),
  with a line-by-line mapping of `RegularFunction`/`Jacobian`/`comp`/`id` to their
  definitional unfoldings as used in the root statements;
- the tweet and paper (map coefficients, witness points), cross-checked this session by
  exact rational arithmetic in an independent CAS (sympy).

A review can only authorize the exact text it reviewed: the server recomputes all hashes
on submission and rejects mismatches.

## 6. The 11-variable cubic reduction: layered certificate

The gist certificate (`certificates/11var_cubic_reduction_gist.py`) reduces the map to an
11-variable degree-3 map Φ with the same three-point collision. Its determinant claim
rests on the construction chain (stabilizations + triangular automorphisms + two det −1
linear changes), asserted symbolically end-to-end by its own script; it never computes
the 11×11 determinant directly, and a direct symbolic Berkowitz expansion stalled
(hours, no output — as predicted, the raw expansion is far more expensive than the
certificate warrants). `certificates/layered_certificate_11var.py` replaces it:

1. **Random-point redundancy**: det JΦ = −2 at 40 exact integer points in [−10⁴,10⁴]¹¹
   (Schwartz–Zippel, deg ≤ 22 — transcription-error detection, not symbolic proof);
2. **Structural factors**: det of the linear part = −2, matching the chain;
3. **Monic normalization** closing the `F₀ = X + Q + C` fidelity gap: F₀ :=
   JΦ(p₁)⁻¹·(Φ(·+p₁) − Φ(p₁)) — the linear factor must be **JΦ(p₁)**, not JΦ(0)
   (translation regenerates linear terms through z = −1/4, c = ½). Verified exactly:
   identity linear part, homogeneous degrees {2,3} only, zero fiber containing the three
   distinct shifted points, det JF₀ = 1 (structural + 40 random points).

## 7. The Poisson bridge: status and the budget wall

Following the dependency order (Theorem 5 → Poisson bridge → Weyl → Dixmier), the
Poisson-bridge computational core was attacked as theorem 6: J·B = −2·I (mixed brackets)
plus the 27 commuting-derivation identities Σᵣ (Bᵣᵢ∂ᵣBₛⱼ − Bᵣⱼ∂ᵣBₛᵢ) = 0 (p-brackets),
with B the inverse-Jacobian matrix. All 36 identities are **verified in exact sympy
arithmetic**, and one conjunct is **kernel-verified**: episode `563b30de` proved
`J * J.adjugate = −2•1` through the tracked path before its give-up. The commuting
identities hit a hard environment constraint mapped precisely across three episodes
(`563b30de`, `7eb8bafc` ledgers): the kernel's 200k-heartbeat budget is fixed at command
start (tactic-level `set_option maxHeartbeats` is a no-op, unlike `maxRecDepth`), the
statement and proof share it, adjugate-unfolds-under-`pderiv` blow it in proof, and even
stating the 9 explicit inverse entries (~4KB of literals) blows it in elaboration.
Next-session design: three per-column-pair problems (6 entries, ~2.5KB each) or factored
nested literals, then a packaging theorem. The environment lessons are recorded in the
episode ledgers and the project memory.

## 8. What remains informal

- The paper's fibration analysis (Prop. 4.1: ℂ³ ≅ the simple-root locus of the incidence
  cubic), fiber counts, the image ℂ³ ∖ Γ, the nonproperness set Σ = V(Δ), the properness
  refinement (Thm 2.2), and the degree-d families (§5) — none formalized.
- The bridges to Dixmier / Mathieu / Zhao / cubic reduction (see `CollateralDamage.lean`
  for exact formal statements of what is and is not proved).
- General-n stabilization (n ≥ 5): the method certifies any fixed n by iterating the
  `det_succ_row` stage; a uniform ∀ n ≥ 3 theorem would need an induction over the
  stabilized determinant, which is future work.
