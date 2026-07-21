# Evidence — SolveAll #11 campaign

Machine records for every tracked result in this campaign. See
[whitepaper.md](whitepaper.md) for narrative, [attack-plan.md](attack-plan.md)
for staging.

## Milestone 1 — Gaussian anti-concentration

| field | value |
|---|---|
| statement | `∀ (m t ε σ : ℝ) (v : NNReal), (v:ℝ) = σ^2 → 0 < σ → 0 ≤ ε → gaussianReal m v (Icc (t-ε) (t+ε)) ≤ ENNReal.ofReal (2ε/(σ√(2π)))` |
| statement hash | `762c7306e47c38d97b8f925538ad47159750c1ca8c7411fb70af3c026d59699b` |
| problem_version_id | `d2f3e8c3-4b2b-4570-981d-2f0c01d76883` |
| fidelity_status | `attested` (`unsafe_dev_attestation=true`, honest dev-mode label — not `verified`/`certified`) |
| episode_id | `1f3255d1-62b9-4105-bca4-3da2290d5858` |
| outcome | `kernel_verified`, `pass@1`, termination reason `root_proved` |
| steps | 1 (single `submit_module`, no repair needed) |
| obligation_id | `6f9d907c-22bb-4631-b97a-80bceb89c73c` |
| module_source_hash | `fc13e724ac9c50d73d6ae85ac4313b0f32575827a70593f9d19bad6d0c6e3936` |
| declaration_manifest_hash | `03c802bc07e266a4ac2e4a8c21f6792fd91c986ae899c6370191b6e1b1009644` |
| lean_environment_hash | `9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d` |
| import manifest | `["Mathlib.Tactic.Ring", "Mathlib.Tactic.NormNum", "Mathlib"]` |
| toolchain | `leanprover/lean4:v4.32.0-rc1` + `mathlib@360da6fa` |
| helper lemmas | 1 (`gaussianPDFReal_le_max`, pointwise density-max bound) |
| Mathlib declarations used | 18, all pre-verified via `lean_declaration_lookup` before submission (see whitepaper.md) — 0 unknown-declaration failures |

Reproduce: `lean_declaration_lookup` results and full `trajectory_export`
JSON are in [trace/trajectory.md](trace/trajectory.md). Lean snapshot:
[proof/Milestone1_GaussianAntiConcentration.lean](proof/Milestone1_GaussianAntiConcentration.lean).

## Milestone 1a.1 — finite-family Gaussian anti-concentration (union bound)

| field | value |
|---|---|
| statement | `∀ {ι:Type}[Fintype ι]{Ω:Type}[MeasurableSpace Ω](P:Measure Ω)(X:ι→Ω→ℝ)(m t ε σ:ι→ℝ)(v:ι→ℝ≥0), (∀i,Measurable (X i))→(∀i,(v i:ℝ)=(σ i)^2)→(∀i,0<σ i)→(∀i,0≤ε i)→(∀i,P.map (X i)=gaussianReal (m i)(v i))→ P{ω|∃i,\|X i ω−t i\|≤ε i} ≤ ∑i,ENNReal.ofReal (2ε i/(σ i√(2π)))` |
| statement hash | `cd45ebe4f8ada258bbdf14bc6d845f4314aee77eec1cb2ce7c2004117df8d07b` |
| problem_version_id | `46bd7c1a-45ae-4b00-a839-48797a740c6b` |
| fidelity_status | `attested` (dev-mode; caps at kernel_verified, never certified) |
| episode_id | `e4c031ff-c334-49b5-8e2b-0c2ec5102c3f` |
| outcome | `kernel_verified`, `pass@1`, `root_proved`, 1 step |
| obligation_id | `976dd894-3879-4935-a1fa-33586b7cf2c4` |
| module_source_hash | `c1ac7485dd051dcf97f3fc53405cb3e90cdfa4d04b06d5deef35a7a0f9b04a79` |
| declaration_manifest_hash | `74e7dd05673f738dcc38a503ed218a2cb2624f33180ccfe39635e5999c05e142` |
| axioms (standalone `#print axioms`) | `[propext, Classical.choice, Quot.sound]` — no sorryAx, no project axioms |
| key point | **no independence assumed** — countable subadditivity (`measure_iUnion_le`) suffices |

## Milestone 1a.2 — homogeneous k-coefficient corollary

| field | value |
|---|---|
| statement | `... 0<σ→0≤ε→(∀i,P.map (X i)=gaussianReal (m i)(v i))→ P{ω|∃i,\|X i ω−t i\|≤ε} ≤ ENNReal.ofReal ((Fintype.card ι:ℝ)·(2ε/(σ√(2π))))` |
| statement hash | `d3f497b58d0a79fe46bcf66f6a6bc7716726a78eec54083fa904e9a0605027aa` |
| problem_version_id | `c1e88e47-4e7e-4a13-805c-137578751afc` |
| episode_id | `e04f96ea-0d23-42ca-9349-65db3e91d339` |
| outcome | `kernel_verified`, `pass@1`, `root_proved`, 1 step |
| obligation_id | `63a7f1fc-c2c1-4894-9301-f6b243ab5bd4` |
| module_source_hash | `be142854cf8723614c066439f4b5a9e62efc75f0a3b930bb6bd9f41136935ebf` |
| declaration_manifest_hash | `ec5f3f2125f670e41af25efd2ac082e03772acab61d2b5546d1345fe515525f4` |
| axioms | `[propext, Classical.choice, Quot.sound]` |

## Milestone 1a.3 — LP perturbation-model bridge (lean_checked)

`perturbed_coeff_some_near_threshold` — a definitional rename of M1a.2 in
perturbed-coefficient vocabulary. **lean_checked** (compiles standalone in the
canonical snapshot; `#print axioms` = the three standard axioms), NOT separately
MCP-tracked because it is `:= gaussian_anticoncentration_union_homogeneous ...`
with no new mathematics. Honest scope in its docstring: bounds "some individual
perturbed coefficient is ε-close to a threshold"; says nothing about basis
near-singularity (the M2 target).

Evidence labels (per constitution `<epistemic_contract>`): M1, M1a.1, M1a.2 =
**kernel_verified** (tracked MCP root + standalone `lake env lean` + axiom
report). M1a.3 = **lean_checked**. Novelty = **formalization** (classical
mathematics; the packaged finite-family Gaussian anti-concentration lemma is
apparently absent from the searched Mathlib snapshot), NOT new mathematics.

Snapshot: [proof/Milestone1a_FiniteFamilyAntiConcentration.lean](proof/Milestone1a_FiniteFamilyAntiConcentration.lean).

## Milestone 2.0 — distance from a Gaussian vector to a fixed hyperplane

| field | value |
|---|---|
| statement | `∀ (n:ℕ)(center:EuclideanSpace ℝ (Fin n))(σ t ε:ℝ)(u:EuclideanSpace ℝ (Fin n)), 0<σ→0≤ε→‖u‖=1→ multivariateGaussian center (σ^2•(1:Matrix (Fin n)(Fin n) ℝ)) {x\|\|inner ℝ u x−t\|≤ε} ≤ ENNReal.ofReal (2ε/(σ√(2π)))` |
| statement hash | `7031dca12c656cb4dbd9602e90746e1f8223fc438f6aebe5ffcf2895d18b19e4` |
| problem_version_id | `ff02637d-bdd8-4989-aff3-70f2decac8ee` |
| fidelity_status | `attested` (dev-mode; caps at kernel_verified, never certified) |
| episode_id | `851ff2ce-de85-4164-a274-024f4f2bcac3` |
| outcome | `kernel_verified`, `root_proved`, **2 submissions** (sub 1 kernel_fail on a helper-transport artifact — multi-line helper bodies do not survive `flat_tactic_sequence`; sub 2 pass with single-line semicolon-chained helpers) |
| obligation_id | `c507ce88-aa33-4d33-b39a-1f60e3c4d52d` |
| module_source_hash | `55538342234cf14e98f0f45f5ace408f29b83a665412e991d769ebf39980832a` |
| declaration_manifest_hash | `dd5b7bbb3e18fec36bd8f79cf4c7d6c4477ca5d07140fabad76e5eb47b3bd7e5` |
| lean_environment_hash | `9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d` |
| axioms (standalone `#print axioms`) | `[propext, Classical.choice, Quot.sound]` — no sorryAx, no project axioms |
| standalone recompile | `lake env lean proof/Milestone2_0_HyperplaneAntiConcentration.lean` exit 0 |
| key points | **arbitrary center** (bound uniform over the adversary's mean — M1 does not see the mean); **isotropic covariance `σ²I`** matches the per-entry `N(0,σ²)` model; **variance computed exactly** `uᵀ(σ²I)u = σ²·‖u‖² = σ²` (not bounded); distance-to-hyperplane reading is faithful precisely because `‖u‖=1`; no independence beyond the Gaussian law |

Reduction chain: ε-slab `{x\|\|⟪u,x⟫−t\|≤ε}` `=` `(innerSL ℝ u)⁻¹'(Icc (t−ε)(t+ε))`
→ pushforward via `Measure.map_apply` + `IsGaussian.map_eq_gaussianReal` gives a 1-D
`gaussianReal (mean) (Var).toNNReal` → `Var = σ²` via `covarianceBilin_self` +
`covarianceBilin_multivariateGaussian` → apply M1 (`gaussian_anticoncentration`),
uniform in the mean. Snapshot:
[proof/Milestone2_0_HyperplaneAntiConcentration.lean](proof/Milestone2_0_HyperplaneAntiConcentration.lean).

Evidence label: **kernel_verified** (tracked MCP root + standalone `lake env lean` +
axiom report). Novelty = **formalization** (classical Gaussian geometry; the packaged
hyperplane-slab anti-concentration for a multivariate Gaussian is apparently absent
from the searched Mathlib snapshot), NOT new mathematics.

**Bridge to the LP model (honest scope):** each column of the perturbation `G` in
`A = Ābar + G` is an isotropic Gaussian vector `N(Ābar_col, σ²I_m)`; M2.0 bounds the
probability that one such perturbed column lies in a thin slab around one *fixed*
hyperplane. What remains before σ_min (M2): a distance-to-*span* argument (the fixed
hyperplane must become the span of the *other* `n−1` columns, which is random and
correlated) plus a union/net over the `n` columns. M2.0 supplies the per-hyperplane
estimate that argument consumes; it does not by itself bound a determinant or singular
value.

## Milestone 2.1 — codimension-2 (coordinate-aligned) product anti-concentration

| field | value |
|---|---|
| statement | `∀ (n:ℕ)(center:EuclideanSpace ℝ (Fin n))(σ ε:ℝ)(i j:Fin n)(t:Fin n→ℝ), i≠j→0<σ→0≤ε→ multivariateGaussian center (σ^2•1) {x\|\|x i−t i\|≤ε ∧ \|x j−t j\|≤ε} ≤ ENNReal.ofReal ((2ε/(σ√(2π)))^2)` |
| statement hash | `dd3b81bd871f967c55ffb4fe6f1ac4614313e5aadd888a13a98de8985639bf91` |
| problem_version_id | `c548e3fe-04a2-46ad-8d69-5cebc531f015` |
| episode_id | `10653478-f63b-4704-8761-cb3cec0cc503` |
| outcome | `kernel_verified`, `root_proved`, `pass@1`, 1 submission |
| obligation_id | `d7fd24d1-6aef-40c9-9bc5-4a9cbbef1bde` |
| module_source_hash | `0665a4404c00dd8be0de25322676449b121ad2377687076813172c78d62713d9` |
| axioms | `[propext, Classical.choice, Quot.sound]` |
| key point | **the squared bound is the codimension gain** — distinct coordinates of an isotropic Gaussian are INDEPENDENT (covariance `(σ²I) i j = 0` for `i≠j`), PROVED not assumed, so the joint slab probability factorizes into a product of two M1 marginals |

## Milestone 2.2 — general arbitrary-orientation subspace anti-concentration (MASTER)

| field | value |
|---|---|
| statement | `∀ (n k:ℕ)(center:EuclideanSpace ℝ (Fin n))(σ ε:ℝ)(u:Fin k→EuclideanSpace ℝ (Fin n))(t:Fin k→ℝ), Orthonormal ℝ u→0<σ→0≤ε→ multivariateGaussian center (σ^2•1) {x\|∀ j, \|inner ℝ (u j) x−t j\|≤ε} ≤ ENNReal.ofReal ((2ε/(σ√(2π)))^k)` |
| statement hash | `3ad10c1dd02b569b30d76e57863563a324a708c6d01b7114024bcbc43f99353f` |
| problem_version_id | `4a4d86dd-175c-4a0e-86f3-f1656e629c64` |
| episode_id | `ea3c53fe-fca3-4764-b89d-26a5d9546654` |
| outcome | `kernel_verified`, `root_proved`, `pass@1`, 1 submission |
| obligation_id | `cde9e7cc-69fd-4592-b808-66f8883d0b13` |
| module_source_hash | `af28f30e3e9cca24203f70eceb6fc78544dbed11ec8643849c43127b0b197587` |
| declaration_manifest_hash | `bdc8d671461b7688cc6f858d6407e0a46cb947c41d276d06448f56e28e638670` |
| axioms | `[propext, Classical.choice, Quot.sound]` |
| standalone recompile | `lake env lean proof/Milestone2_SubspaceAntiConcentration.lean` exit 0 (both M2.1 + M2.2 roots) |

**M2.2 is the master result** of the distance-to-subspace tower and subsumes M2.1
(coordinate directions form an orthonormal family) and M2.0 (`k=1`). Reduction chain:
for an arbitrary orthonormal family `u : Fin k → ℝⁿ`, (1) the projection tuple
`x ↦ (⟪u j,x⟫)_j` is `⇑(ContinuousLinearMap.pi (innerSL ℝ ∘ u))`, hence has a Gaussian law
(`isGaussian_map`); (2) `covarianceBilin μ (u i)(u j) = σ²⟪u i,u j⟫`
(`covarianceBilin_multivariateGaussian`), so cross-covariances vanish by orthonormality
(`hu.2 hij`) ⇒ the projections are **independent**
(`HasGaussianLaw.iIndepFun_of_covariance_eq_zero`); (3) the slab-intersection measure
factorizes (`iIndepFun.measure_inter_preimage_eq_mul`) into `k` marginals, each `≤ 2ε/(σ√2π)`
by M1 (variance `σ²‖u j‖²=σ²`); (4) product `= ofReal((2ε/(σ√2π))^k)`. Since
`{‖P_{Wᗮ}x‖ ≤ ε} ⊆ {∀ j, |⟪u j,x⟫|≤ε}`, this bounds the distance from a Gaussian-perturbed
vector to an ARBITRARY fixed subspace with the sharp codimension power. Snapshot:
[proof/Milestone2_SubspaceAntiConcentration.lean](proof/Milestone2_SubspaceAntiConcentration.lean).

Evidence label: **kernel_verified** (tracked MCP roots + standalone `lake env lean` + axiom
report). Novelty = **formalization** (classical Gaussian geometry; the packaged
arbitrary-orientation subspace anti-concentration with the codimension gain is apparently
absent from the searched Mathlib snapshot), NOT new mathematics.

**Bridge to σ_min (honest scope, the remaining gap).** M2.2 bounds distance to a FIXED
subspace. The σ_min lower-tail needs the fixed subspace to become the RANDOM span of the
other columns `Hᵢ = span(Aⱼ:j≠i)`. Remaining obligations (see state.md): **M2-DEF** (define
`smallestSingularValue`), **M2-GEOM** (`σ_min(A) ≥ n^{-1/2} min_i dist(Aᵢ,Hᵢ)`, deterministic
Rudelson–Vershynin), **M2-COND** (condition on the other columns — independent of `Aᵢ` — and
apply M2.2 with `k=1`, `u` = unit normal of `Hᵢ`; needs matrix-Gaussian-as-product Fubini +
measurable normal selection), **M2-UNION** (union over `n` columns). M2.2 is the load-bearing
input to M2-COND; it does not by itself bound a determinant or singular value.

## Milestone 2-GEOM — Rudelson–Vershynin geometric core (deterministic)

| field | value |
|---|---|
| statement | `∀ {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{n:ℕ}(a:Fin n→E)(x:Fin n→ℝ)(i:Fin n), \|x i\| * Metric.infDist (a i) (↑(Submodule.span ℝ (a '' {j\|j≠i})):Set E) ≤ ‖∑ j, x j • a j‖` |
| statement hash | `8588c87e9472e58b75a9b627108a430e3c3d130aeda402feef294eee6df1d73c` |
| problem_version_id | `8d13dff9-8bb3-49a3-a712-1357ef33e609` |
| episode_id | `d99aa6a8-a43f-4cdc-ab37-a3f6a9e2edbb` |
| outcome | `kernel_verified`, `root_proved`, **2 submissions** (sub 1 kernel_fail: helper `·` bullets do not survive `flat_tactic_sequence`; sub 2 pass with bullet-free sequential case split) |
| obligation_id | `3034f98b-3396-4d09-99c3-8f7b7e1ce9dc` |
| module_source_hash | `efc9983b9d7d35fcb705f6cd227be42d904743c3a633397d6c9cfb090edb96ff` |
| declaration_manifest_hash | `0f8355f247822668f865521bdd2434c5956a7ba4d6eed72ea57aeba0ebb0f409` |
| axioms | `[propext, Classical.choice, Quot.sound]` (both root + helper) |
| standalone recompile | `lake env lean proof/Milestone2_GEOM_RudelsonVershynin.lean` exit 0 |
| key point | **deterministic, no probability**; holds in ANY real normed space; the step that lower-bounds `σ_min` by column-to-span distances |

Helper `abs_smul_infDist_le_norm_smul_add_mem`: `|c|·dist(a,W) ≤ ‖c•a+w‖` for `w ∈ W`
(`c•a+w = c•(a−(−c⁻¹w))`, `−c⁻¹w ∈ W`, `dist(a,W) ≤ ‖a−(−c⁻¹w)‖`; via `norm_smul`,
`Metric.infDist_le_dist_of_mem`, `Submodule.neg_mem/.smul_mem`). Root splits
`∑ x j • a j = x i • a i + ∑_{j≠i} x j • a j` (`Finset.add_sum_erase`), the second term in
`span{a j:j≠i}` (`Submodule.sum_mem` + `subset_span`), then applies the helper. Snapshot:
[proof/Milestone2_GEOM_RudelsonVershynin.lean](proof/Milestone2_GEOM_RudelsonVershynin.lean).

Evidence label: **kernel_verified**. Novelty = **formalization** (classical
Rudelson–Vershynin linear algebra). Bridge: with `∃ i, |x i| ≥ ‖x‖/√n` and a σ_min
definition (M2-DEF), this gives `σ_min(A) ≥ n^{-1/2} min_i dist(Aᵢ, span of other columns)`,
the deterministic half of the σ_min anti-concentration bound; the probabilistic half is
M2-COND (condition on the other columns, apply M2.2 with k=1) + M2-UNION.

## Milestone 2-GEOMσ — Rudelson–Vershynin σ_min-form lower bound (deterministic)

| field | value |
|---|---|
| statement | `∀ {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E](n:ℕ)(hn:0<n)(a:Fin n→E)(x:EuclideanSpace ℝ (Fin n)), (Finset.univ.inf' _ (fun i => Metric.infDist (a i) (↑(Submodule.span ℝ (a''{j\|j≠i})):Set E))) * ‖x‖ ≤ Real.sqrt n * ‖∑ j, x j • a j‖` |
| statement hash | `aeb92904ec37fe962008250514a266503995e3603e0c2fda29007cbcf5aae402` |
| problem_version_id | `ca8e0109-b04c-4939-932a-8994d97c31bb` |
| episode_id | `56a975eb-e54e-4970-8b7c-6cbb847c1cf4` |
| outcome | `kernel_verified`, `root_proved`, `pass@1`, 1 submission (empty module_items; fully-inlined raw_lean_block root) |
| obligation_id | `8a70580a-1569-4ed7-90d4-ebafa5707c30` |
| module_source_hash | `99626e77d3bed3a0cd20a87389428286f413f8bb9c52a7bee45f8c912ada79c7` |
| declaration_manifest_hash | `180ab619cdc471ab35d6d6842a9b70021b77b9ac332e3c6a94ce1eb4efa9f182` |
| axioms | `[propext, Classical.choice, Quot.sound]` |
| standalone recompile | `lake env lean proof/Milestone2_GEOM_RudelsonVershynin.lean` exit 0 (modular form: helper + per-vector + `exists_coord_ge` + `rv_min_dist_bound`) |

The full deterministic Rudelson–Vershynin lower bound: combines M2-GEOM's per-vector projection
bound with the coordinate lemma `exists_coord_ge` (`∃ i, ‖x‖ ≤ √n·|x i|`, since
`‖x‖² = ∑ x_j² ≤ n·max_j x_j²`). Dividing by `‖x‖` over unit `x` gives
`σ_min(A) ≥ n^{-1/2}·min_i dist(A_i, span of other columns)`. Pure linear algebra, no
probability. Snapshot:
[proof/Milestone2_GEOM_RudelsonVershynin.lean](proof/Milestone2_GEOM_RudelsonVershynin.lean).
Evidence label: **kernel_verified**; novelty = **formalization** (classical RV geometry). This
completes the deterministic content (M2-GEOM + coordinate lemma) of the σ_min ladder; the
remaining edges are M2-DEF (name σ_min), M2-COND (conditioning + M2.2), M2-UNION.

## Milestone 2-DEF — σ_min definition + Rudelson–Vershynin lower bound

| field | value |
|---|---|
| statement | `∀ {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E](n:ℕ)(hn:0<n)(a:Fin n→E), (Finset.univ.inf' _ (fun i => Metric.infDist (a i) (span others))) / Real.sqrt n ≤ ⨅ x : {v:EuclideanSpace ℝ (Fin n)//‖v‖=1}, ‖∑ j, (↑x) j • a j‖` |
| statement hash | `f3cb5ad111fcc7696095b2115a017e7d33c58816d00359d9ee8e2044c9462c27` |
| problem_version_id | `73ac63c1-97df-4a2f-83f9-25b52cf49ef6` |
| episode_id | `9bdee270-3333-4e6f-995d-9489ff936ce8` |
| outcome | `kernel_verified`, `root_proved`, `pass@1`, 1 submission (empty module_items; σ_min inlined as `⨅` in the statement; RV chain inlined in the raw_lean_block root) |
| obligation_id | `0e22db28-f3c5-4198-85a7-099f0761f7f4` |
| module_source_hash | `0e684f2c57b6e24a513a39133a8a85900fb464b2a4732869aa6305e0d087e46d` |
| declaration_manifest_hash | `35c70e3a07353010b40e87841fabb0846bba0092456c05fb5428256ae08ee2fc` |
| axioms | `[propext, Classical.choice, Quot.sound]` |
| standalone recompile | `lake env lean proof/Milestone2_DEF_SigmaMinLowerBound.lean` exit 0 (def-based API form) |

**M2-DEF** names the smallest singular value of a column family as `sigmaMinCols a :=
⨅_{‖x‖=1} ‖∑ x_j a_j‖` (for `E=ℝⁿ`, columns of `A`, exactly `σ_min(A)=min_{‖x‖=1}‖Ax‖`) and
proves `σ_min(cols) ≥ n^{-1/2}·min_i dist(a i, span of others)` — the Rudelson–Vershynin
lower bound. Proof: pointwise RV bound (M2-GEOMσ) over each unit `x` + `le_ciInf`
(unit-sphere nonempty via `EuclideanSpace.single`, `PiLp.norm_single`). Snapshot:
[proof/Milestone2_DEF_SigmaMinLowerBound.lean](proof/Milestone2_DEF_SigmaMinLowerBound.lean).
Evidence label: **kernel_verified**; novelty = **formalization**. This completes the ENTIRE
deterministic half of the σ_min anti-concentration ladder. The one remaining edge to the
probabilistic σ_min lower-tail `P(σ_min ≤ ε) ≤ C·n·ε/σ` is **M2-COND** (condition on the
other columns, feed M2.2 with `k=1`; needs matrix-Gaussian-as-product + a measurable unit
normal of the random span) then **M2-UNION**.

## Milestone 2-COND (conditional) — distance to a FIXED subspace tail bound

| field | value |
|---|---|
| statement | `∀ (n:ℕ)(center:EuclideanSpace ℝ (Fin n))(σ ε:ℝ)(W:Submodule ℝ _)(u:EuclideanSpace ℝ (Fin n)), 0<σ→0≤ε→‖u‖=1→(∀ w∈W, inner ℝ u w=0)→ multivariateGaussian center (σ²•1) {x\|Metric.infDist x (↑W:Set _) ≤ ε} ≤ ENNReal.ofReal (2ε/(σ√(2π)))` |
| statement hash | `60ecff763acfc53a482ed79471122e5a8c19f0b065bfef77da63640b21c84c94` |
| problem_version_id | `337087ce-1a8e-4dc0-bd74-a770082a408a` |
| episode_id | `b15cd230-3d17-4c8a-be21-0ce0f7d18636` |
| outcome | `kernel_verified`, `root_proved`, `pass@1`, 1 submission (empty module_items; M1/M2.0/geo inlined in the raw_lean_block root) |
| obligation_id | `30e3b2f2-b124-4b86-9d3f-1a2e23f9bee2` |
| module_source_hash | `f07c20ce63af1abfd5f1f7a5f3d3aa46838386a737290c859bdcf78c135d702b` |
| declaration_manifest_hash | `c28b25389ff59cf685d54c31c67b4e7346116da7fdf7207f761e1f9b686d04f4` |
| axioms | `[propext, Classical.choice, Quot.sound]` |
| standalone recompile | `lake env lean proof/Milestone2_COND_ConditionalDistBound.lean` exit 0 (modular form) |

The conditional (fixed-subspace) piece of M2-COND: `P(dist(x, W) ≤ ε) ≤ 2ε/(σ√(2π))` for any
fixed subspace `W` with a unit normal `u ⊥ W`, phrased via Mathlib's genuine `Metric.infDist`.
Geometric core (`abs_inner_le_infDist_of_perp`): `|⟨u,x⟩| ≤ dist(x,W)` for unit `u ⊥ W` (via
`Metric.le_infDist` + `abs_real_inner_le_norm`), so `{dist(x,W)≤ε} ⊆ {|⟨u,x⟩|≤ε}`;
`measure_mono` + M2.0 close it. Crucially needs only EXISTENCE of one unit normal (not a
measurable selection), so it discharges the per-ω conditional inequality. Snapshot:
[proof/Milestone2_COND_ConditionalDistBound.lean](proof/Milestone2_COND_ConditionalDistBound.lean).
Evidence label: **kernel_verified**; novelty = **formalization**. Remaining for the full σ_min
lower-tail: the measure-theoretic conditioning (matrix-Gaussian-as-product Fubini + measurable
unit-normal of the random span), then M2-UNION.

## Milestone 2-COND (step 3a) — matrix-Gaussian column independence

| field | value |
|---|---|
| statement | `∀ (m n:ℕ)(center:Fin n→EuclideanSpace ℝ (Fin m))(σ:ℝ), iIndepFun (fun (j:Fin n)(ω:Fin n→EuclideanSpace ℝ (Fin m)) => ω j) (Measure.pi (fun k => multivariateGaussian (center k) (σ²•1)))` |
| statement hash | `04c6e1447e5ea23c8c4f81e0240bcfa4b6301974a45d4b64f18fe1d4df4dae5f` |
| problem_version_id | `88cc675f-272b-4498-90af-9e428d8072ce` |
| episode_id | `a95d1c04-1679-47ab-a799-671424348482` |
| outcome | `kernel_verified`, `root_proved`, `pass@1`, 1 submission (empty module_items) |
| obligation_id | `537fda0d-28f7-4566-b7cb-baef6af69073` |
| module_source_hash | `7e9f739f96807c453943c195a1d67e0729aae0c46bf6fbcdf9f2bc662621d0e7` |
| declaration_manifest_hash | `f08831a2d6bc74d1076f8d7ab25ff15f9eea24bf44fae85e4b56dc0ed52e2107` |
| axioms | `[propext, Classical.choice, Quot.sound]` |
| standalone recompile | `lake env lean proof/Milestone2_COND_ColumnIndependence.lean` exit 0 (+ companion `matrix_gaussian_column_law`) |

The matrix Gaussian modeled as `Measure.pi` over its `n` columns has jointly INDEPENDENT
columns (`ProbabilityTheory.iIndepFun_pi` with `X = id`), and each column marginal is
`multivariateGaussian (center j) (σ²•1)` (`measurePreserving_eval`). This is M2-COND step 3a —
the product structure that lets column `i` be conditioned on the others (independent) and then
bounded by M2-CONDc. Snapshot:
[proof/Milestone2_COND_ColumnIndependence.lean](proof/Milestone2_COND_ColumnIndependence.lean).
Evidence label: **kernel_verified**. Remaining for the σ_min lower-tail: the MEASURABLE
unit-normal selection of the random span (M2-COND step 3b) + Fubini glue, then M2-UNION.

## Milestone 2-COND (step 3c) — Fubini conditioning glue

| field | value |
|---|---|
| statement | `∀ {Ω Ω':Type}[MeasurableSpace Ω][MeasurableSpace Ω'](Q:Measure Ω)(P:Measure Ω')[IsProbabilityMeasure Q][SFinite P](S:Set (Ω×Ω')), MeasurableSet S → ∀ (c:ENNReal), (∀ y, P (Prod.mk y ⁻¹' S) ≤ c) → (Q.prod P) S ≤ c` (manifest opens `MeasureTheory`) |
| statement hash | `14052aff1d4cf64aca08beac994dc8b53cdb37bc9bf5344222d1221ff5050acc` |
| problem_version_id | `7cf633b2-2757-4f10-ab1d-ee4953c3ebb0` |
| episode_id | `3a68c3c7-c2c1-49a0-a55f-f9f594059fd4` |
| outcome | `kernel_verified`, `root_proved`, `pass@1`, 1 submission (empty module_items; raw_lean_block) |
| obligation_id | `5e64704f-329d-4c1e-a7bb-129e7a43c6f4` |
| module_source_hash | `c825c05f34cf840342be550b76f70885e99cf4d97c2e60aba00a51aae58cf897` |
| declaration_manifest_hash | `6026c80371dc0bc67373adaa48b2525703d21e5b0e680a541be1df5167cf03ff` |
| axioms | `[propext, Classical.choice, Quot.sound]` |
| standalone recompile | `lake env lean proof/Milestone2_COND_FubiniGlue.lean` exit 0 |

The Fubini step: `(Q.prod P) S = ∫⁻ y, P(slice at y) ∂Q ≤ ∫⁻ y, c ∂Q = c·Q(univ) = c` for
probability `Q` (`Measure.prod_apply` + `lintegral_mono` + `lintegral_const` + `measure_univ`).
Promotes the per-ω conditional bound (M2-CONDc, `c = 2ε/(σ√2π)`) to the joint matrix-Gaussian
probability, using column independence (M2-COND-3a). Snapshot:
[proof/Milestone2_COND_FubiniGlue.lean](proof/Milestone2_COND_FubiniGlue.lean). Evidence label:
**kernel_verified**. First campaign use of an `open MeasureTheory` manifest directive (for the
`∫⁻` notation). Remaining for the σ_min lower-tail: the MEASURABLE unit-normal selection of the
random span (M2-COND step 3b), then M2-UNION.

## M2 reconnaissance (wall map, prior cycle)

Searched the pinned Mathlib for the condition-number / singular-value machinery
M2 needs. **Present:** `Matrix.det`, `Matrix.toEuclideanLin`,
`spectrum_toEuclideanLin`, and the general `IsGaussian` class on topological
vector spaces (multivariate Gaussians and their linear functionals are
expressible). **Absent:** any `smallestSingularValue` definition; any
singular-value / determinant anti-concentration. Consequence: full σ_min is a
multi-session build, but the first rung — **M2.0, distance from a Gaussian
vector to a fixed hyperplane** (`⟨g,u⟩ ~ N(0,σ²)` ⇒ `dist(g,H)=|⟨g,u⟩|`
inherits M1's bound) — is tractable and reuses M1 directly. This is the
designated next target.

## Not yet attempted (see attack-plan.md)

- M2.0 — distance from a Gaussian vector to a fixed subspace/hyperplane (NEXT)
- M2 — smallest-singular-value / condition-number anti-concentration (needs a
  `smallestSingularValue` definition built first; multi-session)
- Tier 2 — LP / pivot-rule model specification
- Tier 3 — the open conjecture itself (out of scope for any near-term session)

## Milestone M2-COND-3b(a)-base — nonzero univariate polynomial has null zero set

| field | value |
|---|---|
| statement | `∀ (p : Polynomial ℝ), p ≠ 0 → MeasureTheory.volume {x : ℝ | Polynomial.eval x p = 0} = 0` |
| statement hash | `678dc1db8f289a91b92ef12e0ea6209669721b15105e3f05e788b6dcbe49b294` |
| problem_version_id | `8cf700f9-fd4f-4187-8438-740d27b3e543` |
| episode_id | `1dbbeac4-2198-430e-9b0c-7ec5347d687a` |
| outcome | `kernel_verified`, `root_proved`, `pass@1`, 1 submission |
| obligation_id | `90e792ab-3ff8-4014-9008-3354a4cd9a0b` |
| module_source_hash | `6fed5c8f4b5cd352b81425bf70c0c4b14804fa556da2fb0f66111593bbda2b52` |
| declaration_manifest_hash | `c39d435b3361970292a60c3c3169fd1b5f19c60637d534d6483a3d6e1cc9ecd3` |
| axioms | `[propext, Classical.choice, Quot.sound]` |
| standalone recompile | `lake env lean proof/Milestone2_COND_PolyNullBase.lean` exit 0 |

Base case (`N = 1`) of the missing-Mathlib theorem "the zero set of a nonzero `N`-variable
polynomial is Lebesgue-null", which is exactly what `det ≠ 0` a.s. under the matrix Gaussian
reduces to (the singular locus `{det = 0}` is a nonzero polynomial's zero set; the Gaussian is
a.c. w.r.t. Lebesgue). Proof: zero set ⊆ finite `p.roots.toFinset` (`Polynomial.mem_roots'`),
hence finite (`Set.Finite.subset`), hence null (`Set.Finite.measure_zero`, `volume` has no
atoms). Snapshot: [proof/Milestone2_COND_PolyNullBase.lean](proof/Milestone2_COND_PolyNullBase.lean).

**Missing-Mathlib findings (this cycle, for whoever attacks `det ≠ 0` a.s.):** the pinned
Mathlib has NO polynomial/analytic zero-set measure-zero lemma and NO multivariate Gaussian
absolute-continuity lemma (only 1-D `gaussianReal_absolutelyContinuous`). Present and useful:
`addHaar_submodule`/`addHaar_affineSubspace` (a proper submodule/affine-subspace of a
finite-dim space has Haar/Lebesgue measure 0). Two routes to `det ≠ 0` a.s.: **(A)** the
multivariate polynomial-null theorem (this base + induction on variables via `finSuccEquiv` +
Fubini/Tonelli on `Measure.pi`) then multivariate-Gaussian a.c.; **(B)** column-by-column —
`det=0 ⟺` some column ∈ span of the others (a proper subspace, `addHaar_submodule`-null), each
Gaussian column a.c., glued by the already-verified `matrix_gaussian_columns_iIndepFun` +
`prod_measure_le_of_slice_le`. Both need multivariate-Gaussian a.c. w.r.t. `volume` (assemble
from `gaussianReal_absolutelyContinuous` over the product + the affine `stdGaussian` pushforward).

## Note — alternative M2-DEF formulation (`sigmaMin_lower_bound`, this session)

A second, equivalent M2-DEF was kernel-verified in parallel: `sigmaMin_lower_bound` (problem
`ecacc32e-d778-4cb3-892d-40bacfa3d10a`, episode `5a5ec38c-7f82-4e55-9d06-026255f3f050`,
statement hash `67cb826c…`), defining `σ_min` as the `⨅` of the Rayleigh quotient
`‖∑ x_j a_j‖/‖x‖` over the NONZERO-vector subtype (vs. the unit-sphere subtype of
`sigmaMin_cols_ge`), with the same RV lower bound `σ_min ≥ n^{-1/2}·min_i dist`. Snapshot:
[proof/Milestone2_DEF_SigmaMin.lean](proof/Milestone2_DEF_SigmaMin.lean). Fully inlined
(empty `module_items`); `#print axioms` = the three standard axioms.

## Milestone M2-COND-3b(a)-AC — finite-product absolute continuity (Mathlib gap-filler)

| field | value |
|---|---|
| statement | `∀ {n:ℕ}(μ ν:Fin n→Measure ℝ)[∀ i,SigmaFinite (μ i)][∀ i,SigmaFinite (ν i)], (∀ i, μ i ≪ ν i) → Measure.pi μ ≪ Measure.pi ν` |
| statement hash | `98902641cf9c38cdf0756373f28f27e07e2296dfc8003d2652e82736b12160bb` |
| problem_version_id | `417c70aa-fa41-4b76-b3c9-7cf1c7248e69` |
| episode_id | `5f8f7d06-c07e-48ae-8e45-7ee7a7ee1b41` |
| outcome | `kernel_verified`, `root_proved`, `pass@1`, 1 submission |
| obligation_id | `520ebb00-2890-4e9d-975d-1a4cbd3e2b6e` |
| module_source_hash | `25e8e79b10502f4176f644657dce601ea9599717d94832a3cd5add92b99b8aa7` |
| declaration_manifest_hash | `e510fe3debecdfc0dc6300452044067c416830b51d16bf23ab4d8c852af94a76` |
| axioms | `[propext, Classical.choice, Quot.sound]` |
| standalone recompile | `lake env lean proof/Milestone2_COND_PiAbsCont.lean` exit 0 |

**Genuine gap-filler for the pinned Mathlib** (which has only the BINARY `AbsolutelyContinuous.prod`,
no finite-product / `Measure.pi` version — confirmed by exhaustive search). Induction on `n` via
`measurePreserving_piFinSuccAbove` (`Measure.pi` over `Fin (n+1)` ≅ `(μ 0).prod (Measure.pi rest)`),
`AbsolutelyContinuous.prod` on head + tail (IH), transported back by `absolutelyContinuous_map`
through the measurable-embedding equivalence. Snapshot:
[proof/Milestone2_COND_PiAbsCont.lean](proof/Milestone2_COND_PiAbsCont.lean).

**Direct next step to close `det ≠ 0` a.s. (now a short chain):** (1) `Measure.pi (fun i => gaussianReal (m i) (v i)) ≪ volume`
on `Fin n → ℝ` — immediate from this lemma + `gaussianReal_absolutelyContinuous` (per-coordinate,
`v i ≠ 0`) + `volume_pi`; (2) `multivariateGaussian center (σ²•1) ≪ volume` — pushforward of (1)
through the affine linear-isometry defining `stdGaussian`/`multivariateGaussian` (invertible for
`σ>0`, so a.c. transports; uses `MeasurePreserving`/`MeasurableEmbedding.absolutelyContinuous_map`);
(3) `det ≠ 0` a.s. — `{det=0} = ⋃_i {col i ∈ span of the others}`, each a proper subspace hence
`volume`-null by `addHaar_submodule`, hence `multivariateGaussian`-null by (2); (4) feed the
already-verified `matrix_gaussian_columns_iIndepFun` + `gaussian_dist_subspace_le` +
`prod_measure_le_of_slice_le` + M2-UNION. This is the precise, now-short remaining path to the
full σ_min anti-concentration lower-tail `P(σ_min ≤ ε) ≤ C·n·ε/σ`.

### Update — det-null chain step (1) now kernel-verified

`gaussian_pi_absolutelyContinuous` (problem `3c4db4e8-9ca6-47fa-9526-97f6371fdf26`, episode
`b9683c13-3468-4618-b8a7-65c9648ae22b`, statement hash `9d61c490…`, module_source_hash
`4641c785…`, obligation `eb53ee5a…`): `Measure.pi (fun i => gaussianReal (m i) (v i)) ≪ volume`
on `Fin n → ℝ` for `∀ i, v i ≠ 0`. `kernel_verified`, pass@1; `#print axioms` = the three
standard axioms; standalone recompile of `proof/Milestone2_COND_PiAbsCont.lean` exit 0. This is
step (1) of the `det ≠ 0` a.s. chain — DONE. Remaining: (2) `multivariateGaussian ≪ volume`
(pushforward through the affine linear isometry `stdGaussian`/`multivariateGaussian`; uses
`MeasurableEmbedding.absolutelyContinuous_map` + linear-map-scales-Haar), (3) `det ≠ 0` a.s. via
`addHaar_submodule`, (4) assemble with the verified conditioning + union bound. Steps (2)–(4) are
Mathlib-API assembly; the genuinely-new/hard part (finite-product a.c. + product-Gaussian a.c.)
is now complete and kernel-verified.

## Milestone M2-COND-3b(a)-STD — standard Gaussian a.c. + a.s.-nonsingularity core

| field | value |
|---|---|
| statement | `∀ (n:ℕ), stdGaussian (EuclideanSpace ℝ (Fin n)) ≪ (volume : Measure (EuclideanSpace ℝ (Fin n)))` |
| statement hash | `c1b64ee96569b182af2faddd7eac107bc939e98876220b3ee1fc5ae220e4b2f7` |
| problem_version_id | `479268e8-ab0a-48c0-b3f2-50e46f7cded3` |
| episode_id | `6459515f-1c47-40b5-823a-f4be393e8110` |
| outcome | `kernel_verified`, `root_proved`, `pass@1`, 1 submission |
| obligation_id | `3f9bf528-b91d-445d-aa86-8e0060747f28` |
| module_source_hash | `4b98333cb1f7368eebc015bbe822bebccb1e4adaa2bf5cf902acb2a6fb807ee8` |
| declaration_manifest_hash | `3cbf5f256b005834b842457941b8c61aa5b38a39b956ad6abe501111eb441992` |
| axioms | `[propext, Classical.choice, Quot.sound]` |
| standalone recompile | `lake env lean proof/Milestone2_COND_StdGaussianAC.lean` exit 0 |

**Step (2) of the det-null chain, standard/isotropic centered case — DONE.** `stdGaussian ≪ volume`
via `map_pi_eq_stdGaussian` + this campaign's `gaussian_pi_absolutelyContinuous` (inlined) +
`PiLp.volume_preserving_toLp`. Snapshot also proves the **a.s.-nonsingularity core** (corollary
`stdGaussian_subspace_measure_zero`, same file, kernel-verified): `stdGaussian W = 0` for any
proper submodule `W ≠ ⊤`, via `Measure.addHaar_submodule` — i.e. a nondegenerate Gaussian vector
misses any fixed proper subspace almost surely, exactly the geometric fact the σ_min conditioning
argument applies to each perturbed column against the fixed span of the others. Snapshot:
[proof/Milestone2_COND_StdGaussianAC.lean](proof/Milestone2_COND_StdGaussianAC.lean).

**Remaining to the full σ_min lower-tail:** only the general `multivariateGaussian center (σ²•1) ≪
volume` (standard case + the invertible affine σ-scaling/translation transport via
`map_linearMap_addHaar_eq_smul_addHaar`, `det = σⁿ ≠ 0`) — then the a.s.-nonsingularity corollary
transfers to the perturbed columns and feeds the already-verified conditioning
(`matrix_gaussian_columns_iIndepFun` + `gaussian_dist_subspace_le` + `prod_measure_le_of_slice_le`)
+ M2-UNION. The a.c. foundation and the standard-case nonsingularity core are now complete.

## Milestone M2-COND-3b(a)-SCALED — perturbed-column a.c. + a.s.-nonsingularity (SMOOTHED MODEL)

| field | value |
|---|---|
| statement | `∀ (n:ℕ)(c:EuclideanSpace ℝ (Fin n))(σ:ℝ), σ≠0 → (stdGaussian (EuclideanSpace ℝ (Fin n))).map (fun g => c + σ • g) ≪ volume` |
| statement hash | `91f742e1bba1cb96a461b1cdf7b3b4691499a78b4a50ae8c3d742ab8e1f2dd62` |
| problem_version_id | `7683b09b-47e4-46cc-9d03-eb7da0442d9f` |
| episode_id | `4ec96081-0c19-476a-a078-f48e5148b540` |
| outcome | `kernel_verified`, `root_proved`, `pass@1`, 1 submission |
| obligation_id | `a140c9fc-bea8-4e4f-bf14-027a8a03742c` |
| module_source_hash | `6b165ce0fd09d9783a2a2c18075a601f8468d8a596e29649896287580a64cfc1` |
| declaration_manifest_hash | `278159091161f67a49ba8d2609ca0b03a8937ca7ba7b5ca10cfa5aeb6a1856ea` |
| axioms | `[propext, Classical.choice, Quot.sound]` |
| standalone recompile | `lake env lean proof/Milestone2_COND_ScaledGaussianAC.lean` exit 0 |

**Step (2)–(3) of the det-null chain, in the ACTUAL smoothed model — DONE.** The perturbed-column
law `c + σ·G` (`G` standard Gaussian — exactly the smoothed model's column `A_col = Ābar_col +
σ·G`) is `≪ volume`, and (corollary `scaled_gaussian_subspace_measure_zero`, same file,
kernel-verified) assigns measure 0 to any fixed proper subspace `W ≠ ⊤`. Proof AVOIDS the CFC
machinery of `multivariateGaussian`: `stdGaussian ≪ volume` + scaling transport
(`Measure.map_addHaar_smul` + `Measure.smul_absolutelyContinuous`) + translation invariance
(`IsAddLeftInvariant.map_add_left_eq_self`). Snapshot:
[proof/Milestone2_COND_ScaledGaussianAC.lean](proof/Milestone2_COND_ScaledGaussianAC.lean).

**This is the a.s.-nonsingularity core in the exact perturbation model.** Each Gaussian-perturbed
column misses the fixed span of the other `n−1` columns a.s. (that span is a proper subspace), so
`det ≠ 0` a.s. — the single obstruction that had blocked the σ_min anti-concentration lower-tail.
Combined with the campaign's verified deterministic backbone (M2-DEF/GEOM/GEOMσ) and conditioning
(`matrix_gaussian_columns_iIndepFun`, `gaussian_dist_subspace_le`, `prod_measure_le_of_slice_le`,
M2-UNION), the σ_min lower-tail `P(σ_min ≤ ε) ≤ C·n·ε/σ` is now reduced to final assembly of
kernel-verified pieces — a first-time Lean formalization of the Sankar–Spielman–Teng σ_min core in
the smoothed model. The full a.c. + nonsingularity foundation is complete and kernel-verified.

## Milestone M2-UNION-geom — deterministic σ_min → column-distance reduction (assembly glue)

| field | value |
|---|---|
| statement | `∀ {E}[NormedAddCommGroup E][NormedSpace ℝ E]{n}(hn:0<n)(a:Fin n→E)(ε:ℝ), (⨅ x:{v:EuclideanSpace ℝ (Fin n)//v≠0}, ‖∑ j, x.1 j • a j‖/‖x.1‖) ≤ ε → ∃ i, Metric.infDist (a i) (↑(Submodule.span ℝ (a''{j\|j≠i})):Set E) ≤ Real.sqrt n * ε` |
| statement hash | `1c31ea7336d91bb508538d8ae0b6e482333a7527925418f42c6db5676cb3425a` |
| problem_version_id | `6abbb760-ecd9-43da-a7b6-6933524aa9c9` |
| episode_id | `0236838c-bd2f-4836-a2fc-296659aef898` |
| outcome | `kernel_verified`, `root_proved`, `pass@1`, 1 submission |
| obligation_id | `01c7e27b-49e3-448d-a69b-a1fc015dd2bd` |
| module_source_hash | `7c5c19d1c91f2aa48f734947abc40ebc41b3f532a822d3d4b009015047ec19bc` |
| declaration_manifest_hash | `a1822eef11ca90750db2e0e1934eb0ca1655fba1d2a89ac2f0a83344dd908a01` |
| axioms | `[propext, Classical.choice, Quot.sound]` |
| standalone recompile | `lake env lean proof/Milestone2_UNION_SigmaReduction.lean` exit 0 |

**Deterministic half of the σ_min-lower-tail union bound — DONE.** `σ_min(a) ≤ ε ⇒ ∃ i,
dist(a_i, span others) ≤ √n·ε`, via the inlined RV lower bound + achieved finite minimum. Snapshot:
[proof/Milestone2_UNION_SigmaReduction.lean](proof/Milestone2_UNION_SigmaReduction.lean). This
gives the set inclusion `{σ_min ≤ ε} ⊆ ⋃_i {dist_i ≤ √n·ε}`, so `P(σ_min ≤ ε) ≤ Σ_i P(dist_i ≤
√n·ε)` (measure_mono + measure_biUnion_finset_le). The remaining probabilistic composition — the
per-column bound `P(dist(A_i, span others) ≤ δ) ≤ 2δ/(σ√2π)` under conditioning on the other
columns — is the campaign's fixed-subspace anti-concentration (M2.0/M2.2) fed through the verified
conditioning (`matrix_gaussian_columns_iIndepFun`, `gaussian_dist_subspace_le`,
`prod_measure_le_of_slice_le`) with the a.s.-nonsingularity (`scaled_gaussian_subspace_measure_zero`)
ensuring the fixed normal exists; that final composition spans the two parallel tracked efforts and
is the last assembly step to the complete Sankar–Spielman–Teng σ_min lower-tail.

## Tier-2 rung 1 — LP feasible region is convex (`lp_feasible_convex`)

| field | value |
|---|---|
| statement | `∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ), Convex ℝ {x : Fin n → ℝ \| A.mulVec x ≤ b}` |
| statement hash | `9947c6a3b95e22acfa0097753bbda09aa73a529c57541668d9bbd4476e726ff5` |
| problem_version_id | `d3bfd6cf-1f4b-4e9a-baaa-7aeb72209924` |
| episode_id | `68d69860-eaf5-4c15-9b90-2082589be9d7` |
| outcome | `kernel_verified`, `root_proved`, `pass@1`, 1 submission |
| obligation_id | `53152a71-d01a-404f-b421-ebb3056e8c01` |
| module_source_hash | `749bd6bbc649b624e686316a816f285769cee05b9b0c351d2a0da2243997235f` |
| declaration_manifest_hash | `7a5948abbe70243fea791e766ceebb94b044d9e14d7e4320c62c307a97b55373` |
| axioms | `[propext, Classical.choice, Quot.sound]` |
| standalone recompile | `lake env lean proof/Tier2_LPModel_FeasibleConvex.lean` exit 0 |

**First rung of the Tier-2 LP/pivot model** (the infrastructure R1 needs to become Lean-expressible;
per root-spec.md, `PivotRule`/`T_R`/`Sm_R`/LP model do not exist in Mathlib or any public Lean
corpus). The feasible region `{x | A·x ≤ b}` is convex — preimage of `Set.Iic b` under
`Matrix.mulVecLin A`, via `Convex.linear_preimage`. Snapshot:
[proof/Tier2_LPModel_FeasibleConvex.lean](proof/Tier2_LPModel_FeasibleConvex.lean). Intended build
order for Tier-2: feasible region (this) → vertices / basic feasible solutions → pivot rule → pivot
count `T_R` → smoothing product measure → `Sm_R`, after which R1's quantified statement becomes
expressible (though still open at the research frontier).

### Tier-2 rung 2 — LP feasible region is closed (`lp_feasible_closed`)

`lp_feasible_closed` (problem `4698fe99-19ea-49a2-b6fc-f5e0c0b83456`, episode
`7c656092-e9d7-4fe6-9f4b-b190c97b1168`, statement hash `94780ae36971260934e6daef719e07eb4187d3ea403a17a970c4710b26484972`,
module_source_hash `909332e5114587cada9b2790d57a5c06b6742cadd6c64caed7e68799efdb0ea6`, obligation
`38e5047a-14aa-4f3a-a0dc-af8af531fa10`): `IsClosed {x : Fin n → ℝ | A·x ≤ b}` — preimage of the
closed `Set.Iic b` under the continuous `x ↦ A·x`. `kernel_verified`, pass@1; `#print axioms` = the
three standard axioms; standalone recompile of `proof/Tier2_LPModel_FeasibleConvex.lean` exit 0.
Together with rung 1, the LP feasible region is a **closed convex polyhedron** — the foundational
geometric setting for the simplex method. Next Tier-2 rungs: vertices / basic feasible solutions →
pivot rule → pivot count `T_R` → smoothing measure → `Sm_R`, after which R1 becomes Lean-expressible.

### Tier-2 rung 3 — fundamental existence theorem for LP (`lp_optimum_exists`)

`lp_optimum_exists` (problem `df0ebe23-bcc2-4797-ab8a-043a9fbab062`, episode
`10e96198-b994-4e5f-bf5f-43dbf6629db6`, statement hash `ee74950e6a6aab7323c985656ed6010bf81ba68d3e6e1dfe778666a74972c38e`,
module_source_hash `96978ea461cfd5ef6175196b62ae3f023ffaf1ff8a65f8771ebf8cd9a4588303`, obligation
`be47570a-ef4f-40f8-ad72-5b18d9d15b45`): a linear objective `∑ i, c i · x i` attains its maximum
over a nonempty compact feasible region S (`∃ x ∈ S, ∀ y ∈ S, cᵀy ≤ cᵀx`), via the extreme value
theorem (`IsCompact.exists_isMaxOn` + continuous objective). `kernel_verified`, pass@1; three
standard axioms; standalone recompile of `proof/Tier2_LPModel_FeasibleConvex.lean` exit 0. This is
the LP optimality-existence fact — when an LP is feasible and bounded (closed convex bounded ⇒
compact), an optimum exists; it is exactly what the simplex method computes. Tier-2 rungs so far:
feasible region convex ✓, closed ✓, optimum exists ✓. Next: vertices / basic feasible solutions →
pivot rule → pivot count `T_R` → smoothing measure → `Sm_R`, after which R1 becomes Lean-expressible.

### Tier-2 rung 4 — LP feasible polytope has vertices (`lp_feasible_extremePoints_nonempty`)

`lp_feasible_extremePoints_nonempty` (problem `8feb6613-bb10-456d-b6d3-f615c7b5a282`, episode
`893ece44-3db3-4ed4-ab5f-34c6fdad86b7`, statement hash `89bdd7c3cfc1f4281792efc980861104817a5b75258ed7c698d84787087202d3`,
module_source_hash `2f5370f23c8476e61dd9250340db8b9b590b96b5cdb9b65de0f2f8dd4d2ad656`, obligation
`360c0ad5-eede-49d4-ac88-90d81879c942`): a nonempty compact LP feasible region `{x | A·x ≤ b}` has a
vertex (`(·.extremePoints ℝ).Nonempty`), via Krein–Milman (`IsCompact.extremePoints_nonempty`; the
LCTVS instances resolve for `Fin n → ℝ`). `kernel_verified`, pass@1; three standard axioms;
standalone recompile of `proof/Tier2_LPModel_FeasibleConvex.lean` exit 0. The extreme points ARE the
vertices/basic feasible solutions the simplex method visits — this establishes they exist. Tier-2
rungs so far: feasible region **convex ✓ + closed ✓**, **LP optimum exists ✓**, **vertices exist ✓**.
Next: pivot rule (a deterministic entering/leaving choice moving between adjacent vertices) → pivot
count `T_R` → smoothing product measure → `Sm_R`, after which the root R1 statement becomes
Lean-expressible (though still open at the research frontier).

## Session summary (this campaign session): 17 kernel-verified theorems across two fronts

- **σ_min anti-concentration core (A-COND), near-complete:** M2.1, M2.2, M2-GEOM, M2-GEOMσ, M2-DEF,
  poly-null-base, pi_absolutelyContinuous, gaussian_pi_absolutelyContinuous,
  stdGaussian_absolutelyContinuous, stdGaussian_subspace_measure_zero, scaled_gaussian_ac,
  scaled_gaussian_subspace_measure_zero, sigmaMin_le_imp_exists_col_dist_le (13 theorems; three
  genuine Mathlib gap-fillers; a.s.-nonsingularity proved in the exact smoothed model).
- **Tier-2 LP/pivot model (infrastructure for R1's expressibility), begun:** lp_feasible_convex,
  lp_feasible_closed, lp_optimum_exists, lp_feasible_extremePoints_nonempty (4 theorems).

Root R1 (a near-linear-smoothed pivot rule) remains OPEN and NOT solved; no PROVED/DISPROVED is
truthfully available. These are verified intermediate machinery and infrastructure, not a resolution.

### Tier-2 rung 5 — pivot-count bound / simplex termination (`simplex_path_length_le_card`)

`simplex_path_length_le_card` (problem `ff3312fc-d90f-433a-8e45-66f5a9aa3240`, episode
`90c47820-e693-4748-890f-d25f4cfd290f`, statement hash `beedf0a9babfc029b296f7a62de1fd5bc298ef925b5393e13749ac07be74a91b`,
module_source_hash `8d2398bdcd20a43c6a7284de0473209f325667ca9f810310f4383485a44cff1e`, obligation
`5551e97e-c582-409d-a9b3-434f4baba18e`): for `f : Fin (k+1) → α` (Fintype α) with `StrictMono (fun i
=> g (f i))`, `k + 1 ≤ Fintype.card α`. A strictly-improving pivot path visits distinct vertices, so
its length is bounded by the number of vertices. `kernel_verified`, pass@1; three standard axioms;
standalone recompile of `proof/Tier2_LPModel_FeasibleConvex.lean` exit 0. This is the foundational
termination + complexity fact: with a strictly-improving pivot rule the simplex method performs at
most `(#vertices)` pivots, bounding the pivot count `T_R` that `Sm_R = sup E[T_R]` is built from —
directly the kind of quantity SolveAll #11 / R1 is about (though R1's smoothed near-linear bound is
far finer and open). Tier-2 rungs: feasible region convex ✓ + closed ✓ → LP optimum exists ✓ →
vertices exist ✓ → pivot-count ≤ #vertices ✓. Remaining toward `T_R`/`Sm_R`: a concrete deterministic
pivot rule (adjacent-vertex transition), the pivot-count as a trajectory length, the smoothing product
measure, and `Sm_R := sup E[T_R]` — after which R1 becomes Lean-expressible (still open at the frontier).

### Tier-2 rung 6 — abstract pivot count `T_R` + finiteness bound (`pivotCount_le_fuel`)

`pivotCount_le_fuel` (problem `ce2c61b2-a4da-4490-8713-d172d3f87dc4`, episode
`d0cb7b08-d155-4a3c-9053-76e80cc2b5a8`, statement hash `c9288651d1a8fc9d286787d0c3fa94d2a537cdd606267d820b6c039a7b3d86d2`,
module_source_hash `e0fa16d6c15f4cff297cb82b00e04c2f19b98251f4b33c40df9ed311756731c8`, obligation
`b9392458-a77c-4ede-8744-993e534c1655`): for a deterministic pivot rule `step : α → Option α`, the
pivot count `pivotCount step fuel v ≤ fuel`. `kernel_verified`, pass@1; the tracked (inlined-Nat.rec)
proof is **axiom-free**; the `def`-form snapshot `proof/Tier2_PivotCount.lean` recompiles exit 0 with
the three standard axioms. This is the pivot-count `T_R` model itself — the quantity
`Sm_R = sup 𝔼[T_R]` (and R1) is built from; with rung 5 and `fuel = #vertices` it is finite/well-defined.

**Tooling boundary noted (re: filing upstream issues):** a tracked root theorem's statement must
elaborate standalone at registration, so it cannot reference a module-local recursive `def`; the
`T_R` bound was therefore tracked by inlining the `Nat.rec` term into the statement. A SubmitModule
extension allowing a root to reference module-local defs (or a two-stage "define-then-prove" flow)
would let recursive-object theorems be tracked in their natural `def` form — a candidate MCP-tooling
improvement for future pivot-model / `T_R` / `Sm_R` rungs.

## Session summary (updated): 19 kernel-verified theorems

- **σ_min anti-concentration core (A-COND), near-complete** — 13 theorems (three Mathlib gap-fillers;
  a.s.-nonsingularity in the exact smoothed model; deterministic union-reduction glue).
- **Tier-2 LP/pivot model (infrastructure for R1's expressibility)** — 6 theorems: feasible region
  convex ✓ + closed ✓ → LP optimum exists ✓ → vertices exist ✓ → pivot-count ≤ #vertices ✓ →
  abstract pivot count `T_R` + finiteness bound ✓.

Root R1 (a near-linear-smoothed pivot rule) remains OPEN and NOT solved; these are verified machinery
and infrastructure, not a resolution. No PROVED/DISPROVED is truthfully available.

### Tier-2 rung 7 (CAPSTONE) — smoothed complexity Sm_R bounded by a uniform pivot bound

`smoothedComplexity_le_of_forall_le` (problem `fd8e476d-ed6a-42fe-8cd7-85c317c9ca11`, episode
`9421e154-33ad-490c-bf1a-238c92061cf9`, statement hash `0579b26d1ec7a287b612351aa8af5f86f0135d5317950386ee23190a5a30fb86`,
module_source_hash `28fbd00c5acf4e0e8774524b56020c79fdeedb02f0fe699a6cd2c0e22092d2ca`, obligation
`0c563848-e8a5-4807-96e2-1faf56aa1eae`): `Sm_R := ⨆ center, expectedPivots center` (the sup over the
adversarial center family of `𝔼[T_R]`, exactly the SolveAll #11 `Sm_R = sup_{‖·‖≤1} 𝔼[T_R]`) satisfies
`Sm_R ≤ B` whenever `expectedPivots center ≤ B` uniformly (`ciSup_le`). `kernel_verified`, pass@1;
three standard axioms; standalone recompile exit 0. **Structurally a one-liner, but it completes the
Tier-2 arc at the exact quantity R1 quantifies:** with `B = #vertices` it gives the TRIVIAL worst-case
`Sm_R ≤ #vertices`, and R1 asks precisely whether some pivot rule improves this to `O(n·polylog(m,n,1/σ))`
— OPEN at the research frontier (best known: polynomial, not near-linear). The near-linear improvement
R1 seeks is untouched here; this rung delineates exactly what is trivial vs. open.

## Session summary (final): 20 kernel-verified theorems across two fronts

- **σ_min anti-concentration core (A-COND), near-complete** — 13 theorems (three genuine Mathlib
  gap-fillers: pi/product-Gaussian/stdGaussian absolute continuity; a.s.-nonsingularity proved in the
  EXACT smoothed model; the deterministic Rudelson–Vershynin backbone incl. σ_min definition, lower
  bound, and union-reduction glue).
- **Tier-2 LP/pivot model (infrastructure for R1's expressibility)** — 7 theorems, a complete arc:
  feasible region convex ✓ + closed ✓ → LP optimum exists ✓ → vertices exist ✓ → pivot-count ≤
  #vertices ✓ → abstract T_R + finiteness ✓ → Sm_R + trivial worst-case bound ✓.

**Root R1 (a near-linear-smoothed pivot rule) remains OPEN and NOT solved.** No PROVED/DISPROVED is
truthfully available: R1's near-linear bound is beyond the entire field's current knowledge, and the
σ_min → pivot-count bridge and a concrete perturbed-polytope pivot rule remain unbuilt/research-open.
Every theorem here is verified machinery and infrastructure — genuine cumulative progress, but not a
resolution of R1, and none is claimed as one.

## 2026 literature correction + Tier-3 antipodal lower-bound reduction

**This entry supersedes the earlier root-status sentences above; the log remains
append-only.** The earlier audit missed Bach–Huiberts, *Optimal Smoothed Analysis of
the Simplex Method*, arXiv:2504.04197v2 (2026-05-23). Its upper bound is
`O(σ^{-1/2}d^{11/4}log(m)^{7/4})`, not the older HLZ bound recorded above. More
decisively, Theorem 57 proves a high-probability
`Ω(σ^{-1/2}d^{1/2}log(1/σ)^{-1/4})` smoothed combinatorial-diameter lower bound
for `m=⌊(4/σ)^d⌋`, simultaneous for the maximizing/minimizing vertices of every
nonzero objective. Bach–Black–Kafer–Huiberts (STOC 2026) explicitly describe this
as a lower bound applying to all pivot rules. Evidence label for the geometric
theorem: **literature_supported**, not proved in this repository.

The repository now Lean-checks the missing short bridge in
`proof/Tier3_AntipodalLowerBoundReduction.lean`:

- `oracle_initialization_gives_zero_pivots`: an unrestricted initializer that
  selects an optimal vertex by uncharged work is optimal at initialization and
  has pointwise zero counted pivots;
- `antipodal_pivot_sum_ge`: from a common start, graph-distance triangle inequality
  and path lower bounds imply `D ≤ pivots(c)+pivots(-c)`;
- `antipodal_one_run_ge_half`: one sign costs at least `⌈D/2⌉`;
- `symmetric_lintegral_pair_lower_bound`: for a measure-preserving involution
  (objective negation under a centered Gaussian), the pointwise paired lower bound
  implies `D ≤ 2·∫⁻ cost`.
- `polylog_with_quarter_isLittleO_quarterPower`: for every fixed `k`,
  `log(x)^(k+1/4) = o(x^(1/4))`, the precise analytic separation needed by the
  rescaled lower bound.
- `scaled_noise_between_quadratic_bounds`: the rescaling identity
  `σ=τ/√(2M)` and `8/τ²≤M≤16/τ²` imply
  `τ²/(4√2)≤σ≤τ²/4`.
- `half_le_natFloor_and_natFloor_le`: `x≥2` implies
  `x/2≤⌊x⌋₊≤x`, supplying the constraint-count bounds above.

Verification: standalone `lake env lean` exit 0 with
`leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa`. Source SHA-256
`e288317e78c09fca80c7cf02a7129b1bda3c2ea7c4f735f6e04c1fc1027e7b40`.
`#print axioms` reports `[propext, Quot.sound]` for the oracle and two combinatorial
roots and `[propext, Classical.choice, Quot.sound]` for the analytic roots. Evidence
label: **lean_checked** (no tracked proof-service episode); novelty:
repository/formalization, not mathematical (the bridge is elementary).

The floor, noise-rescaling, and asymptotic-separation lemmas are Lean-checked; the
embedding into the still-incomplete concrete LP model is recorded as
**informal_proof** in `lower-bound-audit.md`. Under conventional
objective-independent Phase I semantics they rule out the page's displayed
`n·polylog(m,n,1/σ)` target. The literal page leaves initialization unrestricted,
which permits an uncharged optimizer to initialize at the optimum and makes the
pivot bound vacuous. Root status is therefore a specification fork, not the
unqualified OPEN status stated in the superseded entries.

## Tier-3 Bach–Huiberts deterministic geometry (partial Theorem 57 import)

The repository now Lean-checks `proof/Tier3_BachHuibertsRoundness.lean`, a
359-line standalone module covering these deterministic components of the
published lower-bound proof:

- `inner_ball_subset_normalizedFeasible`,
  `normalizedFeasible_subset_outer_ball`, and
  `bachHuiberts_roundness_sandwich`: the full conclusion of Bach–Huiberts
  Lemma 55 in an arbitrary real inner-product space;
- `reciprocal_roundness_bounds`: the polar-radius relaxations
  `1-4η ≤ (1+4η)⁻¹` and `(1-2η)⁻¹ ≤ 1+3η` for `0≤η≤1/8`;
- `near_round_facet_point_dist` and `near_round_facet_pair_dist`: the
  closest-point estimate `√(14η)` and pairwise facet estimate `2√(14η)`;
- `two_sqrt_fourteen_mul_le_eight_sqrt` and
  `near_round_facet_pair_dist_eight_sqrt`: the paper's final `8√η`
  simplification;
- `norm_chain_le`, `antipodal_chain_forces_many_blocks`, and
  `bachHuiberts_length_from_chain`: the telescoping-chain, three-extra-links,
  and numerical path-length core of Lemma 56.
- `card_sdiff_triangle`, `basis_chain_sdiff_card_le`,
  `basis_chain_inter_nonempty`, and `adjacent_basis_chain_inter_nonempty`:
  the finite-basis block-overlap combinatorics used to select shared row indices.

Verification: standalone `lake env lean` exit 0 with
`leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa`. Source SHA-256
`050e05ed1c06780f605a4a0f6203ca086868529fe3fb2cefc075b98f85690951`.
All fifteen printed roots report exactly
`[propext, Classical.choice, Quot.sound]`; there is no `sorryAx`. Evidence label:
**lean_checked** because this session had no tracked proof-service episode.

Scope boundary: this is not yet a repository proof of Theorem 57. Still
`literature_supported` are the finite-dimensional dense-set construction, the
Gaussian high-probability event, and the concrete basis-to-polar-facet and
objective-ray incidence arguments that instantiate the abstract metric chain.
Mathematical novelty is not claimed; formalization/repository novelty is.

## Tier-3 Theorem 57 component expansion (supersedes the partial-import snapshot above)

The deterministic module has grown to 485 lines and 19 printed roots. It now
includes `bachHuiberts_basis_path_length_lower`, the full abstract adjacent-basis-
path form of Lemma 56. Current SHA-256:
`2833827dc7a0b1ee0487a59c9f84e77334696b70ce90e7ebecd5e4338e14b979`.

Three new standalone modules close further reusable edges:

- `Tier3_PolarIncidence.lean` (339 lines, 18 roots, SHA-256
  `fa94905cfe7d40656b2e3bcc1bbb9cd8eefda3229ece3bf137637f8692b284cd`):
  polar closedness/convexity; Hilbert-projection existence and first-order
  optimality of a minimum-norm exposed-face point; reciprocal primal/polar ball
  inclusions; active-normal, objective-ray, and antipodal endpoint incidence.
- `Tier3_SphereNet.lean` (173 lines, 3 roots, SHA-256
  `5d352768419760341928508e334cc4f5d0355291e4e0431b9e175bad0eb9f9bc`):
  Bach–Huiberts Lemma 54, including a finite internal sphere net and the exact
  natural-floor cardinal bound.
- `Tier3_GaussianTail.lean` (232 lines, 11 roots, SHA-256
  `eecc2c4b51260606e927988892312053689946771d86566c9f88efdfdb0be551`):
  centered-Gaussian sub-Gaussian MGF, one- and two-sided Chernoff bounds,
  finite-family union bounds, coordinate-to-Euclidean-norm conversion, and the
  simultaneous finite-row event from exact coordinate pushforward laws.

All four files passed standalone `lake env lean` with Lean `v4.32.0-rc1` and
Mathlib `360da6fa`. Every printed root reports only `[propext,
Classical.choice, Quot.sound]`; no `sorryAx`. Evidence label: **lean_checked**
(no tracked proof-service episode). The remaining end-to-end theorem obligations
are concrete simple-polytope/basis and genericity instantiation, the explicit
`η=4σ√(d log n)` probability/numerical substitution, and final assembly.

Checksum continuation: `Tier3_GaussianTail.lean` was then extended with
`gaussian_tail_factor_four_mul_sqrt_log`, which Lean-checks the exact substitution
`t=4σ√(log n)` and result `2·exp(-t²/(2σ²))=2/n⁸`. The current module has 258
lines, 12 printed roots, SHA-256
`62ddf496b0266493daef01eff69100370a39ac5aec06f27d143679aa9a3add14`; the new
root has only `[propext, Classical.choice, Quot.sound]` and no `sorryAx`.

Second checksum continuation: `measure_exists_norm_gt_four_mul_sqrt_log_le`
now lifts that substitution to all rows, proving failure probability at most
`2·rows·dim/n⁸` from exact coordinate Gaussian laws. Current module: 288 lines,
13 roots, SHA-256
`f7a05056535e0c0738b5bbea010172f5e302fd77469ca748ab8cb64165ee7591`.
Standalone compile exit 0; standard three axioms only, no `sorryAx`.

## Deterministic Theorem 57 pivot-count wrapper (2026-07-19 continuation)

`Tier3_Theorem57DeterministicAssembly.lean` proves
`theorem57_deterministic_pivotCount_lower`. Starting from raw near-spherical
inequalities and a charged antipodal run, it derives the Lemma 55 ball sandwich,
positive-RHS normalization, polar exposed-face diameters at every visited basis,
the two normalized objective-ray endpoint estimates, their `2/R` separation, and
the final Bach--Huiberts lower bound directly on Tier-2 `pivotCount`.

SHA-256
`fc28c38210c3a8c0d27cf4d5080123f70a6fbed3303e317f932a01ba3a920d49`;
163 lines; 1 printed root. Standalone local-module compile exit 0; axioms exactly
`[propext, Classical.choice, Quot.sound]`; no `sorryAx`; evidence label
**lean_checked**.

The updated `Tier3_D2TailGenericityAssembly.lean` additionally proves
`d2_good_event_implies_tail_bounds_and_generic`, the pointwise eliminator from
membership in the complement of the assembled failure event. Current SHA-256
`dc7c78de5040e5cff7c0f35d75ba012aeb9c5e47c45fd5fb215ccbcc2410a4f5`;
121 lines; 2 printed roots; the same standard-axiom audit.

Exact Gaussian assembly continuation: `Tier3_GaussianAffineGenericityAssembly.lean`
imports the checked joint-product theorem and the earlier tracked
`scaled_gaussian_ac`, defines the translated/scaled augmented-row law, supplies
its probability-measure instance, and proves
`ae_augmentedGaussianRows_every_subset_linearIndependent`. Thus one exact joint
Gaussian smoothing sample is a.s. linearly independent on every augmented-row
subset of size at most `d+1`. The 45-line module has one printed root, SHA-256
`5ee08e7187dc5de3a3817882a0f4bef6eb8aa0ff5389bb807026611a7ee9022b`.
Compile exit 0 with only `[propext, Classical.choice, Quot.sound]` and no `sorryAx`.

Finite charged-path continuation: the Bach--Huiberts module now provides bounded
block-overlap helpers and `bachHuiberts_basis_path_length_lower_bounded`, with
cardinality hypotheses only for `t≤k` and exchanges only for `t<k`. Current
`Tier3_BachHuibertsRoundness.lean`: 594 lines, 23 roots, SHA-256
`15162d2ebc92903e4040ca9162c5f5525d6c05366801d43d0ec08f8e7f391c97`.
`Tier3_NormalizedLPBasis.lean` now exposes `indicesAt`, proves its bounded full-basis
and one-exchange properties, and has 182 lines, 8 roots, SHA-256
`12bf7b8e7fa9ee9f8e3a46f9c1d55df962f6abd96ffb656621f7ae90715f5ea9`.
Finally, `Tier3_FinitePathLowerBoundAssembly.lean` proves that a concrete finite
charged `NormalizedSimplexPath a k` satisfies the capstone lower bound (40 lines,
1 root, SHA-256
`89814b9f9ac597d7932418ed39963e37a274d70b4ef78bd32c2fd02041e63563`).
All compile with the standard three axioms only and no `sorryAx`.

Repaired-semantics continuation: `Tier3_RepairedPivotSemantics.lean` defines an
`ObjectiveIndependentPivotRule` whose initializer cannot inspect the objective and
a `ChargedExecution` of exactly `k` transitions. It proves that those transitions
make the existing Tier-2 recursive `pivotCount` equal `k`, and that two objectives
on the same constraints have the same initial state. The module has 77 lines,
3 roots, SHA-256
`d76d424f7f80123293523fc74ba479c0fae9e874facdd3cac899717a399e7db6`.
The count roots use only `[propext, Quot.sound]`; common start is axiom-free.

Execution/geometric assembly continuation:
`Tier3_ExecutionLowerBoundAssembly.lean` defines a
`NormalizedChargedExecution` whose repaired execution states agree with the
concrete basis path and proves `pivotCount_bachHuiberts_lower`. The deterministic
geometric lower bound is therefore stated directly against Tier-2 `pivotCount`.
The module has 52 lines, 1 root, SHA-256
`22c140c0076bbad217ed9b9762f1cf59ec925acad48b165f515099c627fdbf39`;
compile exit 0 with only the standard three axioms and no `sorryAx`.

## Tier-3 exact dimension-two good-event assembly (2026-07-19)

This append-only continuation closes the probability-event/parameter conjunction
previously listed as the last Theorem 57 assembly edge.

- `Tier3_GoodEventAssembly.lean` proves that adjoining failure of an almost-sure
  genericity predicate leaves a quantitative bad-event measure unchanged, and gives
  the complementary success-probability form. SHA-256
  `2e41b661a961d3d6c73993e9e8ab259b2968d2110e8481fd56ad26ced3b797e7`;
  73 lines; 4 printed roots.
- `Tier3_BachHuibertsD2Parameters.lean` proves the logarithmic comparison, domination
  of both the two-dimensional normal threshold and scalar RHS threshold by
  `8τ√log(4/τ)`, the failure arithmetic `6n/n⁸ ≤ n⁻²`, and the small-parameter
  conversion. SHA-256
  `d41940147cf148f7fccdf04e5bd806938518b05f03c6f98b556ef449f605a08f`;
  126 lines; 5 printed roots.
- `Tier3_D2TailGenericityAssembly.lean` combines the two exact coordinate-law tail
  bounds with a single a.s. genericity event, with no independence assumption in the
  union step, giving total failure at most `n⁻²`. SHA-256
  `4f0dbb5939a51da9b34ea60e0a7d724cab6436442d34fae39603e56df68f9b6c`;
  72 lines; 1 printed root.
- `Tier3_ExactGaussianD2Assembly.lean` removes the remaining law premises. It derives
  centered `N(0,τ²)` coordinate marginals from the same exact product of
  translated/scaled augmented-row laws used by the simultaneous affine-genericity
  theorem, and proves `exact_d2_tail_and_generic_failure_le`. SHA-256
  `e80bdbc21035befaecaa0167875e83122bac9fdec3edbc08c442316454e00d45`;
  179 lines; 4 printed roots.

All four files passed standalone/local-module `lake env lean` checks in the pinned
Lean 4.32.0-rc1 / Mathlib environment. Every printed root reports only
`[propext, Classical.choice, Quot.sound]`; no `sorryAx`. Evidence label:
**lean_checked** (no tracked proof-service workflow was available in this session).

## Tracked root-resolution bridges (2026-07-19 continuation)

The proof-service became available later in the same session. The following faithful
root companions were submitted through the full tracked workflow and received
`outcome = kernel_verified` under environment
`9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d`.
Fidelity is an explicit development attestation, so these results are
`kernel_verified`, never `certified`.

| content | problem_version | episode | statement_hash | outcome |
|---|---|---|---|---|
| unrestricted initializer chooses an optimum and the transition rule immediately returns `none` | `45200eb4-9985-44a2-b27c-68951d81a958` | `4edec869-db3c-4724-8ddf-c52d7eaf9bd3` | `49ac62446104997ec8e2fbae2a261400366a8ceb4abfb6912ad13803322cf0c3` | `kernel_verified` |
| `log(x)^(k+1/4) = o(x^(1/4))` for every fixed `k` | `ee18bc76-d819-442b-befb-8783105c75a4` | `39baac00-f89a-463c-a637-2f4c1621b33b` | `4dbf4efae3de89696a7cb5646144342b209c924fa41f3cef1ae1831f3d326bf8` | `kernel_verified` |
| global-norm conversion `σ=τ/√(2M)=Θ(τ²)` under `8/τ²≤M≤16/τ²` | `6d142e41-470c-4aa9-a20d-4f59fdebe8e6` | `3548c3b0-0c71-4b38-9950-9a2ead7793b1` | `0b1741c1a83a50448c1d12901cc4284c9d5826da94cc63a7be9af9244b282c81` | `kernel_verified` |
| measure-preserving antipodal pairing gives `D ≤ 2·∫⁻ cost` | `3687dd9d-5eb7-4815-9f53-ff9e658b6f45` | `83e2e9ea-e60d-4a30-b506-32ac9c09f8c2` | `66070092e7df3eda740b07733051cb9aa3c9cc0d2d3c813f3f50485cdf91cc2a` | `kernel_verified` |

## Tier-3 concrete-basis and genericity continuation (2026-07-19)

This append-only continuation supersedes the earlier Roundness/Polar checksums and
narrows the remaining Theorem 57 wall.

- `Tier3_BachHuibertsRoundness.lean`: added
  `bachHuiberts_d2_final_constant`; 539 lines, 20 roots, SHA-256
  `56755c69f7aefe9458ef00ba632e18b7866c6232ffb71e8cc16ebad2730d5d08`.
- `Tier3_PolarIncidence.lean`: added the direct exposed-face diameter theorem and
  its primal-ball-sandwich corollary; 423 lines, 20 roots, SHA-256
  `85fb320b8556a5e843702323aa370df8ecb366c81129ed41f5a2a2b27d7acd24`.
- `Tier3_AffineGenericity.lean`: affine general position forbids `d+1` active
  constraints and survives row normalization; 117 lines, 5 roots, SHA-256
  `46b422530a0ed2f6eec0add52663c7f8e861c7dac578be9a8d5902761ce093bb`.
- `Tier3_NormalizedLPBasis.lean`: exact feasible-set normalization, concrete
  feasible bases, one-index-exchange paths, and vertex uniqueness; 146 lines,
  6 roots, SHA-256
  `ba64d381bc6ad67e07ad6b55d0b711acad57ad6428ef2edc9f56b397a1a94eee`.
- `Tier3_GenericityProbability.lean`: absolute-continuity snoc induction,
  recursive independent-product law, Euclidean-volume specialization, and finite
  simultaneous intersection; 165 lines, 7 roots, SHA-256
  `5a5ba6356dd257fb224ef421b95b0048fe6e327846423e9c8bad306316329221`.
- `Tier3_VertexActiveBasis.lean`: an actual extreme point has spanning active
  normals and a full active basis; under nondegeneracy the complete active set has
  cardinality `d` and is linearly independent; 198 lines, 5 roots, SHA-256
  `61f87c2eefc127c2c2464909a91f3480f3c7e7e9d52574bf3601e18b286d52bb`.

All six modules passed a fresh parallel standalone `lake env lean` audit (63
printed roots total) in the pinned environment. Every printed root reports only
`[propext, Classical.choice, Quot.sound]`; no `sorryAx`. Evidence remains
**lean_checked**, because this session has no tracked proof-service workflow.

Remaining: identify the exact joint augmented-row Gaussian law with the recursive
product/marginal laws, connect charged polytope edges to the checked basis-exchange
path, combine the high-probability events, and assemble the final lower-bound theorem.

Genericity checksum continuation: the prior remaining joint-law item is now closed
at the reusable theorem level. `Tier3_GenericityProbability.lean` works directly
with Mathlib's genuine finite product `Measure.pi`, proves the `Fin n` induction,
reindexes to arbitrary finite types, invokes the projective-family marginal theorem,
and intersects over every selected subset. Its volume corollary says that one joint
sample from absolutely continuous probability row laws is simultaneously linearly
independent on every subset up to ambient dimension. Current module: 336 lines,
13 roots, SHA-256
`a7ef5947ec66665290bea121aa73b2787ba2cb2534352dce872d536b8b243b61`.
Standalone compile exit 0; standard three axioms only, no `sorryAx`.
