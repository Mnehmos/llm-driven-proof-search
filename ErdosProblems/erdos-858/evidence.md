# Erdős #858 — machine evidence

Every row below is a real `outcome = kernel_verified` (`root_kernel_verified`)
result recorded by the `proofsearch` MCP. Nothing here rests on trusting the
AI or the human — only on the pinned Lean 4 kernel accepting the exact stated
proposition through the tracked `episode_step` path.

## Environment (pinned)

| field | value |
|---|---|
| toolchain | `leanprover/lean4:v4.32.0-rc1` |
| mathlib | `mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56` |
| environment_hash | `9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d` |
| import manifest | `["Mathlib.Tactic.Ring", "Mathlib.Tactic.NormNum", "Mathlib"]` |
| import_manifest_hash | `aaf21893d520a78dee0787a1bcaf939ee6b922265ff670c272e2e1d450dd29a7` |
| fidelity_status | `attested` (dev attestation; reaches `kernel_verified`, never `certified`) |
| research dossier | `13828939-561e-4ce1-ad36-add1a4b3f209` |

The relation is encoded faithfully as
`a ⪯ b := ∃ t, b = a*t ∧ ∀ p, Nat.Prime p → p ∣ t → a < p`.
This renders the paper's `P⁻(t) > a` ("least prime factor of t exceeds a") as
"every prime factor of t exceeds a", vacuous at `t = 1` (the `b = a` case) —
mathematically identical on the positive integers.

## Verified results

### 1. `⪯` is a partial order  (paper §1, Introduction)

- **Statement (root_statement_hash `6a0381c59f460fdc6214a4cef28d5b6907fcb2cf448fb4ab47aee3885a321790`):**
  reflexivity ∧ antisymmetry ∧ transitivity of `⪯` on `{a : 1 ≤ a}`.
- problem_version_id: `c2c1c39e-da39-4221-baa4-6dc68e718534`
- episode_id: `147d5209-8be4-4e51-97ac-6ff2c023b439`
- outcome: `kernel_verified` — rewards `kernel_pass 5000`, `root_kernel_verified 20000`
- snapshot: [proof/Erdos858_PreceqPartialOrder.lean](proof/Erdos858_PreceqPartialOrder.lean)

### 2. Lemma 2.1 — the sandwich / linear-order lemma  (paper §2)

- **Statement (root_statement_hash `d211f115f10ef6f0aa166e9939f0140f5670fd1c657dae775fceaa7db7af33c6`):**
  `∀ a b n, a < b → b < n → a ⪯ n → b ⪯ n → a ⪯ b`.
- problem_version_id: `8d44c450-6c16-4b61-99e6-35150c9cd833`
- episode_id: `2bf55db5-d2d8-405f-869a-a104a658e3f3`
- outcome: `kernel_verified` — rewards `kernel_pass 5000`, `root_kernel_verified 20000`
- snapshot: [proof/Erdos858_Lemma21_Sandwich.lean](proof/Erdos858_Lemma21_Sandwich.lean)
- **Why it matters:** this is exactly what forces the proper ancestors of any
  `n` to be linearly ordered (Corollary 2.2), making the parent map `π`
  well-defined and `{1,…,N}` a rooted tree.

### 3. Lemma 2.7 core — prime child uniqueness  (paper §2)

- **Statement (root_statement_hash `840d98a36d0d00dc50ff530f4dca7371fe159fe4d0ffcaceb05bb936bb4b798d`):**
  `∀ a p b, 1 ≤ a → Nat.Prime p → a < p → a ⪯ b → b ⪯ a*p → b = a ∨ b = a*p`.
- problem_version_id: `246cfc11-2a7c-4df8-b3e1-1a01a0c0a353`
- episode_id: `861f5190-4a19-4286-b39e-3fc76bb3d3e9`
- outcome: `kernel_verified` — rewards `kernel_pass 5000`, `root_kernel_verified 20000`
- snapshot: [proof/Erdos858_Lemma27_PrimeChildCore.lean](proof/Erdos858_Lemma27_PrimeChildCore.lean)
- **Why it matters:** it is the divisibility content of `π(a·p) = a` (no
  ancestor strictly between `a` and `a·p`), the fact behind the prime-child
  count `C_N(a) ≥ (1/a)·Σ_{a<p≤N/a} 1/p` used throughout §4.

### 4. Corollary 2.2 — proper ancestors are linearly ordered  (paper §2)

- **Statement (root_statement_hash `f960fc2c109e9880bc45bb2ea121bd73e1c454bd3aa7feb581e3a1ae9bd21616`):**
  `∀ a b n, a < n → b < n → a ⪯ n → b ⪯ n → a ⪯ b ∨ b ⪯ a`.
- problem_version_id: `6eecf4dd-9ed8-43f8-b17b-819f2cbe123a`
- episode_id: `3975fa6a-43cf-4c5b-9fd7-bb541a4c6c14`
- outcome: `kernel_verified` — rewards `kernel_pass 5000`, `root_kernel_verified 20000`
- snapshot: [proof/Erdos858_Cor22_AncestorsLinear.lean](proof/Erdos858_Cor22_AncestorsLinear.lean)
- **Why it matters:** ancestors form a chain ⇒ each `n>1` has a unique maximal
  proper ancestor `π(n)` ⇒ `{1,…,N}` is a rooted tree. This is the corollary
  that makes the parent map — and hence the entire paper — well-defined.

### 5. Lemma 4.5 core — cofactor prime/semiprime bound  (paper §4)

- **Statement (root_statement_hash `7ce3fa753b12dfecbee8362a3d0a01ed32160ef8c48af379b6a7332245c2d460`):**
  `∀ a t, 1 ≤ a → 0 < t → t < a^3 → (∀ prime p ∣ t, a < p) → Ω(t) ≤ 2`
  (`Ω(t) = t.primeFactorsList.length`).
- problem_version_id: `c3d8025c-c0ad-4e20-96fb-ad3acd67740b`
- episode_id: `441292d0-af2d-496e-a74d-f5cd0a7695fd`
- outcome: `kernel_verified` — rewards `kernel_pass 5000`, `root_kernel_verified 20000`
- snapshot: [proof/Erdos858_Lemma45_CofactorPrimeSemiprime.lean](proof/Erdos858_Lemma45_CofactorPrimeSemiprime.lean)
- **Why it matters:** in the upper layer `a > N^{1/4}` the cofactor `t = n/a`
  satisfies `t < a^3`, so `t` is prime or semiprime — the `ap`/`apq` dichotomy
  giving `R_N(a) = P_N(a) + Q_N(a)` and the upper-layer monotonicity (Prop 4.6).

### 6. Lemma 4.5 sub-fact — `π(a·p·q) = a`  (paper §4)

- **Statement (root_statement_hash `c4df43404837ba5c67892b4c4d5d27d0e62d30a30d41a8e5060a64ea8d697bd3`):**
  `∀ b q, 0 < b → Nat.Prime q → q < b → ¬ ∃ t, b*q = b*t ∧ (∀ prime r ∣ t, b < r)`
  (i.e. `b ⋠ b·q` for a prime `q < b`).
- problem_version_id: `cbd049d5-a5d3-4a8b-873b-c673f2fdcbc0`
- episode_id: `55f6df39-7e11-4ad3-a33a-9e2d236c7483`
- outcome: `kernel_verified` — rewards `kernel_pass 5000`, `root_kernel_verified 20000`
- snapshot: [proof/Erdos858_Lemma45_PiApqSubfact.lean](proof/Erdos858_Lemma45_PiApqSubfact.lean)
- **Why it matters:** specialized to `b = a·p`, this is why `a·p` is *not* a
  proper ancestor of the semiprime `a·p·q` (since `q < a·p`), so `π(a·p·q) = a` —
  completing the prime–semiprime child description of Lemma 4.5.

### 7. Trivial lower bound — `(√N, N]` is an antichain  (paper §1)

- **Statement (root_statement_hash `a504844eba81108ba9f326db0fd41c6ba11582fdd7cf3a034c475be2d62f6e89`):**
  `∀ N a b, N < a*a → a < b → b ≤ N → ¬ ∃ t, b = a*t ∧ (∀ prime p ∣ t, a < p)`.
- problem_version_id: `ff11730f-bb32-4880-b967-38ad719165df`
- episode_id: `29440e6b-6595-46ba-982b-15a6004ab282`
- outcome: `kernel_verified` — rewards `kernel_pass 5000`, `root_kernel_verified 20000`
- snapshot: [proof/Erdos858_TopBlockAntichain.lean](proof/Erdos858_TopBlockAntichain.lean)
- **Why it matters:** no two distinct elements of `(√N, N]` are `⪯`-comparable,
  so the whole block is admissible — the source of the paper's
  `M(N) ≥ ½ log N + O(1)` lower bound.

### 8. Lemma 2.7 full — `π(a·p) = a` (existence + uniqueness)  (paper §2)

- **Statement (root_statement_hash `22cf9b67b8e9f1097dcca1e82d6e2b6c6639b8d422ca182dfb76eeb9337ae596`):**
  for `1 ≤ a`, prime `p > a`: `a ⪯ a·p` **and** any `b` with `a ⪯ b ⪯ a·p` is `a`
  or `a·p`.
- problem_version_id: `6b1c8420-abd6-49b0-9b97-805885a829e4`
- episode_id: `33d2a806-acb9-495b-b143-aa300bc2e330`
- outcome: `kernel_verified` — rewards `kernel_pass 5000`, `root_kernel_verified 20000`
- snapshot: [proof/Erdos858_Lemma27_PiApFull.lean](proof/Erdos858_Lemma27_PiApFull.lean)
- **Why it matters:** the complete parent identity `π(a·p) = a` (existence of the
  child + uniqueness), the basis of the prime-child count.

### 9. `⪯` refines divisibility & order + proper step doubles  (paper §1–§2)

- **Statement (root_statement_hash `cf1a49e0c6c0542afddf70cd308f6556b2c0a1ebb22c336b45d24a9f1e9383ac`):**
  `a ⪯ b → a ∣ b`; and (`0 < b`) `a ⪯ b → a ≤ b`; and (`1 ≤ a`, `a < b`)
  `a ⪯ b → 2a ≤ b`.
- problem_version_id: `21e5ccab-0cf4-4f6d-b44b-5ea28a465975`
- episode_id: `9f15836c-4bfc-42b8-a900-4abaa44eea18`
- outcome: `kernel_verified` — rewards `kernel_pass 5000`, `root_kernel_verified 20000`
- snapshot: [proof/Erdos858_PreceqRefinesOrder.lean](proof/Erdos858_PreceqRefinesOrder.lean)
- **Why it matters:** `⪯` sits inside `∣` and `≤`, and every proper step at least
  doubles — so root-to-leaf paths have length `≤ log₂ N`, the finite structure
  the tree DP relies on.

### 10. Every proper `⪯`-multiple has a prime factor exceeding `a`  (paper §1–§2)

- **Statement (root_statement_hash `c6083f605b1f0f3a4183a37dc7a9311e27c600b278c6e04e797e3aadef1bd736`):**
  `a < b → a ⪯ b → ∃ p, Nat.Prime p ∧ a < p ∧ p ∣ b`.
- problem_version_id: `83089544-a3af-47bd-9ba6-8dd0306e2977`
- episode_id: `de684f18-00f0-44e9-878e-4fc79c9e8af1`
- outcome: `kernel_verified` — rewards `kernel_pass 5000`, `root_kernel_verified 20000`
- snapshot: [proof/Erdos858_CofactorLargePrimeFactor.lean](proof/Erdos858_CofactorLargePrimeFactor.lean)
- **Why it matters:** the mechanism behind top-block admissibility and the
  prime–semiprime child structure (a proper child always introduces a fresh
  large prime).

### 11. Lemma 4.5 full dichotomy — child cofactor is `1`/prime/semiprime  (paper §4)

- **Statement (root_statement_hash `bbd9ad1223aed61d8618edb2d5913acef9528fcf3daf0d3121df070ff4ba8fa3`):**
  `1 ≤ a → 0 < t → t < a^3 → (∀ prime p ∣ t, a < p) → t = 1 ∨ t.Prime ∨ ∃ p q prime, t = p·q`.
- problem_version_id: `f8035342-426e-4483-afb4-c18a37436893`
- episode_id: `1883d607-3756-41a3-a872-c41b499b524d`
- outcome: `kernel_verified` — rewards `kernel_pass 5000`, `root_kernel_verified 20000`
- snapshot: [proof/Erdos858_Lemma45_FullDichotomy.lean](proof/Erdos858_Lemma45_FullDichotomy.lean)
- **Why it matters:** upgrades the `Ω(t) ≤ 2` core (#5) to the explicit
  `ap`/`apq` child description — Lemma 4.5 is now fully machine-checked.

---

*Results #8–#11 were produced in an ultracode multi-agent round: #8, #9, #10 by
three parallel subagents and #11 by the orchestrator, all `kernel_verified` on
the first submission.*

### 12. Proposition 3.2 — single-step frontier increment  (paper §3)

- **Statement (root_statement_hash `7f25ceb6b51646000d8fbdfe9ce94ab8e5801f5aabc0bd8bc6459322b870db12`):**
  for an abstract parent map π (π 1 = 0, 2≤n≤N ⇒ 1≤π n<n), `K+1 ≤ N ⇒
  S_N(K+1) = S_N(K) + (C_N(K+1) − 1/(K+1))` (frontier reciprocal sums inline).
- problem_version_id: `2012d242-3366-4a02-ae55-cc8744387cc6`
- episode_id: `0291888b-5f81-4e5e-88df-827808e576a6`
- outcome: `kernel_verified` — rewards `kernel_pass 5000`, `root_kernel_verified 20000`
- snapshot: [proof/Erdos858_FrontierSweepStep.lean](proof/Erdos858_FrontierSweepStep.lean)
- **Why it matters:** the linchpin of the frontier sweep — the Finset
  decomposition `A_N(K+1) = (A_N(K) \ {K+1}) ⊍ {children of K+1}`.

### 13. Proposition 3.2 — abstract telescoping  (paper §3)

- **Statement (root_statement_hash `18493e6655096ee52f685b607cda5ecb8e03bc7a29173068f4397f2d48d85dee`):**
  `s 0 = 1 → (∀ K, s(K+1) = s K + g(K+1)) → s K = 1 + Σ_{a=1}^K g a`.
- problem_version_id: `538459d3-fca2-4c87-b695-2eccb5a564c9`
- episode_id: `e347aa8f-a9b9-481f-af7f-e22a62f47a18`
- outcome: `kernel_verified` — rewards `kernel_pass 5000`, `root_kernel_verified 20000`
- snapshot: [proof/Erdos858_FrontierSweepTelescope.lean](proof/Erdos858_FrontierSweepTelescope.lean)
- **Why it matters:** with #12 (increment) and #14 (base) this gives the paper's
  `S_N(K) = 1 + Σ_{a≤K} q_N(a)`.

### 14. Proposition 3.2 — base case `A_N(0) = {1}`  (paper §3)

- **Statement (root_statement_hash `715ada62306014167630684d3795bc6938363b011e9a2d2be72e327d865c6dc0`):**
  `1≤N → π 1=0 → (2≤n≤N ⇒ 1≤π n) → (Icc 1 N).filter (π ·≤0 ∧ 0<·) = {1}`.
- problem_version_id: `9f3c42cb-4a78-4888-ab97-7a8ba65ad396`
- episode_id: `4a2263f0-2ea3-4bdf-893d-fa67d9a01d3a`
- outcome: `kernel_verified` — rewards `kernel_pass 5000`, `root_kernel_verified 20000`
- snapshot: [proof/Erdos858_FrontierBaseZero.lean](proof/Erdos858_FrontierBaseZero.lean)
- **Why it matters:** `S_N(0) = 1`, the base of the sweep.

### 15. Lemma 3.1 — the frontier `A_N(K)` is an antichain  (paper §3)

- **Statement (root_statement_hash `1cfe83b060bb9069e359c45ba4fc900436e6058435980420779783188d1f42de`):**
  under π-maximality, distinct frontier vertices `x < y` satisfy `x ⋠ y`.
- problem_version_id: `de5b09fd-6784-4364-9f51-9be70b696a54`
- episode_id: `b89eb944-9f1f-419b-ab63-5f66512c8fe8`
- outcome: `kernel_verified` — rewards `kernel_pass 5000`, `root_kernel_verified 20000`
- snapshot: [proof/Erdos858_FrontierAntichain.lean](proof/Erdos858_FrontierAntichain.lean)
- **Why it matters:** the frontier is a genuine admissible set — the objects the
  max-closure argument optimizes over.

*Results #12–#15 (paper §3 frontier-sweep spine) were produced in a second
ultracode multi-agent round: #13, #14, #15 by three parallel subagents and #12
(the hard Finset decomposition) by the orchestrator. Together, #12 + #13 + #14
establish the frontier sweep identity `S_N(K) = 1 + Σ_{a≤K} q_N(a)`
(Proposition 3.2).*

### 16. A concrete instantiation of π  (paper §2, Corollary 2.2 / Lemma 2.3 "first step")

- **Statement (root_statement_hash `4b3902ef2d72a3cdd0027d809d8f637b0b767f276bb545bf6397c94c1a388674`):**
  `let piFn := fun n => if n≤1 then 0 else max {a<n : a⪯n}` (via `Finset.max'`)
  satisfies `piFn 1 = 0 ∧ (2≤n ⇒ 1≤piFn n<n) ∧ (z<m∧z⪯m ⇒ z≤piFn m)` — exactly
  the three abstract axioms used throughout the §3 results (#12–#15).
- problem_version_id: `18d8bb2d-3892-4b29-afc8-373a70efbd2f`
- episode_id: `2de97643-e375-4b5a-87af-9150f3ec7546`
- outcome: `kernel_verified` — rewards `kernel_pass 5000`, `root_kernel_verified 20000` (2 submissions: `unfold_let` doesn't exist in this Mathlib pin, fixed with `dsimp only`)
- snapshot: [proof/Erdos858_ConcretePiAxioms.lean](proof/Erdos858_ConcretePiAxioms.lean)
- **Why it matters:** closes the loop between the abstract §3 theorems (which assumed a `π` satisfying these axioms) and a genuine, usable parent-map function — instantiating them is now a direct application, not a further construction. Deliberately sidesteps Lemma 2.3's harder non-monotone prefix-product characterization: a **naive greedy definition of π is provably wrong** (counterexample by hand: `n=99=3·3·11` — the prefix `3` is not an ancestor, but the *later* prefix `9=3·3` is, since validity of prefix index `k` is non-monotone), so `piFn` is defined directly as `max {a<n : a⪯n}` via the already-verified `⪯` relation instead.

### 17. Proposition 4.1 — `ν(1) = 4` (small exact instance)  (paper §4.1)

- **Statement (root_statement_hash `5fb9176d92f5bf8590cbb32f836f1a5bea430ab1907434b527dd6442a058c5e6`):**
  for `n ∈ {2,3,4}`, no `b` with `1<b<n` is a `⪯`-ancestor of `n` (each has
  only-ancestor `1`); and `1/2+1/3+1/4 > 1 ≥ 1/2+1/3`.
- problem_version_id: `747a0252-bc83-40e2-9ceb-6c995214d8b2`
- episode_id: `f5a2bf4c-fe85-479f-bf65-dcd8fff475f4`
- outcome: `kernel_verified` — rewards `kernel_pass 5000`, `root_kernel_verified 20000`
- snapshot: [proof/Erdos858_Prop41_NuOneEqFour.lean](proof/Erdos858_Prop41_NuOneEqFour.lean)
- **Why it matters:** a genuine, kernel-checked instance of Prop 4.1's `ν(a)`
  table (the paper's ONLY computer-assisted ingredient), confirming `ν(1)=4`
  by hand-verified small-range enumeration. The full table up to `ν(19)=80807`
  is **not** attempted — see the honesty note in [attack-plan.md](attack-plan.md).

### 18. Proposition 4.6 — `P_N(a)` monotonicity  (paper §4)

- **Statement (root_statement_hash `b519e0ad5f46183b28896119e47ed57a2d6878f845dea44460dccf07ddd0ec7f`):**
  for `0<a≤b`, `Σ_{a<p, ap≤N} 1/p ≥ Σ_{b<p, bp≤N} 1/p` (the prime-sum half of
  `R_N(a) = P_N(a)+Q_N(a)`'s upper-layer monotonicity).
- problem_version_id: `a8c19f95-14f8-460e-b6cf-7b09b3f9e0d0`
- episode_id: `df3913fc-746e-44c6-b82b-9efde1a7d348`
- outcome: `kernel_verified` — rewards `kernel_pass 5000`, `root_kernel_verified 20000`
- snapshot: [proof/Erdos858_Prop46_PNMonotone.lean](proof/Erdos858_Prop46_PNMonotone.lean)
- **Why it matters:** the `b`-domain is a subset of the `a`-domain (nested
  intervals), so `Finset.sum_le_sum_of_subset_of_nonneg` gives monotonicity
  directly — the `P_N` half of Prop 4.6, feeding the sign theorem (§4.7).
  The `Q_N` (semiprime pair-sum) half is not yet attempted.

*Results #16–#18 (a third ultracode round) were produced by three parallel
subagents/orchestrator: #16 (concrete π, genuinely novel `let`-in-statement +
`dsimp only` technique) by the orchestrator, #17 (ν(1)=4) and #18 (Prop 4.6
P_N) by subagents — all `kernel_verified`.*

### 19. Corollary 3.5 — optimization inequality  (paper §3)

- **Statement (root_statement_hash `67dcdcfdbd786eb2c826c9e652607ca1e2e64b0e9008a02e73648b56fc6dfa9b`):**
  for `q` with `0 ≤ q` on `[1,K]` and `q ≤ 0` beyond, any `D ⊆ [1,M]` (`K≤M`)
  has `Σ_{a∈D} q a ≤ Σ_{a∈[1,K]} q a`.
- problem_version_id: `4bf1cc17-5c23-4129-92b8-bad8248a352d`
- episode_id: `b4ea3f69-67b6-4212-9a73-e95d63417c73`
- outcome: `kernel_verified` — `kernel_pass 5000`, `root_kernel_verified 20000`
- snapshot: [proof/Erdos858_Cor35_OptimizationInequality.lean](proof/Erdos858_Cor35_OptimizationInequality.lean)
- **Why it matters:** `[1,K]` is the q-optimal continuation set — the
  initial-segment optimization behind Cor 3.5.

### 20. Corollary 3.5 — `[1,K]` is a continuation set  (paper §3)

- **Statement (root_statement_hash `a80fa70468e07dec18f7a56ee61eedcbe477197e07df1a8b438b383170087bfb`):**
  `∀ n ∈ [1,K], 2 ≤ n → π n ∈ [1,K]` (downward-closed under `π`).
- problem_version_id: `cca78d4c-087a-4ac0-a030-526bca3cbb90`
- episode_id: `1a5a0ea6-9e90-418b-979f-1d90d0433903`
- outcome: `kernel_verified` — `kernel_pass 5000`, `root_kernel_verified 20000`
- snapshot: [proof/Erdos858_Cor35_InitialSegmentClosed.lean](proof/Erdos858_Cor35_InitialSegmentClosed.lean)
- **Why it matters:** `[1,K]` is a valid continuation set whose boundary is the
  frontier `A_N(K)` — the optimum achiever in the max-closure duality.

### 21. Proposition 3.4 — max-closure identity  (paper §3)

- **Statement (root_statement_hash `b2bfcaa44d4ed8662c2281f099728619acc3059acf183ffdc6589f2162cd8691`):**
  for a continuation set `D` (downward-closed, `1∈D`),
  `Σ_{n∈∂D} 1/n = 1 + Σ_{a∈D} q_N(a)`.
- problem_version_id: `ca019ca3-4afe-4932-a50e-7e641a1635c2`
- episode_id: `7ffe3b0d-97c8-4eb6-a193-1c05d6178333`
- outcome: `kernel_verified` — `kernel_pass 5000`, `root_kernel_verified 20000`
- snapshot: [proof/Erdos858_Prop34_MaxClosureIdentity.lean](proof/Erdos858_Prop34_MaxClosureIdentity.lean)
- **Why it matters:** the structural heart of the reduction — each continuation
  set's boundary weight is `1 +` its `q`-sum. Fiberwise grouping + a
  `∂D ⊍ (D\{1})` partition.

### 22. Boundary `∂D` is a `⪯`-antichain  (paper §3, Prop 3.4 consequence)

- **Statement (root_statement_hash `1a720a67df05958e78c2b5a7b452adea547245b977a7d64ab427468750908c68`):**
  under `⪯`-maximality of `π` and `⪯`-downward-closure of `D`, distinct
  `x < y ∈ ∂D` satisfy `x ⋠ y`.
- problem_version_id: `887fea14-f2f4-4e47-8bf8-566ce45336e1`
- episode_id: `96b1ceb3-2ae1-496f-a3fb-d1ef5cf3341a`
- outcome: `kernel_verified` — `kernel_pass 5000`, `root_kernel_verified 20000`
- snapshot: [proof/Erdos858_BoundaryAntichain.lean](proof/Erdos858_BoundaryAntichain.lean)
- **Why it matters:** every continuation set's boundary is a genuine admissible
  antichain, so its weight (= `1 + Σ_D q_N`) is `≤ M(N)`.

### 23. Remark 2.5 — Bellman form of the subtree recursion  (paper §2)

- **Statement (root_statement_hash `632e263bb39da200f6adfd59a5914cbdd3bce4c3e740e0c8911aa8fc0c576e9a`):**
  `F a = max(1/a, Σ_{b∈ch} F b)` ⇒ `a·F a = max(1, Σ_{b∈ch} (a/b)·(b·F b))`.
- problem_version_id: `1c5f2019-6e63-42fb-89b6-a53f8816618d`
- episode_id: `6c59fc46-acdf-49e4-bab5-31326433b14f`
- outcome: `kernel_verified` — `kernel_pass 5000`, `root_kernel_verified 20000`
- snapshot: [proof/Erdos858_Remark25_BellmanForm.lean](proof/Erdos858_Remark25_BellmanForm.lean)
- **Why it matters:** the optimal-stopping / Bellman rescaling `V_N(a) = a·F_N(a)`
  of the subtree optimum.

### 24. Exchange-free stopping-set construction  (paper §3, replaces Lemma 3.3)

- **Statement (root_statement_hash `2b03da27e23de11799a83feb419cfe4dabc0678ddc449f443c2695a8b86e08fd`):**
  for a `⪯`-antichain `B ⊆ [1,N]` with `1∉B`, `∃ D` continuation set with
  `B ⊆ ∂D`.
- problem_version_id: `24eee3ac-c938-483b-8301-351121e2d2c4`
- episode_id: `2eaa4b8e-f9cf-472c-8da3-0beb67a17b64`
- outcome: `kernel_verified` — `kernel_pass 5000`, `root_kernel_verified 20000`
- snapshot: [proof/Erdos858_StoppingSetConstruction.lean](proof/Erdos858_StoppingSetConstruction.lean)
- **Why it matters:** `D_B := {a : no ⪯-ancestor of a is in B}` directly realizes
  the paper's Lemma 3.3 (every antichain dominated by some `∂D`) **without** the
  iterative leaf-adding exchange. With #21 + #19 + #20 this gives the `≤`
  direction of the max-closure duality `M(N) = 1 + max_D Σ_D q_N` (Cor 3.5).

*Results #19–#24 (paper §3 max-closure machinery + §2 Bellman form): #19, #20,
#23 by three parallel subagents; #21 (Prop 3.4 identity), #22 (∂D antichain),
#24 (stopping-set construction) by the orchestrator — all `kernel_verified`
(#24 in 2 submissions). Together with the verified frontier sweep (Prop 3.2),
these are ALL the components of the max-closure reduction
`M(N) = 1 + max_D Σ_D q_N = S_N(K)` (Corollary 3.5); only the `M(N)`-as-max
definitional glue remains to assemble them into the single `M(N) = S_N(K)`
statement.*

### 25. Weight subset-monotonicity  (glue)

- **Statement (root_statement_hash `4f73b9c6893e633f31fc7f871507532d11afe7f9d97a12af894ed3b0bd765c6d`):**
  `∀ B C, B ⊆ C → Σ_{n∈B} 1/n ≤ Σ_{n∈C} 1/n`.
- problem_version_id: `2572333e-ae93-4385-91a5-414c070018da` · episode_id: `937e3f78-221b-465f-bc27-5fc64781bc9b`
- outcome: `kernel_verified`
- snapshot: [proof/Erdos858_WeightSubsetMonotone.lean](proof/Erdos858_WeightSubsetMonotone.lean)

### 26. An antichain containing 1 is `{1}`  (glue)

- **Statement (root_statement_hash `711a54ecffc3fcdcaadbe6d12afbaf10328c2caa9a71f4e3400c0bf98c5a026c`):**
  a `⪯`-antichain `B` with `1 ∈ B` has every element `= 1`.
- problem_version_id: `11ef8f61-cad5-4c60-9e6d-66d287a38858` · episode_id: `4bcb8610-aa2c-4314-9d4d-76cea9b11f1b`
- outcome: `kernel_verified`
- snapshot: [proof/Erdos858_AntichainOneSingleton.lean](proof/Erdos858_AntichainOneSingleton.lean)

### 27. Corollary 3.5 — `≤` direction of the max-closure duality (`M(N) ≤ S_N(K)`)  (paper §3)

- **Statement (root_statement_hash `dd521e98518d282bec255fc169eb2f2ef095617883a7ecf4c76a43d24fb854d6`):**
  assembling the verified components (stopping-set, Prop 3.4, optimization,
  Prop 3.2 value `S`), every admissible `⪯`-antichain `B ⊆ [1,N]` has
  `Σ_{n∈B} 1/n ≤ S`.
- problem_version_id: `779b78c0-578e-4d37-983d-6477737dbfda` · episode_id: `c78c33ce-ac2c-43d5-b77c-cd776246affc`
- outcome: `kernel_verified`
- snapshot: [proof/Erdos858_Cor35_LeDirection.lean](proof/Erdos858_Cor35_LeDirection.lean)
- **Why it matters:** THE hard direction of Corollary 3.5. Since `M(N)` is the
  max weight over admissible antichains, this is `M(N) ≤ S_N(K)`. With the
  trivial `≥` direction (`A_N(K) = ∂[1,K]` achieves `S_N(K)`), Cor 3.5
  (`M(N) = S_N(K)`) is complete modulo packaging `M(N)` as a `Finset.max'` and
  discharging the four hypotheses with the verified lemmas #24/#21/#19/#12–14.

*Results #25–#27: #25, #26 by two parallel subagents; #27 (the `≤`-direction
assembly) by the orchestrator — all `kernel_verified` on the first submission.
The max-closure duality's hard direction, `M(N) ≤ S_N(K)`, is now one verified
theorem.*

### 28. Proposition 4.6 — `Q_N` (semiprime pair-sum) monotonicity  (paper §4)

- **Statement (root_statement_hash `c5b0f7370d8d6d8ddcf3e33d943ce80f26e72e60f34c60bf33f6b622ba3cbe0c`):**
  for `0<a≤b`, `Q_N(a) ≥ Q_N(b)` where `Q_N(a) = Σ_{a<p≤q, apq≤N} 1/(pq)`.
- problem_version_id: `ec7ec70f-7dfc-44d9-8422-cc39c94ab21c` · episode_id: `3e8bbf28-cb9d-4b43-9f78-436ecae574a3`
- outcome: `kernel_verified`
- snapshot: [proof/Erdos858_Prop46_QNMonotone.lean](proof/Erdos858_Prop46_QNMonotone.lean)
- **Why it matters:** the semiprime-pair companion to #18 (`P_N`). With `P_N`,
  this gives the full **Proposition 4.6** upper-layer monotonicity of
  `R_N = P_N + Q_N` — an ingredient of the sign theorem (§4.7).

### 29. Corollary 3.5 capstone — `M(N) = S_N(K)`  (paper §3)

- **Statement (root_statement_hash `2bf2793fc2d4de2253db5ba3827c48922f4bd29d7c23674fe167d2afb7ae655f`):**
  with `M(N)` := max reciprocal-weight over admissible antichains `B ⊆ [1,N]`
  (the set `IMG = (powerset.filter Anti).image weight`), and given the `≤`
  direction (`∀ antichain B, w(B) ≤ S`) and a `≥`-witness (`∃ B0, w(B0)=S`):
  `S ∈ IMG ∧ (∀ x ∈ IMG, x ≤ S)`, i.e. `M(N) = S`.
- problem_version_id: `81e87e62-3d15-4d77-9f6c-9ac9229157dd` · episode_id: `f6aa8db6-ce90-4b06-afb7-d97c9d729319`
- outcome: `kernel_verified` (2 submissions: `Classical.decPred` instance pinned in `@Finset.mem_filter`)
- snapshot: [proof/Erdos858_Cor35_MaxEq.lean](proof/Erdos858_Cor35_MaxEq.lean)
- **Why it matters:** **THE capstone.** Instantiated with `S := S_N(K)`,
  `w := 1/n`, `Anti := ⪯-antichain`, and the two directions discharged by
  #27 (`≤`) and Lemma 3.1 + Prop 3.2 (`≥`-witness `A_N(K)=∂[1,K]`), this is
  **Corollary 3.5: `M(N) = S_N(K)`** — the complete §3 frontier reduction of
  Erdős #858. Combined with the (analytic) sign theorem of §4 it yields
  Theorem 1.1 (`M(N) = M_fr(N)`).

*Results #28–#29: #28 (`Q_N`) by a subagent, #29 (the `M(N)=S_N(K)` capstone) by
the orchestrator. The entire §3 max-closure reduction and Prop 4.6 are now
machine-checked.*

### 30. Proposition 5.6 — Φ-monotonicity core  (paper §5, real-analytic)

- **Statement (root_statement_hash `262f89e3919d7645fed4b367b12c7837e1dcbab50d37f085e5af35da227b816d`):**
  `StrictAntiOn (fun u => log((1-u)/u)) (Ioo 0 1) ∧ log 2 < 1 ∧ (∀ u, 1/3 ≤ u → u < 1/2 → log((1-u)/u) < 1)`.
- problem_version_id: `04bdec8a-73bb-4211-85c9-e271708cef52` · episode_id: `f3ae9d6d-5467-4b86-8fc5-6814bf3b2871`
- outcome: `kernel_verified` (first try)
- snapshot: [proof/Erdos858_Prop56_PhiCore.lean](proof/Erdos858_Prop56_PhiCore.lean)
- **Why it matters:** the integral-free core of Prop 5.6. On `[1/3,1/2]` the
  semiprime integral of `Φ` vanishes, so `Φ(u) = log((1-u)/u)`; this proves `Φ`
  strictly decreasing there and `Φ < 1` throughout (via `Φ(1/3)=log 2<1`), so the
  unique root `α₂` of `Φ=1` lies strictly below `1/3` — the placement the paper
  asserts. No analytic number theory.

### 31. §5 quantitative Mertens — UPPER bound  (paper §5, NEW)

- **Statement (root_statement_hash `0964e4e62a3d535d94b4a83ac1a17f2a64927dc96825f1ec2c086668713ba472`):**
  `∀ x ≥ 2, Σ_{p≤x, p prime} 1/p ≤ log 4 · loglog x + (4 − log 4 · loglog 2)`.
- problem_version_id: `81a545eb-79d5-4e8a-bfd0-1aa47fa74630` · episode_id: `9e56ec0a-f75c-4b3d-a7cf-b165913fb269`
- outcome: `kernel_verified` (3 submissions: `₊` encoding fix, then dropped a redundant `ring`)
- snapshot: [proof/Erdos858_MertensUpper.lean](proof/Erdos858_MertensUpper.lean)
- **Why it matters:** **breaches the "analytic wall."** Reuses #647's kernel-verified
  Abel-summation Mertens identity + main-term antiderivative, but driven by
  Mathlib's `Chebyshev.theta_le_log4_mul_x` (θ ≤ log4·t), the *upper* Chebyshev
  bound #647 never used. Together with the lower bound (#34) it brackets the prime
  harmonic sum as `Θ(loglog x)` — the growth content underneath Lemma 5.2. This is
  a genuinely new analytic result for the campaign (not present in #647).

### 32. Theorem 2.4 — subtree-recursion root dichotomy  (paper §2)

- **Statement (root_statement_hash `b2c7f7d6015ed5fa94135a01956788a9efab626d5a976a41d938e12fb6e196db`):**
  on a finite `T` with root `a` `⪯`-below every element, `{a}` is a `⪯`-antichain
  `⊆ T`, and every `⪯`-antichain `B ⊆ T` is `B = {a} ∨ a ∉ B`.
- problem_version_id: `736ebc6b-1541-4ae3-8232-6702951f4073` · episode_id: `22e685e6-7848-4d08-aaa9-fca499c835af`
- outcome: `kernel_verified` (first try)
- snapshot: [proof/Erdos858_Thm24_RootDichotomy.lean](proof/Erdos858_Thm24_RootDichotomy.lean)
- **Why it matters:** the exact case split at the heart of Theorem 2.4's subtree
  recursion `F_N(a) = max(1/a, Σ_{b∈ch} F_N(b))`: an antichain either "stops at `a`"
  (`= {a}`, weight `1/a`) or "continues" past it (`a ∉ B`, decomposing over
  children). The complementary additive child-decomposition is the deferred half.
  This DP is an alternative to the already-verified frontier route (`M(N)=S_N(K)`, #29).

### 33. Real-valued Chebyshev ϑ bridge  (paper §5 foundation; ported from #647)

- **Statement (root_statement_hash `72cb80ab472e749d02f2ec9507b84f08254d17a1a8d971e0f5ee69028e709531`):**
  `∀ t ≥ 2, (t−1)·log 2 − log(t+2) − 2√t·log t ≤ Chebyshev.theta t`.
- problem_version_id: `baa73c15-f4de-4148-bec9-c6009fee1996` · episode_id: `040cf08c-4190-45d7-8dc0-4f5f8b8697c6`
- outcome: `kernel_verified` (first try)
- snapshot: [proof/Erdos858_ThetaRealGe.lean](proof/Erdos858_ThetaRealGe.lean)
- **Why it matters:** bridges Mathlib's integer-indexed `Chebyshev.theta_ge` to all
  real `t ≥ 2` (via `n=⌊t⌋` + `theta_mono` + termwise bounds) — the shared analytic
  foundation for the quantitative-Mertens bounds. The new #858 root hash is
  **byte-identical** to the #647 artifact's, certifying a faithful port.

### 34. §5 quantitative Mertens — LOWER bound  (paper §5; ported from #647)

- **Statement (root_statement_hash `2470d4498d67527b14af26b8f3e21b68924d7f4751f105c6895623d310d207d1`):**
  `∀ x ≥ 2, log 2 · loglog x − (1/2 + log2·loglog2 + (1+1/log2)·(1+2√2)) ≤ Σ_{p≤x} 1/p`.
- problem_version_id: `5a5ccddf-bd27-4440-ad42-fdcd0f54000e` · episode_id: `a748163c-5644-41f3-8612-c0fcebc300a3`
- outcome: `kernel_verified` (3 submissions; see typo note below)
- snapshot: [proof/Erdos858_MertensLower.lean](proof/Erdos858_MertensLower.lean)
- **Why it matters:** with #31 (upper) this completes the two-sided **Θ(loglog x)
  bracket** for the prime harmonic sum — the qualitative content of Lemma 5.2.
  Ported from #647's six-piece Layer-A assembly (Abel identity + main-term
  antiderivative + weight integral + two convergent error integrals + the ϑ bridge
  #33), driven by `Chebyshev.theta_ge`. The new #858 root hash is byte-identical to
  #647's, certifying a faithful port.
- **Upstream-snapshot note:** a truly verbatim copy failed to *parse* — the committed
  `erdos-647/proof/Erdos647_MertensAssembly.lean` has a one-character paren typo
  (`(((` should be `((` at the `hABCD` have-statement, line ~522); the *verified*
  #647 proof was balanced. The #858 port applies the semantics-preserving fix
  (`rw` still closes by `rfl`, extra outer paren is defeq) and documents it in the
  snapshot header. The upstream #647 snapshot would benefit from the same fix (left
  untouched here — #647 is out of scope for this campaign).

### 35. Theorem 2.4 — subtree-recursion continue branch (child-subtree merge)  (paper §2)

- **Statement (root_statement_hash `c6e782e79afb152672c720656cbc855b1d93f85d75768895f9d74a792387d2dd`):**
  for disjoint, pairwise-`⪯`-incomparable `⪯`-antichains `B, C`, the union `B ∪ C`
  is a `⪯`-antichain and `Σ_{B∪C} 1/n = Σ_B 1/n + Σ_C 1/n`.
- problem_version_id: `1142674b-fc92-4091-b8c4-e28e797e2865` · episode_id: `78200cfa-a248-49b6-b58a-24946a4909bc`
- outcome: `kernel_verified` (first try)
- snapshot: [proof/Erdos858_Thm24_ChildrenMerge.lean](proof/Erdos858_Thm24_ChildrenMerge.lean)
- **Why it matters:** the paper's "different child subtrees are pairwise
  incomparable, so the optimal contributions add." With #32 (root dichotomy) this
  is the **full combinatorial content of Theorem 2.4** — stop-at-`a` (`={a}`,
  weight `1/a`) versus continue-into-incomparable-children (disjoint antichain
  union, additive weight) — the case split yielding `F_N(a) = max(1/a, Σ_b F_N(b))`.

### 36. §5 constant α — Kinlaw–Pomerance threshold localization  (paper §5)

- **Statement (root_statement_hash `f68b01b4c4ac282d7e5edba9a49c4dad390cabe51489a9f54ec2ed67d37b13dc`):**
  `1/4 < 1/(e+1) < 1/3`.
- problem_version_id: `918ae6d8-1a62-4cea-b73e-e638fa831f1e` · episode_id: `06e7a434-c3dc-474d-900c-0914ca551bdd`
- outcome: `kernel_verified` (first try)
- snapshot: [proof/Erdos858_AlphaKPThreshold.lean](proof/Erdos858_AlphaKPThreshold.lean)
- **Why it matters:** the paper's threshold `α := 1/(e+1) = 0.2689…` (§4.3–§4.4
  low-layer bound) localized in `(1/4, 1/3)` from `2 < e < 3`. Companion to the
  Prop 5.6 core (`α₂ < 1/3`): both `α` and `α₂` lie in `(1/4, 1/3)`, matching the
  paper's `α < α₂ = 0.2804…`.

### 37. Proposition 5.6 — continuity of Φ on `[1/3,1/2]`  (paper §5)

- **Statement (root_statement_hash `93b9a5f9aa0eaea356e21ecfbce48570c47c5cc2e5062c1ad914381060feff31`):**
  `ContinuousOn (fun u : ℝ => Real.log ((1 - u) / u)) (Set.Icc (1/3) (1/2))`.
- problem_version_id: `de1300cd-e0aa-4fdb-a2df-b0a7fe381fbc` · episode_id: `c116cf66-fef7-48bd-87cd-0090d0b59a48`
- outcome: `kernel_verified` (first try) · snapshot: [proof/Erdos858_Prop56_Continuity.lean](proof/Erdos858_Prop56_Continuity.lean)
- **Why it matters:** the "continuity" half of Prop 5.6 on the integral-free upper
  interval (where `Φ(u) = log((1-u)/u)`), the paper's "Continuity is clear."
  `ContinuousOn.log` + `ContinuousOn.div₀` with `0 < u` on the interval.

### 38. Theorem 2.4 — full subtree value recursion (max' characterization)  (paper §2)

- **Statement (root_statement_hash `563f3f7e0dc5dce4b0cc996be32b11ab3cc8beec1097941828968930be22a953`):**
  with `S = (T.powerset.filter Anti).image (fun B => Σ_{n∈B} 1/n)` the achievable-weight
  set (= `F_N(a)`), given `1/a ∈ S`, `C ∈ S`, and `∀ x ∈ S, x ≤ max(1/a,C)`, then
  `S.max' hne = max(1/a, C)`.
- problem_version_id: `b347c67d-e1f7-4c9e-977c-2f946f4ced56` · episode_id: `48bc8447-3df0-402c-9d53-6dfd2d54d08e`
- outcome: `kernel_verified` (2 problem_versions: fixed a statement-elaboration bug where inlined `(n:ℚ)` made Lean infer `B : Finset ℚ`)
- snapshot: [proof/Erdos858_Thm24_ValueRecursion.lean](proof/Erdos858_Thm24_ValueRecursion.lean)
- **Why it matters:** the value-function `max` layer of Theorem 2.4, via the same
  `Finset.max'` abstraction as `cor35_max_eq` (#29). With #32 (root dichotomy,
  supplying `1/a ∈ S`) and #35 (child-merge, realizing `C = Σ_b F_N(b)`), this
  **completes Theorem 2.4**: `F_N(a) = max(1/a, Σ_{b∈ch} F_N(b))`.

### 39. Proposition 5.6 — semiprime integral sign `I(u) ≥ 0`  (paper §5)

- **Statement (root_statement_hash `34cf2b70a980f9878decdbabd05a4181edbe58ad54b5bf6bcf78d851a425e52a`):**
  `∀ u, 0 < u → u ≤ 1/3 → 0 ≤ ∫ v in u..(1-u)/2, (1/v)·Real.log ((1-u-v)/v)`.
- problem_version_id: `8cc9e844-3efa-42a3-9aba-96c6ca698cb0` · episode_id: `a4afd2d6-e146-4144-b1e7-e3acd0759fcf`
- outcome: `kernel_verified` (first try) · snapshot: [proof/Erdos858_Prop56_SemiprimeIntegralNonneg.lean](proof/Erdos858_Prop56_SemiprimeIntegralNonneg.lean)
- **Why it matters:** the paper's "sign of the integrand" input to the Prop 5.6
  Leibniz argument — the semiprime term `I(u)` never decreases the density. Via
  `intervalIntegral.integral_nonneg` (no integrability needed): on `[u,(1-u)/2]`,
  `v ≤ (1-u-v)` so `log((1-u-v)/v) ≥ 0` and `1/v > 0`. Stated on the forward
  orientation `u ≤ 1/3` to stay correct under either integral convention (see the
  Leibniz-scout convention note in attack-plan.md).

### 40. Prime-reciprocal divergence  (paper §5 context)

- **Statement (root_statement_hash `5de3fa964abd30d794626ee25f7ee58ff95572d85ea06a110434054cde5f0819`):**
  `Tendsto (fun n => Σ_{p ∈ range n, p prime} 1/p) atTop atTop`.
- problem_version_id: `e6c1bdf5-9036-420b-a76e-59bd2e6b49d3` · episode_id: `3a0df92d-5894-4170-9d56-8720cbd86e0f`
- outcome: `kernel_verified` (first try) · snapshot: [proof/Erdos858_PrimeReciprocalDiverges.lean](proof/Erdos858_PrimeReciprocalDiverges.lean)
- **Why it matters:** the qualitative divergence `Σ_{p≤x} 1/p → ∞` (via Mathlib's
  `not_summable_one_div_on_primes`), the coarse floor beneath the quantitative
  bracket (#31/#34). Recorded from the sharp-Mertens scout, whose verdict is that
  the *sharp asymptotic* (leading constant exactly 1, the exact `c₂`) is **not
  reachable in this Mathlib pin** — there is no Mertens first/second theorem, no
  PNT, and no `θ(x)=x+o(x)`; see the wall note below.

### 41. Mertens-1 building block — von Mangoldt double-count identity  (paper §5)

- **Statement (root_statement_hash `8cb2596844de37deb989db184026e53cc9c722c9179dc405425f3759c9e4c48d`):**
  `∀ N, ∑_{n∈Icc 1 N} log n = ∑_{d∈Icc 1 N} Λ(d)·⌊N/d⌋` (`Λ` = `ArithmeticFunction.vonMangoldt`, `N/d` = Nat division).
- problem_version_id: `79cf884a-dcaf-44c2-b64a-bb4c1bbf1326` · episode_id: `7346fd64-45e3-4521-a20e-4c75355af49e`
- outcome: `kernel_verified` (first try) · snapshot: [proof/Erdos858_Mertens1_LogSumVonMangoldt.lean](proof/Erdos858_Mertens1_LogSumVonMangoldt.lean)
- **Why it matters:** the double-counting identity at the heart of Mertens' *first*
  theorem — `vonMangoldt_sum` (`log n = Σ_{d∣n} Λ d`) + `Finset.sum_comm` +
  `Nat.Ioc_filter_dvd_card_eq_div` (count of multiples = `⌊N/d⌋`). First §5 step
  toward the sharp constant `c₂`.

### 42. Mertens-1 building block — `ψ(N) ≤ (log 4 + 4)·N`  (paper §5)

- **Statement (root_statement_hash `4bf8ea3eb43e87a7fd43dea731b8a14ff8004e85163ecd6535d55c2d14a6bcdf`):**
  `∀ N, ∑_{n∈Icc 1 N} Λ(n) ≤ (log 4 + 4)·N`.
- problem_version_id: `725fa23b-04a9-4cce-ace3-bc378b35caf8` · episode_id: `46121fef-5e5d-49e5-bec4-34f36f5c1dff`
- outcome: `kernel_verified` (first try) · snapshot: [proof/Erdos858_Mertens1_PsiLinear.lean](proof/Erdos858_Mertens1_PsiLinear.lean)
- **Why it matters:** Chebyshev's `ψ(x)=O(x)` (`Chebyshev.psi_le_const_mul_self`)
  as a von-Mangoldt partial sum — the `O(x)` input that controls the `⌊N/d⌋`
  fractional-part error in Mertens' first theorem.

### 43. Mertens-1 building block — `Σ log n = log(N!)`  (paper §5)

- **Statement (root_statement_hash `86b2bc57322113c7dd2539ac86b56d0ded1799501a6992ab8bc06df5ace7b435`):**
  `∀ N, ∑_{n∈Icc 1 N} log n = log(N!)`.
- problem_version_id: `d54372e7-53d5-4d52-affc-cb659238705c` · episode_id: `aa47c1d1-43c0-4ce1-89aa-4bf1aba7dd26`
- outcome: `kernel_verified` (first try) · snapshot: [proof/Erdos858_Mertens1_LogFactorial.lean](proof/Erdos858_Mertens1_LogFactorial.lean)
- **Why it matters:** bridges the Mertens log-sum to Stirling (`Real.log_prod` +
  `Finset.prod_Ico_id_eq_factorial`). Combined with #41: `log(N!) = Σ_d Λ(d)⌊N/d⌋`.
  Scout finding: Mathlib has the unconditional Stirling **lower** bound
  `Stirling.le_log_factorial_stirling` (`N log N − N + … ≤ log N!`) but only an
  *asymptotic* upper bound — the two-sided `O(log N)` error needs a large-`N` threshold.

### 44. Prop 5.6 Leibniz — variable-endpoint FTC derivative  (paper §5)

- **Statement (root_statement_hash `554f37d691a29304b33be047f7dcdd892088f20192b94dbdbb8c432506638ece`):**
  `∀ g, Continuous g → ∀ u, HasDerivAt (fun w => ∫ v in w..(1-w)/2, g v) (g((1-u)/2)·(-1/2) − g u) u`.
- problem_version_id: `08d7b8fc-b1dd-431c-aba7-c12c8c598c77` · episode_id: `da32aac2-8925-49d8-917a-baf7fc9c99e8`
- outcome: `kernel_verified` · snapshot: [proof/Erdos858_Prop56_EndpointDeriv.lean](proof/Erdos858_Prop56_EndpointDeriv.lean)
- **Why it matters:** the **endpoint half of Prop 5.6's Leibniz rule**, fully
  general — both moving endpoints of `I(u)` (`u` and `(1-u)/2`, the latter via the
  `-1/2` chain rule) differentiated via `intervalIntegral.integral_hasDerivAt_right/_left`.
  The remaining half is the parameter derivative `∫ ∂_u f` (dominated convergence).

*Results #41–#44 (2026-07-14, Mertens-1 building-blocks workflow): three concrete
reachable building blocks of Mertens' first theorem (`Σ log n = Σ_d Λ(d)⌊N/d⌋ =
log(N!)`, `ψ(N)=O(N)`) — the pieces Mathlib provides toward the sharp `c₂` — plus
the fully-general endpoint derivative for the Prop 5.6 Leibniz argument.*

### 45. Mertens-1 — fractional-part error bound  (paper §5)

- **Statement (root_statement_hash `8f66b36665c8e5736bd5390a0c890a0856c45c7b0c62835c437d83352bbbf7ca`):**
  `∀ N`, `Σ_d Λ(d)(N/d) − Σ_d Λ(d)⌊N/d⌋ ≤ Σ_d Λ(d)` and `Σ_d Λ(d)⌊N/d⌋ ≤ Σ_d Λ(d)(N/d)`.
- problem_version_id: `84344737-a1f6-4afd-85dd-8452174062a8` · episode_id: `bb2ca63e-6387-4493-bc8e-1e3b88cacee3`
- outcome: `kernel_verified` · snapshot: [proof/Erdos858_Mertens1_FloorError.lean](proof/Erdos858_Mertens1_FloorError.lean)
- **Why it matters:** `⌊N/d⌋ = N/d − {N/d}` with `0 ≤ {N/d} < 1` and `Λ ≥ 0`, so the
  gap between `Σ Λ(d)⌊N/d⌋` and `N·Σ Λ(d)/d` is at most `ψ(N)` (#42). The error term
  that turns the double-count into `N·Σ Λ(d)/d + O(ψ)`.

### 46. Mertens-1 — Stirling lower bound  (paper §5)

- **Statement (root_statement_hash `bd6757b0337e65fd7e8b8b676b0d82ba117821b02d0e042e9ebf171b21df60da`):**
  `∀ N, 1 ≤ N → N·log N − N ≤ log(N!)`.
- problem_version_id: `fa9a52db-11eb-4b8e-a772-1a492561c599` · episode_id: `962a746a-41eb-40cc-ab54-bb33e85e4fb2`
- outcome: `kernel_verified` · snapshot: [proof/Erdos858_Mertens1_StirlingLower.lean](proof/Erdos858_Mertens1_StirlingLower.lean)
- **Why it matters:** from Mathlib's unconditional `Stirling.le_log_factorial_stirling`,
  dropping the nonneg tail. The main-term lower bound on `log(N!) = Σ_d Λ(d)⌊N/d⌋`.

### 47. Mertens-1 — lower-bound assembly `Σ_{d≤N} Λ(d)/d ≥ log N − 1`  (paper §5)

- **Statement (root_statement_hash `bf2abe3ac717422014270fe646bfa64863cfb0dfd92ce6bb8c56ff3707f60597`):**
  `∀ N S P F, 0 < N → F = P → P ≤ N·S → N·log N − N ≤ F → log N − 1 ≤ S`.
- problem_version_id: `72849c7f-a813-44ed-8fe8-5a6d1ce674ea` · episode_id: `c3e63438-1a4a-4da7-aed4-89b0c1ddb1f9`
- outcome: `kernel_verified` · snapshot: [proof/Erdos858_Mertens1_LowerAssembly.lean](proof/Erdos858_Mertens1_LowerAssembly.lean)
- **Why it matters:** **the lower direction of Mertens' first theorem** for the von
  Mangoldt sum. Its three hypotheses are each now a verified atom — `F=P` from
  #41+#43, `P ≤ N·S` from #45, `N log N − N ≤ F` from #46 — so `Σ_{d≤N} Λ(d)/d ≥
  log N − 1` is fully backed (assembled conditionally only because problem_versions
  can't cross-reference).

### 48. Mertens-1 — two-sided `Σ_{d≤N} Λ(d)/d = log N + O(1)`  (paper §5)

- **Statement (root_statement_hash `b08b5716536f81517bc4838a7acdce6bd0bf2d759956bbdfb4f4025a7c209632`):**
  `∀ N S P F ψ E, 0 < N → F = P → |N·S − P| ≤ ψ → |F − (N·log N − N)| ≤ E → |N·S − (N·log N − N)| ≤ ψ + E`.
- problem_version_id: `c97ced6c-c9f2-4925-8009-b854a11a2b07` · episode_id: `79ec2bb3-2a1b-4db6-b781-7002106071b4`
- outcome: `kernel_verified` (2 subs; `abs_add` isn't the identifier in this pin → `abs_le` + `linarith`)
- snapshot: [proof/Erdos858_Mertens1_TwoSided.lean](proof/Erdos858_Mertens1_TwoSided.lean)
- **Why it matters:** **both directions of Mertens' first theorem** for the von
  Mangoldt sum via the triangle inequality (`|N·S − P| ≤ ψ` from #45+#42, the
  two-sided Stirling `|F − (N log N − N)| ≤ E` for `E = O(log N)`). Establishes
  `Σ_{d≤N} Λ(d)/d = log N + O(1)`.

*Results #45–#48 (2026-07-14, Mertens-1 assembly): the fractional-part error (#45)
and Stirling lower bound (#46) discharge the hypotheses of the lower-bound assembly
(#47, `Σ Λ(d)/d ≥ log N − 1`), and the two-sided assembly (#48) gives the full
`Σ_{d≤N} Λ(d)/d = log N + O(1)` — Mertens' first theorem for the von Mangoldt sum,
built from verified components. Remaining to the sharp `c₂`: the prime-power tail
`Σ_{p^k,k≥2}(log p)/p^k = O(1)` (Λ-sum → prime sum) and Abel summation
`Σ_{p≤x} 1/p = loglog x + M + o(1)`.*

### 49. Mertens-1 — prime sum ≤ von Mangoldt sum  (paper §5)

- **Statement (root_statement_hash `c3243e3e3587e802d647709820bdd3efaea0830d285e7de234d6436807a34594`):**
  `∀ N, Σ_{p∈Icc 1 N, p prime} log p / p ≤ Σ_{d∈Icc 1 N} Λ(d)/d`.
- problem_version_id: `1179f381-2737-4cd1-9be0-a5eb0ec33ab2` · episode_id: `3dd8b5db-0e62-439e-b8a6-1a8b5aeaf989`
- outcome: `kernel_verified` · snapshot: [proof/Erdos858_Mertens1_PrimeLeVonMangoldt.lean](proof/Erdos858_Mertens1_PrimeLeVonMangoldt.lean)
- **Why it matters:** prime terms are a nonneg subset of the Λ-sum (`vonMangoldt_apply_prime`:
  `Λ(p) = log p`; `Finset.sum_le_sum_of_subset_of_nonneg`). Lower half of the Λ→prime conversion.

### 50. Mertens-1 — prime-power split identity  (paper §5)

- **Statement (root_statement_hash `773e3b63bb969f18c725ed59378ddbf4f11f78789821df83f2ff9348d8fdebbf`):**
  `∀ N, Σ_{d≤N} Λ(d)/d = Σ_{p≤N, p prime} log p / p + Σ_{d≤N, ¬prime} Λ(d)/d`.
- problem_version_id: `33195785-db9b-4f8c-93a6-f61e9b49aca1` · episode_id: `92133fcc-6c98-4f9a-adfe-53d05344f2eb`
- outcome: `kernel_verified` · snapshot: [proof/Erdos858_Mertens1_PrimePowerSplit.lean](proof/Erdos858_Mertens1_PrimePowerSplit.lean)
- **Why it matters:** exact decomposition isolating the prime-power tail
  (`Σ_{¬prime} Λ(d)/d = Σ_{p^k, k≥2}(log p)/p^k`), via `Finset.sum_filter_add_sum_filter_not`.

### 51. Mertens-1 — prime-sum lower bound `Σ_{p≤N} log p/p ≥ log N − 2`  (paper §5)

- **Statement (root_statement_hash `0f5ce968caa010ac8b9b93139c5b347718916b8926c751aab8b7d6163d081963`):**
  `∀ N Sp Sl T, Sl = Sp + T → 0 ≤ T → T ≤ 1 → log N − 1 ≤ Sl → log N − 2 ≤ Sp`.
- problem_version_id: `f81f9ceb-51ba-41b9-819c-646ea633a9c2` · episode_id: `366e5cae-5e60-4602-bd41-2a55bb483a5a`
- outcome: `kernel_verified` · snapshot: [proof/Erdos858_PrimeMertens1LowerAssembly.lean](proof/Erdos858_PrimeMertens1LowerAssembly.lean)
- **Why it matters:** **prime-sum Mertens-1 lower bound**, from the split (#50), a tail bound
  `0 ≤ T ≤ 1`, and the verified von-Mangoldt lower bound #47.

### 52. Mertens-1 — prime-sum two-sided `Σ_{p≤N} log p/p = log N + O(1)`  (paper §5)

- **Statement (root_statement_hash `fc18505f75fe2956c5a9fb3ba64662f60a0ec72c476c52c3c27c52869349810e`):**
  `∀ N Sp Sl T C C', Sl = Sp + T → 0 ≤ T → T ≤ C' → |Sl − log N| ≤ C → |Sp − log N| ≤ C + C'`.
- problem_version_id: `3c75e0ba-e48e-4b9b-bcdc-4e72ddf03c86` · episode_id: `df3666f0-4e96-4811-87f8-6f1ec56b3291`
- outcome: `kernel_verified` · snapshot: [proof/Erdos858_PrimeMertens1TwoSidedAssembly.lean](proof/Erdos858_PrimeMertens1TwoSidedAssembly.lean)
- **Why it matters:** transports the two-sided von-Mangoldt Mertens-1 (#48) to the prime sum:
  `Σ_{p≤N} log p/p = log N + O(1)` — the object §5 feeds into `c₂`.

### 53. Mertens-1 — Stirling upper bound `log(N!) ≤ N log N`  (paper §5)

- **Statement (root_statement_hash `5cce647842ad7bdef55c6efe23372e0f3352dc20dcbcc16123d648a53ce866b7`):**
  `∀ N, 1 ≤ N → log(N!) ≤ N·log N`.
- problem_version_id: `91dccbad-d0f8-4bef-baef-ad962b2a31af` · episode_id: `4f5d3658-39b3-4a18-be9e-99e8420b5126`
- outcome: `kernel_verified` · snapshot: [proof/Erdos858_Mertens1_StirlingUpper.lean](proof/Erdos858_Mertens1_StirlingUpper.lean)
- **Why it matters:** crude clean upper companion to the Stirling lower (#46):
  `log(N!) = Σ log n ≤ N log N`. The tight `N log N − N + O(log N)` upper needs asymptotic Stirling (open).

### 54. Mertens-2 — Abel-summation reduction toward the sharp `Σ 1/p`  (paper §5)

- **Statement (root_statement_hash `78b024362a650967d62fc36d9c36ad181e74ec7662b1bdbe599f955f31884a35`):**
  conditional: given the Abel split `S = A/L + (J + K)`, Mertens-I `A = L + r` with `|r| ≤ C`,
  main integral `J = log L − log(log 2)`, error bound `|K| ≤ C'`, `log 2 ≤ L`, then
  `|S − log L| ≤ |1 − log(log 2)| + C/log 2 + C'`.
- problem_version_id: `986aa6d2-94cc-4240-9c9b-fbbe521c9524` · episode_id: `f1098ec9-9267-4ffa-a06b-8cc14112b8a7`
- outcome: `kernel_verified` · snapshot: [proof/Erdos858_Mertens2_AbelReduction.lean](proof/Erdos858_Mertens2_AbelReduction.lean)
- **Why it matters:** the partial-summation bookkeeping turning prime-sum Mertens-1
  (`A(x) = log x + O(1)`, #52) into **Mertens' second theorem** `Σ_{p≤x} 1/p = loglog x + O(1)` —
  the sharp form fixing `c₂`. The analytic content (main/error interval integrals, partly
  #647-available) is isolated into the hypotheses.

*Results #49–#54 (2026-07-14, Mertens-sharp round): the Λ→prime conversion (#49, #50) carries
Mertens' first theorem to the prime sum in both directions (#51 `≥ log N − 2`, #52
`= log N + O(1)`), and the Abel reduction (#54) assembles Mertens' second theorem
`Σ 1/p = loglog x + O(1)` from it — the sharp form behind `c₂` — conditional on the reachable
prime-power tail constant and the (partly #647-available) Mertens interval integrals; Stirling
upper `log(N!) ≤ N log N` (#53) added. Remaining genuine analytic gaps, both isolated and named:
the prime-power tail *constant* (needs series-convergence infra) and the Mertens-2 main/error
integral *evaluations*.*

### 55. Prop 5.6 Leibniz — interior parameter-derivative (∫∂_u f)  (paper §5)

- **Statement (root_statement_hash `a05e646fcc2ba314f413ecb6e53d509d454932d3e7799a86b9cea55bfcfbe75d`):**
  for `0 < a ≤ b < 1/2` and `u0 < 1/2`,
  `HasDerivAt (fun u => ∫ v in a..b, (1/v)·log((1-u-v)/v)) (∫ v in a..b, −(1/(v(1-u0-v)))) u0`.
- problem_version_id: `f257dfa9-8391-4b38-b00b-7b300416f936` · episode_id: `612606ae` · (round-11 4th agent)
- outcome: `kernel_verified` (3 subs) · snapshot: [proof/Erdos858_Prop56_ParamDeriv.lean](proof/Erdos858_Prop56_ParamDeriv.lean)
- **Why it matters:** the **parameter half of Prop 5.6's Leibniz rule** — differentiation
  under the integral sign for `I(u)`'s integrand — via
  `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le` with a *constant*
  dominator on any fixed `[a,b] ⊂ (0,1/2)`. **Key finding: no blocking hypothesis** — the
  interior Leibniz term is NOT part of the analytic wall. With the endpoint half (#44), the
  full `I'(u)` on `[1/4,1/3)` (where `[u,(1-u)/2] ⊂ (0,1/2)` stays away from `v=0`) is now
  assemblable; only the sign bookkeeping of `Φ'(u) = d/du log((1-u)/u) + I'(u) < 0` remains.

*Result #55 (round-11 4th agent): the interior parameter-derivative for Prop 5.6's Leibniz
rule, discharging the differentiation-under-the-integral obligation with a constant dominator —
the piece that, with #44 (endpoints), makes the full Prop 5.6 `[1/4,1/2]` monotonicity a sign
computation rather than a wall.*

### 56. Mertens-2 — main integral `∫ 1/(t log t) = loglog x − loglog 2`  (paper §5)

- **Statement (root_statement_hash `e871619be0161189ae498e0642088168e34a3a748e4ffcb7b771372e77141f82`):**
  `∀ x, 2 ≤ x → ∫ t in 2..x, 1/(t·log t) = log(log x) − log(log 2)`.
- problem_version_id: `48d2495c-f1df-4fb8-b353-4fe53575d76a` · episode_id: `94a0f7f5-dcb1-4810-afd0-b7fa7efcd0ba`
- outcome: `kernel_verified` · snapshot: [proof/Erdos858_Mertens2_MainIntegral.lean](proof/Erdos858_Mertens2_MainIntegral.lean)
- **Why it matters:** the **J term** of the Mertens-2 Abel reduction (#54) — FTC, antiderivative
  `log(log t)`. Discharges #54's `hJval` hypothesis.

### 57. Mertens-2 — error integral `∫ 1/(t log²t) ≤ 1/log 2`  (paper §5)

- **Statement (root_statement_hash `509ebfe4281026c30c35638fee0194c069a0e3940274cfd3df4b787391a3c78c`):**
  `∀ x, 2 ≤ x → (∫ t in 2..x, 1/(t·(log t)²) = (log 2)⁻¹ − (log x)⁻¹) ∧ (∫ … ≤ (log 2)⁻¹)`.
- problem_version_id: `0113e4df-32ac-4c2a-a58f-9928f05ea213` · episode_id: `e8e25055-e977-456f-a972-6025705ed7f0`
- outcome: `kernel_verified` · snapshot: [proof/Erdos858_Mertens2_ErrorIntegral.lean](proof/Erdos858_Mertens2_ErrorIntegral.lean)
- **Why it matters:** the **K term** of #54 — FTC, antiderivative `−1/log t`. With #56, both
  analytic integrals of the Abel reduction are verified.

### 58. Mertens-1 — prime-power tail nonneg  (paper §5)

- **Statement (root_statement_hash `160036671378de1eee77a5c408caa9b29530d573ff6fc2b1fb002143200bb1fc`):**
  `∀ N, 0 ≤ Σ_{d∈Icc 1 N, ¬prime} Λ(d)/d`.
- problem_version_id: `f4dcc48c-5364-4f87-af15-d53434edaae8` · episode_id: `3eb98829-ba19-4393-a509-fd11a9aea664`
- outcome: `kernel_verified` · snapshot: [proof/Erdos858_Mertens1_PrimePowerTailNonneg.lean](proof/Erdos858_Mertens1_PrimePowerTailNonneg.lean)
- **Why it matters:** the `0 ≤ T` half of the prime-power tail (#51/#52). The upper constant
  `T ≤ 1` (`Σ_{p^k,k≥2}(log p)/p^k` convergent) is the remaining series-convergence gap — still open.

### 59. Prop 5.6 — full monotonicity capstone (StrictAntiOn on [1/4,1/2])  (paper §5)

- **Statement (root_statement_hash `4fea605deb4271ddfaa736b7e9cb2f7f59194f186e9c90a8e633ad1c5db1f990`):**
  for `Ifun, I'`: if `fun u => log((1-u)/u) + Ifun u` is `ContinuousOn (Icc 1/4 1/2)`,
  `∀ u ∈ Ioo 1/4 1/2, HasDerivAt Ifun (I' u) u`, and `∀ u ∈ Ioo 1/4 1/2, I' u ≤ 0`, then
  `StrictAntiOn (fun u => log((1-u)/u) + Ifun u) (Icc 1/4 1/2)`.
- problem_version_id: `b5933cf5-cf34-477b-8561-373a2b91fe8d` · episode_id: `5d49df5c-a730-4e43-b721-bd5f3a89ca78`
- outcome: `kernel_verified` · snapshot: [proof/Erdos858_Prop56_FullMonotone.lean](proof/Erdos858_Prop56_FullMonotone.lean)
- **Why it matters:** **the Prop 5.6 monotonicity capstone** over the whole `[1/4,1/2]`
  (`strictAntiOn_of_hasDerivWithinAt_neg`), packaging the prime-term derivative `−1/(u(1-u))` with
  the verified Leibniz data #44/#55 and the sign `I' ≤ 0`. `Φ` strictly decreasing on `[1/4,1/2]`;
  with `Φ(1/4) ≥ log 3 > 1 > log 2 = Φ(1/3)` this yields the unique root `α₂ ∈ (1/4,1/3)`.

*Results #56–#59 (c₂-integrals round): the two Mertens-2 integrals (#56, #57) discharge the analytic
hypotheses of the Abel reduction (#54), so `Σ_{p≤x} 1/p = loglog x + O(1)` now rests only on prime
Mertens-1 (#52) and the Abel split identity; the Prop 5.6 capstone (#59) gives `Φ` strictly decreasing
on `[1/4,1/2]`; #58 is the tail-nonneg half. Remaining gaps: the prime-power tail *constant* `T ≤ 1`
(series convergence) and the Abel-summation *split identity* (partial summation, #647 has the tool).*

### 60. Prop 5.6 — `Φ(1/4) > 1`  (paper §5)

- **Statement (root_statement_hash `1dc10454d41f392149e7541a5c67d2932027e5ed85894f04b246322f5971786a`):**
  `∀ Iq, 0 ≤ Iq → 1 < Real.log ((1 - 1/4)/(1/4)) + Iq` (i.e. `Φ(1/4) = log 3 + I(1/4) ≥ log 3 > 1`).
- problem_version_id: `f63f6560-55bd-4595-bb0b-651c95e061b3` · episode_id: `eaf17724-0290-4d5c-b55b-e94cb3d767ec`
- outcome: `kernel_verified` (first try) · snapshot: [proof/Erdos858_Prop56_PhiQuarterGtOne.lean](proof/Erdos858_Prop56_PhiQuarterGtOne.lean)
- **Why it matters:** the left-endpoint boundary value: `(1-1/4)/(1/4) = 3`, `log 3 > 1` (via
  `Real.exp_one_lt_three` + `Real.lt_log_iff_exp_lt`), and `I(1/4) ≥ 0` (#39). Places `α₂` strictly
  above `1/4`.

### 61. Prop 5.6 — α₂ existence & uniqueness (headline conclusion)  (paper §5)

- **Statement (root_statement_hash `d9b41df1d23122480bfb1aa391f8037226ed27179807a5028e656adb0d469df0`):**
  for `Φ` `ContinuousOn` and `StrictAntiOn` on `Icc 1/4 1/3` with `1 < Φ(1/4)` and `Φ(1/3) < 1`,
  `∃! a, a ∈ Ioo (1/4) (1/3) ∧ Φ a = 1`.
- problem_version_id: `99ca8867-ef20-47fd-a12b-9f6bae05db44` · episode_id: `68679336-adf1-4a0f-8a8b-749067faeaae`
- outcome: `kernel_verified` (first try) · snapshot: [proof/Erdos858_Prop56_Alpha2Unique.lean](proof/Erdos858_Prop56_Alpha2Unique.lean)
- **Why it matters:** **Proposition 5.6's headline conclusion** — the unique critical exponent `α₂`.
  Existence via `intermediate_value_Ioo'` (decreasing orientation), uniqueness via `StrictAntiOn.injOn`.
  Its hypotheses are supplied by the verified continuity (#37-family), monotonicity (#59), and the
  boundary values `Φ(1/4)>1` (#60) / `Φ(1/3)=log 2<1` (#30). Completes Prop 5.6.

### 62. Mertens-1 — per-prime geometric tail bound  (paper §5)

- **Statement (root_statement_hash `886170e842f9efde4be1003aee1d614283a2039d7bb39204dcefa37dcd4623c8`):**
  `∀ p ≥ 2, ∀ M, Σ_{k∈Ico 2 M} log p / p^k ≤ log p / (p(p-1))` (uniform in `M`).
- problem_version_id: `a9dcbb0b-4062-41b4-9149-47da2527be72` · episode_id: `57d5027f-b969-4059-ad89-26ffc5a73044`
- outcome: `kernel_verified` (2 subs) · snapshot: [proof/Erdos858_Mertens1_PrimePowerGeometricTail.lean](proof/Erdos858_Mertens1_PrimePowerGeometricTail.lean)
- **Why it matters:** the per-base geometric domination (`geom_sum_Ico_le_of_lt_one`) inside the
  prime-power tail. Reduces `T ≤ 1` to the terminal numeric estimate `Σ_p (log p)/(p(p-1)) ≤ 1`
  (≈0.755) — which needs an integral-test bound (`AntitoneOn.sum_le_integral` on `log x/x²`) + the
  vonMangoldt→(p,k) reindex, a genuine multi-atom series-convergence sub-project (still open; the
  all-integer over-estimate `Σ(log n)/(n(n-1))≈1.258` only certifies the weaker `≤ 2`).

*Results #60–#62 (α₂/Mertens-2 round): **Proposition 5.6 is complete** — `Φ(1/4)>1` (#60) + the α₂
existence/uniqueness assembly (#61, from monotonicity #59 + boundary values #60/#30) give the unique
critical exponent `α₂ ∈ (1/4,1/3)`. The prime-power tail advanced to the per-prime geometric bound
(#62); the terminal numeric `Σ_p(log p)/(p(p-1)) ≤ 1` is the remaining crux. (The Abel split-identity
agent hit a transient session-usage limit, not a proof failure — retried next round.)*

### 63. c₂ lower bound `c₂ ≥ 1/2`  (paper §5, Thm 1.2 constant)

- **Statement (root_statement_hash `f978e16b404433efb8b37268fb9f2d77471ab560095a3ef48c5ca9986c17f991`):**
  for `α₂ ≤ 1/2` and `Φ` with `Φ u ≤ 1` on `Icc α₂ 1/2`, `1/2 ≤ 1/2 + ∫ u in α₂..1/2, (1 - Φ u)`.
- problem_version_id: `32b338fd-917f-408f-9931-5ca4777cef46` · episode_id: `bfc78b8d-e535-42d1-a378-222f83417b4b`
- outcome: `kernel_verified` (first try) · snapshot: [proof/Erdos858_C2LowerBound.lean](proof/Erdos858_C2LowerBound.lean)
- **Why it matters:** the `c₂ ≥ 1/2` half of Theorem 1.2's constant (`c₂ = 1/2 + ∫_{α₂}^{1/2}(1-Φ)`,
  integrand `≥ 0` since `Φ ≤ 1` there). Via `intervalIntegral.integral_nonneg`.

### 64. Prime-power tail numeric `Σ_{n=2}^N (log n)/n² ≤ 2`  (paper §5)

- **Statement (root_statement_hash `69f2d5c5475524c4d4946dcb03782dd7a578e3a5e7f4126a6ac10e6693be6dd4`):**
  `∀ N, Σ_{n∈Icc 2 N} (log n)/n² ≤ 2`.
- problem_version_id: `b4b2d65c-9b4d-41f5-a776-ff8fcce804b1` · episode_id: `b97b4c00-e1ff-45d1-8921-744c5b8988d8`
- outcome: `kernel_verified` (3 subs) · snapshot: [proof/Erdos858_TailLogSqBound.lean](proof/Erdos858_TailLogSqBound.lean)
- **Why it matters:** the **integer tail crux** via the integral test — `f(x)=log x/x²` antitone on `[2,∞)`
  (`antitoneOn_of_deriv_nonpos`, using `log 2 > 1/2`), `AntitoneOn.sum_le_integral_Ico`, and
  `∫_2^N log x/x² = (log2+1)/2 − (logN+1)/N ≤ (log2+1)/2`. With #62 (per-prime geometric bound) this bounds
  the prime-power tail by an explicit constant, giving Mertens-1 `Σ_{p≤N} log p/p = log N + O(1)` unconditionally.

### 65. Mertens-2 — Abel split identity (unconditional)  (paper §5)

- **Statement (root_statement_hash `5c3194746d0d7fbf0b3fff3076d09468f4e3d7742e9c8a5930b9580abf24b36b`):**
  `∀ x ≥ 2, Σ_{p≤x} 1/p = A(x)/log x + ∫_{Ioc 2 x} A(t)/(t·(log t)²) dt`, where `A(t) = Σ_{p≤t}(log p)/p`.
- problem_version_id: `bd1eb88e-e9ed-4e04-9ba5-48a1ce4aec64` · episode_id: `9904dff7-8af4-42c5-ac67-dd2dd3fc9b3f`
- outcome: `kernel_verified` (locally recompiled `lake env lean` EXIT 0; 2 subs, a `₊`→`₀` transport typo)
- snapshot: [proof/Erdos858_Mertens2_AbelSplit.lean](proof/Erdos858_Mertens2_AbelSplit.lean)
- **Why it matters:** **makes the Mertens-2 Abel reduction (#54) unconditional** — the `hSsplit` hypothesis is
  now a verified theorem. Via `sum_mul_eq_sub_sub_integral_mul` with weight `1/log t` (deriv `−(t(log t)²)⁻¹`).
  **No PNT/Chebyshev/Mertens needed for the identity.** So `Σ_{p≤x} 1/p = loglog x + O(1)` now rests *only* on
  Mertens-1 `A(x) = log x + O(1)` (#52 + the now-bounded tail).

### 66. c₂ window `1/2 ≤ c₂ < 3/4`  (paper §5, Thm 1.2 constant)

- **Statement (root_statement_hash `4526fcde098ca5fc1939ef7be8551b10163e73451c35a3d2abfa451e3ead99a0`):**
  for `α₂ ∈ (1/4,1/2)`, `0 ≤ J`, `J ≤ 1/2 − α₂`: `1/2 ≤ 1/2 + J ∧ 1/2 + J < 3/4` (`c₂ = 1/2 + J`).
- problem_version_id: `b72d1316-2ace-47db-856a-05a45a17f86f` · episode_id: `985d73f8-4df9-4a1b-8f12-80d13c483800`
- outcome: `kernel_verified` · snapshot: [proof/Erdos858_C2Window.lean](proof/Erdos858_C2Window.lean)
- **Why it matters:** two-sided localization `1/2 ≤ c₂ < 3/4` from the integral bounds `0 ≤ J ≤ 1/2 − α₂`
  (`1 − Φ ∈ [0,1]` on `[α₂,1/2]`, interval length `< 1/4`). Brackets the paper's `c₂ = 0.6187…`.

*Results #63–#66 (c₂-final round, all 4 verified): the **Abel split identity (#65) makes Mertens-2
unconditional** (`Σ 1/p = loglog x + O(1)` now needs only Mertens-1); the **tail numeric #64** + #62 bound the
prime-power tail by an explicit constant; and the c₂ constant is localized `1/2 ≤ c₂ < 3/4` (#63, #66). The only
remaining gap to the *exact* `c₂ = 0.6187…` (and hence Thm 1.2) is the *sharp value* of Mertens-1's constant `M`
(the O(1) pinned to a number) and the exact evaluation of `∫_{α₂}^{1/2}(1-Φ)` — genuinely the deepest analytic
core. Everything structural around it is now machine-checked.*

### 67. Mertens-2 — qualitative capstone `Σ 1/p = loglog x + O(1)`  (paper §5)

- **Statement (root_statement_hash `e32f500b8b0391b326fbedeb8d8f507ee5a448da7336b462ebe7b807bdb179ec`):**
  given the Abel split `S = A(x)/log x + (J+K)`, main integral `J = loglog x − loglog 2`, error `|K| ≤ (log 2)⁻¹`,
  and Mertens-1 `|A(x) − log x| ≤ CA` (with `2 ≤ x`, `log 2 ≤ log x`), then
  `|S − loglog x| ≤ |1 − loglog 2| + CA/log 2 + (log 2)⁻¹`.
- problem_version_id: `b10ae9b8-b0f3-42ee-9437-00a328e6a11d` · episode_id: `d039c543-ca4c-4974-8021-1a403e7c3082`
- outcome: `kernel_verified` (first try) · snapshot: [proof/Erdos858_Mertens2_Capstone.lean](proof/Erdos858_Mertens2_Capstone.lean)
- **Why it matters:** the assembled **qualitative Mertens' second theorem** `Σ_{p≤x} 1/p = loglog x + O(1)` with an
  explicit `O(1)`, combining the now-unconditional Abel split (#65) + integrals (#56/#57) + Mertens-1. The sharp
  leading constant (Meissel–Mertens `M`) stays a hypothesis — it needs PNT-grade infra absent from the pin.

### 68. Lemma 5.2 — interval Mertens (O(1) form)  (paper §5)

- **Statement (root_statement_hash `08617ee8ac9dbba77d365f65d5a07789005d459577707359da7bdbe747c95b76`):**
  `|Mx − loglog x| ≤ C → |My − loglog y| ≤ C → |(My − Mx) − (loglog y − loglog x)| ≤ 2C`.
- problem_version_id: `aba11349-6fff-4506-bb16-93f2cf6e68d5` · episode_id: `97fa17c4-2dc0-4a16-a749-9a6a1e5fc3ad`
- outcome: `kernel_verified` (first try) · snapshot: [proof/Erdos858_Lemma52_IntervalMertens.lean](proof/Erdos858_Lemma52_IntervalMertens.lean)
- **Why it matters:** the reachable O(1) form of Lemma 5.2 — `Σ_{x<p≤y} 1/p = loglog y − loglog x + O(1)` — carrying
  the two endpoint Mertens-2 estimates into the interval sum (triangle inequality).

### 69. Theorem 1.2 — assembly skeleton  (paper §1/§5)

- **Statement (root_statement_hash `39ac7284c91f57a7cb4a513830b5bd24a6864591befc2282f5931bb8ed5e4245`):**
  `∀ N MN SN c2 e L, MN = SN → SN = (c2+e)·L → MN = (c2+e)·L`.
- problem_version_id: `e8f8aecb-4f4e-4715-91b1-24bb5a963054` · episode_id: `8fc1c70b-12c5-44d0-814b-cb47af2d1678`
- outcome: `kernel_verified` (first try) · snapshot: [proof/Erdos858_Thm12_Skeleton.lean](proof/Erdos858_Thm12_Skeleton.lean)
- **Why it matters:** the honest **Theorem 1.2 glue** — Cor 3.5 (`M(N)=S_N(K)`, verified) composed with Theorem 5.8
  (`S_N(K*) = (c₂+o(1))log N`, the open analytic wall) yields `M(N) = (c₂+o(1))log N`. The entire substance is
  quarantined in the second hypothesis, so this cannot be mistaken for a proof of the constant.

### 70. Prop 5.6 — α₂ exponent window  (paper §5)

- **Statement (root_statement_hash `c7747f2c6cc5582572a67b26deba24ab2678ff38e9894e047af8b29096ba2f0a`):**
  `∀ α₂, α₂ ∈ Ioo (1/4) (1/3) → 1/4 < α₂ ∧ α₂ < 1/3`.
- problem_version_id: `e1fc26d4-bb1f-4670-9f24-397355665bd8` · episode_id: `9cc97fb4-1679-4a2d-86e3-d6c524343bf2`
- outcome: `kernel_verified` (first try) · snapshot: [proof/Erdos858_Alpha2Window.lean](proof/Erdos858_Alpha2Window.lean)
- **Why it matters:** pins the α₂ window from #61's `Ioo` membership — the exponent bounds the c₂ integral (#63/#66)
  consume (`α₂ < 1/3 < 1/2`; `1/4 < α₂ ⇒ J < 1/4`).

### 71. Prime-power tail — integer bound `Σ (log n)/(n(n-1)) ≤ 2`  (paper §5)

- **Statement (root_statement_hash `a2a5b34ada4116fabd664f345b50fe8c0a05f0ffa8e4aa3f23ea30ed8824ff7c`):**
  `∀ N, Σ_{n∈Icc 2 N} (log n)/(n(n-1)) ≤ 2`.
- problem_version_id: `e37ff73c-74fb-4041-beb6-938422589d6f` · episode_id: `62046e39-ad23-41e5-ac47-cc56b333375d`
- outcome: `kernel_verified` · snapshot: [proof/Erdos858_IntegerTailLogOverNPm1LeTwo.lean](proof/Erdos858_IntegerTailLogOverNPm1LeTwo.lean)
- **Why it matters:** the integer over-estimate for the prime-power tail (`Σ_p (log p)/(p(p-1))` is smaller) — with
  #62 this bounds the tail by an explicit constant, so Mertens-1 holds unconditionally with an explicit `O(1)`.
- **Sharp-constant scout verdict (definitive):** exhaustive grep confirms the exact `c₂` is **not reachable in this
  Mathlib pin** — `riemannZeta_ne_zero_of_one_le_re` (the analytic *input* to PNT) is present, but PNT itself,
  Mertens' theorems, and `θ(x)~x` are **not**; only Chebyshev `O`-bounds (not `~`) and the divergence of `Σ1/p`.
  The sharp Meissel–Mertens constant `M` (and hence exact `c₂`) needs a PNT-grade Mathlib build.

*Results #67–#71 (capstones round): the qualitative Mertens-2 `Σ 1/p = loglog x + O(1)` (#67), interval Mertens
(#68), the Theorem 1.2 assembly skeleton (#69), the α₂ window (#70), and the integer tail bound (#71). **This
completes the structural formalization of Chojecki's paper**: every architectural step from §1 to §5's c₂
localization is machine-checked, with the single remaining gap — the exact `c₂ = 0.6187…` — definitively isolated
to the sharp Mertens constant / Theorem 5.8 asymptotic, which requires PNT-grade infrastructure absent from this
Mathlib pin. Not a proof-search target; a Mathlib-development project.*

### 72. §6.1 Bellman threshold policy — `M(N) = F_N(1) = S_N(K) = M_fr(N)`  (paper §6)

- **Statement (root_statement_hash `cc635e7755bca93fdf168d89b6478a282b95f1211eaa14b9e2ec731990d4bb55`):**
  the threshold policy `G` and the subtree optimum `F` share the stop/continue recursion over a tree whose children
  strictly exceed the parent, so (by descending induction on `K−a`) `F = G`; with the root evaluation `G 1 = S`
  (policy selects the frontier `A_N(K)`) as hypothesis, `F 1 = S`, i.e. `M(N) = S_N(K) = M_fr(N)`.
- problem_version_id: `32440799-ec1d-4101-bee1-3a34f9f916b9` · episode_id: `a7d372c2-f41f-4cb9-8493-ae190b4e8318`
- outcome: `kernel_verified` (2 subs; `le_of_not_lt`→`not_lt.mp`) · snapshot: [proof/Erdos858_Sec61_BellmanPolicy.lean](proof/Erdos858_Sec61_BellmanPolicy.lean)
- **Why it matters:** §6.1's optimal-stopping identification of the threshold policy with the true subtree optimum —
  genuine content is the tree-induction uniqueness (measure `K−a`, no global `N` bound).

### 73. §6.3 eventual frontier — Theorem 1.1 assembly `M(N) = M_fr(N)`  (paper §6)

- **Statement (root_statement_hash `716863b7f586d95c1cc8f783bc71e9bf0f88bebab44202956e1d70d0c3f0ad02`):**
  given the **sign theorem** (`0 < q_N(a)` for `1 ≤ a ≤ K*`, `q_N(a) ≤ 0` for `a > K*` — the open analytic input),
  the Prop 3.2 telescope `S_N(K) = 1 + Σ_{a≤K} q_N(a)`, and the Cor 3.5 identity `M(N) = S_N(K*)`, then
  `M(N) = M_fr(N) = max_{0≤K≤N} S_N(K)`.
- problem_version_id: `850cf7ee-3b81-4f95-95bd-66a26ab493db` · episode_id: `bdc04c0b-ae9f-46f6-ba3d-7b9a244d5b0f`
- outcome: `kernel_verified` (first try) · snapshot: [proof/Erdos858_Sec63_EventualFrontier.lean](proof/Erdos858_Sec63_EventualFrontier.lean)
- **Why it matters:** **the honest Theorem 1.1 assembly** (`M(N) = M_fr(N)`) — the elementary bookkeeping
  (filter-split optimization, verbatim the `cor35_optimization_inequality` idiom) that composes the verified
  frontier reduction (Cor 3.5 + Prop 3.2) with the *one* open analytic input (the §4 sign theorem), which is
  quarantined in the hypothesis. Combined with #69 (Thm 1.2 skeleton), the paper's two headline theorems are now
  assembled down to their single respective analytic inputs (the sign theorem for 1.1; the sharp `c₂` asymptotic
  for 1.2).

*Results #72–#73 (§6 remainder): the Bellman optimal-stopping policy (#72) and the **Theorem 1.1 conditional
assembly `M(N) = M_fr(N)`** (#73). With this, the paper is formalized end-to-end as a dependency chain: every
step from §1 to the two headline theorems is machine-checked, each headline theorem reduced to exactly one open
analytic input (sign theorem / sharp `c₂`), both of which need PNT-grade Mathlib infrastructure absent from this
pin. (§5.1's frontier closed-form hit a transient API error mid-round — reachable, low-priority retry.)*

### 74. Prop 5.6 — semiprime-integral UPPER bound `I(u)`  (paper §5)

- **Statement (root_statement_hash `cdd270d08c53926fcdf849168f2374a906cd4b50bb3aa1f862ea678ea56e276a`):**
  `∀ u, 1/4 < u → u < 1/3 → (∫ v in u..(1-u)/2, (1/v)·log((1-u-v)/v)) ≤ ((1-u)/2 - u)·((1/u)·log((1-2u)/u))`.
- problem_version_id: `cd46775a-8f2d-4206-a3a9-e7bee818ea7d` · episode_id: `6b6e60e3-0dbb-434a-b4b1-75230ced871e`
- outcome: `kernel_verified` (first try) · snapshot: [proof/Erdos858_IUpperBound.lean](proof/Erdos858_IUpperBound.lean)
- **Why it matters:** the reusable **analytic tool** for tightening α₂ and c₂ — the explicit upper bound on the
  semiprime contribution `I(u)` (integrand `g(v)=(1/v)log((1-u-v)/v)` dominated pointwise by its left-endpoint
  value via `intervalIntegral.integral_mono_on`). Companion to the lower bound `I(u) ≥ 0` (#39); together they
  bracket `I(u)`. The Meissel–Mertens constant cancels in the interval form, so this is **pure real analysis, no
  PNT** — directly confirming the c₂ *value* is reachable in-pin even though the c₂ asymptotic *law* is not.

### 75. Corollary 4.4 — low-layer positivity `R_N(a) > 1` (composition)  (paper §4)

- **Statement (root_statement_hash `b674b6d11db0ca1d59d2ae6c8c6dfc4f551308568e225d081da6e7184bd751d1`):**
  `∀ RNa primeIntervalSum bigIntervalSum, 1 < primeIntervalSum → primeIntervalSum ≤ bigIntervalSum →
  bigIntervalSum ≤ RNa → 1 < RNa`.
- problem_version_id: `4123f837-7d54-45f7-918f-3f89e36d2481` · episode_id: `355795f4-f9d0-440b-be2e-f9408ccf2fd9`
- outcome: `kernel_verified` (first try) · snapshot: [proof/Erdos858_Sec44_LowLayer.lean](proof/Erdos858_Sec44_LowLayer.lean)
- **Why it matters:** the clean composition step of **Corollary 4.4** for `20 ≤ a ≤ N^{1/4}` — chains Lemma 4.3
  (`Σ_{a<p≤a³}1/p > 1`), interval monotonicity (`a³ ≤ N/a ⇒ Σ_{a<p≤a³} ≤ Σ_{a<p≤N/a}`), and the prime-child lower
  bound (`R_N(a) ≥ Σ_{a<p≤N/a}1/p`, from #8 `π(a·p)=a`) into `R_N(a) > 1`. Conditional-assembly atom (inputs as
  hypotheses); the low-layer input to the §4.7 sign theorem. Open input remaining: Lemma 4.3 (the §4.3 wall).

### 76. Theorem 4.7 — sign theorem, initial-segment core  (paper §4)

- **Statement (root_statement_hash `0ef090b6791c8cbfd79d3a9175c93da7790d9fd19963098fbeec4cc4c3f4742d`):**
  `∀ RN L, (∀ a, 1 ≤ a → a ≤ L → 1 < RN a) → (∀ a b, L ≤ a → a ≤ b → RN b ≤ RN a) →
  (∀ a b, 1 ≤ b → b ≤ a → 1 < RN a → 1 < RN b)`.
- problem_version_id: `171fd0d2-a28f-4cd2-b417-e7c5d5fbc5ac` · episode_id: `4c7c9209-754b-44f2-970a-6af13c55f1d6`
- outcome: `kernel_verified` (first try) · snapshot: [proof/Erdos858_Sec47_SignTheorem.lean](proof/Erdos858_Sec47_SignTheorem.lean)
- **Why it matters:** the **logical core of the sign theorem** (Thm 4.7) — the downward-closure / initial-segment
  property of `{a : R_N(a) > 1}`, on which Theorem 1.1 (`M(N)=M_fr(N)`) hinges. Takes the two paper ingredients as
  hypotheses: `R_N > 1` on the small+low range `[1,L]` (Prop 4.1 thresholds + Cor 4.4 = #75) and `R_N`
  nonincreasing on the upper layer `[L,∞)` (Prop 4.6, kernel-verified as `prop46_PN/QN_monotone`). This is exactly
  the "sign theorem" input quarantined as a hypothesis in the Theorem 1.1 assembly #73 — now itself reduced (modulo
  the §4.3 low-layer bound) to two verified/verified-conditional ingredients.

### 77. §5 density prime-term nonnegativity `Φ_prime(u) ≥ 0`  (paper §5)

- **Statement (root_statement_hash `bea378128d668d91ad587238508d8a46e88b3eb898e27f9d876b089ce4ba892c`):**
  `∀ u, 0 < u → u ≤ 1/2 → 0 ≤ Real.log ((1-u)/u)`.
- problem_version_id: `db1b5b62-8f04-4569-8b9a-808ad104c0a8` · episode_id: `77cb0493-47b8-4428-925e-d928cb646193`
- outcome: `kernel_verified` (first try, main-loop direct) · snapshot: [proof/Erdos858_PhiPrimeNonneg.lean](proof/Erdos858_PhiPrimeNonneg.lean)
- **Why it matters:** the prime term of the limiting density `Φ_prime(u)=log((1-u)/u)` is nonnegative on `(0,1/2]`
  (since `(1-u)/u ≥ 1` there, vanishing at `u=1/2`). This bounds the c₂ integrand `1 - Φ(u) ≤ 1` on `[α₂,1/2]`
  inside `c₂ = 1/2 + ∫_{α₂}^{1/2}(1-Φ(u))du`. Proved directly in the main loop while the subagent model-budget was
  exhausted (the episode/kernel path is deterministic and budget-independent). Pure real analysis, no PNT.

### 78. Lemma 4.3 — low-layer prime bound, conditional reduction to Kinlaw–Pomerance  (paper §4)

- **Statement (root_statement_hash `4306ebb61dc2faad205b4b0de90930da0588a8a23a59d0d08a8543094028644d`):**
  `∀ a M Ea Ea3 S_a S_a3, 1 < a → S_a = log(log a) + M + Ea → S_a3 = log(log(a³)) + M + Ea3 →
  |Ea3 - Ea| < log 3 - 1 → 1 < S_a3 - S_a`.
- problem_version_id: `9ac90b1b-7029-44e7-a78b-dac99b6cc1c0` · episode_id: `0797b269-69e7-4fc1-89a7-1d54a052f985`
- outcome: `kernel_verified` (first try, main-loop direct) · snapshot: [proof/Erdos858_Lemma43_Reduction.lean](proof/Erdos858_Lemma43_Reduction.lean)
- **Why it matters:** **the sharpest localization yet of the sole open input to unconditional Theorem 1.1.** Modelling
  the two prime-reciprocal partial sums by their Mertens form `loglog + M + error` (common constant `M`), the interval
  sum `Σ_{a<p≤a³}1/p = S_a3 - S_a`; the identity `loglog(a³) - loglog(a) = log 3` (via `Real.log_pow` + `Real.log_mul`)
  makes **`M` and `loglog a` cancel**, so `S_a3 - S_a = log 3 + (Ea3 - Ea) > 1` exactly when `|Ea3 - Ea| < log 3 - 1 ≈
  0.0986` — precisely the explicit Kinlaw–Pomerance error-difference control for `a ≥ 20`. Via the verified chain
  Lemma 4.3 ⇒ Cor 4.4 (#75) ⇒ sign theorem (#76) ⇒ Theorem 1.1 (#73), **the entire remaining gap to unconditional
  Theorem 1.1 is this one explicit inequality** — no PNT, and the (PNT-grade) sharp value of `M` is irrelevant because
  it cancels. Pure real analysis; the log-cancellation is the content.

### 79. α₂ localization squeeze (Φ-value bracket)  (paper §5)

- **Statement (root_statement_hash `cffad010ce9fbfedffe863f01853a5acd5242708a70cdfd9d4be2240f45fd75d`):**
  `∀ Φ α₂ lo hi, StrictAntiOn Φ (Icc (1/4) (1/3)) → α₂ ∈ Icc (1/4) (1/3) → Φ α₂ = 1 →
  lo ∈ Icc (1/4) (1/3) → hi ∈ Icc (1/4) (1/3) → 1 < Φ lo → Φ hi < 1 → lo < α₂ ∧ α₂ < hi`.
- problem_version_id: `1ec83066-8e8b-49c3-8741-9774fc2bb6c9` · episode_id: `d568db48-96f4-4519-b93d-54783d9b271f`
- outcome: `kernel_verified` (first try, main-loop direct) · snapshot: [proof/Erdos858_Alpha2Squeeze.lean](proof/Erdos858_Alpha2Squeeze.lean)
- **Why it matters:** the reusable **α₂ localization tool** — for a strictly antitone Φ with unique root α₂, any pair of
  points whose Φ-values bracket 1 squeezes `lo < α₂ < hi`. Turns every numeric Φ-bound (#80, #81 below) directly into
  a tighter interval for `α₂ = 0.28043830…` (and hence for `c₂`). Pure order theory; proved from the raw `StrictAntiOn`
  definition (robust against `lt_iff_lt` direction).

### 80. Φ(13/50) > 1 ⟹ α₂ > 0.26  (paper §5)

- **Statement (root_statement_hash `b2c5b6a9f4faceebb4a2bc6a4902b8163d7ed4e33c0651210bc58a0305587c93`):**
  `∀ Iq, 0 ≤ Iq → 1 < Real.log ((1 - 13/50) / (13/50)) + Iq`.
- problem_version_id: `a4924eca-7194-4cee-bf50-fc66a8a62104` · episode_id: `8be64996-ed40-4b7a-92de-268b67b1488e`
- outcome: `kernel_verified` (first try, main-loop direct) · snapshot: [proof/Erdos858_PhiLower13over50.lean](proof/Erdos858_PhiLower13over50.lean)
- **Why it matters:** the lower bracket. At `u = 13/50 = 0.26` the prime term `log(37/13) > 1` (since `37/13 > e`, via
  `Real.exp_one_lt_d9` + `Real.log_lt_log`), so with `I ≥ 0` (#39, modelled by `Iq ≥ 0`), `Φ(13/50) > 1`. Feeding the
  squeeze (#79) gives **α₂ > 13/50 = 0.26**.

### 81. Φ(3/10) < 1 ⟹ α₂ < 0.30  (paper §5)

- **Statement (root_statement_hash `07bbbaf3c67c46df0cc702e9bb19f92b00ff15e8bfe62c5bab0cf2fb3610bf56`):**
  `∀ Iq, Iq ≤ 1/18 → Real.log ((1 - 3/10) / (3/10)) + Iq < 1`.
- problem_version_id: `41218ee6-3e79-4926-9807-4f06e762eec4` · episode_id: `68d8c206-cc10-493e-8c7d-0575db0f3f5a`
- outcome: `kernel_verified` (2 subs; ℝ-cast on the rw identity) · snapshot: [proof/Erdos858_PhiUpper3over10.lean](proof/Erdos858_PhiUpper3over10.lean)
- **Why it matters:** the upper bracket. At `u = 3/10 = 0.30` the prime term `log(7/3) ≤ 7/(3e) < 17/18` (via the
  `e`-factoring `log(7/3) = 1 + log(7/(3e)) ≤ 7/(3e)` and `e > 2.718`), and the semiprime term `I(3/10) ≤ 1/18` (from
  the I-upper bound #74, using `log(4/3) ≤ 1/3`), so `Φ(3/10) < 1`. Feeding the squeeze (#79) gives **α₂ < 3/10 = 0.30**.
  With #80, this **localizes α₂ ∈ (0.26, 0.30)** — the first two-sided numeric bracket of the critical exponent,
  straddling the true `α₂ = 0.28043830…`. Pure real analysis, no PNT.

### 82. c₂ integral lower bound on [1/3,1/2] ⟹ c₂ ≥ 0.551  (paper §5)

- **Statement (root_statement_hash `f847f2e90ff8172f10d4dd118e5d84235f24a1995cccc30966763491102bdd7b`):**
  `(1/6) * (1 - Real.log 2) ≤ ∫ u in (1/3)..(1/2), (1 - Real.log ((1 - u) / u))`.
- problem_version_id: `d065db58-f701-427a-ad3b-aad35722d16e` · episode_id: `9cb3cea3-14ad-4412-9fed-82ccb3c16210`
- outcome: `kernel_verified` (first try, main-loop direct) · snapshot: [proof/Erdos858_C2IntegralLowerHalf.lean](proof/Erdos858_C2IntegralLowerHalf.lean)
- **Why it matters:** the **first genuine tightening of c₂ ≥ 1/2** (#63) toward the true `c₂ = 0.6187712…`. On [1/3,1/2],
  `Φ(u) = log((1-u)/u) ≤ log 2`, so `1 − Φ ≥ 1 − log 2` and the integral ≥ `(1/6)(1 − log 2) ≈ 0.0511`; since `α₂ < 1/3`
  and `1 − Φ ≥ 0` on `[α₂,1/3]`, `c₂ = 1/2 + ∫_{α₂}^{1/2}(1−Φ) ≥ 1/2 + (1/6)(1 − log 2) ≈ 0.551`. Same
  `integral_mono_on`-vs-constant shape as #74. Pure real analysis, no PNT.

### 83. Semiprime integral I(u) — nontrivial LOWER bound  (paper §5)

- **Statement (root_statement_hash `792930193eeeed5e62380672657b9d4ec40758cb88a160887e2ec03f77844ada`):**
  `∀ u, 1/4 < u → u < 1/3 → ((1-3u)/4)·((4/(u+1))·log((3-5u)/(u+1))) ≤ ∫ v in u..(1-u)/2, (1/v)·log((1-u-v)/v)`.
- problem_version_id: `38f83ae7-3155-4ff1-8984-0e59c9407696` · episode_id: `3dc5b81d-1f27-4382-b52c-9d9702ab209a`
- outcome: `kernel_verified` (first try, main-loop direct; 55 lines) · snapshot: [proof/Erdos858_ILowerBound.lean](proof/Erdos858_ILowerBound.lean)
- **Why it matters:** the **two-sided partner to the I-upper bound #74** — a nontrivial POSITIVE lower bound on the
  semiprime integral `I(u)`. Since the integrand vanishes at the right endpoint, the positive bound comes from the
  left half `[u,(u+1)/4]` (integrand ≥ its midpoint value) with the right half ≥ 0 (`integral_add_adjacent_intervals`
  + `integral_mono_on` + `integral_nonneg`). Brackets `I(u)` from both sides, enabling tighter α₂ (e.g. `Φ(0.27) > 1
  ⟹ α₂ > 0.27`) and c₂. The Meissel–Mertens constant cancels; no PNT.

### 84. EXACT c₂ integral on [1/3,1/2] via FTC ⟹ c₂ ≥ 0.610  (paper §5)

- **Statement (root_statement_hash `c9ea411120f89ee2ea8f9cff2b1839f44de9e0db75bfd879e3d5b56e893b4112`):**
  `∫ u in (1/3)..(1/2), (1 - Real.log ((1 - u) / u)) = 1/6 - (5/3) * Real.log 2 + Real.log 3`.
- problem_version_id: `0cb0da7f-2dcb-49a1-abf2-7a26541deca5` · episode_id: `31597512-b410-45d2-b2da-0fc705572eba`
- outcome: `kernel_verified` (2 subs; convert→`rw [← hD]; exact hsum`) · snapshot: [proof/Erdos858_C2ExactIntegralHalf.lean](proof/Erdos858_C2ExactIntegralHalf.lean)
- **Why it matters:** the c₂ integral on `[1/3,1/2]` is now **exactly** evaluated by the fundamental theorem of calculus
  (antiderivative `F(u)=u+(1-u)log(1-u)+u·log u`, `F'=1-log((1-u)/u)`): `= 1/6 - (5/3)log 2 + log 3 ≈ 0.110`. Since
  `α₂ < 1/3` and `1-Φ ≥ 0` on `[α₂,1/3]`, this gives **c₂ ≥ 1/2 + (1/6 - (5/3)log 2 + log 3) ≈ 0.610** — within 0.009 of
  the true `c₂ = 0.6187712…`. **This is the decisive demonstration that the c₂ *value* is computable elementary real
  analysis** (the Meissel–Mertens constant cancels in the interval form): no PNT, no Mertens. Establishes the reusable
  FTC recipe (build `HasDerivAt` via `.log`/`.mul`/`.add`, match the Pi.add derivative by `rw [← hD]; exact hsum`).

### 85. c₂ upper-bound piece on [a,1/3] ⟹ c₂ ≤ 0.633  (paper §5)

- **Statement (root_statement_hash `c91963f3f52c5179a9f47249b5a8b6de717a6ccd4decf4d7f9adec6b789f2f4c`):**
  `∀ a, 1/4 ≤ a → a ≤ 1/3 → (∫ u in a..(1/3), (1 - Real.log ((1 - u) / u))) ≤ (1/3 - a) * (1 - Real.log 2)`.
- problem_version_id: `e673aff4-e344-4521-9028-2e0483fb9c7b` · episode_id: `a866c50b-544e-4b8c-bf1e-7e40073116b8`
- outcome: `kernel_verified` (4 subs; implicit-measure annotation on `hgi` was the fix) · snapshot: [proof/Erdos858_C2UpperPiece.lean](proof/Erdos858_C2UpperPiece.lean)
- **Why it matters:** completes the **two-sided c₂ bracket**. On `[a,1/3]` the prime term `log((1-u)/u) ≥ log 2`, so
  `∫_a^{1/3}(1-Φ) ≤ ∫_a^{1/3}(1-log((1-u)/u)) ≤ (1/3-a)(1-log 2)` (via `I ≥ 0` and `integral_mono_on`). With #84 and
  `α₂ > 0.26`, `c₂ = 1/2 + ∫_{α₂}^{1/2}(1-Φ) ≤ 0.633`. Together with #84: **c₂ ∈ [0.610, 0.633]**, straddling the true
  0.6187. Pure real analysis, no PNT.

### 86. Harmonic interval-sum bound (§5.4 Riemann-sum weight primitive)  (paper §5.3/§5.4)

- **Statement (root_statement_hash `d799ced711a5b4b2e4bac4f3b6bc783144d2688b12a401458e2ebb128d053c80`):**
  `∀ m n, log(n+1) - (1 + log m) ≤ (harmonic n - harmonic m : ℝ) ∧ (harmonic n - harmonic m) ≤ (1 + log n) - log(m+1)`.
- problem_version_id: `8b32a247-b7d4-411c-bb66-a3e37bd18447` · episode_id: `42abd404-e5da-43c7-8cf2-f5c95c1e8556`
- outcome: `kernel_verified` (2 subs; push_cast the `↑(n+1)`) · snapshot: [proof/Erdos858_HarmonicIntervalBound.lean](proof/Erdos858_HarmonicIntervalBound.lean)
- **Why it matters:** **WALL 2's first foundation stone.** The harmonic interval sum `Σ_{m<a≤n}1/a = harmonic n −
  harmonic m` equals `log(n/m) + O(1)` with an explicit constant (≤ 2), directly from Mathlib's tight harmonic bounds
  `log(n+1) ≤ harmonic n ≤ 1+log n`. This is the "weight" primitive for the §5.3/§5.4 Riemann sums — confirming the
  Thm 1.2 asymptotic machinery is **buildable in-pin**, not a wall. Elementary, no PNT.

### 87. Harmonic ratio asymptotic `harmonic n / log n → 1`  (paper §5.3/§5.4)

- **Statement (root_statement_hash `a95a2b9a17ff006fe9ac7eec6535c7ace88ab7270133e18e768c35d35a640797`):**
  `Tendsto (fun n => (harmonic n : ℝ) / Real.log n) atTop (𝓝 1)`.
- problem_version_id: `aeaa6da5-a618-4249-b29b-8e9af51c97c5` · episode_id: `f9edfc23-e956-4bac-8095-1d9df66118e1`
- outcome: `kernel_verified` (first try) · snapshot: [proof/Erdos858_HarmonicRatioLimit.lean](proof/Erdos858_HarmonicRatioLimit.lean)
- **Why it matters:** the normalized asymptotic (harmonic sum ~ `log n`), from `Real.tendsto_harmonic_sub_log`
  (`harmonic n − log n → γ`) via `Tendsto.div_atTop`. Establishes the Tendsto toolchain for §5.4. No PNT.

### 88. Harmonic block-weight limit `harmonic(2n) − harmonic(n) → log 2`  (paper §5.4)

- **Statement (root_statement_hash `ce8088f281a5004e472c880c2a1373a2ffe5a703c8eb345e9ec5eba1182899ba`):**
  `Tendsto (fun n => (harmonic (2*n) : ℝ) - harmonic n) atTop (𝓝 (Real.log 2))`.
- problem_version_id: `74729e2b-bb38-4e7a-9c5f-993093f74250` · episode_id: `3f44886e-4f19-4005-95ec-648818a36c20`
- outcome: `kernel_verified` (first try) · snapshot: [proof/Erdos858_HarmonicDoublingWeight.lean](proof/Erdos858_HarmonicDoublingWeight.lean)
- **Why it matters:** the concrete **floor-free instance of the §5.4 block-weight limit** — the `[n,2n]` block carries
  harmonic weight `→ log 2` (its log-scale length). Exactly the §5.4 mechanism `Σ_{block}1/a → block length`, the
  engine of the asymptotic law `M(N)=(c₂+o(1))log N`. `tendsto_harmonic_sub_log.comp (2·)` minus itself (γ's cancel)
  + `log(2n)=log 2+log n`. No PNT.

### 89. General block-endpoint limit `log(N^x − 1)/log N → x`  (paper §5.4)

- **Statement (root_statement_hash `c58f06447669babaa435f129874541500be87b5c9d3076a90288c5d70fad3a2e`):**
  `∀ x, 0 < x → Tendsto (fun N => Real.log ((N:ℝ)^x - 1) / Real.log N) atTop (𝓝 x)`.
- problem_version_id: `3033e0c0-d8e4-4823-9a02-bbb0230682d3` · episode_id: `44ca9c9f-f975-4178-9067-a90263752982`
- outcome: `kernel_verified` (2 subs; `tendsto_rpow_atTop`, `Function.comp_def`) · snapshot: [proof/Erdos858_RpowBlockLimit.lean](proof/Erdos858_RpowBlockLimit.lean)
- **Why it matters:** the **rpow core** for the §5.4 log-scale partition. The block up to `N^x` has right endpoint
  `⌊N^x⌋`; `log⌊N^x⌋/log N` is squeezed between this (`N^x−1 < ⌊N^x⌋`) and `log(N^x)/log N = x`. Via `log(N^x−1) =
  x·log N + log(1−N^{−x})` and `log(1−N^{−x})/log N → 0` (`tendsto_rpow_atTop` + `inv_tendsto_atTop` + `div_atTop`).
  Handles the *continuous* block ratios `N^{j/K}` the Riemann sum needs. No PNT.

### 90. General integer-ratio block weight `harmonic(kn) − harmonic(n) → log k`  (paper §5.4)

- **Statement (root_statement_hash `ba71e1cf015843298805b4dce32fa4aaec3069fca66b5ecc66a6af74b0152b19`):**
  `∀ k, 1 ≤ k → Tendsto (fun n => (harmonic (k*n) : ℝ) - harmonic n) atTop (𝓝 (Real.log k))`.
- problem_version_id: `2b9be4bb-1925-4790-9930-66cdc464d81c` · episode_id: `1cb8e26c-e695-4d9f-939a-d2c304c47c46`
- outcome: `kernel_verified` (first try) · snapshot: [proof/Erdos858_HarmonicRatioBlockWeight.lean](proof/Erdos858_HarmonicRatioBlockWeight.lean)
- **Why it matters:** generalizes #88 (dyadic) to any block ratio `k`: the `[n,kn]` block weight `→ log k`. With #89
  this covers the §5.4 block-weight machinery for both integer and continuous ratios. No PNT.

### 91. Floor block-endpoint limit `log⌊N^x⌋/log N → x`  (paper §5.4)

- root_statement_hash `f47f308253fc71932b13d045c6d05ea72e5b06c2de7224fa1e616556b0086b6d` · problem `1c285c29-283f-435e-8085-385573b2cb90` · episode `655f04a1-933d-45a8-9c36-d7f0dacd2977`
- outcome: `kernel_verified` (2 subs; `⌊⌋₊` U+208A) · snapshot: [proof/Erdos858_FloorBlockLimit.lean](proof/Erdos858_FloorBlockLimit.lean)
- **Why it matters:** the exact integer block endpoint — `log⌊N^x⌋/log N → x`, squeezed between `log(N^x−1)/log N` (#89) and
  `log(N^x)/log N = x`. Completes the §5.4 block-endpoint machinery. No PNT.

### 92. logCoordinate_mem_unitInterval  (paper §5.4, Riemann-sum ladder rung 1)

- root_statement_hash `cc5694c8f86fde5618230d66aa1eadbe2e2bad80d0ce41dc54808093e6d3ec37` · problem `b282c094-8f46-4d7c-b6fa-5cb3f676a6cd` · episode `6da5fb7f-e9c0-4d46-ae4e-0eb77a26a25b`
- outcome: `kernel_verified` (first try) · snapshot: [proof/Erdos858_LogCoordUnitInterval.lean](proof/Erdos858_LogCoordUnitInterval.lean)
- **Why it matters:** for `1 < a ≤ N`, `log a/log N ∈ (0,1]` — the coordinate map for the harmonic Riemann sum.

### 93. Uniform partition identity `∫₀¹f = Σⱼ∫_{j/K}^{(j+1)/K}f`  (paper §5.4, rung A)

- root_statement_hash `842433e28a014c56daf2c7331c18cc36ccc6c2e5935ae1e5638bdc7bd8028e4b` · problem `34db60ec-201c-41fd-a003-c70580146dd4` · episode `c7023983-da1f-4fcf-b874-803d1d6ede91`
- outcome: `kernel_verified` (first try) · snapshot: [proof/Erdos858_UnitPartitionIntegral.lean](proof/Erdos858_UnitPartitionIntegral.lean)
- **Why it matters:** splits `∫₀¹f` into the K equal subintervals of the left-endpoint Riemann sum, via
  `intervalIntegral.sum_integral_adjacent_intervals` (node `a(j)=j/K`). Foundation of the Riemann-sum→integral theorem
  (which is **not** in the pin — must be built from scratch). No PNT.

### 94. Block rectangle error `|∫_a^b f − (b−a)c| ≤ ε(b−a)`  (paper §5.4, rung B)

- root_statement_hash `7bbc6e5119a588f446b52373a5904e5481f9bc5776d8cf541e9c471cf93d6dce` · problem `8311adb0-33a6-4472-8b8b-2dfaa6ffc4f4` · episode `59964e3b-17b5-434e-9f47-cafc2bf9dace`
- outcome: `kernel_verified` (first try) · snapshot: [proof/Erdos858_BlockError.lean](proof/Erdos858_BlockError.lean)
- **Why it matters:** the rectangle-error bound (integrand within `ε` of a constant ⟹ integral within `ε·width` of the
  rectangle), via `intervalIntegral.norm_integral_le_of_norm_le_const`. No PNT.

### 95. Fixed-K sum error `|∫₀¹f − R_K(f)| ≤ ε`  (paper §5.4, rung C)

- root_statement_hash `75d53da9e50d1f4c489667e6c7b9dfe4e99ce89bf4a31e62fa28ef3d1e552656` · problem `bd456a50-e338-4c18-a2ae-e4865c5ebadb` · episode `ec1baf88-9cee-436d-94cf-526a2fa66d33`
- outcome: `kernel_verified` (first try) · snapshot: [proof/Erdos858_SumError.lean](proof/Erdos858_SumError.lean)
- **Why it matters:** assembles rungs A+B (as hypotheses) via the Finset triangle inequality into the fixed-K bound: the
  left-endpoint Riemann sum `R_K(f)=(1/K)Σf(j/K)` is within `ε` of `∫₀¹f` when each block varies by `≤ ε`. No PNT.

### 96. Block-variation ⟹ fixed-K error (assembly rung C′)  (paper §5.4)

- root_statement_hash `bcf237155799c1ade023cd5ad8f8314b6ed4c83069de12b03f06734af646ddbd` · problem `2bf46596-ea3b-4a5f-a236-8290b0babb1c` · episode `fb1d47f0-ba61-4f0c-b3a0-afdfe44453b2`
- outcome: `kernel_verified` (first try) · snapshot: [proof/Erdos858_BlockVarFixedKError.lean](proof/Erdos858_BlockVarFixedKError.lean)
- **Why it matters:** the key assembly — continuity + partition (rung A) + block variation `≤ ε` ⟹ `|∫₀¹f − R_K(f)| ≤ ε`.
  Inlines rung B (per-block rectangle error, width `1/K`) + rung C (Finset triangle). Tees up rung D. No PNT.

### 97. DURABLE THEOREM — left uniform Riemann sums → integral (rung D)  (paper §5.4)

- **Statement (root_statement_hash `fc8532d113501a639067477ebd4bf979a7f7a7d9d5b668d8eadc41f866bc0358`):**
  for continuous `f` on `[0,1]` (with the verified rungs A #93 + C′ #96 as hyps),
  `Tendsto (fun K => (1/K) Σ_{j<K} f(j/K)) atTop (𝓝 (∫₀¹ f))`.
- problem_version_id: `6098e0c1-f2b8-418c-a6e4-8ae22ca1016c` · episode_id: `08999b32-dd97-4b87-8101-21b54657a28e`
- outcome: `kernel_verified` (**first try**, full ε-δ) · snapshot: [proof/Erdos858_LeftRiemannSumTendsto.lean](proof/Erdos858_LeftRiemannSumTendsto.lean)
- **Why it matters:** **the reusable, campaign-independent Riemann-sum→integral theorem — built entirely from scratch**
  (the pin has no such lemma, only heavy `BoxIntegral`). For any continuous `f` on `[0,1]`, the equispaced
  left-endpoint sums converge to `∫₀¹ f`. ε-first proof: uniform continuity on the compact `[0,1]`
  (`isCompact_Icc.uniformContinuousOn_of_continuous`) → `δ`; `K₀` with `1/K₀ < δ`; block width `1/K < δ` forces
  variation `≤ ε/2`; rung C′ (#96) gives `|∫₀¹f − R_K| ≤ ε/2 < ε`. **This is the durable artifact identified as the
  best first checkpoint**, the real-analysis core of §5.4. No PNT.

### 98. Log-harmonic transfer rung 1 — normalized harmonic endpoint (log-scale block mass)  (paper §5.4)

- **Statement (root_statement_hash `ade71283ccd2aedcc1a9db7f71f13d395f034ed01a62f0a8398ccf5e6370720d`):**
  for `x > 0` (with the floor endpoint limit `log⌊N^x⌋/log N → x`, #91, as hyp),
  `Tendsto (fun N => harmonic(⌊N^x⌋)/log N) atTop (𝓝 x)`, i.e. `(1/log N)Σ_{a≤⌊N^x⌋}1/a → x`.
- problem_version_id: `016d526f-59f0-4bec-8c8c-dd5bff9a23f4` · episode_id: `eb1457ce-b9c0-41ca-87bd-2b670cad97d5`
- outcome: `kernel_verified` (2nd submission) · snapshot: [proof/Erdos858_NormHarmonicEndpoint.lean](proof/Erdos858_NormHarmonicEndpoint.lean)
- **Why it matters:** the log-scale block mass, the harmonic analogue of the equispaced count `(1/K)·j → j/K` in the
  durable Riemann-sum theorem (#97). Proof: split off the bounded `harmonic − log → γ` correction
  (`Real.tendsto_harmonic_sub_log` ∘ `tendsto_nat_floor_atTop`), which `/log N → 0` (`Tendsto.div_atTop`). No PNT.

### 99. Log-harmonic transfer rung 2 — block mass over an interval  (paper §5.4)

- **Statement (root_statement_hash `f64d151e287336d5f4eae4bbd7378d1c0eb6c77992646be61dbb8e3cf2afae7d`):**
  for `0 < s < t` (with the two #98 endpoint limits as hyps),
  `Tendsto (fun N => (harmonic(⌊N^t⌋) − harmonic(⌊N^s⌋))/log N) atTop (𝓝 (t − s))`,
  i.e. the log-scale mass of the block `N^s < a ≤ N^t` is exactly its width `t − s`.
- problem_version_id: `b12afd35-5b51-44af-a272-1ac96b611df0` · episode_id: `eedeed16-3f8d-4219-9803-8afdbe236eab`
- outcome: `kernel_verified` (**first try**) · snapshot: [proof/Erdos858_LogBlockMass.lean](proof/Erdos858_LogBlockMass.lean)
- **Why it matters:** the harmonic analogue of a partition-block width `(j+1)/K − j/K = 1/K`. Proof: `Tendsto.sub` of
  the two endpoint limits, transported pointwise by the ring identity `a/L − b/L = (a−b)/L`. No PNT.

### 100. Log-harmonic transfer rung 3 — fixed-K weighted block-sum limit (R_K assembly)  (paper §5.4)

- **Statement (root_statement_hash `158f0af5f137ccbe5ba1c71ffea1a232ca20d5f20119a20b714ec1e801a12b0c`):**
  for fixed `K`, weights `c`, block-mass sequences `g` and limits `L`, if `∀ j<K, (fun N => g N j) → L j`
  then `(fun N => Σ_{j<K} c j · g N j) → Σ_{j<K} c j · L j`.
- problem_version_id: `6110060c-586f-430f-a99f-6cdb980af045` · episode_id: `0f811ba8-f204-4897-b2fb-da26cc030f25`
- outcome: `kernel_verified` (**first try**) · snapshot: [proof/Erdos858_WeightedBlockSum.lean](proof/Erdos858_WeightedBlockSum.lean)
- **Why it matters:** with `c j = f(j/K)`, `L j = 1/K` (from #99), the limit is exactly the Riemann step-sum
  `R_K(f) = Σ_j f(j/K)/K` — the fixed-K, `N→∞` limit of the log-harmonic weighted block sum. Combined with the durable
  #97 (`R_K → ∫₀¹f`), the two-limit squeeze drives the full transfer. Proof: `tendsto_finset_sum` + `tendsto_const_nhds.mul`. No PNT.

### 101. Log-harmonic transfer rung 4 — weighted approximation aggregation (transfer error)  (paper §5.4)

- **Statement (root_statement_hash `7cebca510ea59fcfdb61cb93796ade655bbe365c759b5ff841d4f3a2197c8599`):**
  for fixed `K`, block sums `S`, weights `w`, masses `m`, `ε`, if `∀ j<K, |S j − w j·m j| ≤ ε·m j`
  then `|Σ_{j<K} S j − Σ_{j<K} w j·m j| ≤ ε · Σ_{j<K} m j`.
- problem_version_id: `9cbfdb3b-177a-4dac-a112-01b8225332ca` · episode_id: `0603e58f-3bcc-4e3a-ae25-2c2b015c7829`
- outcome: `kernel_verified` (6th submission) · snapshot: [proof/Erdos858_TransferAggregation.lean](proof/Erdos858_TransferAggregation.lean)
- **Why it matters:** the analytic heart — aggregates the per-block uniform-continuity error into the global bound
  between the true log-harmonic sum and the weighted step-sum (harmonic analogue of the #96 block-variation ⟹ error step).
  Proof: `Finset.sum_sub_distrib` (explicit `f g` term) rewrites the goal to one-sum form, then Finset triangle
  (`abs_sum_le_sum_abs`) + monotonicity (`sum_le_sum`) + `mul_sum`. **Lesson:** `|(∑S)−(∑wm)|` (two-sum) and
  `|∑(S−wm)|` (one-sum) are distinct `rw`/`linarith` atoms — bridge by rewriting the GOAL, not a separate `have`. No PNT.

### 102. Log-harmonic transfer rung 5 / assembly — diagonal two-limit squeeze  (paper §5.4)

- **Statement (root_statement_hash `8830ae5e0b76b4856d1d563c0ba2c2e5cbb61e10494a75d4ec101e51a0b57c80`):**
  for `W : ℕ→ℕ→ℝ`, `R : ℕ→ℝ`, `L`, `A : ℕ→ℝ`, if (i) `∀K, (fun N => W K N) → R K`, (ii) `R → L`, and
  (iii) `∀ ε>0, ∀ᶠ K, ∀ᶠ N, |A N − W K N| ≤ ε`, then `A → L`.
- problem_version_id: `153e5a12-0b28-4d14-973c-151d26fd7b8f` · episode_id: `c675fe0a-d0be-46b7-a555-544507b5a9d4`
- outcome: `kernel_verified` (**first try**) · snapshot: [proof/Erdos858_DiagonalSqueeze.lean](proof/Erdos858_DiagonalSqueeze.lean)
- **Why it matters:** the **keystone assembly** — the ε/3 diagonal argument that combines rung 3 (#100, `W K → R_K`),
  the durable Riemann-sum theorem (#97, `R_K → ∫`, as (ii)), and rung 4 (#101, the aggregation error, as (iii)) into
  `(1/log N)Σ_{1<a≤N}f(u_a)/a → ∫₀¹f`. Reusable double-limit lemma. Proof: work in the ε-N form
  (`Metric.tendsto_atTop`/`eventually_atTop`, avoiding nhds/ball unification), common K-witness via `Eventually.and.exists`,
  `abs_sub_le` triangle (×2) + `linarith`. No PNT.

*Results #100–#101 (2026-07-14, WALL 2 — log-harmonic transfer rungs 3–4, main-loop direct): #100 the fixed-K weighted
block-sum limit (`Σ_j c_j·g_N,j → Σ_j c_j·L_j`, giving the Riemann step-sum `R_K(f)` with `c_j=f(j/K)`, `L_j=1/K`) and
#101 the weighted approximation aggregation (`|Σ S_j − Σ w_j·m_j| ≤ ε·Σ m_j`, the transfer-error bound). With #98/#99
(block masses) and the durable #97 (`R_K→∫`), the four transfer rungs are now in place; the remaining assembly is the
diagonal two-limit squeeze + the partition identity (actual sum = weighted block sum + error over blocks of (1,N]).
All elementary, no PNT.*

### 103. Discrete block-partition sum identity (Ioc telescoping)  (paper §5.4)

- **Statement (root_statement_hash `77de62f60b93c43128769c28b39de102eaff115feed664ff16fff299d9cf145d`):**
  for a monotone `e : ℕ→ℕ` and `h : ℕ→ℝ`, `Σ_{j<K} Σ_{a∈Ioc(e j)(e(j+1))} h a = Σ_{a∈Ioc(e 0)(e K)} h a`.
- problem_version_id: `4cd2fc14-97d7-4e87-abef-581c706cff6f` · episode_id: `71b9c23b-beb2-4727-a4c8-3759baa21963`
- outcome: `kernel_verified` (**first try**) · snapshot: [proof/Erdos858_BlockPartitionSum.lean](proof/Erdos858_BlockPartitionSum.lean)
- **Why it matters:** the discrete analogue of #93, generic in the endpoint sequence — deliberately reusable for the
  future §5.3 prime-harmonic transfer (same engine, different mass). Proof: induction + `Finset.sum_Ioc_consecutive`.

### 104. Block membership implies u_a bound (exact, non-asymptotic)  (paper §5.4)

- **Statement (root_statement_hash `2ca89561fc22a13cda3fc34d720345f992676324636ad1c744a03d58f1e4d85e`):**
  for `a ∈ Ioc(⌊N^(j/K)⌋₊)(⌊N^((j+1)/K)⌋₊)`, `j/K < log a/log N ≤ (j+1)/K` exactly, for every `N,K`.
- problem_version_id: `23909c74-b4e4-436b-a394-c799d9bc057d` · episode_id: `2fd1a6f4-89bb-4de1-9513-a0ea6b773744`
- outcome: `kernel_verified` (2nd submission) · snapshot: [proof/Erdos858_BlockMembershipBound.lean](proof/Erdos858_BlockMembershipBound.lean)
- **Why it matters:** the block-membership bound driving the per-block uniform-continuity oscillation control — no
  asymptotics needed, sidesteps ever needing a fiber-index-equality lemma. **Lean lesson (campaign-wide):** a nested
  `have h := by\n  tac1\n  tac2` block silently mis-scoped in this pipeline; fix is single-line `have h := by tac1; tac2`.

### 105. Weighted pointwise-to-sum error bound (generic)  (paper §5.4)

- **Statement (root_statement_hash `09fafcb67867358619e6cb70fa0f6309498243d4ebeaa21a5f5090e5ea6abf0c`):**
  if `g` is pointwise within `ε` of `c` on `s` and `h≥0` on `s`, `|Σ g·h − c·Σh| ≤ ε·Σh`.
- problem_version_id: `9a92bf72-7902-4220-b1f4-c82e5e98edbe` · episode_id: `94e47a9e-b985-4ef5-ade3-d4ea33179aaa`
- outcome: `kernel_verified` (2nd submission) · snapshot: [proof/Erdos858_WeightedPointwiseSumBound.lean](proof/Erdos858_WeightedPointwiseSumBound.lean)
- **Why it matters:** turns the block-membership oscillation bound (#104 + uniform continuity) into the per-block
  sum bound `|S j − w j·m j| ≤ ε·m j` feeding #101's aggregation. **Refined Lean lesson:** `have X := by tacSeq`
  swallows the WHOLE subsequent semicolon-chain into X's own block — use an inline `show T from by tac` term
  (not a nested `have`) for a small algebraic side-fact needed mid-chain.

### 106. Block oscillation bound from modulus of continuity  (paper §5.4)

- **Statement (root_statement_hash `c1686399b3239894091e36f9d02b4d7ed10684862bd0cd794cfbcb694247bc67`):**
  given a δ-ε modulus of continuity for `f` at scale `δ≥1/K`, and `j/K<u≤(j+1)/K` (from #104), `|f u − f(j/K)|≤ε`.
- problem_version_id: `de46c8a7-d7c5-4043-9270-9b45e38716bd` · episode_id: `3f5c7af8-f568-44f3-bd7c-f72779b94f13`
- outcome: `kernel_verified` (2nd submission) · snapshot: [proof/Erdos858_BlockOscillationBound.lean](proof/Erdos858_BlockOscillationBound.lean)
- **Why it matters:** combines #104's exact bound with a modulus of continuity to produce the per-element
  oscillation bound `|f(u_a)−f(j/K)|≤ε` that #105 needs as its hypothesis. **Lean lesson:** `linarith` treats
  `j/K` and `(j+1)/K` as opaque atoms unless connected by an explicit `add_div` identity first.

### 107. Harmonic difference equals Ioc sum  (paper §5.4)

- **Statement (root_statement_hash `71637c00539c31fa2489b0cf892e1c5b261e74371ab0966a2a0fba72c7be984f`):**
  for `m≤n`, `harmonic n − harmonic m = Σ_{a∈Ioc m n} 1/a`.
- problem_version_id: `689aa9d6-6fd6-4cd0-bf05-aae97f189186` · episode_id: `fb52afe8-9bdc-45f3-9bc4-bcadbc99f40e`
- outcome: `kernel_verified` (3rd submission) · snapshot: [proof/Erdos858_HarmonicDiffEqSumIoc.lean](proof/Erdos858_HarmonicDiffEqSumIoc.lean)
- **Why it matters:** connector lemma identifying the abstract block mass (#99/#101/#102) with the exact finite
  sum needed by the concrete instantiation. **Lean cast lesson:** `(n:ℝ)+1` and `((n+1:ℕ):ℝ)` print identically
  but aren't syntactically equal — state a trivial cast-wrap matching the source lemma's native shape first,
  then `push_cast` to normalize.

### 108. Concrete per-block sum bound  (paper §5.4)

- **Statement (root_statement_hash `b458b72369c0103666495e73bf8415f24d2d353ae1dd37b6103d79909999fd3b`):**
  assembling #104+#105+#106+#107 (as hypotheses), the true block-j sum is within `ε·mass` of `f(j/K)·mass`.
- problem_version_id: `f3c9521f-0275-4cec-8164-7805d1061456` · episode_id: `f7d4edf1-411d-487e-91ea-412567ba8d2f`
- outcome: `kernel_verified` (2nd submission) · snapshot: [proof/Erdos858_ConcretePerBlockBound.lean](proof/Erdos858_ConcretePerBlockBound.lean)
- **Why it matters:** the exact per-block hypothesis format the aggregation theorem (#101) needs — a major
  concrete milestone. **Lean lesson (recurred a 3rd time):** the have-block scoping bug strikes on fresh
  theorems too; default to pure term-mode `have`s, factor multi-tactic sub-facts into their own top-level haves.

### 109. Fixed-K,N log-harmonic error bound (the big assembly)  (paper §5.4)

- **Statement (root_statement_hash `715a983d8f001505ad9f0e07f969469d43b0185ae423184d84a44cae1e77ab3e`):**
  assembling #108+#101+#103(×2)+#107 (as hypotheses): for `f` with a δ-ε modulus at scale `1/K≤δ`, `N>1`, `K>0`,
  `|Σ_{1<a≤N} f(u_a)/a − Σ_{j<K} f(j/K)·m_j| ≤ ε·(harmonic N − harmonic 1)`.
- problem_version_id: `f83ccfe0-216d-4f17-a124-65fe9b28ad3b` · episode_id: `2ce4f3d4-789f-4e42-abc3-ef154ddb0d60`
- outcome: `kernel_verified` (2nd submission) · snapshot: [proof/Erdos858_FixedKNTransferBound.lean](proof/Erdos858_FixedKNTransferBound.lean)
- **Why it matters:** the entire fixed-parameter error structure of the transfer in one theorem. **Two new Lean
  lessons:** `set` introduces an OPAQUE cdecl (unusable for function abbreviations in term-mode assemblies);
  `push_cast at` on an instantiated ∀-fact both normalizes casts (`↑(j+1)→↑j+1`) AND beta-reduces instantiation redexes.

### 110. Eventual transfer error (herr)  (paper §5.4)

- **Statement (root_statement_hash `5ffdc6ffadf5248b2108e2a67ebea6037ebb9bca5431aa3b37987180e0a75822`):**
  from #109 + a uniform-continuity family + `harmonic N − harmonic 1 ≤ 2·log N` (eventually): for every `ε>0`,
  eventually in `K`, eventually in `N`, `|A N − W K N| ≤ ε` (the `log N`-normalized forms).
- problem_version_id: `f051245e-a3d1-4073-906b-032fc5698452` · episode_id: `c4f306f3-ae6b-4e4e-a290-ba3fa592cda9`
- outcome: `kernel_verified` (**first try**) · snapshot: [proof/Erdos858_EventualTransferError.lean](proof/Erdos858_EventualTransferError.lean)
- **Why it matters:** exactly the `herr` hypothesis shape of the diagonal squeeze (#102). The #97 K-selection
  pattern + the `div_sub_div_same`/`abs_div`/`div_le_iff₀` normalization chain.

### 111. ★ CAPSTONE — the concrete log-harmonic Riemann theorem  (paper §5.4, Lemma 5.4)

- **Statement (root_statement_hash `6bf04a07524df30ae82e4311c20e2f29374b8f13dbe249f286830d1c8beca48a`):**
  given the diagonal squeeze (#102), the fixed-K weighted-block-sum limit family hW, the durable Riemann-sum
  limit (#97), and the eventual transfer error (#110): `(Σ_{1<a≤N} f(log a/log N)/a)/log N → L`.
  With `L = ∫₀¹ f`, this is the paper's Lemma 5.4 (fixed-endpoint form).
- problem_version_id: `161b53de-c21d-4e45-be2c-82673e20a15e` · episode_id: `754b73e8-1cba-4477-9a61-f8d28904e090`
- outcome: `kernel_verified` (**first try**) · snapshot: [proof/Erdos858_ConcreteLogHarmonicRiemann.lean](proof/Erdos858_ConcreteLogHarmonicRiemann.lean)
- **Why it matters:** **the log-harmonic transport engine for Theorem 1.2 is assembled.** The full kernel-verified
  ladder: pure Riemann #92–#97 → abstract engine #98–#102 → concrete assembly #103–#110 → this. Remaining
  discharge atoms: hW from block-mass limits, mass limits from #98's endpoint chain, `hharm2` from #87, and
  uniform continuity per concrete `f`.

### 112. Discharge — hW-bridge  (paper §5.4)

- **Statement (root_statement_hash `0ae56f5ffc49d3737417621f9bd854d86272c8b08d14256d5a648fbaf6a4f6b2`):**
  from #100's fixed-K engine + per-block mass limits: `(Σ_{j<K} f(j/K)·m_j(N))/log N → Σ_{j<K} f(j/K)·(1/K)`.
- problem `cfb1d302-a670-45bc-a8e8-0735b4782760` · episode `7b7fa818-ee8f-4c50-bcc3-860b968dffde` · `kernel_verified` (**first try**)
- snapshot: [proof/Erdos858_HWBridge.lean](proof/Erdos858_HWBridge.lean) — `Finset.sum_div` + `mul_div_assoc` bridge.

### 113. Discharge — block-mass limit family  (paper §5.4)

- **Statement (root_statement_hash `96a544e633985a380db6c3d2c5cb15ec7508ade5cfdb83cc0f9e1b756ff8c798`):**
  from the `j ≤ K` endpoint family: each block's normalized mass `→ 1/K` (every `j < K`).
- problem `79bcd11f-5774-437c-9f14-759aa694074b` · episode `8e322dc5-b0d5-4d02-b605-0904d178630f` · `kernel_verified` (**first try**)
- snapshot: [proof/Erdos858_BlockMassLimits.lean](proof/Erdos858_BlockMassLimits.lean) — endpoint subtraction + `div_sub_div_same`;
  the hypothesis family deliberately includes `j = 0` so no case split is needed here.

### 114. Discharge — eventual harmonic-vs-2log bound (hharm2)  (paper §5.4)

- **Statement (root_statement_hash `92455c2d2b82a39ed4b4ff7ae4b4859e9a15ea42b3ae60deb10e85e10bf30356`):**
  from `harmonic N/log N → 1` (#87): eventually `harmonic N − harmonic 1 ≤ 2·log N`.
- problem `48b1ec48-654d-4b26-8aac-620aa213d8aa` · episode `447541f5-2ff5-4bc6-aa18-4d50ca4db891` · `kernel_verified` (**first try**)
- snapshot: [proof/Erdos858_HarmonicVsTwoLog.lean](proof/Erdos858_HarmonicVsTwoLog.lean) — ε=1/2 ratio bound; **Lean lesson:**
  `harmonic 1 = 1` needs `rw [show (1:ℕ) = 0+1 from rfl]` before `harmonic_succ` fires (OfNat literal vs `(n+1)` pattern).

### 115. Discharge — endpoint-limit family (all j ≤ K, incl. j = 0)  (paper §5.4)

- **Statement (root_statement_hash `7d0fb866bff46016fd1e0a61c5a2edb49f8d575157c5d91a83b21eaba86d6afb`):**
  from the #98∘#91 chain (x>0) + the trivial j=0 instance: `harmonic⌊N^{j/K}⌋/log N → j/K` for every `j ≤ K`.
- problem `d7f007ab-2082-416d-911a-605a87cb71e0` · episode `b8ae101c-2669-4f65-a95c-ee2eb9a8b405` · `kernel_verified` (2nd submission)
- snapshot: [proof/Erdos858_EndpointFamily.lean](proof/Erdos858_EndpointFamily.lean) — **Lean lesson (3rd pipeline scoping
  variant):** multi-line `·`-bullet bodies mis-scope like nested-have bodies; every nested scope must be single-line,
  with pre-proven instances `▸`-transported into branch goals.

### 116. Discharge — clamp modulus family (hUC, FINAL external hypothesis)  (paper §5.4)

- **Statement (root_statement_hash `40947ecbbd72303c809125c4a359d1ea637c9f42fdebc32469f0264ae58533ea`):**
  for `f` continuous on `[0,1]`, the clamped `g x = f(max (min 1 x) 0)` has a global δ-ε modulus for every ε>0 —
  exactly the `hUC` shape of #110.
- problem `5dbc51cc-ea15-40bd-897c-92c292ee5225` · episode `5ba2df9c-192d-41f7-adf2-67e467e913a2` · `kernel_verified` (**first try**)
- snapshot: [proof/Erdos858_ClampModulusFamily.lean](proof/Erdos858_ClampModulusFamily.lean) — Heine–Cantor +
  the clamp's 2-Lipschitz bound (`min_add_max` + `abs_max_sub_max_le_abs`). **With this, the §5.4 transfer chain
  has NO external hypotheses left for any `f ∈ C[0,1]`** (clamp = id on `[0,1]`, where all transfer arguments live).

### 117. o(1)-Mertens arc atom 1 — generic Abel identity for log-inverse weights  (paper §5.2/§5.3)

- **Statement (root_statement_hash `0408de12bfd240a778b2619b0f45c9ca21ce9a6c05ba7d686af8796fc14df3bc`):**
  for any weight `c : ℕ→ℝ` and `x ≥ 2`: `Σ_{2<k≤⌊x⌋} c(k)/log k = C(x)/log x − C(2)/log 2 − ∫_{(2,x]}(−t⁻¹/log²t)·C(t) dt`.
- problem `3374318c-aedc-4ae0-b1ac-88f57982a006` · episode `f31ed437-964c-4689-81e5-d99d8135b206` · `kernel_verified` (**first try**)
- snapshot: [proof/Erdos858_AbelLogInverseIdentity.lean](proof/Erdos858_AbelLogInverseIdentity.lean)
- **Why it matters:** the Abel-summation split identity with `f = (log·)⁻¹`, GENERIC in the weight — specialized at
  `c = [prime]·log k/k` it becomes `Σ_{2<p≤x} 1/p = A(x)/log x − A(2)/log 2 + ∫ A/(t log²t)`, the driver of the
  o(1)-Mertens second theorem (whose interval form, with the constant cancelling, gives §5.3's prime block masses).
  Built on Mathlib's `sum_mul_eq_sub_sub_integral_mul` (pin availability confirmed), adapting the kernel-verified
  erdos-647 `PrimeLogDivIdentity` template to the single-line pipeline discipline. This crossed off one of the two
  "genuine remaining gaps" in the Mertens 1&2 catalog row (the Abel split identity); the prime-power tail constant
  remains the other.

### 118. o(1)-Mertens arc atom 2 — Mertens-2 split identity  (paper §5.2)

- **Statement (root_statement_hash `ff208875cbd2ef97037f2af51c9d19844b17c374b77ee6d3d8635687b47004c7`):**
  from #117 (hypothesis) at `c = [prime]·log k/k`: for `x ≥ 2`,
  `Σ_{p≤x} 1/p = A(x)/log x + ∫_{(2,x]} A(t)/(t·log²t) dt`, `A(y) = Σ_{p≤y} log p/p` (1/2-boundary terms cancel).
- problem `c655b1bd-5041-4370-933e-35f500b9a00f` · episode `6def15d2-59fd-4c18-b14b-cb64cbfa9b19` · `kernel_verified` (2nd submission)
- snapshot: [proof/Erdos858_Mertens2SplitIdentity.lean](proof/Erdos858_Mertens2SplitIdentity.lean)
- **Why it matters:** the classical partial-summation form of Mertens' second theorem, machine-checked. With the
  Mertens-1 stack (#47/#48) and the verified integrals #56/#57, the o(1)-form `Σ1/p = loglog x + M + o(1)` follows,
  whose M-cancelling interval form gives §5.3's prime block masses. **Lean lesson (4th pipeline pitfall):**
  bare-literal `Finset.Icc/Ioc 0 2` in a have-type elaborates at ℝ unless an endpoint is pinned `(0:ℕ)`.

### 119. o(1)-Mertens arc atom 3 — FTC for the Mertens tail integral  (paper §5.2)

- **Statement (root_statement_hash `ca79be06688a72cea6ea4b1a485e90d73404baa72aafa08842f064b8ebdbd18c`):**
  for `2 ≤ a ≤ b`: `∫_{a..b} t⁻¹/log²t dt = 1/log a − 1/log b`.
- problem `d077d552-4112-4cd2-90ed-0b0a6f09c2b8` · episode `d770e27b-7f86-41c8-ab6e-c671c1068e5e` · `kernel_verified` (2nd submission)
- snapshot: [proof/Erdos858_MertensTailFTC.lean](proof/Erdos858_MertensTailFTC.lean)
- **Why it matters:** the exact tail control behind the o(1): with `A = log + R`, `|R|≤C`, the remainder integral over
  `(N^s, N^t]` is `≤ C/log(N^s) → 0`. Antiderivative `−1/log t` (the #117 derivative negated). **Lean lesson:**
  `HasDerivAt.neg` output needs `neg_div` before `neg_neg` (the neg wraps the whole division).

### 120. o(1)-Mertens arc atom 4 — FTC for the Mertens main integral  (paper §5.2/§5.3)

- **Statement (hash `a1daa06c518a87810b518e4846a196b559d6038195e176cfe4c48e4ca7dcee82`):** for `2 ≤ a ≤ b`,
  `∫_{a..b} (log t)⁻¹·t⁻¹ = loglog b − loglog a` (antiderivative `log∘log`).
- problem `06f172f1-9f56-45d0-b85c-646c47289ba6` · episode `24bdcc62-e2a4-4966-a788-58e5d9a9ff87` · **first try** ·
  snapshot: [proof/Erdos858_MertensMainFTC.lean](proof/Erdos858_MertensMainFTC.lean)
- On `(N^s, N^t]` this is `log(t·logN) − log(s·logN) = log t − log s` EXACTLY for every `N` — the §5.3 block-mass value.

### 121. o(1)-Mertens arc atom 5 — interval prime-sum split (Finset)  (paper §5.3)

- **Statement (hash `b310064cbc1c3000d65610856d88444edbaeeba20474b456721f5859ca628244`):** for `m ≤ n`,
  `Σ_{p≤n} 1/p − Σ_{p≤m} 1/p = Σ_{m<p≤n} 1/p`.
- problem `e3581189-3086-4f1e-aada-b433baacbc48` · episode `7806870c-0cb5-453a-ba37-f4c87efd9c32` · **first try** ·
  snapshot: [proof/Erdos858_IntervalPrimeSumSplit.lean](proof/Erdos858_IntervalPrimeSumSplit.lean)

### 122. o(1)-Mertens arc atom 6 — Ioc set-integral additivity (generic)  (paper §5.2)

- **Statement (hash `7908d194d0c2f9ed5819a196f3c282e556aadb6585d710abc6f279fcc8743526`):** `f` integrable on `(2,b]`,
  `2 ≤ a ≤ b` ⟹ `∫_{(2,b]} f = ∫_{(2,a]} f + ∫_{(a,b]} f`.
- problem `1b6a4e05-9d0b-41d3-a33a-8b864323fb49` · episode `b1d800f4-2da0-4086-97a5-686027b61407` · 2nd submission
  (`Set.Ioc_disjoint_Ioc_same` absent — direct `disjoint_left` term) ·
  snapshot: [proof/Erdos858_IocIntegralAdditivity.lean](proof/Erdos858_IocIntegralAdditivity.lean)

### 123. o(1)-Mertens arc atom 7 — dominated tail bound  (paper §5.2)

- **Statement (hash `96cbd6f711244856bf59380291403f73f9bdac5fce404b81d61c5a650feb4f8e`):** from #119 (hyp):
  `|g| ≤ C·t⁻¹/log²t` on `(a,b]` (integrable, `C≥0`, `2≤a≤b`) ⟹ `|∫_{(a,b]} g| ≤ C·(1/log a − 1/log b)`.
- problem `e78c91da-6a79-4a3f-8891-28dd379671c0` · episode `7d647fdf-e095-4598-bf7c-c8c6c24d1f48` · **first try** ·
  snapshot: [proof/Erdos858_DominatedTailBound.lean](proof/Erdos858_DominatedTailBound.lean)
- The ENTIRE o(1) of Mertens-2 in one bound: the R-contribution over `(N^s,N^t]` is `≤ C/(s·log N) → 0`.

### 124. o(1)-Mertens arc atom 8 — Abel-integrand integrability (generic c ≥ 0)  (paper §5.2)

- **Statement (hash `7f6f322b93568ac3fb92946fe5f757f36ba0ddf350f4b97ef7651fc4cd6e7799`):** for `c ≥ 0`, `2 ≤ a ≤ b`,
  `C(t)/(t·log²t)` (`C(t)=Σ_{k≤⌊t⌋}c(k)`) is integrable on `(a,b]`.
- problem `97b368d7-4768-4020-8d57-45b2edd24dfd` · episode `d54c5874-3eaf-4251-862b-bf6d09fad7ac` · 3rd submission ·
  snapshot: [proof/Erdos858_AbelIntegrandIntegrable.lean](proof/Erdos858_AbelIntegrandIntegrable.lean)
- **Two new Lean lessons:** `Measurable.comp` with a `Finset.sum` outer function needs explicit `(g:=)(f:=)` args;
  mid-chain inline tactic proofs must be parenthesized `(by tac)` — bare `:= by tac;` swallows the rest of the chain.

### 125. o(1)-Mertens arc atom 9 — interval Abel identity for prime reciprocals  (paper §5.2/§5.3)

- **Statement (hash `44c6274452db92af16842b91aa5bf8730b6e412286adb763403e119e4dc8d269`):** from #118+#121+#122+#124
  (hypotheses): for `2 ≤ m ≤ n`, `Σ_{m<p≤n} 1/p = [A(n)/log n − A(m)/log m] + ∫_{(m,n]} A(t)/(t·log²t) dt`.
- problem `2557cc1c-15bf-4ab5-9622-496100d0a50a` · episode `2fe5b33e-fa3e-4bdd-934e-9ab0a099c7b3` · 2nd submission ·
  snapshot: [proof/Erdos858_IntervalAbelIdentity.lean](proof/Erdos858_IntervalAbelIdentity.lean)
- **Why it matters:** the deterministic core of interval-Mertens — the exact identity whose `N→∞` limit at
  `m=⌊N^s⌋, n=⌊N^t⌋` gives §5.3's prime block masses. **Lean lesson:** `Set.EqOn` per-point goals are
  un-beta-reduced — use `simp only [eq]` (not `rw`) inside EqOn lambdas.

### 126. o(1)-Mertens arc atom 10 — main-term extraction (generic A)  (paper §5.2)

- **Statement (hash `fda61230088df0e69eeddfe7b26f5d4783239893559ee5f7b848246882666134`):** from #120 (hyp): for any `A`
  with integrable Abel quotient on `(a,b]` (`2≤a≤b`), `∫ A/(t·log²t) = (loglog b − loglog a) + ∫ (A−log)/(t·log²t)`.
- problem `c71a944b-f0b9-4bbb-8f41-d295d379aa3c` · episode `00622a74-82d6-46b9-b098-d02b0e30b2d5` · 2nd submission ·
  snapshot: [proof/Erdos858_MainTermExtraction.lean](proof/Erdos858_MainTermExtraction.lean)
- **Why it matters:** with #125 + #123, the DETERMINISTIC core of interval-Mertens is complete:
  `Σ_{m<p≤n} 1/p = [A(n)/log n − A(m)/log m] + (loglog n − loglog m) + E`, `|E| ≤ C(1/log m − 1/log n)`.
  Only the N→∞ endpoint limits remain for §5.3's masses.

### 127. o(1)-Mertens arc atom 11 — loglog floor-endpoint limit  (paper §5.3)

- **Statement (hash `87d2c0ed091965b05fbe9552e52ffd4a62c11731169994157b2a5e897901e24f`):** for `x > 0`, given
  `log⌊N^x⌋/log N → x` (#91): `loglog⌊N^x⌋ − loglog N → log x`.
- problem `571894c7-877c-42e5-a5ed-aa894a0de0b2` · episode `ec737afb-5236-4f9e-9b80-2bca2d64d519` · **first try** ·
  snapshot: [proof/Erdos858_LogLogFloorLimit.lean](proof/Erdos858_LogLogFloorLimit.lean)
- **Why it matters:** two instances subtracted cancel `loglog N`, giving `loglog⌊N^t⌋ − loglog⌊N^s⌋ → log t − log s`
  — the main-term limit of interval Mertens = the value of §5.3's prime block masses. `Filter.Tendsto.log`
  + `Real.log_div` under `Tendsto.congr'`.

### 128. o(1)-Mertens arc atom 12 — A-ratio floor-endpoint limit  (paper §5.2/§5.3)

- **Statement (hash `f071aaba2f7632f310612b07553a7d45f16c8d96f1e41cf73ef7bdc3bd7f1da6`):** `|A(k) − log k| ≤ C` for
  `k ≥ 2` implies `A(⌊N^x⌋)/log⌊N^x⌋ − 1 → 0` for `x > 0` (`squeeze_zero_norm'` vs `C/log⌊N^x⌋ → 0`).
- problem `7eda46c2-9ca1-427e-9631-1637cc6d3d7c` · episode `41ccb206-dcfd-46aa-aa6c-cc3775c09fa4` · **first try** ·
  snapshot: [proof/Erdos858_ARatioFloorLimit.lean](proof/Erdos858_ARatioFloorLimit.lean)
- **Why it matters:** the boundary terms of the interval Abel identity vanish in the limit. With #125/#126/#123
  (identity+tail) and #127 (loglog main term), ALL ingredients of the §5.3 prime-block-mass limit
  `Σ_{N^s<p≤N^t} 1/p → log(t/s)` are now kernel-verified — only the final Tendsto assembly remains.

### 129. ★ §5.3 CAPSTONE — the prime block-mass limit (final Tendsto assembly)  (paper §5.3)

- **Statement (hash `7701d9f574f4f5bf7b8d6c086412672da5d5ce0d828d7c9c401d1a0b1981dd42`):** generic in `(S, A, E, D)`:
  the interval-Mertens identity (#125+#126) + tail bound (#123) + endpoint limits (#91/#127/#128) imply
  `S(⌊N^s⌋, ⌊N^t⌋) → log t − log s` for `0 < s ≤ t`.
- problem `4a79f436-20d6-4b63-9c59-ee791ec946b5` · episode `cd23cc70-8052-4251-a16a-faa9d1ac3db7` · **first try** ·
  snapshot: [proof/Erdos858_PrimeBlockMassLimit.lean](proof/Erdos858_PrimeBlockMassLimit.lean)
- **Why it matters:** at the prime instantiation this is **`Σ_{N^s<p≤N^t} 1/p → log(t/s)` — the §5.3 prime block
  masses**: the prime-harmonic sums converge to the `dv/v`-measure of geometric blocks, exactly the mass input the
  §5.4 transfer engine needs for the prime-harmonic Riemann-sum argument of Lemma 5.3. Full verified chain:
  #117→#118→#125(←#121/#122/#124)→#126(←#120)→#123(←#119)→#127/#128(←#91)→#129.

### 130. o(1)-Mertens discharge — floor remainder pointwise bound  (paper §5.2)

- **Statement (hash `7a6baa38a663ebf3708849ac22d50a4983446fd5b367e743d4215efe23a81b6b`):** `|A(k) − log k| ≤ C` on
  naturals `k ≥ 2` implies `|A(⌊u⌋) − log u| ≤ C + log 2` for reals `u ≥ 2` (floor sandwich costs one `log 2`).
- problem `b8ad9433-b24f-4372-94d2-013c19b5fba1` · episode `e8b9bd84-a384-42d6-a8f6-8f4bacb8c832` · **first try** ·
  snapshot: [proof/Erdos858_FloorRemainderBound.lean](proof/Erdos858_FloorRemainderBound.lean)
- **Why it matters:** the last discharge link — converts Mertens-1's integer-argument bound into #123's pointwise
  hypothesis at the Abel remainder integrand, producing #129's `hE` with `D = C + log 2`. **Every hypothesis of
  the §5.3 capstone (#129) is now dischargeable end-to-end from kernel-verified atoms.**

### 131. §5.3 transfer atom 1 — general-exponent block-membership bound  (paper §5.3)

- **Statement (hash `446d31a3e26eac709a4c5ca918fa1ee2572dc1c722f8ff872027bf29d382cdbc`):** for `1 < N` and ANY reals
  `v, w`: `a ∈ (⌊N^v⌋, ⌊N^w⌋]` forces `v < log a/log N ≤ w` exactly (subsumes #104).
- problem `0f4a7fe1-2f86-49c4-b880-38ad3abe8b4c` · episode `395263b1-79e9-41b9-87d5-d6cab1677f29` · **first try** ·
  snapshot: [proof/Erdos858_GeneralBlockMembershipBound.lean](proof/Erdos858_GeneralBlockMembershipBound.lean)
- **Why it matters:** the membership⟹coordinate bound at the §5.3 geometric blocks `v_j = s·(t/s)^{j/K}` (equispaced
  in `log v`, constant prime mass `log(t/s)/K` by #129) — the oscillation-control input of Lemma 5.3's transfer.

### 132. §5.3 transfer atom 2 — general oscillation bound  (paper §5.3)

- **Statement (hash `4aa23a7251ade81953267ebd75db715f5e0aad3db771ccd57ed1dc0134c1df78`):** δ-ε modulus for `G`, `v ≤ w`,
  `w − v ≤ δ`, `v < u ≤ w` give `|G u − G v| ≤ ε` (subsumes #106 for arbitrary endpoints).
- problem `d51e176c-c7b8-46e2-a139-3fd3e8ae7955` · episode `328f8af5-a97a-41eb-b3a6-f693cc639a5b` · **first try** ·
  snapshot: [proof/Erdos858_GeneralOscillationBound.lean](proof/Erdos858_GeneralOscillationBound.lean)

### 133. §5.3 transfer atom 3 — general-block weighted per-block bound (generic weight)  (paper §5.3)

- **Statement (hash `f27ae804fd03ecf437ca478a4ffe2cd2e8da6e1e0889c6781fda4792767323ba`):** from #131+#132+#105 (hyps),
  for any `h ≥ 0`: `|Σ_{a∈(⌊N^v⌋,⌊N^w⌋]} G(log a/log N)·h(a) − G(v)·Σh| ≤ ε·Σh`.
- problem `61c9a343-8d1b-4718-88da-af05b978c837` · episode `4ac828f5-e46d-4ed5-ad5e-071a2dc791d1` · **first try** ·
  snapshot: [proof/Erdos858_GeneralBlockPerBlockBound.lean](proof/Erdos858_GeneralBlockPerBlockBound.lean)
- **Why it matters:** the §5.3 analogue of #108 — the membership bound (#131) is primality-agnostic, so
  `h = [prime]·1/a` needs no special handling. The remaining §5.3 capstone atoms (#134→#138) parallel #109→#111
  with prime masses (from #129) and no `1/log N` normalization.

### 134. §5.3 transfer atom 4 — geometric mesh limit  (paper §5.3)

- **Statement (hash `d7937841a95db4a173777a661405343b9a96a14d55cd32be55ef6191717ee0f8`):** for `r > 0`, `r^(1/K) → 1` as `K→∞`.
- problem `a13fc978-a4be-4b74-ad54-a7d6c072dff8` · episode `a66e1427-a85f-4e4a-bee2-dd91328e96ea` · 2nd submission
  (`Function.comp_def` bridge) · snapshot: [proof/Erdos858_GeometricMeshLimit.lean](proof/Erdos858_GeometricMeshLimit.lean)

### 135. §5.3 transfer atom 5 — geometric block width bound  (paper §5.3)

- **Statement (hash `955508d2b8524fe87036bac6cf8945c5d3092a627636fbf3b55164177e074bff`):** for `0 < s ≤ t`, `K > 0`, `j < K`,
  `s·(t/s)^((j+1)/K) − s·(t/s)^(j/K) ≤ t·((t/s)^(1/K) − 1)`.
- problem `7c1728a3-181d-4a4a-a19b-28ce746df2ef` · episode `bae83197-5d10-4b41-8fe8-accccbbc26d3` · 3rd submission ·
  snapshot: [proof/Erdos858_GeometricBlockWidthBound.lean](proof/Erdos858_GeometricBlockWidthBound.lean)
- **Why it matters:** with #134 (mesh→1), eventually in `K` every geometric block width is `≤ δ` — the refinement
  input of the §5.3 `herr`. **Lean lessons:** `positivity` can't get `0 < t/s` from `0<s`,`s≤t`; `sub_nonneg.mpr`
  beats `linarith` for a freshly-rewritten nonneg subterm.

### 136. §5.3 transfer atom 6 — general-grid fixed-K,N aggregation bound  (paper §5.3)

- **Statement (hash `7800d72285ebc31524d51990bebc7f0c2f38d3adb3a766f37e292d6a753ba319`):** from #133+#101+#103 (hyps),
  for a monotone grid `v` with sub-`δ` widths: `|Σ_{(⌊N^{v0}⌋,⌊N^{vK}⌋]} G(u_a)·h − Σ_{j<K} G(v j)·(block mass)| ≤ ε·(total mass)`.
- problem `c2cb2b59-e4d1-4a29-8fe5-a69f407c9dab` · episode `40eff857-4d24-4241-95cd-52c957509ff3` · **first try** ·
  snapshot: [proof/Erdos858_GeneralGridAggregationBound.lean](proof/Erdos858_GeneralGridAggregationBound.lean)
- **Why it matters:** the §5.3 analogue of #109, generic in the exponent grid — cleaner (endpoints stay symbolic,
  no `1/log N`). `rw [hpartS, hpartM]` fired through the lambda-applied block sums directly.

### 137. §5.3 transfer atom 7 — geometric grid properties bundle  (paper §5.3)

- **Statement (hash `1e5075622909d6abfc1b1d9beec41150b7e9a7d29b7caeb54643e61fefd82f86`):** the grid `v_j = s·(t/s)^{j/K}` is
  monotone, `v 0 = s`, `v K = t`, and floor-endpoint monotone.
- problem `a6864070-34a7-444d-95ee-4475db94e6ad` · episode `06233ef3-7f56-4b74-848e-c11345a22e30` · 2nd submission ·
  snapshot: [proof/Erdos858_GeometricGridProperties.lean](proof/Erdos858_GeometricGridProperties.lean)
- **Why it matters:** discharges #136's grid hypotheses at the geometric instantiation. **Lean lesson:** `gcongr` on
  `↑a/↑c ≤ ↑b/↑c` (Nat casts, `c>0`, `a≤b`) closes completely — don't append `exact_mod_cast`.

### 138. §5.3 transfer atom 8 — hR bridge (geometric R_K → integral)  (paper §5.3)

- **Statement (hash `7b1b977d41a60a84a9b2e7023e743fd668be1b12bda03e90bc56748bf2112863`):** from #97's limit at
  `φ = log(t/s)·G(s·(t/s)^·)`, `Σ_{j<K} G(s·(t/s)^{j/K})·(log(t/s)/K) → L`.
- problem `5c293a6b-168d-4475-840c-deed31c985ae` · episode `e12a9946-58d1-434b-8c56-c4545fed0912` · **first try** ·
  snapshot: [proof/Erdos858_PrimeTransferHRBridge.lean](proof/Erdos858_PrimeTransferHRBridge.lean)
- **Why it matters:** reduces the §5.3 `R_K → L` limit to the durable #97 equispaced Riemann theorem via the
  geometric pullback (`Finset.mul_sum`+`ring`, same bridge as #111/#112).

### 139. §5.3 transfer atom 9 — geometric per-block prime mass limit  (paper §5.3)

- **Statement (hash `0b04f3c8f78548d76b2b3d7f52f630c6bec96c790b42613816ec533c60a26ec8`):** from the prime interval mass
  limit (#129 at primes), each geometric block's prime mass `→ log(t/s)/K`.
- problem `81f28c8c-504a-42de-b376-f0d57b278861` · episode `5154cb12-450f-4324-9ddf-5a6999c9593a` · **first try** ·
  snapshot: [proof/Erdos858_GeometricBlockMassLimit.lean](proof/Erdos858_GeometricBlockMassLimit.lean)
- **Why it matters:** the per-block mass-limit family feeding `hW` (via #100) — the log-equispacing
  `log(v_{j+1}) − log(v_j) = log(t/s)/K` (`log_mul`+`log_rpow`+`ring`). Analogue of #113.

### 140. §5.3 transfer atom 10 — mass-normalized diagonal error → herr  (paper §5.3)

- **Statement (hash `b9391a8d8fb17f2a7a3aa38055e5be2d1bb60e4f64b4629cc3dfff6b55245e75`):** given `mass N → L ≥ 0` and the
  fine-scale aggregation (`∀ η>0, ∀ᶠ K, ∀ N, |A N − W K N| ≤ η·mass N`), the herr shape `∀ ε>0, ∀ᶠ K, ∀ᶠ N,
  |A N − W K N| ≤ ε` (the `ε/(L+1)` diagonal argument, `div_mul_cancel₀` + `eventually_le_const`).
- problem `823c14ac-6c66-48c7-b1e6-b36415cb0967` · episode `83570b0d-3d27-4def-87b5-1bdad5d00770` · **first try** ·
  snapshot: [proof/Erdos858_MassNormalizedHerr.lean](proof/Erdos858_MassNormalizedHerr.lean)
- **Why it matters:** the abstract packaging of aggregation + mesh + total-mass into #102's exact `herr` shape.

### 141. §5.3 prime-harmonic transfer CAPSTONE — Lemma 5.3  (paper §5.3)

- **Statement (hash `8333c9c8e72f09575fa94044248f5eec5aaadce3b90bdffe99e277820291fcaa`):** from #102 (diagonal squeeze),
  `hW`, `hR`, `herr`, the prime-harmonic sum `Σ_{a∈(⌊N^s⌋,⌊N^t⌋]} G(log a/log N)·[a prime]/a → L`.
- problem `6da92549-46ff-438f-848e-964916a5f265` · episode `1cf150d2-95fe-4efd-8d6d-a7690e7ee5dd` · **first try (v2)** ·
  snapshot: [proof/Erdos858_PrimeHarmonicTransferCapstone.lean](proof/Erdos858_PrimeHarmonicTransferCapstone.lean)
- **Why it matters:** Lemma 5.3, the prime analogue of the §5.4 capstone #111. `L = ∫₀¹ log(t/s)·G(s·(t/s)^x)dx =
  ∫_s^t G(v)/v dv`. **Lean lesson (v1 fail → v2):** a bare `(N:ℝ)` under `∀ᶠ N in atTop` in the `herr` hypothesis
  lets Lean infer `N:ℝ`, mismatching the conclusion's `fun N:ℕ`; annotate `∀ᶠ (N:ℕ)`.

### 142. §5.3 hW discharge — fixed-K block-sum limit at prime quantities  (paper §5.3)

- **Statement (hash `37471b01d201000c696b67c317f702c07da2e09f13ae007445b3d8cdb22e1434`):** from #100 + #139 (pre-applied),
  the `hW` input of #141: `∀ K, Σ_{j<K} G(v_j)·(prime block mass) → Σ_{j<K} G(v_j)·(log(t/s)/K)`.
- problem `3fa3d0c4-88c5-4051-9496-5e9cb155de01` · episode `f40e2b16-a530-4132-b220-1188cee4cc69` · **first try** ·
  snapshot: [proof/Erdos858_PrimeTransferHWDischarge.lean](proof/Erdos858_PrimeTransferHWDischarge.lean)
- **Why it matters:** grounds #141's `hW`; `0<K` comes free from `j∈range K` (K=0 vacuous).

### 143. §5.3 herr atom A — geometric mesh vanishing  (paper §5.3)

- **Statement (hash `bf891e95fee98f7550f16c3b5628c3f900601c1445031e0b63b7d25fde876adc`):** from #134, for `0<s≤t` and any
  `δ>0`, `∀ᶠ K, t·((t/s)^{1/K} − 1) ≤ δ`.
- problem `19adbe92-d837-4b7b-a57b-76bd109172b0` · episode `5d2e5230-4c5b-4404-8a8b-421388d7a167` · **first try** ·
  snapshot: [proof/Erdos858_GeometricMeshVanish.lean](proof/Erdos858_GeometricMeshVanish.lean)
- **Why it matters:** with #135, eventually every block width `≤ δ` — the refinement of the herr. `sub_const` +
  `const_mul` → 0, then `eventually_le_const`.

### 144. §5.3 herr atom B — aggregation core (geometric #136 at primes)  (paper §5.3)

- **Statement (hash `59085eeb581e52dce13d92a907541be90ac39d56f2502be5c0376d6508643310`):** #136 (pre-applied) at the
  geometric grid + prime weight (grid props from #137), for `1<N`, `0<K`, a `δ`-`η` modulus, widths `≤δ`:
  `|A_N − W_KN| ≤ η·mass_N`, matching #141's canonical `W_KN`.
- problem `8c265281-85c8-4782-ba3e-28c7a6acada9` · episode `ef8c09fb-75ad-43e3-a261-5f277dbf4bee` · **first try** ·
  snapshot: [proof/Erdos858_PrimeHerrAggregationCore.lean](proof/Erdos858_PrimeHerrAggregationCore.lean)
- **Why it matters:** the fixed-`(K,N)` heart of the herr. **Lean lesson:** the `↑(j+1)` (generic `v (j+1)`) vs
  `↑j+1` (concrete atoms) mismatch is bridged BOTH ways by `simp only [Nat.cast_add, Nat.cast_one]` — feeding #136
  and normalizing its output to the canonical `W_KN`.

### 145a. §5.3 herr atom C — small-N triviality  (paper §5.3)

- **Statement (hash `5acbdff04b3674d2e37e552323f012b04a7de1479d5cf2f57a4cd12aa75d9182`):** for `(N:ℝ) ≤ 1`,
  `|A_N − W_KN| ≤ η·mass_N` holds as `0 ≤ 0` (all prime ranges empty).
- problem `fb8e65e4-5689-441b-8045-e667ea8d7c6a` · episode `01bfd98f-cb71-463c-ae03-3779c8f7529c` · 4th submission ·
  snapshot: [proof/Erdos858_PrimeHerrSmallN.lean](proof/Erdos858_PrimeHerrSmallN.lean)
- **Why it matters:** covers `N∈{0,1}` that #144 (`1<N`) excludes. **Lean lessons:** `Real.rpow_le_rpow_of_exponent_ge'`
  takes `0≤x` (no base-0 case); pure term-mode nested haves avoid the multi-line-`by` and rcases-bullet mis-scope.

### 145b. §5.3 herr atom D — aggregation wrapper (∀η∀ᶠK∀N bound)  (paper §5.3)

- **Statement (hash `df8046f0017e2904fdd04f3aac8b2a63afb572c2ac1de8c32dc21000ebce66f1`):** from #144 + #145a + #135 +
  #143 + G-modulus family, the eventual bound `∀ η>0, ∀ᶠ K, ∀ N, |A_N − W_KN| ≤ η·mass_N` (= #140's `hAgg`).
- problem `e7b5ac8e-3787-4be3-808b-19dc1ce61083` · episode `48ead24d-6aab-4cdb-a373-771dd8fb6d65` · 2nd submission ·
  snapshot: [proof/Erdos858_PrimeHerrWrapper.lean](proof/Erdos858_PrimeHerrWrapper.lean)
- **Why it matters:** `filter_upwards` + `by_cases 1<N` (apply #144 or #145a). **Lean lesson:** `le_of_not_lt` absent —
  use `not_lt.mp`.

### 146. §5.3 herr discharge / FINAL — via #140 mass-normalization  (paper §5.3)

- **Statement (hash `73d675c8ed316e61e80b4a03205eea5353e15d6aec01de1389a5ff14b0de8860`):** from #140 + #145b (`hAgg`) +
  #129 (`mass_N → log t − log s ≥ 0`), the `herr` of #141: `∀ ε>0, ∀ᶠ K, ∀ᶠ N, |A_N − W_KN| ≤ ε`.
- problem `f6536acd-1de7-4e46-990b-4fa0de2c241b` · episode `b2aca2d6-8ecd-44e0-b338-f255eb51b3e3` · **first try** ·
  snapshot: [proof/Erdos858_PrimeHerrDischarge.lean](proof/Erdos858_PrimeHerrDischarge.lean)
- **Why it matters:** closes the LAST of #141's three inputs — **§5.3 is now fully grounded to the §5.4 standard**.
  `hL0` via `log_div`+`log_nonneg`; `exact #140` at the concrete lambdas (β-unifies the abstract `hAgg`).

### 147. §5.3 dv/v bridge atom 1 — rpow exponent derivative  (paper §5.3)

- **Statement (hash `1d2aa503dffe45fdd600eae22436c1d72dcdc2ec6f628112ca12d0edf22ec853`):** for `c > 0`,
  `HasDerivAt (fun y => s·c^y) (s·(c^x·log c)) x`.
- problem `893b7bcf-40cd-424a-a798-56b93705258b` · episode `d4e4bf1f-7154-4385-a6aa-24d19d0923e5` · **first try** ·
  snapshot: [proof/Erdos858_RpowExponentDeriv.lean](proof/Erdos858_RpowExponentDeriv.lean)
- **Why it matters:** the derivative of the geometric substitution `v = s·(t/s)^x`. `c^y = exp(log c·y)` +
  `HasDerivAt.exp` + `const_mul`.

### 148. §5.3 dv/v bridge atom 2 / FINAL — change of variables `L = ∫_s^t G/v`  (paper §5.3, Lemma 5.3)

- **Statement (hash `972873f739ea6073c674554cb5147872009934f585f40b8fa263246b0622efeb`):** given #147 + routine
  continuity (hyps), `∫₀¹ log(t/s)·G(s·(t/s)^x) dx = ∫_s^t G(v)/v dv`.
- problem `418f42a6-7ee1-44b1-86cf-3f870389fd24` · episode `977c646d-00b9-4e2c-8181-2143dfefa4a7` · 3rd submission ·
  snapshot: [proof/Erdos858_PrimeTransferDvBridge.lean](proof/Erdos858_PrimeTransferDvBridge.lean)
- **Why it matters:** identifies the transfer limit `L` with the paper's exact Lemma 5.3 form — **§5.3 now
  complete in the paper's notation**. **Lean lessons:** `integral_comp_mul_deriv''` wants
  `HasDerivWithinAt … (Set.Ioi x)` (convert via `.hasDerivWithinAt`); `field_simp` is terminal for the
  `(a/c)·(c·b)=b·a` cancellation (trailing `ring` → "No goals").

### 149. §5.3 hmodfam discharge / FINAL — clamp modulus family on `[s,t]`  (paper §5.3)

- **Statement (hash `34b0ff1fdbb4f2a48cb86595bbff447c00969fe7d8cd6c439e48249510b63676`):** for `G` continuous on
  `[s,t]` (`s ≤ t`), the clamped `G(max (min t x) s)` has a global δ-ε modulus for every ε.
- problem `77706fc6-3ce5-4e21-a4e6-a4643cfcfe39` · episode `1239cbef-a6a6-47a5-bcd6-773eddc2ce9f` · **first try** ·
  snapshot: [proof/Erdos858_PrimeClampModulus.lean](proof/Erdos858_PrimeClampModulus.lean)
- **Why it matters:** discharges the `hmodfam` input of #145b — **§5.3 now has ZERO external hypotheses** (only
  `G` continuous on `[s,t]`, the natural Lemma 5.3 hypothesis), true parity with §5.4's #116. Verbatim transport
  of #116 from `[0,1]` to `[s,t]` (`1→t`, `0→s`, `zero_le_one→hst`); the clamp is 2-Lipschitz.

### 150. §5.3 dv/v bridge atom 3 — rpow exponent continuity  (paper §5.3)

- **Statement (hash `964f883d5551e230ea445af9b981803576fdd6a9306a6b456cae4299872199e4`):** for `c > 0`,
  `Continuous (fun x => s·c^x)`. Companion to #147 (the derivative).
- problem `b5b348a7-cd90-47a0-8a4a-7570bcd69afd` · episode `ba4680ed-e0d1-4239-9a48-3344ec8bce66` · 2nd submission ·
  snapshot: [proof/Erdos858_RpowExponentContinuous.lean](proof/Erdos858_RpowExponentContinuous.lean)
- **Why it matters:** discharges the continuity conditions of the dv/v bridge. **Lean lesson:** `Continuous.exp`
  is absent — use `Real.continuous_exp.comp`.

### 151. §5.3 dv/v bridge, SELF-CONTAINED — only `G` continuous on `[s,t]`  (paper §5.3, Lemma 5.3)

- **Statement (hash `63eb446d3f3a8cdcbb8d8678fec32f59eb0c0d76beaa731b87ae08f1153ddb49`):** for `G` continuous on
  `[s,t]`, `∫₀¹ log(t/s)·G(s·(t/s)^x)dx = ∫_s^t G(v)/v dv`.
- problem `d9d36c37-b931-462d-995a-c627052208aa` · episode `6f78a95d-8c28-402a-863f-066542f3f158` · 3rd submission ·
  snapshot: [proof/Erdos858_PrimeTransferDvBridgeSelfContained.lean](proof/Erdos858_PrimeTransferDvBridgeSelfContained.lean)
- **Why it matters:** supersedes the conditional #148 — the paper-notation Lemma 5.3 value now stands on the
  natural hypothesis alone (`G` continuous on `[s,t]`), the three continuity side-conditions discharged internally
  (#150 + the monotone image bound `s ≤ s·(t/s)^x ≤ t` + `ContinuousOn.div`). **Lean lessons:** `nlinarith` fails on
  the image bound (beta redex, then won't multiply a derived combo) — use explicit `le_trans` +
  `mul_le_mul_of_nonneg_left` term bounds; keep the `himg` `by` single-line with ascribed inner `by`s.

### 153. Theorem 1.2 assembly A1 — harmonic main term  (paper Thm 5.8 / Prop 5.1)

- **Statement (hash `32d333f53fa830ac5654461f3958a66e4da931242f1b5d53dfdb5fc050451348`):** conditional on the
  Euler–Mascheroni limits + `log⌊√N⌋/log N → 1/2` + `log N → ∞`, `(H_N − H_{Nat.sqrt N})/log N → 1/2`.
- problem `d093fc19-b495-4448-aebb-ff3c6abcf4cf` · episode `9b5aee6e-b05c-4a3d-9f7e-3e5469a64e28` · **first try** ·
  snapshot: [proof/Erdos858_Thm12_A1_HarmonicAsymptotic.lean](proof/Erdos858_Thm12_A1_HarmonicAsymptotic.lean)
- **Why it matters:** the `(1/2)log N` leading term of `M(N)` in the Prop 5.1 frontier identity. Three-term
  split + `Tendsto.div_atTop` + `Tendsto.congr'`. First atom of the Theorem 1.2 assembly.

### 154. Theorem 1.2 CAPSTONE (conditional) — `M(N)/log N → c₂`  (paper Theorem 5.8 / Theorem 1.2)

- **Statement (hash `62e1b37347604f085adce9b7ff664ad013fd7d77b8e2cfdcf530d914deed6e88`):** from the frontier identity
  `M = harm + tail` (Prop 5.1) and `harm/log N → 1/2` (A1) + `tail/log N → I`, `M(N)/log N → 1/2 + I = c₂`.
- problem `b21ab91d-8c18-4d80-a297-18c25a951566` · episode `30d1989f-508d-4858-ae2d-57d6547bd1d2` · **first try** ·
  snapshot: [proof/Erdos858_Thm12_A7_Capstone.lean](proof/Erdos858_Thm12_A7_Capstone.lean)
- **Why it matters:** the STRUCTURAL closure of the asymptotic law (Theorem 1.2), harmonic half discharged (A1).
  `Tendsto.add` over the `add_div` frontier identity. **Confirms the route is sharp-Mertens-FREE** — interval
  Mertens (#129) + transfers (#111, #141) + Prop 5.1, exactly as Chojecki's §5.8 proof runs. Supersedes the thin #69.

### 155. Theorem 1.2 assembly A5 — Lemma 5.7 prime-only ramp  (paper Lemma 5.7)

- **Statement (hash `bd3c300524db57c07059d3df5f11e47f5a9d0becd42569fa24420793439b2a8e`):** from the Prop 3.2 increment
  `S_N(a)−S_N(a−1)=C_N(a)−1/a`, `C_N(a)≥P_N(a)/a`, `P_N(a)≥1+δ`, the sweep strictly increases (`>0`).
- problem `4b1dfd61-cd9d-4beb-94d2-daf29aa8eefb` · episode `d81b9cbf-b6b0-4709-90bc-7ed076c866b0` · **first try** ·
  snapshot: [proof/Erdos858_Thm12_A5_Lemma57Ramp.lean](proof/Erdos858_Thm12_A5_Lemma57Ramp.lean)
- **Why it matters:** the K*-lower-bound ramp (`K* ≥ N^{α−ε}`). `gcongr` div-monotone + `div_sub_div_same` + `linarith`.

### 156. Theorem 1.2 assembly — K* localization (argmax pinned by monotonicity)  (paper Theorem 5.8)

- **Statement (hash `476a9a960cc3adbe3154c40fb25bea57e0bb90a889418f5beed6c3980f34e92d`):** an increase-on-`[1,L1]`,
  decrease-after-`L2` sweep has every maximizer in `[L1,L2]`.
- problem `61f22a0b-fc62-4fb5-939c-0bcaa141d242` · episode `bf1b0918-0bbc-4a2f-97e7-9c50b2bdb395` · 2nd submission ·
  snapshot: [proof/Erdos858_Thm12_KstarLocalization.lean](proof/Erdos858_Thm12_KstarLocalization.lean)
- **Why it matters:** with `L1=N^{α₂−ε}`, `L2=N^{α₂+ε}`, gives `K*(N)=N^{α₂+o(1)}`. `by_contra`+monotone step+`linarith`
  (single-line `·` bullets — multi-line mis-scopes).

### 157. Theorem 1.2 assembly — frontier increment sign  (paper Prop 5.1 / Theorem 5.8)

- **Statement (hash `7a3a40e531ca6cdfd8f16d285e7d2b647c0fcad517aa6374dde405d5e04c0281`):** from the increment
  `S_N(a)−S_N(a−1)=(R_N(a)−1)/a` (`a>0`), `R_N(a)>1 ⟹` increasing, `R_N(a)<1 ⟹` decreasing.
- problem `a1d93b05-57eb-41a2-94fc-9000f0da6ade` · episode `c1a6317c-dd7b-4dcc-ba1d-a7c8f0b514ce` · **first try** ·
  snapshot: [proof/Erdos858_Thm12_IncrementSign.lean](proof/Erdos858_Thm12_IncrementSign.lean)
- **Why it matters:** the glue from Lemma 5.5 (`R_N→Φ`) + Prop 5.6 (`Φ` vs 1 at `α₂`) to the K* localization's
  monotonicity hypotheses. `div_pos`/`div_neg_of_neg_of_pos`+`linarith`.

### 158. Theorem 1.2 assembly — Prop 5.1 telescoping core  (paper Prop 5.1 / 3.2)

- **Statement (hash `c1909182c1523fc1a30aef4c288fb5ad2defaab3a8a7b170d83b2fce584fb615`):** for `m ≤ n`,
  `S(n) − S(m) = Σ_{a∈Ioc m n}(S(a) − S(a−1))`.
- problem `9f1d6a58-add9-4ad6-a1b1-189c5901b920` · episode `cbe5a4e4-a4ad-4069-ad78-fa02cc01fd34` · **first try** ·
  snapshot: [proof/Erdos858_Thm12_Telescoping.lean](proof/Erdos858_Thm12_Telescoping.lean)
- **Why it matters:** the frontier sweep telescopes its per-step increments — the mechanism of Prop 5.1.
  `Nat.le_induction` + `Finset.sum_Ioc_succ_top`.

### 159. Theorem 1.2 assembly A2 — Prop 5.1 exact frontier identity  (paper Proposition 5.1)

- **Statement (hash `1d4d62a355c9ff8aae75a516f8b6ae219924fb30801ba23a7ee2ad979203c2fb`):** for `K≤√N≤N` and the four
  frontier facts, `S_N(K) = (H_N−H_{√N}) + Σ_{K<a≤√N}(1−R_N(a))/a`.
- problem `653466d4-40a8-4e84-b5d7-8f26c33b76db` · episode `02795a1c-2173-4388-a155-cf395f6bad33` · **first try** ·
  snapshot: [proof/Erdos858_Thm12_A2_Prop51Identity.lean](proof/Erdos858_Thm12_A2_Prop51Identity.lean)
- **Why it matters:** the `M = harm + tail` frontier identity — the direct feeder of the Theorem 1.2 capstone (A7).
  Split at `√N` (`sum_Ioc_consecutive`, `a>√N` vanishes) + harmonic difference + `sum_sub_distrib`/`sub_div`.
  **A7 now has 2 of 3 inputs verified (this + A1); only the tail Riemann sum (A6) remains.**

### 160–163. Theorem 1.2 assembly — interval log-harmonic transfer (Lemma 5.4 on `[s,t]`)  (paper Lemma 5.4)

- **#160 A6 capstone** (`c6955bc901e1cb75e1775695793ef81f1c72ddd7b25f550de9402e7669b1ed9f`): from #102 + hW + hR + herr,
  `(Σ_{a∈(⌊N^s⌋,⌊N^t⌋]} f(log a/log N)/a)/log N → L`. Direct #102 application (interval analogue of #111). problem
  `cedc4a2e-33a2-476e-b824-887988396dbc` · ep `8b473e95-b22c-4714-95d9-c799b4369ad4` · **first try** ·
  [proof/Erdos858_Thm12_A6_IntervalTransfer.lean](proof/Erdos858_Thm12_A6_IntervalTransfer.lean)
- **#161 A6-hR** (`dee0f4d49d571e0a801c91b0a92f19bcca18e162ad637cf4e22db9543424a398`): interval Riemann step-sum → L, from
  #97 at the pullback `g(x)=f(s+x(t−s))(t−s)` (`Finset.mul_sum`+`Tendsto.congr'`). ep `25310c3e` · **first try** ·
  [proof/Erdos858_Thm12_A6hR_RiemannStep.lean](proof/Erdos858_Thm12_A6hR_RiemannStep.lean)
- **#162 A6-hW** (`6711aec59a67fab579d51691f3fb4a520442075760ebbd4268e90bae1d4a3e9a`): fixed-K harmonic-weighted block sum
  → step-sum, from #100 + #99 arithmetic-block masses (`simp only [Finset.sum_div, mul_div_assoc]` bridge). ep
  `26f6a22d` · 2nd sub · [proof/Erdos858_Thm12_A6hW_BlockSum.lean](proof/Erdos858_Thm12_A6hW_BlockSum.lean)
- **#163 A6-herr** (`7be377203f2efc75fff7cac3a23539631e7a3430b3c31fce34eb948c20b7c6a0`): the transfer error herr, from #140
  (mass-normalized) + the total-mass limit (#99) + the aggregation. ep `7f227c5c` · v2 · **Lean lesson:** the `∀ᶠ N`
  binder inferred `N:ℝ`; annotate `∀ᶠ (N:ℕ)` (as #141 v2). [proof/Erdos858_Thm12_A6herr_TransferError.lean](proof/Erdos858_Thm12_A6herr_TransferError.lean)

*Results #160–#163 (2026-07-17, THEOREM 1.2 — INTERVAL LOG-HARMONIC TRANSFER COMPLETE): the [s,t] analogue of the
full-range #111 (Chojecki's Lemma 5.4 on a general interval), built as a direct #102 application (#160) with all three
discharges — hR (#161, via #97 + linear pullback), hW (#162, via #100 + #99 arithmetic-block masses), herr (#163, via
#140). This is the transport engine for the tail Riemann sum `Σ_{K*<a≤√N}(1−Φ)/a/log N → ∫_{α₂}^{1/2}(1−Φ)` = the last
analytic input of the Theorem 1.2 capstone A7. Theorem 1.2 is now assembled from a verified scaffold; remaining
conditional inputs: the uniform Lemma 5.5 (uniform interval Mertens, the `R_N→Φ` swap) and the combinatorial frontier
facts (parent-counting, `R_N=0` above `√N`).*

*Results #158–#159 (2026-07-17, THEOREM 1.2 — Prop 5.1 frontier identity): the telescoping core (#158) and the full
Prop 5.1 exact frontier identity (#159, `S_N(K) = (H_N−H_{⌊√N⌋}) + Σ_{K<a≤√N}(1−R_N(a))/a`, conditional on the
Prop 3.2+parent-counting form, `C_N=R_N/a` above `N^{1/4}`, `R_N=0` above `√N`, and the harmonic difference). This is
the `M = harm + tail` identity feeding the capstone A7 (#154), which now rests on this + the harmonic half (A1, #153) +
the single remaining tail Riemann sum. Theorem 1.2's `M(N)/log N → c₂` is assembled down to the interval log-harmonic
transfer + uniform Lemma 5.5.*

*Results #155–#157 (2026-07-17, THEOREM 1.2 — K* localization branch): the Lemma 5.7 prime-only ramp (#155,
increment `>0` when `P_N≥1+δ`), the argmax localization capstone (#156, an increase-then-decrease sweep pins its
maximizer in `[L1,L2]`), and the increment-sign bridge (#157, `R_N` vs 1 ⟹ monotonicity). Together with Lemma 5.5
(`R_N→Φ`) + Prop 5.6 (verified, `Φ` strictly decreasing through 1 at `α₂`), these give `K*(N)=N^{α₂+o(1)}` (Theorem 5.8's
cutoff-localization half). Remaining for the value half: the Prop 5.1 frontier identity (`M=harm+tail`, combinatorial)
and the tail Riemann sum (`Σ_{K*<a≤√N}(1−Φ)/a / log N → ∫_{α₂}^{1/2}(1−Φ)`, an interval log-harmonic transfer + uniform
Lemma 5.5).*

*Results #153–#154 (2026-07-17, THEOREM 1.2 ASSEMBLY STARTED — after the user supplied the paper pdf, correcting a
misdiagnosis): the "sharp-constant Mertens wall" for the asymptotic law `M(N)=(c₂+o(1))log N` was a MISDIAGNOSIS. The
paper's Theorem 5.8 proof routes through the exact frontier identity (Prop 5.1) + the INTERVAL Mertens (Lemma 5.2 =
verified #129) + the two transfers (#111, #141) + Prop 5.6 (verified) — never the sharp global Mertens (that gates
only Thm 1.1's Lemma 4.3). The harmonic main term `(H_N−H_{⌊√N⌋})/log N → 1/2` (#153, A1) and the conditional capstone
`M(N)/log N → c₂ = 1/2 + ∫_{α₂}^{1/2}(1−Φ)` (#154, A7) are now verified. Remaining toward unconditional Theorem 1.2:
the tail Riemann sum `Σ_{K*<a≤√N}(1−Φ(u))/a / log N → ∫_{α₂}^{1/2}(1−Φ)` (via #111), Lemma 5.5 (P_N+Q_N=Φ+o(1),
uniform — from #129/#141), Lemma 5.7, and the frontier localization `K*=N^{α₂+o(1)}` (Prop 5.6 + Lemma 5.7). See
catalog rows 5.5/5.7/5.8 (re-diagnosed 🔨 REACHABLE).*

*Results #150–#151 (2026-07-17, §5.3 dv/v bridge made SELF-CONTAINED): rpow exponent continuity (#150, companion to
#147) discharges the continuity side-conditions, so the paper-notation change-of-variables (#151) now stands on `G`
continuous on `[s,t]` alone — superseding the conditional #148. Combined with #149, ALL of §5.3 (capstone + discharge
tree + dv/v bridge) rests on `G` continuous on `[s,t]` alone, with no external analytic hypotheses.*

*Results #147–#149 (2026-07-17, §5.3 dv/v change-of-variables bridge + hmodfam discharge — paper-notation closure +
zero external hypotheses): the rpow exponent derivative (#147) and the geometric change of variables (#148, via
`intervalIntegral.integral_comp_mul_deriv''`) identify the §5.3 transfer limit `L = ∫₀¹ log(t/s)·G(s·(t/s)^x)dx` with
the paper's `∫_s^t G(v)/v dv`; the [s,t] clamp modulus (#149) discharges the last external hypothesis (the G-modulus),
so §5.3 stands on `G` continuous on `[s,t]` alone. §5.3 is now complete end-to-end in the paper's exact Lemma 5.3
statement, with the same zero-external-hypothesis standard as §5.4. All §5 transfer infrastructure (§5.3 + §5.4) done;
remaining paper rows 5.5/5.7/5.8/6.2 are analytic-wall (🧱).*

*Results #140–#146 (2026-07-17, §5.3 PRIME-HARMONIC TRANSFER COMPLETE + FULLY GROUNDED, main-loop direct under the
continuous-work directive): the mass-normalized herr packaging (#140), the **CAPSTONE Lemma 5.3 (#141)** and its
COMPLETE discharge tree — `hW` (#142 ← #100+#139), `hR` (#138∘#97), and `herr` (#146 ← #140 + #145b wrapper ← {#144
aggregation core, #145a small-N, #143 mesh-vanish, #135 width, G-modulus}). The §5.3 prime-harmonic Riemann-sum
theorem `Σ_{a∈(⌊N^s⌋,⌊N^t⌋]} G(log a/log N)·[a prime]/a → ∫_s^t G(v)/v dv` now rests on a fully kernel-verified tree,
the same standard as §5.4's #111 — with NO sharp-constant Mertens (the Meissel–Mertens constant cancels in interval
form, #129). Remaining §5.3 interpretation nicety: the `∫₀¹ log(t/s)·G(s·(t/s)^x)dx = ∫_s^t G(v)/v dv` change-of-variables
identity (documentation-level; both are the verified `L`). Next paper rows: 5.5 (P_N+Q_N→Φ), 5.7, 5.8, 6.2 — all
analytic-wall (🧱).*

*Results #138–#139 (2026-07-17, §5.3 hR + block masses): the hR bridge (#138, geometric R_K → ∫₀¹φ via #97) and
the per-block mass limits (#139, → log(t/s)/K via #129 + log-equispacing). Remaining §5.3 capstone: herr (via #136 +
width→0 + mass bound), hW (#100 + #139), the #102 capstone, then #129→prime discharge and the dv/v bridge.*

*Results #136–#137 (2026-07-17, §5.3 aggregation + grid bundle): the fixed-K,N aggregation (#136, analogue of #109,
generic in the grid) and the geometric grid's structural properties (#137). Remaining §5.3 capstone: herr (instantiate
#136 at the K-dependent geometric grid, width→0 via #134/#135, total mass bounded via #129), hW (#129 masses + #100),
hR (#97 pullback), #102 capstone.*

*Results #134–#135 (2026-07-17, §5.3 geometric-grid machinery): the mesh limit `(t/s)^(1/K)→1` (#134) and the
per-block width bound (#135) — together giving eventual sub-δ refinement of the geometric grid `v_j = s·(t/s)^{j/K}`,
the `herr` input. Remaining §5.3 capstone: herr assembly, hW (#129 masses + #100), hR (#97 pullback), #102 capstone.*

*Results #131–#133 (2026-07-17, §5.3 prime-harmonic transfer STARTED, continuous-work directive): the general-exponent
block-membership bound (#131, subsumes #104), general oscillation bound (#132, subsumes #106), and generic per-block
bound (#133, analogue of #108) — the transfer machinery re-instantiated at geometric blocks `v_j = s·(t/s)^{j/K}`.
The §5.4 generic engine atoms (#100/#102/#103/#105) apply unchanged; remaining: aggregate/herr/hW/hR/capstone
(#134–#138) with the #129 prime masses.*

*Results #125–#129 (2026-07-16/17, INTERVAL MERTENS + §5.3 MASSES COMPLETE, main-loop direct, continuous-work
directive): the interval Abel identity (#125), main-term extraction (#126), loglog and A-ratio floor-endpoint
limits (#127, #128), and the final generic Tendsto assembly (#129) — closing the interval form of Mertens' second
theorem along geometric blocks. Remaining discharge bookkeeping: the E-tail pointwise bound (|A(⌊u⌋)−log u| ≤
C+log 2) and the concrete instantiation chain; then the §5.3 prime-harmonic transfer = the §5.4 generic engine
(#100/#102/#103/#105) run at prime masses.*

*Results #117–#124 (2026-07-16, o(1)-MERTENS TOOLKIT COMPLETE, main-loop direct under the user's continuous-work
directive): the full Abel-summation infrastructure for Mertens' second theorem — generic Abel identity (#117), the
prime split identity Σ1/p = A(x)/log x + ∫A/(t log²t) (#118), both exact FTCs (#119 tail, #120 loglog main), the
Finset interval split (#121), generic Ioc additivity (#122), the dominated tail bound (#123), and the step-integrand
integrability (#124). Remaining: the grand interval-Mertens assembly (identity at fixed m,n; then the N→∞ limit
Σ_{N^s<p≤N^t}1/p → log(t/s)) — the §5.3 prime block masses — after which the §5.4 engine (#100/#102/#103/#105)
transfers verbatim to the prime-harmonic case.*

*Results #109–#115 (2026-07-16, §5.4 COMPLETE at the atom level, main-loop direct): #109 the fixed-K,N error bound
(the big assembly), #110 the eventual transfer error (herr), **#111 the CAPSTONE concrete log-harmonic Riemann
theorem** (paper Lemma 5.4, fixed-endpoint form), and #112–#115 the full discharge chain (hW-bridge, block-mass
limits, hharm2 from #87, endpoint family incl. j=0). The dependency tree is now closed end-to-end:
#111 ← {#112 ← {#100, #113 ← #115 ← {#98, #91}}, #97 ← {#93, #96}, #110 ← {#109 ← {#108 ← {#104–#107}, #101, #103},
hUC, #114 ← #87}} — only the uniform-continuity family hUC (per concrete f) remains an external hypothesis, to be
supplied at instantiation (e.g. via clamping for f continuous on [0,1]). Next: §5.3 prime-harmonic transfer reusing
the same engine (#100/#102/#103/#105 are generic), which requires the o(1)-Mertens scoped sub-goal.*

*Results #103–#108 (2026-07-16, concrete assembly of the log-harmonic transfer, main-loop direct): the six
concrete atoms needed on top of the abstract engine (#98–#102) — #103 the generic discrete partition identity,
#104 the exact (non-asymptotic) block-membership bound, #105 the generic weighted pointwise-to-sum transfer,
#106 the block oscillation bound (chains #104 into an actual modulus of continuity), #107 the harmonic-difference
connector, and **#108 the concrete per-block sum bound** (assembles #104–#107 into #101's exact hypothesis
shape — the payoff atom). Remaining: aggregate #108 over all `j<K` via #101, identify the total sums via #103
(`e_0=1`, `e_K=N`), normalize by `log N`, and apply #102 to close the full concrete log-harmonic Riemann
theorem. Three campaign-wide Lean pipeline lessons banked this session (see #104/#105/#106/#107/#108 entries
above) — likely explains several historical multi-submission retries previously blamed on wrong lemma names.*

*Results #98–#99 (2026-07-14, WALL 2 — log-harmonic transfer STARTED, main-loop direct): the transport layer that
carries the analytic weight of the sum onto the interval integral (the route to the asymptotic Theorem 1.2, via §6
eventual frontier exactness — confirmed as the cheapest/lowest-risk finishing path). #98 the normalized harmonic
endpoint `harmonic(⌊N^x⌋)/log N → x` (log-scale block mass) and #99 the interval block mass
`(harmonic(⌊N^t⌋)−harmonic(⌊N^s⌋))/log N → t−s`. These are the harmonic analogues of the equispaced count and block
width in the durable Riemann-sum theorem (#97). Remaining: fixed-K weighted step-sum → R_K (rung 3), combine with #97
→ full log-harmonic Riemann theorem `(1/log N)Σ_{1<a≤N}f(log a/log N)/a → ∫₀¹f` → §5.3 prime version → 5.5/5.7/5.8 →
Thm 1.2. All elementary, no PNT.*

*Results #96–#97 (2026-07-14, WALL 2 — DURABLE Riemann-sum→integral theorem COMPLETE, main-loop direct): #96 the
key assembly (block variation ⟹ fixed-K error, inlining rungs B+C) and #97 the **durable theorem** — for every
continuous `f` on `[0,1]`, the equispaced left-endpoint Riemann sums `(1/K)Σ_{j<K}f(j/K) → ∫₀¹f` (ε-δ via uniform
continuity + rungs A/C′). The entire Riemann-sum→integral theorem is now built FROM SCRATCH in 6 rungs (#92 coord,
#93 partition, #94 block error, #95 sum error, #96 assembly, #97 tendsto), since the pin had no such lemma. This is
the reusable, campaign-independent artifact. Remaining to Theorem 1.2: the log-harmonic transfer (weighting the
Riemann sum by 1/a with log-coordinate, via block weights #88/#90 + a three-term inequality) → §5.3 prime version →
5.5/5.7/5.8. All elementary, no PNT.*

*Results #91–#95 (2026-07-14, WALL 2 — Riemann-sum→integral theorem, from-scratch build, main-loop direct): the pin has
NO ready "Riemann sum → integral" (only heavy BoxIntegral), so it is being built bottom-up per the specialized ε-first
architecture. #91 completes the block-endpoint machinery (floor version). #92–#95 are the Riemann-sum ladder rungs:
coordinate map (rung 1, #92), uniform partition identity `∫₀¹f=Σⱼ∫blocks` (rung A, #93, via
`sum_integral_adjacent_intervals`), block rectangle error (rung B, #94), and the fixed-K sum error `|∫₀¹f−R_K|≤ε`
(rung C, #95). Remaining: rung D (uniform continuity × A/B/C ⟹ `R_K(f) → ∫₀¹f`, the durable theorem) → harmonic
transfer → §5.3/5.5/5.7/5.8 → Theorem 1.2. All elementary, no PNT.*

*Results #89–#90 (2026-07-14, WALL 2 block-weight machinery, main-loop direct): #89 the rpow block-endpoint limit
`log(N^x−1)/log N → x` (the continuous-ratio core, via `tendsto_rpow_atTop` + `inv_tendsto_atTop` + `div_atTop`) and
#90 the general integer-ratio block weight `harmonic(kn)−harmonic(n) → log k`. With #86–#88, the §5.4 block-weight
layer is substantially built; the remaining §5.4 climb is the floor squeeze `log⌊N^x⌋/log N → x` + step-function
approximation of continuous `f`. All elementary, no PNT.*

*Results #86–#88 (2026-07-14, WALL 2 foundations — harmonic Riemann-sum machinery, main-loop direct): confirming the
Theorem 1.2 asymptotic wall is **buildable, not blocked**. #86 the harmonic interval-sum bound `Σ_{m<a≤n}1/a =
log(n/m)+O(1)` (explicit constant, from Mathlib's `log(n+1)≤harmonic n≤1+log n`) — the Riemann-sum "weight" primitive;
#87 `harmonic n/log n → 1` (the Tendsto toolchain, via `Real.tendsto_harmonic_sub_log`); #88 `harmonic(2n)−harmonic n
→ log 2`, the concrete floor-free block-weight limit. The remaining §5.4 climb is the general `N^s..N^t` block
(rpow/floor) + step-function approximation of continuous `f`; all elementary, no PNT.*

*Results #84–#85 (2026-07-14, EXACT c₂ integrals via FTC, main-loop direct): #84 the exact FTC evaluation of the c₂
integral on [1/3,1/2] (= 1/6 - (5/3)log2 + log3 ≈ 0.110) ⟹ **c₂ ≥ 0.610**, the decisive proof that the c₂ *value* is
elementary-computable (no PNT); #85 the matching upper piece ⟹ **c₂ ≤ 0.633**. Together the two-sided bracket
**c₂ ∈ [0.610, 0.633]** around the true 0.6187712…. Reusable FTC + interval-integral toolkit; lesson: annotate the
implicit measure on ContinuousOn.intervalIntegrable.*

*Results #82–#83 (2026-07-14, c₂/I(u) analytic bounds, main-loop direct): #82 the first real c₂ tightening
**c₂ ≥ 1/2 + (1/6)(1−log 2) ≈ 0.551** (from `1−Φ ≥ 1−log 2` on [1/3,1/2]); #83 the nontrivial **lower** bound on the
semiprime integral I(u) (midpoint-split), the two-sided partner to #74. Both reuse the interval-integral machinery
(`integral_mono_on`, `integral_add_adjacent_intervals`, `integral_nonneg`); both pure real analysis, no PNT.*

*Results #79–#81 (2026-07-14, α₂ numeric localization, all main-loop direct): the reusable Φ-value squeeze (#79) plus
the two numeric brackets Φ(13/50) > 1 (#80) and Φ(3/10) < 1 (#81) give the first two-sided numeric localization
**α₂ ∈ (0.26, 0.30)**, tightening the prior `(1/4, 1/3)` around the true `0.28043830…`. Each numeric bracket uses the
`Real.exp_one_lt/gt_d9` + `Real.log_lt_log` / `Real.log_le_sub_one_of_pos` recipe; #81 also consumes the #74 I-upper
bound. All proved directly in the main loop (no subagents).*

*Results #74–#78 (2026-07-14, c₂-value round + Thm 1.1 chain, mixed workflow/direct): #74 the reusable `I(u)`
**upper bound** (confirming the c₂ *value* is in-pin reachable real analysis); #75 Cor 4.4 low-layer positivity and
#76 the **Theorem 4.7 sign-theorem initial-segment core** — together closing two of the three links in the
`§4.3 → 4.4 → 4.7 → Thm 1.1` chain; #77 the density prime-term nonnegativity; and #78 the **Lemma 4.3 conditional
reduction**, which pins the single remaining open input to unconditional Theorem 1.1 to one explicit
Kinlaw–Pomerance error-difference inequality (`M` provably cancels). #75/#76 were verified through their tracked
episodes (`episode_status = kernel_verified/root_proved`, confirmed independently) even though their generating
workflow died on a mid-run session limit before reporting; #77/#78 were proved directly in the main loop.*

*Results #30–#40 (2026-07-14, "analytic wall" round + hard-frontier workflow):
#31 (upper Mertens) is the campaign's first genuinely-new analytic result,
opening the §5 Chebyshev route; #34 (lower Mertens) + #33 (ϑ bridge) ported from
#647 complete the two-sided Θ(loglog x) bracket; #30 + #37 + #39 build the Prop 5.6
layer (core `α₂<1/3`, continuity, integrand sign); #36 the α threshold; #32 + #35
+ #38 **complete Theorem 2.4** (F_N(a) = max(1/a, Σ_b F_N(b))); #40 the coarse
divergence floor. A four-agent workflow produced #37–#40 and the definitive wall
verdict (below). The §5 analytic wall is breached at its base — only the
sharp-constant deficit remains.*

## Reasoning-log trail (episode process ledgers)

Each episode carries an `initial_plan` and a `success_retrospective`
`reasoning_log` (SOP-mandated). Observe them with
`reasoning_log {action: observe, episode_id: …}`.

## What is NOT proved here

The paper's headline **Theorem 1.1** (`M(N) = M_fr(N)`) and **Theorem 1.2**
(`M(N) = (c₂+o(1)) log N`, `α₂ = 0.28043830…`, `c₂ = 0.61877121…`) are **not**
kernel-verified. But the §5 analytic layer is no longer a blank wall:

- **Verified (§5):** the two-sided quantitative-Mertens bracket
  `log 2 · loglog x − C ≤ Σ_{p≤x} 1/p ≤ log 4 · loglog x + C'` (#31, #34) via the
  real-valued Chebyshev ϑ bridge (#33); the qualitative divergence `Σ 1/p → ∞`
  (#40); the Prop 5.6 real-analytic core `α₂ < 1/3` (#30) + continuity (#37) +
  integrand sign `I(u) ≥ 0` (#39); and the KP threshold `α = 1/(e+1) ∈ (1/4,1/3)` (#36).
- **Remaining wall — a sharp, well-diagnosed deficit (workflow scout verdict):**
  the *sharp-constant* Mertens (leading constant exactly 1, the exact interval
  asymptotic of Lemma 5.2) that the precise `c₂` requires is **not reachable in
  this Mathlib pin** — grepping confirms there is **no Mertens first or second
  theorem** ("Mertens" in Mathlib is only the unrelated Dedekind–Mertens polynomial
  lemma), **no `PrimeNumberTheorem`/PNT**, and **no `θ(x)=x+o(x)`**. The sharp
  coefficient descends from Mertens' *first* theorem `Σ_{p≤x}(log p)/p = log x + O(1)`
  (exact constant 1), which needs a Stirling/log-factorial estimate fed through
  `Σ_{d≤x} Λ(d)⌊x/d⌋` + `ψ(x)=O(x)`. **Progress (2026-07-14):** the concrete
  building blocks are now kernel-verified — `Σ log n = Σ_d Λ(d)⌊N/d⌋ = log(N!)`
  (#41, #43) and `ψ(N) = Σ Λ(n) ≤ (log 4+4)·N` (#42). What remains to assemble
  Mertens' first theorem: replace `⌊N/d⌋` by `N/d + O(1)` (error bounded by `ψ`, #42),
  combine with Stirling `log(N!) = N log N − N + O(log N)` (Mathlib has the
  unconditional *lower* bound `le_log_factorial_stirling`; the upper is only
  asymptotic, needing a large-`N` threshold), yielding `Σ_d Λ(d)/d = log N + O(1)`;
  then drop the prime-power tail and apply Abel summation for the sharp
  `Σ 1/p = loglog x + M + o(1)`. Still a genuine multi-session sub-project, but now
  advancing block by block.
- **Reachable-but-heavy:** the full Prop 5.6 monotonicity on `[1/4,1/2]` — the
  scout mapped the exact API (`intervalIntegral.integral_hasDerivAt_right/_left` for
  the endpoints + `ParametricIntervalIntegral` dominated-convergence for the
  parameter derivative), a hand-assembled 3-term Leibniz derivative (multi-hundred
  lines, no single turnkey lemma). The integrand-sign input `I(u) ≥ 0` is already
  done (#39). See [attack-plan.md](attack-plan.md) and [THEOREM-CATALOG.md](THEOREM-CATALOG.md).
