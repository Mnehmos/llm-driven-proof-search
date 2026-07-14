# Erdős Problem #858 — an exact frontier theorem, and what we can machine-check

**Problem folder whitepaper — started 2026-07-13, LIVE campaign**

> **Status: Erdős Problem #858 is marked SOLVED** on
> [erdosproblems.com/858](https://www.erdosproblems.com/858) (page last edited
> 24 April 2026): the answer `max_A Σ 1/n = (c + o(1)) log N`, `c ≈ 0.618…`,
> credited to Chojecki and GPT-5.4 Pro — matching the `erdos858.pdf` note here
> (`c₂ = 0.6187712111…`). The site also shows **"Formalised statement? No"**:
> there is *no* machine-checked formalization of #858 yet. This folder does
> **not** independently re-derive the full `c₂` asymptotic (that is the analytic
> wall), so it neither endorses nor refutes the paper's headline theorems. It
> records our own, fully independent, kernel-verified progress on the paper's
> foundational layer, and an honest map of exactly where the analytic wall begins.

## The problem

For `A ⊆ {1,…,N}`, call `A` *admissible* if there is no solution to `b = a·t`
with `a, b ∈ A` and `P⁻(t) > a` (the least prime factor of `t` exceeds `a`).
Let

```
M(N) := max_A  Σ_{n∈A} 1/n,        𝓜(N) := M(N) / log N.
```

This is Erdős #858 (Erdős, *Some extremal problems in combinatorial number
theory*, 1970, p. 128). A trivial construction — all of `(√N, N]` — already
gives `M(N) ≥ ½ log N + O(1)`; the paper's point is that the true optimum is far
more rigid.

## The paper's architecture (and where it gets hard)

Chojecki attaches to the relation a **partial order** `a ⪯ b ⟺ b = a·t,
P⁻(t) > a`. Admissibility is exactly "`A` is a `⪯`-antichain". Then:

1. **§1–§2 — the rooted tree.** `⪯` is a partial order; the proper ancestors of
   any `n` are linearly ordered (Lemma 2.1 ⇒ Cor 2.2), so each `n>1` has a
   well-defined parent `π(n)` = maximal proper ancestor, making `{1,…,N}` a
   rooted tree. `π(a·p) = a` for primes `p > a` (Lemma 2.7). *Elementary,
   order-theoretic.*
2. **§3 — frontiers & max-closure.** With `q_N(a) := C_N(a) − 1/a`, the frontier
   sums telescope (`S_N(K) = 1 + Σ_{a≤K} q_N(a)`), and a max-closure identity
   reduces `M(N)` to `1 + max_D Σ_{a∈D} q_N(a)` over continuation sets. *Finite
   combinatorics on the tree.*
3. **§4 — the sign theorem.** `M(N) = M_fr(N)` follows once `{a : R_N(a) > 1}`
   (`R_N(a) := a·C_N(a)`) is an *initial segment*. Proved by three ingredients:
   (i) a finite exact `ν(a)` table for `a ≤ 19`; (ii) a prime-harmonic bound on
   the low layer `20 ≤ a ≤ N^{1/4}`; (iii) monotonicity on the upper layer via
   the prime–semiprime description of children. *Ingredient (ii) needs
   explicit-error Mertens.*
4. **§5–§6 — the asymptotic constant.** Prime–semiprime Riemann-sum analysis
   gives `K*(N) = N^{α₂+o(1)}`, `M(N) = (c₂+o(1)) log N`, where `α₂` is the
   unique root in `(¼,⅓)` of `Φ(u)=1` and `c₂ = ½ + ∫_{α₂}^{1/2}(1−Φ(u))du`.
   *Genuine analytic number theory: Mertens on polynomial intervals, uniform
   Riemann-sum convergence, monotonicity of an integral functional.*

## What we machine-checked (2026-07-13 – 2026-07-14)

The **§1–§2 order-theoretic backbone (plus a concrete `π`), the §1 trivial-bound
admissibility, the complete §4 prime–semiprime description (Lemma 4.5), the §3
frontier-sweep spine (Prop 3.2 + Lemma 3.1), the entire §3 max-closure reduction
machinery culminating in the Corollary 3.5 capstone `M(N) = S_N(K)`, the **fully
verified Theorem 2.4 subtree recursion** (root dichotomy + child-merge +
value-function `max'` ⟹ `F_N(a) = max(1/a, Σ_b F_N(b))`), Remark 2.5 (Bellman
form), Prop 4.1 `ν(1)=4`, and the full Prop 4.6 (`P_N` + `Q_N`)** — and, in the
**2026-07-14 "analytic wall" round (orchestrator + a four-agent hard-frontier
workflow), the first §5 analytic results**: the **two-sided quantitative-Mertens
bracket** `log 2·loglog x − C ≤ Σ_{p≤x} 1/p ≤ log 4·loglog x + C'` (built on a
real-valued Chebyshev `ϑ` bridge over Mathlib's `Chebyshev.theta_ge` /
`theta_le_log4_mul_x`), `Σ 1/p → ∞`, the **Proposition 5.6** real-analytic core
(`Φ` strictly decreasing and `< 1` on `[1/3,1/2]`, so `α₂ < 1/3`) with continuity
on `[1/3,1/2]` and the semiprime-integral sign `I(u) ≥ 0`, and the
**Kinlaw–Pomerance threshold** `α = 1/(e+1) ∈ (1/4,1/3)`, and the first
**Mertens-first-theorem building blocks** (`Σ log n = Σ_d Λ(d)⌊N/d⌋ = log N!`,
`ψ(N) ≤ (log 4+4)N`) toward the sharp `c₂` — as **seventy-three** independent
`kernel_verified` results (pinned Lean 4.32.0-rc1 + mathlib@360da6fa; full records
in [evidence.md](evidence.md)):

- **`⪯` is a partial order** — reflexivity, antisymmetry, transitivity on the
  positive integers (paper §1). The Introduction *asserts* this; here it is
  proved.
  → [proof/Erdos858_PreceqPartialOrder.lean](proof/Erdos858_PreceqPartialOrder.lean)
- **Lemma 2.1 (sandwich lemma)** — `a⪯n, b⪯n, a<b<n ⇒ a⪯b`. This is the
  lemma that makes the ancestor chain linear and hence `π` well-defined and the
  rooted tree exist.
  → [proof/Erdos858_Lemma21_Sandwich.lean](proof/Erdos858_Lemma21_Sandwich.lean)
- **Lemma 2.7 core (prime child uniqueness)** — for prime `p > a`, any ancestor
  `b` with `a ⪯ b ⪯ a·p` is `a` or `a·p`; i.e. `π(a·p) = a`, the fact behind
  the prime-child count.
  → [proof/Erdos858_Lemma27_PrimeChildCore.lean](proof/Erdos858_Lemma27_PrimeChildCore.lean)
- **Corollary 2.2 (ancestors linearly ordered)** — any two proper ancestors of
  `n` are `⪯`-comparable, so the maximal proper ancestor `π(n)` exists and the
  rooted tree is well-defined. The corollary that legitimizes the construction.
  → [proof/Erdos858_Cor22_AncestorsLinear.lean](proof/Erdos858_Cor22_AncestorsLinear.lean)
- **Lemma 4.5 core (prime–semiprime cofactor)** — in the upper layer
  `a > N^{1/4}`, a child's cofactor `t = n/a` satisfies `t < a³` and has all
  prime factors `> a`, hence `Ω(t) ≤ 2`: `t` is prime or semiprime. This is the
  `ap`/`apq` dichotomy giving `R_N(a) = P_N(a) + Q_N(a)`.
  → [proof/Erdos858_Lemma45_CofactorPrimeSemiprime.lean](proof/Erdos858_Lemma45_CofactorPrimeSemiprime.lean)
- **Lemma 4.5 sub-fact (`π(a·p·q) = a`)** — `b ⋠ b·q` for a prime `q < b`; with
  `b = a·p` this shows `a·p` is not a proper ancestor of the semiprime `a·p·q`,
  so its parent is `a`. Completes the prime–semiprime child description.
  → [proof/Erdos858_Lemma45_PiApqSubfact.lean](proof/Erdos858_Lemma45_PiApqSubfact.lean)
- **Trivial lower bound (`(√N, N]` antichain)** — `N < a²`, `a < b ≤ N` ⇒
  `a ⋠ b`, so the top block is admissible: the source of the paper's
  `M(N) ≥ ½ log N + O(1)`.
  → [proof/Erdos858_TopBlockAntichain.lean](proof/Erdos858_TopBlockAntichain.lean)
- **Lemma 2.7 full (`π(a·p) = a`)** — existence of the child `a·p` plus the
  uniqueness core, together the complete parent identity.
  → [proof/Erdos858_Lemma27_PiApFull.lean](proof/Erdos858_Lemma27_PiApFull.lean)
- **`⪯` refines `∣` and `≤`, and a proper step doubles** — `a ⪯ b ⇒ a ∣ b`,
  `a ≤ b`, and `a < b ⇒ 2a ≤ b`. Root-to-leaf paths thus have length `≤ log₂ N`.
  → [proof/Erdos858_PreceqRefinesOrder.lean](proof/Erdos858_PreceqRefinesOrder.lean)
- **Every proper `⪯`-multiple has a prime factor `> a`** — the mechanism behind
  admissibility and the prime–semiprime child structure.
  → [proof/Erdos858_CofactorLargePrimeFactor.lean](proof/Erdos858_CofactorLargePrimeFactor.lean)
- **Lemma 4.5 full dichotomy** — a child cofactor `t < a³` (all prime factors
  `> a`) is `1`, prime, or a product of two primes: the explicit `a`/`a·p`/`a·p·q`
  child forms, completing Lemma 4.5.
  → [proof/Erdos858_Lemma45_FullDichotomy.lean](proof/Erdos858_Lemma45_FullDichotomy.lean)

The last four were produced in a single **ultracode multi-agent round**: three
parallel subagents proved `π(a·p)=a`, the order-compatibility bundle, and the
large-prime cofactor fact, while the orchestrator proved the Lemma 4.5 dichotomy
— all four `kernel_verified` on the first submission.

### The §3 frontier-sweep spine (Proposition 3.2 + Lemma 3.1)

A second ultracode round machine-checked the frontier sweep — the identity that
makes the frontier problem tractable:

- **Prop 3.2, single-step increment** — `S_N(K+1) = S_N(K) + (C_N(K+1) −
  1/(K+1))`, via the Finset decomposition `A_N(K+1) = (A_N(K) \ {K+1}) ⊍
  {children of K+1}` (raise the cutoff: lose vertex `K+1`, gain its children).
  The hard linchpin; proved by the orchestrator.
  → [proof/Erdos858_FrontierSweepStep.lean](proof/Erdos858_FrontierSweepStep.lean)
- **Prop 3.2, abstract telescoping** — `s 0 = 1 ∧ s(K+1) = s K + g(K+1) ⇒
  s K = 1 + Σ_{a=1}^K g a`.
  → [proof/Erdos858_FrontierSweepTelescope.lean](proof/Erdos858_FrontierSweepTelescope.lean)
- **Prop 3.2, base** — `A_N(0) = {1}`, so `S_N(0) = 1`.
  → [proof/Erdos858_FrontierBaseZero.lean](proof/Erdos858_FrontierBaseZero.lean)
- **Lemma 3.1** — the frontier `A_N(K)` is a `⪯`-antichain (so it is a genuine
  admissible set).
  → [proof/Erdos858_FrontierAntichain.lean](proof/Erdos858_FrontierAntichain.lean)

Composing the first three gives the paper's **`S_N(K) = 1 + Σ_{a≤K} q_N(a)`
(Proposition 3.2)**. The remaining spine toward Theorem 1.1 is the **max-closure
duality** — Proposition 3.4 (`M(N) = 1 + max_D Σ_{a∈D} q_N(a)`) and Corollary 3.5
(the initial-segment optimization) — which needs a continuation-set /
`M(N)`-as-max-over-antichains layer (the exchange argument of Lemma 3.3). That is
the precisely-scoped next target.

The §3 lemmas are stated over an **abstract parent map** `π` with the structural
axioms proved in §1–§2 (`π 1 = 0`, `2 ≤ n ≤ N ⇒ 1 ≤ π n < n`, and — for the
antichain — π-maximality from Corollary 2.2), so they compose directly onto the
verified order-theoretic foundation once `π` is instantiated.

### A genuine concrete π, and Tier 1's remaining pieces

A third ultracode round closed the "abstract π" gap and picked up two more
Tier-1 targets:

- **Concrete `π`** — `piFn(n) := max{a<n : a⪯n}` (via `Finset.max'` over the
  already-verified `⪯` relation) satisfies all three abstract axioms used
  above, in a single kernel-verified theorem. This deliberately **avoids**
  re-deriving Lemma 2.3's prefix-product characterization: hand-checking the
  paper's own definitions turns up a genuine subtlety — a *naive greedy* `π`
  (left-to-right, extend while the next prime exceeds the running product,
  stop at the first failure) is **provably wrong**. Counterexample:
  `n = 99 = 3·3·11`. The prefix `3` is *not* an ancestor of `99` (cofactor
  `33=3·11` has least prime factor `3`, not `>3`), but the *later* prefix
  `9=3·3` *is* an ancestor (cofactor `11`, least prime factor `11>9`) —
  validity of a prefix index is genuinely non-monotone, so Lemma 2.3's own
  statement ("`π(n)=P_k` for the **largest** valid `k`") reflects a real
  subtlety a greedy scan would miss. `piFn` sidesteps this entirely by taking
  the max directly over the verified order relation.
  → [proof/Erdos858_ConcretePiAxioms.lean](proof/Erdos858_ConcretePiAxioms.lean)
- **Prop 4.1, `ν(1)=4`** — a genuine, kernel-checked instance of the paper's
  one computer-assisted table entry: `n∈{2,3,4}` each have only-ancestor `1`,
  and `1/2+1/3+1/4>1≥1/2+1/3`.
  → [proof/Erdos858_Prop41_NuOneEqFour.lean](proof/Erdos858_Prop41_NuOneEqFour.lean)
- **Prop 4.6, `P_N` monotonicity** — `0<a≤b ⇒ P_N(a)≥P_N(b)`, via nested
  prime-sum domain containment.
  → [proof/Erdos858_Prop46_PNMonotone.lean](proof/Erdos858_Prop46_PNMonotone.lean)

**Honesty note on the rest of Prop 4.1.** The full `ν(a)` table (`a=2..19`,
with `ν(19)=80807`) is **not** attempted here. Our `⪯` relation is Prop-valued
(`∃t,∀prime p∣t,...`), decidable in this proof only via `Classical.decPred`
(proof-theoretic, not computable) — evaluating it via `decide`/`native_decide`
over ranges up to tens of thousands is not realistic without first building a
genuinely computable reformulation (e.g. via `Nat.minFac`) and proving it
equivalent to `⪯`, a substantially larger undertaking than the rest of this
round. Similarly, Prop 4.6's `Q_N` (semiprime pair-sum) half is not yet done.

### The §3 max-closure reduction — all components, exchange-free

The paper reduces the Erdős maximum `M(N)` to the frontier problem via a
max-closure duality: `M(N) = 1 + max_D Σ_{a∈D} q_N(a)` over continuation sets
`D`, then optimizes to `[1,K]`. Every component of this reduction is now
machine-checked (all over the abstract parent map `π`):

- **Proposition 3.4 (max-closure identity)** — `Σ_{n∈∂D} 1/n = 1 + Σ_{a∈D} q_N(a)`
  for a continuation set `D`. Fiberwise grouping (`Finset.sum_fiberwise_of_maps_to`)
  + the partition `{m : π m ∈ D} = ∂D ⊍ (D\{1})` + root-splitting.
  → [proof/Erdos858_Prop34_MaxClosureIdentity.lean](proof/Erdos858_Prop34_MaxClosureIdentity.lean)
- **∂D is a `⪯`-antichain** — so each continuation set's boundary is a genuine
  admissible antichain (weight `≤ M(N)`).
  → [proof/Erdos858_BoundaryAntichain.lean](proof/Erdos858_BoundaryAntichain.lean)
- **Cor 3.5 optimization inequality** — `Σ_{a∈D} q_N ≤ Σ_{a≤K} q_N` under the
  sign condition, and **`[1,K]` is a continuation set** (downward-closed).
  → [proof/Erdos858_Cor35_OptimizationInequality.lean](proof/Erdos858_Cor35_OptimizationInequality.lean),
  [proof/Erdos858_Cor35_InitialSegmentClosed.lean](proof/Erdos858_Cor35_InitialSegmentClosed.lean)
- **Exchange-free stopping-set construction (replacing Lemma 3.3)** — the paper
  turns an arbitrary antichain into a `∂D` by *iteratively adding leaves*. We
  found a **direct, non-iterative** construction: for any antichain `B` (with
  `1 ∉ B`), the set `D_B := {a : no ⪯-ancestor of a lies in B}` is a
  continuation set with `B ⊆ ∂D_B`. This is arguably a small simplification of
  the paper's own argument.
  → [proof/Erdos858_StoppingSetConstruction.lean](proof/Erdos858_StoppingSetConstruction.lean)

Chaining these (for any antichain `B`: `w(B) ≤ w(∂D_B) = 1 + Σ_{D_B} q_N ≤
1 + Σ_{[1,K]} q_N = S_N(K)`, and `A_N(K) = ∂[1,K]` achieves `S_N(K)`) gives
Corollary 3.5, `M(N) = S_N(K)`. **The only unwritten step is the definitional
glue**: packaging `M(N)` as a `Finset.max'` over the admissible antichains
(`(Icc 1 N).powerset.filter(antichain)`) and quoting the verified components —
no new mathematics, just Lean bookkeeping. Also verified: **Remark 2.5**, the
Bellman rescaling `V_N(a) = a·F_N(a)` making the subtree optimization an
optimal-stopping problem.
→ [proof/Erdos858_Remark25_BellmanForm.lean](proof/Erdos858_Remark25_BellmanForm.lean)

### One idea did all three

The paper argues §2 through per-prime `p`-adic valuations (`ν_q(a) = ν_q(n)`).
In Lean that bookkeeping is unnecessary: encoding `P⁻(t) > a` as *"every prime
factor of `t` exceeds `a`"* turns each lemma into elementary divisibility.
The recurring device is **cancel `a`**: from `a·u = b·v = a·(t·v)` conclude
`u = t·v` (`Nat.eq_of_mul_eq_mul_left`), which transports a prime lower bound
from one cofactor onto another. Coprimality (`Nat.coprime_of_dvd`) replaces the
"no small prime is shared" half of Lemma 2.1, and `Nat.Prime.eq_one_or_self_of_dvd`
collapses the sandwiched ancestor in Lemma 2.7. All three proofs landed on the
first submission.

## Where the wall is — honestly

`M(N) = M_fr(N)` (Theorem 1.1) and the constant `c₂` (Theorem 1.2) are **not**
machine-checked here. But the picture has changed materially: the §3 frontier
combinatorics is **done** (the Corollary 3.5 capstone `M(N) = S_N(K)` is
kernel-verified, as is the full Theorem 2.4 subtree recursion and Prop 4.6), and
the §5 analytic wall — previously a blank barrier — has been **breached at its
base**. What remains:

- **✅ Combinatorics complete (§2–§3).** The frontier sweep, max-closure identity
  and Corollary 3.5 reduction, and the **full Theorem 2.4 recursion**
  (`F_N(a) = max(1/a, Σ_b F_N(b))`, all three pieces) are verified. No
  infrastructure gap remains between the order theory and the frontier
  characterization `M(N) = S_N(K)`.
- **✅/🧱 §5 analytic layer, first results (2026-07-14).** The two-sided
  **quantitative-Mertens bracket** `log 2·loglog x − C ≤ Σ_{p≤x} 1/p ≤
  log 4·loglog x + C'` is now kernel-verified, via a real-valued Chebyshev `ϑ`
  bridge over Mathlib's `Chebyshev.theta_ge` / `theta_le_log4_mul_x`; so are
  `Σ 1/p → ∞`, the Prop 5.6 real-analytic core (`α₂ < 1/3`) with continuity on
  `[1/3,1/2]` and the semiprime-integral sign `I(u) ≥ 0`, and the KP threshold
  `α = 1/(e+1)`.
- **🧱 The remaining wall — a sharply *diagnosed* deficit.** A workflow scout
  grepped the pin: the exact `c₂` needs Mertens with leading constant *exactly 1*,
  but Mathlib has **no Mertens first or second theorem** (only the unrelated
  Dedekind–Mertens polynomial lemma), **no PNT**, and **no `θ(x)=x+o(x)`** — so the
  sharp constant is genuinely a multi-session Mathlib-development sub-project (build
  Mertens' first theorem from Stirling + `Σ Λ(d)⌊x/d⌋` + `ψ(x)=O(x)`). Lemma 4.3
  depends on it. The other open piece — the full Prop 5.6 monotonicity on
  `[1/4,1/2]` — is *reachable but heavy*: the scout mapped the exact Leibniz API
  (FTC endpoint lemmas + `ParametricIntervalIntegral` dominated convergence) to a
  hand-assembled 3-term derivative; the integrand-sign input `I(u) ≥ 0` is done.

**The foothold became a result.** The sibling campaign
[erdos-647/proof/Erdos647_MertensAssembly.lean](../erdos-647/proof/Erdos647_MertensAssembly.lean)
kernel-verifies the Abel-summation identity
`Σ_{p≤x} 1/p = θ(x)/(x log x) + ∫ (log t+1)/(t² log²t)·θ(t) dt` and a full lower
Mertens bound; #858 ported that lower bound (evidence #34) and, driving the same
identity with Chebyshev's *upper* bound, added the matching **upper** bound
(evidence #31, new to the ecosystem) — see [attack-plan.md](attack-plan.md).

## The single computer-assisted step (Prop 4.1)

Per the paper's own Remark 4.2, the `ν(a)` threshold table for `a ≤ 19` is the
*only* computer-assisted ingredient in Theorem 1.1; everything else past
`a ≤ 19` is analytic. That finite exact rational computation is independent of
the wall and is a clean near-term target (🟡).

## Status, plainly

No claim on the open problem (it is already solved; this is a formalization
effort). What changed: the paper's entire order-theoretic foundation and §3
frontier combinatorics are machine-checked through the Corollary 3.5 capstone
`M(N) = S_N(K)`; the Theorem 2.4 recursion's combinatorial content is verified;
and the §5 analytic wall has been breached at its base — the two-sided
quantitative-Mertens bracket, the Prop 5.6 core, and the KP threshold are now
kernel-verified (102 results total; incl. the reusable **left-endpoint Riemann-sum →
interval-integral theorem for continuous f, built from scratch** as the §5.4 engine; α₂ now numerically bracketed to (0.26, 0.30),
and — via EXACT FTC evaluation of the density integral, no PNT — c₂ bracketed
two-sided to **[0.610, 0.633]** around the true 0.6187712…; and the §5.4 log-harmonic
transfer for Theorem 1.2 now has its five abstract rungs verified — the log-scale block mass
`harmonic(⌊N^x⌋)/log N → x` (#98), interval mass
`(harmonic(⌊N^t⌋)−harmonic(⌊N^s⌋))/log N → t−s` (#99), the fixed-K weighted step-sum →
Riemann step-sum `R_K(f)` (#100), the aggregation error bound
`|Σ S_j − Σ w_j·m_j| ≤ ε·Σ m_j` (#101), and the diagonal two-limit squeeze that assembles
them into `(1/log N)Σ f(u_a)/a → ∫₀¹f` (#102) — leaving only the concrete block partition
identity), and the concrete
building blocks of Mertens'
first theorem are now verified (double-count identity, `log(N!)` bridge, `ψ=O(x)`).
Toward the two headline theorems the dependency chains have tightened further: the
**Theorem 4.7 sign-theorem initial-segment core** and the **Cor 4.4 low-layer
positivity** are now kernel-verified (#76, #75), reducing unconditional Theorem 1.1
to the single §4.3 low-layer prime bound; and the explicit **`I(u)` upper bound**
(#74) confirms the exact `c₂` *value* is reachable in-pin real analysis.
The remaining barrier is a *sharp-constant* Mertens / exact-`c₂` deficit —
diagnosed to a specific missing Mathlib layer (no assembled Mertens theorem, no
PNT) that the campaign is now building block by block. Full inventory:
[THEOREM-CATALOG.md](THEOREM-CATALOG.md). Machine records:
[evidence.md](evidence.md). Attribution and limits: [credit.md](credit.md).
