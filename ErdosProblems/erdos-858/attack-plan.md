# Erdős #858 — attack plan

Ordered by tractability. The goal is to grow the machine-checked region of the
paper outward from the verified §1–§2 backbone, being explicit about which
targets are infrastructure (📐) vs. real analysis (🧱).

## Campaign status — 2026-07-14 (analytic-wall round: the wall is breached at its base)

**40 kernel-verified theorems.** The complete combinatorial content of Erdős #858
is machine-checked — capstone **Corollary 3.5 `M(N) = S_N(K)`** plus §1–§3 in
full, §4 arithmetic (Lemma 4.5, Prop 4.6 `P_N`+`Q_N`, `ν(1)=4`), and the **FULLY
verified Theorem 2.4 subtree recursion** (root dichotomy #32 + child-merge #35 +
value-function `max'` characterization #38 ⟹ `F_N(a) = max(1/a, Σ_b F_N(b))`).
First machine-checked formalization of any part of #858 (site: "Formalised
statement? No").

**The "analytic wall" of §5 was breached this round** (the earlier "concluded at
the combinatorial boundary" assessment is superseded) — orchestrator + a
four-agent hard-frontier workflow. Verified §5/analytic:

- ✅ **Two-sided quantitative-Mertens bracket** (#31 upper, #34 lower):
  `log 2·loglog x − C ≤ Σ_{p≤x} 1/p ≤ log 4·loglog x + C'`, via the real-valued
  Chebyshev `ϑ` bridge (#33) over Mathlib's `Chebyshev.theta_ge` /
  `theta_le_log4_mul_x`. The **upper bound (#31) is new to the ecosystem** — #647
  only had the lower. Growth content under Lemma 5.2. Plus `Σ 1/p → ∞` (#40).
- ✅ **Prop 5.6** (#30 core `α₂ < 1/3`; #37 continuity on `[1/3,1/2]`; #39
  semiprime-integral sign `I(u) ≥ 0` for `u ≤ 1/3`, the Leibniz argument's
  integrand-sign input).
- ✅ **KP threshold** `α = 1/(e+1) ∈ (1/4,1/3)` (#36).

**Remaining frontier — sharply DIAGNOSED (workflow scout verdicts):**

- 🧱 **Sharp-constant Mertens / exact `c₂` — NOT reachable in this Mathlib pin.**
  A scout grepped the pin: **no Mertens first or second theorem** ("Mertens" is
  only the Dedekind–Mertens polynomial lemma), **no PNT**, **no `θ(x)=x+o(x)`**,
  and Chebyshev's clean lower bound is an open TODO. The sharp coefficient `1`
  descends from Mertens' *first* theorem `Σ(log p)/p = log x + O(1)`, whose
  Stirling + `Σ Λ(d)⌊x/d⌋` + `ψ(x)=O(x)` assembly Mathlib lacks. The Chebyshev
  route only brackets `log 2 ≤ const ≤ log 4`. This is a genuine multi-session
  Mathlib-development sub-project (build Mertens' first theorem from scratch).
- 🧱 **Full Prop 5.6 monotonicity on `[1/4,1/2]`** — REACHABLE BUT HEAVY. Scout
  mapped the exact API: `intervalIntegral.integral_hasDerivAt_right/_left` (FTC
  endpoints) + `ParametricIntervalIntegral` dominated-convergence (parameter
  derivative) → a hand-assembled 3-term `I'(u)` derivative, then sign analysis.
  No turnkey Leibniz lemma; multi-hundred-line obligation. Integrand-sign input
  `I(u) ≥ 0` already done (#39). CONVENTION WARNING: in Lean's `intervalIntegral`,
  `I(u)` for `u > 1/3` reverses orientation ((1-u)/2 < u) → strictly POSITIVE, not
  zero; any Φ encoding must use `∫ v in Set.Ioc u ((1-u)/2)` (vanishes on the empty
  domain) or restrict `I`'s formula to `u < 1/3` and set `Φ = log((1-u)/u)` for `u ≥ 1/3`.
- 🧱 **§4 sign theorem** (Lemma 4.3 `Σ_{a<p≤a³} 1/p > 1` for `a≥20`, then 4.4/4.7/4.8)
  — depends on the sharp Mertens (the `log 2` / `log 4` bracket is too loose).
- ⛔ **Full `ν(a)` table** (`a=2..19`) — needs a computable reformulation of the
  Prop-valued `⪯` (via `Nat.minFac`) + equivalence proof.

**To resume:** the only genuinely-new formal mathematics left is (a) building
Mertens' first theorem in Mathlib (the real gate to `c₂`) or (b) the heavy 3-term
Leibniz assembly for full Prop 5.6. `/loop` continues autonomously; if a round
finds only these two multi-session items, it logs footholds rather than spinning.

## Done (2026-07-13)

- ✅ `⪯` partial order (§1)
- ✅ Lemma 2.1 sandwich (§2)
- ✅ Lemma 2.7 prime-child uniqueness core (§2)
- ✅ Corollary 2.2 ancestors linearly ordered (§2) — `π` / rooted tree justified
- ✅ Lemma 4.5 cofactor prime/semiprime bound `Ω(t) ≤ 2` (§4)
- ✅ Lemma 4.5 sub-fact `b ⋠ b·q` (prime `q < b`) ⇒ `π(a·p·q) = a` (§4)
- ✅ Trivial lower bound: `(√N, N]` is a `⪯`-antichain (§1)
- ✅ Lemma 2.7 full `π(a·p) = a` (existence + uniqueness) (§2)
- ✅ `⪯ ⊆ (∣, ≤)` + proper step doubles (`a⪯b, a<b ⇒ 2a≤b`) (§1–§2)
- ✅ Proper `⪯`-multiple of `a` has a prime factor `> a` (§1–§2)
- ✅ Lemma 4.5 full dichotomy: child cofactor is `1`/prime/semiprime (§4)
- ✅ Prop 3.2 single-step increment `S(K+1)=S(K)+(C(K+1)−1/(K+1))` (§3)
- ✅ Prop 3.2 abstract telescoping `s K = 1 + Σ g` (§3)
- ✅ Prop 3.2 base `A_N(0)={1}` (§3)
- ✅ Lemma 3.1 frontier `A_N(K)` is a `⪯`-antichain (§3)

- ✅ Concrete `π` instantiation: `piFn(n):=max{a<n:a⪯n}` satisfies all 3
  abstract axioms used in §3 (§2, Cor 2.2 / Lemma 2.3 "first step")
- ✅ Prop 4.1 small instance: `ν(1)=4` (§4)
- ✅ Prop 4.6 `P_N` monotonicity (`0<a≤b ⇒ P_N(a)≥P_N(b)`) (§4)

- ✅ Prop 3.4 max-closure identity `Σ_∂D 1/n = 1 + Σ_D q_N` (§3)
- ✅ ∂D is a `⪯`-antichain (§3, Prop 3.4 consequence)
- ✅ Cor 3.5 optimization inequality `Σ_D q ≤ Σ_[1,K] q` (§3)
- ✅ `[1,K]` is a continuation set (downward-closed) (§3)
- ✅ exchange-free stopping-set construction, replaces Lemma 3.3 (§3)
- ✅ Remark 2.5 Bellman form `V_N(a)=max(1,Σ(a/b)V_N(b))` (§2)

**24 kernel-verified atoms. §1–§2 fully (with a concrete `π`), Lemma 4.5 fully,
the §3 frontier-sweep spine, the ENTIRE §3 max-closure reduction machinery
(Prop 3.4 + ∂D-antichain + optimization + [1,K]-closed + Lemma 3.3 stopping-set),
Remark 2.5, a Prop 4.1 instance, and Prop 4.6's `P_N` half are machine-checked.
Every component of Cor 3.5's `M(N)=1+max_D Σ_D q_N = S_N(K)` is verified.**

## Tier 1 — elementary, status

1. **Prop 4.1 `ν(a)` table (`a ≤ 19`).** ✅ `ν(1)=4` DONE (kernel-verified,
   small-range direct enumeration). **⚠️ Honest assessment on `a=2..19`:** the
   remaining thresholds range up to `ν(19)=80807`. Our `⪯` relation is
   Prop-valued (`∃t,∀prime p∣t,...`) and only decidable via `Classical.decPred`
   (proof-theoretic, not computable) — `decide`/`native_decide` over ranges of
   tens of thousands is **not realistically achievable** without first: (a)
   reformulating `⪯` computably (e.g. `a∣n ∧ (n/a=1 ∨ Nat.minFac(n/a)>a)` via
   `Nat.minFac`, which IS computable), (b) proving that reformulation
   equivalent to the Prop-valued `⪯` used everywhere else in this campaign,
   and (c) confirming the verifier's resource limits (300s proof timeout, 4MB
   source) actually accommodate evaluating `π` up to `n≈80807`. This is a
   genuinely separate, substantially larger sub-project — not attempted
   further here, flagged honestly rather than silently skipped or blindly
   retried.
2. **Lemma 2.3 (`π` prefix-product form).** ⚠️ **Attempted, gave up (honest).**
   SUPERSEDED for practical purposes by the concrete `π` instantiation above
   (✅ #16), which satisfies everything §3 needs without re-deriving Lemma 2.3's
   own (harder, genuinely non-monotone — see whitepaper.md's `n=99`
   counterexample) characterization. The *existence* half (valid-index prefix
   products of `n.primeFactorsList` ARE ancestors) was attempted twice (once by
   a subagent, killed mid-submission by a session limit; once by the
   orchestrator, problem `b4918b94`, episode `da15285b`, `gave_up`). The math is
   correct and all 6 needed Mathlib lemma names are deep_check-confirmed
   (`List.take_append_drop`, `List.prod_append`, `Prime.dvd_prod_iff`,
   `List.getElem_of_mem`, `List.getElem_drop`,
   `List.SortedLE.getElem_le_getElem_of_le`), but both submissions hit a
   `getElem` index-validity synthesis failure (`⊢ k < …length` with only
   `n k : ℕ` in scope) — the assembled `theorem := by` module cannot
   re-synthesize the index proof for the bare `n.primeFactorsList[k]` notation
   in the (hash-locked) statement, even though `problem_create` accepted it.
   **Fix for a future session:** register a NEW problem stating the prefix
   cutoff getElem-free — e.g. via `(n.primeFactorsList.drop k).headI`, or a
   bundled `n.primeFactorsList.get ⟨k, hk⟩`, or by pushing `k < length` into the
   existential — then the same proof strategy should go through. Low priority:
   completeness nicety, not on the critical path (concrete `π` already covers
   §3's needs).

## Tier 2 — infrastructure layer (📐: define, then the proofs are easy)

These are *elementary* once the supporting objects exist in Lean. Build, in order:

- **The parent map `π`** (Lemma 2.3 prefix-product form) and the child sets
  `ch_N(a)`, over `Finset (Icc 1 N)`.
- **The `1/n` sum layer:** `C_N(a) = Σ_{π(n)=a} 1/n`, `S_N(K) = Σ_{A_N(K)} 1/n`,
  `q_N(a) = C_N(a) − 1/a`, over `ℚ`.

Already done abstractly (over an abstract `π` with the §1–§2 axioms), composing
once `π` is instantiated: **Prop 3.2** (✅), **Lemma 3.1** (✅), and now the
**ENTIRE max-closure reduction machinery**: **Prop 3.4** identity (✅), **∂D
antichain** (✅), **Cor 3.5 optimization** (✅), **`[1,K]`-closed** (✅), and the
**exchange-free Lemma 3.3 stopping-set construction** (✅ — `D_B={a: no
⪯-ancestor in B}`, no iterative leaf-adding). **Remark 2.5** Bellman form (✅).

**THE ONE REMAINING STEP for a single-theorem Corollary 3.5 (`M(N) = S_N(K)`):**
the `M(N)`-as-max **definitional glue** (📐, no new mathematics). Define
`M(N) := ((Icc 1 N).powerset.filter (⪯-antichain)).image weight |>.max'` (or
`sup'`), then assemble the verified components:
  - ≤: any antichain `B`; if `1∉B`, stopping-set gives `D` with `B⊆∂D`, so
    `w(B) ≤ w(∂D)` (subset, weights ≥0) `= 1+Σ_D q` (Prop 3.4) `≤ 1+Σ_[1,K] q`
    (optimization) `= S_N(K)` (Prop 3.2); the `1∈B` case is `B={1}`, `w=1 ≤ S_N(K)`.
  - ≥: `A_N(K) = ∂[1,K]` is an admissible antichain (Lemma 3.1) with weight
    `S_N(K)` (Prop 3.2), so `M(N) ≥ S_N(K)`.
  The friction is purely Lean bookkeeping (SubmitModule combining the verified
  lemmas as helpers, or a conditional theorem taking their conclusions as
  hypotheses + the `Finset.max'` machinery). This is the recommended next target.

Still further out:
- **Prop 4.6 `Q_N` half** (semiprime pair-sum monotonicity) — the `P_N` half is ✅.
- **Lemma 6.1 / Thm 2.4 (Bellman DP)** — needs `F_N` as an actual max over
  subtree antichains (same `M(N)`-as-max layer as above).

Landing the glued Cor 3.5 gives the reduction "sign theorem ⇒ Theorem 1.1" fully
machine-checked — the milestone that isolates the analytic content (§4.2/§5 wall).

## Tier 3 — the analytic wall (🧱: real analysis / quantitative Mertens)

- **Lemma 4.3 / Cor 4.4 (low layer).** `Σ_{a<p≤a³} 1/p > 1` for `a ≥ 20`.
  Base cases `20 ≤ a ≤ 26` are finite prime sums (🟡). The tail `a ≥ 27` needs
  the explicit Mertens bracket `T(x) = loglog x + B + E(x)`, `−1/(2log²x) < E(x)
  < 1/log²x` (Kinlaw–Pomerance, Integers 19 (2019) A22).
  **Foothold:** [../erdos-647/proof/Erdos647_MertensIdentity.lean](../erdos-647/proof/Erdos647_MertensIdentity.lean)
  gives the exact `Σ 1/p = θ(x)/(x log x) + ∫ …·θ(t) dt` identity; combined with
  Mathlib `Chebyshev.theta` bounds this is the route to an explicit `E(x)`.
- **Lemma 5.2 (Mertens on polynomial intervals).** `Σ_{x<p≤y} 1/p =
  log(log y/log x) + o(1)` uniformly for `N^β ≤ x ≤ y ≤ N`. Direct consequence
  of `B(x) = loglog x + B₁ + o(1)`; the 647 identity is the same foothold.
- **Lemmas 5.3/5.4 (Riemann sums).** Uniform convergence of prime-harmonic and
  harmonic Riemann sums to `∫ …`. Standard but no ready Mathlib lemma.
- **Prop 5.6 (`Φ` analysis).** `Φ` strictly decreasing on `[¼,½]`, unique root
  `α₂` of `Φ = 1`. Pure real analysis (Leibniz rule, a monotonicity computation)
  — self-contained and arguably the *most* tractable wall piece.
- **Thm 4.7 (sign theorem) → Thm 1.1**, then **Thm 5.8 → Thm 1.2**.

## Sequencing recommendation

Tier 1 (esp. Prop 4.1 and Cor 2.2) this-or-next session; then invest in the
Tier-2 `π`/sum infrastructure, because Cor 3.5 is the single result that cleanly
separates "combinatorics (done)" from "analysis (wall)". Prop 5.6 is a good
standalone analytic warm-up that needs no #858 infrastructure.
