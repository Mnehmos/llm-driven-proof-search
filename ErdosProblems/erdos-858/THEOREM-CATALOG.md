# Erdős #858 — theorem catalog (paper → formalization status)

Complete inventory of every definition, lemma, proposition, and theorem in
Chojecki (2026), *An exact frontier theorem and the asymptotic constant for
Erdős problem #858*, with its current formalization status in this environment.

Status legend:
- ✅ **verified** — kernel_verified in a tracked episode (see [evidence.md](evidence.md))
- 🟡 **tractable** — elementary/finite; formalizable with the current toolchain, next targets
- 🧱 **wall** — analytic; beyond current Mathlib out-of-the-box (multi-session)
- 📐 **infra** — needs supporting definitions (π, frontier sums) formalized first

| # | Paper item | Content | Status |
|---|---|---|---|
| — | §1 relation `⪯` | `a ⪯ b ⟺ b = a·t, P⁻(t) > a`; admissible = ⪯-antichain | ✅ (poset) |
| — | §1 partial order | `⪯` reflexive, antisymmetric, transitive | ✅ **verified** |
| — | §1 trivial bound | `M(N) ≥ ½ log N + O(1)`: `(√N, N]` is an antichain | ✅ **verified (antichain)** |
| — | §1–§2 order facts | `⪯ ⊆ (∣, ≤)`; proper step doubles (`a⪯b, a<b ⇒ 2a≤b`) | ✅ **verified** |
| — | §1–§2 large prime | proper `⪯`-multiple of `a` has a prime factor `> a` | ✅ **verified** |
| — | §2 concrete `π` | `π(n) := max{a<n:a⪯n}` satisfies the 3 abstract axioms used in §3 | ✅ **verified** |
| 1.1 | **exact frontier thm** | `M(N) = M_fr(N)` for all `N ≥ 2` | ✅/🧱 **conditional assembly verified** (#73: sign thm ⨾ Cor 3.5 + Prop 3.2 ⟹ `M(N)=M_fr(N)`); sign thm itself now reduced — its initial-segment core (#76) + Cor 4.4 (#75) + Prop 4.6 (verified) leave **only Lemma 4.3** (`Σ_{a<p≤a³}1/p>1`) as the single open analytic input — and #78 reduces even that to one explicit error-difference inequality `\|Ea3−Ea\| < log 3 − 1` (`M` cancels), the lone Kinlaw–Pomerance constant absent from the pin |
| 1.2 | **asymptotic law** | `M(N) = (c₂+o(1)) log N`, `K*(N) = N^{α₂+o(1)}` | 🧱 |
| 2.1 | sandwich lemma | `a⪯n, b⪯n, a<b<n ⇒ a⪯b` | ✅ **verified** |
| 2.2 | ancestors linear | proper ancestors of `n` linearly ordered ⇒ `π(n)` defined | ✅ **verified** |
| 2.3 | `π` prefix form | `π(n) = P_k`, largest `k` with `p_{k+1} > P_k` | 🟡 |
| 2.4 | subtree recursion | `F_N(a) = max(1/a, Σ_{b∈ch} F_N(b))` (exact DP) | ✅ **FULLY verified** — root dichotomy (`{a}` or avoids `a`) + child-merge (disjoint incomparable antichains → additive weight) + value-function `max'` characterization (`F_N(a) = max(1/a, C)`) |
| 2.5 | Bellman form | `V_N(a) = max(1, Σ (a/b) V_N(b))` | ✅ **verified** (algebraic rescaling `V=a·F`) |
| 2.7 | prime child lemma | `π(a·p) = a` for prime `p > a`; `C_N(a) ≥ (1/a)Σ 1/p` | ✅ **verified (full: π(a·p)=a)** |
| 3.1 | frontier antichain | `A_N(K)` is a `⪯`-antichain | ✅ **verified** |
| 3.2 | frontier sweep | `S_N(K) − S_N(K−1) = q_N(K)`; `S_N(K) = 1 + Σ q_N` | ✅ **verified (step + telescope + base)** |
| 3.3 | stopping antichain | max-weight antichain has form `∂D`, `D` continuation set | ✅ **verified (exchange-free: any antichain B ⊆ ∂D_B, D_B={a: no ⪯-ancestor in B})** |
| 3.4 | max-closure identity | `Σ_{∂D} 1/n = 1 + Σ_{D} q_N`; `M(N) = 1 + max_D Σ q_N` | ✅ **verified identity** (+ ∂D antichain); `M(N)=1+max_D` consequence needs the `M(N)`-as-max glue |
| 3.5 | initial-segment ⇒ frontier | `q_N>0` on `[1,K]`, `≤0` after ⇒ `M(N)=S_N(K)` | ✅ **verified** — `M(N)=S_N(K)` as a max-over-antichains characterization (`cor35_max_eq`), assembling the `≤` direction (`cor35_le_direction`) + `≥` witness (`A_N(K)=∂[1,K]` via Lemma 3.1/Prop 3.2). The whole §3 max-closure reduction is machine-checked. |
| 4.1 | small thresholds `ν(a)` | exact rational table `ν(1..19)` (computer-assisted) | ✅/🟡 **verified `ν(1)=4`; `ν(2..19)` not attempted (values up to 80807, likely infeasible via Lean kernel evaluation — see attack-plan.md)** |
| 4.3 | low-layer prime bound | `Σ_{a<p≤a³} 1/p > 1` for `a ≥ 20` (Mertens + Kinlaw–Pomerance) | 🧱/✅ **conditional reduction verified (#78)**: `M` cancels (`loglog(a³)−loglog(a)=log 3`), so the whole statement reduces to the single explicit error-difference bound `\|Ea3−Ea\| < log 3 − 1 ≈ 0.0986`; that inequality (the Kinlaw–Pomerance interval-Mertens constants) is the sole piece absent from the pin |
| 4.4 | low-layer corollary | `20 ≤ a ≤ N^{1/4} ⇒ R_N(a) > 1` | ✅/🧱 **composition verified (#75)**: `Σ_{a<p≤a³}1/p>1` ⨾ interval-monotonicity ⨾ prime-child bound ⟹ `R_N(a)>1`; sole open input = 4.3 |
| 4.5 | prime–semiprime | children of `a > N^{1/4}` are `ap` or `apq`; `R_N=P_N+Q_N` | ✅ **verified (full: Ω≤2 + dichotomy + π(apq)=a)** |
| 4.6 | upper-layer monotone | `a ↦ R_N(a)` nonincreasing on `a > N^{1/4}` | ✅ **verified — both `P_N` and `Q_N` halves** (nested-interval subset sums); `R_N = P_N + Q_N` nonincreasing |
| 4.7 | **sign theorem** | `{a : R_N(a) > 1}` is an initial segment | ✅/🧱 **initial-segment core verified (#76)**: downward-closure from `R_N>1` on `[1,L]` (4.1+4.4=#75) + `R_N` nonincreasing on `[L,∞)` (4.6=verified); sole open input = 4.3 |
| 4.8 | exact frontier again | `M(N) = M_fr(N)` (= Thm 1.1) | ✅/🧱 **conditional assembly (#73)**; ⇐ sign thm (open) |
| 5.1 | frontier identity | `S_N(K)` closed form via `H_m`, `P_N`, `Q_N` | 📐 |
| — | ϑ real bridge | `∀ t≥2, (t−1)log2 − log(t+2) − 2√t·log t ≤ θ(t)` | ✅ **verified** (ported from #647; foundation) |
| 5.2 | Mertens on intervals | `Σ_{x<p≤y} 1/p = log(log y/log x) + o(1)`, `N^β≤x≤y≤N` | ✅/🧱 **two-sided Θ(loglog x) bracket verified** (upper `≤ log4·loglog x + C` NEW; lower `≥ log2·loglog x − C` ported from #647); sharp leading constant 1 (exact interval asymptotic, needed for `c₂`) still 🧱 |
| — | α threshold | `α := 1/(e+1) = 0.2689…` (Kinlaw–Pomerance) | ✅ **localized** `1/4 < α < 1/3` |
| 5.3 | prime-harmonic sums | Riemann-sum limit of `Σ G(u, log p/log N)/p` | 🧱 |
| 5.4 | harmonic sums | `(1/log N) Σ f(log a/log N)/a → ∫ f` | 🧱→🔨 **foundations built** (from Mathlib's harmonic bounds + Euler–Mascheroni): #86 interval-sum weight `Σ_{m<a≤n}1/a=log(n/m)+O(1)`, #87 `harmonic n/log n→1`, #88 block weight `harmonic(2n)−harmonic(n)→log2`; remaining: general `N^s..N^t` block (rpow/floor) + step-function approx — all elementary, no PNT |
| 5.5 | `P_N+Q_N → Φ(u)` | uniform prime–semiprime asymptotics | 🧱 |
| 5.6 | `Φ` monotone | `Φ` strictly decreasing; unique `α₂` root of `Φ=1` | ✅/🧱 **core + continuity + integrand-sign + BOTH Leibniz halves verified** (prime term strictly antitone & `Φ<1` on `[1/3,1/2]` ⟹ `α₂<1/3`; `ContinuousOn`; `I(u)≥0`; endpoint-derivative #44 + interior parameter-derivative #55 — the latter with *no* blocking hypothesis on `[a,b]⊂(0,1/2)`); **full `[1/4,1/2]` monotonicity capstone verified** (`strictAntiOn_of_hasDerivWithinAt_neg`, conditional on the verified Leibniz data + `I'≤0`); with `Φ(1/4)≥log 3>1>log 2=Φ(1/3)` ⟹ unique root `α₂∈(1/4,1/3)`; **numerically bracketed `α₂∈(0.26,0.30)`** via the reusable Φ-value squeeze (#79) + `Φ(13/50)>1` (#80) + `Φ(3/10)<1` (#81, using the I-upper bound #74); **I(u) two-sided bracketed** (#74 upper + #83 lower, midpoint-split); **c₂ now two-sided bracketed `[0.610, 0.633]`** around the true 0.6187712… via EXACT FTC evaluation of the density integral (#84 `∫_{1/3}^{1/2}(1−Φ)=1/6−(5/3)log2+log3≈0.110` ⟹ c₂≥0.610; #85 upper piece ⟹ c₂≤0.633; #82 was the first step c₂≥0.551) — no PNT, demonstrating the c₂ *value* is elementary-computable |
| — | Σ1/p diverges | `Σ_{p≤x} 1/p → ∞` | ✅ **verified** (qualitative floor; `not_summable_one_div_on_primes`) |
| — | Mertens 1 & 2 | Mertens' first & second theorems (toward `c₂`) | ✅ **assembled from verified blocks**: Λ-sum `Σ_{d≤N} Λ(d)/d = log N + O(1)` (blocks: double-count, `=log N!`, `ψ≤(log4+4)N`, Stirling lower/upper, fractional-part) → prime sum `Σ_{p≤N} log p/p = log N + O(1)` (via prime-power split) → Mertens-2 Abel reduction `Σ 1/p = loglog x + O(1)` — with the two Mertens-2 **interval integrals now verified** (`∫1/(t log t)=loglog x−loglog 2`, `∫1/(t log²t)≤1/log 2`). Genuine remaining gaps (both isolated): prime-power tail *constant* `T≤1` (series convergence) + the Abel-summation *split identity* (partial summation) 🧱 |
| 5.7 | prime-only ramp | `S_N(K)` strictly increasing for `K ≤ N^{α−ε}` | 🧱 |
| 5.8 | frontier asymptotic law | `K*(N)=N^{α₂+o(1)}`, `M(N)=(c₂+o(1))log N` | 🧱 |
| 6.1 | Bellman threshold policy | frontier policy weight `G_{N,K}(1) = S_N(K)` | ✅ **verified** (#72: threshold policy = subtree optimum by tree-induction ⟹ `M(N)=S_N(K)=M_fr(N)`) |
| 6.2 | eventual continuation | Bellman continuation set is an initial interval (large `N`) | 🧱 |
| 6.3 | analytic eventual frontier | `M(N) = M_fr(N)` for large `N`, no computer aid | ✅/🧱 **conditional assembly (#73)**; ⇐ sign thm (open) |
| 7 | sample exact values | `M(10^k)` table, `k=2..7` | 🟡 (finite DP) |

## The single computer-assisted ingredient

Per the paper (Remark 4.2), **Proposition 4.1** (the `ν(a)` table for `a ≤ 19`)
is the *only* computer-assisted step; everything past `a ≤ 19` is analytic.
We verified `ν(1)=4` exactly by hand-scoped small-range enumeration
(`n∈{2,3,4}`). The full table's larger entries (`ν(19)=80807`, etc.) are
**honestly not attempted**: our `⪯` relation is Prop-valued
(`∃t,∀p,...`), decidable only via `Classical.decPred` (proof-theoretic, not
computable), so naive `decide`/`native_decide` evaluation over ranges up to
tens of thousands is not a realistic path without a substantially larger
decidability-engineering effort (a computable reformulation via `Nat.minFac`,
plus proving it equivalent to `⪯`) — see [attack-plan.md](attack-plan.md).

## Verified vs. wall, in one line

The **entire §1–§2 order-theoretic foundation** (`⪯` is a poset; `⪯ ⊆ (∣,≤)`;
proper steps double; ancestors are linearly ordered so `π` and the rooted tree
exist; `π(a·p)=a` in full; **plus a genuine concrete `π` instantiation**
satisfying all abstract axioms used in §3) is now machine-checked, **plus the
§1 trivial-bound admissibility (`(√N,N]` antichain), the complete §4
prime–semiprime description (Lemma 4.5: `Ω(t) ≤ 2`, the `1`/prime/semiprime
dichotomy, and `π(a·p·q)=a`), the §3 frontier-sweep spine (Lemma 3.1 antichain
+ Prop 3.2 `S_N(K) = 1 + Σ_{a≤K} q_N(a)` via base + single-step +
telescoping), a verified instance of Prop 4.1 (`ν(1)=4`), the `P_N` half of
Prop 4.6, **the entire §3 max-closure reduction machinery (Prop 3.4 identity,
∂D antichain, the Cor 3.5 optimization inequality, `[1,K]` downward-closed, and
the exchange-free Lemma 3.3 stopping-set construction), and Remark 2.5 (Bellman
form)** — **seventy-three kernel-verified theorems total**. This includes the
**complete §3 max-closure reduction culminating in the Corollary 3.5 capstone
`M(N) = S_N(K)`** (the frontier reduction of Theorem 1.1), the **fully verified
Theorem 2.4 subtree recursion** (root dichotomy + child-merge + value-function
`max'` characterization ⟹ `F_N(a) = max(1/a, Σ_b F_N(b))`), the full
**Proposition 4.6** (`P_N` + `Q_N`), and — the 2026-07-14 "analytic wall" round
(orchestrator + a four-agent hard-frontier workflow) — the **§5 analytic layer's
first kernel-verified results**: the two-sided quantitative-Mertens bracket
`log 2·loglog x − C ≤ Σ_{p≤x} 1/p ≤ log 4·loglog x + C'` (via the real-valued
Chebyshev `ϑ` bridge over Mathlib's `Chebyshev.theta_ge`/`theta_le_log4_mul_x`),
`Σ 1/p → ∞`, the **Proposition 5.6** real-analytic core (`Φ` strictly decreasing
and `< 1` on `[1/3,1/2]`, so `α₂ < 1/3`) + continuity on `[1/3,1/2]` + the
semiprime-integral sign `I(u) ≥ 0`, and the KP threshold `α = 1/(e+1) ∈ (1/4,1/3)`.

The **remaining wall (🧱)** is now sharply diagnosed (workflow scout verdict): the
*sharp-constant* Mertens — leading constant exactly `1`, the exact interval
asymptotic of Lemma 5.2 that the precise `c₂` requires — is **not reachable in
this Mathlib pin**: there is **no Mertens first or second theorem** (only the
unrelated Dedekind–Mertens polynomial lemma), **no PNT**, and **no `θ(x)=x+o(x)`**;
the sharp constant descends from Mertens' *first* theorem, whose Stirling +
`Σ Λ(d)⌊x/d⌋` + `ψ(x)=O(x)` assembly Mathlib has not built — though its concrete
**building blocks are now kernel-verified here** (`Σ log n = Σ_d Λ(d)⌊N/d⌋ = log(N!)`,
`ψ(N) ≤ (log 4+4)N`; #41–#43), so the assembly is advancing block by block. Also open: the full
Prop 5.6 monotonicity on `[1/4,1/2]` (a hand-assembled 3-term Leibniz derivative —
API mapped: FTC endpoints + `ParametricIntervalIntegral` dominated convergence;
heavy, no turnkey lemma); the §4 sign theorem (Lemma 4.3, needs the sharp Mertens);
the full `ν(a)` table (`⪯` not `decide`-able without a `Nat.minFac` reformulation);
and the §7 sample values (`M(N)`/`F_N` computed).
