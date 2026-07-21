# Erdős #858 — living campaign folder

**Problem ([erdosproblems.com/858](https://www.erdosproblems.com/858), Erdős 1970):**
for `A ⊆ {1,…,N}` admissible iff no `b = a·t` with `a,b ∈ A` and `P⁻(t) > a`,
how large can `M(N) = max_A Σ_{n∈A} 1/n` be?

**Status on erdosproblems.com: SOLVED** (page last edited 24 April 2026, accessed
2026-07-13). The site records the answer `max_A Σ 1/n = (c + o(1)) log N` with
`c ≈ 0.618…`, attributed to **Chojecki and GPT-5.4 Pro** — the same result as the
`erdos858.pdf` note in this folder (`c₂ = 0.6187712111…`). Crucially, the site
also shows **"Formalised statement? No"**: there is *no* machine-checked
formalization of #858 anywhere yet. This campaign is the first.

**This folder** documents an independent, machine-checked formalization campaign
built from the paper *An exact frontier theorem and the asymptotic constant for
Erdős problem #858*. We kernel-verify the paper's §1–§2 order-theoretic
foundation and its first §4 arithmetic lemma, scope the frontier combinatorics
as infrastructure, and map the analytic wall (with a concrete Mertens foothold
from the sibling erdos-647 campaign).

**These are living documents.** Every "verified" claim is backed by a real Lean 4
kernel verification recorded in this environment; nothing rests on trusting the
AI or the paper. We do not independently re-derive the full `c₂` asymptotic —
that is the analytic wall — so this folder neither endorses nor refutes the
paper's headline theorems; it machine-checks the part now within reach.

## Start here

| file | what it is |
|---|---|
| [whitepaper.md](whitepaper.md) | the full story: problem, the paper's architecture, what we checked, where the wall is |
| [THEOREM-CATALOG.md](THEOREM-CATALOG.md) | every paper item (defs, lemmas, theorems) with formalization status |
| [evidence.md](evidence.md) | machine records: statements, hashes, problem/episode IDs, outcomes |
| [attack-plan.md](attack-plan.md) | ordered next targets (Tier 1 elementary → Tier 3 analytic wall) |
| [credit.md](credit.md) | attribution (Erdős, Chojecki, Bloom, Kinlaw–Pomerance) + honest limits |
| [proof/](proof/) | byte-faithful `.lean` snapshots of the kernel-verified theorems |
| [erdos858.pdf](erdos858.pdf) | the source paper |

## Headline results (kernel-verified 2026-07-13)

The paper's **§1–§2 order-theoretic backbone (plus a concrete `π`), its §1
trivial-bound admissibility, its complete §4 prime–semiprime description
(Lemma 4.5), its §3 frontier-sweep spine (Prop 3.2 + Lemma 3.1), the entire §3
max-closure reduction culminating in the Corollary 3.5 capstone `M(N) = S_N(K)`,
the full Theorem 2.4 subtree-recursion combinatorics (root dichotomy +
child-merge), Remark 2.5 (Bellman form), Prop 4.1 `ν(1)=4`, the full Prop 4.6
(`P_N` + `Q_N`), and — the 2026-07-14 "analytic wall" round — the first §5
results: the two-sided quantitative-Mertens bracket `log 2·loglog x − C ≤
Σ_{p≤x} 1/p ≤ log 4·loglog x + C'` (via a real-valued Chebyshev `ϑ` bridge), the
Prop 5.6 real-analytic core (`α₂ < 1/3`, + continuity + integrand sign), and the
KP threshold `α = 1/(e+1) ∈ (1/4,1/3)`, and the first **Mertens-first-theorem
building blocks** toward `c₂`**, as **one hundred and sixty-four** independent `kernel_verified`
results (`leanprover/lean4:v4.32.0-rc1` + `mathlib@360da6fa`; full records in
[evidence.md](evidence.md)). The first 18 are listed below; #19–#164 (the
max-closure machinery, Bellman, the full Theorem 2.4 recursion, the §5 analytic
layer, the Mertens-1 building blocks, the log-harmonic transfer, and the **complete
§5.3 prime-harmonic transfer** — Lemma 5.3 capstone #141 on a fully kernel-verified
discharge tree #142–#146 with **zero external hypotheses** (the G-modulus discharged by
the clamp-modulus #149, mirroring §5.4's #116), closed in the paper's exact
`∫_s^t G(v)/v dv` notation by the geometric change of variables #147–#148) are in
[evidence.md](evidence.md):

1. **`⪯` is a partial order** (§1) — reflexivity, antisymmetry, transitivity of
   `a ⪯ b := ∃ t, b = a·t ∧ (∀ prime p ∣ t, a < p)`. The Introduction asserts
   it; here it is proved.
   → [proof/Erdos858_PreceqPartialOrder.lean](proof/Erdos858_PreceqPartialOrder.lean)
2. **Lemma 2.1 (sandwich)** — `a⪯n, b⪯n, a<b<n ⇒ a⪯b`.
   → [proof/Erdos858_Lemma21_Sandwich.lean](proof/Erdos858_Lemma21_Sandwich.lean)
3. **Lemma 2.7 core** — for prime `p > a`, any `b` with `a ⪯ b ⪯ a·p` is `a` or
   `a·p` (i.e. `π(a·p) = a`).
   → [proof/Erdos858_Lemma27_PrimeChildCore.lean](proof/Erdos858_Lemma27_PrimeChildCore.lean)
4. **Corollary 2.2** — proper ancestors of `n` are `⪯`-comparable, so `π` and
   the rooted tree are well-defined. This is the corollary that makes the whole
   construction legitimate.
   → [proof/Erdos858_Cor22_AncestorsLinear.lean](proof/Erdos858_Cor22_AncestorsLinear.lean)
5. **Lemma 4.5 core** (§4) — a child's cofactor `t < a³` (upper layer
   `a > N^{1/4}`) with all prime factors `> a` has `Ω(t) ≤ 2`: it is prime or
   semiprime — the `ap`/`apq` dichotomy behind `R_N = P_N + Q_N`.
   → [proof/Erdos858_Lemma45_CofactorPrimeSemiprime.lean](proof/Erdos858_Lemma45_CofactorPrimeSemiprime.lean)
6. **Lemma 4.5 sub-fact** (§4) — `b ⋠ b·q` for a prime `q < b`; specialized to
   `b = a·p` this gives `π(a·p·q) = a`, finishing the prime–semiprime child
   description.
   → [proof/Erdos858_Lemma45_PiApqSubfact.lean](proof/Erdos858_Lemma45_PiApqSubfact.lean)
7. **Trivial lower bound** (§1) — `(√N, N]` is a `⪯`-antichain (`N < a²`,
   `a < b ≤ N` ⇒ `a ⋠ b`), the admissibility behind `M(N) ≥ ½ log N + O(1)`.
   → [proof/Erdos858_TopBlockAntichain.lean](proof/Erdos858_TopBlockAntichain.lean)
8. **Lemma 2.7 full** (§2) — `π(a·p) = a`: existence of the child `a·p` plus
   uniqueness. The complete parent identity.
   → [proof/Erdos858_Lemma27_PiApFull.lean](proof/Erdos858_Lemma27_PiApFull.lean)
9. **`⪯` refines `∣`/`≤` + doubling** (§1–§2) — `a ⪯ b ⇒ a ∣ b`, `a ≤ b`, and a
   proper step gives `2a ≤ b` (so tree depth `≤ log₂ N`).
   → [proof/Erdos858_PreceqRefinesOrder.lean](proof/Erdos858_PreceqRefinesOrder.lean)
10. **Large-prime cofactor** (§1–§2) — a proper `⪯`-multiple of `a` has a prime
    factor `> a`.
    → [proof/Erdos858_CofactorLargePrimeFactor.lean](proof/Erdos858_CofactorLargePrimeFactor.lean)
11. **Lemma 4.5 full dichotomy** (§4) — a child cofactor `t < a³` (primes `> a`)
    is `1`, prime, or semiprime: the explicit `a`/`a·p`/`a·p·q` child forms.
    → [proof/Erdos858_Lemma45_FullDichotomy.lean](proof/Erdos858_Lemma45_FullDichotomy.lean)

*(Results 8–11 were produced in an ultracode multi-agent round — three parallel
subagents plus the orchestrator, all kernel-verified on the first submission.)*

12. **Prop 3.2 single-step** (§3) — `S_N(K+1) = S_N(K) + (C_N(K+1) − 1/(K+1))`,
    the frontier decomposition `A_N(K+1) = (A_N(K) \ {K+1}) ⊍ children(K+1)`.
    → [proof/Erdos858_FrontierSweepStep.lean](proof/Erdos858_FrontierSweepStep.lean)
13. **Prop 3.2 telescoping** (§3) — `s 0 = 1 ∧ s(K+1)=s K+g(K+1) ⇒ s K = 1 + Σ g`.
    → [proof/Erdos858_FrontierSweepTelescope.lean](proof/Erdos858_FrontierSweepTelescope.lean)
14. **Prop 3.2 base** (§3) — `A_N(0) = {1}`, so `S_N(0) = 1`.
    → [proof/Erdos858_FrontierBaseZero.lean](proof/Erdos858_FrontierBaseZero.lean)
15. **Lemma 3.1** (§3) — the frontier `A_N(K)` is a `⪯`-antichain.
    → [proof/Erdos858_FrontierAntichain.lean](proof/Erdos858_FrontierAntichain.lean)

Together, **12 + 13 + 14 give the frontier sweep identity `S_N(K) = 1 + Σ_{a≤K}
q_N(a)` (Proposition 3.2)**. *(Results 12–15 were a second ultracode round —
three parallel subagents plus the orchestrator on the hard Finset decomposition.)*

16. **Concrete `π` instantiation** (§2) — `piFn(n) := max{a<n : a⪯n}` (via
    `Finset.max'`) satisfies all three abstract axioms used in §3. Deliberately
    avoids re-deriving Lemma 2.3's harder non-monotone characterization (a
    naive greedy `π` is provably **wrong** — counterexample `n=99=3·3·11`).
    → [proof/Erdos858_ConcretePiAxioms.lean](proof/Erdos858_ConcretePiAxioms.lean)
17. **Prop 4.1, `ν(1)=4`** (§4) — a genuine kernel-checked instance of the
    paper's one computer-assisted table entry.
    → [proof/Erdos858_Prop41_NuOneEqFour.lean](proof/Erdos858_Prop41_NuOneEqFour.lean)
18. **Prop 4.6, `P_N` monotonicity** (§4) — `0<a≤b ⇒ P_N(a) ≥ P_N(b)` via
    nested prime-sum domain containment.
    → [proof/Erdos858_Prop46_PNMonotone.lean](proof/Erdos858_Prop46_PNMonotone.lean)

*(Results 16–18 were a third ultracode round — the orchestrator built the
concrete `π` [novel `let`-in-statement + `dsimp only` technique], two parallel
subagents proved 17 and 18.)*

## Status, plainly

`M(N) = M_fr(N)` (Thm 1.1) and `c₂ = 0.61877121…` (Thm 1.2) are **not** verified.
What changed: the paper's §1–§2 order-theoretic foundation (with a **real
concrete `π`**), §4 prime–semiprime description (Lemma 4.5), and the **entire §3
max-closure reduction** are machine-checked through the **Corollary 3.5 capstone
`M(N) = S_N(K)`** (evidence #29) — the complete frontier reduction of Theorem 1.1.
The **full Theorem 2.4 subtree recursion** is verified (root dichotomy +
child-merge + value-function `max'` characterization ⟹ `F_N(a)=max(1/a,Σ_b F_N(b))`,
#32/#35/#38), as is the full **Prop 4.6** (`P_N`+`Q_N`). Then, in the
**2026-07-14 "analytic wall" round** (orchestrator + a four-agent hard-frontier
workflow), the §5 analytic layer was breached at its base: the **two-sided
quantitative-Mertens bracket** `log 2·loglog x − C ≤ Σ_{p≤x} 1/p ≤
log 4·loglog x + C'` (a real-valued Chebyshev `ϑ` bridge over Mathlib's
`Chebyshev.theta_ge`/`theta_le_log4_mul_x`; #31 upper is new to the ecosystem,
#34 lower ported from #647), `Σ 1/p → ∞` (#40), the **Prop 5.6 core** (`α₂ < 1/3`,
#30) with continuity (#37) and integrand sign `I(u)≥0` (#39), and the **KP
threshold** `α = 1/(e+1) ∈ (1/4,1/3)` (#36) — and the first **Mertens-first-theorem
building blocks** (`Σ log n = Σ_d Λ(d)⌊N/d⌋ = log N!`, `ψ(N)≤(log4+4)N`; #41–#43) —
**forty-four** kernel-verified results total. The workflow also *diagnosed* the
remaining barrier precisely: the *sharp-constant* Mertens (leading constant exactly
`1`, needed for `c₂`) is **not assembled in this Mathlib pin** — no Mertens first or
second theorem, no PNT, no `θ(x)=x+o(x)` — but its building blocks are now verified
here, so the campaign is assembling it block by block. Also
open: the full Prop 5.6 monotonicity on `[1/4,1/2]` (a heavy 3-term Leibniz
assembly, exact API mapped) and the full `ν(a)` table (`a=2..19`, needs a
computable reformulation of the Prop-valued `⪯`) — see [attack-plan.md](attack-plan.md).
