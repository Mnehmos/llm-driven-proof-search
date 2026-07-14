/-
Erdős Problem #858 — §5, toward the sharp asymptotic constant c₂: the Abel/partial
summation step that converts the prime-weighted-log sum into the prime-reciprocal
sum (Mertens' second theorem, conditional bookkeeping).
(Chojecki 2026, "An exact frontier theorem and the asymptotic constant for
Erdős problem #858", §5 exact-constant development.)

Byte-faithful snapshot of the kernel-verified root theorem from the proofsearch
MCP pipeline.
  problem_version_id  986aa6d2-94cc-4240-9c9b-fbbe521c9524
  episode_id          f1098ec9-9267-4ffa-a06b-8cc14112b8a7
  root_statement_hash 78b024362a650967d62fc36d9c36ad181e74ec7662b1bdbe599f955f31884a35
  outcome             kernel_verified (root_proved)
  toolchain           leanprover/lean4:v4.32.0-rc1
  mathlib             360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56
  import manifest     ["Mathlib.Tactic.Ring", "Mathlib.Tactic.NormNum", "Mathlib"]

────────────────────────────────────────────────────────────────────────────────
CONTENT.  The sharp constant c₂ of #858 is governed by Mertens' second theorem
Σ_{p≤x} 1/p = loglog x + M + o(1) (leading coefficient exactly 1). The classical
final analytic step starts from Mertens' first theorem for the primes,
    A(x) := Σ_{p≤x} (log p)/p = log x + O(1),
and applies Abel/partial summation with the weight 1/log:
    Σ_{p≤x} 1/p = A(x)/log x + ∫₂ˣ A(t)/(t log²t) dt.
Splitting A(t) = log t + r(t) with |r| ≤ C in the integral,
    ∫₂ˣ A(t)/(t log²t) dt = ∫₂ˣ 1/(t log t) dt + ∫₂ˣ r(t)/(t log²t) dt
                          = (loglog x − loglog 2) + O(1),
while A(x)/log x = 1 + r(x)/log x.

This theorem is the CONDITIONAL bookkeeping that isolates all analytic content
into hypotheses and proves the assembly.  Writing L = log x (≥ log 2 for x ≥ 2),
the hypotheses are:
  • A = L + r,  |r| ≤ C          — Mertens' first theorem A(x) = log x + O(1);
  • S = A/L + (J + K)            — the Abel-summation split (S = Σ_{p≤x} 1/p, J the
                                   main integral, K the error integral);
  • J = log L − log(log 2)       — the evaluated main integral
                                   ∫₂ˣ 1/(t log t) dt = loglog x − loglog 2;
  • |K| ≤ C'                     — the error integral ∫₂ˣ r(t)/(t log²t) dt = O(1).
Conclusion: the explicit two-sided bound
  |S − log L| ≤ |1 − log(log 2)| + C/log 2 + C',
i.e. Σ_{p≤x} 1/p = loglog x + O(1) with an explicit constant — the packaging that
Mertens' second theorem sharpens to the exact leading coefficient 1 and constant M.

It complements the campaign's kernel-verified Mertens-first pieces:
`erdos858_mertens1_lower_assembly` (Σ Λ(d)/d ≥ log N − 1) and
`erdos858_mertens1_two_sided` (Σ Λ(d)/d = log N + O(1)).

────────────────────────────────────────────────────────────────────────────────
ABEL-SUMMATION SCOUT (what the pin provides).  The available Abel-summation
infrastructure is `sum_mul_eq_sub_sub_integral_mul` in
`Mathlib/NumberTheory/AbelSummation.lean`:
    ∑_{k∈Ioc ⌊a⌋ ⌊b⌋} f k · c k
      = f b · (∑_{k∈Icc 0 ⌊b⌋} c k) − f a · (∑_{k∈Icc 0 ⌊a⌋} c k)
        − ∫_{(a,b]} deriv f t · (∑_{k∈Icc 0 ⌊t⌋} c k) dt,
hypotheses `0 ≤ a`, `a ≤ b`, `∀ t ∈ Icc a b, DifferentiableAt ℝ f t`,
`IntegrableOn (deriv f) (Icc a b)`.  Specializations `sum_mul_eq_sub_integral_mul`
(a = 0), `…_mul₀` (c 0 = 0), `…_mul₁` (c 0 = c 1 = 0), the `Nat`-endpoint primed
versions, the limit forms `tendsto_sum_mul_atTop_nhds_one_sub_integral{,₀}`, and
`summable_mul_of_bigO_atTop{,'}` are all present.  erdos-647 instantiated it with
c(k) = (log k)·[k prime] (partial sum = Chebyshev.theta) and f(t) = 1/(t log t) to
get the θ-based identity; the present Mertens-II weight instead takes
c(k) = ((log k)/k)·[k prime] (partial sum = A) and f(t) = 1/log t.

BLOCKER for the UNCONDITIONAL sharp result (leading constant exactly 1 / the value
M).  The pin has no `PrimeNumberTheorem` module, no θ(x) = x + o(x), no Chebyshev
lower bound (an explicit TODO in `Mathlib/NumberTheory/Chebyshev.lean`), and no
Mertens first/second theorem.  Only Chebyshev UPPER bounds (θ x ≤ log 4 · x) and
the Abel-summation lemma above exist.  Consequently the two analytic inputs
    A(x) = log x + O(1)  and  ∫₂ˣ r(t)/(t log²t) dt = O(1)  (|K| ≤ C')
cannot be discharged unconditionally in-pin and are taken as hypotheses here; the
theorem proves exactly the bookkeeping that, given them, yields Σ 1/p = loglog x +
O(1).  (Divergence of Σ 1/p → +∞ IS reachable unconditionally, recorded in
`erdos858_prime_reciprocal_diverges`, but not the sharp constant.)

Lean notes (this pin): `abs_add` is not an identifier — the triangle inequality is
done by `rw [abs_le]` componentwise + `le_abs_self`/`neg_abs_le` + `linarith`. The
cross-multiplication lemma is `div_le_div_iff₀` (a/b ≤ c/d ↔ a·d ≤ c·b), not
`div_le_div_iff`. `positivity` proves `0 < Real.log 2` (numeric-literal extension),
but a `gcongr` on `C/L ≤ C/log 2` emits an undischargeable `0 ≤ C` side goal for
the free variable C, so cross-multiply + `nlinarith` is the robust route.
-/
import Mathlib

namespace Erdos858

/-- Erdős #858, Mertens' second theorem — conditional Abel-summation bookkeeping.
Given the Abel split `S = A/L + (J + K)`, Mertens' first theorem `A = L + r` with
`|r| ≤ C`, the evaluated main integral `J = log L − log(log 2)`, the error-integral
bound `|K| ≤ C'`, and `log 2 ≤ L` (i.e. `x ≥ 2`), the prime-reciprocal sum
`S := Σ_{p≤x} 1/p` satisfies the explicit two-sided bound
`|S − log L| ≤ |1 − log(log 2)| + C/log 2 + C'`, i.e. `Σ_{p≤x} 1/p = loglog x + O(1)`. -/
theorem erdos858_mertens2_abel_reduction :
    ∀ (S A L J K r C C' : ℝ),
      Real.log 2 ≤ L →
      A = L + r →
      |r| ≤ C →
      S = A / L + (J + K) →
      J = Real.log L - Real.log (Real.log 2) →
      |K| ≤ C' →
      |S - Real.log L| ≤ |1 - Real.log (Real.log 2)| + C / Real.log 2 + C' := by
  intro S A L J K r C C' hL hA hrC hSsplit hJval hKbound
  have hL2pos : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hLpos : 0 < L := lt_of_lt_of_le hL2pos hL
  have hLne : L ≠ 0 := ne_of_gt hLpos
  have hCnn : 0 ≤ C := le_trans (abs_nonneg r) hrC
  have hAL : A / L = 1 + r / L := by rw [hA, add_div, div_self hLne]
  have hrLbound : |r / L| ≤ C / Real.log 2 := by
    rw [abs_div, abs_of_pos hLpos, div_le_div_iff₀ hLpos hL2pos]
    nlinarith [hrC, hL, hL2pos, hCnn, abs_nonneg r]
  have hexpr : S - Real.log L = (1 - Real.log (Real.log 2)) + r / L + K := by
    rw [hSsplit, hAL, hJval]; ring
  rw [abs_le] at hrLbound hKbound
  have hb1 := le_abs_self (1 - Real.log (Real.log 2))
  have hb2 := neg_abs_le (1 - Real.log (Real.log 2))
  rw [hexpr, abs_le]
  constructor
  · linarith [hrLbound.1, hrLbound.2, hKbound.1, hKbound.2, hb1, hb2]
  · linarith [hrLbound.1, hrLbound.2, hKbound.1, hKbound.2, hb1, hb2]

end Erdos858
