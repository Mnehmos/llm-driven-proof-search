/-
Erdős Problem #858 — §5, toward the sharp asymptotic constant c₂: the Abel/partial
summation SPLIT IDENTITY that converts Mertens' first theorem for the primes into the
prime-reciprocal sum (Mertens' second theorem), UNCONDITIONALLY.
(Chojecki 2026, "An exact frontier theorem and the asymptotic constant for
Erdős problem #858", §5 exact-constant development.)

Byte-faithful snapshot of the kernel-verified root theorem from the proofsearch
MCP pipeline.
  problem_version_id  bd1eb88e-e9ed-4e04-9ba5-48a1ce4aec64
  episode_id          9904dff7-8af4-42c5-ac67-dd2dd3fc9b3f
  root_statement_hash 5c3194746d0d7fbf0b3fff3076d09468f4e3d7742e9c8a5930b9580abf24b36b
  outcome             kernel_verified (root_proved)
  toolchain           leanprover/lean4:v4.32.0-rc1
  mathlib             360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56
  import manifest     ["Mathlib.Tactic.Ring", "Mathlib.Tactic.NormNum", "Mathlib"]

────────────────────────────────────────────────────────────────────────────────
CONTENT.  With A(x) := Σ_{p≤x} (log p)/p (Mertens' first theorem for the primes),
Abel/partial summation against the C¹ weight f(t) = 1/log t gives, for every real
x ≥ 2, the EXACT identity

    Σ_{p≤x} 1/p = A(x)/log x + ∫₂ˣ A(t)/(t·log²t) dt.

This is precisely the hypothesis `hSsplit : S = A / L + (J + K)` that the campaign's
conditional bookkeeping theorem `erdos858_mertens2_abel_reduction` had to ASSUME.
It is now discharged with no analytic input beyond the general partial-summation
lemma — no PNT, no Chebyshev lower bound, no Mertens theorem is needed for the
identity itself (those remain the blockers only for evaluating A(x) = log x + O(1)).
Both prime sums are written concretely as filtered sums over `Finset.Icc 1 ⌊·⌋₊`.

────────────────────────────────────────────────────────────────────────────────
TECHNIQUE.  Mathlib's `sum_mul_eq_sub_sub_integral_mul`
(`Mathlib/NumberTheory/AbelSummation.lean`),
    ∑_{k∈Ioc ⌊a⌋ ⌊b⌋} f k · c k
      = f b · (∑_{k∈Icc 0 ⌊b⌋} c k) − f a · (∑_{k∈Icc 0 ⌊a⌋} c k)
        − ∫_{(a,b]} deriv f t · (∑_{k∈Icc 0 ⌊t⌋} c k) dt,
with hypotheses `0 ≤ a`, `a ≤ b`, `∀ t ∈ Icc a b, DifferentiableAt ℝ f t`,
`IntegrableOn (deriv f) (Icc a b)`, instantiated at a = 2, b = x by
  • c(k) = ((log k)/k)·[k prime]   (partial sum over `Icc 0 ⌊t⌋₊` = A(t));
  • f(t) = (log t)⁻¹,  deriv f t = −(t·(log t)²)⁻¹ built from
    `(Real.hasDerivAt_log htne).inv hlogtne` (value `−t⁻¹/(log t)²`, reconciled by
    `ring`), continuity of the derivative via `ContinuousOn.inv₀`, integrability via
    `IntegrableOn.congr_fun` off the continuous `g`.
The structure mirrors the kernel-verified Erdős #647 identity block
(`erdos647_mertens_assembly`, the `hid` step) with the lighter weight `1/log t` in
place of `1/(t log t)`.  Post-Abel bookkeeping:
  • `f x · A(x) = A(x)/log x`               (`(log x)⁻¹ · A = A / log x`, `ring`);
  • `f 2 · A(2) = (log 2)⁻¹ · (log 2 / 2) = 1/2`   (only 2 is prime in `Icc 0 2`);
  • the Abel integral term `−∫ (deriv f)·A` is turned into `+∫ A(t)/(t·log²t) dt` by
    `setIntegral_congr_fun` (pointwise `−g·A = −(A/(t log²t))`) then `integral_neg`;
  • `hAdef` relates the filtered prime sum to `Σ_{Icc 0 ⌊·⌋₊} c` (0 is not prime:
    `Finset.filter_insert` + `if_neg Nat.not_prime_zero`);
  • the `p = 2` term is split off (`hset`, `Finset.sum_insert`) and the two sides are
    reconciled by `linarith`.

Role in the density/constant program: this is the missing UNCONDITIONAL step #54 of
the Mertens-2 chain; combined with the evaluated main integral
`erdos858_mertens2_main_integral` (J = loglog x − loglog 2), the weight/error integral
`erdos858_mertens2_error_integral` (K), and the conditional assembly
`erdos858_mertens2_abel_reduction`, it reduces Mertens' second theorem to the single
remaining analytic input A(x) = log x + O(1).

Lean notes (this pin): the nat-floor subscript in `⌊·⌋₊` is U+208A (subscript PLUS),
distinct from the U+2080 (subscript ZERO) in `ContinuousOn.inv₀` — mixing them up is a
parse error when hand-transporting the proof.  `HasDerivAt.inv` yields the derivative
`−c'/(c x)²`; `−t⁻¹/(log t)² = −(t·(log t)²)⁻¹` is a field identity closed by `ring`.
-/
import Mathlib

namespace Erdos858

/-- Erdős #858, Mertens' second theorem — the UNCONDITIONAL Abel/partial-summation
split identity.  For all real `x ≥ 2`, with `A(t) = Σ_{p≤t} (log p)/p` written as a
filtered prime sum,
`Σ_{p≤x} 1/p = A(x)/log x + ∫₂ˣ A(t)/(t·log²t) dt`.
This discharges the `S = A/L + (J+K)` hypothesis of `erdos858_mertens2_abel_reduction`. -/
theorem erdos858_mertens2_abel_split :
    ∀ x : ℝ, 2 ≤ x →
      (∑ p ∈ Finset.Icc 1 ⌊x⌋₊ with p.Prime, (1 / (p : ℝ)))
        = (∑ p ∈ Finset.Icc 1 ⌊x⌋₊ with p.Prime, (Real.log (p : ℝ) / (p : ℝ))) / Real.log x
          + ∫ t in Set.Ioc (2 : ℝ) x,
              (∑ p ∈ Finset.Icc 1 ⌊t⌋₊ with p.Prime, (Real.log (p : ℝ) / (p : ℝ)))
                / (t * (Real.log t) ^ 2) := by
  intro x hx
  have hlogxpos : 0 < Real.log x := Real.log_pos (by linarith)
  have hxpos : 0 < x := by linarith
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsubset2 : Set.Icc (2 : ℝ) x ⊆ {t : ℝ | t ≠ 0} := by
    intro t ht
    have h1 : (2 : ℝ) ≤ t := (Set.mem_Icc.mp ht).1
    exact ne_of_gt (by linarith)
  set f : ℝ → ℝ := fun t => (Real.log t)⁻¹ with hf_def
  set g : ℝ → ℝ := fun t => -(t * (Real.log t) ^ 2)⁻¹ with hg_def
  set c : ℕ → ℝ := fun k => if k.Prime then Real.log (k : ℝ) / (k : ℝ) else 0 with hc_def
  have hlog2ne : Real.log 2 ≠ 0 := ne_of_gt hlog2pos
  -- derivative of the weight f(t) = 1/log t
  have hderiv : ∀ t ∈ Set.Icc (2 : ℝ) x, HasDerivAt f (g t) t := by
    intro t ht
    have ht2 : (2 : ℝ) ≤ t := (Set.mem_Icc.mp ht).1
    have htpos : (0 : ℝ) < t := by linarith
    have hlogtpos : 0 < Real.log t := Real.log_pos (by linarith)
    have hlogtne : Real.log t ≠ 0 := ne_of_gt hlogtpos
    have htne : t ≠ 0 := ne_of_gt htpos
    have hlog : HasDerivAt Real.log t⁻¹ t := Real.hasDerivAt_log htne
    have h2 : HasDerivAt (fun s : ℝ => (Real.log s)⁻¹) (-t⁻¹ / (Real.log t) ^ 2) t :=
      hlog.inv hlogtne
    have heq2 : -t⁻¹ / (Real.log t) ^ 2 = g t := by rw [hg_def]; ring
    rw [heq2] at h2
    exact h2
  have hf_diff : ∀ t ∈ Set.Icc (2 : ℝ) x, DifferentiableAt ℝ f t :=
    fun t ht => (hderiv t ht).differentiableAt
  have hderiv_eq : Set.EqOn g (deriv f) (Set.Icc (2 : ℝ) x) :=
    fun t ht => (hderiv t ht).deriv.symm
  have hgcont : ContinuousOn g (Set.Icc (2 : ℝ) x) := by
    rw [hg_def]
    apply ContinuousOn.neg
    apply ContinuousOn.inv₀
    · exact continuousOn_id.mul ((Real.continuousOn_log.mono hsubset2).pow 2)
    · intro t ht
      have ht2 : (2 : ℝ) ≤ t := (Set.mem_Icc.mp ht).1
      have htpos : (0 : ℝ) < t := by linarith
      have hlogtpos : 0 < Real.log t := Real.log_pos (by linarith)
      have : (0 : ℝ) < t * (Real.log t) ^ 2 := by positivity
      exact ne_of_gt this
  have hf_int : MeasureTheory.IntegrableOn (deriv f) (Set.Icc (2 : ℝ) x) MeasureTheory.volume := by
    apply MeasureTheory.IntegrableOn.congr_fun (f := g)
    · exact hgcont.integrableOn_Icc
    · exact hderiv_eq
    · exact measurableSet_Icc
  -- A(y) as a filtered prime sum equals the Icc-0 partial sum of c
  have hAdef : ∀ y : ℝ,
      (∑ p ∈ Finset.Icc 1 ⌊y⌋₊ with p.Prime, (Real.log (p : ℝ) / (p : ℝ)))
        = ∑ k ∈ Finset.Icc 0 ⌊y⌋₊, c k := by
    intro y
    have hset0 : (Finset.Icc 0 ⌊y⌋₊).filter (fun k => Nat.Prime k)
        = (Finset.Icc 1 ⌊y⌋₊).filter (fun k => Nat.Prime k) := by
      rw [show Finset.Icc 0 ⌊y⌋₊ = insert 0 (Finset.Icc 1 ⌊y⌋₊) from by
        ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega]
      rw [Finset.filter_insert, if_neg Nat.not_prime_zero]
    simp only [hc_def]
    rw [← Finset.sum_filter, hset0]
  have h2le : 2 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  have habel := sum_mul_eq_sub_sub_integral_mul c (by norm_num : (0 : ℝ) ≤ 2) hx hf_diff hf_int
  have hfloor2 : ⌊(2 : ℝ)⌋₊ = 2 := by norm_num
  rw [hfloor2] at habel
  have hset : (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime
      = insert 2 ((Finset.Ioc 2 ⌊x⌋₊).filter Nat.Prime) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨h1, hkn⟩, hp⟩
      have hk2 : 2 ≤ k := hp.two_le
      rcases eq_or_lt_of_le hk2 with heq | hlt
      · left; exact heq.symm
      · right; exact ⟨⟨hlt, hkn⟩, hp⟩
    · rintro (rfl | ⟨⟨h1, hkn⟩, hp⟩)
      · exact ⟨⟨by norm_num, h2le⟩, Nat.prime_two⟩
      · exact ⟨⟨by omega, hkn⟩, hp⟩
  have hLHS : ∑ k ∈ Finset.Ioc 2 ⌊x⌋₊, f (k : ℝ) * c k
      = (∑ p ∈ Finset.Icc 1 ⌊x⌋₊ with p.Prime, (1 / (p : ℝ))) - 1 / 2 := by
    have hfck : ∀ k ∈ Finset.Ioc 2 ⌊x⌋₊, f (k : ℝ) * c k = (if k.Prime then (1 / (k : ℝ)) else 0) := by
      intro k hk
      rw [hf_def, hc_def]
      by_cases hp : k.Prime
      · simp only [hp, if_true]
        have hkpos : (k : ℝ) ≠ 0 := by
          have hh : 2 < k := (Finset.mem_Ioc.mp hk).1
          have : 0 < k := by omega
          positivity
        have h3 : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (Finset.mem_Ioc.mp hk).1
        have hklog : Real.log (k : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by linarith))
        field_simp
      · simp [hp]
    rw [Finset.sum_congr rfl hfck, ← Finset.sum_filter, hset, Finset.sum_insert (by simp)]
    norm_num
  rw [hLHS] at habel
  have h2sum : ∑ k ∈ Finset.Icc 0 2, c k = Real.log 2 / 2 := by
    simp only [show Finset.Icc 0 2 = {0, 1, 2} by decide]
    rw [hc_def]; norm_num [Nat.prime_two]
  rw [h2sum] at habel
  have hf2 : f 2 * (Real.log 2 / 2) = 1 / 2 := by
    rw [hf_def]; field_simp
  rw [← hAdef x] at habel
  have hintsimp : ∫ t in Set.Ioc (2 : ℝ) x, deriv f t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k
      = ∫ t in Set.Ioc (2 : ℝ) x,
          -((∑ p ∈ Finset.Icc 1 ⌊t⌋₊ with p.Prime, (Real.log (p : ℝ) / (p : ℝ)))
              / (t * (Real.log t) ^ 2)) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    dsimp only
    have ht' : t ∈ Set.Icc (2 : ℝ) x := Set.mem_Icc.mpr ⟨le_of_lt ht.1, ht.2⟩
    rw [← hderiv_eq ht', hg_def, ← hAdef t]
    ring
  rw [hintsimp] at habel
  rw [MeasureTheory.integral_neg] at habel
  rw [hf2] at habel
  have hfx : f x * (∑ p ∈ Finset.Icc 1 ⌊x⌋₊ with p.Prime, (Real.log (p : ℝ) / (p : ℝ)))
      = (∑ p ∈ Finset.Icc 1 ⌊x⌋₊ with p.Prime, (Real.log (p : ℝ) / (p : ℝ))) / Real.log x := by
    simp only [hf_def]; ring
  linarith [habel, hfx]

end Erdos858
