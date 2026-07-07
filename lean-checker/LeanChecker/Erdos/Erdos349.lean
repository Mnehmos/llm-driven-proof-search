import Mathlib

/-!
# Erdős Problem 349 — the integer-characterization cluster (COMPLETE)

Seven kernel-verified proofs of `research solved` statements from
[google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
`FormalConjectures/ErdosProblems/349.lean`, all of which carry a `sorry` upstream
plus a `formal_proof using formal_conjectures` link to an external fork
(cepadugato/formal-conjectures, branch `erdos-349-integer-characterization-proof`).

Six of these are the corpus's own dependency chain toward `integer_isGoodPair_iff`
(the full characterization of which integer `(t, α)` pairs make `⌊tαⁿ⌋`
additively complete: only `(1, 2)`). The corpus docblock for that theorem names
its four assembly pieces: `(1,2)` is good, `α ≤ 1` fails, `2 < α` fails, integer
`t ≥ 2` fails — this file has all four
(`one_two_isGoodPair`, `alpha_le_one_not_isGoodPair`,
`alpha_gt_two_not_isGoodPair`, `int_coeff_ge_two_not_isGoodPair`), plus one
lemma those construction pieces depend on (`exists_finset_sum_two_pow`), plus
one extra result outside the four (`dyadic_two_isGoodPair`, showing
`(1/2^k, 2)` is also good for every `k`, not needed by `integer_isGoodPair_iff`
since `1/2^k` isn't an integer for `k ≥ 1`), **plus `integer_isGoodPair_iff`
itself**, assembling all four pieces via case split into the full `Iff`.

This is a real, complete, already-known theorem (proved by the corpus's
external contributors; the `formal_proof` link above), independently
reproduced end-to-end through this repository's own kernel-gated pipeline.
It settles the *integer* sub-case of Erdős #349 — Erdős #349 itself, for
general real `(t, α)`, remains open.

Each statement below is written with the corpus's `IsGoodPair`/`IsAddComplete`/
`subsetSums` abbreviations inlined (all specialize to `M = ℤ`, since `⌊·⌋ : ℝ → ℤ`
fixes the codomain) — this is exactly the text registered with the tracked
benchmark pipeline, so the hash pinned there matches this file verbatim.
-/

namespace LeanChecker.Erdos349

/-- **Binary expansion.** Every natural number `k` is a sum of distinct powers of
two. Mathlib already has this in sharper, bijective form
(`Finset.sum_toFinset_bitIndices_two_pow`, built for the Kruskal–Katona
`Finset.Colex` development) — the existential is one line. -/
theorem exists_finset_sum_two_pow (k : ℕ) : ∃ E : Finset ℕ, k = ∑ i ∈ E, 2 ^ i :=
  ⟨k.bitIndices.toFinset, (Finset.sum_toFinset_bitIndices_two_pow k).symm⟩

/-- **Integer `t ≥ 2` fails.** For any integer `t ≥ 2` and any integer `α`, `(t, α)`
is not a good pair: past a large enough threshold, no subset sum of
`{⌊tαⁿ⌋}` can be `≡ 1 (mod t)`, but the threshold itself always is. -/
theorem int_coeff_ge_two_not_isGoodPair :
    ∀ (t : ℤ), 2 ≤ t → ∀ (α : ℤ),
    ¬ (∀ᶠ k in Filter.atTop, k ∈ {n : ℤ | ∃ B : Finset ℤ, ↑B ⊆ Set.range (fun n : ℕ ↦ ⌊(t:ℝ) * (α:ℝ) ^ n⌋) ∧ n = ∑ i ∈ B, i}) := by
  intro t ht α h
  rw [Filter.eventually_atTop] at h
  obtain ⟨N, hN⟩ := h
  set k : ℤ := t * (N.natAbs + 1) + 1 with hkdef
  have hNk : N ≤ k := by
    have h1 : N ≤ (N.natAbs : ℤ) := Int.le_natAbs
    have h2 : (0:ℤ) ≤ N.natAbs := Int.natCast_nonneg N.natAbs
    nlinarith
  have hkt : ¬ (t ∣ k) := by
    rintro ⟨c, hc⟩
    have h1 : t ∣ (1:ℤ) := ⟨c - (N.natAbs + 1), by linarith [hc]⟩
    have := Int.le_of_dvd one_pos h1
    omega
  obtain ⟨B, hBsub, hBeq⟩ := hN k hNk
  apply hkt
  rw [hBeq]
  apply Finset.dvd_sum
  intro i hi
  obtain ⟨n, hn⟩ := hBsub hi
  simp only at hn
  rw [← hn]
  have heq : (t:ℝ) * (α:ℝ)^n = ((t * α^n : ℤ) : ℝ) := by push_cast; ring
  rw [heq, Int.floor_intCast]
  exact ⟨α^n, rfl⟩

/-- **`α ≤ 1` fails.** For any `t > 0` and `0 < α ≤ 1`, `(t, α)` is not a good
pair: every term `⌊tαⁿ⌋` lies in the fixed finite window `[0, ⌊t⌋]`, so every
subset sum is bounded by a constant, and no large integer can be reached. -/
theorem alpha_le_one_not_isGoodPair :
    ∀ (t : ℝ), 0 < t → ∀ (α : ℝ), 0 < α → α ≤ 1 →
    ¬ (∀ᶠ k in Filter.atTop, k ∈ {n : ℤ | ∃ B : Finset ℤ, ↑B ⊆ Set.range (fun n : ℕ ↦ ⌊t * α ^ n⌋) ∧ n = ∑ i ∈ B, i}) := by
  intro t ht α hα0 hα1 h
  rw [Filter.eventually_atTop] at h
  obtain ⟨N, hN⟩ := h
  have hrange : Set.range (fun n : ℕ ↦ ⌊t * α ^ n⌋) ⊆ ↑(Finset.Icc (0:ℤ) ⌊t⌋) := by
    rintro _ ⟨n, rfl⟩
    simp only [Finset.coe_Icc, Set.mem_Icc]
    have hpow_pos : 0 < α ^ n := pow_pos hα0 n
    have hpow_le : α ^ n ≤ 1 := pow_le_one₀ hα0.le hα1
    have hle : t * α ^ n ≤ t := by nlinarith
    have hpos : 0 < t * α ^ n := by positivity
    exact ⟨Int.floor_nonneg.mpr hpos.le, Int.floor_le_floor hle⟩
  set C : ℤ := ∑ i ∈ Finset.Icc (0:ℤ) ⌊t⌋, i with hCdef
  have hbound : ∀ k ∈ {n : ℤ | ∃ B : Finset ℤ, ↑B ⊆ Set.range (fun n : ℕ ↦ ⌊t * α ^ n⌋) ∧ n = ∑ i ∈ B, i}, k ≤ C := by
    rintro k ⟨B, hBsub, rfl⟩
    have hBsub' : B ⊆ Finset.Icc (0:ℤ) ⌊t⌋ := by
      intro x hx
      have hxr := hBsub hx
      have := hrange hxr
      simpa using this
    exact Finset.sum_le_sum_of_subset_of_nonneg hBsub' (fun i hi _ => by simpa using (Finset.mem_Icc.mp hi).1)
  have hk := hN (max N (C+1)) (le_max_left _ _)
  have := hbound _ hk
  have hge : C + 1 ≤ max N (C+1) := le_max_right _ _
  omega

/-- **The pair `(1, 2)` is good.** The powers of two `⌊1·2ⁿ⌋ = 2ⁿ` are additively
complete by the binary-expansion theorem above. -/
theorem one_two_isGoodPair :
    ∀ᶠ k in Filter.atTop, k ∈ {n : ℤ | ∃ B : Finset ℤ, ↑B ⊆ Set.range (fun n : ℕ ↦ ⌊(1:ℝ) * (2:ℝ) ^ n⌋) ∧ n = ∑ i ∈ B, i} := by
  rw [Filter.eventually_atTop]
  refine ⟨0, fun k hk => ?_⟩
  set E := k.toNat.bitIndices.toFinset with hEdef
  have hE : k.toNat = ∑ i ∈ E, 2 ^ i := (Finset.sum_toFinset_bitIndices_two_pow k.toNat).symm
  refine ⟨E.image (fun i => (2:ℤ)^i), ?_, ?_⟩
  · rintro x hx
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx
    obtain ⟨i, _, rfl⟩ := hx
    refine ⟨i, ?_⟩
    show ⌊(1:ℝ) * (2:ℝ)^i⌋ = 2^i
    have hc : (1:ℝ) * (2:ℝ)^i = ((2^i : ℤ) : ℝ) := by push_cast; ring
    rw [hc, Int.floor_intCast]
  · have hinj : Function.Injective (fun i : ℕ => (2:ℤ)^i) := by
      intro a b hab
      simp only at hab
      have : (2:ℕ)^a = (2:ℕ)^b := by exact_mod_cast hab
      exact Nat.pow_right_injective (le_refl 2) this
    rw [Finset.sum_image (fun x _ y _ h => hinj h)]
    have hk' : k = (k.toNat : ℤ) := (Int.toNat_of_nonneg hk).symm
    rw [hk']
    exact_mod_cast hE

/-- **The dyadic fiber at `α = 2`.** For every `k`, `(1/2^k, 2)` is good: at
index `n = m + k` the term is exactly `2^m`, so the range still contains every
power of two — already additively complete. (Not one of `integer_isGoodPair_iff`'s
four assembly pieces, since `1/2^k` isn't an integer for `k ≥ 1`; a standalone
extra result about the same `α = 2` fiber.) -/
theorem dyadic_two_isGoodPair :
    ∀ (k : ℕ), ∀ᶠ j in Filter.atTop, j ∈ {n : ℤ | ∃ B : Finset ℤ, ↑B ⊆ Set.range (fun n : ℕ ↦ ⌊(1 / (2:ℝ)^k) * (2:ℝ) ^ n⌋) ∧ n = ∑ i ∈ B, i} := by
  intro k
  rw [Filter.eventually_atTop]
  refine ⟨0, fun j hj => ?_⟩
  set E := j.toNat.bitIndices.toFinset with hEdef
  have hE : j.toNat = ∑ i ∈ E, 2 ^ i := (Finset.sum_toFinset_bitIndices_two_pow j.toNat).symm
  refine ⟨E.image (fun i => (2:ℤ)^i), ?_, ?_⟩
  · rintro x hx
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx
    obtain ⟨i, _, rfl⟩ := hx
    refine ⟨i + k, ?_⟩
    show ⌊(1 / (2:ℝ)^k) * (2:ℝ)^(i+k)⌋ = 2^i
    have hc : (1 / (2:ℝ)^k) * (2:ℝ)^(i+k) = ((2^i : ℤ) : ℝ) := by
      rw [pow_add]; push_cast; field_simp
    rw [hc, Int.floor_intCast]
  · have hinj : Function.Injective (fun i : ℕ => (2:ℤ)^i) := by
      intro a b hab
      simp only at hab
      have : (2:ℕ)^a = (2:ℕ)^b := by exact_mod_cast hab
      exact Nat.pow_right_injective (le_refl 2) this
    rw [Finset.sum_image (fun x _ y _ h => hinj h)]
    have hj' : j = (j.toNat : ℤ) := (Int.toNat_of_nonneg hj).symm
    rw [hj']
    exact_mod_cast hE

/-- **`α > 2` fails.** For any `t > 0` and `α > 2`, `(t, α)` is not a good
pair. The terms eventually grow so fast that `a_{n+1}` exceeds the sum `S_n`
of all previous terms by at least two; then `S_n + 1` is a large integer that
no subset sum can hit. -/
theorem alpha_gt_two_not_isGoodPair :
    ∀ (t α : ℝ), 0 < t → 2 < α →
    ¬ (∀ᶠ k in Filter.atTop, k ∈ {n : ℤ | ∃ B : Finset ℤ, ↑B ⊆ Set.range (fun n : ℕ ↦ ⌊t * α ^ n⌋) ∧ n = ∑ i ∈ B, i}) := by
  intro t α ht hα
  set f : ℕ → ℤ := fun n => ⌊t * α ^ n⌋ with hf
  have hα0 : (0 : ℝ) < α := by linarith
  have hα1 : (1 : ℝ) < α := by linarith
  have hα1' : (1 : ℝ) ≤ α := le_of_lt hα1
  have hαm1 : (0 : ℝ) < α - 1 := by linarith
  have hnonneg : ∀ n, 0 ≤ f n := by
    intro n
    rw [hf]
    exact Int.floor_nonneg.mpr (by positivity)
  have hterm_le : ∀ k, (f k : ℝ) ≤ t * α ^ k := by
    intro k
    rw [hf]
    exact Int.floor_le _
  have hmono : Monotone f := by
    intro n m hnm
    rw [hf]
    apply Int.floor_le_floor
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hα1' hnm) (le_of_lt ht)
  set S : ℕ → ℤ := fun n => ∑ k ∈ Finset.range (n + 1), f k with hS
  have hSbound : ∀ n, (S n : ℝ) ≤ t * α ^ (n + 1) / (α - 1) := by
    intro n
    have h1 : (S n : ℝ) = ∑ k ∈ Finset.range (n + 1), (f k : ℝ) := by
      rw [hS]
      push_cast
      rfl
    rw [h1]
    have h2 : ∑ k ∈ Finset.range (n + 1), (f k : ℝ) ≤ ∑ k ∈ Finset.range (n + 1), t * α ^ k := by
      apply Finset.sum_le_sum
      intro k _
      exact hterm_le k
    refine le_trans h2 ?_
    have h3 : ∑ k ∈ Finset.range (n + 1), t * α ^ k = t * ((α ^ (n + 1) - 1) / (α - 1)) := by
      rw [← Finset.mul_sum, geom_sum_eq (by linarith : α ≠ 1)]
    rw [h3]
    rw [mul_div_assoc]
    apply mul_le_mul_of_nonneg_left _ (le_of_lt ht)
    apply div_le_div_of_nonneg_right (by linarith) hαm1.le
  rw [Filter.not_eventually]
  rw [Filter.frequently_atTop]
  intro N
  have htend : Filter.Tendsto (fun n : ℕ => t * α ^ (n + 1) * ((α - 2) / (α - 1)) - 2) Filter.atTop Filter.atTop := by
    have hpow : Filter.Tendsto (fun n : ℕ => α ^ (n + 1)) Filter.atTop Filter.atTop :=
      (tendsto_pow_atTop_atTop_of_one_lt hα1).comp (Filter.tendsto_add_atTop_nat 1)
    have hc2 : (0 : ℝ) < (α - 2) / (α - 1) := by
      apply _root_.div_pos <;> linarith
    have h1 : Filter.Tendsto (fun n : ℕ => t * α ^ (n + 1)) Filter.atTop Filter.atTop := hpow.const_mul_atTop ht
    have h2 : Filter.Tendsto (fun n : ℕ => t * α ^ (n + 1) * ((α - 2) / (α - 1))) Filter.atTop Filter.atTop := h1.atTop_mul_const hc2
    exact Filter.tendsto_atTop_add_const_right Filter.atTop (-2 : ℝ) (by simpa [sub_eq_add_neg] using h2)
  have htend2 : Filter.Tendsto (fun n : ℕ => t * α ^ n - 1) Filter.atTop Filter.atTop := by
    have hpow : Filter.Tendsto (fun n : ℕ => α ^ n) Filter.atTop Filter.atTop := tendsto_pow_atTop_atTop_of_one_lt hα1
    have h1 : Filter.Tendsto (fun n : ℕ => t * α ^ n) Filter.atTop Filter.atTop := hpow.const_mul_atTop ht
    exact Filter.tendsto_atTop_add_const_right Filter.atTop (-1 : ℝ) (by simpa [sub_eq_add_neg] using h1)
  have hev := (htend.eventually_ge_atTop (max ((N : ℝ) + 2) 3)).and (htend2.eventually_ge_atTop ((N : ℝ)))
  obtain ⟨n, hn, hn2⟩ := hev.exists
  have hn' : (N : ℝ) + 2 ≤ t * α ^ (n + 1) * ((α - 2) / (α - 1)) - 2 := le_trans (le_max_left _ _) hn
  have hn3 : (3 : ℝ) ≤ t * α ^ (n + 1) * ((α - 2) / (α - 1)) - 2 := le_trans (le_max_right _ _) hn
  have ha_lb : t * α ^ (n + 1) - 1 < (f (n + 1) : ℝ) := by
    have := Int.sub_one_lt_floor (t * α ^ (n + 1))
    rw [hf]
    exact this
  have hreal : (f (n + 1) : ℝ) - (S n : ℝ) - 1 > t * α ^ (n + 1) * ((α - 2) / (α - 1)) - 2 := by
    have hsb := hSbound n
    have key : t * α ^ (n + 1) * ((α - 2) / (α - 1)) = t * α ^ (n + 1) - t * α ^ (n + 1) / (α - 1) := by
      field_simp
      ring
    rw [key]
    linarith [ha_lb, hsb]
  have hcombine : (f (n + 1) : ℝ) - (S n : ℝ) - 1 > (N : ℝ) + 2 := by
    linarith [hreal, hn']
  have hgapR : (f (n + 1) : ℝ) - (S n : ℝ) - 1 > 3 := by
    linarith [hreal, hn3]
  have hgap : f (n + 1) ≥ S n + 2 := by
    have : ((f (n + 1) - (S n) : ℤ) : ℝ) ≥ ((2 : ℤ) : ℝ) := by
      push_cast
      linarith [hgapR]
    have h2 : (f (n + 1) - (S n) : ℤ) ≥ (2 : ℤ) := by
      exact_mod_cast this
    linarith
  have hSn_lb : (S n : ℝ) ≥ t * α ^ n - 1 := by
    have hlast : f n ≤ S n := by
      rw [hS]
      apply Finset.single_le_sum (fun i _ => hnonneg i)
      simp
    have h1 : (f n : ℝ) ≥ t * α ^ n - 1 := by
      have := Int.sub_one_lt_floor (t * α ^ n)
      have : (t * α ^ n) - 1 ≤ (⌊t * α ^ n⌋ : ℝ) := le_of_lt this
      rw [hf]
      simpa using this
    have h2 : (f n : ℝ) ≤ (S n : ℝ) := by exact_mod_cast hlast
    linarith
  have hSnN : (S n) ≥ N := by
    have : (S n : ℝ) ≥ (N : ℝ) := le_trans hn2 hSn_lb
    exact_mod_cast this
  refine ⟨S n + 1, ?_, ?_⟩
  · linarith
  · rintro ⟨B, hBsub, hBsum⟩
    have hBnonneg : ∀ b ∈ B, (0 : ℤ) ≤ b := by
      intro b hb
      have : b ∈ Set.range f := hBsub hb
      obtain ⟨m, rfl⟩ := this
      exact hnonneg m
    set P : ℤ := f (n + 1) with hP
    by_cases hcase : ∃ b ∈ B, P ≤ b
    · obtain ⟨b, hbB, hPb⟩ := hcase
      have hge : P ≤ ∑ i ∈ B, i := by
        calc P ≤ b := hPb
          _ ≤ ∑ i ∈ B, i := Finset.single_le_sum (fun i hi => hBnonneg i hi) hbB
      have hSgeP : S n + 1 ≥ P := by
        rw [hBsum]
        exact hge
      have hleP : S n + 2 ≤ P := by
        simpa [hP] using hgap
      have : S n + 2 ≤ S n + 1 := le_trans hleP hSgeP
      omega
    · have hlt : ∀ b ∈ B, b < P := by
        intro b hb
        by_contra hc
        exact hcase ⟨b, hb, not_lt.mp hc⟩
      have hBsubimg : B ⊆ (Finset.range (n + 1)).image f := by
        intro b hb
        have hbP : b < P := hlt b hb
        have : b ∈ Set.range f := hBsub hb
        obtain ⟨m, rfl⟩ := this
        have hmle : m ≤ n := by
          by_contra hmn
          have : f (n + 1) ≤ f m := hmono (by omega)
          rw [← hP] at this
          omega
        rw [Finset.mem_image]
        exact ⟨m, Finset.mem_range.mpr (by omega), rfl⟩
      have himg_le : ∑ u ∈ (Finset.range (n + 1)).image f, u ≤ S n := by
        have h := Finset.sum_image_le_of_nonneg (s := Finset.range (n + 1)) (g := f) (f := fun x : ℤ => x) (fun u hu => by
          rw [Finset.mem_image] at hu
          obtain ⟨m, _, rfl⟩ := hu
          exact hnonneg m)
        simpa [hS] using h
      have hBsum_le : ∑ i ∈ B, i ≤ S n := by
        calc ∑ i ∈ B, i ≤ ∑ u ∈ (Finset.range (n + 1)).image f, u :=
            Finset.sum_le_sum_of_subset_of_nonneg hBsubimg (fun i hi _ => by
              rw [Finset.mem_image] at hi
              obtain ⟨m, _, rfl⟩ := hi
              exact hnonneg m)
          _ ≤ S n := himg_le
      rw [← hBsum] at hBsum_le
      omega

/-- **The full integer characterization.** For integers `t, α ≥ 1`, `(t, α)` is
a good pair iff `t = 1` and `α = 2` — assembled from the four theorems above
by case split: rule out `α = 1` (`alpha_le_one_not_isGoodPair`) and `α > 2`
(`alpha_gt_two_not_isGoodPair`) to force `α = 2`, then rule out `t ≥ 2`
(`int_coeff_ge_two_not_isGoodPair`) to force `t = 1`; the converse is
`one_two_isGoodPair`. -/
theorem integer_isGoodPair_iff :
    ∀ (t α : ℤ), 1 ≤ t → 1 ≤ α →
    ((∀ᶠ k in Filter.atTop, k ∈ {n : ℤ | ∃ B : Finset ℤ, ↑B ⊆ Set.range (fun n : ℕ ↦ ⌊(t:ℝ) * (α:ℝ) ^ n⌋) ∧ n = ∑ i ∈ B, i}) ↔ t = 1 ∧ α = 2) := by
  intro t α ht hα
  constructor
  · intro hgp
    have htR : (0:ℝ) < (t:ℝ) := by exact_mod_cast (show (0:ℤ) < t by linarith)
    have hα_ne1 : α ≠ 1 := by
      intro heq
      have hgp' := hgp
      rw [heq] at hgp'
      simp only [Int.cast_one] at hgp'
      exact absurd hgp' (alpha_le_one_not_isGoodPair (t:ℝ) htR (1:ℝ) (by norm_num) (by norm_num))
    have hα_le2 : α ≤ 2 := by
      by_contra hgt
      push_neg at hgt
      have hα3 : (2:ℝ) < (α:ℝ) := by exact_mod_cast (show (2:ℤ) < α by omega)
      exact absurd hgp (alpha_gt_two_not_isGoodPair (t:ℝ) (α:ℝ) htR hα3)
    have hα2 : α = 2 := by omega
    have ht_le1 : t ≤ 1 := by
      by_contra hgt
      push_neg at hgt
      have ht2 : (2:ℤ) ≤ t := by omega
      have hgp' := hgp
      rw [hα2] at hgp'
      have hcast2 : ((2:ℤ):ℝ) = (2:ℝ) := by norm_num
      rw [hcast2] at hgp'
      exact absurd hgp' (int_coeff_ge_two_not_isGoodPair t ht2 2)
    have ht1 : t = 1 := by omega
    exact ⟨ht1, hα2⟩
  · rintro ⟨ht1, hα2⟩
    subst ht1
    subst hα2
    have h1 : ((1:ℤ):ℝ) = 1 := by norm_num
    have h2 : ((2:ℤ):ℝ) = 2 := by norm_num
    rw [h1, h2]
    exact one_two_isGoodPair

end LeanChecker.Erdos349
