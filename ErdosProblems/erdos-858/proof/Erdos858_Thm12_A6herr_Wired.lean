/-
Erdős Problem #858 — Theorem 1.2 assembly, A6-herr full wiring (Chojecki 2026).

`A6-herr full wiring`: composes the clamp modulus (#149), the clamp identity on
`[s,t]` (#172), the generic block-membership bound (#104-generalized), the
harmonic-diff bridge, the general grid aggregation engine (raw, `#136`), the A6
aggregation core (`#170`), and the divide-bound helper (`#173`) into A6-herr's
(`#163`) exact aggregation hypothesis — **unconditionally, for any `f` continuous
on `[s,t]`**:

  `∀ε>0, ∀ᶠK, ∀N, |A_N/log N − W_KN/log N| ≤ ε·(mass_N/log N)`.

This discharges the ONE remaining wiring gap of the interval log-harmonic transfer
A6 (`#160` capstone via herr `#163`), leaving only the mechanical `#97`-at-the-
pullback instantiation (using the already-verified pullback continuity `#167`) for
`hR`, and completing A6 in terms of `f` directly rather than `f∘clamp`.

Proof strategy (after a heartbeat-timeout on the fully-inlined v1): take `#170`
(A6 aggregation core) as a **black-box hypothesis** rather than re-deriving its
grid-property machinery inline — this cuts elaboration cost enough to fit the
default heartbeat budget. Small-N (`N∈{0,1}`): `log N = 0` (`interval_cases` +
`norm_num`), goal trivializes to `0≤0` (`simp`). Big-N (`1<N`): `#170` at
`G:=f∘clamp` gives the raw clamp-composed bound; pointwise clamp-recovery
(`hGeqf_a`/`hGeqf_v`, via `#172`+membership showing `u_a,v_j∈[s,t]` so `clamp=id`
there) + `Finset.sum_congr` rewrites `f∘clamp → f` in both sums; a minimal
one-step floor-monotone fact (`hvstep`+`hfloorstep`, NOT the full `Monotone` —
only what the harmonic-diff conversion needs) + the harmonic-diff bridge convert
the raw block sums to the canonical `harmonic` differences; `mul_one_div`
normalizes `f(u_a)*(1/a)` to `f(u_a)/a`; `#173` divides through by `log N`.

Kernel-verified via the proofsearch MCP:
  episode a2030122-5d26-427b-a742-f1e4bdccd030,
  problem_version_id 891c086c-fdbc-431a-b6c7-13d753d79872.
Outcome: kernel_verified / root_kernel_verified (v2 of the wiring design, 3rd
submission on this problem_version — v1 attempt on this design hit "Unknown
identifier `le_or_lt`" [fixed: `Classical.em`+`not_le.mp` is the portable
le-vs-lt split], v2 hit an `f(x)*(1/a)` vs `f(x)/a` syntactic mismatch against
`hdiv` [fixed: `simp only [mul_one_div] at hbound` before the final `exact`]. The
FULLY-INLINED design (re-deriving `#170`'s grid machinery locally instead of
taking it as a hypothesis) hit a genuine `(deterministic) timeout at whnf,
maximum number of heartbeats (200000)` — `set_option maxHeartbeats N in` as a
proof_term prefix did NOT change the reported limit, so the fix was structural
(black-box `#170` + a minimal one-step floor fact instead of full `Monotone`),
not a budget override.
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 2841db6fc3edbaa8647ee60bb068aa1d15690a2c62f8193a40a012136fccb9b5.

**Lean lessons**: (1) `le_or_lt` is not available under that name in this pin —
use `(Classical.em (a≤b)).elim` + `not_le.mp` for a portable le-vs-lt split.
(2) A `whnf` heartbeat timeout on a large but logically-correct proof term is a
genuine elaboration-cost signal, not necessarily a bug — `set_option
maxHeartbeats N in <tacticSeq>` as a proof_term prefix did NOT raise the
effective limit in this harness; the reliable fix is reducing term complexity
(take an already-verified compound result as an opaque hypothesis rather than
re-deriving its multi-step internals inline). (3) `h136`'s generic weight
`fun a => 1/a` produces `f(...) * (1/a)` sum terms; a target stated with
`f(...) / a` needs an explicit `simp only [mul_one_div]` bridge before matching.
(4) Pre-audit long unicode-heavy proof_term strings via a scratch-file
byte-level check (floor-close immediately followed by subscript-plus; running
paren/bracket balance never dipping negative) BEFORE submitting — this caught a
`₉`/`₊` subscript typo and confirmed bracket correctness across ~4800-character
submissions with zero false negatives.
-/
import Mathlib

namespace Erdos858

/-- Theorem 1.2 A6-herr full wiring: composes `#149`+`#172`+`#104`-generalized+
harmonic-diff+`#136`+`#170`+`#173` into A6-herr's aggregation hypothesis
unconditionally for `f` continuous on `[s,t]`. The mechanical composition step
discharging A6-herr's third hypothesis in terms of `f` directly. -/
theorem erdos858_thm12_a6_herr_wired :
    ∀ (f : ℝ → ℝ) (s t : ℝ),
      s ≤ t → ContinuousOn f (Set.Icc s t) →
      (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x y : ℝ, |x - y| ≤ δ →
        |f (max (min t x) s) - f (max (min t y) s)| ≤ ε) →
      (∀ (s' t' x : ℝ), s' ≤ t' → x ∈ Set.Icc s' t' → max (min t' x) s' = x) →
      (∀ (N : ℕ) (v w : ℝ), 1 < (N:ℝ) → ∀ a : ℕ,
        a ∈ Finset.Ioc ⌊(N:ℝ)^v⌋₊ ⌊(N:ℝ)^w⌋₊ →
        v < Real.log (a:ℝ) / Real.log (N:ℝ) ∧ Real.log (a:ℝ) / Real.log (N:ℝ) ≤ w) →
      (∀ m n : ℕ, m ≤ n → (harmonic n : ℝ) - (harmonic m : ℝ) = ∑ a ∈ Finset.Ioc m n, (1:ℝ) / (a:ℝ)) →
      (∀ (G : ℝ → ℝ) (s' t' : ℝ) (N K : ℕ) (δ' η : ℝ),
          s' ≤ t' → 1 < (N:ℝ) → 0 < K →
          (∀ x y : ℝ, |x - y| ≤ δ' → |G x - G y| ≤ η) →
          ((t' - s')/(K:ℝ) ≤ δ') →
          (∀ (G' : ℝ → ℝ) (h : ℕ → ℝ) (N' K' : ℕ) (δ'' ε'' : ℝ) (v : ℕ → ℝ),
              1 < (N':ℝ) → (∀ k : ℕ, 0 ≤ h k) → (∀ x y : ℝ, |x - y| ≤ δ'' → |G' x - G' y| ≤ ε'') →
              (∀ j : ℕ, v j ≤ v (j + 1)) → (∀ j : ℕ, j < K' → v (j + 1) - v j ≤ δ'') →
              Monotone (fun j => ⌊(N':ℝ) ^ (v j)⌋₊) →
              |(∑ a ∈ Finset.Ioc ⌊(N':ℝ) ^ (v 0)⌋₊ ⌊(N':ℝ) ^ (v K')⌋₊, G' (Real.log (a:ℝ) / Real.log (N':ℝ)) * h a)
                - (∑ j ∈ Finset.range K', G' (v j) * (∑ a ∈ Finset.Ioc ⌊(N':ℝ) ^ (v j)⌋₊ ⌊(N':ℝ) ^ (v (j+1))⌋₊, h a))|
              ≤ ε'' * (∑ a ∈ Finset.Ioc ⌊(N':ℝ) ^ (v 0)⌋₊ ⌊(N':ℝ) ^ (v K')⌋₊, h a)) →
          |(∑ a ∈ Finset.Ioc ⌊(N:ℝ)^s'⌋₊ ⌊(N:ℝ)^t'⌋₊, G (Real.log (a:ℝ) / Real.log (N:ℝ)) * (1/(a:ℝ)))
            - (∑ j ∈ Finset.range K, G (s' + ((j:ℝ)/(K:ℝ))*(t'-s')) * (∑ a ∈ Finset.Ioc ⌊(N:ℝ)^(s' + ((j:ℝ)/(K:ℝ))*(t'-s'))⌋₊ ⌊(N:ℝ)^(s' + (((j:ℝ)+1)/(K:ℝ))*(t'-s'))⌋₊, (1/(a:ℝ))))|
          ≤ η * (∑ a ∈ Finset.Ioc ⌊(N:ℝ)^s'⌋₊ ⌊(N:ℝ)^t'⌋₊, (1/(a:ℝ)))) →
      (∀ (G' : ℝ → ℝ) (h : ℕ → ℝ) (N' K' : ℕ) (δ'' ε'' : ℝ) (v : ℕ → ℝ),
          1 < (N':ℝ) → (∀ k : ℕ, 0 ≤ h k) → (∀ x y : ℝ, |x - y| ≤ δ'' → |G' x - G' y| ≤ ε'') →
          (∀ j : ℕ, v j ≤ v (j + 1)) → (∀ j : ℕ, j < K' → v (j + 1) - v j ≤ δ'') →
          Monotone (fun j => ⌊(N':ℝ) ^ (v j)⌋₊) →
          |(∑ a ∈ Finset.Ioc ⌊(N':ℝ) ^ (v 0)⌋₊ ⌊(N':ℝ) ^ (v K')⌋₊, G' (Real.log (a:ℝ) / Real.log (N':ℝ)) * h a)
            - (∑ j ∈ Finset.range K', G' (v j) * (∑ a ∈ Finset.Ioc ⌊(N':ℝ) ^ (v j)⌋₊ ⌊(N':ℝ) ^ (v (j+1))⌋₊, h a))|
          ≤ ε'' * (∑ a ∈ Finset.Ioc ⌊(N':ℝ) ^ (v 0)⌋₊ ⌊(N':ℝ) ^ (v K')⌋₊, h a)) →
      (∀ (A W mass L ε : ℝ), 0 < L → |A - W| ≤ ε * mass → |A/L - W/L| ≤ ε * (mass/L)) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ K in Filter.atTop, ∀ N : ℕ,
        |(∑ a ∈ Finset.Ioc ⌊(N:ℝ)^s⌋₊ ⌊(N:ℝ)^t⌋₊, f (Real.log (a:ℝ) / Real.log (N:ℝ)) / (a:ℝ)) / Real.log (N:ℝ)
          - (∑ j ∈ Finset.range K, f (s + ((j:ℝ)/(K:ℝ))*(t-s)) * ((harmonic ⌊(N:ℝ) ^ (s + (((j:ℝ)+1)/(K:ℝ))*(t-s))⌋₊ : ℝ) - (harmonic ⌊(N:ℝ) ^ (s + ((j:ℝ)/(K:ℝ))*(t-s))⌋₊ : ℝ))) / Real.log (N:ℝ)|
        ≤ ε * ((∑ a ∈ Finset.Ioc ⌊(N:ℝ)^s⌋₊ ⌊(N:ℝ)^t⌋₊, 1/(a:ℝ)) / Real.log (N:ℝ)) := by
  intro f s t hst hf h149 hclampid hmembership hharmdiff h170 h136 hdiv ε hε
  obtain ⟨δ, hδpos, hδmod⟩ := h149 ε hε
  obtain ⟨K₀, hK₀⟩ := exists_nat_gt ((t-s)/δ)
  rw [Filter.eventually_atTop]
  refine ⟨max 1 K₀, fun K hK => ?_⟩
  have hKpos : 0 < K := lt_of_lt_of_le Nat.one_pos (le_trans (le_max_left 1 K₀) hK)
  have hKR : (0:ℝ) < (K:ℝ) := by exact_mod_cast hKpos
  have hK₀K : (K₀:ℝ) ≤ (K:ℝ) := by exact_mod_cast (le_trans (le_max_right 1 K₀) hK)
  have hwidth : (t-s)/(K:ℝ) ≤ δ := by have h1 : (t-s)/δ < (K:ℝ) := lt_of_lt_of_le hK₀ hK₀K; rw [div_lt_iff₀ hδpos] at h1; rw [div_le_iff₀ hKR]; linarith [h1, mul_comm (K:ℝ) δ]
  intro N
  exact (Classical.em ((N:ℝ) ≤ 1)).elim (fun hN1 => by have hN1' : N ≤ 1 := (by exact_mod_cast hN1); have hlogN0 : Real.log (N:ℝ) = 0 := (by interval_cases N <;> norm_num [Real.log_zero, Real.log_one]); simp [hlogN0]) (fun hN1' => by have hN1 : 1 < (N:ℝ) := not_le.mp hN1'; have hbound := h170 (fun x => f (max (min t x) s)) s t N K δ ε hst hN1 hKpos hδmod hwidth h136; have hGeqf_a : ∀ a : ℕ, a ∈ Finset.Ioc ⌊(N:ℝ)^s⌋₊ ⌊(N:ℝ)^t⌋₊ → f (max (min t (Real.log (a:ℝ)/Real.log (N:ℝ))) s) = f (Real.log (a:ℝ)/Real.log (N:ℝ)) := (fun a ha => by obtain ⟨hlt, hle⟩ := hmembership N s t hN1 a ha; rw [hclampid s t _ hst ⟨le_of_lt hlt, hle⟩]); have hGeqf_v : ∀ j : ℕ, j ≤ K → f (max (min t (s + ((j:ℝ)/(K:ℝ))*(t-s))) s) = f (s + ((j:ℝ)/(K:ℝ))*(t-s)) := (fun j hj => by have hts : (0:ℝ) ≤ t - s := (by linarith); have hmemj : s + ((j:ℝ)/(K:ℝ))*(t-s) ∈ Set.Icc s t := ⟨by nlinarith [mul_nonneg (div_nonneg (Nat.cast_nonneg j) hKR.le) hts], by have hjK1 : ((j:ℝ)/(K:ℝ)) ≤ 1 := (by rw [div_le_one hKR]; exact_mod_cast hj); nlinarith [mul_le_mul_of_nonneg_right hjK1 hts]⟩; rw [hclampid s t _ hst hmemj]); have hAeq : (∑ a ∈ Finset.Ioc ⌊(N:ℝ)^s⌋₊ ⌊(N:ℝ)^t⌋₊, f (max (min t (Real.log (a:ℝ)/Real.log (N:ℝ))) s) * (1/(a:ℝ))) = (∑ a ∈ Finset.Ioc ⌊(N:ℝ)^s⌋₊ ⌊(N:ℝ)^t⌋₊, f (Real.log (a:ℝ)/Real.log (N:ℝ)) * (1/(a:ℝ))) := Finset.sum_congr rfl (fun a ha => by rw [hGeqf_a a ha]); have hWeq : (∑ j ∈ Finset.range K, f (max (min t (s + ((j:ℝ)/(K:ℝ))*(t-s))) s) * (∑ a ∈ Finset.Ioc ⌊(N:ℝ)^(s + ((j:ℝ)/(K:ℝ))*(t-s))⌋₊ ⌊(N:ℝ)^(s + (((j:ℝ)+1)/(K:ℝ))*(t-s))⌋₊, (1/(a:ℝ)))) = (∑ j ∈ Finset.range K, f (s + ((j:ℝ)/(K:ℝ))*(t-s)) * (∑ a ∈ Finset.Ioc ⌊(N:ℝ)^(s + ((j:ℝ)/(K:ℝ))*(t-s))⌋₊ ⌊(N:ℝ)^(s + (((j:ℝ)+1)/(K:ℝ))*(t-s))⌋₊, (1/(a:ℝ)))) := Finset.sum_congr rfl (fun j hj => by rw [hGeqf_v j (le_of_lt (Finset.mem_range.mp hj))]); rw [hAeq, hWeq] at hbound; have hvstep : ∀ j : ℕ, s+((j:ℝ)/(K:ℝ))*(t-s) ≤ s+(((j:ℝ)+1)/(K:ℝ))*(t-s) := (fun j => by have hts2 : (0:ℝ) ≤ t-s := (by linarith); have heq : (s+(((j:ℝ)+1)/(K:ℝ))*(t-s)) - (s+((j:ℝ)/(K:ℝ))*(t-s)) = (t-s)/(K:ℝ) := (by field_simp; ring); nlinarith [div_nonneg hts2 hKR.le, heq]); have hfloorstep : ∀ j : ℕ, ⌊(N:ℝ)^(s+((j:ℝ)/(K:ℝ))*(t-s))⌋₊ ≤ ⌊(N:ℝ)^(s+(((j:ℝ)+1)/(K:ℝ))*(t-s))⌋₊ := (fun j => Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le (le_of_lt hN1) (hvstep j))); have hharmconv : ∀ j : ℕ, (∑ a ∈ Finset.Ioc ⌊(N:ℝ)^(s + ((j:ℝ)/(K:ℝ))*(t-s))⌋₊ ⌊(N:ℝ)^(s + (((j:ℝ)+1)/(K:ℝ))*(t-s))⌋₊, (1:ℝ)/(a:ℝ)) = (harmonic ⌊(N:ℝ)^(s + (((j:ℝ)+1)/(K:ℝ))*(t-s))⌋₊ : ℝ) - (harmonic ⌊(N:ℝ)^(s + ((j:ℝ)/(K:ℝ))*(t-s))⌋₊ : ℝ) := (fun j => (hharmdiff ⌊(N:ℝ)^(s + ((j:ℝ)/(K:ℝ))*(t-s))⌋₊ ⌊(N:ℝ)^(s + (((j:ℝ)+1)/(K:ℝ))*(t-s))⌋₊ (hfloorstep j)).symm); have hWeq2 : (∑ j ∈ Finset.range K, f (s + ((j:ℝ)/(K:ℝ))*(t-s)) * (∑ a ∈ Finset.Ioc ⌊(N:ℝ)^(s + ((j:ℝ)/(K:ℝ))*(t-s))⌋₊ ⌊(N:ℝ)^(s + (((j:ℝ)+1)/(K:ℝ))*(t-s))⌋₊, (1/(a:ℝ)))) = (∑ j ∈ Finset.range K, f (s + ((j:ℝ)/(K:ℝ))*(t-s)) * ((harmonic ⌊(N:ℝ)^(s + (((j:ℝ)+1)/(K:ℝ))*(t-s))⌋₊ : ℝ) - (harmonic ⌊(N:ℝ)^(s + ((j:ℝ)/(K:ℝ))*(t-s))⌋₊ : ℝ))) := Finset.sum_congr rfl (fun j _ => by rw [hharmconv j]); rw [hWeq2] at hbound; simp only [mul_one_div] at hbound; have hlogNpos : 0 < Real.log (N:ℝ) := Real.log_pos hN1; exact hdiv _ _ _ _ ε hlogNpos hbound)

end Erdos858
