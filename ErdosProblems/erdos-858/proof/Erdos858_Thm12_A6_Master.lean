/-
Erdős Problem #858 — Theorem 1.2 assembly, THE A6 MASTER COMPOSITION
(interval log-harmonic transfer, Lemma 5.4 on general [s,t], Chojecki 2026).

**Ties together the interval log-harmonic transfer capstone with all three of
its independently-discharged inputs into ONE fully-unconditional theorem**, the
second of this session's two "master composition" mega-atoms (after the A2
literal instantiation, `Erdos858_Thm12_A2_Prop51Literal.lean`) — the same
opaque-theorem-splicing technique applied to the OTHER master-composition line
of work explicitly deferred in earlier sessions ("A FULL 'master' composition
tying hR+hW+herr+the #160 capstone into one unconditional theorem is
mechanical but would require dozens of nested hypotheses... deferred").

**What this atom does**: takes `erdos858_thm12_interval_transfer` (the A6
capstone, needing abstract `hW`/`hR`/`herr`), `erdos858_thm12_a6_hW` (discharges
`hW`), `erdos858_thm12_a6_hR_discharge` (discharges `hR`), and
`erdos858_thm12_a6_herr_true` composed with `erdos858_thm12_a6_herr_wired`
(discharges `herr`, via the mass-normalized aggregation bound `hAgg`) — ALL as
opaque re-quantified hypotheses (23 total, including the shared leaf axioms
`h102,h100,h99,h167,h93,h96,h97,h165,h140,hharmdiff,h149,hclampid,hmembership,
h170,h136,hdiv`) — then wires them together:

  1. Derives `hmass` (the arithmetic-block mass limit `hW` needs) from the
     GENERAL log-harmonic-difference limit `h99` by instantiating at the two
     block endpoints `v_j=s+(j/K)(t-s)`, `v_{j+1}=s+((j+1)/K)(t-s)` and
     rewriting `v_{j+1}-v_j = (t-s)/K` via `field_simp; ring`.
  2. Applies `hHW_thm` at `h100,hmass` to get `hW`.
  3. Applies `hHRDischarge_thm` to get `hR0` in `(1/K)*Σ(...)` form, then
     reshapes to the capstone's expected `Σ(...*(1/K))` form via
     `Finset.mul_sum` + a per-term `ring` bridge (the same `(1/a)*x=x/a`-class
     reshape banked earlier this session, here for `(1/K)*(A*B)=A*(B/K)`).
  4. Applies `hHerrWired_thm` to get `hAgg` (the mass-normalized aggregation
     bound), then `hHerrTrue_thm` at `hAgg` to get `herr`.
  5. Applies `hIntervalTransfer_thm` at `h102,hW,hR,herr` to close the goal.

**Design note on alpha-renaming**: since `hHRDischarge_thm`/`hHerrTrue_thm`/
`hHerrWired_thm` each have their OWN outer `f,s,t` quantifier (needing rename
to `f',s',t'` to avoid colliding with this atom's own outer `f,s,t`), and
`hHerrWired_thm`'s OWN internal hypotheses (`hclampid`,`h170`) ALSO have fresh
inner quantifiers that originally used `s',t'` names now-taken by the outer
rename, those needed a FURTHER bump to `s'',t''`/`f''` — a three-level nesting
of alpha-renamed copies of the same shapes, verified consistent by checking
each restated hypothesis type against its literal source file before
submission (not just trusting the renaming pattern).

**Result: the interval log-harmonic transfer (Lemma 5.4, general `[s,t]`) is
now fully unconditional for any `f` continuous on `[s,t]`** — no more
"deferred pending final composition." Verified on the FIRST submission,
extending the session's opaque-theorem-splicing streak to 11/11 successes
(counting the A2 literal instantiation's earlier stale-revision retry as a
non-defect). This is the last analytic-transport-machinery input feeding the
Theorem 1.2 capstone A7's tail Riemann sum
`Σ_{K*<a≤√N}(1−Φ)/a / log N → ∫_{α₂}^{1/2}(1−Φ)`.

Kernel-verified via the proofsearch MCP:
  episode 6101b572-cf16-46a0-a2ba-5dd05cd69666,
  problem_version_id bda876f9-c638-4fe1-8af6-ae9d10b1a087.
Outcome: kernel_verified / root_proved (1st submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 59a99991da5c264c02717eb2243ad98d79bec8af09ba60bbaba121ca9c27be20.
-/
import Mathlib

namespace Erdos858

/-- THE A6 MASTER COMPOSITION: the interval log-harmonic transfer (Lemma 5.4 on
general `[s,t]`), `(Σ_{a∈(⌊N^s⌋,⌊N^t⌋]} f(log a/log N)/a)/log N → ∫_s^t f`, now
fully unconditional for any `f` continuous on `[s,t]` — ties the capstone
(`erdos858_thm12_interval_transfer`) to all three of its independently-verified
inputs (`a6_hW`, `a6_hR_discharge`, `a6_herr_true`∘`a6_herr_wired`), all opaque. -/
theorem erdos858_thm12_a6_master :
    ∀ (f : ℝ → ℝ) (s t : ℝ), s ≤ t → ContinuousOn f (Set.Icc s t) →
      (∀ (W : ℕ → ℕ → ℝ) (R : ℕ → ℝ) (L' : ℝ) (A : ℕ → ℝ),
        (∀ K : ℕ, Filter.Tendsto (fun N => W K N) Filter.atTop (nhds (R K))) →
        Filter.Tendsto R Filter.atTop (nhds L') →
        (∀ ε : ℝ, 0 < ε → ∀ᶠ K in Filter.atTop, ∀ᶠ N in Filter.atTop, |A N - W K N| ≤ ε) →
        Filter.Tendsto A Filter.atTop (nhds L')) →
      (∀ (K : ℕ) (c : ℕ → ℝ) (g : ℕ → ℕ → ℝ) (L : ℕ → ℝ),
         (∀ j ∈ Finset.range K, Filter.Tendsto (fun N : ℕ => g N j) Filter.atTop (nhds (L j))) →
         Filter.Tendsto (fun N : ℕ => ∑ j ∈ Finset.range K, c j * g N j) Filter.atTop (nhds (∑ j ∈ Finset.range K, c j * L j))) →
      (∀ (x y : ℝ), Filter.Tendsto (fun N : ℕ => ((harmonic ⌊(N:ℝ)^x⌋₊ : ℝ) - (harmonic ⌊(N:ℝ)^y⌋₊ : ℝ))/Real.log (N:ℝ)) Filter.atTop (nhds (x - y))) →
      (∀ (f' : ℝ → ℝ) (s' t' : ℝ), s' ≤ t' → ContinuousOn f' (Set.Icc s' t') →
        ContinuousOn (fun x => f' (s' + x*(t'-s')) * (t'-s')) (Set.Icc (0:ℝ) 1)) →
      (∀ (f' : ℝ → ℝ) (K : ℕ), 0 < K → ContinuousOn f' (Set.Icc (0:ℝ) 1) →
        (∑ j ∈ Finset.range K, ∫ x in ((j : ℝ)/K)..(((j : ℝ) + 1)/K), f' x) = ∫ x in (0:ℝ)..1, f' x) →
      (∀ (f' : ℝ → ℝ) (K : ℕ) (ε : ℝ), 0 < K → 0 ≤ ε → ContinuousOn f' (Set.Icc (0:ℝ) 1) →
        ((∫ x in (0:ℝ)..1, f' x) = ∑ j ∈ Finset.range K, ∫ x in ((j:ℝ)/K)..(((j:ℝ)+1)/K), f' x) →
        (∀ j ∈ Finset.range K, ∀ x ∈ Set.Icc ((j:ℝ)/K) (((j:ℝ)+1)/K), |f' x - f' ((j:ℝ)/K)| ≤ ε) →
        |(∫ x in (0:ℝ)..1, f' x) - (1/K) * ∑ j ∈ Finset.range K, f' ((j:ℝ)/K)| ≤ ε) →
      (∀ f' : ℝ → ℝ, ContinuousOn f' (Set.Icc (0:ℝ) 1) →
        (∀ (K:ℕ), 0 < K → (∫ x in (0:ℝ)..1, f' x) = ∑ j ∈ Finset.range K, ∫ x in ((j:ℝ)/K)..(((j:ℝ)+1)/K), f' x) →
        (∀ (K:ℕ) (ε':ℝ), 0 < K → 0 ≤ ε' → ((∫ x in (0:ℝ)..1, f' x) = ∑ j ∈ Finset.range K, ∫ x in ((j:ℝ)/K)..(((j:ℝ)+1)/K), f' x) →
          (∀ j ∈ Finset.range K, ∀ x ∈ Set.Icc ((j:ℝ)/K) (((j:ℝ)+1)/K), |f' x - f' ((j:ℝ)/K)| ≤ ε') →
          |(∫ x in (0:ℝ)..1, f' x) - (1/K) * ∑ j ∈ Finset.range K, f' ((j:ℝ)/K)| ≤ ε') →
        Filter.Tendsto (fun K : ℕ => (1/(K:ℝ)) * ∑ j ∈ Finset.range K, f' ((j:ℝ)/K)) Filter.atTop (nhds (∫ x in (0:ℝ)..1, f' x))) →
      (∀ (f' : ℝ → ℝ) (s' t' : ℝ), (t' - s') * (∫ x in (0:ℝ)..1, f' ((t' - s') * x + s')) = ∫ v in s'..t', f' v) →
      (∀ (A : ℕ → ℝ) (W : ℕ → ℕ → ℝ) (mass : ℕ → ℝ) (L : ℝ),
        0 ≤ L → Filter.Tendsto mass Filter.atTop (nhds L) →
        (∀ η : ℝ, 0 < η → ∀ᶠ K in Filter.atTop, ∀ N : ℕ, |A N - W K N| ≤ η * mass N) →
        ∀ ε : ℝ, 0 < ε → ∀ᶠ K in Filter.atTop, ∀ᶠ N in Filter.atTop, |A N - W K N| ≤ ε) →
      (∀ m n : ℕ, m ≤ n → (harmonic n : ℝ) - (harmonic m : ℝ) = ∑ a ∈ Finset.Ioc m n, (1:ℝ) / (a:ℝ)) →
      (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x y : ℝ, |x - y| ≤ δ →
        |f (max (min t x) s) - f (max (min t y) s)| ≤ ε) →
      (∀ (s' t' x : ℝ), s' ≤ t' → x ∈ Set.Icc s' t' → max (min t' x) s' = x) →
      (∀ (N : ℕ) (v w : ℝ), 1 < (N:ℝ) → ∀ a : ℕ,
        a ∈ Finset.Ioc ⌊(N:ℝ)^v⌋₊ ⌊(N:ℝ)^w⌋₊ →
        v < Real.log (a:ℝ) / Real.log (N:ℝ) ∧ Real.log (a:ℝ) / Real.log (N:ℝ) ≤ w) →
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
      (∀ (f' : ℝ → ℝ) (s' t' : ℝ),
          (∀ (K : ℕ) (c : ℕ → ℝ) (g : ℕ → ℕ → ℝ) (L : ℕ → ℝ),
             (∀ j ∈ Finset.range K, Filter.Tendsto (fun N : ℕ => g N j) Filter.atTop (nhds (L j))) →
             Filter.Tendsto (fun N : ℕ => ∑ j ∈ Finset.range K, c j * g N j) Filter.atTop (nhds (∑ j ∈ Finset.range K, c j * L j))) →
          (∀ (K : ℕ), 0 < K → ∀ j : ℕ, j < K →
             Filter.Tendsto (fun N : ℕ => ((harmonic ⌊(N:ℝ) ^ (s' + (((j:ℝ)+1) / (K:ℝ)) * (t' - s'))⌋₊ : ℝ) - (harmonic ⌊(N:ℝ) ^ (s' + ((j:ℝ) / (K:ℝ)) * (t' - s'))⌋₊ : ℝ)) / Real.log (N:ℝ)) Filter.atTop (nhds ((t' - s') / (K:ℝ)))) →
          ∀ K : ℕ, Filter.Tendsto (fun N : ℕ => (∑ j ∈ Finset.range K, f' (s' + ((j:ℝ)/(K:ℝ))*(t'-s')) * ((harmonic ⌊(N:ℝ) ^ (s' + (((j:ℝ)+1)/(K:ℝ))*(t'-s'))⌋₊ : ℝ) - (harmonic ⌊(N:ℝ) ^ (s' + ((j:ℝ)/(K:ℝ))*(t'-s'))⌋₊ : ℝ))) / Real.log (N:ℝ)) Filter.atTop (nhds (∑ j ∈ Finset.range K, f' (s' + ((j:ℝ)/(K:ℝ))*(t'-s')) * ((t'-s')/(K:ℝ))))) →
      (∀ (f' : ℝ → ℝ) (s' t' : ℝ), s' ≤ t' → ContinuousOn f' (Set.Icc s' t') →
          (∀ (f'' : ℝ → ℝ) (s'' t'' : ℝ), s'' ≤ t'' → ContinuousOn f'' (Set.Icc s'' t'') →
            ContinuousOn (fun x => f'' (s'' + x*(t''-s'')) * (t''-s'')) (Set.Icc (0:ℝ) 1)) →
          (∀ (f'' : ℝ → ℝ) (K : ℕ), 0 < K → ContinuousOn f'' (Set.Icc (0:ℝ) 1) →
            (∑ j ∈ Finset.range K, ∫ x in ((j : ℝ)/K)..(((j : ℝ) + 1)/K), f'' x) = ∫ x in (0:ℝ)..1, f'' x) →
          (∀ (f'' : ℝ → ℝ) (K : ℕ) (ε : ℝ), 0 < K → 0 ≤ ε → ContinuousOn f'' (Set.Icc (0:ℝ) 1) →
            ((∫ x in (0:ℝ)..1, f'' x) = ∑ j ∈ Finset.range K, ∫ x in ((j:ℝ)/K)..(((j:ℝ)+1)/K), f'' x) →
            (∀ j ∈ Finset.range K, ∀ x ∈ Set.Icc ((j:ℝ)/K) (((j:ℝ)+1)/K), |f'' x - f'' ((j:ℝ)/K)| ≤ ε) →
            |(∫ x in (0:ℝ)..1, f'' x) - (1/K) * ∑ j ∈ Finset.range K, f'' ((j:ℝ)/K)| ≤ ε) →
          (∀ f'' : ℝ → ℝ, ContinuousOn f'' (Set.Icc (0:ℝ) 1) →
            (∀ (K:ℕ), 0 < K → (∫ x in (0:ℝ)..1, f'' x) = ∑ j ∈ Finset.range K, ∫ x in ((j:ℝ)/K)..(((j:ℝ)+1)/K), f'' x) →
            (∀ (K:ℕ) (ε':ℝ), 0 < K → 0 ≤ ε' → ((∫ x in (0:ℝ)..1, f'' x) = ∑ j ∈ Finset.range K, ∫ x in ((j:ℝ)/K)..(((j:ℝ)+1)/K), f'' x) →
              (∀ j ∈ Finset.range K, ∀ x ∈ Set.Icc ((j:ℝ)/K) (((j:ℝ)+1)/K), |f'' x - f'' ((j:ℝ)/K)| ≤ ε') →
              |(∫ x in (0:ℝ)..1, f'' x) - (1/K) * ∑ j ∈ Finset.range K, f'' ((j:ℝ)/K)| ≤ ε') →
            Filter.Tendsto (fun K : ℕ => (1/(K:ℝ)) * ∑ j ∈ Finset.range K, f'' ((j:ℝ)/K)) Filter.atTop (nhds (∫ x in (0:ℝ)..1, f'' x))) →
          (∀ (f'' : ℝ → ℝ) (s'' t'' : ℝ), (t'' - s'') * (∫ x in (0:ℝ)..1, f'' ((t'' - s'') * x + s'')) = ∫ v in s''..t'', f'' v) →
          Filter.Tendsto (fun K : ℕ => (1/(K:ℝ)) * ∑ j ∈ Finset.range K, (f' (s' + ((j:ℝ)/(K:ℝ))*(t'-s')) * (t'-s'))) Filter.atTop (nhds (∫ v in s'..t', f' v))) →
      (∀ (f' : ℝ → ℝ) (s' t' : ℝ), s' ≤ t' →
          (∀ (A : ℕ → ℝ) (W : ℕ → ℕ → ℝ) (mass : ℕ → ℝ) (L : ℝ),
            0 ≤ L → Filter.Tendsto mass Filter.atTop (nhds L) →
            (∀ η : ℝ, 0 < η → ∀ᶠ K in Filter.atTop, ∀ N : ℕ, |A N - W K N| ≤ η * mass N) →
            ∀ ε : ℝ, 0 < ε → ∀ᶠ K in Filter.atTop, ∀ᶠ N in Filter.atTop, |A N - W K N| ≤ ε) →
          (∀ (x y : ℝ), Filter.Tendsto (fun N : ℕ => ((harmonic ⌊(N:ℝ)^x⌋₊ : ℝ) - (harmonic ⌊(N:ℝ)^y⌋₊ : ℝ))/Real.log (N:ℝ)) Filter.atTop (nhds (x - y))) →
          (∀ m n : ℕ, m ≤ n → (harmonic n : ℝ) - (harmonic m : ℝ) = ∑ a ∈ Finset.Ioc m n, (1:ℝ) / (a:ℝ)) →
          (∀ η : ℝ, 0 < η → ∀ᶠ K in Filter.atTop, ∀ N : ℕ,
            |(∑ a ∈ Finset.Ioc ⌊(N:ℝ)^s'⌋₊ ⌊(N:ℝ)^t'⌋₊, f' (Real.log (a:ℝ) / Real.log (N:ℝ)) / (a:ℝ)) / Real.log (N:ℝ)
              - (∑ j ∈ Finset.range K, f' (s' + ((j:ℝ)/(K:ℝ))*(t'-s')) * ((harmonic ⌊(N:ℝ) ^ (s' + (((j:ℝ)+1)/(K:ℝ))*(t'-s'))⌋₊ : ℝ) - (harmonic ⌊(N:ℝ) ^ (s' + ((j:ℝ)/(K:ℝ))*(t'-s'))⌋₊ : ℝ))) / Real.log (N:ℝ)|
            ≤ η * ((∑ a ∈ Finset.Ioc ⌊(N:ℝ)^s'⌋₊ ⌊(N:ℝ)^t'⌋₊, 1/(a:ℝ)) / Real.log (N:ℝ))) →
          ∀ ε : ℝ, 0 < ε → ∀ᶠ K in Filter.atTop, ∀ᶠ (N : ℕ) in Filter.atTop,
            |(∑ a ∈ Finset.Ioc ⌊(N:ℝ)^s'⌋₊ ⌊(N:ℝ)^t'⌋₊, f' (Real.log (a:ℝ) / Real.log (N:ℝ)) / (a:ℝ)) / Real.log (N:ℝ)
              - (∑ j ∈ Finset.range K, f' (s' + ((j:ℝ)/(K:ℝ))*(t'-s')) * ((harmonic ⌊(N:ℝ) ^ (s' + (((j:ℝ)+1)/(K:ℝ))*(t'-s'))⌋₊ : ℝ) - (harmonic ⌊(N:ℝ) ^ (s' + ((j:ℝ)/(K:ℝ))*(t'-s'))⌋₊ : ℝ))) / Real.log (N:ℝ)| ≤ ε) →
      (∀ (f' : ℝ → ℝ) (s' t' : ℝ),
          s' ≤ t' → ContinuousOn f' (Set.Icc s' t') →
          (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x y : ℝ, |x - y| ≤ δ →
            |f' (max (min t' x) s') - f' (max (min t' y) s')| ≤ ε) →
          (∀ (s'' t'' x : ℝ), s'' ≤ t'' → x ∈ Set.Icc s'' t'' → max (min t'' x) s'' = x) →
          (∀ (N : ℕ) (v w : ℝ), 1 < (N:ℝ) → ∀ a : ℕ,
            a ∈ Finset.Ioc ⌊(N:ℝ)^v⌋₊ ⌊(N:ℝ)^w⌋₊ →
            v < Real.log (a:ℝ) / Real.log (N:ℝ) ∧ Real.log (a:ℝ) / Real.log (N:ℝ) ≤ w) →
          (∀ m n : ℕ, m ≤ n → (harmonic n : ℝ) - (harmonic m : ℝ) = ∑ a ∈ Finset.Ioc m n, (1:ℝ) / (a:ℝ)) →
          (∀ (G : ℝ → ℝ) (s'' t'' : ℝ) (N K : ℕ) (δ' η : ℝ),
              s'' ≤ t'' → 1 < (N:ℝ) → 0 < K →
              (∀ x y : ℝ, |x - y| ≤ δ' → |G x - G y| ≤ η) →
              ((t'' - s'')/(K:ℝ) ≤ δ') →
              (∀ (G' : ℝ → ℝ) (h : ℕ → ℝ) (N' K' : ℕ) (δ'' ε'' : ℝ) (v : ℕ → ℝ),
                  1 < (N':ℝ) → (∀ k : ℕ, 0 ≤ h k) → (∀ x y : ℝ, |x - y| ≤ δ'' → |G' x - G' y| ≤ ε'') →
                  (∀ j : ℕ, v j ≤ v (j + 1)) → (∀ j : ℕ, j < K' → v (j + 1) - v j ≤ δ'') →
                  Monotone (fun j => ⌊(N':ℝ) ^ (v j)⌋₊) →
                  |(∑ a ∈ Finset.Ioc ⌊(N':ℝ) ^ (v 0)⌋₊ ⌊(N':ℝ) ^ (v K')⌋₊, G' (Real.log (a:ℝ) / Real.log (N':ℝ)) * h a)
                    - (∑ j ∈ Finset.range K', G' (v j) * (∑ a ∈ Finset.Ioc ⌊(N':ℝ) ^ (v j)⌋₊ ⌊(N':ℝ) ^ (v (j+1))⌋₊, h a))|
                  ≤ ε'' * (∑ a ∈ Finset.Ioc ⌊(N':ℝ) ^ (v 0)⌋₊ ⌊(N':ℝ) ^ (v K')⌋₊, h a)) →
              |(∑ a ∈ Finset.Ioc ⌊(N:ℝ)^s''⌋₊ ⌊(N:ℝ)^t''⌋₊, G (Real.log (a:ℝ) / Real.log (N:ℝ)) * (1/(a:ℝ)))
                - (∑ j ∈ Finset.range K, G (s'' + ((j:ℝ)/(K:ℝ))*(t''-s'')) * (∑ a ∈ Finset.Ioc ⌊(N:ℝ)^(s'' + ((j:ℝ)/(K:ℝ))*(t''-s''))⌋₊ ⌊(N:ℝ)^(s'' + (((j:ℝ)+1)/(K:ℝ))*(t''-s''))⌋₊, (1/(a:ℝ))))|
              ≤ η * (∑ a ∈ Finset.Ioc ⌊(N:ℝ)^s''⌋₊ ⌊(N:ℝ)^t''⌋₊, (1/(a:ℝ)))) →
          (∀ (G' : ℝ → ℝ) (h : ℕ → ℝ) (N' K' : ℕ) (δ'' ε'' : ℝ) (v : ℕ → ℝ),
              1 < (N':ℝ) → (∀ k : ℕ, 0 ≤ h k) → (∀ x y : ℝ, |x - y| ≤ δ'' → |G' x - G' y| ≤ ε'') →
              (∀ j : ℕ, v j ≤ v (j + 1)) → (∀ j : ℕ, j < K' → v (j + 1) - v j ≤ δ'') →
              Monotone (fun j => ⌊(N':ℝ) ^ (v j)⌋₊) →
              |(∑ a ∈ Finset.Ioc ⌊(N':ℝ) ^ (v 0)⌋₊ ⌊(N':ℝ) ^ (v K')⌋₊, G' (Real.log (a:ℝ) / Real.log (N':ℝ)) * h a)
                - (∑ j ∈ Finset.range K', G' (v j) * (∑ a ∈ Finset.Ioc ⌊(N':ℝ) ^ (v j)⌋₊ ⌊(N':ℝ) ^ (v (j+1))⌋₊, h a))|
              ≤ ε'' * (∑ a ∈ Finset.Ioc ⌊(N':ℝ) ^ (v 0)⌋₊ ⌊(N':ℝ) ^ (v K')⌋₊, h a)) →
          (∀ (A W mass L ε : ℝ), 0 < L → |A - W| ≤ ε * mass → |A/L - W/L| ≤ ε * (mass/L)) →
          ∀ ε : ℝ, 0 < ε → ∀ᶠ K in Filter.atTop, ∀ N : ℕ,
            |(∑ a ∈ Finset.Ioc ⌊(N:ℝ)^s'⌋₊ ⌊(N:ℝ)^t'⌋₊, f' (Real.log (a:ℝ) / Real.log (N:ℝ)) / (a:ℝ)) / Real.log (N:ℝ)
              - (∑ j ∈ Finset.range K, f' (s' + ((j:ℝ)/(K:ℝ))*(t'-s')) * ((harmonic ⌊(N:ℝ) ^ (s' + (((j:ℝ)+1)/(K:ℝ))*(t'-s'))⌋₊ : ℝ) - (harmonic ⌊(N:ℝ) ^ (s' + ((j:ℝ)/(K:ℝ))*(t'-s'))⌋₊ : ℝ))) / Real.log (N:ℝ)|
            ≤ ε * ((∑ a ∈ Finset.Ioc ⌊(N:ℝ)^s'⌋₊ ⌊(N:ℝ)^t'⌋₊, 1/(a:ℝ)) / Real.log (N:ℝ))) →
      (∀ (f' : ℝ → ℝ) (s' t' L : ℝ),
          (∀ (W : ℕ → ℕ → ℝ) (R : ℕ → ℝ) (L' : ℝ) (A : ℕ → ℝ),
            (∀ K : ℕ, Filter.Tendsto (fun N => W K N) Filter.atTop (nhds (R K))) →
            Filter.Tendsto R Filter.atTop (nhds L') →
            (∀ ε : ℝ, 0 < ε → ∀ᶠ K in Filter.atTop, ∀ᶠ N in Filter.atTop, |A N - W K N| ≤ ε) →
            Filter.Tendsto A Filter.atTop (nhds L')) →
          (∀ K : ℕ, Filter.Tendsto (fun N : ℕ => (∑ j ∈ Finset.range K, f' (s' + ((j:ℝ) / (K:ℝ)) * (t' - s')) * ((harmonic ⌊(N:ℝ) ^ (s' + (((j:ℝ) + 1) / (K:ℝ)) * (t' - s'))⌋₊ : ℝ) - (harmonic ⌊(N:ℝ) ^ (s' + ((j:ℝ) / (K:ℝ)) * (t' - s'))⌋₊ : ℝ))) / Real.log (N:ℝ)) Filter.atTop (nhds (∑ j ∈ Finset.range K, f' (s' + ((j:ℝ) / (K:ℝ)) * (t' - s')) * ((t' - s') / (K:ℝ))))) →
          Filter.Tendsto (fun K : ℕ => ∑ j ∈ Finset.range K, f' (s' + ((j:ℝ) / (K:ℝ)) * (t' - s')) * ((t' - s') / (K:ℝ))) Filter.atTop (nhds L) →
          (∀ ε : ℝ, 0 < ε → ∀ᶠ K : ℕ in Filter.atTop, ∀ᶠ N : ℕ in Filter.atTop,
            |(∑ a ∈ Finset.Ioc ⌊(N:ℝ)^s'⌋₊ ⌊(N:ℝ)^t'⌋₊, f' (Real.log (a:ℝ) / Real.log (N:ℝ)) / (a:ℝ)) / Real.log (N:ℝ)
              - (∑ j ∈ Finset.range K, f' (s' + ((j:ℝ) / (K:ℝ)) * (t' - s')) * ((harmonic ⌊(N:ℝ) ^ (s' + (((j:ℝ) + 1) / (K:ℝ)) * (t' - s'))⌋₊ : ℝ) - (harmonic ⌊(N:ℝ) ^ (s' + ((j:ℝ) / (K:ℝ)) * (t' - s'))⌋₊ : ℝ))) / Real.log (N:ℝ)| ≤ ε) →
          Filter.Tendsto (fun N : ℕ => (∑ a ∈ Finset.Ioc ⌊(N:ℝ)^s'⌋₊ ⌊(N:ℝ)^t'⌋₊, f' (Real.log (a:ℝ) / Real.log (N:ℝ)) / (a:ℝ)) / Real.log (N:ℝ)) Filter.atTop (nhds L)) →
      Filter.Tendsto (fun N : ℕ => (∑ a ∈ Finset.Ioc ⌊(N:ℝ)^s⌋₊ ⌊(N:ℝ)^t⌋₊, f (Real.log (a:ℝ) / Real.log (N:ℝ)) / (a:ℝ)) / Real.log (N:ℝ)) Filter.atTop (nhds (∫ v in s..t, f v)) := by
  intro f s t hst hf h102 h100 h99 h167 h93 h96 h97 h165 h140 hharmdiff h149 hclampid hmembership h170 h136 hdiv hHW_thm hHRDischarge_thm hHerrTrue_thm hHerrWired_thm hIntervalTransfer_thm
  have hmass : ∀ (K : ℕ), 0 < K → ∀ j : ℕ, j < K →
      Filter.Tendsto (fun N : ℕ => ((harmonic ⌊(N:ℝ) ^ (s + (((j:ℝ)+1) / (K:ℝ)) * (t - s))⌋₊ : ℝ) - (harmonic ⌊(N:ℝ) ^ (s + ((j:ℝ) / (K:ℝ)) * (t - s))⌋₊ : ℝ)) / Real.log (N:ℝ)) Filter.atTop (nhds ((t - s) / (K:ℝ))) := (by
    intro K hK j hj
    have hKne : (K:ℝ) ≠ 0 := (by have h1 : K ≠ 0 := (by omega); exact_mod_cast h1)
    have h99inst := h99 (s + (((j:ℝ)+1) / (K:ℝ)) * (t - s)) (s + ((j:ℝ) / (K:ℝ)) * (t - s))
    have heq : (s + (((j:ℝ)+1) / (K:ℝ)) * (t - s)) - (s + ((j:ℝ) / (K:ℝ)) * (t - s)) = (t - s) / (K:ℝ) := (by field_simp; ring)
    rw [heq] at h99inst
    exact h99inst)
  have hW := hHW_thm f s t h100 hmass
  have hR0 := hHRDischarge_thm f s t hst hf h167 h93 h96 h97 h165
  have hR : Filter.Tendsto (fun K : ℕ => ∑ j ∈ Finset.range K, f (s + ((j:ℝ) / (K:ℝ)) * (t - s)) * ((t - s) / (K:ℝ))) Filter.atTop (nhds (∫ v in s..t, f v)) := (by
    have heq : (fun K:ℕ => (1/(K:ℝ)) * ∑ j ∈ Finset.range K, (f (s+((j:ℝ)/(K:ℝ))*(t-s)) * (t-s))) = (fun K:ℕ => ∑ j ∈ Finset.range K, f (s+((j:ℝ)/(K:ℝ))*(t-s)) * ((t-s)/(K:ℝ))) := (funext (fun K => by rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _ => by ring)))
    exact heq ▸ hR0)
  have hAgg := hHerrWired_thm f s t hst hf h149 hclampid hmembership hharmdiff h170 h136 hdiv
  have herr := hHerrTrue_thm f s t hst h140 h99 hharmdiff hAgg
  exact hIntervalTransfer_thm f s t (∫ v in s..t, f v) h102 hW hR herr

end Erdos858
