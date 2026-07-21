/-
Erdős Problem #858 — §5.4 log-harmonic transfer, concrete instantiation atom 2 (Chojecki 2026).

`fixed-K,N log-harmonic error bound` (the big assembly): combining the concrete
per-block sum bound (#108), the aggregation theorem (#101), the discrete
partition identity (#103), and the harmonic-difference connector (#107) as
hypotheses (conditional assembly), derives the full fixed-parameter error bound:
for `f` with a δ-ε modulus of continuity at scale `1/K ≤ δ`, `N > 1`, `K > 0`,

  `|Σ_{1<a≤N} f(log a/log N)/a  −  Σ_{j<K} f(j/K)·m_j|  ≤  ε·(harmonic N − harmonic 1)`,

where `m_j = harmonic(⌊N^{(j+1)/K}⌋) − harmonic(⌊N^{j/K}⌋)`. After normalizing by
`log N` and letting `N → ∞` (harmonic N ∼ log N), this becomes the `herr`
hypothesis of the diagonal squeeze (#102), closing the gap to the full concrete
log-harmonic Riemann theorem `(1/log N) Σ_{1<a≤N} f(u_a)/a → ∫₀¹ f`.

Proof: the per-block bounds (#108) aggregate over `j < K` via #101; the total
true sum is identified with the block sums via the partition identity #103
instantiated at `e j = ⌊N^{j/K}⌋₊` with `h = f(u)/a` (endpoints: `e 0 = ⌊N^0⌋ = 1`
via `zero_div`+`rpow_zero`+`floor_one`, `e K = ⌊N^1⌋ = N` via `div_self`+
`rpow_one`+`floor_natCast`); the total mass telescopes to `harmonic N − harmonic 1`
via #103 again (`h = 1/a`) + #107 per block and at the endpoints. Elementary, no PNT.

Kernel-verified via the proofsearch MCP:
  episode 2ce4f3d4-789f-4e42-abc3-ef154ddb0d60,
  problem_version_id f83ccfe0-216d-4f17-a124-65fe9b28ad3b.
Outcome: kernel_verified / root_kernel_verified (2nd submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 715a983d8f001505ad9f0e07f969469d43b0185ae423184d84a44cae1e77ab3e.

**Lean lessons (two new, from the 1st-submission failure)**:
1. `set x := v with h` introduces an OPAQUE local constant (cdecl) plus an
   equation — NOT a transparent let. Terms built from hypotheses come out in
   raw form and refuse to unify with `set`-name forms; `set` is unusable for
   function abbreviations in term-mode assemblies. Use raw expressions plus
   explicitly-ascribed `have`s (beta-only defeq) instead.
2. `push_cast at h` on an instantiated ∀-fact both normalizes casts
   (`↑(j+1) → ↑j+1`, `↑0 → 0`) AND beta-reduces the lambda redexes left by
   instantiation (simp-based) — the canonical bridge when a generic lemma
   instantiated with a lambda must match a goal stated in cast-distributed form.
   Also: `gcongr` alone proves `↑j₁/↑K ≤ ↑j₂/↑K` from `j₁ ≤ j₂` in context.
-/
import Mathlib

namespace Erdos858

/-- Concrete instantiation atom 2 (fixed-K,N log-harmonic error bound):
assembling #108 (per-block bound) + #101 (aggregation) + #103 (partition, used
twice) + #107 (mass connector), the true log-harmonic sum over `(1,N]` is within
`ε·(harmonic N − harmonic 1)` of the weighted block step-sum. The fixed-parameter
form of the transfer error — becomes #102's `herr` after `log N` normalization. -/
theorem erdos858_fixed_KN_transfer_bound :
    (∀ (f : ℝ → ℝ) (N K j : ℕ) (δ ε : ℝ),
      1 < (N:ℝ) → 0 < K → j < K → (1:ℝ) / (K:ℝ) ≤ δ →
      (∀ x y : ℝ, |x - y| ≤ δ → |f x - f y| ≤ ε) →
      |(∑ a ∈ Finset.Ioc (⌊(N:ℝ) ^ ((j:ℝ) / (K:ℝ))⌋₊) (⌊(N:ℝ) ^ (((j:ℝ) + 1) / (K:ℝ))⌋₊), f (Real.log (a:ℝ) / Real.log (N:ℝ)) / (a:ℝ))
        - f ((j:ℝ) / (K:ℝ)) * ((harmonic ⌊(N:ℝ) ^ (((j:ℝ) + 1) / (K:ℝ))⌋₊ : ℝ) - (harmonic ⌊(N:ℝ) ^ ((j:ℝ) / (K:ℝ))⌋₊ : ℝ))|
      ≤ ε * ((harmonic ⌊(N:ℝ) ^ (((j:ℝ) + 1) / (K:ℝ))⌋₊ : ℝ) - (harmonic ⌊(N:ℝ) ^ ((j:ℝ) / (K:ℝ))⌋₊ : ℝ))) →
    (∀ (K : ℕ) (S w m : ℕ → ℝ) (ε : ℝ),
      (∀ j ∈ Finset.range K, |S j - w j * m j| ≤ ε * m j) →
      |(∑ j ∈ Finset.range K, S j) - (∑ j ∈ Finset.range K, w j * m j)| ≤ ε * (∑ j ∈ Finset.range K, m j)) →
    (∀ (K : ℕ) (e : ℕ → ℕ), Monotone e → ∀ (h : ℕ → ℝ),
      ∑ j ∈ Finset.range K, ∑ a ∈ Finset.Ioc (e j) (e (j + 1)), h a = ∑ a ∈ Finset.Ioc (e 0) (e K), h a) →
    (∀ m n : ℕ, m ≤ n →
      (harmonic n : ℝ) - (harmonic m : ℝ) = ∑ a ∈ Finset.Ioc m n, (1:ℝ) / (a:ℝ)) →
    ∀ (f : ℝ → ℝ) (N K : ℕ) (δ ε : ℝ),
      1 < (N:ℝ) → 0 < K → (1:ℝ) / (K:ℝ) ≤ δ →
      (∀ x y : ℝ, |x - y| ≤ δ → |f x - f y| ≤ ε) →
      |(∑ a ∈ Finset.Ioc 1 N, f (Real.log (a:ℝ) / Real.log (N:ℝ)) / (a:ℝ))
        - (∑ j ∈ Finset.range K, f ((j:ℝ) / (K:ℝ)) * ((harmonic ⌊(N:ℝ) ^ (((j:ℝ) + 1) / (K:ℝ))⌋₊ : ℝ) - (harmonic ⌊(N:ℝ) ^ ((j:ℝ) / (K:ℝ))⌋₊ : ℝ)))|
      ≤ ε * ((harmonic N : ℝ) - (harmonic 1 : ℝ)) := by
  intro hpb hagg hpart hharmdiff f N K δ ε hN hK hKd hmod
  have hN' : 1 < N := by exact_mod_cast hN
  have hKrne : (K:ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  have hmono_e : Monotone (fun j : ℕ => ⌊(N:ℝ) ^ ((j:ℝ) / (K:ℝ))⌋₊) := fun j1 j2 hj12 => Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le (by linarith : (1:ℝ) ≤ (N:ℝ)) (by gcongr))
  have hexp_le : ∀ j : ℕ, (j:ℝ) / (K:ℝ) ≤ ((j:ℝ) + 1) / (K:ℝ) := fun j => by rw [add_div]; linarith [show (0:ℝ) ≤ 1 / (K:ℝ) from by positivity]
  have hmonoj : ∀ j : ℕ, ⌊(N:ℝ) ^ ((j:ℝ) / (K:ℝ))⌋₊ ≤ ⌊(N:ℝ) ^ (((j:ℝ) + 1) / (K:ℝ))⌋₊ := fun j => Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le (by linarith : (1:ℝ) ≤ (N:ℝ)) (hexp_le j))
  have hpbAll : ∀ j ∈ Finset.range K, |(∑ a ∈ Finset.Ioc (⌊(N:ℝ) ^ ((j:ℝ) / (K:ℝ))⌋₊) (⌊(N:ℝ) ^ (((j:ℝ) + 1) / (K:ℝ))⌋₊), f (Real.log (a:ℝ) / Real.log (N:ℝ)) / (a:ℝ)) - f ((j:ℝ) / (K:ℝ)) * ((harmonic ⌊(N:ℝ) ^ (((j:ℝ) + 1) / (K:ℝ))⌋₊ : ℝ) - (harmonic ⌊(N:ℝ) ^ ((j:ℝ) / (K:ℝ))⌋₊ : ℝ))| ≤ ε * ((harmonic ⌊(N:ℝ) ^ (((j:ℝ) + 1) / (K:ℝ))⌋₊ : ℝ) - (harmonic ⌊(N:ℝ) ^ ((j:ℝ) / (K:ℝ))⌋₊ : ℝ)) := fun j hj => hpb f N K j δ ε hN hK (Finset.mem_range.mp hj) hKd hmod
  have hagg2 : |(∑ j ∈ Finset.range K, ∑ a ∈ Finset.Ioc (⌊(N:ℝ) ^ ((j:ℝ) / (K:ℝ))⌋₊) (⌊(N:ℝ) ^ (((j:ℝ) + 1) / (K:ℝ))⌋₊), f (Real.log (a:ℝ) / Real.log (N:ℝ)) / (a:ℝ)) - (∑ j ∈ Finset.range K, f ((j:ℝ) / (K:ℝ)) * ((harmonic ⌊(N:ℝ) ^ (((j:ℝ) + 1) / (K:ℝ))⌋₊ : ℝ) - (harmonic ⌊(N:ℝ) ^ ((j:ℝ) / (K:ℝ))⌋₊ : ℝ)))| ≤ ε * (∑ j ∈ Finset.range K, ((harmonic ⌊(N:ℝ) ^ (((j:ℝ) + 1) / (K:ℝ))⌋₊ : ℝ) - (harmonic ⌊(N:ℝ) ^ ((j:ℝ) / (K:ℝ))⌋₊ : ℝ))) := hagg K (fun j => ∑ a ∈ Finset.Ioc (⌊(N:ℝ) ^ ((j:ℝ) / (K:ℝ))⌋₊) (⌊(N:ℝ) ^ (((j:ℝ) + 1) / (K:ℝ))⌋₊), f (Real.log (a:ℝ) / Real.log (N:ℝ)) / (a:ℝ)) (fun j => f ((j:ℝ) / (K:ℝ))) (fun j => (harmonic ⌊(N:ℝ) ^ (((j:ℝ) + 1) / (K:ℝ))⌋₊ : ℝ) - (harmonic ⌊(N:ℝ) ^ ((j:ℝ) / (K:ℝ))⌋₊ : ℝ)) ε hpbAll
  have hpartS := hpart K (fun j : ℕ => ⌊(N:ℝ) ^ ((j:ℝ) / (K:ℝ))⌋₊) hmono_e (fun a => f (Real.log (a:ℝ) / Real.log (N:ℝ)) / (a:ℝ))
  have hpartM := hpart K (fun j : ℕ => ⌊(N:ℝ) ^ ((j:ℝ) / (K:ℝ))⌋₊) hmono_e (fun a => (1:ℝ) / (a:ℝ))
  push_cast at hpartS hpartM
  have hend0 : ⌊(N:ℝ) ^ ((0:ℝ) / (K:ℝ))⌋₊ = 1 := by rw [zero_div, Real.rpow_zero, Nat.floor_one]
  have hendK : ⌊(N:ℝ) ^ ((K:ℝ) / (K:ℝ))⌋₊ = N := by rw [div_self hKrne, Real.rpow_one, Nat.floor_natCast]
  rw [hend0, hendK] at hpartS hpartM
  have hmjeq : ∀ j : ℕ, (harmonic ⌊(N:ℝ) ^ (((j:ℝ) + 1) / (K:ℝ))⌋₊ : ℝ) - (harmonic ⌊(N:ℝ) ^ ((j:ℝ) / (K:ℝ))⌋₊ : ℝ) = ∑ a ∈ Finset.Ioc (⌊(N:ℝ) ^ ((j:ℝ) / (K:ℝ))⌋₊) (⌊(N:ℝ) ^ (((j:ℝ) + 1) / (K:ℝ))⌋₊), (1:ℝ) / (a:ℝ) := fun j => hharmdiff _ _ (hmonoj j)
  have hsummjeq : (∑ j ∈ Finset.range K, ((harmonic ⌊(N:ℝ) ^ (((j:ℝ) + 1) / (K:ℝ))⌋₊ : ℝ) - (harmonic ⌊(N:ℝ) ^ ((j:ℝ) / (K:ℝ))⌋₊ : ℝ))) = ∑ j ∈ Finset.range K, ∑ a ∈ Finset.Ioc (⌊(N:ℝ) ^ ((j:ℝ) / (K:ℝ))⌋₊) (⌊(N:ℝ) ^ (((j:ℝ) + 1) / (K:ℝ))⌋₊), (1:ℝ) / (a:ℝ) := Finset.sum_congr rfl (fun j _ => hmjeq j)
  have htotalmass : (∑ j ∈ Finset.range K, ((harmonic ⌊(N:ℝ) ^ (((j:ℝ) + 1) / (K:ℝ))⌋₊ : ℝ) - (harmonic ⌊(N:ℝ) ^ ((j:ℝ) / (K:ℝ))⌋₊ : ℝ))) = (harmonic N : ℝ) - (harmonic 1 : ℝ) := by rw [hsummjeq, hpartM]; exact (hharmdiff 1 N hN'.le).symm
  rw [hpartS] at hagg2
  rw [htotalmass] at hagg2
  exact hagg2

end Erdos858
