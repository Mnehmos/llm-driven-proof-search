/-
Erdős Problem #858 — §5.3 CAPSTONE: the prime block-mass limit (Chojecki 2026).

`prime block-mass limit` (final Tendsto assembly, fully generic): given
  (i)   the interval-Mertens identity `S(m,n) = [A(n)/log n − A(m)/log m] +
        [loglog n − loglog m] + E(m,n)` for `2 ≤ m ≤ n` (from #125 + #126),
  (ii)  the tail bound `|E(m,n)| ≤ D/log m` (from #123),
  (iii) the floor log-ratio limits (#91's family),
  (iv)  the loglog floor limits (#127, implication form),
  (v)   the boundary-ratio limits (composed #128 form),
then for `0 < s ≤ t`:

  `S(⌊N^s⌋, ⌊N^t⌋)  →  log t − log s`   as `N → ∞`.

Instantiated at `S(m,n) = Σ_{m<p≤n} 1/p` and `A(k) = Σ_{p≤k} log p/p` (with
`E(m,n) = ∫_{(m,n]} (A(⌊u⌋) − log u)/(u·log²u)` and `D = C + log 2` from the
Mertens-1 remainder bound), this is

  `Σ_{N^s<p≤N^t} 1/p  →  log(t/s)`

— the §5.3 PRIME BLOCK MASSES: the prime-harmonic sums converge to the
`dv/v`-measure of the geometric block, exactly the mass input the §5.4
transfer engine (#100/#102/#103/#105) needs to run the prime-harmonic
Riemann-sum argument of Lemma 5.3, toward the asymptotic law Theorem 1.2.

The complete verified chain behind the hypotheses:
#117 (generic Abel) → #118 (prime split) → #125 (interval identity, via
#121/#122/#124) → #126 (main-term extraction, via #120) → #123 (tail, via
#119) → #127/#128 (endpoint limits, via the #91-chain) → this assembly.

Kernel-verified via the proofsearch MCP:
  episode cd23cc70-8052-4251-a16a-faa9d1ac3db7,
  problem_version_id 4a79f436-20d6-4b63-9c59-ee791ec946b5.
Outcome: kernel_verified / root_kernel_verified (1st submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 7701d9f574f4f5bf7b8d6c086412672da5d5ce0d828d7c9c401d1a0b1981dd42.
-/
import Mathlib

namespace Erdos858

/-- §5.3 CAPSTONE (prime block-mass limit, generic assembly): the
interval-Mertens identity + tail bound + endpoint limits imply
`S(⌊N^s⌋, ⌊N^t⌋) → log t − log s` for `0 < s ≤ t`. At the prime instantiation:
`Σ_{N^s<p≤N^t} 1/p → log(t/s)` — the §5.3 prime block masses. -/
theorem erdos858_prime_block_mass_limit :
    ∀ (S : ℕ → ℕ → ℝ) (A : ℕ → ℝ) (E : ℕ → ℕ → ℝ) (D : ℝ) (s t : ℝ), 0 < s → s ≤ t →
      (∀ m n : ℕ, 2 ≤ m → m ≤ n → S m n = (A n / Real.log (n:ℝ) - A m / Real.log (m:ℝ)) + (Real.log (Real.log (n:ℝ)) - Real.log (Real.log (m:ℝ))) + E m n) →
      (∀ m n : ℕ, 2 ≤ m → m ≤ n → |E m n| ≤ D / Real.log (m:ℝ)) →
      (∀ x : ℝ, 0 < x → Filter.Tendsto (fun N : ℕ => Real.log ((⌊(N:ℝ)^x⌋₊ : ℝ)) / Real.log (N:ℝ)) Filter.atTop (nhds x)) →
      (∀ x : ℝ, 0 < x → Filter.Tendsto (fun N : ℕ => Real.log ((⌊(N:ℝ)^x⌋₊ : ℝ)) / Real.log (N:ℝ)) Filter.atTop (nhds x) → Filter.Tendsto (fun N : ℕ => Real.log (Real.log ((⌊(N:ℝ)^x⌋₊ : ℝ))) - Real.log (Real.log (N:ℝ))) Filter.atTop (nhds (Real.log x))) →
      (∀ x : ℝ, 0 < x → Filter.Tendsto (fun N : ℕ => A ⌊(N:ℝ)^x⌋₊ / Real.log ((⌊(N:ℝ)^x⌋₊ : ℝ)) - 1) Filter.atTop (nhds 0)) →
      Filter.Tendsto (fun N : ℕ => S ⌊(N:ℝ)^s⌋₊ ⌊(N:ℝ)^t⌋₊) Filter.atTop (nhds (Real.log t - Real.log s)) := by
  intro S A E D s t hs hst hID hE h91 h127 hAr
  have ht : 0 < t := lt_of_lt_of_le hs hst
  have hNxs : Filter.Tendsto (fun N : ℕ => (N:ℝ)^s) Filter.atTop Filter.atTop := (tendsto_rpow_atTop hs).comp tendsto_natCast_atTop_atTop
  have hfloors : Filter.Tendsto (fun N : ℕ => ⌊(N:ℝ)^s⌋₊) Filter.atTop Filter.atTop := tendsto_nat_floor_atTop.comp hNxs
  have hlogTs : Filter.Tendsto (fun N : ℕ => Real.log ((⌊(N:ℝ)^s⌋₊ : ℝ))) Filter.atTop Filter.atTop := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hfloors)
  have h1 := (hAr t ht).sub (hAr s hs)
  have h2 := (h127 t ht (h91 t ht)).sub (h127 s hs (h91 s hs))
  have hg : Filter.Tendsto (fun N : ℕ => D / Real.log ((⌊(N:ℝ)^s⌋₊ : ℝ))) Filter.atTop (nhds 0) := tendsto_const_nhds.div_atTop hlogTs
  have hev2s : ∀ᶠ N : ℕ in Filter.atTop, 2 ≤ ⌊(N:ℝ)^s⌋₊ := hfloors.eventually_ge_atTop 2
  have hevN1 : ∀ᶠ N : ℕ in Filter.atTop, 1 ≤ N := Filter.eventually_ge_atTop 1
  have hevmono : ∀ᶠ N : ℕ in Filter.atTop, ⌊(N:ℝ)^s⌋₊ ≤ ⌊(N:ℝ)^t⌋₊ := by filter_upwards [hevN1] with N hN1; exact Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1) hst)
  have hevE : ∀ᶠ N : ℕ in Filter.atTop, ‖E ⌊(N:ℝ)^s⌋₊ ⌊(N:ℝ)^t⌋₊‖ ≤ D / Real.log ((⌊(N:ℝ)^s⌋₊ : ℝ)) := by filter_upwards [hev2s, hevmono] with N h2s hmn; rw [Real.norm_eq_abs]; exact hE ⌊(N:ℝ)^s⌋₊ ⌊(N:ℝ)^t⌋₊ h2s hmn
  have hE0 : Filter.Tendsto (fun N : ℕ => E ⌊(N:ℝ)^s⌋₊ ⌊(N:ℝ)^t⌋₊) Filter.atTop (nhds 0) := squeeze_zero_norm' hevE hg
  have hsum := (h1.add h2).add hE0
  have hval : ((0:ℝ) - 0) + (Real.log t - Real.log s) + 0 = Real.log t - Real.log s := (by ring)
  rw [hval] at hsum
  refine hsum.congr' ?_
  filter_upwards [hev2s, hevmono] with N h2s hmn
  rw [hID ⌊(N:ℝ)^s⌋₊ ⌊(N:ℝ)^t⌋₊ h2s hmn]
  ring

end Erdos858
