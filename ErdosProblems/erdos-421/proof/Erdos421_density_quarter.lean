/-
Erdos Problem #421 -- density-1/4 partial result (self-authored sub-goal).

Snapshot of the kernel-verified construction, reconstructed from the three
proofsearch MCP episode_step submissions (obligations O_1446cf16b3e14f8c,
O_83c289dc5c4649bc, and the root assembly) in episode
0f5562fe-e14f-41b9-9f7b-ac11485a1be6, problem_version_id
49ca0931-9dd1-4e06-85bf-0afc3aa1cb99. Toolchain: leanprover/lean4:v4.32.0-rc1
+ mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56 (per environment_describe).

Claim: the sequence d(n) = 4n+2 (naturals == 2 mod 4) is strictly
increasing, starts >= 1, has natural density 1/4, and has all
consecutive-index-block products pairwise distinct -- the property Erdos
#421 asks for, realized at density 1/4 instead of the open density-1 case.
-/

open scoped BigOperators

section Erdos421DensityQuarter

/-- The structural half: strict monotonicity, positivity, and the
consecutive-block-product injectivity property. Proved via a 2-adic
valuation argument (every term has valuation exactly 1, forcing equal
block length) plus a `Finset.image_add_left_Icc` reindexing argument
(fixed-length block products are strictly increasing in start index). -/
theorem structural :
    StrictMono (fun n : ℕ => 4 * n + 2) ∧ 1 ≤ (4 * 0 + 2 : ℕ) ∧
      {p : ℕ × ℕ | p.1 ≤ p.2}.InjOn (fun p => ∏ i ∈ Finset.Icc p.1 p.2, (4 * i + 2)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b hab
    show 4 * a + 2 < 4 * b + 2
    omega
  · norm_num
  · intro p hp q hq hfpq
    have hp' : p.1 ≤ p.2 := hp
    have hq' : q.1 ≤ q.2 := hq
    have hfpq' : ∏ i ∈ Finset.Icc p.1 p.2, (4 * i + 2) = ∏ i ∈ Finset.Icc q.1 q.2, (4 * i + 2) := hfpq
    have hval : ∀ n : ℕ, (4 * n + 2).factorization 2 = 1 := by
      intro n
      have heq : 4 * n + 2 = 2 * (2 * n + 1) := by ring
      rw [heq, Nat.factorization_mul (by norm_num) (by omega), Finsupp.add_apply]
      have h2 : (2 : ℕ).factorization 2 = 1 := Nat.Prime.factorization_self Nat.prime_two
      have h3 : (2 * n + 1).factorization 2 = 0 :=
        Nat.factorization_eq_zero_of_not_dvd (by rw [Nat.dvd_iff_mod_eq_zero]; omega)
      rw [h2, h3]
    have hne : ∀ n : ℕ, (4 * n + 2 : ℕ) ≠ 0 := by intro n; omega
    have hcard : ∀ u v : ℕ, (∏ i ∈ Finset.Icc u v, (4 * i + 2)).factorization 2 = (Finset.Icc u v).card := by
      intro u v
      rw [Nat.factorization_prod_apply (fun i _ => hne i)]
      have hsum : (Finset.Icc u v).sum (fun i => (4 * i + 2).factorization 2) = (Finset.Icc u v).sum (fun _ => 1) :=
        Finset.sum_congr rfl (fun i _ => hval i)
      rw [hsum]
      simp
    have hlen : (Finset.Icc p.1 p.2).card = (Finset.Icc q.1 q.2).card := by
      rw [← hcard p.1 p.2, ← hcard q.1 q.2, hfpq']
    rw [Nat.card_Icc, Nat.card_Icc] at hlen
    rcases lt_trichotomy p.1 q.1 with hlt | heqv | hgt
    · exfalso
      have hL : p.2 - p.1 = q.2 - q.1 := by omega
      set L := p.2 - p.1 with hLdef
      have hp2 : p.2 = p.1 + L := by omega
      have hq2 : q.2 = q.1 + L := by omega
      have himg : Finset.Icc q.1 (q.1 + L) = (Finset.Icc p.1 (p.1 + L)).image ((q.1 - p.1) + ·) := by
        rw [Finset.image_add_left_Icc]
        congr 1 <;> omega
      have hstep : ∏ i ∈ Finset.Icc p.1 (p.1 + L), (4 * i + 2) < ∏ i ∈ Finset.Icc q.1 (q.1 + L), (4 * i + 2) := by
        rw [himg, Finset.prod_image (fun x _ y _ h => by omega)]
        exact Finset.prod_lt_prod_of_nonempty (fun i _ => by omega) (fun i _ => by omega)
          (Finset.nonempty_Icc.mpr (by omega))
      rw [← hp2, ← hq2, hfpq'] at hstep
      exact lt_irrefl _ hstep
    · exact Prod.ext heqv (by omega)
    · exfalso
      have hL : q.2 - q.1 = p.2 - p.1 := by omega
      set L := q.2 - q.1 with hLdef
      have hq2 : q.2 = q.1 + L := by omega
      have hp2 : p.2 = p.1 + L := by omega
      have himg : Finset.Icc p.1 (p.1 + L) = (Finset.Icc q.1 (q.1 + L)).image ((p.1 - q.1) + ·) := by
        rw [Finset.image_add_left_Icc]
        congr 1 <;> omega
      have hstep : ∏ i ∈ Finset.Icc q.1 (q.1 + L), (4 * i + 2) < ∏ i ∈ Finset.Icc p.1 (p.1 + L), (4 * i + 2) := by
        rw [himg, Finset.prod_image (fun x _ y _ h => by omega)]
        exact Finset.prod_lt_prod_of_nonempty (fun i _ => by omega) (fun i _ => by omega)
          (Finset.nonempty_Icc.mpr (by omega))
      rw [← hq2, ← hp2, hfpq'] at hstep
      exact lt_irrefl _ hstep

/-- The density half: the natural density of `{n | n ≡ 2 (mod 4)}` is
exactly `1/4`, via a floor-division squeeze against the affine ratio limit
`tendsto_add_mul_div_add_mul_atTop_nhds`. -/
theorem density :
    Filter.Tendsto (fun (N : ℕ) => ((Set.range (fun n : ℕ => 4 * n + 2) ∩ Set.Iio N).ncard : ℝ) / (Set.Iio N).ncard)
      Filter.atTop (nhds (1 / 4 : ℝ)) := by
  have hinj : Function.Injective (fun n : ℕ => 4 * n + 2) := fun a b h => by
    simp only at h; omega
  have hset : ∀ N : ℕ, Set.range (fun n : ℕ => 4 * n + 2) ∩ Set.Iio N
      = (fun n : ℕ => 4 * n + 2) '' (Set.Iio ((N + 1) / 4)) := by
    intro N
    ext m
    simp only [Set.mem_inter_iff, Set.mem_range, Set.mem_Iio, Set.mem_image]
    constructor
    · rintro ⟨⟨n, rfl⟩, hlt⟩
      exact ⟨n, by omega, rfl⟩
    · rintro ⟨n, hn, rfl⟩
      exact ⟨⟨n, rfl⟩, by omega⟩
  have hcard : ∀ N : ℕ, (Set.range (fun n : ℕ => 4 * n + 2) ∩ Set.Iio N).ncard = (N + 1) / 4 := by
    intro N
    rw [hset N, Set.ncard_image_of_injective _ hinj, Set.ncard_Iio_nat]
  have hfun_eq : (fun N : ℕ => ((Set.range (fun n : ℕ => 4 * n + 2) ∩ Set.Iio N).ncard : ℝ) / (Set.Iio N).ncard)
      = (fun N : ℕ => (((N + 1) / 4 : ℕ) : ℝ) / (N : ℝ)) := by
    funext N
    rw [hcard N, Set.ncard_Iio_nat]
  rw [hfun_eq]
  have hg : Filter.Tendsto (fun N : ℕ => ((-12 : ℝ) + 1 * (N : ℝ)) / ((0 : ℝ) + 4 * (N : ℝ))) Filter.atTop (nhds (1 / 4)) :=
    tendsto_add_mul_div_add_mul_atTop_nhds (-12) 0 1 (by norm_num : (4 : ℝ) ≠ 0)
  have hh : Filter.Tendsto (fun N : ℕ => ((4 : ℝ) + 1 * (N : ℝ)) / ((0 : ℝ) + 4 * (N : ℝ))) Filter.atTop (nhds (1 / 4)) :=
    tendsto_add_mul_div_add_mul_atTop_nhds 4 0 1 (by norm_num : (4 : ℝ) ≠ 0)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hg hh
  · filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    have h1 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have h4N : (0 : ℝ) < (0 : ℝ) + 4 * (N : ℝ) := by nlinarith
    have hb2 : N ≤ 4 * ((N + 1) / 4) + 3 := by omega
    have hb2R : (N : ℝ) ≤ 4 * (((N + 1) / 4 : ℕ) : ℝ) + 3 := by exact_mod_cast hb2
    rw [div_le_div_iff₀ h4N h1]
    nlinarith [hb2R, h1.le]
  · filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    have h1 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have h4N : (0 : ℝ) < (0 : ℝ) + 4 * (N : ℝ) := by nlinarith
    have hb1 : 4 * ((N + 1) / 4) ≤ N + 1 := by omega
    have hb1R : 4 * (((N + 1) / 4 : ℕ) : ℝ) ≤ (N : ℝ) + 1 := by exact_mod_cast hb1
    rw [div_le_div_iff₀ h1 h4N]
    nlinarith [hb1R, h1.le]

/-- The full root theorem, matching Erdos #421's exact statement shape at
density `1/4` instead of the open density-1 case. -/
theorem erdos_421_density_quarter :
    ∃ (d : ℕ → ℕ), StrictMono d ∧ 1 ≤ d 0 ∧
      Filter.Tendsto (fun (N : ℕ) => ((Set.range d ∩ Set.Iio N).ncard : ℝ) / (Set.Iio N).ncard)
        Filter.atTop (nhds (1 / 4 : ℝ)) ∧
      {p : ℕ × ℕ | p.1 ≤ p.2}.InjOn (fun p => ∏ i ∈ Finset.Icc p.1 p.2, d i) :=
  ⟨fun n : ℕ => 4 * n + 2, structural.1, structural.2.1, density, structural.2.2⟩

end Erdos421DensityQuarter
