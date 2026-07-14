/-
Erdős Problem #858 — §6.2–§6.3 eventual-frontier exactness, ASSEMBLY SKELETON.
(Chojecki 2026, "An exact frontier theorem and the asymptotic constant for Erdős
problem #858", Theorem 6.3 / Proposition 6.2, tied to the §4 sign theorem and the
§3 frontier reduction.)

Byte-faithful reconstruction of the kernel-verified root theorem from the
proofsearch MCP episode bdc04c0b-ae9f-46f6-ba3d-7b9a244d5b0f,
problem_version_id 850cf7ee-3b81-4f95-95bd-66a26ab493db.
Outcome: kernel_verified / root_kernel_verified (first submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 716863b7f586d95c1cc8f783bc71e9bf0f88bebab44202956e1d70d0c3f0ad02.

WHAT THIS ATOM IS. Theorem 6.3 (purely analytic eventual frontier exactness)
states: for all sufficiently large N there exists a cutoff K(N) with
    M(N) = S_N(K(N)) = M_fr(N).
The paper reaches it by combining
  • Proposition 6.2 / Theorem 4.7 — the sign theorem: the positivity set
    {a : R_N(a) > 1} (equivalently {a : q_N(a) > 0}, equivalently the Bellman
    continuation set C_N = {a : B_N(a) ≥ 1}) is an initial interval [1, K(N)].
    This rests on the §4/§5 Mertens + prime–semiprime monotonicity analysis; the
    sharp analytic input is PNT-grade and OUT OF this Mathlib pin.
  • Corollary 3.5 (VERIFIED here — cor35_max_eq / Cor35 family) — under that sign
    condition M(N) = S_N(K), and the initial segment [1,K] is the optimal
    continuation set, so S_N(K) = M_fr(N).
  • Proposition 3.2 (VERIFIED here — frontier_sweep_telescope) —
    S_N(K) = 1 + Σ_{a=1}^{K} q_N(a).

This snapshot is the honest §6.3 GLUE. It takes as hypotheses:
  (a) hpos / hnp — the sign theorem in its q_N form:  0 < q_N(a) for 1 ≤ a ≤ Kstar
      and q_N(a) ≤ 0 for a > Kstar. This is "{a : R_N(a) > 1} = [1, Kstar] is an
      initial interval" (paper Thm 4.7: q_N(a) > 0 ⟺ R_N(a) = a·C_N(a) > 1). This
      is the OPEN analytic substance and is DELIBERATELY quarantined into the
      hypothesis — it is NOT proved here.
  (b) hMN — the verified Corollary 3.5 identity  M(N) = S_N(Kstar).
  (c) hSN — the verified Proposition 3.2 telescope  S_N(K) = 1 + Σ_{a≤K} q_N(a).
      (Legitimate conditional-assembly hypothesis: hSN is itself the separately
      kernel-verified atom frontier_sweep_telescope.)
and PROVES the elementary bookkeeping conclusion
    M(N) = M_fr(N) := max_{0 ≤ K ≤ N} S_N(K),
rendered — exactly as in cor35_max_eq — by the two directions
    MN ∈ (Icc 0 N).image SN            (M(N) is achieved by the cutoff Kstar ≤ N)
    ∀ x ∈ (Icc 0 N).image SN, x ≤ MN   (M(N) upper-bounds every S_N(K), K ≤ N).

HYPOTHESIS vs CONCLUSION.
  HYPOTHESIS (open, analytic):  hpos, hnp   — the sign theorem / Prop 6.2 interval.
  HYPOTHESIS (verified atoms):  hSN (Prop 3.2), hMN (Cor 3.5).
  CONCLUSION (proved here):     M(N) = M_fr(N), the frontier optimum.

PROOF SHAPE. First derive `hopt : ∀ K ≤ N, S_N(K) ≤ S_N(Kstar)`: rewrite both
sides through the telescope hSN, reducing to Σ_{Icc 1 K} q_N ≤ Σ_{Icc 1 Kstar} q_N,
which is the Cor 3.5 initial-segment optimization inequality — proved verbatim by
the cor35_optimization_inequality idiom (Finset.sum_filter_add_sum_filter_not split
on `· ≤ Kstar`; the `> Kstar` part is ≤ 0 by Finset.sum_nonpos + hnp; the `≤ Kstar`
part is ≤ Σ_{Icc 1 Kstar} q_N by Finset.sum_le_sum_of_subset_of_nonneg + hpos).
Then the max characterization: Kstar ∈ Icc 0 N and hMN give the achieved
direction (hMN.symm); for the upper bound, any image element x = S_N(K) with K ≤ N
satisfies x = S_N(K) ≤ S_N(Kstar) = M(N) by hopt. No decidability pinning is needed
(the max set is a plain Finset image, no filter).

HONESTY BOUNDARY. Nothing in this file proves the sign theorem (Theorem 4.7 /
Proposition 6.2). The entire analytic content lives in hpos/hnp. This atom records
only that (open) sign theorem ⨾ (verified) Cor 3.5 + Prop 3.2 ⟹ M(N) = M_fr(N),
which is Theorem 6.3's bookkeeping — the §6.3 glue tying the analytic wall to the
verified frontier reduction.
-/
import Mathlib

namespace Erdos858

/-- §6.3 eventual-frontier exactness (assembly skeleton). Given the Proposition 3.2
telescope `S_N(K) = 1 + Σ_{a≤K} q_N(a)` (verified), the sign theorem
`0 < q_N(a)` on `[1,Kstar]` and `q_N(a) ≤ 0` above (the OPEN analytic input,
i.e. `{a : R_N(a) > 1} = [1,Kstar]`), and the Corollary 3.5 identity
`M(N) = S_N(Kstar)` (verified), the maximum `M(N)` equals the frontier optimum
`M_fr(N) = max_{0≤K≤N} S_N(K)`, rendered as "achieved and upper bound" over
`(Finset.Icc 0 N).image SN`. -/
theorem erdos858_sec63_eventual_frontier :
    ∀ (N Kstar : ℕ) (qN SN : ℕ → ℚ) (MN : ℚ),
      Kstar ≤ N →
      (∀ K : ℕ, SN K = 1 + ∑ a ∈ Finset.Icc 1 K, qN a) →
      (∀ a : ℕ, 1 ≤ a → a ≤ Kstar → 0 < qN a) →
      (∀ a : ℕ, Kstar < a → qN a ≤ 0) →
      MN = SN Kstar →
      MN ∈ (Finset.Icc 0 N).image SN ∧
        (∀ x ∈ (Finset.Icc 0 N).image SN, x ≤ MN) := by
  intro N Kstar qN SN MN hKN hSN hpos hnp hMN
  have hopt : ∀ K : ℕ, K ≤ N → SN K ≤ SN Kstar := by
    intro K hK
    rw [hSN K, hSN Kstar]
    have hsum : ∑ a ∈ Finset.Icc 1 K, qN a ≤ ∑ a ∈ Finset.Icc 1 Kstar, qN a := by
      rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 K) (fun a => a ≤ Kstar)]
      have h2 : ∑ a ∈ (Finset.Icc 1 K).filter (fun a => ¬ a ≤ Kstar), qN a ≤ 0 := by
        apply Finset.sum_nonpos
        intro a ha
        simp only [Finset.mem_filter] at ha
        exact hnp a (by omega)
      have h1 : ∑ a ∈ (Finset.Icc 1 K).filter (fun a => a ≤ Kstar), qN a ≤ ∑ a ∈ Finset.Icc 1 Kstar, qN a := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro a ha
          simp only [Finset.mem_filter, Finset.mem_Icc] at ha ⊢
          omega
        · intro a ha _
          simp only [Finset.mem_Icc] at ha
          exact le_of_lt (hpos a ha.1 ha.2)
      linarith
    linarith
  refine ⟨?_, ?_⟩
  · rw [Finset.mem_image]
    refine ⟨Kstar, ?_, hMN.symm⟩
    simp only [Finset.mem_Icc]
    omega
  · intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨K, hKmem, hKeq⟩ := hx
    simp only [Finset.mem_Icc] at hKmem
    rw [← hKeq, hMN]
    exact hopt K hKmem.2

end Erdos858
