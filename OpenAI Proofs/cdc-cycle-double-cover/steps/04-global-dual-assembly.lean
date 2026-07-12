/-
CDC step 04 — Global dual-obstruction assembly: a shared edge-parity
                certificate implies solvability of system (4)
                (certificate form of CDCLean.compatibility_solvable)
Problem version : 9eafd294-d3b7-4f2f-8704-6e530e0d227e
Episode         : 4eeb87f5-2ee8-48f1-a414-0b1e4c942ee6
Outcome         : kernel_verified (2026-07-11)
Exported via    : proof_export (format = lean), LLM-Driven Proof Search Environment
-/
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic

theorem root_theorem : ∀ (K Γ V E : Type) [Field K] [CharP K 2]
    [AddCommGroup Γ] [Module K Γ] [FiniteDimensional K Γ]
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endpoint : E × Fin 2 → V) (f : E → Γ)
    (g : E × Fin 2 → Γ) (d : E → Γ),
  (∀ e, d e = g (e, 0) + g (e, 1)) →
  (∀ Φ : Module.Dual K (E → Γ),
    (∀ (t : V → Γ) (ε : E → K),
      Φ (fun e =>
        t (endpoint (e, 0)) + t (endpoint (e, 1)) + ε e • f e) = 0) →
    ∃ χ : E → K, ∀ w,
      (∑ i ∈ Finset.univ.filter (fun i => endpoint i = w),
        (Φ.comp (LinearMap.single K (fun _ : E => Γ) i.1)) (g i)) =
      ∑ i ∈ Finset.univ.filter (fun i => endpoint i = w), χ i.1) →
  ∃ (t : V → Γ) (ε : E → K), ∀ e,
    t (endpoint (e, 0)) + t (endpoint (e, 1)) + ε e • f e = d e := by
intro K Γ V E _ _ _ _ _ _ _ _ _ endpoint f g d hd hparity
classical
let L : ((V → Γ) × (E → K)) →ₗ[K] (E → Γ) :=
  { toFun := fun x e =>
      x.1 (endpoint (e, 0)) + x.1 (endpoint (e, 1)) + x.2 e • f e
    map_add' := by
      intro x y
      funext e
      simp [add_smul]
      abel
    map_smul' := by
      intro c x
      funext e
      simp [smul_add, mul_smul] }
have hdRange : d ∈ LinearMap.range L := by
  apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff
    (LinearMap.range L) d).mp
  intro Φ hΦ
  have hAnn : ∀ (t : V → Γ) (ε : E → K),
      Φ (fun e =>
        t (endpoint (e, 0)) + t (endpoint (e, 1)) + ε e • f e) = 0 := by
    intro t ε
    exact (Submodule.mem_dualAnnihilator Φ).mp hΦ
      (L (t, ε)) (LinearMap.mem_range_self L (t, ε))
  let η : E → Module.Dual K Γ :=
    fun e => Φ.comp (LinearMap.single K (fun _ : E => Γ) e)
  have hcoord : ∀ x : E → Γ, Φ x = ∑ e, η e (x e) := by
    intro x
    calc
      Φ x = Φ (∑ e, Pi.single e (x e)) := by
        exact congrArg Φ (Finset.univ_sum_single x).symm
      _ = ∑ e, Φ (Pi.single e (x e)) := by rw [map_sum]
      _ = ∑ e, η e (x e) := by
        apply Finset.sum_congr rfl
        intro e he
        rfl
  have hpart : ∀ c : E × Fin 2 → K,
      (∑ w, ∑ i ∈ Finset.univ.filter (fun i => endpoint i = w), c i) =
        ∑ i, c i := by
    intro c
    simp [Finset.sum_filter, Finset.sum_comm]
  obtain ⟨χ, hlocal⟩ := hparity Φ hAnn
  have htotal : (∑ i : E × Fin 2, η i.1 (g i)) = 0 := by
    calc
      (∑ i : E × Fin 2, η i.1 (g i)) =
          ∑ w, ∑ i ∈ Finset.univ.filter (fun i => endpoint i = w),
            η i.1 (g i) :=
        (hpart (fun i => η i.1 (g i))).symm
      _ = ∑ w, ∑ i ∈ Finset.univ.filter (fun i => endpoint i = w),
            χ i.1 := by
        apply Finset.sum_congr rfl
        intro w hw
        exact hlocal w
      _ = ∑ i : E × Fin 2, χ i.1 := hpart (fun i => χ i.1)
      _ = ∑ e, ∑ j : Fin 2, χ e := by
        rw [Fintype.sum_prod_type]
      _ = 0 := by
        simp [Fin.sum_univ_two, CharTwo.two_eq_zero]
  calc
    Φ d = ∑ e, η e (d e) := hcoord d
    _ = ∑ e, η e (g (e, 0) + g (e, 1)) := by
      apply Finset.sum_congr rfl
      intro e he
      rw [hd e]
    _ = ∑ e, (η e (g (e, 0)) + η e (g (e, 1))) := by
      simp
    _ = ∑ i : E × Fin 2, η i.1 (g i) := by
      rw [Fintype.sum_prod_type]
      simp [Fin.sum_univ_two]
    _ = 0 := htotal
obtain ⟨x, hx⟩ := hdRange
refine ⟨x.1, x.2, ?_⟩
intro e
exact congrFun hx e
