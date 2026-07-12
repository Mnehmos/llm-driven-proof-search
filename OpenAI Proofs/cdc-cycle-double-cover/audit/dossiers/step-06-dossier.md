# ⚠️ KERNEL-VERIFIED FORMAL STATEMENT — FIDELITY NOT YET VERIFIED — CDC paper (OpenAI, arXiv 2026) Lemma 2.2, complete: for every finite loopless cubic multigraph (encoded by a slot equivalence inc : (V × Fin 3) ≃ (E × Fin 2) with the loopless condition that the two ends of an edge lie at distinct vertices) and every nowhere-zero F2^3-flow f (conservation: the three incident flow values at each vertex sum to zero), the edge-compatibility system t_u + t_v + eps_e f(e) = d_e is solvable, where d_e = g_{u,e} + g_{v,e} is the manuscript's right-hand side built from the local base points g_{v,e} = (if e is the slot-1 edge at v then the flow value of the slot-0 edge at v else 0). This is the paper's central dual-obstruction calculation (equations (4)-(9)) assembled into its final form; mirrors CDCLean.compatibility_solvable in the openai/cdc-lean repository.

> This proof establishes:
>
> `∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (inc : (V × Fin 3) ≃ (E × Fin 2))
    (f : E → (Fin 3 → ZMod 2)),
  (∀ e : E, (inc.symm (e, 0)).1 ≠ (inc.symm (e, 1)).1) →
  (∀ e : E, f e ≠ 0) →
  (∀ v : V, (∑ i : Fin 3, f ((inc (v, i)).1)) = 0) →
  ∃ (t : V → (Fin 3 → ZMod 2)) (ε : E → ZMod 2),
    ∀ e : E,
      t ((inc.symm (e, 0)).1) + t ((inc.symm (e, 1)).1) + ε e • f e =
        (if e = (inc ((inc.symm (e, 0)).1, 1)).1
          then f ((inc ((inc.symm (e, 0)).1, 0)).1) else 0) +
        (if e = (inc ((inc.symm (e, 1)).1, 1)).1
          then f ((inc ((inc.symm (e, 1)).1, 0)).1) else 0)`
>
> It does **not yet** certify the source claim above.

**Root goal (formal):** `∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (inc : (V × Fin 3) ≃ (E × Fin 2))
    (f : E → (Fin 3 → ZMod 2)),
  (∀ e : E, (inc.symm (e, 0)).1 ≠ (inc.symm (e, 1)).1) →
  (∀ e : E, f e ≠ 0) →
  (∀ v : V, (∑ i : Fin 3, f ((inc (v, i)).1)) = 0) →
  ∃ (t : V → (Fin 3 → ZMod 2)) (ε : E → ZMod 2),
    ∀ e : E,
      t ((inc.symm (e, 0)).1) + t ((inc.symm (e, 1)).1) + ε e • f e =
        (if e = (inc ((inc.symm (e, 0)).1, 1)).1
          then f ((inc ((inc.symm (e, 0)).1, 0)).1) else 0) +
        (if e = (inc ((inc.symm (e, 1)).1, 1)).1
          then f ((inc ((inc.symm (e, 1)).1, 0)).1) else 0)`

| Proof soundness | Statement fidelity | Canonical promotion | Training eligibility |
|---|---|---|---|
| VERIFIED | ATTESTED (unsafe_dev_attestation — not reviewed) | BLOCKED | QUARANTINED |

| episode | state | steps | budget left (μ$) | started | finished |
|---|---|---|---|---|---|
| `0c06c7cd-de31-45f2-9fde-03a3690c6e81` | terminated (root_proved) | 2 | — | 2026-07-11T07:04:24 | 2026-07-11T07:11:56 |

## Proof tree

- ✅ **root_theorem** : `∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (inc : (V × Fin 3) ≃ (E × Fin 2))
    (f : E → (Fin 3 → ZMod 2)),
  (∀ e : E, (inc.symm (e, 0)).1 ≠ (inc.symm (e, 1)).1) →
  (∀ e : E, f e ≠ 0) →
  (∀ v : V, (∑ i : Fin 3, f ((inc (v, i)).1)) = 0) →
  ∃ (t : V → (Fin 3 → ZMod 2)) (ε : E → ZMod 2),
    ∀ e : E,
      t ((inc.symm (e, 0)).1) + t ((inc.symm (e, 1)).1) + ε e • f e =
        (if e = (inc ((inc.symm (e, 0)).1, 1)).1
          then f ((inc ((inc.symm (e, 0)).1, 0)).1) else 0) +
        (if e = (inc ((inc.symm (e, 1)).1, 1)).1
          then f ((inc ((inc.symm (e, 1)).1, 0)).1) else 0)`

## The proof, assembled

```lean
import Mathlib

theorem root_theorem : ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (inc : (V × Fin 3) ≃ (E × Fin 2))
    (f : E → (Fin 3 → ZMod 2)),
  (∀ e : E, (inc.symm (e, 0)).1 ≠ (inc.symm (e, 1)).1) →
  (∀ e : E, f e ≠ 0) →
  (∀ v : V, (∑ i : Fin 3, f ((inc (v, i)).1)) = 0) →
  ∃ (t : V → (Fin 3 → ZMod 2)) (ε : E → ZMod 2),
    ∀ e : E,
      t ((inc.symm (e, 0)).1) + t ((inc.symm (e, 1)).1) + ε e • f e =
        (if e = (inc ((inc.symm (e, 0)).1, 1)).1
          then f ((inc ((inc.symm (e, 0)).1, 0)).1) else 0) +
        (if e = (inc ((inc.symm (e, 1)).1, 1)).1
          then f ((inc ((inc.symm (e, 1)).1, 0)).1) else 0) := by
intro V E _ _ _ _ inc f hloop hnz hcons
classical
set L : ((V → (Fin 3 → ZMod 2)) × (E → ZMod 2)) →ₗ[ZMod 2] (E → (Fin 3 → ZMod 2)) :=
  { toFun := fun x e => x.1 ((inc.symm (e, 0)).1) + x.1 ((inc.symm (e, 1)).1) + x.2 e • f e
    map_add' := by
      intro x y
      funext e i
      simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    map_smul' := by
      intro c x
      funext e i
      simp only [Prod.smul_fst, Prod.smul_snd, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        RingHom.id_apply]
      ring } with hLdef
have hfin2 : ∀ a b : Fin 2, a ≠ b → a = 0 ∧ b = 1 ∨ a = 1 ∧ b = 0 := by decide
have hne : ∀ (v : V) (i k : Fin 3), i ≠ k → (inc (v, i)).1 ≠ (inc (v, k)).1 := by
  intro v i k hik heq
  by_cases hj : (inc (v, i)).2 = (inc (v, k)).2
  · exact hik (congrArg Prod.snd (inc.injective (Prod.ext_iff.mpr ⟨heq, hj⟩)))
  · have h1 : (inc.symm ((inc (v, i)).1, (inc (v, i)).2)).1 = v := by simp
    have h2 : (inc.symm ((inc (v, i)).1, (inc (v, k)).2)).1 = v := by
      rw [heq]
      simp
    rcases hfin2 _ _ hj with ⟨hj1, hj2⟩ | ⟨hj1, hj2⟩
    · rw [hj1] at h1
      rw [hj2] at h2
      exact hloop ((inc (v, i)).1) (h1.trans h2.symm)
    · rw [hj1] at h1
      rw [hj2] at h2
      exact hloop ((inc (v, i)).1) (h2.trans h1.symm)
have hd : (fun e : E =>
    (if e = (inc ((inc.symm (e, 0)).1, 1)).1
      then f ((inc ((inc.symm (e, 0)).1, 0)).1) else 0) +
    (if e = (inc ((inc.symm (e, 1)).1, 1)).1
      then f ((inc ((inc.symm (e, 1)).1, 0)).1) else 0)) ∈ LinearMap.range L := by
  apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff (LinearMap.range L) _).mp
  intro φ hφann
  have hφ : ∀ x, φ (L x) = 0 := fun x =>
    (Submodule.mem_dualAnnihilator φ).mp hφann (L x) (LinearMap.mem_range.mpr ⟨x, rfl⟩)
  set η : E → Module.Dual (ZMod 2) (Fin 3 → ZMod 2) :=
    fun e => φ.comp (LinearMap.single (ZMod 2) (fun _ : E => Fin 3 → ZMod 2) e) with hηdef
  have hsumcoord : ∀ y : E → Fin 3 → ZMod 2, φ y = ∑ e : E, η e (y e) := by
    intro y
    calc φ y = φ (∑ e : E, Pi.single e (y e)) := by rw [Finset.univ_sum_single]
      _ = ∑ e : E, φ (Pi.single e (y e)) := map_sum φ _ _
      _ = ∑ e : E, η e (y e) := Finset.sum_congr rfl fun e _ => by
          simp [hηdef, LinearMap.single_apply]
  have hedge : ∀ e : E, η e (f e) = 0 := by
    intro e
    set se : E → ZMod 2 := Pi.single e (1 : ZMod 2) with hsedef
    have hz := hφ ((0 : V → Fin 3 → ZMod 2), se)
    rw [hsumcoord] at hz
    have hLk : ∀ k : E, (L ((0 : V → Fin 3 → ZMod 2), se)) k = se k • f k := by
      intro k
      simp only [hLdef, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply, zero_add]
    rw [Finset.sum_congr rfl fun k _ => congrArg (η k) (hLk k)] at hz
    have hzero : ∀ k : E, k ≠ e → η k (se k • f k) = 0 := by
      intro k hk
      rw [hsedef, Pi.single_eq_of_ne hk, zero_smul, map_zero]
    rw [Fintype.sum_eq_single e hzero, hsedef, Pi.single_eq_same, one_smul] at hz
    exact hz
  have hvertex : ∀ v : V,
      η ((inc (v, 0)).1) + η ((inc (v, 1)).1) + η ((inc (v, 2)).1) = 0 := by
    intro v
    refine LinearMap.ext fun q => ?_
    set sq : V → Fin 3 → ZMod 2 := Pi.single v q with hsqdef
    have hz := hφ (sq, (0 : E → ZMod 2))
    rw [hsumcoord] at hz
    have hLk : ∀ k : E, (L (sq, (0 : E → ZMod 2))) k =
        sq ((inc.symm (k, 0)).1) + sq ((inc.symm (k, 1)).1) := by
      intro k
      simp only [hLdef, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply, zero_smul, add_zero]
    rw [Finset.sum_congr rfl fun k _ => congrArg (η k) (hLk k)] at hz
    have hsplit : (∑ k : E, η k (sq ((inc.symm (k, 0)).1) + sq ((inc.symm (k, 1)).1))) =
        ∑ k : E, ∑ j : Fin 2, η k (sq ((inc.symm (k, j)).1)) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_add, Fin.sum_univ_two]
    rw [hsplit] at hz
    have hprod : (∑ k : E, ∑ j : Fin 2, η k (sq ((inc.symm (k, j)).1))) =
        ∑ p : E × Fin 2, η p.1 (sq ((inc.symm p).1)) :=
      (Fintype.sum_prod_type (f := fun p : E × Fin 2 =>
        η p.1 (sq ((inc.symm p).1)))).symm
    rw [hprod] at hz
    have hcomp : (∑ s : V × Fin 3, η ((inc s).1) (sq s.1)) =
        ∑ p : E × Fin 2, η p.1 (sq ((inc.symm p).1)) := by
      refine Eq.trans ?_ (Equiv.sum_comp inc (fun p : E × Fin 2 =>
        η p.1 (sq ((inc.symm p).1))))
      refine Finset.sum_congr rfl fun s _ => ?_
      show η ((inc s).1) (sq s.1) = η ((inc s).1) (sq ((inc.symm (inc s)).1))
      rw [Equiv.symm_apply_apply]
    rw [← hcomp] at hz
    have hVsum : (∑ w : V, ∑ i : Fin 3, η ((inc (w, i)).1) (sq w)) =
        ∑ s : V × Fin 3, η ((inc s).1) (sq s.1) :=
      (Fintype.sum_prod_type (f := fun s : V × Fin 3 =>
        η ((inc s).1) (sq s.1))).symm
    rw [← hVsum] at hz
    have hzero : ∀ w : V, w ≠ v → (∑ i : Fin 3, η ((inc (w, i)).1) (sq w)) = 0 := by
      intro w hw
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [hsqdef, Pi.single_eq_of_ne hw, map_zero]
    rw [Fintype.sum_eq_single v hzero, Fin.sum_univ_three, hsqdef] at hz
    simp only [Pi.single_eq_same] at hz
    simpa [LinearMap.add_apply] using hz
  have hldi : ∀ x y a b c : Fin 3 → ZMod 2,
      x ≠ 0 → y ≠ 0 → x ≠ y → a + b + c = 0 →
      (∑ i : Fin 3, x i * a i) = 0 →
      (∑ i : Fin 3, y i * b i) = 0 →
      (∑ i : Fin 3, (x + y) i * c i) = 0 →
      (∑ i : Fin 3, x i * b i) =
        (if a = 0 then (0 : ZMod 2) else 1) + (if b = 0 then (0 : ZMod 2) else 1) +
          (if c = 0 then (0 : ZMod 2) else 1) := by
    decide
  have hft : ∀ x y z : Fin 3 → ZMod 2,
      x ≠ 0 → y ≠ 0 → z ≠ 0 → x + y + z = 0 → z = x + y ∧ x ≠ y := by
    decide
  set code : E → Fin 3 → ZMod 2 := fun e i => η e (Pi.single i 1) with hcodedef
  have happly : ∀ (e : E) (x : Fin 3 → ZMod 2), η e x = ∑ i : Fin 3, x i * code e i := by
    intro e x
    calc η e x = η e (∑ i : Fin 3, Pi.single i (x i)) := by rw [Finset.univ_sum_single]
      _ = ∑ i : Fin 3, η e (Pi.single i (x i)) := map_sum (η e) _ _
      _ = ∑ i : Fin 3, x i * code e i := Finset.sum_congr rfl fun i _ => by
          have hone : (Pi.single i (x i) : Fin 3 → ZMod 2) =
              x i • Pi.single i (1 : ZMod 2) := by
            rw [← Pi.single_smul, smul_eq_mul, mul_one]
          rw [hone, map_smul, smul_eq_mul, hcodedef]
  have hlocal : ∀ v : V,
      η ((inc (v, 1)).1) (f ((inc (v, 0)).1)) =
        (if code ((inc (v, 0)).1) = 0 then (0 : ZMod 2) else 1) +
        (if code ((inc (v, 1)).1) = 0 then (0 : ZMod 2) else 1) +
        (if code ((inc (v, 2)).1) = 0 then (0 : ZMod 2) else 1) := by
    intro v
    have hsum3 : f ((inc (v, 0)).1) + f ((inc (v, 1)).1) + f ((inc (v, 2)).1) = 0 := by
      have h := hcons v
      rwa [Fin.sum_univ_three] at h
    obtain ⟨hz2, hxy⟩ := hft _ _ _ (hnz _) (hnz _) (hnz _) hsum3
    have hcsum : code ((inc (v, 0)).1) + code ((inc (v, 1)).1) + code ((inc (v, 2)).1) = 0 := by
      funext k
      have hq := LinearMap.congr_fun (hvertex v) (Pi.single k 1)
      simpa [hcodedef, LinearMap.add_apply] using hq
    have h0 : (∑ i : Fin 3, f ((inc (v, 0)).1) i * code ((inc (v, 0)).1) i) = 0 := by
      rw [← happly]
      exact hedge _
    have h1 : (∑ i : Fin 3, f ((inc (v, 1)).1) i * code ((inc (v, 1)).1) i) = 0 := by
      rw [← happly]
      exact hedge _
    have h2 : (∑ i : Fin 3,
        (f ((inc (v, 0)).1) + f ((inc (v, 1)).1)) i * code ((inc (v, 2)).1) i) = 0 := by
      rw [← hz2, ← happly]
      exact hedge _
    have hmain := hldi (f ((inc (v, 0)).1)) (f ((inc (v, 1)).1))
      (code ((inc (v, 0)).1)) (code ((inc (v, 1)).1)) (code ((inc (v, 2)).1))
      (hnz _) (hnz _) hxy hcsum h0 h1 h2
    rw [happly]
    exact hmain
  calc φ (fun e : E =>
        (if e = (inc ((inc.symm (e, 0)).1, 1)).1
          then f ((inc ((inc.symm (e, 0)).1, 0)).1) else 0) +
        (if e = (inc ((inc.symm (e, 1)).1, 1)).1
          then f ((inc ((inc.symm (e, 1)).1, 0)).1) else 0))
      = ∑ p : E × Fin 2, η p.1
          (if p.1 = (inc ((inc.symm p).1, 1)).1
            then f ((inc ((inc.symm p).1, 0)).1) else 0) := by
        rw [hsumcoord]
        refine Eq.trans ?_ (Fintype.sum_prod_type (f := fun p : E × Fin 2 => η p.1
          (if p.1 = (inc ((inc.symm p).1, 1)).1
            then f ((inc ((inc.symm p).1, 0)).1) else 0))).symm
        refine Finset.sum_congr rfl fun e _ => ?_
        show η e ((if e = (inc ((inc.symm (e, 0)).1, 1)).1
            then f ((inc ((inc.symm (e, 0)).1, 0)).1) else 0) +
          (if e = (inc ((inc.symm (e, 1)).1, 1)).1
            then f ((inc ((inc.symm (e, 1)).1, 0)).1) else 0)) =
          ∑ j : Fin 2, η e (if e = (inc ((inc.symm (e, j)).1, 1)).1
            then f ((inc ((inc.symm (e, j)).1, 0)).1) else 0)
        rw [map_add, Fin.sum_univ_two]
    _ = ∑ s : V × Fin 3, η ((inc s).1)
          (if (inc s).1 = (inc (s.1, 1)).1 then f ((inc (s.1, 0)).1) else 0) := by
        refine Eq.trans (Equiv.sum_comp inc (fun p : E × Fin 2 => η p.1
          (if p.1 = (inc ((inc.symm p).1, 1)).1
            then f ((inc ((inc.symm p).1, 0)).1) else 0))).symm ?_
        refine Finset.sum_congr rfl fun s _ => ?_
        show η ((inc s).1)
            (if (inc s).1 = (inc ((inc.symm (inc s)).1, 1)).1
              then f ((inc ((inc.symm (inc s)).1, 0)).1) else 0) = _
        rw [Equiv.symm_apply_apply]
    _ = ∑ v : V, ∑ i : Fin 3, η ((inc (v, i)).1)
          (if (inc (v, i)).1 = (inc (v, 1)).1 then f ((inc (v, 0)).1) else 0) :=
        Fintype.sum_prod_type (f := fun s : V × Fin 3 => η ((inc s).1)
          (if (inc s).1 = (inc (s.1, 1)).1 then f ((inc (s.1, 0)).1) else 0))
    _ = ∑ v : V, η ((inc (v, 1)).1) (f ((inc (v, 0)).1)) := by
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [Fin.sum_univ_three, if_neg (hne v 0 1 (by decide)), if_pos rfl,
          if_neg (hne v 2 1 (by decide)), map_zero, map_zero, zero_add, add_zero]
    _ = ∑ v : V, ∑ i : Fin 3,
          (if code ((inc (v, i)).1) = 0 then (0 : ZMod 2) else 1) := by
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [Fin.sum_univ_three]
        exact hlocal v
    _ = ∑ s : V × Fin 3, (if code ((inc s).1) = 0 then (0 : ZMod 2) else 1) :=
        (Fintype.sum_prod_type (f := fun s : V × Fin 3 =>
          if code ((inc s).1) = 0 then (0 : ZMod 2) else 1)).symm
    _ = ∑ p : E × Fin 2, (if code p.1 = 0 then (0 : ZMod 2) else 1) :=
        Equiv.sum_comp inc (fun p : E × Fin 2 =>
          if code p.1 = 0 then (0 : ZMod 2) else 1)
    _ = ∑ e : E, ((if code e = 0 then (0 : ZMod 2) else 1) +
          (if code e = 0 then (0 : ZMod 2) else 1)) := by
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [Fin.sum_univ_two]
    _ = 0 := by
        refine Finset.sum_eq_zero fun e _ => ?_
        exact CharTwo.add_self_eq_zero _
obtain ⟨x, hx⟩ := LinearMap.mem_range.mp hd
refine ⟨x.1, x.2, fun e => ?_⟩
have hxe := congrFun hx e
calc x.1 ((inc.symm (e, 0)).1) + x.1 ((inc.symm (e, 1)).1) + x.2 e • f e
    = (L x) e := by
      simp only [hLdef, LinearMap.coe_mk, AddHom.coe_mk]
  _ = (if e = (inc ((inc.symm (e, 0)).1, 1)).1
        then f ((inc ((inc.symm (e, 0)).1, 0)).1) else 0) +
      (if e = (inc ((inc.symm (e, 1)).1, 1)).1
        then f ((inc ((inc.symm (e, 1)).1, 0)).1) else 0) := hxe

```

## How it went — every attempt, in order

| # | obligation | action | detail | verdict |
|---|---|---|---|---|
| 2 | `root_theorem` | solve | `intro V E _ _ _ _ inc f hloop hnz hcons ; classical ; set L : ((V → (Fin 3 → ZMod 2)) × (E → ZMod 2)) →ₗ[ZMod 2] (E → (Fin 3 → ZMod 2)) := ;   { toFun := fun x e => x.1 ((inc.symm (e, 0)).1) + x.1 ((inc.symm (e, 1)).1) + x.2 e • f e ;     map_add' := by ;       intro x y ;       funext e i ;       simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, Pi.smul_apply, smul_eq_mul] ;       ring ;     map_smul' := by ;       intro c x ;       funext e i ;       simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply] ;       ring } with hLdef ; have hfin2 : ∀ a b : Fin 2, a ≠ b → a = 0 ∧ b = 1 ∨ a = 1 ∧ b = 0 := by decide ; have hne : ∀ (v : V) (i k : Fin 3), i ≠ k → (inc (v, i)).1 ≠ (inc (v, k)).1 := by ;   intro v i k hik heq ;   by_cases hj : (inc (v, i)).2 = (inc (v, k)).2 ;   · exact hik (congrArg Prod.snd (inc.injective (Prod.ext_iff.mpr ⟨heq, hj⟩))) ;   · have h1 : (inc.symm ((inc (v, i)).1, (inc (v, i)).2)).1 = v := by simp ;     have h2 : (inc.symm ((inc (v, i)).1, (inc (v, k)).2)).1 = v := by ;       rw [heq] ;       simp ;     rcases hfin2 _ _ hj with ⟨hj1, hj2⟩ \| ⟨hj1, hj2⟩ ;     · rw [hj1] at h1 ;       rw [hj2] at h2 ;       exact hloop ((inc (v, i)).1) (h1.trans h2.symm) ;     · rw [hj1] at h1 ;       rw [hj2] at h2 ;       exact hloop ((inc (v, i)).1) (h2.trans h1.symm) ; have hd : (fun e : E => ;     (if e = (inc ((inc.symm (e, 0)).1, 1)).1 ;       then f ((inc ((inc.symm (e, 0)).1, 0)).1) else 0) + ;     (if e = (inc ((inc.symm (e, 1)).1, 1)).1 ;       then f ((inc ((inc.symm (e, 1)).1, 0)).1) else 0)) ∈ LinearMap.range L := by ;   apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff (LinearMap.range L) _).mp ;   intro φ hφann ;   have hφ : ∀ x, φ (L x) = 0 := fun x => ;     (Submodule.mem_dualAnnihilator φ).mp hφann (L x) (LinearMap.mem_range.mpr ⟨x, rfl⟩) ;   set η : E → Module.Dual (ZMod 2) (Fin 3 → ZMod 2) := ;     fun e => φ.comp (LinearMap.single (ZMod 2) (fun _ : E => Fin 3 → ZMod 2) e) with hηdef ;   have hsumcoord : ∀ y : E → Fin 3 → ZMod 2, φ y = ∑ e : E, η e (y e) := by ;     intro y ;     calc φ y = φ (∑ e : E, Pi.single e (y e)) := by rw [Finset.univ_sum_single] ;       _ = ∑ e : E, φ (Pi.single e (y e)) := map_sum φ _ _ ;       _ = ∑ e : E, η e (y e) := Finset.sum_congr rfl fun e _ => by ;           simp [hηdef, LinearMap.single_apply] ;   have hedge : ∀ e : E, η e (f e) = 0 := by ;     intro e ;     have hz := hφ ((0 : V → Fin 3 → ZMod 2), Pi.single e (1 : ZMod 2)) ;     rw [hsumcoord] at hz ;     have hLk : ∀ k : E, (L ((0 : V → Fin 3 → ZMod 2), Pi.single e (1 : ZMod 2))) k = ;         Pi.single e (1 : ZMod 2) k • f k := by ;       intro k ;       simp only [hLdef, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply, zero_add] ;     rw [Finset.sum_congr rfl fun k _ => congrArg (η k) (hLk k)] at hz ;     have hzero : ∀ k : E, k ≠ e → η k (Pi.single e (1 : ZMod 2) k • f k) = 0 := by ;       intro k hk ;       rw [Pi.single_eq_of_ne hk, zero_smul, map_zero] ;     rw [Fintype.sum_eq_single e hzero, Pi.single_eq_same, one_smul] at hz ;     exact hz ;   have hvertex : ∀ v : V, ;       η ((inc (v, 0)).1) + η ((inc (v, 1)).1) + η ((inc (v, 2)).1) = 0 := by ;     intro v ;     refine LinearMap.ext fun q => ?_ ;     have hz := hφ (Pi.single v q, (0 : E → ZMod 2)) ;     rw [hsumcoord] at hz ;     have hLk : ∀ k : E, (L (Pi.single v q, (0 : E → ZMod 2))) k = ;         Pi.single v q ((inc.symm (k, 0)).1) + Pi.single v q ((inc.symm (k, 1)).1) := by ;       intro k ;       simp only [hLdef, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply, zero_smul, add_zero] ;     rw [Finset.sum_congr rfl fun k _ => congrArg (η k) (hLk k)] at hz ;     have hsplit : (∑ k : E, η k (Pi.single v q ((inc.symm (k, 0)).1) + ;         Pi.single v q ((inc.symm (k, 1)).1))) = ;         ∑ k : E, ∑ j : Fin 2, η k (Pi.single v q ((inc.symm (k, j)).1)) := by ;       refine Finset.sum_congr rfl fun k _ => ?_ ;       rw [map_add, Fin.sum_univ_two] ;     rw [hsplit] at hz ;     have hprod : (∑ k : E, ∑ j : Fin 2, η k (Pi.single v q ((inc.symm (k, j)).1))) = ;         ∑ p : E × Fin 2, η p.1 (Pi.single v q ((inc.symm p).1)) := ;       (Fintype.sum_prod_type (f := fun p : E × Fin 2 => ;         η p.1 (Pi.single v q ((inc.symm p).1)))).symm ;     rw [hprod] at hz ;     have hcomp : (∑ s : V × Fin 3, η ((inc s).1) (Pi.single v q s.1)) = ;         ∑ p : E × Fin 2, η p.1 (Pi.single v q ((inc.symm p).1)) := by ;       refine Eq.trans ?_ (Equiv.sum_comp inc (fun p : E × Fin 2 => ;         η p.1 (Pi.single v q ((inc.symm p).1)))) ;       refine Finset.sum_congr rfl fun s _ => ?_ ;       show η ((inc s).1) (Pi.single v q s.1) = ;         η ((inc s).1) (Pi.single v q ((inc.symm (inc s)).1)) ;       rw [Equiv.symm_apply_apply] ;     rw [← hcomp] at hz ;     have hVsum : (∑ w : V, ∑ i : Fin 3, η ((inc (w, i)).1) (Pi.single v q w)) = ;         ∑ s : V × Fin 3, η ((inc s).1) (Pi.single v q s.1) := ;       (Fintype.sum_prod_type (f := fun s : V × Fin 3 => ;         η ((inc s).1) (Pi.single v q s.1))).symm ;     rw [← hVsum] at hz ;     have hzero : ∀ w : V, w ≠ v → ;         (∑ i : Fin 3, η ((inc (w, i)).1) (Pi.single v q w)) = 0 := by ;       intro w hw ;       refine Finset.sum_eq_zero fun i _ => ?_ ;       rw [Pi.single_eq_of_ne hw, map_zero] ;     rw [Fintype.sum_eq_single v hzero, Fin.sum_univ_three] at hz ;     simp only [Pi.single_eq_same] at hz ;     simpa [LinearMap.add_apply] using hz ;   have hldi : ∀ x y a b c : Fin 3 → ZMod 2, ;       x ≠ 0 → y ≠ 0 → x ≠ y → a + b + c = 0 → ;       (∑ i : Fin 3, x i * a i) = 0 → ;       (∑ i : Fin 3, y i * b i) = 0 → ;       (∑ i : Fin 3, (x + y) i * c i) = 0 → ;       (∑ i : Fin 3, x i * b i) = ;         (if a = 0 then (0 : ZMod 2) else 1) + (if b = 0 then (0 : ZMod 2) else 1) + ;           (if c = 0 then (0 : ZMod 2) else 1) := by ;     decide ;   have hft : ∀ x y z : Fin 3 → ZMod 2, ;       x ≠ 0 → y ≠ 0 → z ≠ 0 → x + y + z = 0 → z = x + y ∧ x ≠ y := by ;     decide ;   set code : E → Fin 3 → ZMod 2 := fun e i => η e (Pi.single i 1) with hcodedef ;   have happly : ∀ (e : E) (x : Fin 3 → ZMod 2), η e x = ∑ i : Fin 3, x i * code e i := by ;     intro e x ;     calc η e x = η e (∑ i : Fin 3, Pi.single i (x i)) := by rw [Finset.univ_sum_single] ;       _ = ∑ i : Fin 3, η e (Pi.single i (x i)) := map_sum (η e) _ _ ;       _ = ∑ i : Fin 3, x i * code e i := Finset.sum_congr rfl fun i _ => by ;           have hone : Pi.single i (x i) = x i • Pi.single i (1 : ZMod 2) := by ;             rw [← Pi.single_smul, smul_eq_mul, mul_one] ;           rw [hone, map_smul, smul_eq_mul, hcodedef] ;   have hlocal : ∀ v : V, ;       η ((inc (v, 1)).1) (f ((inc (v, 0)).1)) = ;         (if code ((inc (v, 0)).1) = 0 then (0 : ZMod 2) else 1) + ;         (if code ((inc (v, 1)).1) = 0 then (0 : ZMod 2) else 1) + ;         (if code ((inc (v, 2)).1) = 0 then (0 : ZMod 2) else 1) := by ;     intro v ;     have hsum3 : f ((inc (v, 0)).1) + f ((inc (v, 1)).1) + f ((inc (v, 2)).1) = 0 := by ;       have h := hcons v ;       rwa [Fin.sum_univ_three] at h ;     obtain ⟨hz2, hxy⟩ := hft _ _ _ (hnz _) (hnz _) (hnz _) hsum3 ;     have hcsum : code ((inc (v, 0)).1) + code ((inc (v, 1)).1) + code ((inc (v, 2)).1) = 0 := by ;       funext k ;       have hq := LinearMap.congr_fun (hvertex v) (Pi.single k 1) ;       simpa [hcodedef, LinearMap.add_apply] using hq ;     have h0 : (∑ i : Fin 3, f ((inc (v, 0)).1) i * code ((inc (v, 0)).1) i) = 0 := by ;       rw [← happly] ;       exact hedge _ ;     have h1 : (∑ i : Fin 3, f ((inc (v, 1)).1) i * code ((inc (v, 1)).1) i) = 0 := by ;       rw [← happly] ;       exact hedge _ ;     have h2 : (∑ i : Fin 3, ;         (f ((inc (v, 0)).1) + f ((inc (v, 1)).1)) i * code ((inc (v, 2)).1) i) = 0 := by ;       rw [← hz2, ← happly] ;       exact hedge _ ;     have hmain := hldi (f ((inc (v, 0)).1)) (f ((inc (v, 1)).1)) ;       (code ((inc (v, 0)).1)) (code ((inc (v, 1)).1)) (code ((inc (v, 2)).1)) ;       (hnz _) (hnz _) hxy hcsum h0 h1 h2 ;     rw [happly] ;     exact hmain ;   calc φ (fun e : E => ;         (if e = (inc ((inc.symm (e, 0)).1, 1)).1 ;           then f ((inc ((inc.symm (e, 0)).1, 0)).1) else 0) + ;         (if e = (inc ((inc.symm (e, 1)).1, 1)).1 ;           then f ((inc ((inc.symm (e, 1)).1, 0)).1) else 0)) ;       = ∑ p : E × Fin 2, η p.1 ;           (if p.1 = (inc ((inc.symm p).1, 1)).1 ;             then f ((inc ((inc.symm p).1, 0)).1) else 0) := by ;         rw [hsumcoord] ;         refine Eq.trans ?_ (Fintype.sum_prod_type (f := fun p : E × Fin 2 => η p.1 ;           (if p.1 = (inc ((inc.symm p).1, 1)).1 ;             then f ((inc ((inc.symm p).1, 0)).1) else 0))).symm ;         refine Finset.sum_congr rfl fun e _ => ?_ ;         show η e ((if e = (inc ((inc.symm (e, 0)).1, 1)).1 ;             then f ((inc ((inc.symm (e, 0)).1, 0)).1) else 0) + ;           (if e = (inc ((inc.symm (e, 1)).1, 1)).1 ;             then f ((inc ((inc.symm (e, 1)).1, 0)).1) else 0)) = ;           ∑ j : Fin 2, η e (if e = (inc ((inc.symm (e, j)).1, 1)).1 ;             then f ((inc ((inc.symm (e, j)).1, 0)).1) else 0) ;         rw [map_add, Fin.sum_univ_two] ;     _ = ∑ s : V × Fin 3, η ((inc s).1) ;           (if (inc s).1 = (inc (s.1, 1)).1 then f ((inc (s.1, 0)).1) else 0) := by ;         refine Eq.trans (Equiv.sum_comp inc (fun p : E × Fin 2 => η p.1 ;           (if p.1 = (inc ((inc.symm p).1, 1)).1 ;             then f ((inc ((inc.symm p).1, 0)).1) else 0))).symm ?_ ;         refine Finset.sum_congr rfl fun s _ => ?_ ;         show η ((inc s).1) ;             (if (inc s).1 = (inc ((inc.symm (inc s)).1, 1)).1 ;               then f ((inc ((inc.symm (inc s)).1, 0)).1) else 0) = _ ;         rw [Equiv.symm_apply_apply] ;     _ = ∑ v : V, ∑ i : Fin 3, η ((inc (v, i)).1) ;           (if (inc (v, i)).1 = (inc (v, 1)).1 then f ((inc (v, 0)).1) else 0) := ;         Fintype.sum_prod_type (f := fun s : V × Fin 3 => η ((inc s).1) ;           (if (inc s).1 = (inc (s.1, 1)).1 then f ((inc (s.1, 0)).1) else 0)) ;     _ = ∑ v : V, η ((inc (v, 1)).1) (f ((inc (v, 0)).1)) := by ;         refine Finset.sum_congr rfl fun v _ => ?_ ;         rw [Fin.sum_univ_three, if_neg (hne v 0 1 (by decide)), if_pos rfl, ;           if_neg (hne v 2 1 (by decide)), map_zero, map_zero, zero_add, add_zero] ;     _ = ∑ v : V, ∑ i : Fin 3, ;           (if code ((inc (v, i)).1) = 0 then (0 : ZMod 2) else 1) := by ;         refine Finset.sum_congr rfl fun v _ => ?_ ;         rw [Fin.sum_univ_three] ;         exact hlocal v ;     _ = ∑ s : V × Fin 3, (if code ((inc s).1) = 0 then (0 : ZMod 2) else 1) := ;         (Fintype.sum_prod_type (f := fun s : V × Fin 3 => ;           if code ((inc s).1) = 0 then (0 : ZMod 2) else 1)).symm ;     _ = ∑ p : E × Fin 2, (if code p.1 = 0 then (0 : ZMod 2) else 1) := ;         Equiv.sum_comp inc (fun p : E × Fin 2 => ;           if code p.1 = 0 then (0 : ZMod 2) else 1) ;     _ = ∑ e : E, ((if code e = 0 then (0 : ZMod 2) else 1) + ;           (if code e = 0 then (0 : ZMod 2) else 1)) := by ;         rw [Fintype.sum_prod_type] ;         refine Finset.sum_congr rfl fun e _ => ?_ ;         rw [Fin.sum_univ_two] ;     _ = 0 := by ;         refine Finset.sum_eq_zero fun e _ => ?_ ;         exact CharTwo.add_self_eq_zero _ ; obtain ⟨x, hx⟩ := LinearMap.mem_range.mp hd ; refine ⟨x.1, x.2, fun e => ?_⟩ ; have hxe := congrFun hx e ; calc x.1 ((inc.symm (e, 0)).1) + x.1 ((inc.symm (e, 1)).1) + x.2 e • f e ;     = (L x) e := by ;       simp only [hLdef, LinearMap.coe_mk, AddHom.coe_mk] ;   _ = (if e = (inc ((inc.symm (e, 0)).1, 1)).1 ;         then f ((inc ((inc.symm (e, 0)).1, 0)).1) else 0) + ;       (if e = (inc ((inc.symm (e, 1)).1, 1)).1 ;         then f ((inc ((inc.symm (e, 1)).1, 0)).1) else 0) := hxe` | ❌ kernel_fail |
| 3 | `root_theorem` | solve | `intro V E _ _ _ _ inc f hloop hnz hcons ; classical ; set L : ((V → (Fin 3 → ZMod 2)) × (E → ZMod 2)) →ₗ[ZMod 2] (E → (Fin 3 → ZMod 2)) := ;   { toFun := fun x e => x.1 ((inc.symm (e, 0)).1) + x.1 ((inc.symm (e, 1)).1) + x.2 e • f e ;     map_add' := by ;       intro x y ;       funext e i ;       simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, Pi.smul_apply, smul_eq_mul] ;       ring ;     map_smul' := by ;       intro c x ;       funext e i ;       simp only [Prod.smul_fst, Prod.smul_snd, Pi.add_apply, Pi.smul_apply, smul_eq_mul, ;         RingHom.id_apply] ;       ring } with hLdef ; have hfin2 : ∀ a b : Fin 2, a ≠ b → a = 0 ∧ b = 1 ∨ a = 1 ∧ b = 0 := by decide ; have hne : ∀ (v : V) (i k : Fin 3), i ≠ k → (inc (v, i)).1 ≠ (inc (v, k)).1 := by ;   intro v i k hik heq ;   by_cases hj : (inc (v, i)).2 = (inc (v, k)).2 ;   · exact hik (congrArg Prod.snd (inc.injective (Prod.ext_iff.mpr ⟨heq, hj⟩))) ;   · have h1 : (inc.symm ((inc (v, i)).1, (inc (v, i)).2)).1 = v := by simp ;     have h2 : (inc.symm ((inc (v, i)).1, (inc (v, k)).2)).1 = v := by ;       rw [heq] ;       simp ;     rcases hfin2 _ _ hj with ⟨hj1, hj2⟩ \| ⟨hj1, hj2⟩ ;     · rw [hj1] at h1 ;       rw [hj2] at h2 ;       exact hloop ((inc (v, i)).1) (h1.trans h2.symm) ;     · rw [hj1] at h1 ;       rw [hj2] at h2 ;       exact hloop ((inc (v, i)).1) (h2.trans h1.symm) ; have hd : (fun e : E => ;     (if e = (inc ((inc.symm (e, 0)).1, 1)).1 ;       then f ((inc ((inc.symm (e, 0)).1, 0)).1) else 0) + ;     (if e = (inc ((inc.symm (e, 1)).1, 1)).1 ;       then f ((inc ((inc.symm (e, 1)).1, 0)).1) else 0)) ∈ LinearMap.range L := by ;   apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff (LinearMap.range L) _).mp ;   intro φ hφann ;   have hφ : ∀ x, φ (L x) = 0 := fun x => ;     (Submodule.mem_dualAnnihilator φ).mp hφann (L x) (LinearMap.mem_range.mpr ⟨x, rfl⟩) ;   set η : E → Module.Dual (ZMod 2) (Fin 3 → ZMod 2) := ;     fun e => φ.comp (LinearMap.single (ZMod 2) (fun _ : E => Fin 3 → ZMod 2) e) with hηdef ;   have hsumcoord : ∀ y : E → Fin 3 → ZMod 2, φ y = ∑ e : E, η e (y e) := by ;     intro y ;     calc φ y = φ (∑ e : E, Pi.single e (y e)) := by rw [Finset.univ_sum_single] ;       _ = ∑ e : E, φ (Pi.single e (y e)) := map_sum φ _ _ ;       _ = ∑ e : E, η e (y e) := Finset.sum_congr rfl fun e _ => by ;           simp [hηdef, LinearMap.single_apply] ;   have hedge : ∀ e : E, η e (f e) = 0 := by ;     intro e ;     set se : E → ZMod 2 := Pi.single e (1 : ZMod 2) with hsedef ;     have hz := hφ ((0 : V → Fin 3 → ZMod 2), se) ;     rw [hsumcoord] at hz ;     have hLk : ∀ k : E, (L ((0 : V → Fin 3 → ZMod 2), se)) k = se k • f k := by ;       intro k ;       simp only [hLdef, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply, zero_add] ;     rw [Finset.sum_congr rfl fun k _ => congrArg (η k) (hLk k)] at hz ;     have hzero : ∀ k : E, k ≠ e → η k (se k • f k) = 0 := by ;       intro k hk ;       rw [hsedef, Pi.single_eq_of_ne hk, zero_smul, map_zero] ;     rw [Fintype.sum_eq_single e hzero, hsedef, Pi.single_eq_same, one_smul] at hz ;     exact hz ;   have hvertex : ∀ v : V, ;       η ((inc (v, 0)).1) + η ((inc (v, 1)).1) + η ((inc (v, 2)).1) = 0 := by ;     intro v ;     refine LinearMap.ext fun q => ?_ ;     set sq : V → Fin 3 → ZMod 2 := Pi.single v q with hsqdef ;     have hz := hφ (sq, (0 : E → ZMod 2)) ;     rw [hsumcoord] at hz ;     have hLk : ∀ k : E, (L (sq, (0 : E → ZMod 2))) k = ;         sq ((inc.symm (k, 0)).1) + sq ((inc.symm (k, 1)).1) := by ;       intro k ;       simp only [hLdef, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply, zero_smul, add_zero] ;     rw [Finset.sum_congr rfl fun k _ => congrArg (η k) (hLk k)] at hz ;     have hsplit : (∑ k : E, η k (sq ((inc.symm (k, 0)).1) + sq ((inc.symm (k, 1)).1))) = ;         ∑ k : E, ∑ j : Fin 2, η k (sq ((inc.symm (k, j)).1)) := by ;       refine Finset.sum_congr rfl fun k _ => ?_ ;       rw [map_add, Fin.sum_univ_two] ;     rw [hsplit] at hz ;     have hprod : (∑ k : E, ∑ j : Fin 2, η k (sq ((inc.symm (k, j)).1))) = ;         ∑ p : E × Fin 2, η p.1 (sq ((inc.symm p).1)) := ;       (Fintype.sum_prod_type (f := fun p : E × Fin 2 => ;         η p.1 (sq ((inc.symm p).1)))).symm ;     rw [hprod] at hz ;     have hcomp : (∑ s : V × Fin 3, η ((inc s).1) (sq s.1)) = ;         ∑ p : E × Fin 2, η p.1 (sq ((inc.symm p).1)) := by ;       refine Eq.trans ?_ (Equiv.sum_comp inc (fun p : E × Fin 2 => ;         η p.1 (sq ((inc.symm p).1)))) ;       refine Finset.sum_congr rfl fun s _ => ?_ ;       show η ((inc s).1) (sq s.1) = η ((inc s).1) (sq ((inc.symm (inc s)).1)) ;       rw [Equiv.symm_apply_apply] ;     rw [← hcomp] at hz ;     have hVsum : (∑ w : V, ∑ i : Fin 3, η ((inc (w, i)).1) (sq w)) = ;         ∑ s : V × Fin 3, η ((inc s).1) (sq s.1) := ;       (Fintype.sum_prod_type (f := fun s : V × Fin 3 => ;         η ((inc s).1) (sq s.1))).symm ;     rw [← hVsum] at hz ;     have hzero : ∀ w : V, w ≠ v → (∑ i : Fin 3, η ((inc (w, i)).1) (sq w)) = 0 := by ;       intro w hw ;       refine Finset.sum_eq_zero fun i _ => ?_ ;       rw [hsqdef, Pi.single_eq_of_ne hw, map_zero] ;     rw [Fintype.sum_eq_single v hzero, Fin.sum_univ_three, hsqdef] at hz ;     simp only [Pi.single_eq_same] at hz ;     simpa [LinearMap.add_apply] using hz ;   have hldi : ∀ x y a b c : Fin 3 → ZMod 2, ;       x ≠ 0 → y ≠ 0 → x ≠ y → a + b + c = 0 → ;       (∑ i : Fin 3, x i * a i) = 0 → ;       (∑ i : Fin 3, y i * b i) = 0 → ;       (∑ i : Fin 3, (x + y) i * c i) = 0 → ;       (∑ i : Fin 3, x i * b i) = ;         (if a = 0 then (0 : ZMod 2) else 1) + (if b = 0 then (0 : ZMod 2) else 1) + ;           (if c = 0 then (0 : ZMod 2) else 1) := by ;     decide ;   have hft : ∀ x y z : Fin 3 → ZMod 2, ;       x ≠ 0 → y ≠ 0 → z ≠ 0 → x + y + z = 0 → z = x + y ∧ x ≠ y := by ;     decide ;   set code : E → Fin 3 → ZMod 2 := fun e i => η e (Pi.single i 1) with hcodedef ;   have happly : ∀ (e : E) (x : Fin 3 → ZMod 2), η e x = ∑ i : Fin 3, x i * code e i := by ;     intro e x ;     calc η e x = η e (∑ i : Fin 3, Pi.single i (x i)) := by rw [Finset.univ_sum_single] ;       _ = ∑ i : Fin 3, η e (Pi.single i (x i)) := map_sum (η e) _ _ ;       _ = ∑ i : Fin 3, x i * code e i := Finset.sum_congr rfl fun i _ => by ;           have hone : (Pi.single i (x i) : Fin 3 → ZMod 2) = ;               x i • Pi.single i (1 : ZMod 2) := by ;             rw [← Pi.single_smul, smul_eq_mul, mul_one] ;           rw [hone, map_smul, smul_eq_mul, hcodedef] ;   have hlocal : ∀ v : V, ;       η ((inc (v, 1)).1) (f ((inc (v, 0)).1)) = ;         (if code ((inc (v, 0)).1) = 0 then (0 : ZMod 2) else 1) + ;         (if code ((inc (v, 1)).1) = 0 then (0 : ZMod 2) else 1) + ;         (if code ((inc (v, 2)).1) = 0 then (0 : ZMod 2) else 1) := by ;     intro v ;     have hsum3 : f ((inc (v, 0)).1) + f ((inc (v, 1)).1) + f ((inc (v, 2)).1) = 0 := by ;       have h := hcons v ;       rwa [Fin.sum_univ_three] at h ;     obtain ⟨hz2, hxy⟩ := hft _ _ _ (hnz _) (hnz _) (hnz _) hsum3 ;     have hcsum : code ((inc (v, 0)).1) + code ((inc (v, 1)).1) + code ((inc (v, 2)).1) = 0 := by ;       funext k ;       have hq := LinearMap.congr_fun (hvertex v) (Pi.single k 1) ;       simpa [hcodedef, LinearMap.add_apply] using hq ;     have h0 : (∑ i : Fin 3, f ((inc (v, 0)).1) i * code ((inc (v, 0)).1) i) = 0 := by ;       rw [← happly] ;       exact hedge _ ;     have h1 : (∑ i : Fin 3, f ((inc (v, 1)).1) i * code ((inc (v, 1)).1) i) = 0 := by ;       rw [← happly] ;       exact hedge _ ;     have h2 : (∑ i : Fin 3, ;         (f ((inc (v, 0)).1) + f ((inc (v, 1)).1)) i * code ((inc (v, 2)).1) i) = 0 := by ;       rw [← hz2, ← happly] ;       exact hedge _ ;     have hmain := hldi (f ((inc (v, 0)).1)) (f ((inc (v, 1)).1)) ;       (code ((inc (v, 0)).1)) (code ((inc (v, 1)).1)) (code ((inc (v, 2)).1)) ;       (hnz _) (hnz _) hxy hcsum h0 h1 h2 ;     rw [happly] ;     exact hmain ;   calc φ (fun e : E => ;         (if e = (inc ((inc.symm (e, 0)).1, 1)).1 ;           then f ((inc ((inc.symm (e, 0)).1, 0)).1) else 0) + ;         (if e = (inc ((inc.symm (e, 1)).1, 1)).1 ;           then f ((inc ((inc.symm (e, 1)).1, 0)).1) else 0)) ;       = ∑ p : E × Fin 2, η p.1 ;           (if p.1 = (inc ((inc.symm p).1, 1)).1 ;             then f ((inc ((inc.symm p).1, 0)).1) else 0) := by ;         rw [hsumcoord] ;         refine Eq.trans ?_ (Fintype.sum_prod_type (f := fun p : E × Fin 2 => η p.1 ;           (if p.1 = (inc ((inc.symm p).1, 1)).1 ;             then f ((inc ((inc.symm p).1, 0)).1) else 0))).symm ;         refine Finset.sum_congr rfl fun e _ => ?_ ;         show η e ((if e = (inc ((inc.symm (e, 0)).1, 1)).1 ;             then f ((inc ((inc.symm (e, 0)).1, 0)).1) else 0) + ;           (if e = (inc ((inc.symm (e, 1)).1, 1)).1 ;             then f ((inc ((inc.symm (e, 1)).1, 0)).1) else 0)) = ;           ∑ j : Fin 2, η e (if e = (inc ((inc.symm (e, j)).1, 1)).1 ;             then f ((inc ((inc.symm (e, j)).1, 0)).1) else 0) ;         rw [map_add, Fin.sum_univ_two] ;     _ = ∑ s : V × Fin 3, η ((inc s).1) ;           (if (inc s).1 = (inc (s.1, 1)).1 then f ((inc (s.1, 0)).1) else 0) := by ;         refine Eq.trans (Equiv.sum_comp inc (fun p : E × Fin 2 => η p.1 ;           (if p.1 = (inc ((inc.symm p).1, 1)).1 ;             then f ((inc ((inc.symm p).1, 0)).1) else 0))).symm ?_ ;         refine Finset.sum_congr rfl fun s _ => ?_ ;         show η ((inc s).1) ;             (if (inc s).1 = (inc ((inc.symm (inc s)).1, 1)).1 ;               then f ((inc ((inc.symm (inc s)).1, 0)).1) else 0) = _ ;         rw [Equiv.symm_apply_apply] ;     _ = ∑ v : V, ∑ i : Fin 3, η ((inc (v, i)).1) ;           (if (inc (v, i)).1 = (inc (v, 1)).1 then f ((inc (v, 0)).1) else 0) := ;         Fintype.sum_prod_type (f := fun s : V × Fin 3 => η ((inc s).1) ;           (if (inc s).1 = (inc (s.1, 1)).1 then f ((inc (s.1, 0)).1) else 0)) ;     _ = ∑ v : V, η ((inc (v, 1)).1) (f ((inc (v, 0)).1)) := by ;         refine Finset.sum_congr rfl fun v _ => ?_ ;         rw [Fin.sum_univ_three, if_neg (hne v 0 1 (by decide)), if_pos rfl, ;           if_neg (hne v 2 1 (by decide)), map_zero, map_zero, zero_add, add_zero] ;     _ = ∑ v : V, ∑ i : Fin 3, ;           (if code ((inc (v, i)).1) = 0 then (0 : ZMod 2) else 1) := by ;         refine Finset.sum_congr rfl fun v _ => ?_ ;         rw [Fin.sum_univ_three] ;         exact hlocal v ;     _ = ∑ s : V × Fin 3, (if code ((inc s).1) = 0 then (0 : ZMod 2) else 1) := ;         (Fintype.sum_prod_type (f := fun s : V × Fin 3 => ;           if code ((inc s).1) = 0 then (0 : ZMod 2) else 1)).symm ;     _ = ∑ p : E × Fin 2, (if code p.1 = 0 then (0 : ZMod 2) else 1) := ;         Equiv.sum_comp inc (fun p : E × Fin 2 => ;           if code p.1 = 0 then (0 : ZMod 2) else 1) ;     _ = ∑ e : E, ((if code e = 0 then (0 : ZMod 2) else 1) + ;           (if code e = 0 then (0 : ZMod 2) else 1)) := by ;         rw [Fintype.sum_prod_type] ;         refine Finset.sum_congr rfl fun e _ => ?_ ;         rw [Fin.sum_univ_two] ;     _ = 0 := by ;         refine Finset.sum_eq_zero fun e _ => ?_ ;         exact CharTwo.add_self_eq_zero _ ; obtain ⟨x, hx⟩ := LinearMap.mem_range.mp hd ; refine ⟨x.1, x.2, fun e => ?_⟩ ; have hxe := congrFun hx e ; calc x.1 ((inc.symm (e, 0)).1) + x.1 ((inc.symm (e, 1)).1) + x.2 e • f e ;     = (L x) e := by ;       simp only [hLdef, LinearMap.coe_mk, AddHom.coe_mk] ;   _ = (if e = (inc ((inc.symm (e, 0)).1, 1)).1 ;         then f ((inc ((inc.symm (e, 0)).1, 0)).1) else 0) + ;       (if e = (inc ((inc.symm (e, 1)).1, 1)).1 ;         then f ((inc ((inc.symm (e, 1)).1, 0)).1) else 0) := hxe` | ✅ kernel_pass |

## Verification context

- **Environment hash:** `9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d`
- **Import manifest hash:** `b71c3c9da913b2ce43017a08a69ccf102d0e4a6d621776a18c3ef555960af7fc`
- **Import manifest:** `["Mathlib"]`
- **proof_body_redacted:** false

## Integrity

4 hash-chained trajectory events, `13c2e4525e44…` → `be049f7d110f…` (GENESIS-anchored). Re-verify anytime with `episode_replay`.
