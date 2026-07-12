# ⚠️ KERNEL-VERIFIED FORMAL STATEMENT — FIDELITY NOT YET VERIFIED — CDC paper: a nowhere-zero F2^3-flow on the vertex-ring expansion yields the localized expansion cover (mirrors CDCLean.cubicExpansion + expansionIncidence + applying cubic_even_double_cover to the expansion). The vertex-ring expansion of a multigraph with a fixed-point-free half-edge rotation is itself a slot-equivalence cubic multigraph: vertices are half-edges, edges are spokes (inl) plus rings (inr), with slot 0 the spoke, slot 1 the outgoing ring, slot 2 the incoming ring named by next.symm; looplessness of rings is exactly fixed-point-freeness. Taking the FULL slot-form even-double-cover theorem (the verified statement of problem 3917309c) as a hypothesis and instantiating it at this incidence equivalence with a nowhere-zero flow whose conservation is given in localized triple form produces the localized cover consumed by the projection step (problem b202d6d2). First use of theorem-as-hypothesis chaining across problems. Pre-flighted clean on the pinned lean-checker in 14.8s.

> This proof establishes:
>
> `∀ (E : Type) [Fintype E] [DecidableEq E] (next : Equiv.Perm (E × Fin 2)),
  (∀ h : E × Fin 2, next h ≠ h) →
  (∀ (V' E' : Type) [Fintype V'] [Fintype E'] [DecidableEq V'] [DecidableEq E']
      (inc : (V' × Fin 3) ≃ (E' × Fin 2)) (f : E' → (Fin 3 → ZMod 2)),
    (∀ e : E', (inc.symm (e, 0)).1 ≠ (inc.symm (e, 1)).1) →
    (∀ e : E', f e ≠ 0) →
    (∀ v : V', (∑ i : Fin 3, f ((inc (v, i)).1)) = 0) →
    ∃ member : (Fin 3 → ZMod 2) → E' → ZMod 2,
      (∀ (s : Fin 3 → ZMod 2) (v : V'),
        (∑ i : Fin 3, member s ((inc (v, i)).1)) = 0) ∧
      (∀ e : E',
        (Finset.univ.filter fun s : Fin 3 → ZMod 2 => member s e = 1).card = 2)) →
  ∀ fK : (E ⊕ (E × Fin 2)) → (Fin 3 → ZMod 2),
    (∀ k, fK k ≠ 0) →
    (∀ h : E × Fin 2,
      fK (Sum.inl h.1) + fK (Sum.inr h) + fK (Sum.inr (next.symm h)) = 0) →
    ∃ memberK : (Fin 3 → ZMod 2) → (E ⊕ (E × Fin 2)) → ZMod 2,
      (∀ (s : Fin 3 → ZMod 2) (h : E × Fin 2),
        memberK s (Sum.inl h.1) + memberK s (Sum.inr h) +
          memberK s (Sum.inr (next.symm h)) = 0) ∧
      (∀ e : E, (Finset.univ.filter fun s : Fin 3 → ZMod 2 =>
        memberK s (Sum.inl e) = 1).card = 2)`
>
> It does **not yet** certify the source claim above.

**Root goal (formal):** `∀ (E : Type) [Fintype E] [DecidableEq E] (next : Equiv.Perm (E × Fin 2)),
  (∀ h : E × Fin 2, next h ≠ h) →
  (∀ (V' E' : Type) [Fintype V'] [Fintype E'] [DecidableEq V'] [DecidableEq E']
      (inc : (V' × Fin 3) ≃ (E' × Fin 2)) (f : E' → (Fin 3 → ZMod 2)),
    (∀ e : E', (inc.symm (e, 0)).1 ≠ (inc.symm (e, 1)).1) →
    (∀ e : E', f e ≠ 0) →
    (∀ v : V', (∑ i : Fin 3, f ((inc (v, i)).1)) = 0) →
    ∃ member : (Fin 3 → ZMod 2) → E' → ZMod 2,
      (∀ (s : Fin 3 → ZMod 2) (v : V'),
        (∑ i : Fin 3, member s ((inc (v, i)).1)) = 0) ∧
      (∀ e : E',
        (Finset.univ.filter fun s : Fin 3 → ZMod 2 => member s e = 1).card = 2)) →
  ∀ fK : (E ⊕ (E × Fin 2)) → (Fin 3 → ZMod 2),
    (∀ k, fK k ≠ 0) →
    (∀ h : E × Fin 2,
      fK (Sum.inl h.1) + fK (Sum.inr h) + fK (Sum.inr (next.symm h)) = 0) →
    ∃ memberK : (Fin 3 → ZMod 2) → (E ⊕ (E × Fin 2)) → ZMod 2,
      (∀ (s : Fin 3 → ZMod 2) (h : E × Fin 2),
        memberK s (Sum.inl h.1) + memberK s (Sum.inr h) +
          memberK s (Sum.inr (next.symm h)) = 0) ∧
      (∀ e : E, (Finset.univ.filter fun s : Fin 3 → ZMod 2 =>
        memberK s (Sum.inl e) = 1).card = 2)`

| Proof soundness | Statement fidelity | Canonical promotion | Training eligibility |
|---|---|---|---|
| VERIFIED | ATTESTED (unsafe_dev_attestation — not reviewed) | BLOCKED | QUARANTINED |

| episode | state | steps | budget left (μ$) | started | finished |
|---|---|---|---|---|---|
| `dcc3a393-8dcd-4673-9757-4e4b91e7365d` | terminated (root_proved) | 1 | — | 2026-07-11T17:16:15 | 2026-07-11T17:17:23 |

## Proof tree

- ✅ **root_theorem** : `∀ (E : Type) [Fintype E] [DecidableEq E] (next : Equiv.Perm (E × Fin 2)),
  (∀ h : E × Fin 2, next h ≠ h) →
  (∀ (V' E' : Type) [Fintype V'] [Fintype E'] [DecidableEq V'] [DecidableEq E']
      (inc : (V' × Fin 3) ≃ (E' × Fin 2)) (f : E' → (Fin 3 → ZMod 2)),
    (∀ e : E', (inc.symm (e, 0)).1 ≠ (inc.symm (e, 1)).1) →
    (∀ e : E', f e ≠ 0) →
    (∀ v : V', (∑ i : Fin 3, f ((inc (v, i)).1)) = 0) →
    ∃ member : (Fin 3 → ZMod 2) → E' → ZMod 2,
      (∀ (s : Fin 3 → ZMod 2) (v : V'),
        (∑ i : Fin 3, member s ((inc (v, i)).1)) = 0) ∧
      (∀ e : E',
        (Finset.univ.filter fun s : Fin 3 → ZMod 2 => member s e = 1).card = 2)) →
  ∀ fK : (E ⊕ (E × Fin 2)) → (Fin 3 → ZMod 2),
    (∀ k, fK k ≠ 0) →
    (∀ h : E × Fin 2,
      fK (Sum.inl h.1) + fK (Sum.inr h) + fK (Sum.inr (next.symm h)) = 0) →
    ∃ memberK : (Fin 3 → ZMod 2) → (E ⊕ (E × Fin 2)) → ZMod 2,
      (∀ (s : Fin 3 → ZMod 2) (h : E × Fin 2),
        memberK s (Sum.inl h.1) + memberK s (Sum.inr h) +
          memberK s (Sum.inr (next.symm h)) = 0) ∧
      (∀ e : E, (Finset.univ.filter fun s : Fin 3 → ZMod 2 =>
        memberK s (Sum.inl e) = 1).card = 2)`

## The proof, assembled

```lean
import Mathlib

theorem root_theorem : ∀ (E : Type) [Fintype E] [DecidableEq E] (next : Equiv.Perm (E × Fin 2)),
  (∀ h : E × Fin 2, next h ≠ h) →
  (∀ (V' E' : Type) [Fintype V'] [Fintype E'] [DecidableEq V'] [DecidableEq E']
      (inc : (V' × Fin 3) ≃ (E' × Fin 2)) (f : E' → (Fin 3 → ZMod 2)),
    (∀ e : E', (inc.symm (e, 0)).1 ≠ (inc.symm (e, 1)).1) →
    (∀ e : E', f e ≠ 0) →
    (∀ v : V', (∑ i : Fin 3, f ((inc (v, i)).1)) = 0) →
    ∃ member : (Fin 3 → ZMod 2) → E' → ZMod 2,
      (∀ (s : Fin 3 → ZMod 2) (v : V'),
        (∑ i : Fin 3, member s ((inc (v, i)).1)) = 0) ∧
      (∀ e : E',
        (Finset.univ.filter fun s : Fin 3 → ZMod 2 => member s e = 1).card = 2)) →
  ∀ fK : (E ⊕ (E × Fin 2)) → (Fin 3 → ZMod 2),
    (∀ k, fK k ≠ 0) →
    (∀ h : E × Fin 2,
      fK (Sum.inl h.1) + fK (Sum.inr h) + fK (Sum.inr (next.symm h)) = 0) →
    ∃ memberK : (Fin 3 → ZMod 2) → (E ⊕ (E × Fin 2)) → ZMod 2,
      (∀ (s : Fin 3 → ZMod 2) (h : E × Fin 2),
        memberK s (Sum.inl h.1) + memberK s (Sum.inr h) +
          memberK s (Sum.inr (next.symm h)) = 0) ∧
      (∀ e : E, (Finset.univ.filter fun s : Fin 3 → ZMod 2 =>
        memberK s (Sum.inl e) = 1).card = 2) := by
intro E _ _ next hne h08 fK hnz hcons
set incK : ((E × Fin 2) × Fin 3) ≃ ((E ⊕ (E × Fin 2)) × Fin 2) :=
  { toFun := fun p =>
      match p.2 with
      | 0 => (Sum.inl p.1.1, p.1.2)
      | 1 => (Sum.inr p.1, 0)
      | 2 => (Sum.inr (next.symm p.1), 1)
    invFun := fun q =>
      match q.1, q.2 with
      | Sum.inl e, j => ((e, j), 0)
      | Sum.inr k, 0 => (k, 1)
      | Sum.inr k, 1 => (next k, 2)
    left_inv := by
      rintro ⟨h, i⟩
      fin_cases i
      · rfl
      · rfl
      · show (next (next.symm h), 2) = (h, 2)
        rw [Equiv.apply_symm_apply]
    right_inv := by
      rintro ⟨e | k, j⟩
      · fin_cases j <;> rfl
      · fin_cases j
        · rfl
        · show (Sum.inr (next.symm (next k)), (1 : Fin 2)) = (Sum.inr k, 1)
          rw [Equiv.symm_apply_apply] } with hinc
have hloopK : ∀ k : E ⊕ (E × Fin 2), (incK.symm (k, 0)).1 ≠ (incK.symm (k, 1)).1 := by
  rintro (e | k) heq
  · rw [hinc] at heq
    have h2 : ((e, 0) : E × Fin 2) = ((e, 1) : E × Fin 2) := heq
    have h3 : (0 : Fin 2) = 1 := congrArg Prod.snd h2
    exact absurd h3 (by decide)
  · rw [hinc] at heq
    have h2 : k = next k := heq
    exact hne k h2.symm
have hconsK : ∀ w : E × Fin 2, (∑ i : Fin 3, fK ((incK (w, i)).1)) = 0 := by
  intro w
  rw [Fin.sum_univ_three, hinc]
  show fK (Sum.inl w.1) + fK (Sum.inr w) + fK (Sum.inr (next.symm w)) = 0
  exact hcons w
obtain ⟨member, hEven, hTwo⟩ :=
  h08 (E × Fin 2) (E ⊕ (E × Fin 2)) incK fK hloopK hnz hconsK
refine ⟨member, ?_, ?_⟩
· intro s h
  have hE := hEven s h
  rw [Fin.sum_univ_three, hinc] at hE
  exact hE
· intro e
  exact hTwo (Sum.inl e)

```

## How it went — every attempt, in order

| # | obligation | action | detail | verdict |
|---|---|---|---|---|
| 2 | `root_theorem` | solve | `intro E _ _ next hne h08 fK hnz hcons ; set incK : ((E × Fin 2) × Fin 3) ≃ ((E ⊕ (E × Fin 2)) × Fin 2) := ;   { toFun := fun p => ;       match p.2 with ;       \| 0 => (Sum.inl p.1.1, p.1.2) ;       \| 1 => (Sum.inr p.1, 0) ;       \| 2 => (Sum.inr (next.symm p.1), 1) ;     invFun := fun q => ;       match q.1, q.2 with ;       \| Sum.inl e, j => ((e, j), 0) ;       \| Sum.inr k, 0 => (k, 1) ;       \| Sum.inr k, 1 => (next k, 2) ;     left_inv := by ;       rintro ⟨h, i⟩ ;       fin_cases i ;       · rfl ;       · rfl ;       · show (next (next.symm h), 2) = (h, 2) ;         rw [Equiv.apply_symm_apply] ;     right_inv := by ;       rintro ⟨e \| k, j⟩ ;       · fin_cases j <;> rfl ;       · fin_cases j ;         · rfl ;         · show (Sum.inr (next.symm (next k)), (1 : Fin 2)) = (Sum.inr k, 1) ;           rw [Equiv.symm_apply_apply] } with hinc ; have hloopK : ∀ k : E ⊕ (E × Fin 2), (incK.symm (k, 0)).1 ≠ (incK.symm (k, 1)).1 := by ;   rintro (e \| k) heq ;   · rw [hinc] at heq ;     have h2 : ((e, 0) : E × Fin 2) = ((e, 1) : E × Fin 2) := heq ;     have h3 : (0 : Fin 2) = 1 := congrArg Prod.snd h2 ;     exact absurd h3 (by decide) ;   · rw [hinc] at heq ;     have h2 : k = next k := heq ;     exact hne k h2.symm ; have hconsK : ∀ w : E × Fin 2, (∑ i : Fin 3, fK ((incK (w, i)).1)) = 0 := by ;   intro w ;   rw [Fin.sum_univ_three, hinc] ;   show fK (Sum.inl w.1) + fK (Sum.inr w) + fK (Sum.inr (next.symm w)) = 0 ;   exact hcons w ; obtain ⟨member, hEven, hTwo⟩ := ;   h08 (E × Fin 2) (E ⊕ (E × Fin 2)) incK fK hloopK hnz hconsK ; refine ⟨member, ?_, ?_⟩ ; · intro s h ;   have hE := hEven s h ;   rw [Fin.sum_univ_three, hinc] at hE ;   exact hE ; · intro e ;   exact hTwo (Sum.inl e)` | ✅ kernel_pass |

## Verification context

- **Environment hash:** `9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d`
- **Import manifest hash:** `b71c3c9da913b2ce43017a08a69ccf102d0e4a6d621776a18c3ef555960af7fc`
- **Import manifest:** `["Mathlib"]`
- **proof_body_redacted:** false

## Integrity

3 hash-chained trajectory events, `66bfd800f4f1…` → `442e2ad7d02e…` (GENESIS-anchored). Re-verify anytime with `episode_replay`.
