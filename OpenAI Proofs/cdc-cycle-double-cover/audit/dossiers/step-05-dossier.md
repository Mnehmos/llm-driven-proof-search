# ⚠️ KERNEL-VERIFIED FORMAL STATEMENT — FIDELITY NOT YET VERIFIED — Derived manuscript annihilator uniqueness: in a three-dimensional vector space over a two-element field, two distinct nonzero vectors span a plane, and any two nonzero dual vectors vanishing on both are equal.

> This proof establishes:
>
> `∀ (K Γ : Type) [Field K] [AddCommGroup Γ] [Module K Γ]
    [FiniteDimensional K Γ] (x y : Γ),
  (∀ c : K, c = 0 ∨ c = 1) →
  Module.finrank K Γ = 3 →
  x ≠ 0 → y ≠ 0 → x ≠ y →
  ∀ p q : Module.Dual K Γ,
    p ≠ 0 → q ≠ 0 →
    p x = 0 → p y = 0 → q x = 0 → q y = 0 → p = q`
>
> It does **not yet** certify the source claim above.

**Root goal (formal):** `∀ (K Γ : Type) [Field K] [AddCommGroup Γ] [Module K Γ]
    [FiniteDimensional K Γ] (x y : Γ),
  (∀ c : K, c = 0 ∨ c = 1) →
  Module.finrank K Γ = 3 →
  x ≠ 0 → y ≠ 0 → x ≠ y →
  ∀ p q : Module.Dual K Γ,
    p ≠ 0 → q ≠ 0 →
    p x = 0 → p y = 0 → q x = 0 → q y = 0 → p = q`

| Proof soundness | Statement fidelity | Canonical promotion | Training eligibility |
|---|---|---|---|
| VERIFIED | ATTESTED (unsafe_dev_attestation — not reviewed) | BLOCKED | QUARANTINED |

| episode | state | steps | budget left (μ$) | started | finished |
|---|---|---|---|---|---|
| `9763965c-5107-45db-bc6e-f5b2e391b250` | terminated (root_proved) | 1 | — | 2026-07-11T06:38:14 | 2026-07-11T06:41:05 |

## Proof tree

- ✅ **root_theorem** : `∀ (K Γ : Type) [Field K] [AddCommGroup Γ] [Module K Γ]
    [FiniteDimensional K Γ] (x y : Γ),
  (∀ c : K, c = 0 ∨ c = 1) →
  Module.finrank K Γ = 3 →
  x ≠ 0 → y ≠ 0 → x ≠ y →
  ∀ p q : Module.Dual K Γ,
    p ≠ 0 → q ≠ 0 →
    p x = 0 → p y = 0 → q x = 0 → q y = 0 → p = q`

## The proof, assembled

```lean
import Mathlib

theorem root_theorem : ∀ (K Γ : Type) [Field K] [AddCommGroup Γ] [Module K Γ]
    [FiniteDimensional K Γ] (x y : Γ),
  (∀ c : K, c = 0 ∨ c = 1) →
  Module.finrank K Γ = 3 →
  x ≠ 0 → y ≠ 0 → x ≠ y →
  ∀ p q : Module.Dual K Γ,
    p ≠ 0 → q ≠ 0 →
    p x = 0 → p y = 0 → q x = 0 → q y = 0 → p = q := by
intro K Γ _ _ _ _ x y htwo hrank hx hy hxy p q hp hq hpx hpy hqx hqy
have hli : LinearIndependent K ![x, y] := by
  rw [linearIndependent_fin2]
  constructor
  · simpa using hy
  · intro a ha
    simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero] at ha
    rcases htwo a with h0 | h1
    · rw [h0, zero_smul] at ha
      exact hx ha.symm
    · rw [h1, one_smul] at ha
      exact hxy ha.symm
have hW2 : Module.finrank K (Submodule.span K (Set.range ![x, y])) = 2 := by
  rw [finrank_span_eq_card hli]
  simp
have hsum := Subspace.finrank_add_finrank_dualAnnihilator_eq (Submodule.span K (Set.range ![x, y]))
rw [hW2, hrank] at hsum
have hann : Module.finrank K (Submodule.span K (Set.range ![x, y])).dualAnnihilator = 1 := by
  omega
have hker : ∀ r : Module.Dual K Γ, r x = 0 → r y = 0 →
    r ∈ (Submodule.span K (Set.range ![x, y])).dualAnnihilator := by
  intro r hrx hry
  rw [Submodule.mem_dualAnnihilator]
  intro w hw
  have hle : Submodule.span K (Set.range ![x, y]) ≤ LinearMap.ker r := by
    rw [Submodule.span_le]
    rintro v ⟨i, rfl⟩
    fin_cases i
    · simpa using hrx
    · simpa using hry
  exact LinearMap.mem_ker.mp (hle hw)
have hpA : p ∈ (Submodule.span K (Set.range ![x, y])).dualAnnihilator := hker p hpx hpy
have hqA : q ∈ (Submodule.span K (Set.range ![x, y])).dualAnnihilator := hker q hqx hqy
have hp0 : (⟨p, hpA⟩ : (Submodule.span K (Set.range ![x, y])).dualAnnihilator) ≠ 0 := by
  intro h
  exact hp (by simpa using congrArg Subtype.val h)
have hall := (finrank_eq_one_iff_of_nonzero'
  (⟨p, hpA⟩ : (Submodule.span K (Set.range ![x, y])).dualAnnihilator) hp0).mp hann
obtain ⟨c, hc⟩ := hall ⟨q, hqA⟩
rcases htwo c with h0 | h1
· exfalso
  rw [h0, zero_smul] at hc
  exact hq (by simpa using congrArg Subtype.val hc.symm)
· rw [h1, one_smul] at hc
  simpa using congrArg Subtype.val hc

```

## How it went — every attempt, in order

| # | obligation | action | detail | verdict |
|---|---|---|---|---|
| 2 | `root_theorem` | solve | `intro K Γ _ _ _ _ x y htwo hrank hx hy hxy p q hp hq hpx hpy hqx hqy ; have hli : LinearIndependent K ![x, y] := by ;   rw [linearIndependent_fin2] ;   constructor ;   · simpa using hy ;   · intro a ha ;     simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero] at ha ;     rcases htwo a with h0 \| h1 ;     · rw [h0, zero_smul] at ha ;       exact hx ha.symm ;     · rw [h1, one_smul] at ha ;       exact hxy ha.symm ; have hW2 : Module.finrank K (Submodule.span K (Set.range ![x, y])) = 2 := by ;   rw [finrank_span_eq_card hli] ;   simp ; have hsum := Subspace.finrank_add_finrank_dualAnnihilator_eq (Submodule.span K (Set.range ![x, y])) ; rw [hW2, hrank] at hsum ; have hann : Module.finrank K (Submodule.span K (Set.range ![x, y])).dualAnnihilator = 1 := by ;   omega ; have hker : ∀ r : Module.Dual K Γ, r x = 0 → r y = 0 → ;     r ∈ (Submodule.span K (Set.range ![x, y])).dualAnnihilator := by ;   intro r hrx hry ;   rw [Submodule.mem_dualAnnihilator] ;   intro w hw ;   have hle : Submodule.span K (Set.range ![x, y]) ≤ LinearMap.ker r := by ;     rw [Submodule.span_le] ;     rintro v ⟨i, rfl⟩ ;     fin_cases i ;     · simpa using hrx ;     · simpa using hry ;   exact LinearMap.mem_ker.mp (hle hw) ; have hpA : p ∈ (Submodule.span K (Set.range ![x, y])).dualAnnihilator := hker p hpx hpy ; have hqA : q ∈ (Submodule.span K (Set.range ![x, y])).dualAnnihilator := hker q hqx hqy ; have hp0 : (⟨p, hpA⟩ : (Submodule.span K (Set.range ![x, y])).dualAnnihilator) ≠ 0 := by ;   intro h ;   exact hp (by simpa using congrArg Subtype.val h) ; have hall := (finrank_eq_one_iff_of_nonzero' ;   (⟨p, hpA⟩ : (Submodule.span K (Set.range ![x, y])).dualAnnihilator) hp0).mp hann ; obtain ⟨c, hc⟩ := hall ⟨q, hqA⟩ ; rcases htwo c with h0 \| h1 ; · exfalso ;   rw [h0, zero_smul] at hc ;   exact hq (by simpa using congrArg Subtype.val hc.symm) ; · rw [h1, one_smul] at hc ;   simpa using congrArg Subtype.val hc` | ✅ kernel_pass |

## Verification context

- **Environment hash:** `9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d`
- **Import manifest hash:** `b71c3c9da913b2ce43017a08a69ccf102d0e4a6d621776a18c3ef555960af7fc`
- **Import manifest:** `["Mathlib"]`
- **proof_body_redacted:** false

## Integrity

3 hash-chained trajectory events, `3f5623b17a55…` → `fc22898483fd…` (GENESIS-anchored). Re-verify anytime with `episode_replay`.
