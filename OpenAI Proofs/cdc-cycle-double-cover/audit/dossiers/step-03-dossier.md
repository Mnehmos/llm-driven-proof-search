# ⚠️ KERNEL-VERIFIED FORMAL STATEMENT — FIDELITY NOT YET VERIFIED — Abstract vertex calculation for manuscript equations (7)–(9): if ηc=ηa+ηb satisfies the three flow-orthogonality constraints and the common annihilator of x,y has a unique nonzero member, then λ=ηb(x) is the parity of the nonzero ηa,ηb,ηc.

> This proof establishes:
>
> `∀ (K Γ : Type) [Field K] [CharP K 2]
    [AddCommGroup Γ] [Module K Γ]
    (χ : Module.Dual K Γ → K) (x y : Γ)
    (a b : Module.Dual K Γ),
  (∀ c : K, c = 0 ∨ c = 1) →
  χ 0 = 0 →
  (∀ η : Module.Dual K Γ, η ≠ 0 → χ η = 1) →
  (∀ p q : Module.Dual K Γ,
    p ≠ 0 → q ≠ 0 →
    p x = 0 → p y = 0 → q x = 0 → q y = 0 → p = q) →
  a x = 0 → b y = 0 → (a + b) (x + y) = 0 →
  b x = χ a + χ b + χ (a + b)`
>
> It does **not yet** certify the source claim above.

**Root goal (formal):** `∀ (K Γ : Type) [Field K] [CharP K 2]
    [AddCommGroup Γ] [Module K Γ]
    (χ : Module.Dual K Γ → K) (x y : Γ)
    (a b : Module.Dual K Γ),
  (∀ c : K, c = 0 ∨ c = 1) →
  χ 0 = 0 →
  (∀ η : Module.Dual K Γ, η ≠ 0 → χ η = 1) →
  (∀ p q : Module.Dual K Γ,
    p ≠ 0 → q ≠ 0 →
    p x = 0 → p y = 0 → q x = 0 → q y = 0 → p = q) →
  a x = 0 → b y = 0 → (a + b) (x + y) = 0 →
  b x = χ a + χ b + χ (a + b)`

| Proof soundness | Statement fidelity | Canonical promotion | Training eligibility |
|---|---|---|---|
| VERIFIED | ATTESTED (unsafe_dev_attestation — not reviewed) | BLOCKED | QUARANTINED |

| episode | state | steps | budget left (μ$) | started | finished |
|---|---|---|---|---|---|
| `b64f8ba3-3ba8-46e5-8487-2dff301ee410` | terminated (root_proved) | 2 | — | 2026-07-11T06:16:45 | 2026-07-11T06:18:15 |

## Proof tree

- ✅ **root_theorem** : `∀ (K Γ : Type) [Field K] [CharP K 2]
    [AddCommGroup Γ] [Module K Γ]
    (χ : Module.Dual K Γ → K) (x y : Γ)
    (a b : Module.Dual K Γ),
  (∀ c : K, c = 0 ∨ c = 1) →
  χ 0 = 0 →
  (∀ η : Module.Dual K Γ, η ≠ 0 → χ η = 1) →
  (∀ p q : Module.Dual K Γ,
    p ≠ 0 → q ≠ 0 →
    p x = 0 → p y = 0 → q x = 0 → q y = 0 → p = q) →
  a x = 0 → b y = 0 → (a + b) (x + y) = 0 →
  b x = χ a + χ b + χ (a + b)`

## The proof, assembled

```lean
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic

theorem root_theorem : ∀ (K Γ : Type) [Field K] [CharP K 2]
    [AddCommGroup Γ] [Module K Γ]
    (χ : Module.Dual K Γ → K) (x y : Γ)
    (a b : Module.Dual K Γ),
  (∀ c : K, c = 0 ∨ c = 1) →
  χ 0 = 0 →
  (∀ η : Module.Dual K Γ, η ≠ 0 → χ η = 1) →
  (∀ p q : Module.Dual K Γ,
    p ≠ 0 → q ≠ 0 →
    p x = 0 → p y = 0 → q x = 0 → q y = 0 → p = q) →
  a x = 0 → b y = 0 → (a + b) (x + y) = 0 →
  b x = χ a + χ b + χ (a + b) := by
intro K Γ _ _ _ _ χ x y a b htwo hχ0 hχ1 huniq hax hby habxy
have h11 : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
have hrel : a y = b x := by
  have h := habxy
  simp [hax, hby] at h
  exact CharTwo.add_eq_zero.mp h
by_cases ha : a = 0
· subst a
  have hbx : b x = 0 := by simpa using hrel.symm
  by_cases hb : b = 0
  · subst b
    simp [hχ0]
  · have hχb := hχ1 b hb
    simp [hbx, hχ0, hχb, h11]
by_cases hb : b = 0
· subst b
  have hχa := hχ1 a ha
  simp [hχ0, hχa, h11]
by_cases hab0 : a + b = 0
· have heq : a = b := by
    ext z
    apply CharTwo.add_eq_zero.mp
    exact LinearMap.congr_fun hab0 z
  have hbx : b x = 0 := by
    rw [← heq]
    exact hax
  have hχa := hχ1 a ha
  have hχb := hχ1 b hb
  simp [hbx, hab0, hχ0, hχa, hχb, h11]
by_cases hbx : b x = 0
· have hay : a y = 0 := hrel.trans hbx
  have heq : a = b := huniq a b ha hb hax hay hbx hby
  exfalso
  apply hab0
  ext z
  apply CharTwo.add_eq_zero.mpr
  exact LinearMap.congr_fun heq z
· rcases htwo (b x) with hz | hone
  · exact False.elim (hbx hz)
  · have hχa := hχ1 a ha
    have hχb := hχ1 b hb
    have hχab := hχ1 (a + b) hab0
    simp [hone, hχa, hχb, hχab, h11]

```

## How it went — every attempt, in order

| # | obligation | action | detail | verdict |
|---|---|---|---|---|
| 2 | `root_theorem` | solve | `intro K Γ _ _ _ χ x y a b htwo hχ0 hχ1 huniq hax hby habxy ; have h11 : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1 ; have hrel : a y = b x := by ;   have h := habxy ;   simp [hax, hby] at h ;   exact CharTwo.add_eq_zero.mp h ; by_cases ha : a = 0 ; · subst a ;   have hbx : b x = 0 := by simpa using hrel.symm ;   by_cases hb : b = 0 ;   · subst b ;     simp [hχ0] ;   · have hχb := hχ1 b hb ;     simp [hbx, hχ0, hχb, h11] ; by_cases hb : b = 0 ; · subst b ;   have hχa := hχ1 a ha ;   simp [hχ0, hχa, h11] ; by_cases hab0 : a + b = 0 ; · have heq : a = b := by ;     ext z ;     apply CharTwo.add_eq_zero.mp ;     exact LinearMap.congr_fun hab0 z ;   have hbx : b x = 0 := by ;     rw [← heq] ;     exact hax ;   have hχa := hχ1 a ha ;   have hχb := hχ1 b hb ;   simp [hbx, hab0, hχ0, hχa, hχb, h11] ; by_cases hbx : b x = 0 ; · have hay : a y = 0 := hrel.trans hbx ;   have heq : a = b := huniq a b ha hb hax hay hbx hby ;   exfalso ;   apply hab0 ;   ext z ;   apply CharTwo.add_eq_zero.mpr ;   exact LinearMap.congr_fun heq z ; · rcases htwo (b x) with hz \| hone ;   · exact False.elim (hbx hz) ;   · have hχa := hχ1 a ha ;     have hχb := hχ1 b hb ;     have hχab := hχ1 (a + b) hab0 ;     simp [hone, hχa, hχb, hχab, h11]` | ❌ kernel_fail |
| 3 | `root_theorem` | solve | `intro K Γ _ _ _ _ χ x y a b htwo hχ0 hχ1 huniq hax hby habxy ; have h11 : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1 ; have hrel : a y = b x := by ;   have h := habxy ;   simp [hax, hby] at h ;   exact CharTwo.add_eq_zero.mp h ; by_cases ha : a = 0 ; · subst a ;   have hbx : b x = 0 := by simpa using hrel.symm ;   by_cases hb : b = 0 ;   · subst b ;     simp [hχ0] ;   · have hχb := hχ1 b hb ;     simp [hbx, hχ0, hχb, h11] ; by_cases hb : b = 0 ; · subst b ;   have hχa := hχ1 a ha ;   simp [hχ0, hχa, h11] ; by_cases hab0 : a + b = 0 ; · have heq : a = b := by ;     ext z ;     apply CharTwo.add_eq_zero.mp ;     exact LinearMap.congr_fun hab0 z ;   have hbx : b x = 0 := by ;     rw [← heq] ;     exact hax ;   have hχa := hχ1 a ha ;   have hχb := hχ1 b hb ;   simp [hbx, hab0, hχ0, hχa, hχb, h11] ; by_cases hbx : b x = 0 ; · have hay : a y = 0 := hrel.trans hbx ;   have heq : a = b := huniq a b ha hb hax hay hbx hby ;   exfalso ;   apply hab0 ;   ext z ;   apply CharTwo.add_eq_zero.mpr ;   exact LinearMap.congr_fun heq z ; · rcases htwo (b x) with hz \| hone ;   · exact False.elim (hbx hz) ;   · have hχa := hχ1 a ha ;     have hχb := hχ1 b hb ;     have hχab := hχ1 (a + b) hab0 ;     simp [hone, hχa, hχb, hχab, h11]` | ✅ kernel_pass |

## Verification context

- **Environment hash:** `9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d`
- **Import manifest hash:** `4e6153919d29728249f2f05ad1f19b6350b7059ce3685cbb7042def53e6c1879`
- **Import manifest:** `["Mathlib.Tactic.Ring","Mathlib.Tactic.NormNum","Mathlib.LinearAlgebra.Dual.Defs","Mathlib.Algebra.CharP.Two","Mathlib.Tactic"]`
- **proof_body_redacted:** false

## Integrity

4 hash-chained trajectory events, `ac27ba5bd94c…` → `89e66e78382d…` (GENESIS-anchored). Re-verify anytime with `episode_replay`.
