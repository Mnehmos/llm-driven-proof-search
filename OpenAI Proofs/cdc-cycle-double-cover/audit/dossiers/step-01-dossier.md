# ⚠️ KERNEL-VERIFIED FORMAL STATEMENT — FIDELITY NOT YET VERIFIED — Paper p.2, equations (2)–(3): for nonzero distinct x,y in Γ = F₂³, put z=x+y. The three local two-element sets {t,t+x}, {t+x,t+z}, and {t,t+z} contain every s∈Γ either zero or exactly twice.

> This proof establishes:
>
> `∀ (x y t s : Fin 3 → ZMod 2),
  x ≠ 0 → y ≠ 0 → x ≠ y →
  let z := x + y
  let count : ℕ :=
    (if s = t ∨ s = t + x then 1 else 0) +
    (if s = t + x ∨ s = t + z then 1 else 0) +
    (if s = t ∨ s = t + z then 1 else 0)
  count = 0 ∨ count = 2`
>
> It does **not yet** certify the source claim above.

**Root goal (formal):** `∀ (x y t s : Fin 3 → ZMod 2),
  x ≠ 0 → y ≠ 0 → x ≠ y →
  let z := x + y
  let count : ℕ :=
    (if s = t ∨ s = t + x then 1 else 0) +
    (if s = t + x ∨ s = t + z then 1 else 0) +
    (if s = t ∨ s = t + z then 1 else 0)
  count = 0 ∨ count = 2`

| Proof soundness | Statement fidelity | Canonical promotion | Training eligibility |
|---|---|---|---|
| VERIFIED | ATTESTED (unsafe_dev_attestation — not reviewed) | BLOCKED | QUARANTINED |

| episode | state | steps | budget left (μ$) | started | finished |
|---|---|---|---|---|---|
| `90be1f6b-3408-4362-9711-17380cd615fb` | terminated (root_proved) | 3 | — | 2026-07-11T04:15:09 | 2026-07-11T04:16:31 |

## Proof tree

- ✅ **root_theorem** : `∀ (x y t s : Fin 3 → ZMod 2),
  x ≠ 0 → y ≠ 0 → x ≠ y →
  let z := x + y
  let count : ℕ :=
    (if s = t ∨ s = t + x then 1 else 0) +
    (if s = t + x ∨ s = t + z then 1 else 0) +
    (if s = t ∨ s = t + z then 1 else 0)
  count = 0 ∨ count = 2`

## The proof, assembled

```lean
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.CharP.Two

theorem root_theorem : ∀ (x y t s : Fin 3 → ZMod 2),
  x ≠ 0 → y ≠ 0 → x ≠ y →
  let z := x + y
  let count : ℕ :=
    (if s = t ∨ s = t + x then 1 else 0) +
    (if s = t + x ∨ s = t + z then 1 else 0) +
    (if s = t ∨ s = t + z then 1 else 0)
  count = 0 ∨ count = 2 := by
intro x y t s hx hy hxy
dsimp
have hz : x + y ≠ 0 := by
  intro h
  apply hxy
  funext i
  apply CharTwo.add_eq_zero.mp
  exact congrFun h i
by_cases h0 : s = t <;>
  by_cases h1 : s = t + x <;>
  by_cases h2 : s = t + (x + y) <;>
  simp_all

```

## How it went — every attempt, in order

| # | obligation | action | detail | verdict |
|---|---|---|---|---|
| 2 | `root_theorem` | solve | `intro x y t s hx hy hxy ; dsimp ; by_cases h0 : s = t <;> ;   by_cases h1 : s = t + x <;> ;   by_cases h2 : s = t + (x + y) <;> ;   simp_all` | ❌ kernel_fail |
| 3 | `root_theorem` | solve | `intro x y t s hx hy hxy ; dsimp ; have hz : x + y ≠ 0 := by ;   intro h ;   exact hxy (CharTwo.add_eq_zero.mp h) ; by_cases h0 : s = t <;> ;   by_cases h1 : s = t + x <;> ;   by_cases h2 : s = t + (x + y) <;> ;   simp_all` | ❌ kernel_fail |
| 4 | `root_theorem` | solve | `intro x y t s hx hy hxy ; dsimp ; have hz : x + y ≠ 0 := by ;   intro h ;   apply hxy ;   funext i ;   apply CharTwo.add_eq_zero.mp ;   exact congrFun h i ; by_cases h0 : s = t <;> ;   by_cases h1 : s = t + x <;> ;   by_cases h2 : s = t + (x + y) <;> ;   simp_all` | ✅ kernel_pass |

## Verification context

- **Environment hash:** `9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d`
- **Import manifest hash:** `7e0da7e69fcb50f7b45d3b077bb506d1735f263622809204fa654bad3ef8bed9`
- **Import manifest:** `["Mathlib.Tactic.Ring","Mathlib.Tactic.NormNum","Mathlib.Data.ZMod.Basic","Mathlib.Algebra.CharP.Two"]`
- **proof_body_redacted:** false

## Integrity

5 hash-chained trajectory events, `2b356a0b63a9…` → `dfb089a57404…` (GENESIS-anchored). Re-verify anytime with `episode_replay`.
