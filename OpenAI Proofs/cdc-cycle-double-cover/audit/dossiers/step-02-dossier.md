# ⚠️ KERNEL-VERIFIED FORMAL STATEMENT — FIDELITY NOT YET VERIFIED — Paper equations (7)–(9), with its one-dimensional-annihilator step exposed as an explicit hypothesis: any two nonzero dual-coordinate vectors annihilating both independent vectors x,y are equal. Under that fact, λ=ηb(x) is the parity of the nonzero ηa,ηb,ηc.

> This proof establishes:
>
> `∀ (x y a b : Fin 3 → ZMod 2),
  x ≠ 0 → y ≠ 0 → x ≠ y →
  (∀ p q : Fin 3 → ZMod 2,
    p ≠ 0 → q ≠ 0 →
    dotProduct p x = 0 → dotProduct p y = 0 →
    dotProduct q x = 0 → dotProduct q y = 0 → p = q) →
  dotProduct a x = 0 →
  dotProduct b y = 0 →
  dotProduct (a + b) (x + y) = 0 →
  dotProduct b x =
    (if a = 0 then 0 else 1) +
    (if b = 0 then 0 else 1) +
    (if a + b = 0 then 0 else 1)`
>
> It does **not yet** certify the source claim above.

**Root goal (formal):** `∀ (x y a b : Fin 3 → ZMod 2),
  x ≠ 0 → y ≠ 0 → x ≠ y →
  (∀ p q : Fin 3 → ZMod 2,
    p ≠ 0 → q ≠ 0 →
    dotProduct p x = 0 → dotProduct p y = 0 →
    dotProduct q x = 0 → dotProduct q y = 0 → p = q) →
  dotProduct a x = 0 →
  dotProduct b y = 0 →
  dotProduct (a + b) (x + y) = 0 →
  dotProduct b x =
    (if a = 0 then 0 else 1) +
    (if b = 0 then 0 else 1) +
    (if a + b = 0 then 0 else 1)`

| Proof soundness | Statement fidelity | Canonical promotion | Training eligibility |
|---|---|---|---|
| VERIFIED | ATTESTED (unsafe_dev_attestation — not reviewed) | BLOCKED | QUARANTINED |

| episode | state | steps | budget left (μ$) | started | finished |
|---|---|---|---|---|---|
| `23b209f0-a31f-40be-8ec4-429ebbfa56d9` | terminated (root_proved) | 4 | — | 2026-07-11T05:37:20 | 2026-07-11T05:40:05 |

## Proof tree

- ✅ **root_theorem** : `∀ (x y a b : Fin 3 → ZMod 2),
  x ≠ 0 → y ≠ 0 → x ≠ y →
  (∀ p q : Fin 3 → ZMod 2,
    p ≠ 0 → q ≠ 0 →
    dotProduct p x = 0 → dotProduct p y = 0 →
    dotProduct q x = 0 → dotProduct q y = 0 → p = q) →
  dotProduct a x = 0 →
  dotProduct b y = 0 →
  dotProduct (a + b) (x + y) = 0 →
  dotProduct b x =
    (if a = 0 then 0 else 1) +
    (if b = 0 then 0 else 1) +
    (if a + b = 0 then 0 else 1)`

## The proof, assembled

```lean
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.CharP.Two
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.FinCases

theorem root_theorem : ∀ (x y a b : Fin 3 → ZMod 2),
  x ≠ 0 → y ≠ 0 → x ≠ y →
  (∀ p q : Fin 3 → ZMod 2,
    p ≠ 0 → q ≠ 0 →
    dotProduct p x = 0 → dotProduct p y = 0 →
    dotProduct q x = 0 → dotProduct q y = 0 → p = q) →
  dotProduct a x = 0 →
  dotProduct b y = 0 →
  dotProduct (a + b) (x + y) = 0 →
  dotProduct b x =
    (if a = 0 then 0 else 1) +
    (if b = 0 then 0 else 1) +
    (if a + b = 0 then 0 else 1) := by
intro x y a b hx hy hxy huniq hax hby hc
have h11 : (1 : ZMod 2) + 1 = 0 := by native_decide
have hrel : dotProduct a y = dotProduct b x := by
  rw [add_dotProduct, dotProduct_add, dotProduct_add] at hc
  simp [hax, hby] at hc
  exact CharTwo.add_eq_zero.mp hc
by_cases ha : a = 0
· subst a
  have hbx0 : dotProduct b x = 0 := by
    simpa only [zero_dotProduct] using hrel.symm
  by_cases hb0 : b = 0
  · simpa [hb0, hbx0] using h11.symm
  · simpa [hb0, hbx0] using h11.symm
by_cases hb : b = 0
· subst b
  simpa [ha] using h11.symm
by_cases hab0 : a + b = 0
· have hab : a = b := by
    funext i
    apply CharTwo.add_eq_zero.mp
    exact congrFun hab0 i
  rw [hab] at hax
  simpa [ha, hb, hab0, hax] using h11.symm
by_cases hbx : dotProduct b x = 0
· have hay : dotProduct a y = 0 := hrel.trans hbx
  have hab : a = b := huniq a b ha hb hax hay hbx hby
  apply False.elim
  apply hab0
  funext i
  apply CharTwo.add_eq_zero.mpr
  exact congrFun hab i
· have hvfin : (ZMod.finEquiv 2).symm (dotProduct b x) ≠ 0 := by
    intro hv
    apply hbx
    have hz := congrArg (ZMod.finEquiv 2) hv
    simpa using hz
  have hvone := Fin.eq_one_of_ne_zero _ hvfin
  have hbone : dotProduct b x = 1 := by
    have hz := congrArg (ZMod.finEquiv 2) hvone
    simpa using hz
  simpa [ha, hb, hab0, hbone] using h11

```

## How it went — every attempt, in order

| # | obligation | action | detail | verdict |
|---|---|---|---|---|
| 2 | `root_theorem` | solve | `intro x y a b hx hy hxy huniq hax hby hc ; have hrel : dotProduct a y = dotProduct b x := by ;   rw [add_dotProduct, dotProduct_add, dotProduct_add] at hc ;   simp [hax, hby] at hc ;   exact CharTwo.add_eq_zero.mp hc ; by_cases ha : a = 0 ; · subst a ;   simp at hrel ;   simp [hrel, CharTwo.add_self_eq_zero] ; by_cases hb : b = 0 ; · subst b ;   simp [CharTwo.add_self_eq_zero] ; by_cases hab0 : a + b = 0 ; · have hab : a = b := by ;     funext i ;     apply CharTwo.add_eq_zero.mp ;     exact congrFun hab0 i ;   subst a ;   simp at hax ;   simp [hax, hab0, CharTwo.add_self_eq_zero] ; by_cases hbx : dotProduct b x = 0 ; · have hay : dotProduct a y = 0 := hrel.trans hbx ;   have hab : a = b := huniq a b ha hb hax hay hbx hby ;   apply False.elim ;   apply hab0 ;   funext i ;   apply CharTwo.add_eq_zero.mpr ;   exact congrFun hab i ; · fin_cases hval : dotProduct b x <;> simp_all` | ❌ kernel_fail |
| 3 | `root_theorem` | solve | `intro x y a b hx hy hxy huniq hax hby hc ; have hrel : dotProduct a y = dotProduct b x := by ;   rw [add_dotProduct, dotProduct_add, dotProduct_add] at hc ;   simp [hax, hby] at hc ;   exact CharTwo.add_eq_zero.mp hc ; by_cases ha : a = 0 ; · subst a ;   have hbx0 : dotProduct b x = 0 := hrel.symm ;   by_cases hb0 : b = 0 <;> simp [hb0, hbx0] <;> norm_num ; by_cases hb : b = 0 ; · subst b ;   simp [ha] ;   norm_num ; by_cases hab0 : a + b = 0 ; · have hab : a = b := by ;     funext i ;     apply CharTwo.add_eq_zero.mp ;     exact congrFun hab0 i ;   rw [hab] at hax ;   simp [ha, hb, hab0, hax] ;   norm_num ; by_cases hbx : dotProduct b x = 0 ; · have hay : dotProduct a y = 0 := hrel.trans hbx ;   have hab : a = b := huniq a b ha hb hax hay hbx hby ;   apply False.elim ;   apply hab0 ;   funext i ;   apply CharTwo.add_eq_zero.mpr ;   exact congrFun hab i ; · have hvfin : (ZMod.finEquiv 2).symm (dotProduct b x) ≠ 0 := by ;     intro hv ;     apply hbx ;     have hz := congrArg (ZMod.finEquiv 2) hv ;     simpa using hz ;   have hvone := Fin.eq_one_of_ne_zero _ hvfin ;   have hbone : dotProduct b x = 1 := by ;     have hz := congrArg (ZMod.finEquiv 2) hvone ;     simpa using hz ;   simp [ha, hb, hab0, hbone] ;   norm_num` | ❌ kernel_fail |
| 4 | `root_theorem` | solve | `intro x y a b hx hy hxy huniq hax hby hc ; have htwo : (2 : ZMod 2) = 0 := by native_decide ; have hrel : dotProduct a y = dotProduct b x := by ;   rw [add_dotProduct, dotProduct_add, dotProduct_add] at hc ;   simp [hax, hby] at hc ;   exact CharTwo.add_eq_zero.mp hc ; by_cases ha : a = 0 ; · subst a ;   have hbx0 : dotProduct b x = 0 := by ;     simpa only [zero_dotProduct] using hrel.symm ;   by_cases hb0 : b = 0 ;   · simpa [hb0, hbx0] using htwo.symm ;   · simpa [hb0, hbx0] using htwo.symm ; by_cases hb : b = 0 ; · subst b ;   simpa [ha] using htwo.symm ; by_cases hab0 : a + b = 0 ; · have hab : a = b := by ;     funext i ;     apply CharTwo.add_eq_zero.mp ;     exact congrFun hab0 i ;   rw [hab] at hax ;   simpa [ha, hb, hab0, hax] using htwo.symm ; by_cases hbx : dotProduct b x = 0 ; · have hay : dotProduct a y = 0 := hrel.trans hbx ;   have hab : a = b := huniq a b ha hb hax hay hbx hby ;   apply False.elim ;   apply hab0 ;   funext i ;   apply CharTwo.add_eq_zero.mpr ;   exact congrFun hab i ; · have hvfin : (ZMod.finEquiv 2).symm (dotProduct b x) ≠ 0 := by ;     intro hv ;     apply hbx ;     have hz := congrArg (ZMod.finEquiv 2) hv ;     simpa using hz ;   have hvone := Fin.eq_one_of_ne_zero _ hvfin ;   have hbone : dotProduct b x = 1 := by ;     have hz := congrArg (ZMod.finEquiv 2) hvone ;     simpa using hz ;   simpa [ha, hb, hab0, hbone] using htwo` | ❌ kernel_fail |
| 5 | `root_theorem` | solve | `intro x y a b hx hy hxy huniq hax hby hc ; have h11 : (1 : ZMod 2) + 1 = 0 := by native_decide ; have hrel : dotProduct a y = dotProduct b x := by ;   rw [add_dotProduct, dotProduct_add, dotProduct_add] at hc ;   simp [hax, hby] at hc ;   exact CharTwo.add_eq_zero.mp hc ; by_cases ha : a = 0 ; · subst a ;   have hbx0 : dotProduct b x = 0 := by ;     simpa only [zero_dotProduct] using hrel.symm ;   by_cases hb0 : b = 0 ;   · simpa [hb0, hbx0] using h11.symm ;   · simpa [hb0, hbx0] using h11.symm ; by_cases hb : b = 0 ; · subst b ;   simpa [ha] using h11.symm ; by_cases hab0 : a + b = 0 ; · have hab : a = b := by ;     funext i ;     apply CharTwo.add_eq_zero.mp ;     exact congrFun hab0 i ;   rw [hab] at hax ;   simpa [ha, hb, hab0, hax] using h11.symm ; by_cases hbx : dotProduct b x = 0 ; · have hay : dotProduct a y = 0 := hrel.trans hbx ;   have hab : a = b := huniq a b ha hb hax hay hbx hby ;   apply False.elim ;   apply hab0 ;   funext i ;   apply CharTwo.add_eq_zero.mpr ;   exact congrFun hab i ; · have hvfin : (ZMod.finEquiv 2).symm (dotProduct b x) ≠ 0 := by ;     intro hv ;     apply hbx ;     have hz := congrArg (ZMod.finEquiv 2) hv ;     simpa using hz ;   have hvone := Fin.eq_one_of_ne_zero _ hvfin ;   have hbone : dotProduct b x = 1 := by ;     have hz := congrArg (ZMod.finEquiv 2) hvone ;     simpa using hz ;   simpa [ha, hb, hab0, hbone] using h11` | ✅ kernel_pass |

## Verification context

- **Environment hash:** `9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d`
- **Import manifest hash:** `9627630418df2d0499ebfb72d6e7e1cd337a353d8bcf4bd5f571d1e3b12d07d7`
- **Import manifest:** `["Mathlib.Tactic.Ring","Mathlib.Tactic.NormNum","Mathlib.Data.ZMod.Basic","Mathlib.Algebra.CharP.Two","Mathlib.Data.Matrix.Mul","Mathlib.Tactic.FinCases"]`
- **proof_body_redacted:** false

## Integrity

6 hash-chained trajectory events, `3ca6f20f17c1…` → `156f1ae08bc7…` (GENESIS-anchored). Re-verify anytime with `episode_replay`.
