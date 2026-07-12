/-
CDC step 02 — Local dual identity, dot-product form (paper eqs. (7)–(9);
                mirrors CDCLean.local_dual_identity, with the annihilator-
                uniqueness hypothesis discharged later by step 05)
Problem version : 3d5b9cb6-b3a3-4358-95aa-b2e52bb2032b
Episode         : 23b209f0-a31f-40be-8ec4-429ebbfa56d9
Outcome         : kernel_verified (2026-07-11)
⚠ TRUST NOTE    : this early artifact uses `native_decide` (ofReduceBool),
                  extending trust beyond the Lean kernel. The final chain
                  (steps 06→07→08) does NOT depend on this file — the same
                  content is re-derived there with plain kernel `decide`.
Exported via    : proof_export (format = lean), LLM-Driven Proof Search Environment
-/
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
