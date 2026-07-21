-- proof_body_redacted: false
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib

theorem root_theorem : let Board := {B : Multiset ℕ // B.card = 2026}
let Move : Board → Board → Prop := fun B B' =>
  ∃ (R : Multiset ℕ) (m n : ℕ),
    0 < R.prod ∧ 1 < m ∧ 1 < n ∧
    B.1 = m ::ₘ n ::ₘ R ∧
    B'.1 = Nat.gcd m n ::ₘ (Nat.lcm m n / Nat.gcd m n) ::ₘ R
WellFounded (fun B' B => Move B B') := by
  dsimp
  let stat : Multiset ℕ → ℕ :=
    fun S => S.prod * 2027 + (S.filter (fun x => 1 < x)).card
  let μ : {B : Multiset ℕ // B.card = 2026} → ℕ := fun B => stat B.1
  have hwf : WellFounded (fun A B :
      {B : Multiset ℕ // B.card = 2026} => μ A < μ B) :=
    WellFounded.onFun Nat.lt_wfRel.wf
  apply hwf.mono
  intro B' B hmove
  rcases hmove with ⟨R, m, n, hR, hm, hn, hB, hB'⟩
  have hlocal :
      (Nat.gcd m n ::ₘ (Nat.lcm m n / Nat.gcd m n) ::ₘ R).prod <
          (m ::ₘ n ::ₘ R).prod ∨
        ((Nat.gcd m n ::ₘ (Nat.lcm m n / Nat.gcd m n) ::ₘ R).prod =
            (m ::ₘ n ::ₘ R).prod ∧
          ((Nat.gcd m n ::ₘ (Nat.lcm m n / Nat.gcd m n) ::ₘ R).filter
            (fun x => 1 < x)).card <
          ((m ::ₘ n ::ₘ R).filter (fun x => 1 < x)).card) := by
    have hd : Nat.gcd m n ∣ Nat.lcm m n :=
      (Nat.gcd_dvd_left m n).trans (Nat.dvd_lcm_left m n)
    have hpair :
        Nat.gcd m n * (Nat.lcm m n / Nat.gcd m n) = Nat.lcm m n :=
      Nat.mul_div_cancel' hd
    by_cases hg : Nat.gcd m n = 1
    · right
      have hlcm : Nat.lcm m n = m * n := by
        simpa [hg] using Nat.gcd_mul_lcm m n
      have hq : Nat.lcm m n / Nat.gcd m n = m * n := by
        simp [hg, hlcm]
      have hmn : 1 < m * n := by nlinarith
      have hlcmgt : 1 < Nat.lcm m n := by omega
      constructor
      · simp only [Multiset.prod_cons]
        rw [← Nat.mul_assoc, hpair, hlcm, ← Nat.mul_assoc]
      · simp [Multiset.filter_cons, hg, hlcmgt, hm, hn]
    · left
      have hgpos : 1 < Nat.gcd m n := by
        have : 0 < Nat.gcd m n := Nat.gcd_pos_of_pos_left n (by omega)
        omega
      have hlcmpos : 0 < Nat.lcm m n := Nat.lcm_pos (by omega) (by omega)
      have hlcm : Nat.lcm m n < m * n := by
        have hgl := Nat.gcd_mul_lcm m n
        nlinarith
      simp only [Multiset.prod_cons]
      rw [← Nat.mul_assoc, hpair, ← Nat.mul_assoc]
      exact Nat.mul_lt_mul_of_pos_right hlcm hR
  have hcard : (m ::ₘ n ::ₘ R).card = 2026 := by
    rw [← hB]
    exact B.property
  have hcard' :
      (Nat.gcd m n ::ₘ
        (Nat.lcm m n / Nat.gcd m n) ::ₘ R).card = 2026 := by
    rw [← hB']
    exact B'.property
  have hk :
      ((m ::ₘ n ::ₘ R).filter (fun x => 1 < x)).card ≤ 2026 := by
    calc
      ((m ::ₘ n ::ₘ R).filter (fun x => 1 < x)).card
          ≤ (m ::ₘ n ::ₘ R).card :=
        Multiset.card_le_card
          (Multiset.filter_le (fun x : ℕ => 1 < x) (m ::ₘ n ::ₘ R))
      _ = 2026 := hcard
  have hk' :
      ((Nat.gcd m n ::ₘ (Nat.lcm m n / Nat.gcd m n) ::ₘ R).filter
        (fun x => 1 < x)).card ≤ 2026 := by
    calc
      ((Nat.gcd m n ::ₘ (Nat.lcm m n / Nat.gcd m n) ::ₘ R).filter
        (fun x => 1 < x)).card
          ≤ (Nat.gcd m n ::ₘ
              (Nat.lcm m n / Nat.gcd m n) ::ₘ R).card :=
        Multiset.card_le_card
          (Multiset.filter_le (fun x : ℕ => 1 < x)
            (Nat.gcd m n ::ₘ
              (Nat.lcm m n / Nat.gcd m n) ::ₘ R))
      _ = 2026 := hcard'
  have hmeasure :
      stat (Nat.gcd m n ::ₘ
        (Nat.lcm m n / Nat.gcd m n) ::ₘ R) <
      stat (m ::ₘ n ::ₘ R) := by
    dsimp [stat]
    rcases hlocal with hp | ⟨hp, hc⟩
    · omega
    · omega
  change μ B' < μ B
  calc
    μ B' = stat (Nat.gcd m n ::ₘ
        (Nat.lcm m n / Nat.gcd m n) ::ₘ R) := by
      exact congrArg stat hB'
    _ < stat (m ::ₘ n ::ₘ R) := hmeasure
    _ = μ B := by
      exact (congrArg stat hB).symm

