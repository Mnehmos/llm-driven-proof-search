-- proof_body_redacted: false
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
noncomputable section

namespace ProofSearch.P_97d0b02d054e4530

def P1Board : Type :=
  {B : Multiset ℕ // B.card = 2026 ∧ ∀ x ∈ B, 0 < x}

def P1Move : P1Board → P1Board → Prop :=
  fun B B' => ∃ (R : Multiset ℕ) (m n : ℕ), 1 < m ∧ 1 < n ∧ B.1 = m ::ₘ n ::ₘ R ∧ B'.1 = Nat.gcd m n ::ₘ (Nat.lcm m n / Nat.gcd m n) ::ₘ R

def P1Terminal : P1Board → Prop :=
  fun B => ¬ ∃ B', P1Move B B'

def P1Inv : P1Board → ℕ → ℕ :=
  fun B p => (B.1.map fun x => x.factorization p).gcd

theorem root_theorem : let Board := {B : Multiset ℕ // B.card = 2026 ∧ ∀ x ∈ B, 0 < x}
let Move : Board → Board → Prop := fun B B' =>
  ∃ (R : Multiset ℕ) (m n : ℕ),
    1 < m ∧ 1 < n ∧
    B.1 = m ::ₘ n ::ₘ R ∧
    B'.1 = Nat.gcd m n ::ₘ (Nat.lcm m n / Nat.gcd m n) ::ₘ R
let Terminal : Board → Prop := fun B => ¬ ∃ B', Move B B'
∀ B₀ : Board, (∀ x ∈ B₀.1, 1 < x) →
  WellFounded (fun B' B => Move B B') ∧
  ∃ M : ℕ, 1 < M ∧
    (∃ Bₜ : Board, Relation.ReflTransGen Move B₀ Bₜ ∧ Terminal Bₜ) ∧
    ∀ Bₜ : Board, Relation.ReflTransGen Move B₀ Bₜ → Terminal Bₜ →
      Bₜ.1.filter (fun x => 1 < x) = {M} := by
  have p1_move_wf : WellFounded (fun B' B : P1Board => P1Move B B') := by
    let stat : Multiset ℕ → ℕ := fun S => S.prod * 2027 + (S.filter (fun x => 1 < x)).card
    let μ : P1Board → ℕ := fun B => stat B.1
    have hwf : WellFounded (fun A B : P1Board => μ A < μ B) := WellFounded.onFun Nat.lt_wfRel.wf
    apply hwf.mono
    intro B' B hmove
    rcases hmove with ⟨R, m, n, hm, hn, hB, hB'⟩
    have hR : 0 < R.prod := by
      apply Multiset.prod_pos
      intro x hx
      exact B.property.2 x (by rw [hB]; simp [hx])
    have hlocal :
        (Nat.gcd m n ::ₘ (Nat.lcm m n / Nat.gcd m n) ::ₘ R).prod < (m ::ₘ n ::ₘ R).prod ∨
        ((Nat.gcd m n ::ₘ (Nat.lcm m n / Nat.gcd m n) ::ₘ R).prod = (m ::ₘ n ::ₘ R).prod ∧
         ((Nat.gcd m n ::ₘ (Nat.lcm m n / Nat.gcd m n) ::ₘ R).filter (fun x => 1 < x)).card <
         ((m ::ₘ n ::ₘ R).filter (fun x => 1 < x)).card) := by
      have hd : Nat.gcd m n ∣ Nat.lcm m n := (Nat.gcd_dvd_left m n).trans (Nat.dvd_lcm_left m n)
      have hpair : Nat.gcd m n * (Nat.lcm m n / Nat.gcd m n) = Nat.lcm m n := Nat.mul_div_cancel' hd
      by_cases hg : Nat.gcd m n = 1
      · right
        have hlcm : Nat.lcm m n = m * n := by simpa [hg] using Nat.gcd_mul_lcm m n
        have hmn : 1 < m * n := by nlinarith
        have hlcmgt : 1 < Nat.lcm m n := by omega
        constructor
        · simp only [Multiset.prod_cons]
          rw [← Nat.mul_assoc, hpair, hlcm, ← Nat.mul_assoc]
        · simp [Multiset.filter_cons, hg, hlcmgt, hm, hn, hlcm, hmn]
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
    have hcard : (m ::ₘ n ::ₘ R).card = 2026 := by rw [← hB]; exact B.property.1
    have hcard' : (Nat.gcd m n ::ₘ (Nat.lcm m n / Nat.gcd m n) ::ₘ R).card = 2026 := by rw [← hB']; exact B'.property.1
    have hk : ((m ::ₘ n ::ₘ R).filter (fun x => 1 < x)).card ≤ 2026 := by
      calc
        _ ≤ (m ::ₘ n ::ₘ R).card := Multiset.card_le_card (Multiset.filter_le (fun x : ℕ => 1 < x) _)
        _ = 2026 := hcard
    have hk' : ((Nat.gcd m n ::ₘ (Nat.lcm m n / Nat.gcd m n) ::ₘ R).filter (fun x => 1 < x)).card ≤ 2026 := by
      calc
        _ ≤ (Nat.gcd m n ::ₘ (Nat.lcm m n / Nat.gcd m n) ::ₘ R).card := Multiset.card_le_card (Multiset.filter_le (fun x : ℕ => 1 < x) _)
        _ = 2026 := hcard'
    have hmeasure : stat (Nat.gcd m n ::ₘ (Nat.lcm m n / Nat.gcd m n) ::ₘ R) < stat (m ::ₘ n ::ₘ R) := by
      dsimp [stat]
      rcases hlocal with hp | ⟨hp, hc⟩ <;> omega
    change μ B' < μ B
    calc
      μ B' = stat (Nat.gcd m n ::ₘ (Nat.lcm m n / Nat.gcd m n) ::ₘ R) := congrArg stat hB'
      _ < stat (m ::ₘ n ::ₘ R) := hmeasure
      _ = μ B := (congrArg stat hB).symm
  have p1_reachable_terminal : ∀ B : P1Board, ∃ T : P1Board, Relation.ReflTransGen P1Move B T ∧ P1Terminal T := by
    intro B
    induction B using p1_move_wf.induction with
    | h B ih =>
        by_cases ht : P1Terminal B
        · exact ⟨B, .refl, ht⟩
        · have hs : ∃ C, P1Move B C := by simpa [P1Terminal] using ht
          rcases hs with ⟨C, hBC⟩
          rcases ih C hBC with ⟨T, hCT, hT⟩
          exact ⟨T, hCT.head hBC, hT⟩
  have p1_move_product_gt_one : ∀ {B B' : P1Board}, P1Move B B' → 1 < B'.1.prod := by
    intro B B' h
    rcases h with ⟨R, m, n, hm, hn, hB, hB'⟩
    have hR : 0 < R.prod := by
      apply Multiset.prod_pos
      intro x hx
      exact B.property.2 x (by rw [hB]; simp [hx])
    have hd : Nat.gcd m n ∣ Nat.lcm m n := (Nat.gcd_dvd_left m n).trans (Nat.dvd_lcm_left m n)
    have hpair : Nat.gcd m n * (Nat.lcm m n / Nat.gcd m n) = Nat.lcm m n := Nat.mul_div_cancel' hd
    have hlpos : 0 < Nat.lcm m n := Nat.lcm_pos (by omega) (by omega)
    have hmle : m ≤ Nat.lcm m n := Nat.le_of_dvd hlpos (Nat.dvd_lcm_left m n)
    have hl : 1 < Nat.lcm m n := lt_of_lt_of_le hm hmle
    rw [hB']
    simp only [Multiset.prod_cons]
    rw [← Nat.mul_assoc, hpair]
    nlinarith
  have p1_initial_product_gt_one : ∀ (B : P1Board), (∀ x ∈ B.1, 1 < x) → 1 < B.1.prod := by
    intro B h
    have hne : B.1 ≠ 0 := by
      intro hz
      have hc := B.property.1
      simp [hz] at hc
    rcases Multiset.exists_mem_of_ne_zero hne with ⟨x, hx⟩
    rcases Multiset.exists_cons_of_mem hx with ⟨R, hBR⟩
    have hR : 0 < R.prod := by
      apply Multiset.prod_pos
      intro y hy
      exact B.property.2 y (by rw [hBR]; simp [hy])
    rw [hBR]
    simp only [Multiset.prod_cons]
    nlinarith [h x hx]
  have p1_reachable_product_gt_one : ∀ {B T : P1Board}, (∀ x ∈ B.1, 1 < x) → Relation.ReflTransGen P1Move B T → 1 < T.1.prod := by
    intro B T hB hpath
    induction hpath with
    | refl => exact p1_initial_product_gt_one B hB
    | tail hpath hmove ih => exact p1_move_product_gt_one hmove
  have p1_terminal_no_pair : ∀ {B : P1Board}, P1Terminal B → ¬ ∃ (R : Multiset ℕ) (m n : ℕ), 1 < m ∧ 1 < n ∧ B.1 = m ::ₘ n ::ₘ R := by
    intro B hterm hp
    rcases hp with ⟨R, m, n, hm, hn, hB⟩
    have hRpos : ∀ x ∈ R, 0 < x := by
      intro x hx
      exact B.property.2 x (by rw [hB]; simp [hx])
    have hgpos : 0 < Nat.gcd m n := Nat.gcd_pos_of_pos_left n (by omega)
    have hlpos : 0 < Nat.lcm m n := Nat.lcm_pos (by omega) (by omega)
    have hd : Nat.gcd m n ∣ Nat.lcm m n := (Nat.gcd_dvd_left m n).trans (Nat.dvd_lcm_left m n)
    have hpair : Nat.gcd m n * (Nat.lcm m n / Nat.gcd m n) = Nat.lcm m n := Nat.mul_div_cancel' hd
    have hgle : Nat.gcd m n ≤ Nat.lcm m n := Nat.le_of_dvd hlpos hd
    have hqpos : 0 < Nat.lcm m n / Nat.gcd m n := Nat.div_pos hgle hgpos
    let B' : P1Board :=
      ⟨Nat.gcd m n ::ₘ (Nat.lcm m n / Nat.gcd m n) ::ₘ R, by
        constructor
        · have hc := B.property.1
          rw [hB] at hc
          simpa using hc
        · intro x hx
          simp only [Multiset.mem_cons] at hx
          rcases hx with rfl | rfl | hx
          · exact hgpos
          · exact hqpos
          · exact hRpos x hx⟩
    apply hterm
    exact ⟨B', R, m, n, hm, hn, hB, rfl⟩
  have p1_terminal_singleton : ∀ {B : P1Board}, 1 < B.1.prod → P1Terminal B → ∃ M : ℕ, 1 < M ∧ B.1.filter (fun x => 1 < x) = {M} := by
    intro B hprod hterm
    have hnopair := p1_terminal_no_pair hterm
    generalize hF : B.1.filter (fun x => 1 < x) = F
    induction F using Multiset.induction_on with
    | empty =>
        exfalso
        have hall : ∀ x ∈ B.1, x = 1 := by
          intro x hx
          have hxnot : ¬ 1 < x := by
            intro hxl
            have hmem : x ∈ B.1.filter (fun y => 1 < y) := Multiset.mem_filter.mpr ⟨hx, hxl⟩
            rw [hF] at hmem
            simp at hmem
          have hxpos := B.property.2 x hx
          omega
        have hpone := Multiset.prod_eq_one hall
        omega
    | @cons M S ih =>
        cases S using Multiset.induction_on with
        | empty =>
            have hmF : M ∈ B.1.filter (fun x => 1 < x) := by rw [hF]; simp
            exact ⟨M, (Multiset.mem_filter.mp hmF).2, by simpa using hF⟩
        | @cons N T ih =>
            exfalso
            have hmF : M ∈ B.1.filter (fun x => 1 < x) := by rw [hF]; simp
            have hm : 1 < M := (Multiset.mem_filter.mp hmF).2
            have hmB : M ∈ B.1 := (Multiset.mem_filter.mp hmF).1
            rcases Multiset.exists_cons_of_mem hmB with ⟨R₁, hBR₁⟩
            have hfilterR₁ : R₁.filter (fun x => 1 < x) = N ::ₘ T := by
              rw [hBR₁] at hF
              simp only [Multiset.filter_cons, if_pos hm] at hF
              exact (Multiset.cons_inj_right M).mp hF
            have hnF : N ∈ R₁.filter (fun x => 1 < x) := by rw [hfilterR₁]; simp
            have hn : 1 < N := (Multiset.mem_filter.mp hnF).2
            have hnR : N ∈ R₁ := (Multiset.mem_filter.mp hnF).1
            rcases Multiset.exists_cons_of_mem hnR with ⟨R, hR₁⟩
            apply hnopair
            exact ⟨R, M, N, hm, hn, hBR₁.trans (congrArg (fun S => M ::ₘ S) hR₁)⟩
  have p1_inv_move : ∀ {B B' : P1Board} {p : ℕ}, p.Prime → P1Move B B' → P1Inv B' p = P1Inv B p := by
    intro B B' p hp hmove
    rcases hmove with ⟨R, m, n, hm, hn, hB, hB'⟩
    have hm0 : m ≠ 0 := by omega
    have hn0 : n ≠ 0 := by omega
    have hd : Nat.gcd m n ∣ Nat.lcm m n := (Nat.gcd_dvd_left m n).trans (Nat.dvd_lcm_left m n)
    have hv₁ : (Nat.gcd m n).factorization p = min (m.factorization p) (n.factorization p) := by
      rw [Nat.factorization_gcd hm0 hn0]
      rfl
    have hv₂ : (Nat.lcm m n / Nat.gcd m n).factorization p =
        max (m.factorization p) (n.factorization p) - min (m.factorization p) (n.factorization p) := by
      rw [Nat.factorization_div hd, Nat.factorization_lcm hm0 hn0, Nat.factorization_gcd hm0 hn0]
      rfl
    unfold P1Inv
    rw [hB, hB']
    simp only [Multiset.map_cons, Multiset.gcd_cons, hv₁, hv₂]
    rw [← gcd_assoc, ← gcd_assoc]
    congr 1
    rcases le_total (m.factorization p) (n.factorization p) with h | h
    · simp only [min_eq_left h, max_eq_right h]
      exact Nat.gcd_sub_self_right h
    · simp only [min_eq_right h, max_eq_left h]
      change Nat.gcd (n.factorization p) (m.factorization p - n.factorization p) =
        Nat.gcd (m.factorization p) (n.factorization p)
      rw [Nat.gcd_sub_self_right h, Nat.gcd_comm]
  have p1_inv_path : ∀ {B T : P1Board} {p : ℕ}, p.Prime → Relation.ReflTransGen P1Move B T → P1Inv T p = P1Inv B p := by
    intro B T p hp hpath
    induction hpath with
    | refl => rfl
    | tail hpath hmove ih => exact (p1_inv_move hp hmove).trans ih
  have p1_inv_of_singleton : ∀ {B : P1Board} {M p : ℕ}, p.Prime → B.1.filter (fun x => 1 < x) = {M} → P1Inv B p = M.factorization p := by
    intro B M p hp hfilter
    have hmF : M ∈ B.1.filter (fun x => 1 < x) := by rw [hfilter]; simp
    have hmB : M ∈ B.1 := (Multiset.mem_filter.mp hmF).1
    have hmmap : M.factorization p ∈ B.1.map (fun x => x.factorization p) := Multiset.mem_map.mpr ⟨M, hmB, rfl⟩
    unfold P1Inv
    apply Nat.dvd_antisymm
    · exact Multiset.gcd_dvd hmmap
    · rw [Multiset.dvd_gcd]
      intro v hv
      rcases Multiset.mem_map.mp hv with ⟨x, hx, rfl⟩
      by_cases hxgt : 1 < x
      · have hxF : x ∈ B.1.filter (fun y => 1 < y) := Multiset.mem_filter.mpr ⟨hx, hxgt⟩
        rw [hfilter] at hxF
        have hxM : x = M := by simpa using hxF
        simp [hxM]
      · have hxpos := B.property.2 x hx
        have hx1 : x = 1 := by omega
        simp [hx1]
  have p1_survivors_equal : ∀ {B T₁ T₂ : P1Board} {M₁ M₂ : ℕ}, Relation.ReflTransGen P1Move B T₁ → Relation.ReflTransGen P1Move B T₂ → T₁.1.filter (fun x => 1 < x) = {M₁} → T₂.1.filter (fun x => 1 < x) = {M₂} → M₁ = M₂ := by
    intro B T₁ T₂ M₁ M₂ h₁ h₂ hs₁ hs₂
    have hm₁F : M₁ ∈ T₁.1.filter (fun x => 1 < x) := by rw [hs₁]; simp
    have hm₂F : M₂ ∈ T₂.1.filter (fun x => 1 < x) := by rw [hs₂]; simp
    have hm₁0 : M₁ ≠ 0 := by have := (Multiset.mem_filter.mp hm₁F).2; omega
    have hm₂0 : M₂ ≠ 0 := by have := (Multiset.mem_filter.mp hm₂F).2; omega
    apply Nat.factorization_inj hm₁0 hm₂0
    ext p
    by_cases hp : p.Prime
    · calc
        M₁.factorization p = P1Inv T₁ p := (p1_inv_of_singleton hp hs₁).symm
        _ = P1Inv B p := p1_inv_path hp h₁
        _ = P1Inv T₂ p := (p1_inv_path hp h₂).symm
        _ = M₂.factorization p := p1_inv_of_singleton hp hs₂
    · rw [Nat.factorization_eq_zero_of_not_prime M₁ hp,
          Nat.factorization_eq_zero_of_not_prime M₂ hp]
  dsimp
  intro B₀ hB₀
  constructor
  · exact p1_move_wf
  · rcases p1_reachable_terminal B₀ with ⟨T, hpath, hterm⟩
    have hprod : 1 < T.1.prod := p1_reachable_product_gt_one hB₀ hpath
    rcases p1_terminal_singleton hprod hterm with ⟨M, hM, hs⟩
    refine ⟨M, hM, ⟨T, hpath, hterm⟩, ?_⟩
    intro T' hpath' hterm'
    have hprod' : 1 < T'.1.prod := p1_reachable_product_gt_one hB₀ hpath'
    rcases p1_terminal_singleton hprod' hterm' with ⟨M', hM', hs'⟩
    have heq : M' = M := p1_survivors_equal hpath' hpath hs' hs
    simpa [heq] using hs'

end ProofSearch.P_97d0b02d054e4530
end



