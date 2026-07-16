import Mathlib

/-!
# Erdős #647 — exact arbitrary-block power-prefix equivalence

This module isolates the strongest purely formal block-production
statement currently available.  A positive shift `k` has a unique coordinate
pair

`k = block * q + s`, with `0 < s ≤ block`.

Consequently a divisor bound on the local form `block * M - s` turns the
global family of shift budgets into an *exactly equivalent* family of
class-sensitive power-prefix checks, one in every block.  The function `C`
is allowed to depend on the local rung `s`; for Erdős #647 one specializes
`block = 2520`, `exp = 3`, `A = 35`, and `C s` to the verified gcd-class
coefficient from `Erdos647_GcdClassCubeBound.lean`.

The final injectivity theorem is the honest novelty result obtained for free:
different block/rung cells produce different shifted integers.  It is
coordinate novelty only; it does not assert that their prime factors are new.

The core equivalence `erdos647_block_power_prefix_iff_shift_budgets` was
independently kernel-verified through the tracked proof-search pipeline on
2026-07-16:

* preverification job: `a8b1cd4a-8d75-40a4-972a-222a49d8b959`
* problem version: `a958f713-e614-4f6f-8cb1-7cee63ceac4f`
* episode: `bd495411-637a-4442-8618-25266c535a43`
* root statement hash:
  `95b265c2316da496bfd5d7e94c618e1dfb267838fbd38770badf6b24bfa9a33b`
* outcome: `kernel_verified`

The exact Formal-Conjectures-shaped candidate equivalence
`erdos647_candidate_iff_block_power_prefix` was also independently tracked:

* preverification job: `2aa4cb7f-c043-47db-b737-5fd3cf70b19b`
* problem version: `39ea138e-842a-4758-90fe-eb11135aa239`
* episode: `7f4f33c1-8a25-4b44-8db6-3c74bea6a18b`
* root statement hash:
  `74ccf2d0251e73cacff3308e74292d7958f0849bb78835abb771402d8fe4374d`
* outcome: `kernel_verified`
-/

/-- Every positive natural has unique positive-remainder block coordinates. -/
theorem erdos647_positive_block_coordinates_unique :
    ∀ block k : ℕ, 0 < block → 0 < k →
      ∃! qr : ℕ × ℕ,
        0 < qr.2 ∧ qr.2 ≤ block ∧ k = block * qr.1 + qr.2 := by
  intro block k hblock hk
  let q := (k - 1) / block
  let s := (k - 1) % block + 1
  have hslt : (k - 1) % block < block := Nat.mod_lt _ hblock
  have hdivmod := Nat.div_add_mod (k - 1) block
  have hkqs : k = block * q + s := by
    dsimp [q, s]
    omega
  refine ⟨(q, s), ?_, ?_⟩
  · exact ⟨by dsimp [s]; omega, by dsimp [s]; omega, hkqs⟩
  · rintro ⟨q', s'⟩ ⟨hs'0, hs'le, hkq's'⟩
    change 0 < s' at hs'0
    change s' ≤ block at hs'le
    change k = block * q' + s' at hkq's'
    have hqq' : q = q' := by
      rcases lt_trichotomy q q' with hlt | heq | hgt
      · have hmul : block * (q + 1) ≤ block * q' :=
          Nat.mul_le_mul_left block (by omega)
        have hk_le : k ≤ block * (q + 1) := by
          rw [hkqs]
          calc
            block * q + s ≤ block * q + block := Nat.add_le_add_left (by dsimp [s]; omega) _
            _ = block * (q + 1) := by ring
        have hk_lt : block * q' < k := by
          rw [hkq's']
          omega
        omega
      · exact heq
      · have hmul : block * (q' + 1) ≤ block * q :=
          Nat.mul_le_mul_left block (by omega)
        have hk_le : k ≤ block * (q' + 1) := by
          rw [hkq's']
          calc
            block * q' + s' ≤ block * q' + block := Nat.add_le_add_left hs'le _
            _ = block * (q' + 1) := by ring
        have hk_lt : block * q < k := by
          rw [hkqs]
          have hs0 : 0 < s := by dsimp [s]; omega
          omega
        omega
    have hss' : s = s' := by
      rw [hqq'] at hkqs
      omega
    cases hqq'
    cases hss'
    rfl

/--
The exact arbitrary-block production theorem.

The left side is the full family of excess-`B` shift budgets at height
`block * N`.  The right side asks only for cells lying in their local
power-prefix window.  The coefficient `C s` may vary with the local rung.
-/
theorem erdos647_block_power_prefix_iff_shift_budgets :
    ∀ (block exp A B N : ℕ) (C : ℕ → ℕ),
      0 < block →
      0 < exp →
      0 < A →
      1 ≤ N →
      (∀ M s : ℕ, 1 ≤ M → 0 < s → s < block * M →
        A * (ArithmeticFunction.sigma 0 (block * M - s)) ^ exp ≤
          C s * (block * M - s)) →
      ((∀ k : ℕ, 0 < k → k < block * N →
          ArithmeticFunction.sigma 0 (block * N - k) ≤ B + k) ↔
        ∀ q s : ℕ,
          q < N →
          0 < s →
          s ≤ block →
          s < block * (N - q) →
          A * (B + block * q + s) ^ exp <
              C s * (block * (N - q) - s) →
          ArithmeticFunction.sigma 0 (block * (N - q) - s) ≤
            B + block * q + s) := by
  intro block exp A B N C hblock hexp hA hdiv hlocal
  constructor
  · intro hbudget q s hqN hs0 hsle hslocal _
    have hNsplit : block * N = block * q + block * (N - q) := by
      rw [← Nat.mul_add]
      congr 1
      omega
    have hk0 : 0 < block * q + s := by omega
    have hkn : block * q + s < block * N := by omega
    have hvalue : block * N - (block * q + s) =
        block * (N - q) - s := by omega
    simpa [hvalue, add_assoc] using hbudget (block * q + s) hk0 hkn
  · intro hprefix k hk0 hkn
    let q := (k - 1) / block
    let s := (k - 1) % block + 1
    have hslt : (k - 1) % block < block := Nat.mod_lt _ hblock
    have hdivmod := Nat.div_add_mod (k - 1) block
    have hkqs : k = block * q + s := by
      dsimp [q, s]
      omega
    have hs0 : 0 < s := by dsimp [s]; omega
    have hsle : s ≤ block := by dsimp [s]; omega
    have hbq_lt : block * q < block * N := by omega
    have hqN : q < N := (Nat.mul_lt_mul_left hblock).mp hbq_lt
    have hMpos : 1 ≤ N - q := by omega
    have hNsplit : block * N = block * q + block * (N - q) := by
      rw [← Nat.mul_add]
      congr 1
      omega
    have hslocal : s < block * (N - q) := by omega
    have hvalue : block * N - k = block * (N - q) - s := by omega
    by_cases hpref :
        A * (B + block * q + s) ^ exp <
          C s * (block * (N - q) - s)
    · have hb := hprefix q s hqN hs0 hsle hslocal hpref
      rw [hvalue]
      simpa [hkqs, add_assoc] using hb
    · push Not at hpref
      have hb := hlocal (N - q) s hMpos hs0 hslocal
      have hmul :
          A * (ArithmeticFunction.sigma 0 (block * (N - q) - s)) ^ exp ≤
            A * (B + block * q + s) ^ exp := hb.trans hpref
      have hpows :
          (ArithmeticFunction.sigma 0 (block * (N - q) - s)) ^ exp ≤
            (B + block * q + s) ^ exp :=
        le_of_mul_le_mul_left hmul hA
      have hbudget : ArithmeticFunction.sigma 0 (block * (N - q) - s) ≤
          B + block * q + s :=
        (Nat.pow_le_pow_iff_left (Nat.ne_of_gt hexp)).mp hpows
      rw [hvalue]
      simpa [hkqs, add_assoc] using hbudget

/--
Exact Formal-Conjectures-shaped corollary at excess `B = 2`.

This turns a class-sensitive local power bound into an exact blockwise
certificate interface for the original candidate predicate.
-/
theorem erdos647_candidate_iff_block_power_prefix :
    ∀ (block exp A N : ℕ) (C : ℕ → ℕ),
      0 < block →
      0 < exp →
      0 < A →
      1 ≤ N →
      (∀ M s : ℕ, 1 ≤ M → 0 < s → s < block * M →
        A * (ArithmeticFunction.sigma 0 (block * M - s)) ^ exp ≤
          C s * (block * M - s)) →
      (((⨆ m : Fin (block * N),
          (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ block * N + 2) ↔
        ∀ q s : ℕ,
          q < N →
          0 < s →
          s ≤ block →
          s < block * (N - q) →
          A * (2 + block * q + s) ^ exp <
              C s * (block * (N - q) - s) →
          ArithmeticFunction.sigma 0 (block * (N - q) - s) ≤
            2 + block * q + s) := by
  intro block exp A N C hblock hexp hA hN hlocal
  rw [← erdos647_block_power_prefix_iff_shift_budgets
    block exp A 2 N C hblock hexp hA hN hlocal]
  constructor
  · intro H k hk0 hkn
    let f : Fin (block * N) → ℕ := fun x =>
      (x : ℕ) + ArithmeticFunction.sigma 0 x
    have hbdd : BddAbove (Set.range f) := by
      refine ⟨2 * (block * N), ?_⟩
      rintro y ⟨x, rfl⟩
      dsimp [f]
      rw [ArithmeticFunction.sigma_zero_apply]
      have hc := Nat.card_divisors_le_self (x : ℕ)
      have hx : (x : ℕ) < block * N := x.isLt
      omega
    let m : Fin (block * N) := ⟨block * N - k, by omega⟩
    have hm : f m ≤ block * N + 2 := le_trans (le_ciSup hbdd m) H
    dsimp [f, m] at hm
    omega
  · intro H
    have hnpos : 0 < block * N := Nat.mul_pos hblock (by omega)
    letI : Nonempty (Fin (block * N)) := Fin.pos_iff_nonempty.mp hnpos
    apply ciSup_le
    intro m
    by_cases hm0 : (m : ℕ) = 0
    · have hs0 : ArithmeticFunction.sigma 0 (m : ℕ) = 0 := by
        rw [hm0]
        native_decide
      omega
    · let k := block * N - (m : ℕ)
      have hk0 : 0 < k := by
        dsimp [k]
        omega
      have hkn : k < block * N := by
        dsimp [k]
        omega
      have hk := H k hk0 hkn
      have hnkm : block * N - k = (m : ℕ) := by
        dsimp [k]
        omega
      rw [hnkm] at hk
      omega

/-- Distinct canonical block/rung cells produce distinct shifted integers. -/
theorem erdos647_block_shift_value_injective :
    ∀ block N q₁ s₁ q₂ s₂ : ℕ,
      0 < block →
      q₁ < N → q₂ < N →
      0 < s₁ → s₁ ≤ block →
      0 < s₂ → s₂ ≤ block →
      block * (N - q₁) - s₁ = block * (N - q₂) - s₂ →
      q₁ = q₂ ∧ s₁ = s₂ := by
  intro block N q₁ s₁ q₂ s₂ hblock hq₁ hq₂ hs₁0 hs₁le hs₂0 hs₂le heq
  have hsplit₁ : block * N = block * q₁ + block * (N - q₁) := by
    rw [← Nat.mul_add]
    congr 1
    omega
  have hsplit₂ : block * N = block * q₂ + block * (N - q₂) := by
    rw [← Nat.mul_add]
    congr 1
    omega
  have hk₁le : block * q₁ + s₁ ≤ block * N := by
    calc
      block * q₁ + s₁ ≤ block * q₁ + block := Nat.add_le_add_left hs₁le _
      _ ≤ block * q₁ + block * (N - q₁) := by
        have hb : block ≤ block * (N - q₁) := by
          simpa using Nat.mul_le_mul_left block (by omega : 1 ≤ N - q₁)
        exact Nat.add_le_add_left hb _
      _ = block * N := hsplit₁.symm
  have hk₂le : block * q₂ + s₂ ≤ block * N := by
    calc
      block * q₂ + s₂ ≤ block * q₂ + block := Nat.add_le_add_left hs₂le _
      _ ≤ block * q₂ + block * (N - q₂) := by
        have hb : block ≤ block * (N - q₂) := by
          simpa using Nat.mul_le_mul_left block (by omega : 1 ≤ N - q₂)
        exact Nat.add_le_add_left hb _
      _ = block * N := hsplit₂.symm
  have hv₁ : block * (N - q₁) - s₁ =
      block * N - (block * q₁ + s₁) := by
    rw [hsplit₁]
    omega
  have hv₂ : block * (N - q₂) - s₂ =
      block * N - (block * q₂ + s₂) := by
    rw [hsplit₂]
    omega
  have hk : block * q₁ + s₁ = block * q₂ + s₂ := by
    rw [hv₁, hv₂] at heq
    omega
  have hq : q₁ = q₂ := by
    rcases lt_trichotomy q₁ q₂ with hlt | he | hgt
    · have hmul : block * (q₁ + 1) ≤ block * q₂ :=
        Nat.mul_le_mul_left block (by omega)
      have hle : block * q₁ + s₁ ≤ block * (q₁ + 1) := by
        calc
          block * q₁ + s₁ ≤ block * q₁ + block := Nat.add_le_add_left hs₁le _
          _ = block * (q₁ + 1) := by ring
      have hlt' : block * q₂ < block * q₂ + s₂ := by omega
      omega
    · exact he
    · have hmul : block * (q₂ + 1) ≤ block * q₁ :=
        Nat.mul_le_mul_left block (by omega)
      have hle : block * q₂ + s₂ ≤ block * (q₂ + 1) := by
        calc
          block * q₂ + s₂ ≤ block * q₂ + block := Nat.add_le_add_left hs₂le _
          _ = block * (q₂ + 1) := by ring
      have hlt' : block * q₁ < block * q₁ + s₁ := by omega
      omega
  constructor
  · exact hq
  · rw [hq] at hk
    omega
