import Mathlib

/-!
# Erdős Problem #1113 — there are infinitely many Sierpiński numbers

A **Sierpiński number** is a positive odd `k` such that `k·2ⁿ + 1` is composite
for every `n`. Sierpiński (1960) proved there are infinitely many; the corpus
(`FormalConjectures/ErdosProblems/1113.lean`) ships the statement as `sorry`.
This file gives a self-contained, kernel-verified proof.

`Composite` and `IsSierpinskiNumber` below are byte-for-byte the corpus /
`FormalConjecturesForMathlib` definitions (they are not in plain Mathlib).

**Trust note.** This proof uses only kernel `decide` (not `native_decide`) for
the finite covering checks, so `#print axioms` is exactly
`[propext, Classical.choice, Quot.sound]` — the standard Mathlib trio, with no
compiler-trusted `Lean.ofReduceBool`. That is a strictly stronger guarantee than
the corpus's own `selfridge_78557`, which discharges the same checks by
`native_decide`.

## Proof

Selfridge's covering set `P = {3,5,7,13,19,37,73}` works for `78557`: every
`78557·2ⁿ+1` is divisible by some `p ∈ P` (checked on `n mod 36`, valid since
`2³⁶ ≡ 1 (mod p)` for each `p`). Because every `p ∈ P` divides
`M = 3·5·7·13·19·37·73 = 70050435`, **any** `k ≡ 78557 (mod M)` satisfies
`k·2ⁿ+1 ≡ 78557·2ⁿ+1 (mod p)`, so the same covering makes every `k·2ⁿ+1`
composite. The arithmetic progression `k = 78557 + j·(2M)` (`j ∈ ℕ`) stays odd
and stays `≡ 78557 (mod M)`, giving infinitely many Sierpiński numbers. ∎
-/

namespace Erdos1113

/-- `Composite n` (copy of `FormalConjecturesForMathlib.Data.Nat.Prime.Composite`). -/
def Composite (n : ℕ) : Prop := 1 < n ∧ ¬ n.Prime

/-- `IsSierpinskiNumber k` (copy of `FormalConjecturesForMathlib.NumberTheory.SierpinskiNumber`). -/
def IsSierpinskiNumber (k : ℕ) : Prop := ¬ 2 ∣ k ∧ ∀ n, Composite (k * 2 ^ n + 1)

-- The covering modulus is `M = 3·5·7·13·19·37·73 = 70050435`, inlined below.

set_option maxHeartbeats 4000000 in
/-- **Any `k ≡ 78557 (mod M)` that is odd is a Sierpiński number** — Selfridge's
covering set for `78557` transfers to the whole residue class. -/
theorem sierpinski_of_congr (k : ℕ) (hodd : ¬ 2 ∣ k)
    (hk : k ≡ 78557 [MOD 70050435]) : IsSierpinskiNumber k := by
  have hk78557 : 78557 ≤ k := by
    have h : k % 70050435 = 78557 := by
      have h2 := hk
      unfold Nat.ModEq at h2
      rwa [Nat.mod_eq_of_lt (by norm_num : (78557 : ℕ) < 70050435)] at h2
    calc (78557 : ℕ) = k % 70050435 := h.symm
      _ ≤ k := Nat.mod_le k 70050435
  refine ⟨hodd, fun n => ⟨?_, ?_⟩⟩
  · -- 1 < k·2ⁿ+1
    have hp : 0 < k * 2 ^ n := Nat.mul_pos (by omega) (pow_pos (show 0 < 2 by norm_num) n)
    omega
  · -- ¬ (k·2ⁿ+1).Prime, via the transferred covering
    have hcov : ∃ p ∈ ([3, 5, 7, 13, 19, 37, 73] : List ℕ), p ∣ (k * 2 ^ n + 1) := by
      have base : ∀ r, r < 36 → ∃ p ∈ ([3, 5, 7, 13, 19, 37, 73] : List ℕ),
          p ∣ (78557 * 2 ^ r + 1) := by decide
      obtain ⟨p, hpmem, hpdvd⟩ := base (n % 36) (Nat.mod_lt _ (by norm_num))
      refine ⟨p, hpmem, ?_⟩
      have hp36 : (2 : ℕ) ^ 36 ≡ 1 [MOD p] := by fin_cases hpmem <;> decide
      have e2 : (2 : ℕ) ^ n ≡ 2 ^ (n % 36) [MOD p] := by
        conv_lhs => rw [← Nat.div_add_mod n 36, pow_add, pow_mul]
        calc ((2 : ℕ) ^ 36) ^ (n / 36) * 2 ^ (n % 36)
            ≡ 1 ^ (n / 36) * 2 ^ (n % 36) [MOD p] := Nat.ModEq.mul_right _ (hp36.pow _)
          _ = 2 ^ (n % 36) := by rw [one_pow, one_mul]
      have hp78557 : p ∣ 78557 * 2 ^ n + 1 := by
        have e3 : 78557 * 2 ^ n + 1 ≡ 78557 * 2 ^ (n % 36) + 1 [MOD p] :=
          (e2.mul_left 78557).add_right 1
        exact (Nat.modEq_zero_iff_dvd).mp (e3.trans ((Nat.modEq_zero_iff_dvd).mpr hpdvd))
      have hpM : p ∣ 70050435 := by fin_cases hpmem <;> decide
      have hkp : k ≡ 78557 [MOD p] := hk.of_dvd hpM
      have ek : k * 2 ^ n + 1 ≡ 78557 * 2 ^ n + 1 [MOD p] := (hkp.mul_right _).add_right 1
      exact (Nat.modEq_zero_iff_dvd).mp (ek.trans ((Nat.modEq_zero_iff_dvd).mpr hp78557))
    intro hprime
    obtain ⟨p, hpmem, hpdvd⟩ := hcov
    have h2n : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    rcases hprime.eq_one_or_self_of_dvd p hpdvd with h | h <;> fin_cases hpmem <;>
      nlinarith [hk78557, h2n]

/-- **Erdős #1113 (Sierpiński 1960): there are infinitely many Sierpiński numbers.** -/
theorem infinitely_many_sierpinski : Set.Infinite {k : ℕ | IsSierpinskiNumber k} := by
  apply Set.infinite_of_injective_forall_mem (f := fun j : ℕ => 78557 + j * (2 * 70050435))
  · intro x y hxy
    simp only [] at hxy
    omega
  · intro j
    simp only [Set.mem_setOf_eq]
    refine sierpinski_of_congr _ ?_ ?_
    · omega
    · -- 78557 + j·(2·70050435) ≡ 78557 (mod 70050435)
      have hz : j * (2 * 70050435) ≡ 0 [MOD 70050435] :=
        (Nat.modEq_zero_iff_dvd).mpr ⟨j * 2, by ring⟩
      simpa using Nat.ModEq.add_left 78557 hz

end Erdos1113
