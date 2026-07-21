import Mathlib

/-!
# Erdős #647 — exact residue encoding of the 7-adic and 3-adic depths

The sharp base gauntlet bounds the depths in
`360N-1 = 7^a7 q7` and `280N-1 = 3^a9 q9` by two, with the residual
cofactors coprime to the extracted primes.  Consequently all three possible
depths are exact congruence conditions on `N`: modulo `7,49` for `a7` and
modulo `3,9` for `a9`.

Together with the separate modulo-five theorem, this removes every adic depth
as an existential variable from the finite survivor state.  It is still a
structural reduction, not a global failed-shift theorem.

Tracked proof-search verification (2026-07-16):

* preverification job: `0d94fc60-8bd9-424a-8366-96ebff6ae4fe`
* problem version: `b6e53c77-9e5d-47f7-8a27-10dc5f5ed6ef`
* episode: `f9641fd5-9ce1-47ff-84d4-edc0a2083f42`
* root statement hash:
  `424d86d4216fd65b510715045d39c7e0ac7724da641800e6e1e1f9e2a641fe60`
* outcome: `kernel_verified`; replay: `matched(1)`
-/

namespace Erdos647

theorem base_gauntlet_higher_adic_depth_residues :
    ∀ N a7 q7 a9 q9 : ℕ,
      1 ≤ N →
      360 * N - 1 = 7 ^ a7 * q7 →
      ¬ 7 ∣ q7 →
      a7 ≤ 2 →
      280 * N - 1 = 3 ^ a9 * q9 →
      ¬ 3 ∣ q9 →
      a9 ≤ 2 →
      (a7 = 0 ↔ N % 7 ≠ 5) ∧
      (a7 = 1 ↔ N % 7 = 5 ∧ N % 49 ≠ 26) ∧
      (a7 = 2 ↔ N % 49 = 26) ∧
      (a9 = 0 ↔ N % 3 ≠ 1) ∧
      (a9 = 1 ↔ N % 3 = 1 ∧ N % 9 ≠ 1) ∧
      (a9 = 2 ↔ N % 9 = 1) := by
  intro N a7 q7 a9 q9 hN h7eq hq7 h7depth h9eq hq9 h9depth
  have hmod7 := Nat.mod_add_div N 7
  have hmod49 := Nat.mod_add_div N 49
  have hmod3 := Nat.mod_add_div N 3
  have hmod9 := Nat.mod_add_div N 9
  have h7zero : a7 = 0 → N % 7 ≠ 5 := by
    intro ha hres
    subst a7
    have hNform : N = 7 * (N / 7) + 5 := by omega
    have hqeq : q7 = 7 * (360 * (N / 7) + 257) := by
      norm_num at h7eq
      rw [hNform] at h7eq
      omega
    exact hq7 ⟨360 * (N / 7) + 257, hqeq⟩
  have h7one : a7 = 1 → N % 7 = 5 ∧ N % 49 ≠ 26 := by
    intro ha
    subst a7
    constructor
    · have hlt : N % 7 < 7 := Nat.mod_lt N (by norm_num)
      interval_cases hres : N % 7 <;> omega
    · intro hres
      have hNform : N = 49 * (N / 49) + 26 := by omega
      have hqeq : q7 = 7 * (360 * (N / 49) + 191) := by
        norm_num at h7eq
        rw [hNform] at h7eq
        omega
      exact hq7 ⟨360 * (N / 49) + 191, hqeq⟩
  have h7two : a7 = 2 → N % 49 = 26 := by
    intro ha
    subst a7
    have hlt : N % 49 < 49 := Nat.mod_lt N (by norm_num)
    interval_cases hres : N % 49 <;> omega
  have h9zero : a9 = 0 → N % 3 ≠ 1 := by
    intro ha hres
    subst a9
    have hNform : N = 3 * (N / 3) + 1 := by omega
    have hqeq : q9 = 3 * (280 * (N / 3) + 93) := by
      norm_num at h9eq
      rw [hNform] at h9eq
      omega
    exact hq9 ⟨280 * (N / 3) + 93, hqeq⟩
  have h9one : a9 = 1 → N % 3 = 1 ∧ N % 9 ≠ 1 := by
    intro ha
    subst a9
    constructor
    · have hlt : N % 3 < 3 := Nat.mod_lt N (by norm_num)
      interval_cases hres : N % 3 <;> omega
    · intro hres
      have hNform : N = 9 * (N / 9) + 1 := by omega
      have hqeq : q9 = 3 * (280 * (N / 9) + 31) := by
        norm_num at h9eq
        rw [hNform] at h9eq
        omega
      exact hq9 ⟨280 * (N / 9) + 31, hqeq⟩
  have h9two : a9 = 2 → N % 9 = 1 := by
    intro ha
    subst a9
    have hlt : N % 9 < 9 := Nat.mod_lt N (by norm_num)
    interval_cases hres : N % 9 <;> omega
  have h49to7 : N % 49 = 26 → N % 7 = 5 := by
    intro hres
    have hNform : N = 49 * (N / 49) + 26 := by omega
    have hlt : N % 7 < 7 := Nat.mod_lt N (by norm_num)
    interval_cases h : N % 7 <;> omega
  have h9to3 : N % 9 = 1 → N % 3 = 1 := by
    intro hres
    have hNform : N = 9 * (N / 9) + 1 := by omega
    have hlt : N % 3 < 3 := Nat.mod_lt N (by norm_num)
    interval_cases h : N % 3 <;> omega
  refine ⟨⟨h7zero, ?_⟩, ⟨h7one, ?_⟩, ⟨h7two, ?_⟩,
    ⟨h9zero, ?_⟩, ⟨h9one, ?_⟩, ⟨h9two, ?_⟩⟩
  · intro hres
    interval_cases ha : a7
    · rfl
    · exact absurd (h7one rfl).1 hres
    · exact absurd (h49to7 (h7two rfl)) hres
  · rintro ⟨hres7, hres49⟩
    interval_cases ha : a7
    · exact False.elim ((h7zero rfl) hres7)
    · rfl
    · exact absurd (h7two rfl) hres49
  · intro hres49
    interval_cases ha : a7
    · exact False.elim ((h7zero rfl) (h49to7 hres49))
    · exact absurd hres49 (h7one rfl).2
    · rfl
  · intro hres
    interval_cases ha : a9
    · rfl
    · exact absurd (h9one rfl).1 hres
    · exact absurd (h9to3 (h9two rfl)) hres
  · rintro ⟨hres3, hres9⟩
    interval_cases ha : a9
    · exact False.elim ((h9zero rfl) hres3)
    · rfl
    · exact absurd (h9two rfl) hres9
  · intro hres9
    interval_cases ha : a9
    · exact False.elim ((h9zero rfl) (h9to3 hres9))
    · exact absurd hres9 (h9one rfl).2
    · rfl

end Erdos647
