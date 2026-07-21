import Mathlib

/-!
# Erdős #647 — exact residue encoding of the two 5-adic gauntlet depths

The sharp base-gauntlet state bounds the 5-adic escape depths at shifts `5`
and `10` by one.  Once the extracted cofactors are known to be coprime to
five, those depths are not merely bounded: they are determined exactly by
the residue of the common parameter `N` modulo five.

This removes two existential branch variables from the finite survivor state
used in the continuing attempt to prove a universal failed shift.  It is a
structural reduction, not a closure of the Formal Conjectures declaration.

Tracked proof-search verification (2026-07-16):

* preverification job: `a3ea80e7-012f-4ae6-ad2c-22f850b923bc`
* problem version: `eebc0500-b83d-48ee-b488-ab270994c41b`
* episode: `dce030c5-2b7c-4e69-99fc-f4596b52f736`
* root statement hash:
  `d30e78189281a84b83205ca5a2b336783a66c90ed10f273523034b2220d140e5`
* outcome: `kernel_verified`; replay: `matched(1)`
-/

namespace Erdos647

theorem base_gauntlet_five_adic_depth_residues :
    ∀ N a5 q5 a10 q10 : ℕ,
      1 ≤ N →
      504 * N - 1 = 5 ^ a5 * q5 →
      ¬ 5 ∣ q5 →
      a5 ≤ 1 →
      252 * N - 1 = 5 ^ a10 * q10 →
      ¬ 5 ∣ q10 →
      a10 ≤ 1 →
      (a5 = 1 ↔ N % 5 = 4) ∧ (a10 = 1 ↔ N % 5 = 3) := by
  intro N a5 q5 a10 q10 hN h5eq hq5 h5depth h10eq hq10 h10depth
  have hmodlt : N % 5 < 5 := Nat.mod_lt N (by norm_num)
  have hdecomp := Nat.mod_add_div N 5
  constructor
  · constructor
    · intro ha5
      subst a5
      interval_cases hres : N % 5 <;> omega
    · intro hres
      interval_cases ha5 : a5
      · have hNform : N = 5 * (N / 5) + 4 := by omega
        have hq5eq : q5 = 5 * (504 * (N / 5) + 403) := by
          norm_num at h5eq
          rw [hNform] at h5eq
          omega
        have hdiv : 5 ∣ q5 := by
          refine ⟨504 * (N / 5) + 403, ?_⟩
          exact hq5eq
        exact absurd hdiv hq5
      · rfl
  · constructor
    · intro ha10
      subst a10
      interval_cases hres : N % 5 <;> omega
    · intro hres
      interval_cases ha10 : a10
      · have hNform : N = 5 * (N / 5) + 3 := by omega
        have hq10eq : q10 = 5 * (252 * (N / 5) + 151) := by
          norm_num at h10eq
          rw [hNform] at h10eq
          omega
        have hdiv : 5 ∣ q10 := by
          refine ⟨252 * (N / 5) + 151, ?_⟩
          exact hq10eq
        exact absurd hdiv hq10
      · rfl

end Erdos647
