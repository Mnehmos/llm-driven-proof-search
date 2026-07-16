import Mathlib

/-!
# Erdős #647 — exact gcd-class transport for shifted multiples of 2520

Divisibility by every divisor of `2520` is transported exactly from the
shift `k` to `2520*N-k`.  Consequently the two numbers have the same gcd
with `2520`.  This is the arithmetic interface for the class-sensitive
power-prefix constants.

Both declarations were kernel-verified on 2026-07-16:

* `erdos647_divisor_dvd_shift_iff`: problem
  `0a9d617d-7ccf-4d61-b24c-fd8e9cb98ebc`, episode
  `f2d12a4a-4591-4894-9985-744928091a00`, statement hash
  `7a25e346cef0e9d77264dc3d87a2e20de89138508a920351d2b7c6e70c03e0ed`,
  preverification `c7c59712-0bf9-418c-bfb0-d424a303adf4` (`kernel_pass`).
* `erdos647_shift_gcd_2520`: problem
  `80655568-e511-4b2a-bb75-323cb62ed186`, episode
  `d32e0f26-8d19-4ce7-8eb4-36f049af57ce`, statement hash
  `11c7ebee0179d2d86b4965341a58125ea74135f63a82f687bb5ef0ed43c4d063`,
  preverification `be7bbab3-225e-42a1-bb5b-b6b01b495180` (`kernel_pass`).
  Its tracked proof inlined the first declaration because tracked replays do
  not import sibling snapshots.
-/

theorem erdos647_divisor_dvd_shift_iff :
    ∀ N k p : ℕ, k ≤ 2520 * N → p ∣ 2520 →
      (p ∣ 2520 * N - k ↔ p ∣ k) := by
  intro N k p hkn hp
  have hbase : p ∣ 2520 * N := Dvd.dvd.mul_right hp N
  constructor
  · intro hshift
    have h := Nat.dvd_sub hbase hshift
    rwa [show 2520 * N - (2520 * N - k) = k by omega] at h
  · intro hk
    exact Nat.dvd_sub hbase hk

theorem erdos647_shift_gcd_2520 :
    ∀ N k : ℕ, k ≤ 2520 * N →
      Nat.gcd (2520 * N - k) 2520 = Nat.gcd k 2520 := by
  intro N k hkn
  apply Nat.dvd_antisymm
  · apply Nat.dvd_gcd
    · exact (erdos647_divisor_dvd_shift_iff N k (Nat.gcd (2520 * N - k) 2520)
        hkn (Nat.gcd_dvd_right _ _)).mp (Nat.gcd_dvd_left _ _)
    · exact Nat.gcd_dvd_right _ _
  · apply Nat.dvd_gcd
    · exact (erdos647_divisor_dvd_shift_iff N k (Nat.gcd k 2520)
        hkn (Nat.gcd_dvd_right _ _)).mpr (Nat.gcd_dvd_left _ _)
    · exact Nat.gcd_dvd_right _ _
