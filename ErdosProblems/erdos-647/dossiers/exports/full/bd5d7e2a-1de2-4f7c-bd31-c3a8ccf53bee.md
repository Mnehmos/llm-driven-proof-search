# ⚠️ KERNEL-VERIFIED FORMAL STATEMENT — FIDELITY NOT YET VERIFIED — Erdos #647 continuation: a survivor satisfying every shift budget escapes any fixed multiplicative prime catalog M at a positive shift k bounded by M, producing a prime factor not dividing M.

> This proof establishes:
>
> `∀ n M : ℕ,
  0 < M →
  M + 1 < n →
  (∀ k : ℕ, 0 < k → k < n →
    ArithmeticFunction.sigma 0 (n - k) ≤ k + 2) →
  ∃ k p : ℕ,
    0 < k ∧ k ≤ M ∧ k < n ∧
    Nat.Prime p ∧ p ∣ n - k ∧ ¬ p ∣ M ∧
    ArithmeticFunction.sigma 0 (n - k) ≤ M + 2`
>
> It does **not yet** certify the source claim above.

**Root goal (formal):** `∀ n M : ℕ,
  0 < M →
  M + 1 < n →
  (∀ k : ℕ, 0 < k → k < n →
    ArithmeticFunction.sigma 0 (n - k) ≤ k + 2) →
  ∃ k p : ℕ,
    0 < k ∧ k ≤ M ∧ k < n ∧
    Nat.Prime p ∧ p ∣ n - k ∧ ¬ p ∣ M ∧
    ArithmeticFunction.sigma 0 (n - k) ≤ M + 2`

| Proof soundness | Statement fidelity | Canonical promotion | Training eligibility |
|---|---|---|---|
| VERIFIED | ATTESTED (unsafe_dev_attestation — not reviewed) | BLOCKED | QUARANTINED |

| episode | state | steps | budget left (μ$) | started | finished |
|---|---|---|---|---|---|
| `bd5d7e2a-1de2-4f7c-bd31-c3a8ccf53bee` | terminated (root_proved) | 1 | — | 2026-07-16T19:51:16 | 2026-07-16T19:51:52 |

## Proof tree

- ✅ **root_theorem** : `∀ n M : ℕ,
  0 < M →
  M + 1 < n →
  (∀ k : ℕ, 0 < k → k < n →
    ArithmeticFunction.sigma 0 (n - k) ≤ k + 2) →
  ∃ k p : ℕ,
    0 < k ∧ k ≤ M ∧ k < n ∧
    Nat.Prime p ∧ p ∣ n - k ∧ ¬ p ∣ M ∧
    ArithmeticFunction.sigma 0 (n - k) ≤ M + 2`

## The proof, assembled

```lean
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib

theorem root_theorem : ∀ n M : ℕ,
  0 < M →
  M + 1 < n →
  (∀ k : ℕ, 0 < k → k < n →
    ArithmeticFunction.sigma 0 (n - k) ≤ k + 2) →
  ∃ k p : ℕ,
    0 < k ∧ k ≤ M ∧ k < n ∧
    Nat.Prime p ∧ p ∣ n - k ∧ ¬ p ∣ M ∧
    ArithmeticFunction.sigma 0 (n - k) ≤ M + 2 := by
intro n M hM hMn hbudget
let r := (n - 1) % M
obtain ⟨k, hkpos, hkM, hkn, hd⟩ :
    ∃ k, 0 < k ∧ k ≤ M ∧ k < n ∧ M ∣ (n - k - 1) := by
  by_cases hr : r = 0
  · refine ⟨M, hM, le_rfl, by omega, ?_⟩
    have hd : M ∣ n - 1 := Nat.dvd_iff_mod_eq_zero.2 hr
    have heq : n - M - 1 = (n - 1) - M := by omega
    rw [heq]
    exact Nat.dvd_sub hd (dvd_refl M)
  · have hrpos : 0 < r := Nat.pos_of_ne_zero hr
    have hrlt : r < M := Nat.mod_lt _ hM
    refine ⟨r, hrpos, hrlt.le, by omega, ?_⟩
    have hdecomp : n - 1 = M * ((n - 1) / M) + r := by
      simpa [r, Nat.add_comm] using (Nat.mod_add_div (n - 1) M).symm
    refine ⟨(n - 1) / M, ?_⟩
    omega
have hmgt : 1 < n - k := by omega
obtain ⟨q, hq⟩ := hd
have hmrepr : n - k = 1 + M * q := by omega
have hcop : Nat.Coprime M (n - k) := by
  rw [hmrepr]
  exact (Nat.coprime_add_mul_left_right M 1 q).2 (Nat.coprime_one_right M)
obtain ⟨p, hpprime, hpdvd⟩ := Nat.exists_prime_and_dvd (by omega : n - k ≠ 1)
have hpnot : ¬ p ∣ M := by
  intro hpM
  have hMp : Nat.Coprime M p := hcop.coprime_dvd_right hpdvd
  have hpone : p = 1 := Nat.eq_one_of_dvd_coprimes hMp hpM (dvd_refl p)
  exact hpprime.ne_one hpone
have hτ := hbudget k hkpos hkn
refine ⟨k, p, hkpos, hkM, hkn, hpprime, hpdvd, hpnot, ?_⟩
omega

```

## How it went — every attempt, in order

| # | obligation | action | detail | verdict |
|---|---|---|---|---|
| 2 | `root_theorem` | solve | `intro n M hM hMn hbudget ; let r := (n - 1) % M ; obtain ⟨k, hkpos, hkM, hkn, hd⟩ : ;     ∃ k, 0 < k ∧ k ≤ M ∧ k < n ∧ M ∣ (n - k - 1) := by ;   by_cases hr : r = 0 ;   · refine ⟨M, hM, le_rfl, by omega, ?_⟩ ;     have hd : M ∣ n - 1 := Nat.dvd_iff_mod_eq_zero.2 hr ;     have heq : n - M - 1 = (n - 1) - M := by omega ;     rw [heq] ;     exact Nat.dvd_sub hd (dvd_refl M) ;   · have hrpos : 0 < r := Nat.pos_of_ne_zero hr ;     have hrlt : r < M := Nat.mod_lt _ hM ;     refine ⟨r, hrpos, hrlt.le, by omega, ?_⟩ ;     have hdecomp : n - 1 = M * ((n - 1) / M) + r := by ;       simpa [r, Nat.add_comm] using (Nat.mod_add_div (n - 1) M).symm ;     refine ⟨(n - 1) / M, ?_⟩ ;     omega ; have hmgt : 1 < n - k := by omega ; obtain ⟨q, hq⟩ := hd ; have hmrepr : n - k = 1 + M * q := by omega ; have hcop : Nat.Coprime M (n - k) := by ;   rw [hmrepr] ;   exact (Nat.coprime_add_mul_left_right M 1 q).2 (Nat.coprime_one_right M) ; obtain ⟨p, hpprime, hpdvd⟩ := Nat.exists_prime_and_dvd (by omega : n - k ≠ 1) ; have hpnot : ¬ p ∣ M := by ;   intro hpM ;   have hMp : Nat.Coprime M p := hcop.coprime_dvd_right hpdvd ;   have hpone : p = 1 := Nat.eq_one_of_dvd_coprimes hMp hpM (dvd_refl p) ;   exact hpprime.ne_one hpone ; have hτ := hbudget k hkpos hkn ; refine ⟨k, p, hkpos, hkM, hkn, hpprime, hpdvd, hpnot, ?_⟩ ; omega` | ✅ kernel_pass |

## Verification context

- **Environment hash:** `9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d`
- **Import manifest hash:** `aaf21893d520a78dee0787a1bcaf939ee6b922265ff670c272e2e1d450dd29a7`
- **Import manifest:** `["Mathlib.Tactic.Ring","Mathlib.Tactic.NormNum","Mathlib"]`
- **proof_body_redacted:** false

## Integrity

3 hash-chained trajectory events, `2f153966ae38…` → `dd89c491d3fe…` (GENESIS-anchored). Re-verify anytime with `episode_replay`.
