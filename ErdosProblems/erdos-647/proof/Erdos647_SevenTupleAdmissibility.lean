import Mathlib

/-!
# Erdős #647 — Layer C: seven-tuple root-union admissibility

Snapshots of the exact statements + proof terms kernel-verified through the
tracked proof-search pipeline on 2026-07-14.

## The seven-tuple

Layer C (the 7-tuple application of the Selberg-sieve density-bound
program) needs an explicit admissible tuple of 7 linear forms. Rather than
Hughes's exact construction (whose proof lives in an unpublished
companion manuscript, "HughesChains, submitted for publication 2026",
absent from his public Lean repo — see campaign memory for the full
research trace), this campaign independently re-derived a seven-tuple
directly from its OWN already-proven theorems:

  - Stage 1 (proven elsewhere): every candidate `n > 84` has `2520 ∣ n`;
    write `n = 2520N`.
  - Stage 2 (proven elsewhere): every candidate lies in Family A
    (`n = 8s+8` with `s, 2s+1, 4s+3, 8s+7` all prime) or Family B. For
    Family A, `2520 ∣ n` forces `s = 315N - 1`, turning the four base
    forms into `315N-1, 630N-1, 1260N-1, 2520N-1`.
  - The campaign's own prior pure-prime shift classifications (shifts
    3, 6, 12) give three more forms directly from `n = 2520N`:
    `(n-3)/3 = 840N-1`, `(n-6)/6 = 420N-1`, `(n-12)/12 = 210N-1`.

Together: the seven-tuple `{210N-1, 315N-1, 420N-1, 630N-1, 840N-1,
1260N-1, 2520N-1}`, i.e. `(2520/k)·N - 1` for `k ∈ {1,2,3,4,6,8,12}`.

## Admissibility

`gcd(210,315,420,630,840,1260,2520) = 105 = 3·5·7`: every coefficient is
divisible by 3, 5, and 7 (structurally — none of `k∈{1,2,3,4,6,8,12}`
shares a factor with 5 or 7, and at most one factor of 3 is ever divided
out of `2520 = 2³·3²·5·7`). Consequence: every form is `≡ -1` mod
`{3,5,7}` identically, so these three primes never divide any form
(root-union size 0 — verified below) and are structurally EXCLUDED from
the sieve's active prime set (Mathlib's `BoundingSieve` requires
`0 < ν(p)` for every included prime, which `ν=0` at these primes would
violate). At `p=2`, only the `315N-1` form has an odd coefficient, giving
root-union size exactly 1. At every prime `p>7`, none of the seven
coefficients share a factor with `p` (their only prime factors are
`≤7<p`), so all seven forms are "active" and the root-union has size
between 1 and 7.

  problem_version_id (small primes)   92b5e5ae-10c1-4bf5-afe5-a92f2e8a370e
  episode_id (small primes)           979203b4-13fe-41e7-a21c-f623eb6636a8
  problem_version_id (general p>7)    d11f502a-b003-42c5-a2db-5530a4a8b141
  episode_id (general p>7)            0d088b9a-9a13-4b05-9e1b-1fdc3a0cc761
  outcome                             kernel_verified (root_proved), both
  import manifest                     ["Mathlib.Tactic.Ring", "Mathlib.Tactic.NormNum", "Mathlib"]

The general theorem (`erdos647_seventuple_admissible_general`) is proven
UNIFORMLY for every prime `p>7` — not checked for finitely many primes —
via existence (each coefficient is a unit mod `p`, giving a `ZMod p`
inverse) and uniqueness (cancellation in the field `ZMod p`) of the root
of `c·r ≡ 1 (mod p)` for each of the 7 coefficients, combined via a
union-of-≤7-singletons cardinality bound.
-/

theorem erdos647_seventuple_admissible_small_primes :
    ((Finset.range 2).filter (fun r => (210*r)%2=1 ∨ (315*r)%2=1 ∨ (420*r)%2=1 ∨ (630*r)%2=1 ∨ (840*r)%2=1 ∨ (1260*r)%2=1 ∨ (2520*r)%2=1)).card = 1 ∧
    ((Finset.range 3).filter (fun r => (210*r)%3=1 ∨ (315*r)%3=1 ∨ (420*r)%3=1 ∨ (630*r)%3=1 ∨ (840*r)%3=1 ∨ (1260*r)%3=1 ∨ (2520*r)%3=1)).card = 0 ∧
    ((Finset.range 5).filter (fun r => (210*r)%5=1 ∨ (315*r)%5=1 ∨ (420*r)%5=1 ∨ (630*r)%5=1 ∨ (840*r)%5=1 ∨ (1260*r)%5=1 ∨ (2520*r)%5=1)).card = 0 ∧
    ((Finset.range 7).filter (fun r => (210*r)%7=1 ∨ (315*r)%7=1 ∨ (420*r)%7=1 ∨ (630*r)%7=1 ∨ (840*r)%7=1 ∨ (1260*r)%7=1 ∨ (2520*r)%7=1)).card = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

theorem erdos647_seventuple_admissible_general :
    ∀ (p : ℕ), p.Prime → 7 < p →
      1 ≤ ((Finset.range p).filter (fun r => (210*r)%p=1 ∨ (315*r)%p=1 ∨ (420*r)%p=1 ∨ (630*r)%p=1 ∨ (840*r)%p=1 ∨ (1260*r)%p=1 ∨ (2520*r)%p=1)).card ∧
      ((Finset.range p).filter (fun r => (210*r)%p=1 ∨ (315*r)%p=1 ∨ (420*r)%p=1 ∨ (630*r)%p=1 ∨ (840*r)%p=1 ∨ (1260*r)%p=1 ∨ (2520*r)%p=1)).card ≤ 7 := by
  intro p hp hp7
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (1 < p) := ⟨hp.one_lt⟩
  have hexists : ∀ (c : ℕ), ¬ p ∣ c → ∃ r < p, (c * r) % p = 1 := by
    intro c hpc
    have hcne : (c : ZMod p) ≠ 0 := by rwa [Ne, ZMod.natCast_eq_zero_iff]
    refine ⟨((c:ZMod p)⁻¹).val, ZMod.val_lt _, ?_⟩
    have h1 : (c:ZMod p) * (c:ZMod p)⁻¹ = 1 := mul_inv_cancel₀ hcne
    have h2 : ((c * ((c:ZMod p)⁻¹).val : ℕ) : ZMod p) = 1 := by
      push_cast; rw [ZMod.natCast_val, ZMod.cast_id]; exact h1
    have h4 : (c * ((c:ZMod p)⁻¹).val) % p < p := Nat.mod_lt _ hp.pos
    have h3 : (((c * ((c:ZMod p)⁻¹).val) % p : ℕ) : ZMod p) = 1 := by rwa [ZMod.natCast_mod]
    have h6 := congrArg ZMod.val h3
    rw [ZMod.val_cast_of_lt h4, ZMod.val_one] at h6
    exact h6
  have hunique : ∀ (c : ℕ), ¬ p ∣ c → ∀ r1 r2, r1 < p → r2 < p → (c*r1)%p=1 → (c*r2)%p=1 → r1=r2 := by
    intro c hpc r1 r2 hr1 hr2 h1 h2
    have hcne : (c : ZMod p) ≠ 0 := by rwa [Ne, ZMod.natCast_eq_zero_iff]
    have e1 : ((c*r1 : ℕ) : ZMod p) = 1 := by
      have hh := congrArg (Nat.cast (R := ZMod p)) h1
      rw [ZMod.natCast_mod] at hh
      simpa using hh
    have e2 : ((c*r2 : ℕ) : ZMod p) = 1 := by
      have hh := congrArg (Nat.cast (R := ZMod p)) h2
      rw [ZMod.natCast_mod] at hh
      simpa using hh
    have e3 : (c:ZMod p) * (r1:ZMod p) = (c:ZMod p) * (r2:ZMod p) := by
      push_cast at e1 e2
      rw [e1, e2]
    have e4 : (r1 : ZMod p) = (r2 : ZMod p) := mul_left_cancel₀ hcne e3
    have e5 := congrArg ZMod.val e4
    rwa [ZMod.val_cast_of_lt hr1, ZMod.val_cast_of_lt hr2] at e5
  have hnd : ∀ c ∈ ([210,315,420,630,840,1260,2520] : List ℕ), ¬ p ∣ c := by
    intro c hc hpdvd
    have hcdvd : c ∣ 2520 := by fin_cases hc <;> norm_num
    have hpdvd2520 : p ∣ 2520 := hpdvd.trans hcdvd
    have hpmem : p ∈ Nat.primeFactors 2520 := Nat.mem_primeFactors.mpr ⟨hp, hpdvd2520, by norm_num⟩
    have hpf : Nat.primeFactors 2520 = {2,3,5,7} := by native_decide
    rw [hpf] at hpmem
    fin_cases hpmem <;> omega
  set S210 := (Finset.range p).filter (fun r => (210*r)%p=1) with hS210
  set S315 := (Finset.range p).filter (fun r => (315*r)%p=1) with hS315
  set S420 := (Finset.range p).filter (fun r => (420*r)%p=1) with hS420
  set S630 := (Finset.range p).filter (fun r => (630*r)%p=1) with hS630
  set S840 := (Finset.range p).filter (fun r => (840*r)%p=1) with hS840
  set S1260 := (Finset.range p).filter (fun r => (1260*r)%p=1) with hS1260
  set S2520 := (Finset.range p).filter (fun r => (2520*r)%p=1) with hS2520
  have hcard1 : ∀ c ∈ ([210,315,420,630,840,1260,2520] : List ℕ), ((Finset.range p).filter (fun r => (c*r)%p=1)).card ≤ 1 := by
    intro c hc
    rw [Finset.card_le_one]
    intro r1 hr1 r2 hr2
    simp only [Finset.mem_filter, Finset.mem_range] at hr1 hr2
    exact hunique c (hnd c hc) r1 r2 hr1.1 hr2.1 hr1.2 hr2.2
  have hS210c : S210.card ≤ 1 := hcard1 210 (by simp)
  have hS315c : S315.card ≤ 1 := hcard1 315 (by simp)
  have hS420c : S420.card ≤ 1 := hcard1 420 (by simp)
  have hS630c : S630.card ≤ 1 := hcard1 630 (by simp)
  have hS840c : S840.card ≤ 1 := hcard1 840 (by simp)
  have hS1260c : S1260.card ≤ 1 := hcard1 1260 (by simp)
  have hS2520c : S2520.card ≤ 1 := hcard1 2520 (by simp)
  have hSeq : (Finset.range p).filter (fun r => (210*r)%p=1 ∨ (315*r)%p=1 ∨ (420*r)%p=1 ∨ (630*r)%p=1 ∨ (840*r)%p=1 ∨ (1260*r)%p=1 ∨ (2520*r)%p=1) = S210 ∪ S315 ∪ S420 ∪ S630 ∪ S840 ∪ S1260 ∪ S2520 := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union, hS210, hS315, hS420, hS630, hS840, hS1260, hS2520]
    tauto
  rw [hSeq]
  constructor
  · obtain ⟨r, hr, hr1⟩ := hexists 2520 (hnd 2520 (by simp))
    have hrmem : r ∈ S2520 := by simp [hS2520, hr, hr1]
    have hpos : 0 < S2520.card := Finset.card_pos.mpr ⟨r, hrmem⟩
    calc 1 ≤ S2520.card := hpos
      _ ≤ (S210 ∪ S315 ∪ S420 ∪ S630 ∪ S840 ∪ S1260 ∪ S2520).card := by
          apply Finset.card_le_card
          intro x hx
          simp only [Finset.mem_union]
          tauto
  · calc (S210 ∪ S315 ∪ S420 ∪ S630 ∪ S840 ∪ S1260 ∪ S2520).card
        ≤ S210.card + S315.card + S420.card + S630.card + S840.card + S1260.card + S2520.card := by
          apply le_trans (Finset.card_union_le _ _)
          gcongr
          apply le_trans (Finset.card_union_le _ _)
          gcongr
          apply le_trans (Finset.card_union_le _ _)
          gcongr
          apply le_trans (Finset.card_union_le _ _)
          gcongr
          apply le_trans (Finset.card_union_le _ _)
          gcongr
          exact Finset.card_union_le _ _
      _ ≤ 1+1+1+1+1+1+1 := by
          gcongr
      _ = 7 := by norm_num
