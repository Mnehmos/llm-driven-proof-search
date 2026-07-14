/-
Erdős Problem #858 — a concrete instantiation of the parent map π.
(Chojecki 2026, "An exact frontier theorem and the asymptotic constant for
Erdős problem #858", Corollary 2.2 / Lemma 2.3 "first step toward defining π
in Lean".)

Byte-faithful reconstruction of the kernel-verified root theorem from the
proofsearch MCP episode 2de97643-e375-4b5a-87af-9150f3ec7546,
problem_version_id 18d8bb2d-3892-4b29-afc8-373a70efbd2f.
Outcome: kernel_verified / root_kernel_verified.
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 4b3902ef…

The §3 frontier-sweep results (Erdos858_FrontierSweepStep/Telescope/BaseZero,
Erdos858_FrontierAntichain) were proved ABSTRACTLY for any parent map π
satisfying three structural axioms: π 1 = 0, (2 ≤ n ⇒ 1 ≤ π n < n), and
π-maximality (z < m, z ⪯ m ⇒ z ≤ π m). This theorem exhibits a genuine,
concrete π and proves it satisfies exactly those axioms — closing the gap
between the abstract §3 theorems and a real, usable parent-map function.

IMPORTANT DESIGN NOTE (why this avoids Lemma 2.3's harder direction): a
naive "greedy" definition of π via a left-to-right walk over the sorted prime
factorization (extend while the next prime exceeds the running product, stop
at the first failure) is WRONG. Counterexample found by hand: n = 99 = 3·3·11.
The prefix 3 is NOT an ancestor of 99 (cofactor 33 = 3·11 has minFac 3, not
> 3), but the prefix 9 = 3·3 IS an ancestor (cofactor 11, minFac 11 > 9) —
validity of prefix index k is genuinely non-monotone in k, so a greedy scan
would incorrectly stop at k=1 (giving 3) instead of finding the true maximum
at k=2 (giving 9). Lemma 2.3's own characterization ("π(n) = P_k for the
LARGEST valid k") reflects this. Rather than re-deriving that harder
characterization, this theorem sidesteps it entirely: define
`piFn n := max { a < n : a ⪯ n }` directly via `Finset.max'` over the
already-verified `⪯` relation (Erdos858_PreceqPartialOrder /
Erdos858_Lemma21_Sandwich / Erdos858_Cor22_AncestorsLinear). Since `1 ⪯ n`
always holds, this set is always nonempty for n ≥ 2, and the three axioms
follow directly from `Finset.le_max'` / `Finset.max'_mem` — no prefix-product
reasoning needed at all.

TECHNICAL NOTE: since this environment's problem_versions are elaborated
independently (a plain top-level `def` in one problem cannot be referenced by
a separately-registered problem's root_formal_statement), `piFn` is defined
INLINE via a `let` inside the root statement itself, using
`Classical.decPred` for the `⪯`-filter's decidability (proof-theoretic only,
no computation needed). After `refine`/`intro` on such a goal, the let-bound
name does NOT survive as a usable local variable — Lean shows it as an
unreduced `(fun n => ...) n` application. `dsimp only` (NOT `unfold_let`,
which does not exist in this Mathlib pin) is the tactic that exposes the
raw `dite` structure for `dif_pos`/`dif_neg` rewriting.
-/
import Mathlib

namespace Erdos858

/-- A concrete parent map `piFn`, defined as the maximum proper `⪯`-ancestor
(or 0 for n ≤ 1), satisfying exactly the three structural axioms used
abstractly throughout the §3 frontier-sweep theorems. -/
theorem concrete_pi_axioms :
    let piFn : ℕ → ℕ := fun n =>
      if h : n ≤ 1 then 0
      else
        if hS : (@Finset.filter ℕ (fun a => ∃ t : ℕ, n = a * t ∧ ∀ p : ℕ, Nat.Prime p → p ∣ t → a < p) (Classical.decPred _) (Finset.range n)).Nonempty
        then (@Finset.filter ℕ (fun a => ∃ t : ℕ, n = a * t ∧ ∀ p : ℕ, Nat.Prime p → p ∣ t → a < p) (Classical.decPred _) (Finset.range n)).max' hS
        else 0
    piFn 1 = 0 ∧ (∀ n : ℕ, 2 ≤ n → 1 ≤ piFn n ∧ piFn n < n) ∧
      (∀ z m : ℕ, z < m → (∃ t : ℕ, m = z * t ∧ ∀ p : ℕ, Nat.Prime p → p ∣ t → z < p) → z ≤ piFn m) := by
  refine ⟨?_, ?_, ?_⟩
  · dsimp only
    rw [dif_pos (le_refl 1)]
  · intro n hn
    have hone : ∃ t : ℕ, n = 1 * t ∧ ∀ p : ℕ, Nat.Prime p → p ∣ t → 1 < p := by
      refine ⟨n, (one_mul n).symm, ?_⟩
      intro p hp _
      have := hp.two_le
      omega
    have hSne : (@Finset.filter ℕ (fun a => ∃ t : ℕ, n = a * t ∧ ∀ p : ℕ, Nat.Prime p → p ∣ t → a < p) (Classical.decPred _) (Finset.range n)).Nonempty := by
      refine ⟨1, ?_⟩
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hone⟩
    have heq : (if h : n ≤ 1 then (0:ℕ) else if hS : (@Finset.filter ℕ (fun a => ∃ t : ℕ, n = a * t ∧ ∀ p : ℕ, Nat.Prime p → p ∣ t → a < p) (Classical.decPred _) (Finset.range n)).Nonempty then (@Finset.filter ℕ (fun a => ∃ t : ℕ, n = a * t ∧ ∀ p : ℕ, Nat.Prime p → p ∣ t → a < p) (Classical.decPred _) (Finset.range n)).max' hS else 0) = (@Finset.filter ℕ (fun a => ∃ t : ℕ, n = a * t ∧ ∀ p : ℕ, Nat.Prime p → p ∣ t → a < p) (Classical.decPred _) (Finset.range n)).max' hSne := by
      rw [dif_neg (by omega), dif_pos hSne]
    dsimp only
    rw [heq]
    refine ⟨?_, ?_⟩
    · have h1mem : (1:ℕ) ∈ (@Finset.filter ℕ (fun a => ∃ t : ℕ, n = a * t ∧ ∀ p : ℕ, Nat.Prime p → p ∣ t → a < p) (Classical.decPred _) (Finset.range n)) := by
        simp only [Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, hone⟩
      exact Finset.le_max' _ 1 h1mem
    · have hmem : (@Finset.filter ℕ (fun a => ∃ t : ℕ, n = a * t ∧ ∀ p : ℕ, Nat.Prime p → p ∣ t → a < p) (Classical.decPred _) (Finset.range n)).max' hSne ∈ (@Finset.filter ℕ (fun a => ∃ t : ℕ, n = a * t ∧ ∀ p : ℕ, Nat.Prime p → p ∣ t → a < p) (Classical.decPred _) (Finset.range n)) := Finset.max'_mem _ hSne
      simp only [Finset.mem_filter, Finset.mem_range] at hmem
      exact hmem.1
  · intro z m hzm hpre
    have hzpos : 1 ≤ z := by
      rcases Nat.eq_zero_or_pos z with hz0 | hzpos
      · exfalso
        obtain ⟨t, ht, _⟩ := hpre
        rw [hz0, Nat.zero_mul] at ht
        omega
      · exact hzpos
    have hm2 : 2 ≤ m := by omega
    have hone : ∃ t : ℕ, m = 1 * t ∧ ∀ p : ℕ, Nat.Prime p → p ∣ t → 1 < p := by
      refine ⟨m, (one_mul m).symm, ?_⟩
      intro p hp _
      have := hp.two_le
      omega
    have hSne : (@Finset.filter ℕ (fun a => ∃ t : ℕ, m = a * t ∧ ∀ p : ℕ, Nat.Prime p → p ∣ t → a < p) (Classical.decPred _) (Finset.range m)).Nonempty := by
      refine ⟨1, ?_⟩
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hone⟩
    have heq : (if h : m ≤ 1 then (0:ℕ) else if hS : (@Finset.filter ℕ (fun a => ∃ t : ℕ, m = a * t ∧ ∀ p : ℕ, Nat.Prime p → p ∣ t → a < p) (Classical.decPred _) (Finset.range m)).Nonempty then (@Finset.filter ℕ (fun a => ∃ t : ℕ, m = a * t ∧ ∀ p : ℕ, Nat.Prime p → p ∣ t → a < p) (Classical.decPred _) (Finset.range m)).max' hS else 0) = (@Finset.filter ℕ (fun a => ∃ t : ℕ, m = a * t ∧ ∀ p : ℕ, Nat.Prime p → p ∣ t → a < p) (Classical.decPred _) (Finset.range m)).max' hSne := by
      rw [dif_neg (by omega), dif_pos hSne]
    dsimp only
    rw [heq]
    have hzmem : z ∈ (@Finset.filter ℕ (fun a => ∃ t : ℕ, m = a * t ∧ ∀ p : ℕ, Nat.Prime p → p ∣ t → a < p) (Classical.decPred _) (Finset.range m)) := by
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨hzm, hpre⟩
    exact Finset.le_max' _ z hzmem

end Erdos858
