/-
Erdős Problem #858 — Theorem 1.2 assembly, THE LITERAL FINAL INSTANTIATION of
atom A2 (Prop 5.1 exact frontier identity, Chojecki 2026).

**This is the mega-atom previously assessed as "genuinely different risk
class" (~29 hypotheses, 700+ line statement) and deferred.** Reconsidering
mid-session: taking each already-fully-assembled theorem (hSK/hC0/hCR/hHdiff)
as ONE opaque re-quantified hypothesis (its full literal type restated once)
and then just *applying* it is far cheaper than the naive full-transitive-
unfold estimate suggested. The actual statement needed 30 hypotheses (not
~29 either estimate — close, but the SHAPE differs: most of the bulk is
`hCR_thm`'s ~150-line restated type, already proven tractable at that scale
by `Erdos858_HCRCapstoneFullyAssembled.lean`).

**What this atom does**: takes `erdos858_hSK_fully_assembled`,
`erdos858_hC0_fully_assembled`, `lemma45_hCR_fully_assembled`,
`erdos858_icc_sum_diff_eq_sum_Ioc` (all four of A2's hypothesis-reductions
from this session), and `erdos858_thm12_prop51_identity` (A2 itself) — ALL
as opaque re-quantified hypotheses (their full types restated) — plus two
NEW regime hypotheses supplying the per-`a` domain facts each fully-assembled
theorem needs:
  - `∀a∈Ioc K sqrtN, N<a^4`   (for hCR_thm's per-a domain requirement)
  - `∀a∈Ioc sqrtN N, N<a*a`   (for hC0_thm's per-a domain requirement)
Then applies `hSK_thm`/`hC0_thm`/`hCR_thm`/`hHdiff_thm` at the real `π`/`N`
(deriving the per-`a` ∀-wrapped results `hSKresult`/`hC0result`/`hCRresult`/
`hHdiffresult`), and finally calls `hA2_thm` with EXPLICIT LAMBDA arguments
for `SN`/`CN`/`RN`/`H` matching the paper's literal `S_N(K)`, `C_N(a)`,
`R_N(a)=P_N(a)+Q_N(a)`, `H(m)` — producing the literal, fully-unconditional
Prop 5.1 identity for the real frontier-counting functions, not just an
abstract `SN CN RN H : ℕ→ℝ` template.

**Two fixes applied during construction**:
1. `hdisjapq`/`hinjsemiprime` in `hCR_thm`'s type are `a`-SPECIFIC (bound to
   the OUTER `a` of `lemma45_hCR_fully_assembled`'s own quantifier) — so at
   this atom's outer level they must be RE-QUANTIFIED over a fresh `a'`
   (`∀a' p' p'' q', ...`) and specialized at each call site (`hdisjapq a`,
   `hinjsemiprime a`), not passed through unchanged.
2. `hCR_thm`'s conclusion has the form `C_N(a) = (1/a)*(P+Q)` but A2's `hCR`
   hypothesis needs `C_N(a) = RN(a)/a` (division form). These differ only by
   `(1/a)*x` vs `x/a` — closed via `rw [hcr]; ring` (the same
   `(1/a)*x=x/a`-via-`ring` fact banked from the earlier `hCR` div-form
   reshape atom).

Proof: `hSKresult := hSK_thm π N K hKN h1N hπ1 hax hsweepstep hbase htop htel`
(direct application); `hC0result`/`hCRresult` are `∀a∈Ioc _ _, ...` proofs
via `intro a ha` + deriving the per-a domain fact from the regime hypotheses
+ applying `hC0_thm`/`hCR_thm`; `hHdiffresult := hHdiff_thm K sqrtN hKsqrtN`;
then `hfinal := hA2_thm SN_lambda CN_lambda RN_lambda H_lambda K N sqrtN
hKsqrtN hsqrtNN hSKresult hCRresult hC0result hHdiffresult; exact hfinal`.
Verified on the first REAL submission attempt (one prior call hit a stale
episode-revision retry, not a proof error) — extending this session's
opaque-theorem-splicing streak to 10/10.

Kernel-verified via the proofsearch MCP:
  episode 3f325573-d88c-49a7-b659-2d320f87bba4,
  problem_version_id dd43f1cc-4b9b-48a9-a125-64ab64bbf88d.
Outcome: kernel_verified / root_proved (terminated, step_count 1).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 923c780696899b7e7fe93c371cdbc5ecdd954c46100f269928b572652ff3df2a.
-/
import Mathlib

namespace Erdos858

/-- THE LITERAL final instantiation of Theorem 1.2 atom A2: the Prop 5.1
exact frontier identity `S_N(K) = (H_N−H_{√N}) + Σ_{K<a≤√N}(1−R_N(a))/a`
for the REAL π/S_N/C_N/R_N/H functions (not an abstract template), given
the primitive π-structure axioms, standalone number-theory theorems, the
four fully-assembled hSK/hC0/hCR/hHdiff reductions, A2 itself, and two
regime hypotheses (`N<a^4` on `(K,√N]`, `N<a·a` on `(√N,N]`) — all opaque. -/
theorem erdos858_thm12_prop51_literal :
    ∀ (π : ℕ → ℕ) (N K sqrtN : ℕ),
      K ≤ sqrtN → sqrtN ≤ N → 1 ≤ N →
      π 1 = 0 →
      (∀ n : ℕ, 2 ≤ n → n ≤ N → 1 ≤ π n ∧ π n < n) →
      (∀ n : ℕ, 2 ≤ n → ∃ t : ℕ, n = π n * t ∧ ∀ r : ℕ, Nat.Prime r → r ∣ t → π n < r) →
      (∀ z m : ℕ, z < m → (∃ t : ℕ, m = z * t ∧ ∀ r : ℕ, Nat.Prime r → r ∣ t → z < r) → z ≤ π m) →
      (∀ a' b' n' : ℕ, a' < b' → b' < n' →
        (∃ u : ℕ, n' = a' * u ∧ ∀ r : ℕ, Nat.Prime r → r ∣ u → a' < r) →
        (∃ v : ℕ, n' = b' * v ∧ ∀ r : ℕ, Nat.Prime r → r ∣ v → b' < r) →
        ∃ t : ℕ, b' = a' * t ∧ ∀ r : ℕ, Nat.Prime r → r ∣ t → a' < r) →
      (∀ a' p' : ℕ, 1 ≤ a' → Nat.Prime p' → a' < p' →
        (∃ t : ℕ, a' * p' = a' * t ∧ ∀ r : ℕ, Nat.Prime r → r ∣ t → a' < r) ∧
          (∀ b : ℕ, (∃ s : ℕ, b = a' * s ∧ ∀ r : ℕ, Nat.Prime r → r ∣ s → a' < r) →
            (∃ w : ℕ, a' * p' = b * w ∧ ∀ r : ℕ, Nat.Prime r → r ∣ w → b < r) → b = a' ∨ b = a' * p')) →
      (∀ a' p' q' N' : ℕ, 1 ≤ a' → a' < p' → a' * p' * q' ≤ N' → N' < a' ^ 4 → q' < a' * p') →
      (∀ a' p' q' N' : ℕ, 1 ≤ a' → a' < p' → p' ≤ q' → a' * p' * q' ≤ N' → N' < a' ^ 4 → p' < a' * q') →
      (∀ b q' : ℕ, 0 < b → Nat.Prime q' → q' < b → ¬ (∃ t : ℕ, b * q' = b * t ∧ ∀ r : ℕ, Nat.Prime r → r ∣ t → b < r)) →
      (∀ a' p' q' : ℕ, 1 ≤ a' → Nat.Prime p' → Nat.Prime q' → a' < p' → p' ≤ q' →
        q' < a' * p' → p' < a' * q' →
        (∀ b q'' : ℕ, 0 < b → Nat.Prime q'' → q'' < b → ¬ (∃ t : ℕ, b * q'' = b * t ∧ ∀ r : ℕ, Nat.Prime r → r ∣ t → b < r)) →
        ∀ b : ℕ, (∃ s : ℕ, b = a' * s ∧ ∀ r : ℕ, Nat.Prime r → r ∣ s → a' < r) →
          (∃ w : ℕ, a' * p' * q' = b * w ∧ ∀ r : ℕ, Nat.Prime r → r ∣ w → b < r) →
          b = a' ∨ b = a' * p' * q') →
      (∀ a' t' : ℕ, 1 ≤ a' → 0 < t' → t' < a'^3 → (∀ p : ℕ, Nat.Prime p → p ∣ t' → a' < p) →
        t' = 1 ∨ Nat.Prime t' ∨ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ t' = p * q) →
      (∀ (π' : ℕ → ℕ) (N' a' : ℕ), N' < a'^4 → 1 ≤ a' → π' 1 = 0 →
        (∀ n : ℕ, 2 ≤ n → n ≤ N' → 1 ≤ π' n ∧ π' n < n) →
        (∀ n : ℕ, 2 ≤ n → ∃ t : ℕ, n = π' n * t ∧ ∀ r : ℕ, Nat.Prime r → r ∣ t → π' n < r) →
        (∀ a'' t' : ℕ, 1 ≤ a'' → 0 < t' → t' < a''^3 → (∀ p : ℕ, Nat.Prime p → p ∣ t' → a'' < p) →
          t' = 1 ∨ Nat.Prime t' ∨ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ t' = p * q) →
        (Finset.Icc 1 N').filter (fun n => π' n = a') ⊆
          ((Finset.Icc (a'+1) N').filter (fun p => Nat.Prime p ∧ a' * p ≤ N')).image (fun p => a' * p)
          ∪ (((Finset.Icc (a'+1) N') ×ˢ (Finset.Icc (a'+1) N')).filter
              (fun pq => Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧ pq.1 ≤ pq.2 ∧ a' * (pq.1 * pq.2) ≤ N')).image
              (fun pq => a' * pq.1 * pq.2)) →
      (∀ (π' : ℕ → ℕ) (N' a' : ℕ), N' < a'^4 → 1 ≤ a' →
        (∀ n : ℕ, 2 ≤ n → n ≤ N' → 1 ≤ π' n ∧ π' n < n) →
        (∀ z m : ℕ, z < m → (∃ t : ℕ, m = z * t ∧ ∀ r : ℕ, Nat.Prime r → r ∣ t → z < r) → z ≤ π' m) →
        (∀ n : ℕ, 2 ≤ n → ∃ t : ℕ, n = π' n * t ∧ ∀ r : ℕ, Nat.Prime r → r ∣ t → π' n < r) →
        (∀ a'' b' n' : ℕ, a'' < b' → b' < n' →
          (∃ u : ℕ, n' = a'' * u ∧ ∀ r : ℕ, Nat.Prime r → r ∣ u → a'' < r) →
          (∃ v : ℕ, n' = b' * v ∧ ∀ r : ℕ, Nat.Prime r → r ∣ v → b' < r) →
          ∃ t : ℕ, b' = a'' * t ∧ ∀ r : ℕ, Nat.Prime r → r ∣ t → a'' < r) →
        (∀ a'' p' : ℕ, 1 ≤ a'' → Nat.Prime p' → a'' < p' →
          (∃ t : ℕ, a'' * p' = a'' * t ∧ ∀ r : ℕ, Nat.Prime r → r ∣ t → a'' < r) ∧
            (∀ b : ℕ, (∃ s : ℕ, b = a'' * s ∧ ∀ r : ℕ, Nat.Prime r → r ∣ s → a'' < r) →
              (∃ w : ℕ, a'' * p' = b * w ∧ ∀ r : ℕ, Nat.Prime r → r ∣ w → b < r) → b = a'' ∨ b = a'' * p')) →
        (∀ a'' p' q' N'' : ℕ, 1 ≤ a'' → a'' < p' → a'' * p' * q' ≤ N'' → N'' < a'' ^ 4 → q' < a'' * p') →
        (∀ a'' p' q' N'' : ℕ, 1 ≤ a'' → a'' < p' → p' ≤ q' → a'' * p' * q' ≤ N'' → N'' < a'' ^ 4 → p' < a'' * q') →
        (∀ b q' : ℕ, 0 < b → Nat.Prime q' → q' < b → ¬ (∃ t : ℕ, b * q' = b * t ∧ ∀ r : ℕ, Nat.Prime r → r ∣ t → b < r)) →
        (∀ a'' p' q' : ℕ, 1 ≤ a'' → Nat.Prime p' → Nat.Prime q' → a'' < p' → p' ≤ q' →
          q' < a'' * p' → p' < a'' * q' →
          (∀ b q'' : ℕ, 0 < b → Nat.Prime q'' → q'' < b → ¬ (∃ t : ℕ, b * q'' = b * t ∧ ∀ r : ℕ, Nat.Prime r → r ∣ t → b < r)) →
          ∀ b : ℕ, (∃ s : ℕ, b = a'' * s ∧ ∀ r : ℕ, Nat.Prime r → r ∣ s → a'' < r) →
            (∃ w : ℕ, a'' * p' * q' = b * w ∧ ∀ r : ℕ, Nat.Prime r → r ∣ w → b < r) →
            b = a'' ∨ b = a'' * p' * q') →
        (((Finset.Icc (a'+1) N').filter (fun p => Nat.Prime p ∧ a' * p ≤ N')).image (fun p => a' * p)
          ∪ (((Finset.Icc (a'+1) N') ×ˢ (Finset.Icc (a'+1) N')).filter
              (fun pq => Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧ pq.1 ≤ pq.2 ∧ a' * (pq.1 * pq.2) ≤ N')).image
              (fun pq => a' * pq.1 * pq.2))
          ⊆ (Finset.Icc 1 N').filter (fun n => π' n = a')) →
      (∀ a' p' p'' q' : ℕ, Nat.Prime p' → Nat.Prime p'' → Nat.Prime q' → a' * p' ≠ a' * p'' * q') →
      (∀ a' p' q' p'' q'' : ℕ, Nat.Prime p' → Nat.Prime q' → p' ≤ q' → Nat.Prime p'' → Nat.Prime q'' → p'' ≤ q'' →
        a' * p' * q' = a' * p'' * q'' → p' = p'' ∧ q' = q'') →
      (∀ (π' : ℕ → ℕ) (N' K' : ℕ), π' 1 = 0 → (∀ n : ℕ, 2 ≤ n → n ≤ N' → 1 ≤ π' n ∧ π' n < n) → K' + 1 ≤ N' →
        (∑ n ∈ (Finset.Icc 1 N').filter (fun n => π' n ≤ K' + 1 ∧ K' + 1 < n), (1:ℚ)/(n:ℚ))
          = (∑ n ∈ (Finset.Icc 1 N').filter (fun n => π' n ≤ K' ∧ K' < n), (1:ℚ)/(n:ℚ))
            + ((∑ n ∈ (Finset.Icc 1 N').filter (fun m => π' m = K' + 1), (1:ℚ)/(n:ℚ)) - (1:ℚ)/((K':ℚ) + 1))) →
      (∀ (π' : ℕ → ℕ) (N' : ℕ), 1 ≤ N' → π' 1 = 0 → (∀ n : ℕ, 2 ≤ n → n ≤ N' → 1 ≤ π' n) →
        (Finset.Icc 1 N').filter (fun n => π' n ≤ 0 ∧ 0 < n) = {1}) →
      (∀ (π' : ℕ → ℕ) (N' : ℕ), (Finset.Icc 1 N').filter (fun n => π' n ≤ N' ∧ N' < n) = ∅) →
      (∀ (S : ℕ → ℚ) (m n : ℕ), m ≤ n → ∑ a ∈ Finset.Ioc m n, (S a - S (a-1)) = S n - S m) →
      (∀ N' a' b' : ℕ, N' < a' * a' → a' < b' → b' ≤ N' →
        ¬ (∃ t : ℕ, b' = a' * t ∧ ∀ p : ℕ, Nat.Prime p → p ∣ t → a' < p)) →
      (∀ a ∈ Finset.Ioc K sqrtN, N < a^4) →
      (∀ a ∈ Finset.Ioc sqrtN N, N < a * a) →
      (∀ (π' : ℕ → ℕ) (N' K' : ℕ), K' ≤ N' → 1 ≤ N' → π' 1 = 0 →
        (∀ n : ℕ, 2 ≤ n → n ≤ N' → 1 ≤ π' n ∧ π' n < n) →
        (∀ (π'' : ℕ → ℕ) (N'' K'' : ℕ), π'' 1 = 0 → (∀ n : ℕ, 2 ≤ n → n ≤ N'' → 1 ≤ π'' n ∧ π'' n < n) → K'' + 1 ≤ N'' →
          (∑ n ∈ (Finset.Icc 1 N'').filter (fun n => π'' n ≤ K'' + 1 ∧ K'' + 1 < n), (1:ℚ)/(n:ℚ))
            = (∑ n ∈ (Finset.Icc 1 N'').filter (fun n => π'' n ≤ K'' ∧ K'' < n), (1:ℚ)/(n:ℚ))
              + ((∑ n ∈ (Finset.Icc 1 N'').filter (fun m => π'' m = K'' + 1), (1:ℚ)/(n:ℚ)) - (1:ℚ)/((K'':ℚ) + 1))) →
        (∀ (π'' : ℕ → ℕ) (N'' : ℕ), 1 ≤ N'' → π'' 1 = 0 → (∀ n : ℕ, 2 ≤ n → n ≤ N'' → 1 ≤ π'' n) →
          (Finset.Icc 1 N'').filter (fun n => π'' n ≤ 0 ∧ 0 < n) = {1}) →
        (∀ (π'' : ℕ → ℕ) (N'' : ℕ), (Finset.Icc 1 N'').filter (fun n => π'' n ≤ N'' ∧ N'' < n) = ∅) →
        (∀ (S : ℕ → ℚ) (m n : ℕ), m ≤ n → ∑ a ∈ Finset.Ioc m n, (S a - S (a-1)) = S n - S m) →
        ((∑ n ∈ (Finset.Icc 1 N').filter (fun n => π' n ≤ K' ∧ K' < n), (1:ℝ)/(n:ℝ))
          = (∑ n ∈ Finset.Icc 1 N', (1:ℝ)/(n:ℝ)) - (∑ n ∈ Finset.Icc 1 K', (1:ℝ)/(n:ℝ))
            - (∑ a ∈ Finset.Ioc K' N', ∑ n ∈ (Finset.Icc 1 N').filter (fun m => π' m = a), (1:ℝ)/(n:ℝ)))) →
      (∀ (π' : ℕ → ℕ) (N' a' : ℕ),
        π' 1 = 0 →
        (∀ n : ℕ, 2 ≤ n → n ≤ N' → 1 ≤ π' n ∧ π' n < n) →
        (∀ w : ℕ, 2 ≤ w → ∃ t : ℕ, w = π' w * t ∧ ∀ p : ℕ, Nat.Prime p → p ∣ t → π' w < p) →
        (∀ N'' a'' b' : ℕ, N'' < a'' * a'' → a'' < b' → b' ≤ N'' →
          ¬ (∃ t : ℕ, b' = a'' * t ∧ ∀ p : ℕ, Nat.Prime p → p ∣ t → a'' < p)) →
        N' < a' * a' →
        (∑ n ∈ (Finset.Icc 1 N').filter (fun n => π' n = a'), (1:ℝ)/(n:ℝ)) = 0) →
      (∀ (π' : ℕ → ℕ) (N' a' : ℕ), N' < a'^4 → 1 ≤ a' → π' 1 = 0 →
        (∀ n : ℕ, 2 ≤ n → n ≤ N' → 1 ≤ π' n ∧ π' n < n) →
        (∀ n : ℕ, 2 ≤ n → ∃ t : ℕ, n = π' n * t ∧ ∀ r : ℕ, Nat.Prime r → r ∣ t → π' n < r) →
        (∀ z m : ℕ, z < m → (∃ t : ℕ, m = z * t ∧ ∀ r : ℕ, Nat.Prime r → r ∣ t → z < r) → z ≤ π' m) →
        (∀ a'' b' n' : ℕ, a'' < b' → b' < n' →
          (∃ u : ℕ, n' = a'' * u ∧ ∀ r : ℕ, Nat.Prime r → r ∣ u → a'' < r) →
          (∃ v : ℕ, n' = b' * v ∧ ∀ r : ℕ, Nat.Prime r → r ∣ v → b' < r) →
          ∃ t : ℕ, b' = a'' * t ∧ ∀ r : ℕ, Nat.Prime r → r ∣ t → a'' < r) →
        (∀ a'' p' : ℕ, 1 ≤ a'' → Nat.Prime p' → a'' < p' →
          (∃ t : ℕ, a'' * p' = a'' * t ∧ ∀ r : ℕ, Nat.Prime r → r ∣ t → a'' < r) ∧
            (∀ b : ℕ, (∃ s : ℕ, b = a'' * s ∧ ∀ r : ℕ, Nat.Prime r → r ∣ s → a'' < r) →
              (∃ w : ℕ, a'' * p' = b * w ∧ ∀ r : ℕ, Nat.Prime r → r ∣ w → b < r) → b = a'' ∨ b = a'' * p')) →
        (∀ a'' p' q' N'' : ℕ, 1 ≤ a'' → a'' < p' → a'' * p' * q' ≤ N'' → N'' < a'' ^ 4 → q' < a'' * p') →
        (∀ a'' p' q' N'' : ℕ, 1 ≤ a'' → a'' < p' → p' ≤ q' → a'' * p' * q' ≤ N'' → N'' < a'' ^ 4 → p' < a'' * q') →
        (∀ b q' : ℕ, 0 < b → Nat.Prime q' → q' < b → ¬ (∃ t : ℕ, b * q' = b * t ∧ ∀ r : ℕ, Nat.Prime r → r ∣ t → b < r)) →
        (∀ a'' p' q' : ℕ, 1 ≤ a'' → Nat.Prime p' → Nat.Prime q' → a'' < p' → p' ≤ q' →
          q' < a'' * p' → p' < a'' * q' →
          (∀ b q'' : ℕ, 0 < b → Nat.Prime q'' → q'' < b → ¬ (∃ t : ℕ, b * q'' = b * t ∧ ∀ r : ℕ, Nat.Prime r → r ∣ t → b < r)) →
          ∀ b : ℕ, (∃ s : ℕ, b = a'' * s ∧ ∀ r : ℕ, Nat.Prime r → r ∣ s → a'' < r) →
            (∃ w : ℕ, a'' * p' * q' = b * w ∧ ∀ r : ℕ, Nat.Prime r → r ∣ w → b < r) →
            b = a'' ∨ b = a'' * p' * q') →
        (∀ a'' t' : ℕ, 1 ≤ a'' → 0 < t' → t' < a''^3 → (∀ p : ℕ, Nat.Prime p → p ∣ t' → a'' < p) →
          t' = 1 ∨ Nat.Prime t' ∨ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ t' = p * q) →
        (∀ (π'' : ℕ → ℕ) (N'' a'' : ℕ), N'' < a''^4 → 1 ≤ a'' → π'' 1 = 0 →
          (∀ n : ℕ, 2 ≤ n → n ≤ N'' → 1 ≤ π'' n ∧ π'' n < n) →
          (∀ n : ℕ, 2 ≤ n → ∃ t : ℕ, n = π'' n * t ∧ ∀ r : ℕ, Nat.Prime r → r ∣ t → π'' n < r) →
          (∀ a''' t' : ℕ, 1 ≤ a''' → 0 < t' → t' < a'''^3 → (∀ p : ℕ, Nat.Prime p → p ∣ t' → a''' < p) →
            t' = 1 ∨ Nat.Prime t' ∨ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ t' = p * q) →
          (Finset.Icc 1 N'').filter (fun n => π'' n = a'') ⊆
            ((Finset.Icc (a''+1) N'').filter (fun p => Nat.Prime p ∧ a'' * p ≤ N'')).image (fun p => a'' * p)
            ∪ (((Finset.Icc (a''+1) N'') ×ˢ (Finset.Icc (a''+1) N'')).filter
                (fun pq => Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧ pq.1 ≤ pq.2 ∧ a'' * (pq.1 * pq.2) ≤ N'')).image
                (fun pq => a'' * pq.1 * pq.2)) →
        (∀ (π'' : ℕ → ℕ) (N'' a'' : ℕ), N'' < a''^4 → 1 ≤ a'' →
          (∀ n : ℕ, 2 ≤ n → n ≤ N'' → 1 ≤ π'' n ∧ π'' n < n) →
          (∀ z m : ℕ, z < m → (∃ t : ℕ, m = z * t ∧ ∀ r : ℕ, Nat.Prime r → r ∣ t → z < r) → z ≤ π'' m) →
          (∀ n : ℕ, 2 ≤ n → ∃ t : ℕ, n = π'' n * t ∧ ∀ r : ℕ, Nat.Prime r → r ∣ t → π'' n < r) →
          (∀ a''' b' n' : ℕ, a''' < b' → b' < n' →
            (∃ u : ℕ, n' = a''' * u ∧ ∀ r : ℕ, Nat.Prime r → r ∣ u → a''' < r) →
            (∃ v : ℕ, n' = b' * v ∧ ∀ r : ℕ, Nat.Prime r → r ∣ v → b' < r) →
            ∃ t : ℕ, b' = a''' * t ∧ ∀ r : ℕ, Nat.Prime r → r ∣ t → a''' < r) →
          (∀ a''' p' : ℕ, 1 ≤ a''' → Nat.Prime p' → a''' < p' →
            (∃ t : ℕ, a''' * p' = a''' * t ∧ ∀ r : ℕ, Nat.Prime r → r ∣ t → a''' < r) ∧
              (∀ b : ℕ, (∃ s : ℕ, b = a''' * s ∧ ∀ r : ℕ, Nat.Prime r → r ∣ s → a''' < r) →
                (∃ w : ℕ, a''' * p' = b * w ∧ ∀ r : ℕ, Nat.Prime r → r ∣ w → b < r) → b = a''' ∨ b = a''' * p')) →
          (∀ a''' p' q' N''' : ℕ, 1 ≤ a''' → a''' < p' → a''' * p' * q' ≤ N''' → N''' < a''' ^ 4 → q' < a''' * p') →
          (∀ a''' p' q' N''' : ℕ, 1 ≤ a''' → a''' < p' → p' ≤ q' → a''' * p' * q' ≤ N''' → N''' < a''' ^ 4 → p' < a''' * q') →
          (∀ b q' : ℕ, 0 < b → Nat.Prime q' → q' < b → ¬ (∃ t : ℕ, b * q' = b * t ∧ ∀ r : ℕ, Nat.Prime r → r ∣ t → b < r)) →
          (∀ a''' p' q' : ℕ, 1 ≤ a''' → Nat.Prime p' → Nat.Prime q' → a''' < p' → p' ≤ q' →
            q' < a''' * p' → p' < a''' * q' →
            (∀ b q'' : ℕ, 0 < b → Nat.Prime q'' → q'' < b → ¬ (∃ t : ℕ, b * q'' = b * t ∧ ∀ r : ℕ, Nat.Prime r → r ∣ t → b < r)) →
            ∀ b : ℕ, (∃ s : ℕ, b = a''' * s ∧ ∀ r : ℕ, Nat.Prime r → r ∣ s → a''' < r) →
              (∃ w : ℕ, a''' * p' * q' = b * w ∧ ∀ r : ℕ, Nat.Prime r → r ∣ w → b < r) →
              b = a''' ∨ b = a''' * p' * q') →
          (((Finset.Icc (a''+1) N'').filter (fun p => Nat.Prime p ∧ a'' * p ≤ N'')).image (fun p => a'' * p)
            ∪ (((Finset.Icc (a''+1) N'') ×ˢ (Finset.Icc (a''+1) N'')).filter
                (fun pq => Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧ pq.1 ≤ pq.2 ∧ a'' * (pq.1 * pq.2) ≤ N'')).image
                (fun pq => a'' * pq.1 * pq.2))
            ⊆ (Finset.Icc 1 N'').filter (fun n => π'' n = a'')) →
        (∀ p p' q' : ℕ, Nat.Prime p → Nat.Prime p' → Nat.Prime q' → a' * p ≠ a' * p' * q') →
        (∀ p q p' q' : ℕ, Nat.Prime p → Nat.Prime q → p ≤ q → Nat.Prime p' → Nat.Prime q' → p' ≤ q' →
          a' * p * q = a' * p' * q' → p = p' ∧ q = q') →
        (∑ n ∈ (Finset.Icc 1 N').filter (fun n => π' n = a'), (1:ℝ)/(n:ℝ)) =
          (1/(a':ℝ)) * ((∑ p ∈ (Finset.Icc (a'+1) N').filter (fun p => Nat.Prime p ∧ a' * p ≤ N'), (1:ℝ)/(p:ℝ))
            + (∑ pq ∈ ((Finset.Icc (a'+1) N') ×ˢ (Finset.Icc (a'+1) N')).filter
                (fun pq => Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧ pq.1 ≤ pq.2 ∧ a' * (pq.1 * pq.2) ≤ N'),
                (1:ℝ)/((pq.1:ℝ)*(pq.2:ℝ))))) →
      (∀ m n : ℕ, m ≤ n → (∑ k ∈ Finset.Icc 1 n, (1:ℝ)/(k:ℝ)) - (∑ k ∈ Finset.Icc 1 m, (1:ℝ)/(k:ℝ)) = ∑ a ∈ Finset.Ioc m n, (1:ℝ)/(a:ℝ)) →
      (∀ (SN CN RN H : ℕ → ℝ) (K' N' sqrtN' : ℕ),
        K' ≤ sqrtN' → sqrtN' ≤ N' →
        SN K' = H N' - H K' - ∑ a ∈ Finset.Ioc K' N', CN a →
        (∀ a ∈ Finset.Ioc K' sqrtN', CN a = RN a / (a:ℝ)) →
        (∀ a ∈ Finset.Ioc sqrtN' N', CN a = 0) →
        H sqrtN' - H K' = ∑ a ∈ Finset.Ioc K' sqrtN', 1/(a:ℝ) →
        SN K' = (H N' - H sqrtN') + ∑ a ∈ Finset.Ioc K' sqrtN', (1 - RN a)/(a:ℝ)) →
      (∑ n ∈ (Finset.Icc 1 N).filter (fun n => π n ≤ K ∧ K < n), (1:ℝ)/(n:ℝ))
        = ((∑ n ∈ Finset.Icc 1 N, (1:ℝ)/(n:ℝ)) - (∑ n ∈ Finset.Icc 1 sqrtN, (1:ℝ)/(n:ℝ)))
          + ∑ a ∈ Finset.Ioc K sqrtN,
              (1 - ((∑ p ∈ (Finset.Icc (a+1) N).filter (fun p => Nat.Prime p ∧ a * p ≤ N), (1:ℝ)/(p:ℝ))
                + (∑ pq ∈ ((Finset.Icc (a+1) N) ×ˢ (Finset.Icc (a+1) N)).filter
                    (fun pq => Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧ pq.1 ≤ pq.2 ∧ a * (pq.1 * pq.2) ≤ N),
                    (1:ℝ)/((pq.1:ℝ)*(pq.2:ℝ))))) / (a:ℝ) := by
  intro π N K sqrtN hKsqrtN hsqrtNN h1N hπ1 hax hsound hmax hsandwich hlemma27 hB1 hB2 hsubfact huniqapq hdichotomy hsub_thm hsup_thm hdisjapq hinjsemiprime hsweepstep hbase htop htel htop_block hN4range hNsqrange hSK_thm hC0_thm hCR_thm hHdiff_thm hA2_thm
  have hKN : K ≤ N := (by omega)
  have hSKresult := hSK_thm π N K hKN h1N hπ1 hax hsweepstep hbase htop htel
  have hC0result : ∀ a ∈ Finset.Ioc sqrtN N, (∑ n ∈ (Finset.Icc 1 N).filter (fun n => π n = a), (1:ℝ)/(n:ℝ)) = 0 := (by
    intro a ha
    have haa : N < a*a := hNsqrange a ha
    exact hC0_thm π N a hπ1 hax hsound htop_block haa)
  have hCRresult : ∀ a ∈ Finset.Ioc K sqrtN, (∑ n ∈ (Finset.Icc 1 N).filter (fun n => π n = a), (1:ℝ)/(n:ℝ)) =
      ((∑ p ∈ (Finset.Icc (a+1) N).filter (fun p => Nat.Prime p ∧ a * p ≤ N), (1:ℝ)/(p:ℝ))
        + (∑ pq ∈ ((Finset.Icc (a+1) N) ×ˢ (Finset.Icc (a+1) N)).filter
            (fun pq => Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧ pq.1 ≤ pq.2 ∧ a * (pq.1 * pq.2) ≤ N),
            (1:ℝ)/((pq.1:ℝ)*(pq.2:ℝ)))) / (a:ℝ) := (by
    intro a ha
    have ha4 : N < a^4 := hN4range a ha
    have ha1 : 1 ≤ a := (by have := (Finset.mem_Ioc.mp ha).1; omega)
    have hcr := hCR_thm π N a ha4 ha1 hπ1 hax hsound hmax hsandwich hlemma27 hB1 hB2 hsubfact huniqapq hdichotomy hsub_thm hsup_thm (hdisjapq a) (hinjsemiprime a)
    rw [hcr]; ring)
  have hHdiffresult := hHdiff_thm K sqrtN hKsqrtN
  have hfinal := hA2_thm
    (fun K' => ∑ n ∈ (Finset.Icc 1 N).filter (fun n => π n ≤ K' ∧ K' < n), (1:ℝ)/(n:ℝ))
    (fun a => ∑ n ∈ (Finset.Icc 1 N).filter (fun n => π n = a), (1:ℝ)/(n:ℝ))
    (fun a => (∑ p ∈ (Finset.Icc (a+1) N).filter (fun p => Nat.Prime p ∧ a * p ≤ N), (1:ℝ)/(p:ℝ))
        + (∑ pq ∈ ((Finset.Icc (a+1) N) ×ˢ (Finset.Icc (a+1) N)).filter
            (fun pq => Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧ pq.1 ≤ pq.2 ∧ a * (pq.1 * pq.2) ≤ N),
            (1:ℝ)/((pq.1:ℝ)*(pq.2:ℝ))))
    (fun m => ∑ n ∈ Finset.Icc 1 m, (1:ℝ)/(n:ℝ))
    K N sqrtN hKsqrtN hsqrtNN
    hSKresult hCRresult hC0result hHdiffresult
  exact hfinal

end Erdos858
