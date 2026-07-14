# Evidence Ledger — Erdős 888

## Phase 0: Setup (complete)
- [x] Source audit (Ulam paper, Erdős page, forum, Formal Conjectures, Ulam Lean draft)
- [x] Mathlib inventory (squarefree, factorization, asymptotics, IsTheta)
- [x] Mathlib gap map
- [x] Known traps documented (global kernel reduction invalid, exact finite max false)

## Phase 1: Foundations (in progress)

### Theorem 1: `squarefree_kernel_exists`
- **Statement**: `∀ a : ℕ, a ≠ 0 → ∃ (k s : ℕ), k^2 * s = a ∧ Squarefree s`
- **Status**: KERNEL VERIFIED
- **Problem**: `1939d126-761e-44ff-a831-f1a89b644e63`
- **Episode**: `ab540cf4-cc60-41ab-a6b4-d3f0f954ff39`
- **Proof technique**: Strong induction on `a`. If `Squarefree a`, take `k=1, s=a`. Otherwise, prime `p` with `p²|a` via `Nat.squarefree_iff_prime_squarefree`, write `a = p²·a'`, apply induction to `a'`.
- **Date**: 2026-07-14

### Theorem 2: `squarefree_kernel_unique`
- **Statement**: `∀ k₁ k₂ s₁ s₂ : ℕ, k₁^2 * s₁ = k₂^2 * s₂ → k₁ ≠ 0 → Squarefree s₁ → Squarefree s₂ → s₁ = s₂ ∧ k₁ = k₂`
- **Status**: KERNEL VERIFIED
- **Problem**: `b3c70e4f-5485-4fbe-990e-6a75b9a52e8d`
- **Episode**: `7541da74-d3f9-4587-a656-f9b2f2461387`
- **Proof technique**: Factorization parity. `Nat.factorization_mul` + `Nat.factorization_pow` gives `2·k₁.factorization + s₁.factorization = 2·k₂.factorization + s₂.factorization`. Mod 2 with `natFactorization_le_one` gives `s₁.factorization = s₂.factorization`, hence `s₁ = s₂`. Cancel `s₁` to get `k₁² = k₂²`, then `Nat.pow_left_injective (2 ≠ 0)` gives `k₁ = k₂`.
- **Date**: 2026-07-14

### Theorem 3: `fiber_admissible`
- **Statement**: `∀ (A : Finset ℕ) (k : ℕ), (∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A, a ≤ b → b ≤ c → c ≤ d → IsSquare (a * b * c * d) → a * d = b * c) → 0 < k → (∀ s ∈ ((A.filter (λ a => k^2 ∣ a)).image (λ a => a / k^2)), ∀ t ∈ ((A.filter (λ a => k^2 ∣ a)).image (λ a => a / k^2)), ∀ u ∈ ((A.filter (λ a => k^2 ∣ a)).image (λ a => a / k^2)), ∀ v ∈ ((A.filter (λ a => k^2 ∣ a)).image (λ a => a / k^2)), s ≤ t → t ≤ u → u ≤ v → IsSquare (s * t * u * v) → s * v = t * u)`
- **Status**: KERNEL VERIFIED
- **Problem**: `f0f330d8-3967-4c78-9420-a711a6edc8fb`
- **Episode**: `ec230b95-6c70-4781-a08d-a8ba2cf72c9c`
- **Proof technique**: For s,t,u,v in the fiber A_k = {a/k² | a∈A, k²|a}, their preimages a,b,c,d in A are ordered the same way (k² > 0 preserves order). The product a·b·c·d is a square because (k²)⁴ is a square and s·t·u·v is a square. By admissibility of A, a·d = b·c, and canceling k⁴ gives s·v = t·u.
- **Date**: 2026-07-14

### Theorem 4: `sqfree_product_lemma`
- **Statement**: `∀ x y : ℕ, Squarefree x → Squarefree y → IsSquare (x * y) → x = y`
- **Status**: KERNEL VERIFIED
- **Problem**: `6808365d-79c3-4eb9-b3cb-6673f43cc850`
- **Episode**: `91672cb4-2ef6-4211-9b8e-3e83983e3561`
- **Proof technique**: Factorization parity. For each prime p, v_p(x),v_p(y) ∈ {0,1} (squarefree). Since x·y is a square, v_p(x)+v_p(y) is even, so =0 or 2. Hence v_p(x)=v_p(y) for all p, so x=y by `Nat.eq_of_factorization_eq`.
- **Date**: 2026-07-14

---

## Theorem Inventory

| # | Name | Status | Verified | Date |
|---|------|--------|----------|------|
| 1 | `squarefree_kernel_exists` | KERNEL VERIFIED | `1939d126` | 2026-07-14 |
| 2 | `squarefree_kernel_unique` | KERNEL VERIFIED | `b3c70e4f` | 2026-07-14 |
| 3 | `fiber_admissible` | KERNEL VERIFIED | `f0f330d8` | 2026-07-14 |
| 4 | `sqfree_product_lemma` | KERNEL VERIFIED | `6808365d` | 2026-07-14 |
| 5 | `lower_bound_rigidity` | IN PROGRESS | `e726fca4` | 2026-07-14 |

### Theorem 5: `lower_bound_rigidity` (IN PROGRESS)
- **Statement**: `∀ a b c d : ℕ, Squarefree a → Squarefree b → Squarefree c → Squarefree d → (Nat.Prime a ∨ (∃ p q, p.Prime ∧ q.Prime ∧ p < q ∧ a = p * q)) → ... → a ≤ b → b ≤ c → c ≤ d → IsSquare (a * b * c * d) → a * d = b * c`
- **Status**: IN PROGRESS — 2 fixable bugs remain
- **Problem**: `e726fca4`
- **Proof technique**: Factorization parity. For each prime p, `a.fact p + b.fact p + c.fact p + d.fact p` is even (since `a*b*c*d = s²`). Since each is 0 or 1 (squarefree), sum is 0, 2, or 4. If sum is 0 or 4, balance `a.fact p + d.fact p = b.fact p + c.fact p` holds trivially. If sum is 2, the "bad split" case analysis derives a contradiction:
  - Bug 1: `fun h => by ...` doesn't expose `h` in nested `by` blocks — fix: use `intro h` with `Ne x 0`
  - Bug 2: `omega` can't prove `ad=2` since both `ad=2,bc=0` and `ad=0,bc=2` are consistent — fix: `by_cases` on `a.factorization p = 1` to split into two symmetric cases
- **Key API**: `Squarefree.ne_zero`, `Nat.prime_dvd_prime_iff_eq` (`.symm`), `padicValNat_dvd_iff` (needs `haveI : Fact p.Prime`), `Nat.Prime.pos`, `Nat.eq_of_mul_eq_mul_left` (needs `0 < c`), `ext`+`simp` for finsupp equality
- **Date**: 2026-07-14