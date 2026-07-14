-- Helper theorems for lower bound rigidity
-- These will be submitted as module_items

-- squarefree_of_dvd
-- sqfree_product_lemma
-- root_theorem (main)

-- The proof structure:
-- 1. Factorization parity: a.fact + b.fact + c.fact + d.fact = 2 * s.fact (even)
-- 2. For each prime p, balance: a.fact p + d.fact p = b.fact p + c.fact p
-- 3. If balance fails (bad split):
--    Case 1 (ad=2, bc=0): p|a,d, ¬p|b,c → contradiction via ordering
--    Case 2 (ad=0, bc=2): p|b,c, ¬p|a,d → contradiction via ordering (symmetric to Case 1)
-- 4. Nat.eq_of_factorization_eq gives a*d = b*c

-- Key API:
-- Squarefree.ne_zero : Squarefree n → n ≠ 0
-- Nat.prime_dvd_prime_iff_eq : (hp : Nat.Prime p) (hq : Nat.Prime q) → p ∣ q ↔ p = q (use .symm for a = p)
-- padicValNat_dvd_iff : [Fact p.Prime] → ∀ n, p^n ∣ a ↔ a = 0 ∨ n ≤ padicValNat p a
-- Nat.factorization_def : (hp : p.Prime) → n.factorization p = padicValNat p n
-- Nat.factorization_eq_zero_of_not_prime : ¬p.Prime → n.factorization p = 0
-- Nat.Prime.pos : Nat.Prime p → 0 < p
-- Nat.eq_of_mul_eq_mul_left : 0 < c → c*a = c*b → a = b
-- ext + simp [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, two_mul] for finsupp equality
