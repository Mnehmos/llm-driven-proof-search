# Erdős #9 — infinitely many odd `n ≠ p + 2^k + 2^l` (Crocker 1971)

**Target:** `erdos_9.variants.infinite : Erdos9A.Infinite` (corpus, shipped `sorry`)
where `Erdos9A = {n | Odd n ∧ ¬ ∃ p k l, p.Prime ∧ n = p + 2^k + 2^l}`.

**Status: IN PROGRESS — large multi-part covering construction, NOT a fill.**
Assessed 2026-07-07 against Hao Pan, *On the integers not of the form p+2^a+2^b*
(arXiv:0905.3809) and Crocker, *Pacific J. Math.* 36 (1971) 103–107.

## Banked (kernel-verified) — `lean-checker/LeanChecker/Erdos/Erdos9.lean`

- `odd_add_one_dvd_pow_add_one : Odd t → (a+1) ∣ (a^t + 1)`.
- `fermat_dvd_two_pow_add : Odd t → (2^(2^s)+1) ∣ (2^a + 2^(a + 2^s·t))`
  — the **a≠b key lemma**: if `v₂(b−a) = s` then the Fermat number `F_s = 2^(2^s)+1`
  divides `2^a + 2^b`, so `p = n − 2^a − 2^b ≡ n (mod F_s)`.

## The construction (from Pan §2 / Crocker)

Split a hypothetical `n = p + 2^a + 2^b` (`0 ≤ a ≤ b`, `p` prime) into:

- **Case a ≠ b.** `b − a = 2^s·t`, `t` odd, `0 ≤ s < m` (bounded because
  `a,b ≤ log₂ n`). By `fermat_dvd_two_pow_add`, `F_s ∣ 2^a+2^b`. Let `γ_s` be the
  smallest prime factor of `F_s`. If `n ≡ 0 (mod γ_s)` then `γ_s ∣ p`, forcing
  `p = γ_s`. Need `γ_s` distinct (they are: Fermat numbers are pairwise coprime)
  so CRT can set `n ≡ 0 mod ∏γ_s`.
- **Case a = b.** Then `n = p + 2^(a+1)`, i.e. `p = n − 2^(a+1)` is a prime that is
  `n` minus a power of 2. This is exactly **Erdős's classical covering** [Er50]:
  every `n ≡ 7629217 (mod 11184810 = 2·3·5·7·13·17·241)` has `n − 2^c` divisible
  by one of `{3,5,7,13,17,241}` for all `c` (orders of 2 cover all residues mod 24),
  hence composite. Formalizable like #1113 (pure `decide` covering data).

## Remaining obligations (the hard part)

1. **a=b Erdős covering** as a standalone lemma: `n ≡ 7629217 (mod 11184810) →
   ∀ c ≥ 1, ¬ (n − 2^c).Prime` (via one of the 6 covering primes dividing it).
   ~#1113-scale; compute residue table in python, then `Nat.ModEq`/`decide`.
2. **Fermat smallest-prime-factors** `γ_k`: distinctness (Fermat numbers pairwise
   coprime — check Mathlib `Nat.coprime_fermatNumber_fermatNumber`), and
   `γ_k ≡ 1 (mod 2^(k+1))`, `γ_k > 2^(k+1)`.
3. **Existence per m (the delicate crux).** For each `m`, produce an actual odd `n`
   with `n ≡ 0 (mod γ_s)` for `s < m`, the Erdős residue mod `11184810`, and
   `n ≤ 2^(2^m)` (so every `a<b` has `v₂(b−a) < m`). Range (`n ≤ 2^(2^m)`) vs
   modulus (`2W ≈ 2^(2^m)`) is TIGHT — this is where Crocker/Pan work hardest; a
   clean "AP ⟹ infinite" (as in #1113) does NOT directly apply. Must also exclude
   the finitely many `p = γ_s` / `p ∣ W` edge representations.
4. **Assemble** `Erdos9A.Infinite`: injective map `m ↦ n_m`, each `n_m` odd and
   with every representation blocked.

## Honesty

Obligations 1–2 are #1113-scale and tractable. Obligation 3 (existence in range)
is the genuine research difficulty and is NOT a covering-system fill — Pan uses
Selberg sieve for the density version; the bare infinitude still needs the tight
range/modulus balance. This is a multi-session effort; **the Fermat key lemma is
banked as reusable progress.** Whether to invest in the full assembly is a user
call (large, uncertain).
