import Mathlib

/-!
# Erdős #647 — Layer B/C bridge: the Selberg optimal weight's magnitude bound

Snapshot of the exact statement + proof term kernel-verified through the
tracked proof-search pipeline on 2026-07-14.

  problem_version_id  3e0b43d9-5c96-4620-b93c-abc520b2bcda
  episode_id          602b62ae-85e0-46d8-9f0c-44a1e68a1342
  root_statement_hash a3ff0a108a4db57bdbd5da8f5d04d0ca9b59e05303e324f6da7483a0476cb0d9
  outcome             kernel_verified (root_proved)
  import manifest     ["Mathlib.Tactic.Ring", "Mathlib.Tactic.NormNum", "Mathlib"]

Content: `erdos647_selberg_optimal_weight` constructs an explicit weight
`w(d)` (via Möbius inversion of `y_l := μ(l)·selbergTerms(l)/L`) achieving
the exact constrained minimum of the Selberg sieve's `mainSum`, but
supplies NO bound on `|w(d)|` itself. This theorem closes that gap:

  `|w(d)| ≤ selbergTerms(d)/ν(d)`  for every `d ∈ prodPrimes.divisors`.

This is the missing analytic ingredient flagged at the end of the prior
session: neither Mathlib's `SelbergSieve.lean` (confirmed by reading the
whole file) nor a pure Legendre/Möbius shortcut (confirmed to blow up
exponentially in `π(z)`) supplies this bound — it had to be derived from
scratch.

**Derivation** (worked by hand before formalizing, catching a sign error
in the process — see below). Write `w(d)·ν(d) = ∑_{l'∈D,d∣l'}
μ(l'/d)·y(l')`. Substitute `l'=d·e` (reindexing bijection `l'↦l'/d`,
`e↦d·e`, onto `(prodPrimes/d).divisors` — since `d∣prodPrimes` and
`prodPrimes` is squarefree, `d·e∣prodPrimes ↔ e∣(prodPrimes/d)`). Using
multiplicativity of `μ` and `selbergTerms` (valid since `d,e` are
automatically coprime — squarefree `d·e` forces `Coprime d e` via
`Nat.coprime_of_squarefree_mul`) and `μ(e)²=1` (squarefree `e`):

  `w(d)·ν(d) = ∑_e μ(e)·μ(d)μ(e)·selbergTerms(d)selbergTerms(e)/L
             = μ(d)·(selbergTerms(d)/L)·∑_e selbergTerms(e)`

Since `∑_{e∈(prodPrimes/d).divisors} selbergTerms(e)` is a sub-sum of
`L = ∑_{l∈D} selbergTerms(l)` over POSITIVE terms (divisors of
`prodPrimes/d` are a subset of `D`), it is `≤ L` (and `≥0`), giving
`|w(d)·ν(d)| ≤ |μ(d)|·(selbergTerms(d)/L)·L = selbergTerms(d)` (using
`|μ(d)|=1`), hence `|w(d)| ≤ selbergTerms(d)/ν(d)`.

**Sign-error catch (important self-correction, worth recording)**: an
earlier hand-derivation (recorded in the prior session's closing summary)
mistakenly concluded `0 ≤ w(d)` — treating `μ(l'/d)` and `μ(l')` as if
they contributed `μ(d)²` (always `+1`). Re-deriving carefully term-by-term
showed only ONE factor of `μ(d)` survives (from `μ(l')=μ(d·e)=μ(d)μ(e)`,
combined with the standalone `μ(l'/d)=μ(e)` — giving `μ(e)²·μ(d)`, not
`μ(d)²·μ(e)²`), so `w(d)` genuinely alternates sign with `μ(d)`. The
CORRECT, provable statement is the absolute-value bound, not `w(d)≥0`.
This is exactly the kind of statement-level error the Lean kernel does
NOT catch on its own (a wrong but internally-consistent formalization
would have compiled) — caught here by manual re-derivation before
formalizing, not by the prover.

Proof (Lean-level, beyond the math): the reindexing bijection uses
`Finset.sum_nbij'` (six components — forward/backward maps, four
membership/inverse obligations) on Finset-native `Finset.mem_filter`/
`Nat.mem_divisors` membership (NOT the `Set`-coerced form
`card_bij`/`card_le_card_of_injOn` used elsewhere in this campaign —
`sum_nbij'` operates on plain `∀a∈s,...` hypotheses). Two Lean bugs fixed
across 2 verification-tool rounds before this landed:
1. A self-referential `rw [← hNd]` (`hNd : d*(prodPrimes/d)=prodPrimes`)
   inside a goal that ITSELF contained the subterm `prodPrimes/d` rewrote
   BOTH the intended occurrence and the one buried inside the division,
   producing a garbled `d*(prodPrimes/d) = d*(d*(prodPrimes/d)/d)`-shaped
   goal. Fixed by precomputing a clean fact
   (`hcofactor_dvd : prodPrimes/d ∣ prodPrimes := ⟨d,
   (Nat.div_mul_cancel hdvdN).symm⟩`) ONCE and reusing it, avoiding the
   self-referential rewrite entirely.
2. `rw [Finset.mul_sum]` on a doubly-nested product `μ(d)*((T(d)/L)*∑e)`
   matched the WRONG (inner) instantiation, silently dropping the outer
   `μ(d)` factor. Fixed by proving the per-term equality as an explicit
   named `have hterm`, then combining via `Finset.sum_congr rfl hterm`
   followed by a single, unambiguous `← Finset.mul_sum` (only one
   `Finset.sum` present in the goal at that point, so no ambiguity).
   `field_simp; nlinarith [...]` also proved unreliable for the per-term
   algebraic identity (μ(e)²=1 substitution) — replaced with an explicit
   3-step `calc` chain (pure `ring` steps bracketing one clean `rw`),
   which is far more predictable than trusting `nlinarith` to find a
   nonlinear equality proof from a squared-term hint.
-/

theorem erdos647_selberg_weight_bound :
    ∀ (s : SelbergSieve) (d : ℕ), d ∈ s.prodPrimes.divisors →
      |(∑ l' ∈ s.prodPrimes.divisors, if d ∣ l' then (ArithmeticFunction.moebius (l'/d) : ℝ) *
            ((ArithmeticFunction.moebius l' : ℝ) * s.selbergTerms l' / (∑ l ∈ s.prodPrimes.divisors, s.selbergTerms l))
          else 0) / s.nu d|
      ≤ s.selbergTerms d / s.nu d := by
  intro s d hd
  set D := s.prodPrimes.divisors with hD_def
  set L := ∑ l ∈ D, s.selbergTerms l with hL_def
  have h1mem : (1:ℕ) ∈ D := Nat.mem_divisors.mpr ⟨one_dvd _, s.prodPrimes_squarefree.ne_zero⟩
  have hLpos : 0 < L := Finset.sum_pos (fun l hl => s.selbergTerms_pos (Nat.dvd_of_mem_divisors hl)) ⟨1, h1mem⟩
  have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
  have hdvdN : d ∣ s.prodPrimes := Nat.dvd_of_mem_divisors hd
  have hNne0 : s.prodPrimes ≠ 0 := s.prodPrimes_squarefree.ne_zero
  have hnudpos : 0 < s.nu d := BoundingSieve.nu_pos_of_dvd_prodPrimes hdvdN
  have hTdpos : 0 < s.selbergTerms d := s.selbergTerms_pos hdvdN
  have hNd : d * (s.prodPrimes/d) = s.prodPrimes := Nat.mul_div_cancel' hdvdN
  have hcofactor_dvd : (s.prodPrimes/d) ∣ s.prodPrimes := ⟨d, (Nat.div_mul_cancel hdvdN).symm⟩
  have hgeneral_reindex : ∀ (N dd : ℕ), 0 < dd → dd ∣ N → N ≠ 0 → ∀ (f : ℕ → ℝ),
      (∑ l' ∈ N.divisors, if dd ∣ l' then f l' else 0) = ∑ e ∈ (N/dd).divisors, f (dd*e) := by
    intro N dd hdd hdvd hN f
    have hNd' : dd * (N/dd) = N := Nat.mul_div_cancel' hdvd
    rw [← Finset.sum_filter]
    apply Finset.sum_nbij' (fun l' => l'/dd) (fun e => dd*e)
    · intro l' hl'
      simp only [Finset.mem_filter, Nat.mem_divisors] at hl'
      obtain ⟨⟨hl'dvd, _⟩, hdl'⟩ := hl'
      simp only [Nat.mem_divisors]
      obtain ⟨e, he⟩ := hdl'
      refine ⟨?_, ?_⟩
      · rw [he]
        have hstep : dd * e ∣ dd * (N/dd) := by rw [hNd', ← he]; exact hl'dvd
        have he2 : e ∣ N/dd := (mul_dvd_mul_iff_left hdd.ne').mp hstep
        rw [Nat.mul_div_cancel_left e hdd]
        exact he2
      · intro hcontra
        apply hN
        rw [← hNd', hcontra, mul_zero]
    · intro e he
      simp only [Nat.mem_divisors] at he
      simp only [Finset.mem_filter, Nat.mem_divisors]
      obtain ⟨he1, he2⟩ := he
      refine ⟨⟨?_, hN⟩, ?_⟩
      · obtain ⟨f2, hf2⟩ := he1
        refine ⟨f2, ?_⟩
        rw [← hNd', hf2]
        ring
      · exact Dvd.intro e rfl
    · intro l' hl'
      simp only [Finset.mem_filter, Nat.mem_divisors] at hl'
      obtain ⟨⟨_, _⟩, hdl'⟩ := hl'
      obtain ⟨e, he⟩ := hdl'
      rw [he, Nat.mul_div_cancel_left e hdd]
    · intro e he
      simp only [Nat.mem_divisors] at he
      rw [Nat.mul_div_cancel_left e hdd]
    · intro l' hl'
      simp only [Finset.mem_filter, Nat.mem_divisors] at hl'
      obtain ⟨⟨_, _⟩, hdl'⟩ := hl'
      obtain ⟨e, he⟩ := hdl'
      rw [he, Nat.mul_div_cancel_left e hdd]
  have hreindex := hgeneral_reindex s.prodPrimes d hdpos hdvdN hNne0
      (fun l' => (ArithmeticFunction.moebius (l'/d) : ℝ) * ((ArithmeticFunction.moebius l' : ℝ) * s.selbergTerms l' / L))
  have hdsqfree : Squarefree d := Squarefree.squarefree_of_dvd hdvdN s.prodPrimes_squarefree
  have hmoebius_sq_d : (ArithmeticFunction.moebius d : ℝ)^2 = 1 := by
    rw [ArithmeticFunction.moebius_apply_of_squarefree hdsqfree]
    push_cast
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  have hmoebius_abs_d : |(ArithmeticFunction.moebius d : ℝ)| = 1 := by
    nlinarith [sq_abs (ArithmeticFunction.moebius d : ℝ), hmoebius_sq_d, abs_nonneg (ArithmeticFunction.moebius d : ℝ)]
  have hstep2 : (∑ e ∈ (s.prodPrimes/d).divisors, (ArithmeticFunction.moebius ((d*e)/d) : ℝ) *
      ((ArithmeticFunction.moebius (d*e) : ℝ) * s.selbergTerms (d*e) / L))
    = (ArithmeticFunction.moebius d : ℝ) * (s.selbergTerms d / L) * (∑ e ∈ (s.prodPrimes/d).divisors, s.selbergTerms e) := by
    have hterm : ∀ e ∈ (s.prodPrimes/d).divisors, (ArithmeticFunction.moebius ((d*e)/d) : ℝ) *
        ((ArithmeticFunction.moebius (d*e) : ℝ) * s.selbergTerms (d*e) / L)
        = (ArithmeticFunction.moebius d : ℝ) * (s.selbergTerms d / L) * s.selbergTerms e := by
      intro e he
      rw [Nat.mem_divisors] at he
      have hedvdN : e ∣ s.prodPrimes := he.1.trans hcofactor_dvd
      have hdesqfree : Squarefree (d*e) := by
        apply Squarefree.squarefree_of_dvd _ s.prodPrimes_squarefree
        obtain ⟨f2, hf2⟩ := he.1
        exact ⟨f2, by rw [← hNd, hf2]; ring⟩
      have hcop : Nat.Coprime d e := Nat.coprime_of_squarefree_mul hdesqfree
      have hesqfree : Squarefree e := Squarefree.squarefree_of_dvd hedvdN s.prodPrimes_squarefree
      have hmoebius_sq_e : (ArithmeticFunction.moebius e : ℝ)^2 = 1 := by
        rw [ArithmeticFunction.moebius_apply_of_squarefree hesqfree]
        push_cast
        rw [← pow_mul, mul_comm, pow_mul]
        norm_num
      rw [Nat.mul_div_cancel_left e hdpos, s.selbergTerms_isMultiplicative.map_mul_of_coprime hcop]
      have hmoebius_mul : (ArithmeticFunction.moebius (d*e) : ℝ) = (ArithmeticFunction.moebius d : ℝ) * (ArithmeticFunction.moebius e : ℝ) := by
        have hmm := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop
        exact_mod_cast hmm
      rw [hmoebius_mul]
      have hesq : (ArithmeticFunction.moebius e:ℝ) * (ArithmeticFunction.moebius e:ℝ) = 1 := by
        rw [← sq]; exact hmoebius_sq_e
      calc (ArithmeticFunction.moebius e:ℝ) * ((ArithmeticFunction.moebius d:ℝ) * (ArithmeticFunction.moebius e:ℝ) * (s.selbergTerms d * s.selbergTerms e) / L)
          = ((ArithmeticFunction.moebius e:ℝ) * (ArithmeticFunction.moebius e:ℝ)) * (ArithmeticFunction.moebius d:ℝ) * (s.selbergTerms d * s.selbergTerms e) / L := by ring
        _ = 1 * (ArithmeticFunction.moebius d:ℝ) * (s.selbergTerms d * s.selbergTerms e) / L := by rw [hesq]
        _ = (ArithmeticFunction.moebius d:ℝ) * (s.selbergTerms d / L) * s.selbergTerms e := by ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have hbound_sum : (∑ e ∈ (s.prodPrimes/d).divisors, s.selbergTerms e) ≤ L := by
    rw [hL_def]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro x hx
      rw [Nat.mem_divisors] at hx ⊢
      exact ⟨hx.1.trans hcofactor_dvd, hNne0⟩
    · intro i hi _
      exact le_of_lt (s.selbergTerms_pos (Nat.dvd_of_mem_divisors hi))
  have hsum_nonneg : 0 ≤ (∑ e ∈ (s.prodPrimes/d).divisors, s.selbergTerms e) :=
    Finset.sum_nonneg (fun e he => le_of_lt (s.selbergTerms_pos ((Nat.dvd_of_mem_divisors he).trans hcofactor_dvd)))
  rw [hreindex, hstep2]
  rw [abs_div, abs_of_pos hnudpos]
  gcongr
  rw [mul_assoc, abs_mul, hmoebius_abs_d, one_mul, abs_of_nonneg (mul_nonneg (le_of_lt (div_pos hTdpos hLpos)) hsum_nonneg)]
  rw [div_mul_eq_mul_div, div_le_iff₀ hLpos]
  nlinarith [hbound_sum, hTdpos]
