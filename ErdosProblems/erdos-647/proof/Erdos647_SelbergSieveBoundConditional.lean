import Mathlib

/-!
# Erdős #647 — Layer B+C CAPSTONE: the full conditional Selberg sieve bound

Snapshot of the exact statement + proof term kernel-verified through the
tracked proof-search pipeline on 2026-07-14.

  problem_version_id  2cd69153-4e77-4db7-8aba-0d330e95711f
  episode_id          29124031-7d87-42be-b4bd-0544e2d6a4a3
  root_statement_hash 0455f341aa86b2db5641f0315eb32bb13ed715e9238e50502208947b06535102
  outcome             kernel_verified (root_proved)
  import manifest     ["Mathlib.Tactic.Ring", "Mathlib.Tactic.NormNum", "Mathlib"]

Content: for ANY `s : SelbergSieve`, the full Selberg sieve upper bound in
CONCRETE closed form:

  `siftedSum ≤ totalMass/L + ∑_{d∣prodPrimes} (∏_{p∈d.primeFactors}
    (1+(1-ν(p))⁻¹))² · |rem d|`,  where `L := ∑_{l∣prodPrimes} selbergTerms(l)`

This is the CAPSTONE of the "conditional assembly" strategy adopted this
session: it combines essentially all of Layer B and the Layer B/C bridge
into ONE theorem, deliberately leaving `|rem d|` abstract (Mathlib's own
`s.rem`) so the wiring stays fully generic and reusable for ANY
`SelbergSieve` — the campaign's own concrete seven-tuple instantiation
(via `erdos647_rem_bound_squarefree`/`erdos647_rem_bound_one` for `|rem
d|`, and Layer A's `erdos647_mertens_assembly` for the Mertens estimate
needed to make `L` and the level `z` concrete) is the one remaining step,
to be substituted inside a single self-contained final submission (per
the `Nonempty BoundingSieve`/no-cross-reference environment constraint).

**What's combined** (all inlined, since cross-submission references
don't work in this environment):
1. The EXPLICIT optimal-weight construction via Möbius inversion
   (`erdos647_selberg_optimal_weight`'s technique): `y_l := μ(l)·
   selbergTerms(l)/L`, `w(d) := (∑_{l':d∣l'}μ(l'/d)·y(l'))/ν(d)`, giving
   `w(1)=1` and `mainSum(lambdaSquared w) = 1/L`.
2. The SAME weight's pointwise magnitude bound `|w(d)|≤selbergTerms(d)/
   ν(d)` (`erdos647_selberg_weight_bound`'s technique), adapted to route
   through the SAME shared `y`/`w` definitions (one `set w := ... with
   hw_def` reused by both halves) rather than re-deriving from a raw
   formula — avoiding a syntactic-mismatch risk between two independently
   -defined `w`s that are only definitionally, not syntactically, equal.
   The only new step versus the original proof: `hterm`'s goal is phrased
   via `y(d·e)` instead of the raw formula, needing one extra rewrite
   (`y(d·e) = (μ(d·e):ℝ)·selbergTerms(d·e)/L`, via `hdemem : d·e∈D` and
   `hy_def`) before the rest of the original algebra proceeds unchanged.
3. Mathlib's `BoundingSieve.upperMoebius_lambdaSquared` (needs `w 1=1`)
   and `SelbergSieve.siftedSum_le_mainSum_errSum_of_upperMoebius`.
4. The errSum aggregate bound via `erdos647_lambdaSquared_bound` +
   `erdos647_divisor_sum_selbergTerms_div_nu` (both inlined, exactly as
   in `erdos647_errSum_conditional_bound`), using `hwbound` (from step 2)
   as the pointwise hypothesis.

**Zero new Lean bugs** — landed FIRST TRY on both the untracked
pre-check (~22s Lean CPU time for this ~400-line combined proof) and the
tracked pipeline, since every individual piece reused was already
independently debugged in prior sessions, and the merge strategy (share
`D`/`L`/`y`/`w` via one scope, adapt only the minimal necessary bridging
step in `hterm`) avoided introducing new failure surface.

**Remaining for the final numeric `x/(log x)^7` theorem** (genuinely the
last step): inline this campaign's own seven-tuple `BoundingSieve`
construction (`erdos647_boundingSieve_instance`'s technique) as a
concrete `s`, substitute `|s.rem d| ≤ rootUnionCount(d) ≤ 7^ω(d)` for
squarefree `d` (`erdos647_rem_bound_squarefree` + `erdos647_
rootUnionCount_le`) and `rem(1)=0` (`erdos647_rem_bound_one`), combine
with Layer A's `erdos647_mertens_assembly` to get an explicit growth rate
for `L=∑selbergTerms(l)` and the RHS sum as functions of the level `z`,
then choose `z=z(x)` optimally balancing main term vs error term. This is
now genuinely "assembly + one growth-rate estimate," not open research —
though the growth-rate estimate for `∑_{d|prodPrimes(z)}
(∏_{p|d}(1+(1-ν(p))⁻¹))²·7^ω(d)`-type multiplicative sums over `z` still
needs real care.
-/

theorem erdos647_selberg_sieve_bound_conditional :
    ∀ (s : SelbergSieve),
      s.siftedSum ≤ s.totalMass / (∑ l ∈ s.prodPrimes.divisors, s.selbergTerms l) +
        ∑ d ∈ s.prodPrimes.divisors, (∏ p ∈ d.primeFactors, (1 + (1 - s.nu p)⁻¹))^2 * |s.rem d| := by
  intro s
  set D := s.prodPrimes.divisors with hD_def
  set L := ∑ l ∈ D, s.selbergTerms l with hL_def
  have h1mem : (1:ℕ) ∈ D := Nat.mem_divisors.mpr ⟨one_dvd _, s.prodPrimes_squarefree.ne_zero⟩
  have hLpos : 0 < L := Finset.sum_pos (fun l hl => s.selbergTerms_pos (Nat.dvd_of_mem_divisors hl)) ⟨1, h1mem⟩
  have hNne0 : s.prodPrimes ≠ 0 := s.prodPrimes_squarefree.ne_zero
  set y : ℕ → ℝ := fun l => if l ∈ D then (ArithmeticFunction.moebius l : ℝ) * s.selbergTerms l / L else 0 with hy_def
  have hmoebius_sq : ∀ l ∈ D, (ArithmeticFunction.moebius l : ℝ)^2 = 1 := by
    intro l hl
    have hsqfree : Squarefree l := BoundingSieve.squarefree_of_dvd_prodPrimes (Nat.dvd_of_mem_divisors hl)
    rw [ArithmeticFunction.moebius_apply_of_squarefree hsqfree]
    push_cast
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  have hswap : ∀ l ∈ D, (∑ d ∈ D, if l ∣ d then
        (∑ l' ∈ D, if d ∣ l' then (ArithmeticFunction.moebius (l'/d) : ℝ) * y l' else 0) else 0) = y l := by
    intro l hl
    have hmi : ∀ m : ℕ, 0 < m → ∑ e ∈ m.divisors, (ArithmeticFunction.moebius e : ℝ) = if m = 1 then 1 else 0 := by
      intro m hm
      have h1 : (ArithmeticFunction.moebius * ArithmeticFunction.zeta : ArithmeticFunction ℝ) m = ∑ i ∈ m.divisors, (ArithmeticFunction.moebius i : ℝ) := ArithmeticFunction.coe_mul_zeta_apply
      have h2 : (ArithmeticFunction.moebius * ArithmeticFunction.zeta : ArithmeticFunction ℝ) = 1 := ArithmeticFunction.coe_moebius_mul_coe_zeta
      rw [h2, ArithmeticFunction.one_apply] at h1
      exact h1.symm
    have hNpos : 0 < s.prodPrimes := s.prodPrimes_squarefree.ne_zero.bot_lt
    have hlpos : 0 < l := Nat.pos_of_mem_divisors hl
    have hldvdN : l ∣ s.prodPrimes := Nat.dvd_of_mem_divisors hl
    have hstep1 : (∑ d ∈ D, if l ∣ d then
          (∑ l' ∈ D, if d ∣ l' then (ArithmeticFunction.moebius (l'/d) : ℝ) * y l' else 0) else 0)
        = ∑ d ∈ D, ∑ l' ∈ D, (if l ∣ d ∧ d ∣ l' then (ArithmeticFunction.moebius (l'/d) : ℝ) * y l' else 0) := by
      apply Finset.sum_congr rfl
      intro d hd
      by_cases hld : l ∣ d
      · simp only [hld, if_true, true_and]
      · rw [if_neg hld]
        symm
        apply Finset.sum_eq_zero
        intro l' _
        exact if_neg (fun h => hld h.1)
    rw [hstep1, Finset.sum_comm]
    have hstep2 : ∑ l' ∈ D, ∑ d ∈ D, (if l ∣ d ∧ d ∣ l' then (ArithmeticFunction.moebius (l'/d) : ℝ) * y l' else 0)
        = ∑ l' ∈ D, (if l' = l then y l' else 0) := by
      apply Finset.sum_congr rfl
      intro l' hl'
      have hl'pos : 0 < l' := Nat.pos_of_mem_divisors hl'
      have hl'dvdN : l' ∣ s.prodPrimes := Nat.dvd_of_mem_divisors hl'
      by_cases hll' : l ∣ l'
      · obtain ⟨m, hm⟩ := hll'
        have hmpos : 0 < m := by
          rcases Nat.eq_zero_or_pos m with h0 | h0
          · exfalso; rw [h0, mul_zero] at hm; omega
          · exact h0
        have hml' : m ∣ l' := ⟨l, by rw [hm]; ring⟩
        have hfilter_eq : D.filter (fun d => l ∣ d ∧ d ∣ l') = l'.divisors.filter (fun d => l ∣ d) := by
          ext d
          simp only [hD_def, Finset.mem_filter, Nat.mem_divisors]
          constructor
          · rintro ⟨⟨_, _⟩, hld, hdl'⟩
            exact ⟨⟨hdl', hl'pos.ne'⟩, hld⟩
          · rintro ⟨⟨hdl', _⟩, hld⟩
            exact ⟨⟨hdl'.trans hl'dvdN, s.prodPrimes_squarefree.ne_zero⟩, hld, hdl'⟩
        have hbij : ∑ d ∈ D, (if l ∣ d ∧ d ∣ l' then (ArithmeticFunction.moebius (l'/d) : ℝ) * y l' else 0)
            = ∑ e ∈ m.divisors, (ArithmeticFunction.moebius e : ℝ) * y l' := by
          rw [← Finset.sum_filter, hfilter_eq]
          apply Finset.sum_nbij' (fun x => l' / x) (fun x => l' / x)
          · intro d hd
            simp only [Finset.mem_filter, Nat.mem_divisors] at hd
            obtain ⟨⟨hdl', _⟩, hld⟩ := hd
            rw [Nat.mem_divisors]
            refine ⟨?_, hmpos.ne'⟩
            obtain ⟨e, he⟩ := hld
            have hde : d * (l' / d) = l' := Nat.mul_div_cancel' hdl'
            have heq1 : l * (e * (l' / d)) = l * m := by rw [← mul_assoc, ← he, hde, hm]
            have hem : e * (l' / d) = m := Nat.eq_of_mul_eq_mul_left hlpos heq1
            exact ⟨e, by rw [← hem]; ring⟩
          · intro e he
            simp only [Finset.mem_coe, Nat.mem_divisors] at he
            simp only [Finset.mem_filter, Nat.mem_divisors]
            obtain ⟨e', he'⟩ := he.1
            have hepos : 0 < e := Nat.pos_of_dvd_of_pos he.1 hmpos
            have hl'e : l' / e = l * e' := by
              have hl'eq : l' = (l * e') * e := by rw [hm, he']; ring
              rw [hl'eq, Nat.mul_div_cancel _ hepos]
            refine ⟨⟨⟨e, by rw [hl'e, hm, he']; ring⟩, hl'pos.ne'⟩, ⟨e', hl'e⟩⟩
          · intro d hd
            simp only [Finset.mem_filter, Nat.mem_divisors] at hd
            obtain ⟨⟨hdl', _⟩, _⟩ := hd
            have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdl' hl'pos
            have hde : (l' / d) * d = l' := Nat.div_mul_cancel hdl'
            have hddpos : 0 < l' / d := Nat.div_pos (Nat.le_of_dvd hl'pos hdl') hdpos
            nth_rewrite 1 [show l' = (l'/d) * d from hde.symm]
            exact Nat.mul_div_cancel_left d hddpos
          · intro e he
            simp only [Finset.mem_coe, Nat.mem_divisors] at he
            have hel' : e ∣ l' := he.1.trans hml'
            have hepos : 0 < e := Nat.pos_of_dvd_of_pos he.1 hmpos
            have hde : (l' / e) * e = l' := Nat.div_mul_cancel hel'
            have hdepos : 0 < l' / e := Nat.div_pos (Nat.le_of_dvd hl'pos hel') hepos
            nth_rewrite 1 [show l' = (l'/e) * e from hde.symm]
            exact Nat.mul_div_cancel_left e hdepos
          · intro d _
            rfl
        rw [hbij, ← Finset.sum_mul, hmi m hmpos]
        have hiff : m = 1 ↔ l' = l := by
          constructor
          · intro h1; rw [hm, h1, mul_one]
          · intro h2
            have heq2 : l * m = l * 1 := by rw [← hm, h2, mul_one]
            exact Nat.eq_of_mul_eq_mul_left hlpos heq2
        simp only [hiff]
        by_cases hcond : l' = l
        · simp [hcond]
        · simp [hcond]
      · have hzero : ∀ d ∈ D, (if l ∣ d ∧ d ∣ l' then (ArithmeticFunction.moebius (l'/d) : ℝ) * y l' else 0) = 0 := by
          intro d hd
          rw [if_neg]
          intro hc
          exact hll' (hc.1.trans hc.2)
        rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero, if_neg]
        intro heq
        exact hll' (heq ▸ dvd_refl l)
    rw [hstep2, Finset.sum_ite_eq' D l y]
    simp [hl]
  set w : ℕ → ℝ := fun d => if d ∈ D then
      (∑ l' ∈ D, if d ∣ l' then (ArithmeticFunction.moebius (l'/d) : ℝ) * y l' else 0) / s.nu d
    else 0 with hw_def
  have hinv : ∀ l ∈ D, (∑ d ∈ D, if l ∣ d then s.nu d * w d else 0) = y l := by
    intro l hl
    rw [← hswap l hl]
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hld : l ∣ d
    · simp only [hld, if_true]
      rw [hw_def]
      simp only [hd, if_true]
      rw [mul_div_cancel₀]
      exact s.nu_ne_zero (Nat.dvd_of_mem_divisors hd)
    · simp [hld]
  have hw1 : w 1 = 1 := by
    have hw1' : w 1 = (∑ l' ∈ D, if (1:ℕ) ∣ l' then (ArithmeticFunction.moebius (l'/1) : ℝ) * y l' else 0) / s.nu 1 := by
      rw [hw_def]; simp [h1mem]
    rw [hw1', s.nu_mult.map_one]
    have hsum1 : (∑ l' ∈ D, if (1:ℕ) ∣ l' then (ArithmeticFunction.moebius (l'/1) : ℝ) * y l' else 0) = 1 := by
      have heq : ∀ l' ∈ D, (if (1:ℕ) ∣ l' then (ArithmeticFunction.moebius (l'/1) : ℝ) * y l' else 0) = s.selbergTerms l' / L := by
        intro l' hl'
        simp only [one_dvd, if_true, Nat.div_one]
        rw [hy_def]
        simp only [hl', if_true]
        have hsq := hmoebius_sq l' hl'
        have hTpos := s.selbergTerms_pos (Nat.dvd_of_mem_divisors hl')
        field_simp
        nlinarith [hsq]
      rw [Finset.sum_congr rfl heq, ← Finset.sum_div, ← hL_def, div_self hLpos.ne']
    rw [hsum1]; norm_num
  have hmainSum : s.mainSum (BoundingSieve.lambdaSquared w) = 1 / L := by
    rw [s.mainSum_lambdaSquared_eq_sum_mul_sum_sq w]
    have hstep : ∀ l ∈ D, (s.selbergTerms l)⁻¹ * (∑ d ∈ D, if l ∣ d then s.nu d * w d else 0)^2
        = s.selbergTerms l / L^2 := by
      intro l hl
      rw [hinv l hl, hy_def]
      simp only [hl, if_true]
      have hsq := hmoebius_sq l hl
      have hTpos := s.selbergTerms_pos (Nat.dvd_of_mem_divisors hl)
      field_simp
      nlinarith [hsq, hTpos]
    rw [Finset.sum_congr rfl hstep, ← Finset.sum_div, ← hL_def]
    rw [pow_two, ← div_div, div_self hLpos.ne', one_div]
  have hwbound : ∀ d ∈ D, |w d| ≤ s.selbergTerms d / s.nu d := by
    intro d hd
    rw [hw_def]
    simp only [hd, if_true]
    have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
    have hdvdN : d ∣ s.prodPrimes := Nat.dvd_of_mem_divisors hd
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
        (fun l' => (ArithmeticFunction.moebius (l'/d) : ℝ) * y l')
    have hdsqfree : Squarefree d := Squarefree.squarefree_of_dvd hdvdN s.prodPrimes_squarefree
    have hmoebius_sq_d : (ArithmeticFunction.moebius d : ℝ)^2 = 1 := by
      rw [ArithmeticFunction.moebius_apply_of_squarefree hdsqfree]
      push_cast
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    have hmoebius_abs_d : |(ArithmeticFunction.moebius d : ℝ)| = 1 := by
      nlinarith [sq_abs (ArithmeticFunction.moebius d : ℝ), hmoebius_sq_d, abs_nonneg (ArithmeticFunction.moebius d : ℝ)]
    have hstep2 : (∑ e ∈ (s.prodPrimes/d).divisors, (ArithmeticFunction.moebius ((d*e)/d) : ℝ) * y (d*e))
      = (ArithmeticFunction.moebius d : ℝ) * (s.selbergTerms d / L) * (∑ e ∈ (s.prodPrimes/d).divisors, s.selbergTerms e) := by
      have hterm : ∀ e ∈ (s.prodPrimes/d).divisors, (ArithmeticFunction.moebius ((d*e)/d) : ℝ) * y (d*e)
          = (ArithmeticFunction.moebius d : ℝ) * (s.selbergTerms d / L) * s.selbergTerms e := by
        intro e he
        rw [Nat.mem_divisors] at he
        have hedvdN : e ∣ s.prodPrimes := he.1.trans hcofactor_dvd
        have hdemem : (d*e) ∈ D := by
          rw [hD_def, Nat.mem_divisors]
          refine ⟨?_, hNne0⟩
          rw [← hNd]; exact mul_dvd_mul_left d he.1
        rw [show y (d*e) = (ArithmeticFunction.moebius (d*e) : ℝ) * s.selbergTerms (d*e) / L from by rw [hy_def]; simp [hdemem]]
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
  have hupper : BoundingSieve.IsUpperMoebius (BoundingSieve.lambdaSquared w) := BoundingSieve.upperMoebius_lambdaSquared w hw1
  have hsifted : s.siftedSum ≤ s.totalMass * s.mainSum (BoundingSieve.lambdaSquared w) + s.errSum (BoundingSieve.lambdaSquared w) :=
    s.siftedSum_le_mainSum_errSum_of_upperMoebius (BoundingSieve.lambdaSquared w) hupper
  rw [hmainSum] at hsifted
  have hlambda_bound : ∀ d ∈ D, |BoundingSieve.lambdaSquared w d| ≤ (∑ d1 ∈ d.divisors, s.selbergTerms d1 / s.nu d1)^2 := by
    intro d hd
    have hdvdN : d ∣ s.prodPrimes := Nat.dvd_of_mem_divisors hd
    have hwd : ∀ d1 ∈ d.divisors, |w d1| ≤ s.selbergTerms d1 / s.nu d1 := by
      intro d1 hd1
      have hd1dvd : d1 ∣ d := Nat.dvd_of_mem_divisors hd1
      exact hwbound d1 (Nat.mem_divisors.mpr ⟨hd1dvd.trans hdvdN, hNne0⟩)
    have hstep : |BoundingSieve.lambdaSquared w d| ≤ ∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors, |w d1| * |w d2| := by
      unfold BoundingSieve.lambdaSquared
      calc |∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors, if d = Nat.lcm d1 d2 then w d1 * w d2 else 0|
          ≤ ∑ d1 ∈ d.divisors, |∑ d2 ∈ d.divisors, if d = Nat.lcm d1 d2 then w d1 * w d2 else 0| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors, |if d = Nat.lcm d1 d2 then w d1 * w d2 else 0| := by
            apply Finset.sum_le_sum
            intro d1 _
            exact Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors, |w d1| * |w d2| := by
            apply Finset.sum_le_sum
            intro d1 _
            apply Finset.sum_le_sum
            intro d2 _
            split_ifs with h
            · rw [abs_mul]
            · rw [abs_zero]; positivity
    have heq : (∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors, |w d1| * |w d2|) = (∑ d1 ∈ d.divisors, |w d1|) * (∑ d2 ∈ d.divisors, |w d2|) := by
      rw [Finset.sum_mul_sum]
    have hsum_le : (∑ d1 ∈ d.divisors, |w d1|) ≤ ∑ d1 ∈ d.divisors, s.selbergTerms d1 / s.nu d1 :=
      Finset.sum_le_sum hwd
    have hsum_nonneg : 0 ≤ ∑ d1 ∈ d.divisors, |w d1| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    calc |BoundingSieve.lambdaSquared w d| ≤ ∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors, |w d1| * |w d2| := hstep
      _ = (∑ d1 ∈ d.divisors, |w d1|) * (∑ d2 ∈ d.divisors, |w d2|) := heq
      _ = (∑ d1 ∈ d.divisors, |w d1|)^2 := by rw [sq]
      _ ≤ (∑ d1 ∈ d.divisors, s.selbergTerms d1 / s.nu d1)^2 := pow_le_pow_left₀ hsum_nonneg hsum_le 2
  have hclosed_form : ∀ d ∈ D, ∑ d1 ∈ d.divisors, s.selbergTerms d1 / s.nu d1 = ∏ p ∈ d.primeFactors, (1 + (1 - s.nu p)⁻¹) := by
    intro d hd
    have hdvdN : d ∣ s.prodPrimes := Nat.dvd_of_mem_divisors hd
    have hdsqfree : Squarefree d := Squarefree.squarefree_of_dvd hdvdN s.prodPrimes_squarefree
    have hdeq : (∏ p ∈ d.primeFactors, p) = d := Nat.prod_primeFactors_of_squarefree hdsqfree
    have hp_all : ∀ p ∈ d.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
    have hgeneral : ∀ (t : Finset ℕ), (∀ p ∈ t, p.Prime) → ∀ (f : ℕ → ℝ),
        ∑ d1 ∈ (∏ p ∈ t, p).divisors, ∏ p ∈ d1.primeFactors, f p = ∏ p ∈ t, (1 + f p) := by
      intro t
      induction t using Finset.induction_on with
      | empty => intro f; simp
      | @insert p t' hp_notin ih =>
        intro hp_all f
        have hp_prime : p.Prime := hp_all p (Finset.mem_insert_self p t')
        have ht'_prime : ∀ q ∈ t', q.Prime := fun q hq => hp_all q (Finset.mem_insert_of_mem hq)
        have hM_pos : 0 < ∏ q ∈ t', q := Finset.prod_pos (fun q hq => (ht'_prime q hq).pos)
        have hcop : Nat.Coprime p (∏ q ∈ t', q) := by
          apply Nat.Coprime.prod_right
          intro q hq
          rw [Nat.coprime_primes hp_prime (ht'_prime q hq)]
          intro heq; exact hp_notin (heq ▸ hq)
        conv_lhs => rw [Finset.prod_insert hp_notin]
        conv_rhs => rw [Finset.prod_insert hp_notin]
        rw [← ih ht'_prime f]
        have hMne0 : (∏ q ∈ t', q) ≠ 0 := hM_pos.ne'
        have hpMne0 : (p * ∏ q ∈ t', q) ≠ 0 := Nat.mul_ne_zero hp_prime.pos.ne' hMne0
        have hsplit : (p * ∏ q ∈ t', q).divisors = (∏ q ∈ t', q).divisors ∪ (∏ q ∈ t', q).divisors.image (fun b => p*b) := by
          ext d1
          simp only [Finset.mem_union, Finset.mem_image, Nat.mem_divisors]
          constructor
          · rintro ⟨hdvd, _⟩
            by_cases hpd : p ∣ d1
            · obtain ⟨e, he⟩ := hpd
              right
              refine ⟨e, ⟨?_, hMne0⟩, he.symm⟩
              rw [he] at hdvd
              exact (mul_dvd_mul_iff_left hp_prime.pos.ne').mp hdvd
            · left
              refine ⟨?_, hMne0⟩
              have hcop2 : Nat.Coprime d1 p := ((Nat.Prime.coprime_iff_not_dvd hp_prime).mpr hpd).symm
              exact (Nat.Coprime.dvd_of_dvd_mul_left hcop2 hdvd)
          · rintro (⟨hdvd, _⟩ | ⟨e, ⟨he, _⟩, heq⟩)
            · exact ⟨hdvd.trans ⟨p, by ring⟩, hpMne0⟩
            · rw [← heq]
              exact ⟨mul_dvd_mul_left p he, hpMne0⟩
        rw [hsplit]
        have hdisj : Disjoint ((∏ q ∈ t', q).divisors) ((∏ q ∈ t', q).divisors.image (fun b => p*b)) := by
          apply Finset.disjoint_left.mpr
          intro a ha1 ha2
          simp only [Finset.mem_image] at ha2
          obtain ⟨e, he, heq⟩ := ha2
          have haM : a ∣ (∏ q ∈ t', q) := Nat.dvd_of_mem_divisors ha1
          have hpa : p ∣ a := by rw [← heq]; exact Dvd.intro e rfl
          have hpM : p ∣ (∏ q ∈ t', q) := hpa.trans haM
          exact absurd (Nat.eq_one_of_dvd_coprimes hcop (dvd_refl p) hpM) hp_prime.ne_one
        rw [Finset.sum_union hdisj]
        have hstep2 : ∑ b ∈ (∏ q ∈ t', q).divisors.image (fun b => p*b), ∏ p_1 ∈ b.primeFactors, f p_1
            = f p * ∑ b ∈ (∏ q ∈ t', q).divisors, ∏ p_1 ∈ b.primeFactors, f p_1 := by
          rw [Finset.mul_sum]
          rw [Finset.sum_image]
          · apply Finset.sum_congr rfl
            intro b hb
            have hbM : b ∣ (∏ q ∈ t', q) := Nat.dvd_of_mem_divisors hb
            have hcopb : Nat.Coprime p b := hcop.coprime_dvd_right hbM
            have hbne0 : b ≠ 0 := by
              intro hb0; rw [hb0] at hbM; exact hMne0 (Nat.eq_zero_of_zero_dvd hbM)
            have hpb_pf : (p * b).primeFactors = insert p b.primeFactors := by
              rw [Nat.primeFactors_mul hp_prime.ne_zero hbne0, Nat.Prime.primeFactors hp_prime]
              rfl
            rw [hpb_pf]
            rw [Finset.prod_insert]
            intro hpmem
            have : p ∣ b := Nat.dvd_of_mem_primeFactors hpmem
            exact absurd (Nat.eq_one_of_dvd_coprimes hcopb (dvd_refl p) this) hp_prime.ne_one
          · intro a1 ha1 a2 ha2 heq
            exact Nat.eq_of_mul_eq_mul_left hp_prime.pos heq
        rw [hstep2]
        ring
    have hsum_eq : ∑ d1 ∈ d.divisors, ∏ p ∈ d1.primeFactors, (1 - s.nu p)⁻¹ = ∏ p ∈ d.primeFactors, (1 + (1 - s.nu p)⁻¹) := by
      conv_lhs => rw [← hdeq]
      exact hgeneral d.primeFactors hp_all (fun p => (1 - s.nu p)⁻¹)
    rw [← hsum_eq]
    apply Finset.sum_congr rfl
    intro d1 hd1
    rw [Nat.mem_divisors] at hd1
    have hd1dvdN : d1 ∣ s.prodPrimes := hd1.1.trans hdvdN
    have hnud1pos : 0 < s.nu d1 := BoundingSieve.nu_pos_of_dvd_prodPrimes hd1dvdN
    rw [s.selbergTerms_apply]
    rw [mul_comm, mul_div_assoc, div_self (ne_of_gt hnud1pos), mul_one]
  have herrSum : s.errSum (BoundingSieve.lambdaSquared w) ≤ ∑ d ∈ D, (∏ p ∈ d.primeFactors, (1 + (1 - s.nu p)⁻¹))^2 * |s.rem d| := by
    unfold BoundingSieve.errSum
    apply Finset.sum_le_sum
    intro d hd
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    rw [← hclosed_form d hd]
    exact hlambda_bound d hd
  calc s.siftedSum ≤ s.totalMass * (1/L) + s.errSum (BoundingSieve.lambdaSquared w) := hsifted
    _ ≤ s.totalMass * (1/L) + ∑ d ∈ D, (∏ p ∈ d.primeFactors, (1 + (1 - s.nu p)⁻¹))^2 * |s.rem d| := by linarith [herrSum]
    _ = s.totalMass / L + ∑ d ∈ D, (∏ p ∈ d.primeFactors, (1 + (1 - s.nu p)⁻¹))^2 * |s.rem d| := by rw [mul_one_div]
