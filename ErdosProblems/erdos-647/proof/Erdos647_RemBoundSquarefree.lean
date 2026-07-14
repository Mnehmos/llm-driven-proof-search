import Mathlib

/-!
# Erdős #647 — Layer C: rem(d) bound for composite squarefree d

Snapshot of the exact statement + proof term kernel-verified through the
tracked proof-search pipeline on 2026-07-14.

  problem_version_id  55188345-7099-4e48-8879-f50786ca2404
  episode_id          748fe60f-4951-443a-ab48-1ccb1ec2e782
  root_statement_hash c3d316e4a96f444204d3e595d9a1880308458a301fbacdfb65d536ad4096d85d
  outcome             kernel_verified (root_proved)
  import manifest     ["Mathlib.Tactic.Ring", "Mathlib.Tactic.NormNum", "Mathlib"]

Content: generalizes `erdos647_rem_bound` (proven only for prime `p`)
to any squarefree `d` with at least one prime factor. Same conclusion
shape — `|multSum(d,X) - ν(d)·X| ≤ rootUnionCount(d)` — where now `d`
ranges over any squarefree divisor, not just a prime. This is the key
missing piece before Mathlib's `BoundingSieve.errSum` (which, per
`SelbergSieve.lean`, sums `|rem d|` over EVERY `d ∈ prodPrimes(z).divisors`
— i.e. every squarefree product of admissible primes ≤ z, not just
primes) can finally be bounded.

`rootUnionCount(d)` here is defined DIRECTLY as `|{r < d : ∀ p ∈
d.primeFactors, r%p ∈ rootUnionSet(p)}|` (a raw filter over `range d`,
matching what `erdos647_crt_card_finset` would compute as
`∏_{p∣d}rootUnionCount(p)` — that product-formula connection is not
needed for THIS theorem's proof, only for later corollaries that want an
explicit numeric bound).

Proof structure mirrors `erdos647_rem_bound` closely (same biUnion +
floor-counting argument, same real-arithmetic tail), generalized via
three new pieces:

1. **`hsqfree_dvd`**: squarefree `d ∣ m ↔ ∀p∈d.primeFactors, p∣m`
   (`erdos647_squarefree_dvd_iff`'s proof, inlined).
2. **`hbridge`**: `erdos647_forms_divisible_iff`'s proof — already
   universally quantified over `p`, reused verbatim with zero changes.
3. **The mod-reduction chain** (`hmodhelp`/`hmodhelp2`/`hmodhelp3`):
   connects a per-prime-`p` fact about `N` to the SAME fact about `(N%d)%p`
   (since `p∣d`), needed because `Sd`'s membership condition is phrased
   via `r%p` for `r:=N%d`, introducing an EXTRA layer of `%p` beyond what
   the prime-only proof needed. `hmodhelp3 : (c·((N%d)%p))%p = (c·N)%p`
   packages the full round-trip, and `hdisj_iff` applies it to all 7
   coefficients at once so the whole 7-way disjunction converts between
   "N-form" and "(N%d)%p-form" in a single `rw` chain (auto-closing via
   `rfl` once both sides match syntactically).

Two new Lean lessons from this proof:

1. **A double-mod bug, not just a transport bug**: an early draft used
   `hmodhelp2` alone to bridge `hSrp`/`hthis` directly against the goal,
   but `Sd`'s condition `r%p ∈ (range p).filter(fun s=>(210*s)%p=1∨...)`
   evaluated at `r:=N%d` produces `(210*((N%d)%p))%p=1` — an EXTRA `%p`
   layer beyond `hmodhelp2`'s `(210*(N%d))%p=1` — silently mismatched
   types that the verifier caught as a genuine (not just cosmetic) gap.
   Fixed by deriving `hmodhelp3` (chaining `hmodhelp2` with a second
   `hmodhelp` application) and `hdisj_iff` (packaging all 7 coefficients).
2. **`simp only [Finset.mem_filter, Finset.mem_range]` can legitimately
   report "no progress" on what LOOKS like a fresh, unfolded Finset
   membership** — apparently because an EARLIER `simp only` call on the
   same goal (here, the one right after `rw [hM, hSd]` before the
   `constructor`) already recursively unfolds nested `∀`-bound
   memberships too, so by the time execution reaches a narrower branch,
   the hypothesis/goal is already in fully-unfolded conjunction form and
   a repeat `simp only` with the same lemma set is a genuine no-op. Fix:
   wrap such calls in `try simp only [...]` when their necessity is
   uncertain (unfolding already done vs. still needed) rather than
   guessing — `try` accepts either outcome, and the downstream tactics
   (which already assumed the unfolded shape) work either way.
-/

theorem erdos647_rem_bound_squarefree :
    ∀ (d X : ℕ), Squarefree d → d.primeFactors.Nonempty →
      |(((Finset.Icc 1 X).filter (fun N => d ∣ (210*N-1)*(315*N-1)*(420*N-1)*(630*N-1)*(840*N-1)*(1260*N-1)*(2520*N-1))).card : ℝ)
        - (((Finset.range d).filter (fun r => ∀ p ∈ Nat.primeFactors d, r%p ∈ (Finset.range p).filter (fun s => (210*s)%p=1 ∨ (315*s)%p=1 ∨ (420*s)%p=1 ∨ (630*s)%p=1 ∨ (840*s)%p=1 ∨ (1260*s)%p=1 ∨ (2520*s)%p=1))).card : ℝ) / d * X|
      ≤ (((Finset.range d).filter (fun r => ∀ p ∈ Nat.primeFactors d, r%p ∈ (Finset.range p).filter (fun s => (210*s)%p=1 ∨ (315*s)%p=1 ∨ (420*s)%p=1 ∨ (630*s)%p=1 ∨ (840*s)%p=1 ∨ (1260*s)%p=1 ∨ (2520*s)%p=1))).card : ℝ) := by
  intro d X hd hne
  have hdpos : 0 < d := hd.ne_zero.bot_lt
  have hdpos' : (0:ℝ) < d := by exact_mod_cast hdpos
  have hprod_eq : ∏ p ∈ d.primeFactors, p = d := Nat.prod_primeFactors_of_squarefree hd
  have hsqfree_dvd : ∀ m : ℕ, d ∣ m ↔ ∀ p ∈ d.primeFactors, p ∣ m := by
    intro m
    constructor
    · intro hdvd p hp
      exact (Nat.dvd_of_mem_primeFactors hp).trans hdvd
    · intro h
      have h2 : ∀ p ∈ d.primeFactors, Prime p := fun p hp => (Nat.prime_of_mem_primeFactors hp).prime
      have hprod : ∏ p ∈ d.primeFactors, p ∣ m := Finset.prod_primes_dvd m h2 h
      rwa [hprod_eq] at hprod
  have hbridge : ∀ (p N : ℕ), p.Prime → 1 ≤ N → (p ∣ (210*N-1)*(315*N-1)*(420*N-1)*(630*N-1)*(840*N-1)*(1260*N-1)*(2520*N-1) ↔
      ((210*N)%p=1 ∨ (315*N)%p=1 ∨ (420*N)%p=1 ∨ (630*N)%p=1 ∨ (840*N)%p=1 ∨ (1260*N)%p=1 ∨ (2520*N)%p=1)) := by
    intro p N hp hN
    have key : ∀ c : ℕ, 0 < c*N → (p ∣ c*N-1 ↔ (c*N)%p=1) := by
      intro c hcN
      constructor
      · intro hdvd
        obtain ⟨k, hk⟩ := hdvd
        have h1 : c*N = p*k+1 := by omega
        have h2 : p*k+1 = 1+k*p := by ring
        rw [h1, h2, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hp.one_lt]
      · intro hmod
        have h1 : c*N = p*(c*N/p) + (c*N)%p := (Nat.div_add_mod (c*N) p).symm
        rw [hmod] at h1
        exact ⟨c*N/p, by omega⟩
    constructor
    · intro hdvd
      rw [hp.prime.dvd_mul] at hdvd
      rcases hdvd with hd | hd
      · rw [hp.prime.dvd_mul] at hd
        rcases hd with hd | hd
        · rw [hp.prime.dvd_mul] at hd
          rcases hd with hd | hd
          · rw [hp.prime.dvd_mul] at hd
            rcases hd with hd | hd
            · rw [hp.prime.dvd_mul] at hd
              rcases hd with hd | hd
              · left; exact (key 210 (by omega)).mp hd
              · right;left; exact (key 315 (by omega)).mp hd
            · right;right;left; exact (key 420 (by omega)).mp hd
          · right;right;right;left; exact (key 630 (by omega)).mp hd
        · right;right;right;right;left; exact (key 840 (by omega)).mp hd
      · right;right;right;right;right;left; exact (key 1260 (by omega)).mp hd
    · intro h
      rcases h with h|h|h|h|h|h|h
      · exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right ((key 210 (by omega)).mpr h) _) _) _) _) _) _
      · exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_left ((key 315 (by omega)).mpr h) _) _) _) _) _) _
      · exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_left ((key 420 (by omega)).mpr h) _) _) _) _) _
      · exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_left ((key 630 (by omega)).mpr h) _) _) _) _
      · exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_left ((key 840 (by omega)).mpr h) _) _) _
      · exact Dvd.dvd.mul_right (Dvd.dvd.mul_left ((key 1260 (by omega)).mpr h) _) _
      · exact Dvd.dvd.mul_left ((key 2520 (by omega)).mpr h) _
  have hmodhelp : ∀ (p c N : ℕ), (c*N)%p = (c*(N%p))%p := by
    intro p c N
    exact (Nat.mod_modEq N p).symm.mul_left c
  have hmodhelp2 : ∀ (p c N : ℕ), p ∣ d → (c*N)%p = (c*(N%d))%p := by
    intro p c N hpd
    have e1 : N%p = (N%d)%p := by
      have h1 : N%d ≡ N [MOD d] := Nat.mod_modEq N d
      have h2 : N%d ≡ N [MOD p] := h1.of_dvd hpd
      exact h2.symm
    rw [hmodhelp p c N, e1, ← hmodhelp p c (N%d)]
  have hmodhelp3 : ∀ (p c N : ℕ), p ∣ d → (c*((N%d)%p))%p = (c*N)%p :=
    fun p c N hpd => ((hmodhelp2 p c N hpd).trans (hmodhelp p c (N%d))).symm
  have hdisj_iff : ∀ (N p : ℕ), p ∣ d →
      (((210*N)%p=1 ∨ (315*N)%p=1 ∨ (420*N)%p=1 ∨ (630*N)%p=1 ∨ (840*N)%p=1 ∨ (1260*N)%p=1 ∨ (2520*N)%p=1) ↔
       ((210*((N%d)%p))%p=1 ∨ (315*((N%d)%p))%p=1 ∨ (420*((N%d)%p))%p=1 ∨ (630*((N%d)%p))%p=1 ∨ (840*((N%d)%p))%p=1 ∨ (1260*((N%d)%p))%p=1 ∨ (2520*((N%d)%p))%p=1)) := by
    intro N p hpd
    rw [hmodhelp3 p 210 N hpd, hmodhelp3 p 315 N hpd, hmodhelp3 p 420 N hpd, hmodhelp3 p 630 N hpd, hmodhelp3 p 840 N hpd, hmodhelp3 p 1260 N hpd, hmodhelp3 p 2520 N hpd]
  set Sd := (Finset.range d).filter (fun r => ∀ p ∈ Nat.primeFactors d, r%p ∈ (Finset.range p).filter (fun s => (210*s)%p=1 ∨ (315*s)%p=1 ∨ (420*s)%p=1 ∨ (630*s)%p=1 ∨ (840*s)%p=1 ∨ (1260*s)%p=1 ∨ (2520*s)%p=1)) with hSd
  set M := (Finset.Icc 1 X).filter (fun N => d ∣ (210*N-1)*(315*N-1)*(420*N-1)*(630*N-1)*(840*N-1)*(1260*N-1)*(2520*N-1)) with hM
  clear_value Sd M
  have hchar : ∀ (N : ℕ), N ∈ M ↔ (N ∈ Finset.Icc 1 X ∧ N % d ∈ Sd) := by
    intro N
    rw [hM, hSd]
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hNX, hdvd⟩
      have hN1 : 1 ≤ N := (Finset.mem_Icc.mp hNX).1
      refine ⟨hNX, Nat.mod_lt N hdpos, ?_⟩
      intro p hp
      have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hpd : p ∣ d := Nat.dvd_of_mem_primeFactors hp
      have hdvdp : p ∣ (210*N-1)*(315*N-1)*(420*N-1)*(630*N-1)*(840*N-1)*(1260*N-1)*(2520*N-1) := (hsqfree_dvd _).mp hdvd p hp
      have hthis := (hbridge p N hp_prime hN1).mp hdvdp
      try simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨Nat.mod_lt (N%d) hp_prime.pos, (hdisj_iff N p hpd).mp hthis⟩
    · rintro ⟨hNX, _, hSr⟩
      have hN1 : 1 ≤ N := (Finset.mem_Icc.mp hNX).1
      refine ⟨hNX, ?_⟩
      apply (hsqfree_dvd _).mpr
      intro p hp
      have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hpd : p ∣ d := Nat.dvd_of_mem_primeFactors hp
      have hSrp := hSr p hp
      try simp only [Finset.mem_filter, Finset.mem_range] at hSrp
      exact (hbridge p N hp_prime hN1).mpr ((hdisj_iff N p hpd).mpr hSrp.2)
  have hMeq : M = Sd.biUnion (fun r => (Finset.Icc 1 X).filter (fun N => N % d = r)) := by
    ext N
    rw [hchar]
    simp only [Finset.mem_biUnion, Finset.mem_filter]
    constructor
    · rintro ⟨hNX, hSr⟩
      exact ⟨N % d, hSr, hNX, rfl⟩
    · rintro ⟨r, hSr, hNX, hNr⟩
      exact ⟨hNX, hNr ▸ hSr⟩
  have hdisj : ∀ r1 ∈ Sd, ∀ r2 ∈ Sd, r1 ≠ r2 → Disjoint ((Finset.Icc 1 X).filter (fun N => N % d = r1)) ((Finset.Icc 1 X).filter (fun N => N % d = r2)) := by
    intro r1 _ r2 _ hne'
    apply Finset.disjoint_left.mpr
    intro N hN1 hN2
    simp only [Finset.mem_filter] at hN1 hN2
    exact hne' (hN1.2.symm.trans hN2.2)
  have hMcard : M.card = ∑ r ∈ Sd, ((Finset.Icc 1 X).filter (fun N => N % d = r)).card := by
    rw [hMeq]
    exact Finset.card_biUnion hdisj
  have hr0 : ∀ r ∈ Sd, r ≠ 0 := by
    intro r hr hreq
    rw [hreq, hSd] at hr
    try simp only [Finset.mem_filter, Finset.mem_range] at hr
    obtain ⟨p0, hp0⟩ := hne
    have h0 := hr.2 p0 hp0
    try simp only [Finset.mem_filter, Finset.mem_range] at h0
    have hz : (0:ℕ) % p0 = 0 := Nat.zero_mod p0
    rw [hz] at h0
    simp only [Nat.mul_zero, Nat.zero_mod] at h0
    rcases h0 with ⟨_, h|h|h|h|h|h|h⟩ <;> omega
  have hub : ∀ r ∈ Sd, ((Finset.Icc 1 X).filter (fun N => N % d = r)).card ≤ X / d + 1 := by
    intro r hr
    have hr' : r ∈ Finset.range d := by rw [hSd] at hr; exact (Finset.mem_filter.mp hr).1
    have hrlt : r < d := Finset.mem_range.mp hr'
    have hcard : ((Finset.Icc 1 X).filter (fun N => N % d = r)).card ≤ (Finset.range (X/d+1)).card := by
      apply Finset.card_le_card_of_injOn (fun N => N / d) (t := Finset.range (X/d+1))
      · intro N hN
        have hN' := Finset.mem_filter.mp (Finset.mem_coe.mp hN)
        simp only [Finset.mem_coe, Finset.mem_range]
        have hle : N / d ≤ X / d := Nat.div_le_div_right (Finset.mem_Icc.mp hN'.1).2
        omega
      · intro N1 hN1 N2 hN2 heq
        have heq' : N1 / d = N2 / d := heq
        have hN1' := Finset.mem_filter.mp (Finset.mem_coe.mp hN1)
        have hN2' := Finset.mem_filter.mp (Finset.mem_coe.mp hN2)
        have h1 : d * (N1 / d) + r = N1 := by rw [← hN1'.2]; exact Nat.div_add_mod N1 d
        have h2 : d * (N2 / d) + r = N2 := by rw [← hN2'.2]; exact Nat.div_add_mod N2 d
        rw [← h1, ← h2, heq']
    rwa [Finset.card_range] at hcard
  have hlb : ∀ r ∈ Sd, X / d ≤ ((Finset.Icc 1 X).filter (fun N => N % d = r)).card := by
    intro r hr
    have hr' : r ∈ Finset.range d := by rw [hSd] at hr; exact (Finset.mem_filter.mp hr).1
    have hrlt : r < d := Finset.mem_range.mp hr'
    have hrne : r ≠ 0 := hr0 r hr
    have hr1 : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr hrne
    have hsub : (Finset.range (X/d)).image (fun k => r + k*d) ⊆ (Finset.Icc 1 X).filter (fun N => N % d = r) := by
      intro N hN
      simp only [Finset.mem_image, Finset.mem_range] at hN
      obtain ⟨k, hk, hNeq⟩ := hN
      have hexp : (k+1)*d = k*d + d := by ring
      have h2 : (k+1)*d ≤ X := by
        calc (k+1)*d ≤ (X/d)*d := Nat.mul_le_mul_right d (by omega)
          _ ≤ X := Nat.div_mul_le_self X d
      simp only [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      rw [← hNeq, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hrlt]
    have hcardimg : ((Finset.range (X/d)).image (fun k => r + k*d)).card = X/d := by
      rw [Finset.card_image_of_injOn]
      · exact Finset.card_range _
      · intro k1 hk1 k2 hk2 heq
        simp only at heq
        have heq' : k1*d = k2*d := by omega
        exact Nat.eq_of_mul_eq_mul_right hdpos heq'
    calc X/d = ((Finset.range (X/d)).image (fun k => r + k*d)).card := hcardimg.symm
      _ ≤ ((Finset.Icc 1 X).filter (fun N => N % d = r)).card := Finset.card_le_card hsub
  have hsum_ub : ∑ r ∈ Sd, ((Finset.Icc 1 X).filter (fun N => N % d = r)).card ≤ ∑ r ∈ Sd, (X/d+1) := by
    apply Finset.sum_le_sum
    intro r hr
    exact hub r hr
  have hsum_lb : ∑ r ∈ Sd, (X/d) ≤ ∑ r ∈ Sd, ((Finset.Icc 1 X).filter (fun N => N % d = r)).card := by
    apply Finset.sum_le_sum
    intro r hr
    exact hlb r hr
  simp only [Finset.sum_const, smul_eq_mul] at hsum_ub hsum_lb
  have hMlb : Sd.card * (X/d) ≤ M.card := by rw [hMcard]; exact hsum_lb
  have hMub : M.card ≤ Sd.card * (X/d+1) := by rw [hMcard]; exact hsum_ub
  have hXeq : (X:ℝ) = d * (X/d:ℕ) + (X%d:ℕ) := by
    have hXdm := Nat.div_add_mod X d
    exact_mod_cast hXdm.symm
  have hXmodlt : (X%d:ℕ) < (d:ℝ) := by exact_mod_cast Nat.mod_lt X hdpos
  have hSc : (0:ℝ) ≤ (Sd.card:ℝ) := Nat.cast_nonneg _
  have hnuX_lb : (Sd.card : ℝ) * (X/d:ℕ) ≤ (Sd.card:ℝ)/d*X := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hdpos']
    have hle2 : (X/d:ℕ) * (d:ℝ) ≤ (X:ℝ) := by
      have hm : (0:ℝ) ≤ (X%d:ℕ) := Nat.cast_nonneg _
      rw [hXeq]; nlinarith
    calc (Sd.card:ℝ) * (X/d:ℕ) * d = (Sd.card:ℝ) * ((X/d:ℕ) * (d:ℝ)) := by ring
      _ ≤ (Sd.card:ℝ) * X := mul_le_mul_of_nonneg_left hle2 hSc
  have hnuX_ub : (Sd.card:ℝ)/d*X ≤ (Sd.card:ℝ) * (X/d:ℕ) + (Sd.card:ℝ) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hdpos']
    have hbound : (Sd.card:ℝ)*(X%d:ℕ) ≤ (Sd.card:ℝ)*d := mul_le_mul_of_nonneg_left hXmodlt.le hSc
    calc (Sd.card:ℝ) * X = (Sd.card:ℝ)*(d*(X/d:ℕ)+(X%d:ℕ)) := by rw [hXeq]
      _ = (Sd.card:ℝ)*d*(X/d:ℕ) + (Sd.card:ℝ)*(X%d:ℕ) := by ring
      _ ≤ (Sd.card:ℝ)*d*(X/d:ℕ) + (Sd.card:ℝ)*d := by linarith
      _ = ((Sd.card:ℝ) * (X/d:ℕ) + (Sd.card:ℝ)) * d := by ring
  have hcast1 : ((Sd.card:ℝ) * (X/d:ℕ):ℝ) ≤ (M.card:ℝ) := by exact_mod_cast hMlb
  have hcast2 : (M.card:ℝ) ≤ (Sd.card:ℝ) * (X/d:ℕ) + (Sd.card:ℝ) := by
    have hMubcast := hMub
    exact_mod_cast hMubcast
  rw [abs_le]
  constructor
  · linarith [hnuX_ub, hcast1]
  · linarith [hnuX_lb, hcast2]
