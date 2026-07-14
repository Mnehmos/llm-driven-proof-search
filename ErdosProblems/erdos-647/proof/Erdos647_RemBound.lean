import Mathlib

/-!
# Erdős #647 — Layer C: rem(p) bound for the seven-tuple Selberg sieve

Snapshot of the exact statement + proof term kernel-verified through the
tracked proof-search pipeline on 2026-07-14.

  problem_version_id  c50eebb8-ac67-4009-9fa5-532c783cfb32
  episode_id          abcea53f-deb0-4598-851d-c33e1b165463
  root_statement_hash 9f545ba8a6f928b9b149489fb606c983bca0f0303f274939fd5969b99fbf4c8e
  outcome             kernel_verified (root_proved)
  import manifest     ["Mathlib.Tactic.Ring", "Mathlib.Tactic.NormNum", "Mathlib"]

Content: for prime `p` and level `X`, the sieve's actual candidate count
`multSum(p,X) := |{N ∈ [1,X] : p ∣ ∏ᵢ formᵢ(N)}|` (built from the real
`BoundingSieve` support, see `Erdos647_SupportInjective.lean` /
`Erdos647_BoundingSieveInstance.lean`) satisfies

  `|multSum(p,X) - ν(p)·X| ≤ rootUnionCount(p)`

where `ν(p) = rootUnionCount(p)/p` is the density function from
`Erdos647_NuAdmissible.lean`. This is the first genuine per-prime `rem`
bound for the Selberg sieve's `errSum`, combining three previously-proven
pieces: `Erdos647_FormsDivisibleIff.lean` (the Euclid's-lemma bridge
letting `multSum(p,X)` be rewritten as a filter on `N%p ∈ rootUnionSet(p)`)
and both `Erdos647_ResidueCountBound.lean` / `Erdos647_ResidueCountLowerBound.lean`
(per-residue floor-counting: each residue class contributes a count in
`[X/p, X/p+1]`).

Proof shape: `multSum(p,X)` is rewritten as a disjoint `Finset.biUnion`
over `rootUnionSet(p)` (at most 7 residues), so its card is
`∑ r ∈ rootUnionSet(p), |{N : N%p=r}|` (`Finset.card_biUnion`, disjointness
since `N%p` is a function of `N`). Each summand lies in `[X/p, X/p+1]`, so
the sum lies in `[cnt·(X/p), cnt·(X/p)+cnt]` where `cnt = rootUnionCount(p)`.
Separately, `X = p·(X/p) + (X%p)` with `0 ≤ X%p < p` places `ν(p)·X =
cnt/p·X` in the SAME bracket, so the two quantities differ by at most `cnt`.

Two new Lean lessons from this proof (beyond the transport-format lesson
in `Erdos647_FormsDivisibleIff.lean`):

1. **`positivity`/`field_simp`/bare `simp` can hit `maximum recursion
   depth` when the local context has `set`-introduced local definitions**
   (`set S := <huge filter expression> with hS`) — these tactics can try
   to zeta-unfold the `set`-bound value even when only proving something
   about, e.g., `S.card`'s sign. Fix: `clear_value S M` immediately after
   the `set` calls, which keeps the equation hypotheses (`hS`, `hM`) but
   makes `S`/`M` fully opaque local constants — every downstream `simp`/
   `field_simp`/`positivity` call then stays fast, and any place that
   still needs to unfold `S`/`M` does so explicitly via `rw [hS]`/`rw [hM]`.
2. **Chained type ascriptions `(e : T1 : T2)` are a Lean 4 parse error**,
   not silently accepted — `(X/p : ℕ : ℝ)` fails with "unexpected token
   ':'; expected ')'"; the fix is to just write the single ascription
   `(X/p : ℕ)` inside an already-real-typed expression (the coercion to
   `ℝ` is inserted automatically by unification) rather than trying to
   force it explicitly with a second ascription.

Also: `le_div_iff₀`/`div_le_iff₀` only match a goal shaped exactly `a ≤
b/c`/`a/c ≤ b`, not `a ≤ (b/c)*d` — apply `div_mul_eq_mul_div` first to
turn `(b/c)*d` into `(b*d)/c` before those lemmas will fire.
-/

theorem erdos647_rem_bound :
    ∀ (p X : ℕ), p.Prime →
      |(((Finset.Icc 1 X).filter (fun N => p ∣ (210*N-1)*(315*N-1)*(420*N-1)*(630*N-1)*(840*N-1)*(1260*N-1)*(2520*N-1))).card : ℝ)
        - (((Finset.range p).filter (fun r => (210*r)%p=1 ∨ (315*r)%p=1 ∨ (420*r)%p=1 ∨ (630*r)%p=1 ∨ (840*r)%p=1 ∨ (1260*r)%p=1 ∨ (2520*r)%p=1)).card : ℝ) / p * X|
      ≤ (((Finset.range p).filter (fun r => (210*r)%p=1 ∨ (315*r)%p=1 ∨ (420*r)%p=1 ∨ (630*r)%p=1 ∨ (840*r)%p=1 ∨ (1260*r)%p=1 ∨ (2520*r)%p=1)).card : ℝ) := by
  intro p X hp
  have hppos : 0 < p := hp.pos
  have hppos' : (0:ℝ) < p := by exact_mod_cast hppos
  set S := (Finset.range p).filter (fun r => (210*r)%p=1 ∨ (315*r)%p=1 ∨ (420*r)%p=1 ∨ (630*r)%p=1 ∨ (840*r)%p=1 ∨ (1260*r)%p=1 ∨ (2520*r)%p=1) with hS
  set M := (Finset.Icc 1 X).filter (fun N => p ∣ (210*N-1)*(315*N-1)*(420*N-1)*(630*N-1)*(840*N-1)*(1260*N-1)*(2520*N-1)) with hM
  clear_value S M
  have hbridge : ∀ (N : ℕ), 1 ≤ N → (p ∣ (210*N-1)*(315*N-1)*(420*N-1)*(630*N-1)*(840*N-1)*(1260*N-1)*(2520*N-1) ↔
      ((210*N)%p=1 ∨ (315*N)%p=1 ∨ (420*N)%p=1 ∨ (630*N)%p=1 ∨ (840*N)%p=1 ∨ (1260*N)%p=1 ∨ (2520*N)%p=1)) := by
    intro N hN
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
              · rw [hp.prime.dvd_mul] at hd
                rcases hd with hd | hd
                · left; exact (key 210 (by omega)).mp hd
                · right;left; exact (key 315 (by omega)).mp hd
              · right;right;left; exact (key 420 (by omega)).mp hd
            · right;right;right;left; exact (key 630 (by omega)).mp hd
          · right;right;right;right;left; exact (key 840 (by omega)).mp hd
        · right;right;right;right;right;left; exact (key 1260 (by omega)).mp hd
      · right;right;right;right;right;right; exact (key 2520 (by omega)).mp hd
    · intro h
      rcases h with h|h|h|h|h|h|h
      · exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right ((key 210 (by omega)).mpr h) _) _) _) _) _) _
      · exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_left ((key 315 (by omega)).mpr h) _) _) _) _) _) _
      · exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_left ((key 420 (by omega)).mpr h) _) _) _) _) _
      · exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_left ((key 630 (by omega)).mpr h) _) _) _) _
      · exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_left ((key 840 (by omega)).mpr h) _) _) _
      · exact Dvd.dvd.mul_right (Dvd.dvd.mul_left ((key 1260 (by omega)).mpr h) _) _
      · exact Dvd.dvd.mul_left ((key 2520 (by omega)).mpr h) _
  have hmodhelp : ∀ c N : ℕ, (c*N)%p = (c*(N%p))%p := by
    intro c N
    exact (Nat.mod_modEq N p).symm.mul_left c
  have hchar : ∀ (N : ℕ), N ∈ M ↔ (N ∈ Finset.Icc 1 X ∧ N % p ∈ S) := by
    intro N
    rw [hM, hS]
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hNX, hdvd⟩
      have hN1 : 1 ≤ N := (Finset.mem_Icc.mp hNX).1
      refine ⟨hNX, Nat.mod_lt N hppos, ?_⟩
      have hthis := (hbridge N hN1).mp hdvd
      rcases hthis with h|h|h|h|h|h|h
      · left; rw [hmodhelp 210 N] at h; exact h
      · right;left; rw [hmodhelp 315 N] at h; exact h
      · right;right;left; rw [hmodhelp 420 N] at h; exact h
      · right;right;right;left; rw [hmodhelp 630 N] at h; exact h
      · right;right;right;right;left; rw [hmodhelp 840 N] at h; exact h
      · right;right;right;right;right;left; rw [hmodhelp 1260 N] at h; exact h
      · right;right;right;right;right;right; rw [hmodhelp 2520 N] at h; exact h
    · rintro ⟨hNX, _, hSr⟩
      have hN1 : 1 ≤ N := (Finset.mem_Icc.mp hNX).1
      refine ⟨hNX, ?_⟩
      apply (hbridge N hN1).mpr
      rcases hSr with h|h|h|h|h|h|h
      · left; rw [hmodhelp 210 N]; exact h
      · right;left; rw [hmodhelp 315 N]; exact h
      · right;right;left; rw [hmodhelp 420 N]; exact h
      · right;right;right;left; rw [hmodhelp 630 N]; exact h
      · right;right;right;right;left; rw [hmodhelp 840 N]; exact h
      · right;right;right;right;right;left; rw [hmodhelp 1260 N]; exact h
      · right;right;right;right;right;right; rw [hmodhelp 2520 N]; exact h
  have hMeq : M = S.biUnion (fun r => (Finset.Icc 1 X).filter (fun N => N % p = r)) := by
    ext N
    rw [hchar]
    simp only [Finset.mem_biUnion, Finset.mem_filter]
    constructor
    · rintro ⟨hNX, hSr⟩
      exact ⟨N % p, hSr, hNX, rfl⟩
    · rintro ⟨r, hSr, hNX, hNr⟩
      exact ⟨hNX, hNr ▸ hSr⟩
  have hdisj : ∀ r1 ∈ S, ∀ r2 ∈ S, r1 ≠ r2 → Disjoint ((Finset.Icc 1 X).filter (fun N => N % p = r1)) ((Finset.Icc 1 X).filter (fun N => N % p = r2)) := by
    intro r1 _ r2 _ hne
    apply Finset.disjoint_left.mpr
    intro N hN1 hN2
    simp only [Finset.mem_filter] at hN1 hN2
    exact hne (hN1.2.symm.trans hN2.2)
  have hMcard : M.card = ∑ r ∈ S, ((Finset.Icc 1 X).filter (fun N => N % p = r)).card := by
    rw [hMeq]
    exact Finset.card_biUnion hdisj
  have hr0 : ∀ r ∈ S, r ≠ 0 := by
    intro r hr hr0
    rw [hr0] at hr
    simp only [hS, Finset.mem_filter, Finset.mem_range, Nat.mul_zero, Nat.zero_mod] at hr
    rcases hr with ⟨_, h|h|h|h|h|h|h⟩ <;> omega
  have hub : ∀ r ∈ S, ((Finset.Icc 1 X).filter (fun N => N % p = r)).card ≤ X / p + 1 := by
    intro r hr
    have hr' : r ∈ (Finset.range p).filter (fun r => (210*r)%p=1 ∨ (315*r)%p=1 ∨ (420*r)%p=1 ∨ (630*r)%p=1 ∨ (840*r)%p=1 ∨ (1260*r)%p=1 ∨ (2520*r)%p=1) := by rw [← hS]; exact hr
    have hrlt : r < p := Finset.mem_range.mp (Finset.mem_filter.mp hr').1
    have hcard : ((Finset.Icc 1 X).filter (fun N => N % p = r)).card ≤ (Finset.range (X/p+1)).card := by
      apply Finset.card_le_card_of_injOn (fun N => N / p) (t := Finset.range (X/p+1))
      · intro N hN
        have hN' := Finset.mem_filter.mp (Finset.mem_coe.mp hN)
        simp only [Finset.mem_coe, Finset.mem_range]
        have hle : N / p ≤ X / p := Nat.div_le_div_right (Finset.mem_Icc.mp hN'.1).2
        omega
      · intro N1 hN1 N2 hN2 heq
        have heq' : N1 / p = N2 / p := heq
        have hN1' := Finset.mem_filter.mp (Finset.mem_coe.mp hN1)
        have hN2' := Finset.mem_filter.mp (Finset.mem_coe.mp hN2)
        have h1 : p * (N1 / p) + r = N1 := by rw [← hN1'.2]; exact Nat.div_add_mod N1 p
        have h2 : p * (N2 / p) + r = N2 := by rw [← hN2'.2]; exact Nat.div_add_mod N2 p
        rw [← h1, ← h2, heq']
    rwa [Finset.card_range] at hcard
  have hlb : ∀ r ∈ S, X / p ≤ ((Finset.Icc 1 X).filter (fun N => N % p = r)).card := by
    intro r hr
    have hr' : r ∈ (Finset.range p).filter (fun r => (210*r)%p=1 ∨ (315*r)%p=1 ∨ (420*r)%p=1 ∨ (630*r)%p=1 ∨ (840*r)%p=1 ∨ (1260*r)%p=1 ∨ (2520*r)%p=1) := by rw [← hS]; exact hr
    have hrlt : r < p := Finset.mem_range.mp (Finset.mem_filter.mp hr').1
    have hrne : r ≠ 0 := hr0 r hr
    have hr1 : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr hrne
    have hsub : (Finset.range (X/p)).image (fun k => r + k*p) ⊆ (Finset.Icc 1 X).filter (fun N => N % p = r) := by
      intro N hN
      simp only [Finset.mem_image, Finset.mem_range] at hN
      obtain ⟨k, hk, hNeq⟩ := hN
      have hexp : (k+1)*p = k*p + p := by ring
      have h2 : (k+1)*p ≤ X := by
        calc (k+1)*p ≤ (X/p)*p := Nat.mul_le_mul_right p (by omega)
          _ ≤ X := Nat.div_mul_le_self X p
      simp only [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      rw [← hNeq, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hrlt]
    have hcardimg : ((Finset.range (X/p)).image (fun k => r + k*p)).card = X/p := by
      rw [Finset.card_image_of_injOn]
      · exact Finset.card_range _
      · intro k1 hk1 k2 hk2 heq
        simp only at heq
        have heq' : k1*p = k2*p := by omega
        exact Nat.eq_of_mul_eq_mul_right hppos heq'
    calc X/p = ((Finset.range (X/p)).image (fun k => r + k*p)).card := hcardimg.symm
      _ ≤ ((Finset.Icc 1 X).filter (fun N => N % p = r)).card := Finset.card_le_card hsub
  have hsum_ub : ∑ r ∈ S, ((Finset.Icc 1 X).filter (fun N => N % p = r)).card ≤ ∑ r ∈ S, (X/p+1) := by
    apply Finset.sum_le_sum
    intro r hr
    exact hub r hr
  have hsum_lb : ∑ r ∈ S, (X/p) ≤ ∑ r ∈ S, ((Finset.Icc 1 X).filter (fun N => N % p = r)).card := by
    apply Finset.sum_le_sum
    intro r hr
    exact hlb r hr
  simp only [Finset.sum_const, smul_eq_mul] at hsum_ub hsum_lb
  have hMlb : S.card * (X/p) ≤ M.card := by rw [hMcard]; exact hsum_lb
  have hMub : M.card ≤ S.card * (X/p+1) := by rw [hMcard]; exact hsum_ub
  have hXeq : (X:ℝ) = p * (X/p:ℕ) + (X%p:ℕ) := by
    have hXdm := Nat.div_add_mod X p
    exact_mod_cast hXdm.symm
  have hXmodlt : (X%p:ℕ) < (p:ℝ) := by exact_mod_cast Nat.mod_lt X hppos
  have hSc : (0:ℝ) ≤ (S.card:ℝ) := Nat.cast_nonneg _
  have hnuX_lb : (S.card : ℝ) * (X/p:ℕ) ≤ (S.card:ℝ)/p*X := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hppos']
    have hle2 : (X/p:ℕ) * (p:ℝ) ≤ (X:ℝ) := by
      have hm : (0:ℝ) ≤ (X%p:ℕ) := Nat.cast_nonneg _
      rw [hXeq]; nlinarith
    calc (S.card:ℝ) * (X/p:ℕ) * p = (S.card:ℝ) * ((X/p:ℕ) * (p:ℝ)) := by ring
      _ ≤ (S.card:ℝ) * X := mul_le_mul_of_nonneg_left hle2 hSc
  have hnuX_ub : (S.card:ℝ)/p*X ≤ (S.card:ℝ) * (X/p:ℕ) + (S.card:ℝ) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hppos']
    have hbound : (S.card:ℝ)*(X%p:ℕ) ≤ (S.card:ℝ)*p := mul_le_mul_of_nonneg_left hXmodlt.le hSc
    calc (S.card:ℝ) * X = (S.card:ℝ)*(p*(X/p:ℕ)+(X%p:ℕ)) := by rw [hXeq]
      _ = (S.card:ℝ)*p*(X/p:ℕ) + (S.card:ℝ)*(X%p:ℕ) := by ring
      _ ≤ (S.card:ℝ)*p*(X/p:ℕ) + (S.card:ℝ)*p := by linarith
      _ = ((S.card:ℝ) * (X/p:ℕ) + (S.card:ℝ)) * p := by ring
  have hcast1 : ((S.card:ℝ) * (X/p:ℕ):ℝ) ≤ (M.card:ℝ) := by exact_mod_cast hMlb
  have hcast2 : (M.card:ℝ) ≤ (S.card:ℝ) * (X/p:ℕ) + (S.card:ℝ) := by
    have hMubcast := hMub
    exact_mod_cast hMubcast
  rw [abs_le]
  constructor
  · linarith [hnuX_ub, hcast1]
  · linarith [hnuX_lb, hcast2]
