import Mathlib

/-!
# Erdős #647 — Layer C: residue-class counting bound

Snapshot of the exact statement + proof term kernel-verified through the
tracked proof-search pipeline on 2026-07-14.

  problem_version_id  515e1234-c98c-4439-ab58-def605b1ed08
  episode_id          4e6cd6b6-67be-4ee9-b0ba-c94f52c729d1
  root_statement_hash 3307106242e4ba7dea1fa0529daeb36303f24588f4608ec6758717f6fd6c2b7a
  outcome             kernel_verified (root_proved)
  import manifest     ["Mathlib.Tactic.Ring", "Mathlib.Tactic.NormNum", "Mathlib"]

Content: the basic elementary floor-counting fact — for `d>0` and a fixed
residue `r<d`, the number of `N ∈ [1,X]` with `N≡r (mod d)` is at most
`⌊X/d⌋+1`. Proven via an injective map `N ↦ N/d` into `Finset.range
(X/d+1)` (each residue class has a UNIQUE quotient-value inverse, since
`N = d·(N/d) + r` is determined by `N/d` once `r` is fixed).

This is the key elementary ingredient for bounding `errSum`/`rem(d)` in
the seven-tuple sieve's `BoundingSieve` instance: `multSum(d)` sums this
kind of count over the `ν(d)·d`-sized root-union residue set mod `d`, and
comparing against the density prediction `ν(d)·X` requires exactly this
per-residue floor-counting discrepancy bound (bounded by `O(1)` per
residue class, hence `O(ν(d)·d) ≤ O(7)` overall for the seven-tuple).

Three small Lean fixes needed (all now-familiar patterns from this
campaign): (1) `Finset.card_le_card_of_injOn`'s target Finset must be
supplied explicitly via `(t := ...)` — `apply` can't infer it from a
`card ≤ X/d+1` goal that isn't syntactically `Finset.card _`; (2) the
`Set.MapsTo`/`Set.InjOn` obligations present membership as `N ∈
↑(s.filter p)` (Set-coerced), needing `Finset.mem_coe.mp` before
`Finset.mem_filter.mp`; (3) the injectivity hypothesis `heq` arrives as
an un-beta-reduced lambda application `(fun N => N/d) N1 = (fun N =>
N/d) N2` — a direct term-mode assignment `have heq' : N1/d = N2/d := heq`
uses defeq to beta-reduce it cleanly (cheaper than fighting `simp`/`show`
against the coerced-Set goal form, which needed `Finset.mem_coe` in the
simp set to actually make progress).
-/

theorem erdos647_residue_count_bound :
    ∀ (d r X : ℕ), 0 < d → r < d → ((Finset.Icc 1 X).filter (fun N => N % d = r)).card ≤ X / d + 1 := by
  intro d r X hd hr
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
