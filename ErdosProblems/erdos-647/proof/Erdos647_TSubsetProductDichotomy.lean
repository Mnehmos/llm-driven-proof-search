import Mathlib

/-!
# Erdos #647 - t-subset product dichotomy

This generic finite lemma isolates the precise subset-selection input needed
by CRT re-entry.  If at least `t` entries individually satisfy
`(P i)^t < n`, then `t` of them have product below `n`: select `t` good
entries and bound their product by the `t`-th power of their maximum.

Consequently either such a re-entering `t`-subset exists, or fewer than `t`
coordinates satisfy the individual power test.  Positivity of `t` is used to
ensure that the selected set has a maximum.

The constructive selection root was independently verified through the
tracked proof-search pipeline on 2026-07-16:

* preverification `1e75ef7d-0485-4783-a271-72c30ab0b788`
* problem `e11ff87b-6ef0-4467-b49c-537f10bb4b70`
* episode `4ab8fa09-47fc-4155-b825-0f6c83f78393`
* root hash `0ab423d3600367e3ad041fc060fdb842f1faffe219b4e5942ac322a4f7dc1c51`
* outcome `kernel_verified`
-/

/-- At least `t` individually `t`-power-small entries contain a `t`-subset
whose product is smaller than `n`. -/
theorem erdos647_exists_t_subset_product_lt_of_card_le :
    forall (n W t : Nat) (P : Fin W -> Nat),
      0 < t ->
      t <= (Finset.univ.filter (fun i : Fin W => (P i) ^ t < n)).card ->
      exists I : Finset (Fin W),
        I.card = t /\ (∏ i ∈ I, P i) < n := by
  classical
  intro n W t P ht hcard
  let good : Finset (Fin W) :=
    Finset.univ.filter (fun i : Fin W => (P i) ^ t < n)
  have hcard' : t <= good.card := by simpa [good] using hcard
  obtain ⟨I, hIsub, hIcard⟩ := Finset.exists_subset_card_eq hcard'
  have hInonempty : I.Nonempty := Finset.card_pos.mp (by omega)
  have hvalsNonempty : (I.image P).Nonempty := by
    obtain ⟨i, hi⟩ := hInonempty
    exact ⟨P i, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩
  let M : Nat := (I.image P).max' hvalsNonempty
  have hMmem : M ∈ I.image P := by
    dsimp [M]
    exact Finset.max'_mem _ _
  have hMgood : M ^ t < n := by
    obtain ⟨i, hiI, hiM⟩ := Finset.mem_image.mp hMmem
    have hiGood : i ∈ good := hIsub hiI
    have hiPower : (P i) ^ t < n := by
      simpa [good] using hiGood
    rwa [hiM] at hiPower
  refine ⟨I, hIcard, ?_⟩
  calc
    (∏ i ∈ I, P i) <= ∏ i ∈ I, M := by
      apply Finset.prod_le_prod'
      intro i hi
      dsimp [M]
      exact (I.image P).le_max' (P i)
        (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
    _ = M ^ I.card := by simp
    _ = M ^ t := by rw [hIcard]
    _ < n := hMgood

/-- Either a `t`-element product re-enters below `n`, or fewer than `t`
coordinates are individually `t`-power-small. -/
theorem erdos647_t_subset_product_dichotomy :
    forall (n W t : Nat) (P : Fin W -> Nat),
      0 < t ->
      (exists I : Finset (Fin W),
          I.card = t /\ (∏ i ∈ I, P i) < n) \/
        (Finset.univ.filter (fun i : Fin W => (P i) ^ t < n)).card < t := by
  intro n W t P ht
  by_cases hcard :
      t <= (Finset.univ.filter (fun i : Fin W => (P i) ^ t < n)).card
  · left
    exact erdos647_exists_t_subset_product_lt_of_card_le n W t P ht hcard
  · right
    omega
