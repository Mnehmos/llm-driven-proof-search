# ⚠️ KERNEL-VERIFIED FORMAL STATEMENT — FIDELITY NOT YET VERIFIED — CDC paper / Jaeger 8-flow, contraction reduction step JK-E-2c — the full two-cut contraction pullback (mirrors CDCLean.nowhereZeroGammaFlow_of_contractEdge_of_twoCut, JaegerKilpatrick.lean 686-793, in an abstract merge-map form): given a finite multigraph endAt : E -> Fin 2 -> V, a vertex-merge map q : V -> W collapsing EXACTLY the two ends of e1 (q u = q v iff u = v or {u,v} = {end0 e1, end1 e1}), a 2-edge cut {e1, e2} of S (e1 <> e2), and a nowhere-zero flow psi on the CONTRACTED graph (psi nonzero on non-collapsing survivors, and merged conservation: for every w in W, the sum over survivor edges of (if q(end0 e)=w then psi e) + (if q(end1 e)=w then psi e) is 0), the ORIGINAL graph carries a nowhere-zero ends-form F2^3 flow. Takes the verified step 28 (conservation-across-a-2-cut, 8dda72dc) as a theorem-hypothesis. Proof: set phi e := if e survives then psi e else the common cut value avec (= psi e2 if e2 survives else the all-ones vector); phi is nowhere-zero and phi e1 = phi e2 = avec (e1 collapses so it is a non-survivor). Off-support conservation (step 28's hoff): split the defect at v (v not an end of e1) into survivors and non-survivors; non-survivors contribute 0 (their ends are equal or {a,b}, both != v, using char-2 for the loop subcase); survivors match the merged conservation at q v because for v not in {a,b}, end_i e = v iff q(end_i e) = q v. Then step 28 upgrades to full conservation. The abstract q : V -> W (not a committed Quotient type) keeps this reusable and small; the recursion instantiates W = Quotient (contractEdgeSetoid e1). Pre-flighted clean on the pinned lean-checker (3 iterations: set-lambda beta via simp only, vector-level char-2 funext); statement 1.5KB.

> This proof establishes:
>
> `∀ (V E W : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    [DecidableEq W] (endAt : E → Fin 2 → V) (q : V → W)
    (ψ : E → (Fin 3 → ZMod 2)) (e₁ e₂ : E) (S : Finset V),
  (∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (endAt : E → Fin 2 → V) (φ : E → (Fin 3 → ZMod 2)) (S : Finset V) (e₁ e₂ : E),
    (Finset.univ.filter (fun e => ¬((endAt e 0 ∈ S) ↔ (endAt e 1 ∈ S))) = {e₁, e₂}) →
    e₁ ≠ e₂ →
    φ e₁ = φ e₂ →
    (∀ w : V, w ≠ endAt e₁ 0 → w ≠ endAt e₁ 1 →
      (∑ e, ((if endAt e 0 = w then φ e else 0) +
        (if endAt e 1 = w then φ e else 0))) = 0) →
    ∀ v : V, (∑ e, ((if endAt e 0 = v then φ e else 0) +
      (if endAt e 1 = v then φ e else 0))) = 0) →
  (Finset.univ.filter (fun e => ¬((endAt e 0 ∈ S) ↔ (endAt e 1 ∈ S))) = {e₁, e₂}) →
  e₁ ≠ e₂ →
  (∀ u v : V, q u = q v ↔ (u = v ∨
    (u = endAt e₁ 0 ∧ v = endAt e₁ 1) ∨ (u = endAt e₁ 1 ∧ v = endAt e₁ 0))) →
  (∀ e : E, q (endAt e 0) ≠ q (endAt e 1) → ψ e ≠ 0) →
  (∀ w : W, (∑ e ∈ Finset.univ.filter (fun e => q (endAt e 0) ≠ q (endAt e 1)),
    ((if q (endAt e 0) = w then ψ e else 0) +
      (if q (endAt e 1) = w then ψ e else 0))) = 0) →
  ∃ φ : E → (Fin 3 → ZMod 2),
    (∀ e : E, φ e ≠ 0) ∧
    (∀ v : V, (∑ e, ((if endAt e 0 = v then φ e else 0) +
      (if endAt e 1 = v then φ e else 0))) = 0)`
>
> It does **not yet** certify the source claim above.

**Root goal (formal):** `∀ (V E W : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    [DecidableEq W] (endAt : E → Fin 2 → V) (q : V → W)
    (ψ : E → (Fin 3 → ZMod 2)) (e₁ e₂ : E) (S : Finset V),
  (∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (endAt : E → Fin 2 → V) (φ : E → (Fin 3 → ZMod 2)) (S : Finset V) (e₁ e₂ : E),
    (Finset.univ.filter (fun e => ¬((endAt e 0 ∈ S) ↔ (endAt e 1 ∈ S))) = {e₁, e₂}) →
    e₁ ≠ e₂ →
    φ e₁ = φ e₂ →
    (∀ w : V, w ≠ endAt e₁ 0 → w ≠ endAt e₁ 1 →
      (∑ e, ((if endAt e 0 = w then φ e else 0) +
        (if endAt e 1 = w then φ e else 0))) = 0) →
    ∀ v : V, (∑ e, ((if endAt e 0 = v then φ e else 0) +
      (if endAt e 1 = v then φ e else 0))) = 0) →
  (Finset.univ.filter (fun e => ¬((endAt e 0 ∈ S) ↔ (endAt e 1 ∈ S))) = {e₁, e₂}) →
  e₁ ≠ e₂ →
  (∀ u v : V, q u = q v ↔ (u = v ∨
    (u = endAt e₁ 0 ∧ v = endAt e₁ 1) ∨ (u = endAt e₁ 1 ∧ v = endAt e₁ 0))) →
  (∀ e : E, q (endAt e 0) ≠ q (endAt e 1) → ψ e ≠ 0) →
  (∀ w : W, (∑ e ∈ Finset.univ.filter (fun e => q (endAt e 0) ≠ q (endAt e 1)),
    ((if q (endAt e 0) = w then ψ e else 0) +
      (if q (endAt e 1) = w then ψ e else 0))) = 0) →
  ∃ φ : E → (Fin 3 → ZMod 2),
    (∀ e : E, φ e ≠ 0) ∧
    (∀ v : V, (∑ e, ((if endAt e 0 = v then φ e else 0) +
      (if endAt e 1 = v then φ e else 0))) = 0)`

| Proof soundness | Statement fidelity | Canonical promotion | Training eligibility |
|---|---|---|---|
| VERIFIED | ATTESTED (unsafe_dev_attestation — not reviewed) | BLOCKED | QUARANTINED |

| episode | state | steps | budget left (μ$) | started | finished |
|---|---|---|---|---|---|
| `f85271cd-ae3d-4a78-9fef-ce643d32a2fc` | terminated (root_proved) | 1 | — | 2026-07-11T22:42:42 | 2026-07-11T22:44:16 |

## Proof tree

- ✅ **root_theorem** : `∀ (V E W : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    [DecidableEq W] (endAt : E → Fin 2 → V) (q : V → W)
    (ψ : E → (Fin 3 → ZMod 2)) (e₁ e₂ : E) (S : Finset V),
  (∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (endAt : E → Fin 2 → V) (φ : E → (Fin 3 → ZMod 2)) (S : Finset V) (e₁ e₂ : E),
    (Finset.univ.filter (fun e => ¬((endAt e 0 ∈ S) ↔ (endAt e 1 ∈ S))) = {e₁, e₂}) →
    e₁ ≠ e₂ →
    φ e₁ = φ e₂ →
    (∀ w : V, w ≠ endAt e₁ 0 → w ≠ endAt e₁ 1 →
      (∑ e, ((if endAt e 0 = w then φ e else 0) +
        (if endAt e 1 = w then φ e else 0))) = 0) →
    ∀ v : V, (∑ e, ((if endAt e 0 = v then φ e else 0) +
      (if endAt e 1 = v then φ e else 0))) = 0) →
  (Finset.univ.filter (fun e => ¬((endAt e 0 ∈ S) ↔ (endAt e 1 ∈ S))) = {e₁, e₂}) →
  e₁ ≠ e₂ →
  (∀ u v : V, q u = q v ↔ (u = v ∨
    (u = endAt e₁ 0 ∧ v = endAt e₁ 1) ∨ (u = endAt e₁ 1 ∧ v = endAt e₁ 0))) →
  (∀ e : E, q (endAt e 0) ≠ q (endAt e 1) → ψ e ≠ 0) →
  (∀ w : W, (∑ e ∈ Finset.univ.filter (fun e => q (endAt e 0) ≠ q (endAt e 1)),
    ((if q (endAt e 0) = w then ψ e else 0) +
      (if q (endAt e 1) = w then ψ e else 0))) = 0) →
  ∃ φ : E → (Fin 3 → ZMod 2),
    (∀ e : E, φ e ≠ 0) ∧
    (∀ v : V, (∑ e, ((if endAt e 0 = v then φ e else 0) +
      (if endAt e 1 = v then φ e else 0))) = 0)`

## The proof, assembled

```lean
import Mathlib

theorem root_theorem : ∀ (V E W : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    [DecidableEq W] (endAt : E → Fin 2 → V) (q : V → W)
    (ψ : E → (Fin 3 → ZMod 2)) (e₁ e₂ : E) (S : Finset V),
  (∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (endAt : E → Fin 2 → V) (φ : E → (Fin 3 → ZMod 2)) (S : Finset V) (e₁ e₂ : E),
    (Finset.univ.filter (fun e => ¬((endAt e 0 ∈ S) ↔ (endAt e 1 ∈ S))) = {e₁, e₂}) →
    e₁ ≠ e₂ →
    φ e₁ = φ e₂ →
    (∀ w : V, w ≠ endAt e₁ 0 → w ≠ endAt e₁ 1 →
      (∑ e, ((if endAt e 0 = w then φ e else 0) +
        (if endAt e 1 = w then φ e else 0))) = 0) →
    ∀ v : V, (∑ e, ((if endAt e 0 = v then φ e else 0) +
      (if endAt e 1 = v then φ e else 0))) = 0) →
  (Finset.univ.filter (fun e => ¬((endAt e 0 ∈ S) ↔ (endAt e 1 ∈ S))) = {e₁, e₂}) →
  e₁ ≠ e₂ →
  (∀ u v : V, q u = q v ↔ (u = v ∨
    (u = endAt e₁ 0 ∧ v = endAt e₁ 1) ∨ (u = endAt e₁ 1 ∧ v = endAt e₁ 0))) →
  (∀ e : E, q (endAt e 0) ≠ q (endAt e 1) → ψ e ≠ 0) →
  (∀ w : W, (∑ e ∈ Finset.univ.filter (fun e => q (endAt e 0) ≠ q (endAt e 1)),
    ((if q (endAt e 0) = w then ψ e else 0) +
      (if q (endAt e 1) = w then ψ e else 0))) = 0) →
  ∃ φ : E → (Fin 3 → ZMod 2),
    (∀ e : E, φ e ≠ 0) ∧
    (∀ v : V, (∑ e, ((if endAt e 0 = v then φ e else 0) +
      (if endAt e 1 = v then φ e else 0))) = 0) := by
intro V E W _ _ _ _ _ endAt q ψ e₁ e₂ S h28 hcut he₁₂ hq hψnz hmerged
have hchar2 : ∀ x : ZMod 2, x + x = 0 := by decide
have hab : q (endAt e₁ 0) = q (endAt e₁ 1) :=
  (hq (endAt e₁ 0) (endAt e₁ 1)).mpr (Or.inr (Or.inl ⟨rfl, rfl⟩))
-- the common cut value
set avec : (Fin 3 → ZMod 2) :=
  if q (endAt e₂ 0) ≠ q (endAt e₂ 1) then ψ e₂ else (fun _ => 1) with havec
have havecne : avec ≠ 0 := by
  rw [havec]
  by_cases h : q (endAt e₂ 0) ≠ q (endAt e₂ 1)
  · rw [if_pos h]; exact hψnz e₂ h
  · rw [if_neg h]
    intro hc
    have := congrFun hc 0
    simp at this
set φ : E → (Fin 3 → ZMod 2) :=
  fun e => if q (endAt e 0) ≠ q (endAt e 1) then ψ e else avec with hφ
have hφnz : ∀ e : E, φ e ≠ 0 := by
  intro e
  simp only [hφ]
  by_cases h : q (endAt e 0) ≠ q (endAt e 1)
  · rw [if_pos h]; exact hψnz e h
  · rw [if_neg h]; exact havecne
have hφe₁ : φ e₁ = avec := by
  simp only [hφ]
  rw [if_neg (by rw [not_not]; exact hab)]
have hφe₂ : φ e₂ = avec := by
  simp only [hφ]
  by_cases h : q (endAt e₂ 0) ≠ q (endAt e₂ 1)
  · rw [if_pos h, havec, if_pos h]
  · rw [if_neg h]
have hφeq : φ e₁ = φ e₂ := by rw [hφe₁, hφe₂]
-- off-support conservation
have hoff : ∀ v : V, v ≠ endAt e₁ 0 → v ≠ endAt e₁ 1 →
    (∑ e, ((if endAt e 0 = v then φ e else 0) +
      (if endAt e 1 = v then φ e else 0))) = 0 := by
  intro v hva hvb
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun e => q (endAt e 0) ≠ q (endAt e 1))]
  have hnon : (∑ e ∈ Finset.univ.filter (fun e => ¬ q (endAt e 0) ≠ q (endAt e 1)),
      ((if endAt e 0 = v then φ e else 0) + (if endAt e 1 = v then φ e else 0))) = 0 := by
    apply Finset.sum_eq_zero
    intro e he
    have hqe : q (endAt e 0) = q (endAt e 1) := not_not.mp (Finset.mem_filter.mp he).2
    rcases (hq (endAt e 0) (endAt e 1)).mp hqe with heq | ⟨h0, h1⟩ | ⟨h0, h1⟩
    · rw [heq]
      by_cases hx : endAt e 1 = v
      · rw [if_pos hx]; funext i; exact hchar2 _
      · rw [if_neg hx, add_zero]
    · rw [if_neg (by rw [h0]; exact fun hh => hva hh.symm),
          if_neg (by rw [h1]; exact fun hh => hvb hh.symm), add_zero]
    · rw [if_neg (by rw [h0]; exact fun hh => hvb hh.symm),
          if_neg (by rw [h1]; exact fun hh => hva hh.symm), add_zero]
  rw [hnon, add_zero]
  -- survivor part = merged conservation at q v
  have hsurv : (∑ e ∈ Finset.univ.filter (fun e => q (endAt e 0) ≠ q (endAt e 1)),
      ((if endAt e 0 = v then φ e else 0) + (if endAt e 1 = v then φ e else 0))) =
      (∑ e ∈ Finset.univ.filter (fun e => q (endAt e 0) ≠ q (endAt e 1)),
      ((if q (endAt e 0) = q v then ψ e else 0) +
        (if q (endAt e 1) = q v then ψ e else 0))) := by
    apply Finset.sum_congr rfl
    intro e he
    have hs : q (endAt e 0) ≠ q (endAt e 1) := (Finset.mem_filter.mp he).2
    have hφe : φ e = ψ e := by simp only [hφ]; rw [if_pos hs]
    have hi0 : (endAt e 0 = v) ↔ (q (endAt e 0) = q v) := by
      constructor
      · intro h; rw [h]
      · intro h
        rcases (hq (endAt e 0) v).mp h with heq | ⟨_, hv⟩ | ⟨_, hv⟩
        · exact heq
        · exact absurd hv hvb
        · exact absurd hv hva
    have hi1 : (endAt e 1 = v) ↔ (q (endAt e 1) = q v) := by
      constructor
      · intro h; rw [h]
      · intro h
        rcases (hq (endAt e 1) v).mp h with heq | ⟨_, hv⟩ | ⟨_, hv⟩
        · exact heq
        · exact absurd hv hvb
        · exact absurd hv hva
    rw [hφe]
    congr 1
    · by_cases h : endAt e 0 = v
      · rw [if_pos h, if_pos (hi0.mp h)]
      · rw [if_neg h, if_neg (fun hc => h (hi0.mpr hc))]
    · by_cases h : endAt e 1 = v
      · rw [if_pos h, if_pos (hi1.mp h)]
      · rw [if_neg h, if_neg (fun hc => h (hi1.mpr hc))]
  rw [hsurv]
  exact hmerged (q v)
exact ⟨φ, hφnz, h28 V E endAt φ S e₁ e₂ hcut he₁₂ hφeq hoff⟩

```

## How it went — every attempt, in order

| # | obligation | action | detail | verdict |
|---|---|---|---|---|
| 2 | `root_theorem` | solve | `intro V E W _ _ _ _ _ endAt q ψ e₁ e₂ S h28 hcut he₁₂ hq hψnz hmerged ; have hchar2 : ∀ x : ZMod 2, x + x = 0 := by decide ; have hab : q (endAt e₁ 0) = q (endAt e₁ 1) := ;   (hq (endAt e₁ 0) (endAt e₁ 1)).mpr (Or.inr (Or.inl ⟨rfl, rfl⟩)) ; -- the common cut value ; set avec : (Fin 3 → ZMod 2) := ;   if q (endAt e₂ 0) ≠ q (endAt e₂ 1) then ψ e₂ else (fun _ => 1) with havec ; have havecne : avec ≠ 0 := by ;   rw [havec] ;   by_cases h : q (endAt e₂ 0) ≠ q (endAt e₂ 1) ;   · rw [if_pos h]; exact hψnz e₂ h ;   · rw [if_neg h] ;     intro hc ;     have := congrFun hc 0 ;     simp at this ; set φ : E → (Fin 3 → ZMod 2) := ;   fun e => if q (endAt e 0) ≠ q (endAt e 1) then ψ e else avec with hφ ; have hφnz : ∀ e : E, φ e ≠ 0 := by ;   intro e ;   simp only [hφ] ;   by_cases h : q (endAt e 0) ≠ q (endAt e 1) ;   · rw [if_pos h]; exact hψnz e h ;   · rw [if_neg h]; exact havecne ; have hφe₁ : φ e₁ = avec := by ;   simp only [hφ] ;   rw [if_neg (by rw [not_not]; exact hab)] ; have hφe₂ : φ e₂ = avec := by ;   simp only [hφ] ;   by_cases h : q (endAt e₂ 0) ≠ q (endAt e₂ 1) ;   · rw [if_pos h, havec, if_pos h] ;   · rw [if_neg h] ; have hφeq : φ e₁ = φ e₂ := by rw [hφe₁, hφe₂] ; -- off-support conservation ; have hoff : ∀ v : V, v ≠ endAt e₁ 0 → v ≠ endAt e₁ 1 → ;     (∑ e, ((if endAt e 0 = v then φ e else 0) + ;       (if endAt e 1 = v then φ e else 0))) = 0 := by ;   intro v hva hvb ;   rw [← Finset.sum_filter_add_sum_filter_not Finset.univ ;     (fun e => q (endAt e 0) ≠ q (endAt e 1))] ;   have hnon : (∑ e ∈ Finset.univ.filter (fun e => ¬ q (endAt e 0) ≠ q (endAt e 1)), ;       ((if endAt e 0 = v then φ e else 0) + (if endAt e 1 = v then φ e else 0))) = 0 := by ;     apply Finset.sum_eq_zero ;     intro e he ;     have hqe : q (endAt e 0) = q (endAt e 1) := not_not.mp (Finset.mem_filter.mp he).2 ;     rcases (hq (endAt e 0) (endAt e 1)).mp hqe with heq \| ⟨h0, h1⟩ \| ⟨h0, h1⟩ ;     · rw [heq] ;       by_cases hx : endAt e 1 = v ;       · rw [if_pos hx]; funext i; exact hchar2 _ ;       · rw [if_neg hx, add_zero] ;     · rw [if_neg (by rw [h0]; exact fun hh => hva hh.symm), ;           if_neg (by rw [h1]; exact fun hh => hvb hh.symm), add_zero] ;     · rw [if_neg (by rw [h0]; exact fun hh => hvb hh.symm), ;           if_neg (by rw [h1]; exact fun hh => hva hh.symm), add_zero] ;   rw [hnon, add_zero] ;   -- survivor part = merged conservation at q v ;   have hsurv : (∑ e ∈ Finset.univ.filter (fun e => q (endAt e 0) ≠ q (endAt e 1)), ;       ((if endAt e 0 = v then φ e else 0) + (if endAt e 1 = v then φ e else 0))) = ;       (∑ e ∈ Finset.univ.filter (fun e => q (endAt e 0) ≠ q (endAt e 1)), ;       ((if q (endAt e 0) = q v then ψ e else 0) + ;         (if q (endAt e 1) = q v then ψ e else 0))) := by ;     apply Finset.sum_congr rfl ;     intro e he ;     have hs : q (endAt e 0) ≠ q (endAt e 1) := (Finset.mem_filter.mp he).2 ;     have hφe : φ e = ψ e := by simp only [hφ]; rw [if_pos hs] ;     have hi0 : (endAt e 0 = v) ↔ (q (endAt e 0) = q v) := by ;       constructor ;       · intro h; rw [h] ;       · intro h ;         rcases (hq (endAt e 0) v).mp h with heq \| ⟨_, hv⟩ \| ⟨_, hv⟩ ;         · exact heq ;         · exact absurd hv hvb ;         · exact absurd hv hva ;     have hi1 : (endAt e 1 = v) ↔ (q (endAt e 1) = q v) := by ;       constructor ;       · intro h; rw [h] ;       · intro h ;         rcases (hq (endAt e 1) v).mp h with heq \| ⟨_, hv⟩ \| ⟨_, hv⟩ ;         · exact heq ;         · exact absurd hv hvb ;         · exact absurd hv hva ;     rw [hφe] ;     congr 1 ;     · by_cases h : endAt e 0 = v ;       · rw [if_pos h, if_pos (hi0.mp h)] ;       · rw [if_neg h, if_neg (fun hc => h (hi0.mpr hc))] ;     · by_cases h : endAt e 1 = v ;       · rw [if_pos h, if_pos (hi1.mp h)] ;       · rw [if_neg h, if_neg (fun hc => h (hi1.mpr hc))] ;   rw [hsurv] ;   exact hmerged (q v) ; exact ⟨φ, hφnz, h28 V E endAt φ S e₁ e₂ hcut he₁₂ hφeq hoff⟩` | ✅ kernel_pass |

## Verification context

- **Environment hash:** `9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d`
- **Import manifest hash:** `b71c3c9da913b2ce43017a08a69ccf102d0e4a6d621776a18c3ef555960af7fc`
- **Import manifest:** `["Mathlib"]`
- **proof_body_redacted:** false

## Integrity

3 hash-chained trajectory events, `4e7efaf9c140…` → `fe34087317e4…` (GENESIS-anchored). Re-verify anytime with `episode_replay`.
