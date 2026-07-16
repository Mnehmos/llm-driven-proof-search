# ⚠️ KERNEL-VERIFIED FORMAL STATEMENT — FIDELITY NOT YET VERIFIED — Erdos #647 second-layer novelty: large prime factors selected from cofactors across a width-W shifted block are injective.

> This proof establishes:
>
> `forall (n K W : Nat) (q r : Fin W -> Nat),
      K + W <= n ->
      (forall i : Fin W, q i ∣ n - (K + (i : Nat))) ->
      (forall i : Fin W,
        (r i).Prime /\ r i ∣ q i /\ W < r i) ->
      Function.Injective r`
>
> It does **not yet** certify the source claim above.

**Root goal (formal):** `forall (n K W : Nat) (q r : Fin W -> Nat),
      K + W <= n ->
      (forall i : Fin W, q i ∣ n - (K + (i : Nat))) ->
      (forall i : Fin W,
        (r i).Prime /\ r i ∣ q i /\ W < r i) ->
      Function.Injective r`

| Proof soundness | Statement fidelity | Canonical promotion | Training eligibility |
|---|---|---|---|
| VERIFIED | ATTESTED (unsafe_dev_attestation — not reviewed) | BLOCKED | QUARANTINED |

| episode | state | steps | budget left (μ$) | started | finished |
|---|---|---|---|---|---|
| `5f3b332c-a77c-41a3-bbce-1df5cd67c5ec` | terminated (root_proved) | 1 | — | 2026-07-16T20:57:14 | 2026-07-16T20:57:30 |

## Proof tree

- ✅ **root_theorem** : `forall (n K W : Nat) (q r : Fin W -> Nat),
      K + W <= n ->
      (forall i : Fin W, q i ∣ n - (K + (i : Nat))) ->
      (forall i : Fin W,
        (r i).Prime /\ r i ∣ q i /\ W < r i) ->
      Function.Injective r`

## The proof, assembled

```lean
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib

theorem root_theorem : forall (n K W : Nat) (q r : Fin W -> Nat),
      K + W <= n ->
      (forall i : Fin W, q i ∣ n - (K + (i : Nat))) ->
      (forall i : Fin W,
        (r i).Prime /\ r i ∣ q i /\ W < r i) ->
      Function.Injective r := by
have hdistinct : forall (n W k1 k2 q1 q2 r1 r2 : Nat),
      k1 < k2 ->
      k2 < n ->
      k2 - k1 <= W ->
      q1 ∣ n - k1 ->
      q2 ∣ n - k2 ->
      r1.Prime ->
      r1 ∣ q1 ->
      W < r1 ->
      r2.Prime ->
      r2 ∣ q2 ->
      W < r2 ->
      r1 ≠ r2 := by
  intro n W k1 k2 q1 q2 r1 r2 hk12 hk2n hgap hq1 hq2
    hr1prime hr1q1 hr1large hr2prime hr2q2 hr2large heq
  have hr1shift1 : r1 ∣ n - k1 := hr1q1.trans hq1
  have hr1shift2 : r1 ∣ n - k2 := by
    rw [heq]
    exact hr2q2.trans hq2
  have hr1gap : r1 ∣ k2 - k1 := by
    have h := Nat.dvd_sub hr1shift1 hr1shift2
    have hdiff : (n - k1) - (n - k2) = k2 - k1 := by omega
    rwa [hdiff] at h
  have hgapPos : 0 < k2 - k1 := by omega
  have hr1le : r1 <= k2 - k1 := Nat.le_of_dvd hgapPos hr1gap
  omega
intro n K W q r hKW hq hr i j hij
by_contra hne
have hcoe : (i : Nat) ≠ (j : Nat) := by
  intro h
  apply hne
  exact Fin.ext h
rcases lt_or_gt_of_ne hcoe with hijlt | hjilt
· have hjW : (j : Nat) < W := j.isLt
  have hjn : K + (j : Nat) < n := by omega
  have hgap : (K + (j : Nat)) - (K + (i : Nat)) <= W := by omega
  exact hdistinct
    n W (K + (i : Nat)) (K + (j : Nat))
    (q i) (q j) (r i) (r j)
    (by omega) hjn hgap (hq i) (hq j)
    (hr i).1 (hr i).2.1 (hr i).2.2
    (hr j).1 (hr j).2.1 (hr j).2.2 hij
· have hiW : (i : Nat) < W := i.isLt
  have hin : K + (i : Nat) < n := by omega
  have hgap : (K + (i : Nat)) - (K + (j : Nat)) <= W := by omega
  have hne' : r j ≠ r i :=
    hdistinct
      n W (K + (j : Nat)) (K + (i : Nat))
      (q j) (q i) (r j) (r i)
      (by omega) hin hgap (hq j) (hq i)
      (hr j).1 (hr j).2.1 (hr j).2.2
      (hr i).1 (hr i).2.1 (hr i).2.2
  exact hne' hij.symm

```

## How it went — every attempt, in order

| # | obligation | action | detail | verdict |
|---|---|---|---|---|
| 2 | `root_theorem` | solve | `have hdistinct : forall (n W k1 k2 q1 q2 r1 r2 : Nat), ;       k1 < k2 -> ;       k2 < n -> ;       k2 - k1 <= W -> ;       q1 ∣ n - k1 -> ;       q2 ∣ n - k2 -> ;       r1.Prime -> ;       r1 ∣ q1 -> ;       W < r1 -> ;       r2.Prime -> ;       r2 ∣ q2 -> ;       W < r2 -> ;       r1 ≠ r2 := by ;   intro n W k1 k2 q1 q2 r1 r2 hk12 hk2n hgap hq1 hq2 ;     hr1prime hr1q1 hr1large hr2prime hr2q2 hr2large heq ;   have hr1shift1 : r1 ∣ n - k1 := hr1q1.trans hq1 ;   have hr1shift2 : r1 ∣ n - k2 := by ;     rw [heq] ;     exact hr2q2.trans hq2 ;   have hr1gap : r1 ∣ k2 - k1 := by ;     have h := Nat.dvd_sub hr1shift1 hr1shift2 ;     have hdiff : (n - k1) - (n - k2) = k2 - k1 := by omega ;     rwa [hdiff] at h ;   have hgapPos : 0 < k2 - k1 := by omega ;   have hr1le : r1 <= k2 - k1 := Nat.le_of_dvd hgapPos hr1gap ;   omega ; intro n K W q r hKW hq hr i j hij ; by_contra hne ; have hcoe : (i : Nat) ≠ (j : Nat) := by ;   intro h ;   apply hne ;   exact Fin.ext h ; rcases lt_or_gt_of_ne hcoe with hijlt \| hjilt ; · have hjW : (j : Nat) < W := j.isLt ;   have hjn : K + (j : Nat) < n := by omega ;   have hgap : (K + (j : Nat)) - (K + (i : Nat)) <= W := by omega ;   exact hdistinct ;     n W (K + (i : Nat)) (K + (j : Nat)) ;     (q i) (q j) (r i) (r j) ;     (by omega) hjn hgap (hq i) (hq j) ;     (hr i).1 (hr i).2.1 (hr i).2.2 ;     (hr j).1 (hr j).2.1 (hr j).2.2 hij ; · have hiW : (i : Nat) < W := i.isLt ;   have hin : K + (i : Nat) < n := by omega ;   have hgap : (K + (i : Nat)) - (K + (j : Nat)) <= W := by omega ;   have hne' : r j ≠ r i := ;     hdistinct ;       n W (K + (j : Nat)) (K + (i : Nat)) ;       (q j) (q i) (r j) (r i) ;       (by omega) hin hgap (hq j) (hq i) ;       (hr j).1 (hr j).2.1 (hr j).2.2 ;       (hr i).1 (hr i).2.1 (hr i).2.2 ;   exact hne' hij.symm` | ✅ kernel_pass |

## Verification context

- **Environment hash:** `9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d`
- **Import manifest hash:** `aaf21893d520a78dee0787a1bcaf939ee6b922265ff670c272e2e1d450dd29a7`
- **Import manifest:** `["Mathlib.Tactic.Ring","Mathlib.Tactic.NormNum","Mathlib"]`
- **proof_body_redacted:** false

## Integrity

3 hash-chained trajectory events, `605a28497d22…` → `f4cb3e8de1e7…` (GENESIS-anchored). Re-verify anytime with `episode_replay`.
