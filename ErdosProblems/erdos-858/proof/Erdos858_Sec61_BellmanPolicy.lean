/-
Erdős Problem #858 — §6.1, Lemma 6.1 (threshold Bellman policy), the
"Consequently" clause: M(N) = F_N(1) = S_N(K) = M_fr(N).
(Chojecki 2026, "An exact frontier theorem and the asymptotic constant for
Erdős problem #858", §6.1, Lemma 6.1.)

Byte-faithful reconstruction of the kernel-verified root theorem from the
proofsearch MCP episode a7d372c2-f41f-4cb9-8493-ae190b4e8318,
problem_version_id 32440799-ec1d-4101-bee1-3a34f9f916b9.
Outcome: kernel_verified / root_proved.
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash cc635e7755bca93fdf168d89b6478a282b95f1211eaa14b9e2ec731990d4bb55.

CONTEXT. §6.1 gives a purely-analytic (computer-assistance-free) route to
frontier exactness via the optimal-stopping / Bellman viewpoint of Remark 2.5.
For a threshold K, the deterministic threshold policy G_{N,K} continues from a
vertex x while x ≤ K and stops (taking reciprocal weight 1/x) once x > K:
    G_{N,K}(a) = 1/a                       (a > K),
    G_{N,K}(a) = Σ_{b∈ch_N(a)} G_{N,K}(b)  (a ≤ K).
Run from the root this policy selects exactly the first vertices strictly above K
on each root-to-leaf path — the frontier A_N(K) — so G_{N,K}(1) = S_N(K), the
frontier sum. The true subtree optimum F_N (F_N(1) = M(N)) satisfies the SAME
recursion whenever the Bellman continuation set is the initial interval {1,…,K}
(Prop 6.2 / Thm 6.3). Lemma 6.1's "Consequently" clause concludes
    M(N) = F_N(1) = S_N(K) = M_fr(N).

FORMALIZED REACHABLE CORE (conditional-assembly atom, mirroring the campaign's
cor35_max_eq / thm24_value_recursion technique — take the deep combinatorial
conclusion as a hypothesis, verify the assembly). The load-bearing new content
here is the descending-tree-induction UNIQUENESS: two rational functions F, G on
the vertices that both obey the shared stop/continue threshold recursion must
coincide, over any rooted tree whose children map ch strictly increases the
vertex value (b ∈ ch a ⟹ a < b — faithful, since a child is b = a·t with
t > 1 as P⁻(t) > a ≥ 1). Hence F 1 = G 1. Taking the paper's root evaluation
G 1 = S (:= S_N(K), the combinatorial "policy selects exactly A_N(K)" fact) as a
hypothesis yields F 1 = S, i.e. M(N) = S_N(K) = M_fr(N).

Hypotheses (all faithful to Lemma 6.1):
  • hchild : ∀ a, ∀ b ∈ ch a, a < b        (children strictly exceed the parent)
  • hGstop : ∀ a, K < a → G a = 1/a         (policy stop rule)
  • hGcont : ∀ a, a ≤ K → G a = Σ_{b∈ch a} G b  (policy continue rule)
  • hFstop : ∀ a, K < a → F a = 1/a         (F obeys the stop rule)
  • hFcont : ∀ a, a ≤ K → F a = Σ_{b∈ch a} F b  (F obeys the continue rule)
  • hGroot : G 1 = S                          (root evaluation G 1 = S_N(K))
Conclusion: F 1 = S.

PROOF. A helper `key : ∀ d a, K - a ≤ d → F a = G a`, by induction on the
measure d = K - a. This terminates the parent→(strictly larger) child recursion
with NO global bound N: for a > K both functions stop at 1/a; for a ≤ K both
expand over ch a via `Finset.sum_congr`, and every child b > a either stops
(b > K, both 1/b) or has K - b < K - a ≤ d + 1, so the induction hypothesis
applies (the arithmetic K - b ≤ d from a < b ≤ K and K - a ≤ d + 1 is `omega`).
Instantiating `key K 1 (Nat.sub_le K 1)` gives F 1 = G 1; rewriting with hGroot
closes F 1 = S.

Lean note: in this pin `le_of_not_lt` is unavailable; `not_lt.mp` supplies
`a ≤ K` from `¬ K < a`.
-/
import Mathlib

namespace Erdos858

/-- §6.1 Lemma 6.1 ("Consequently" clause), conditional-assembly form: if the
threshold policy `G` and the true subtree optimum `F` both obey the shared
stop (`K < a → · = 1/a`) / continue (`a ≤ K → · = ∑_{b∈ch a} · b`) recursion
over a rooted tree whose children strictly exceed their parent
(`b ∈ ch a → a < b`), and the root policy value is the frontier sum
(`G 1 = S`, i.e. `G_{N,K}(1) = S_N(K)`), then `F 1 = S`
(i.e. `M(N) = F_N(1) = S_N(K) = M_fr(N)`). -/
theorem erdos858_sec61_bellman_policy :
    ∀ (K : ℕ) (F G : ℕ → ℚ) (ch : ℕ → Finset ℕ) (S : ℚ),
      (∀ a, ∀ b ∈ ch a, a < b) →
      (∀ a, K < a → G a = (1 : ℚ) / (a : ℚ)) →
      (∀ a, a ≤ K → G a = ∑ b ∈ ch a, G b) →
      (∀ a, K < a → F a = (1 : ℚ) / (a : ℚ)) →
      (∀ a, a ≤ K → F a = ∑ b ∈ ch a, F b) →
      G 1 = S →
      F 1 = S := by
  intro K F G ch S hchild hGstop hGcont hFstop hFcont hGroot
  have key : ∀ d : ℕ, ∀ a : ℕ, K - a ≤ d → F a = G a := by
    intro d
    induction d with
    | zero =>
      intro a ha
      have hKa : K ≤ a := by omega
      by_cases h : K < a
      · rw [hFstop a h, hGstop a h]
      · have hK : a ≤ K := not_lt.mp h
        rw [hFcont a hK, hGcont a hK]
        apply Finset.sum_congr rfl
        intro b hb
        have hab : a < b := hchild a b hb
        have hbK : K < b := lt_of_le_of_lt hKa hab
        rw [hFstop b hbK, hGstop b hbK]
    | succ d ih =>
      intro a ha
      by_cases h : K < a
      · rw [hFstop a h, hGstop a h]
      · have hK : a ≤ K := not_lt.mp h
        rw [hFcont a hK, hGcont a hK]
        apply Finset.sum_congr rfl
        intro b hb
        have hab : a < b := hchild a b hb
        by_cases hbK : K < b
        · rw [hFstop b hbK, hGstop b hbK]
        · have hbK' : b ≤ K := not_lt.mp hbK
          exact ih b (by omega)
  have huniq : F 1 = G 1 := key K 1 (Nat.sub_le K 1)
  rw [huniq]
  exact hGroot

end Erdos858
