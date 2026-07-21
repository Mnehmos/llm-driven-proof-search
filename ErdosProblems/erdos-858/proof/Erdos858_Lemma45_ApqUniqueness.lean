/-
Erdős Problem #858 — Lemma 4.5 connection, `π(a·p·q)=a` uniqueness half (Chojecki 2026).

The largest new-math atom of the Lemma 4.5 connection effort. Given the
gap-bounds B1 (`q<a*p`, `Erdos858_Lemma45_ApqGapBound1.lean`) and B2
(`p<a*q`, `Erdos858_Lemma45_ApqGapBound2.lean`) plus `lemma45_pi_apq_subfact`
(`Erdos858_Lemma45_PiApqSubfact.lean` — no valid `⪯`-step from a base `b`
multiplying by a SMALLER prime), shows: any valid ancestor `b` of `a·p·q`
that is itself a valid child of `a` (`a⪯b`) must equal `a` or `a·p·q` — i.e.
no OTHER intermediate ancestor exists. Combined with the existence half
(`lemma45_apq_existence`, `Erdos858_Lemma45_ApqExistence.lean`) and B1/B2,
this establishes `π(a·p·q)=a` (Lemma 4.5's maximality argument), the
uniqueness component needed to connect `C_N(a)` to `R_N(a)=P_N(a)+Q_N(a)`
for `a>N^{1/4}`.

Proof: cancel `a` from the two `⪯`-witnesses (`b=a*s`, `a*p*q=b*w`) to get
`p*q=s*w` (via `mul_assoc`-bridge lemmas `e1`/`e2`, since the raw `a*p*q`
and `a*(p*q)` bracketings differ syntactically — `Nat.eq_of_mul_eq_mul_left`
needs the `a*(X)` form). Case-split via `Nat.Prime.dvd_mul` on `p∣s*w`
(itself derived from `p∣p*q=s*w`): whether `p∣s` or `p∣w`. Each branch
factors `p*q=s*w` further (cancel `p`) to `q=s'*w` or `q=s*w'`, and `q`'s
primality (`Nat.Prime.eq_one_or_self_of_dvd`) gives `s∈{1,p,q,p*q}`. The
`s=p` and `s=q` sub-cases are refuted via `hsubfact` instantiated at
`b:=a*p` (using B1) / `b:=a*q` (using B2); the `s=1`/`s=p*q` sub-cases give
the two conclusion disjuncts directly.

Uses `proof_format=raw_lean_block`: the proof needs THREE nested
`rcases...with h|h` splits (6 bullets total), which the default
`flat_tactic_sequence` format's bullet-flattening pitfall (banked in
`feedback-lean-bullet-flattening` — bullets on a flattened `;`-chain don't
reliably transition between goals) would break; `raw_lean_block` preserves
genuine indentation-based bullet scoping instead.

Kernel-verified via the proofsearch MCP:
  episode aada006a-3f72-479b-8bcc-15163d97b5df,
  problem_version_id 225a18e0-fb38-4f63-abb6-fb42b12ef36e.
Outcome: kernel_verified / root_kernel_verified (2nd submission — 1st hit a
`rw` pattern-mismatch, treated `a*p*q` [parses `(a*p)*q`] as syntactically
matching `a*(p*q)` when it doesn't [`rw` needs exact syntactic match, no
automatic associativity search], plus two `positivity` failures on `0<a*p`/
`0<a*q` since `positivity` didn't pull `1≤a` from context automatically;
fixed via explicit `mul_assoc`-bridge `have`s and `Nat.mul_pos (by omega) hp.pos`).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 7dd05b7c7d876433c927b333e8e5c7f83ca61b99a1318c9188f43d1f5284752b.

**Lean lessons (new, banked for reuse)**:
(1) `rw [h]` where `h : a*p*q = X` (parsing as `(a*p)*q=X`) will NOT match a
    goal containing `a*(p*q)` (different bracketing) even though they're
    ring-equal — `rw` requires syntactic (not ring-normal) matching. Fix:
    build explicit bridge equations via `(mul_assoc a p q).symm : a*(p*q)=a*p*q`
    and `rw` through those, rather than hoping the target hypothesis's
    bracketing happens to match.
(2) `positivity` does not reliably pull an ambient hypothesis like `1≤a`
    (for a bare variable `a`) into a strict-positivity proof for a PRODUCT
    like `a*p` — it reported "possible to prove nonnegativity" instead.
    Fix: `Nat.mul_pos (by omega) hp.pos` (explicit, using `omega` for the
    `0<a` half from `1≤a` in context, and `.pos` for the prime factor).
-/
import Mathlib

namespace Erdos858

/-- Lemma 4.5 connection, `π(a·p·q)=a` uniqueness half: any `b` with `a⪯b⪯apq`
must equal `a` or `a·p·q`. The hardest new-math atom of the Lemma 4.5
connection — combines B1/B2 with `lemma45_pi_apq_subfact` via a 4-way
divisor case-bash on `p*q=s*w`. -/
theorem lemma45_apq_uniqueness :
    ∀ a p q : ℕ, 1 ≤ a → Nat.Prime p → Nat.Prime q → a < p → p ≤ q →
      q < a * p → p < a * q →
      (∀ b q' : ℕ, 0 < b → Nat.Prime q' → q' < b → ¬ (∃ t : ℕ, b * q' = b * t ∧ ∀ r : ℕ, Nat.Prime r → r ∣ t → b < r)) →
      ∀ b : ℕ, (∃ s : ℕ, b = a * s ∧ ∀ r : ℕ, Nat.Prime r → r ∣ s → a < r) →
        (∃ w : ℕ, a * p * q = b * w ∧ ∀ r : ℕ, Nat.Prime r → r ∣ w → b < r) →
        b = a ∨ b = a * p * q := by
  intro a p q ha hp hq hap hpq hB1 hB2 hsubfact b hab hbn
  obtain ⟨s, hbs, hs⟩ := hab
  obtain ⟨w, hbw0, hw⟩ := hbn
  have hbw : a*p*q = a*s*w := (by rw [hbs] at hbw0; exact hbw0)
  have e1 : a*(p*q) = a*p*q := (mul_assoc a p q).symm
  have e2 : a*(s*w) = a*s*w := (mul_assoc a s w).symm
  have hbw' : a*(p*q) = a*(s*w) := (by rw [e1, e2]; exact hbw)
  have hsw : p*q = s*w := Nat.eq_of_mul_eq_mul_left ha hbw'
  have hpsw : p ∣ s*w := (by rw [← hsw]; exact dvd_mul_right p q)
  rcases (Nat.Prime.dvd_mul hp).mp hpsw with hps | hpw
  · obtain ⟨s', hs'⟩ := hps
    have hqs'w : q = s'*w := (by have h2 : p*q = p*(s'*w) := (by rw [hsw, hs']; ring); exact Nat.eq_of_mul_eq_mul_left hp.pos h2)
    rcases (hq.eq_one_or_self_of_dvd s' ⟨w,hqs'w⟩) with hs'1 | hs'q
    · exfalso
      have hsp : s = p := (by rw [hs', hs'1, mul_one])
      exact hsubfact (a*p) q (Nat.mul_pos (by omega) hp.pos) hq hB1 ⟨w, (by rw [hsp] at hbw; exact hbw), (by have hbap : b = a*p := (by rw [hbs, hsp]); rw [hbap] at hw; exact hw)⟩
    · right
      rw [hbs, hs', hs'q]; ring
  · obtain ⟨w', hw'⟩ := hpw
    have hqsw' : q = s*w' := (by have h3 : p*q = p*(s*w') := (by rw [hsw, hw']; ring); exact Nat.eq_of_mul_eq_mul_left hp.pos h3)
    rcases (hq.eq_one_or_self_of_dvd s ⟨w',hqsw'⟩) with hs1 | hseq
    · left
      rw [hbs, hs1, mul_one]
    · exfalso
      exact hsubfact (a*q) p (Nat.mul_pos (by omega) hq.pos) hp hB2 ⟨w, (by rw [hseq] at hbw; have ee1 : (a*q)*p = a*p*q := (by ring); rw [ee1]; exact hbw), (by have hbaq : b = a*q := (by rw [hbs, hseq]); rw [hbaq] at hw; exact hw)⟩

end Erdos858
