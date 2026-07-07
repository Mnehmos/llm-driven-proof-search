# Erdős #349's integer sub-case — attack plan (COMPLETE)

**The general question (still open):** for which `(t, α) ∈ (0,∞)²` is `⌊tαⁿ⌋`
additively complete (every sufficiently large integer a sum of distinct
terms)? The powers of two show `(1, 2)` works; the general answer is
unknown. Corpus statement: `erdos_349`, `research open`.

**This attack plan's target — now DONE:** the corpus's fully-scoped
already-solved sub-problem, the complete characterization of which
*integer* `(t, α)` pairs are good:
`integer_isGoodPair_iff (t α : ℤ) (ht : 1 ≤ t) (hα : 1 ≤ α) :
IsGoodPair (t:ℝ) (α:ℝ) ↔ t = 1 ∧ α = 2`. All four of the corpus's own named
assembly pieces are kernel-verified, and the final iff itself is
kernel-verified, assembled from them. This is a real, bounded,
honestly-scoped result — not the open problem itself, but a genuine theorem
about it, independently reproduced end-to-end through this project's tracked
pipeline.

## The four pieces `integer_isGoodPair_iff` assembles — all DONE

| # | piece | status | this folder |
|---|---|---|---|
| 1 | `(1, 2)` is good | **DONE** | `one_two_isGoodPair`, kernel_verified pass@1 |
| 2 | `α ≤ 1` fails | **DONE** | `alpha_le_one_not_isGoodPair`, kernel_verified pass@1 |
| 3 | integer `t ≥ 2` fails | **DONE** | `int_coeff_ge_two_not_isGoodPair`, kernel_verified pass@1 |
| 4 | `2 < α` fails | **DONE** | `alpha_gt_two_not_isGoodPair`, kernel_verified pass@3; see [alpha-gt-two-proof-sketch.md](alpha-gt-two-proof-sketch.md) |

**Assembly — DONE.** `integer_isGoodPair_iff` itself is kernel_verified
pass@1 (episode `4f28677b-09ba-442a-8543-33e49e021e35`, result
`2635b554-0171-48aa-8fd2-8bfc9f80239a`). See [evidence.md](evidence.md) for
the full verification record.

## How piece 4 was completed

`alpha_gt_two_not_isGoodPair (t α : ℝ) (ht : 0 < t) (hα : 2 < α) : ¬ IsGoodPair t α`
had **no proof sketch in the corpus's own docblock** (unlike pieces 1–3, each
of which had a one- or two-sentence argument written out). The corpus
maintainers themselves route its proof through an external `formal_proof`
link rather than inline it, citing the repository's own 25–50 line
guideline — the same signal that made pieces 1–3 tractable (short docblock
arguments) is absent in the upstream corpus text.

The mathematical content is a genuine gap/growth argument: for `α > 2`, the
terms `⌊tαⁿ⌋` eventually grow fast enough that each new term exceeds the sum
of every term before it (`α > 2` makes the geometric ratio too large for the
running partial sums to ever catch up), which is exactly the classical
obstruction to additive completeness (the same phenomenon that makes e.g.
`3ⁿ` not additively complete, unlike `2ⁿ`). A local prose sketch is recorded
in [alpha-gt-two-proof-sketch.md](alpha-gt-two-proof-sketch.md). That sketch
was submitted through the tracked pipeline and accepted by Lean's kernel on
the third attempt: episode `6c0babf6-d577-4847-a2a5-08d2318b97e5`, result
`d986f456-340c-4fa6-ae95-06304a51eedb`, after two namespace-qualification
repairs (`Filter.Tendsto` and `Filter.atTop`).

## How the final assembly was completed

`integer_isGoodPair_iff` is a case split, mechanical once all four pieces
exist: rule out `α = 1` (piece 2) and `α > 2` (piece 4) to force `α = 2`,
then rule out `t ≥ 2` (piece 3) to force `t = 1`; the converse is piece 1.
Because the tracked pipeline verifies each `problem_version` in isolation
(no cross-problem_version imports), the submitted proof restates all four
pieces as local `have`s inside one `solve` submission rather than
referencing them as separately-registered theorems — the living copy in
`lean-checker/LeanChecker/Erdos/Erdos349.lean` states each piece as its own
top-level theorem for readability, since within a single file they can just
call each other by name. First tracked attempt succeeded (pass@1) — no
format issues, since the `problem_imports: ["Mathlib"]` lesson from earlier
in this project (see [evidence.md](evidence.md)) was applied from the start.

## Milestones — all DONE

**M1 — the initially tractable pieces (DONE).**
`one_two_isGoodPair`, `alpha_le_one_not_isGoodPair`,
`int_coeff_ge_two_not_isGoodPair`, plus the binary-expansion lemma
`exists_finset_sum_two_pow` they build on, plus one extra result outside the
four (`dyadic_two_isGoodPair`) — all kernel_verified pass@1.

**M2 — `alpha_gt_two_not_isGoodPair` (DONE, pass@3).** The gap/growth
argument, formalized as a standalone real-analysis lemma. Full prose sketch:
[alpha-gt-two-proof-sketch.md](alpha-gt-two-proof-sketch.md).

**M3 — assemble `integer_isGoodPair_iff` (DONE, pass@1).** The four pieces
combined into the `Iff` via case split.

**M4 — the general open question.** Out of scope for any near-term session;
`integer_isGoodPair_iff` only settles the integer sub-case, not
`erdos_349` itself, which remains genuinely open. No further milestone is
planned here unless a new, similarly well-scoped sub-target is identified
elsewhere in the corpus.

## Ground rules

- Every claim kernel-verified through the tracked pipeline; partial results
  labeled partial (North-Star reporting discipline, issue #124).
- No upstream PRs until the maintainer says go.
- `integer_isGoodPair_iff` is a real, fully-solved (by others) theorem, now
  independently reproduced end-to-end — still distinct from "Erdős Problem
  #349 is solved" (it is not, and this cluster does not touch that claim).
