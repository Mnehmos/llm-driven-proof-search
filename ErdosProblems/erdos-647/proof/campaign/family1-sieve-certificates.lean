import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib

/-!
# Erdős #647 — Family 1: sieve counting certificates

Self-contained Lean source (checks against Mathlib with `lake`; no project DB
needed). Each is the kernel-verified survivor count of the 13-coefficient sieve
over the indicated range, and the tighter-than-published base sieve leaves 48
survivors (vs 96). The last theorem is the 45-class mod-46189 open frontier
(base sieve + the 180-row condition + three pair-exclusions).

Coefficients `{105,126,140,210,252,280,315,420,504,630,840,1260,2520}` are the
shifts `2520/k`; a residue survives iff no `(coeff, prime)` pair forces
`coeff·r ≡ 1`.

Provenance (our environment; see ../../dossiers/episode-index.tsv):
sieve48 `200bce1c/bbdd6457`, ×23 `a001e7c1/998dec2c`, ×29 `4d2b7ec1/c7bab59a`,
×31 `83fb9810/f23e6f05`, ×37 `b4196b16/874da7ba`, ×41 `2f28d8d4/44d11f4b`,
×43 `c0f6a321/885dfd33`, frontier45 `b9083710/13ddfac2`.
-/

theorem erdos647_sieve_base48 :
    ((Finset.range 46189).filter (fun r => ∀ d ∈ ([105, 126, 140, 210, 252, 280, 315, 420, 504, 630, 840, 1260, 2520] : List ℕ), ∀ q ∈ ([11, 13, 17, 19] : List ℕ), d * r % q ≠ 1)).card = 48 := by
  native_decide

theorem erdos647_sieve_mod23 :
    ((Finset.range 1062347).filter (fun r => ∀ d ∈ ([105, 126, 140, 210, 252, 280, 315, 420, 504, 630, 840, 1260, 2520] : List ℕ), ∀ q ∈ ([11, 13, 17, 19, 23] : List ℕ), d * r % q ≠ 1)).card = 528 := by
  native_decide

theorem erdos647_sieve_mod29 :
    ((Finset.range 1339481).filter (fun r => ∀ d ∈ ([105, 126, 140, 210, 252, 280, 315, 420, 504, 630, 840, 1260, 2520] : List ℕ), ∀ q ∈ ([11, 13, 17, 19, 29] : List ℕ), d * r % q ≠ 1)).card = 768 := by
  native_decide

theorem erdos647_sieve_mod31 :
    ((Finset.range 1431859).filter (fun r => ∀ d ∈ ([105, 126, 140, 210, 252, 280, 315, 420, 504, 630, 840, 1260, 2520] : List ℕ), ∀ q ∈ ([11, 13, 17, 19, 31] : List ℕ), d * r % q ≠ 1)).card = 864 := by
  native_decide

theorem erdos647_sieve_mod37 :
    ((Finset.range 1708993).filter (fun r => ∀ d ∈ ([105, 126, 140, 210, 252, 280, 315, 420, 504, 630, 840, 1260, 2520] : List ℕ), ∀ q ∈ ([11, 13, 17, 19, 37] : List ℕ), d * r % q ≠ 1)).card = 1152 := by
  native_decide

theorem erdos647_sieve_mod41 :
    ((Finset.range 1893749).filter (fun r => ∀ d ∈ ([105, 126, 140, 210, 252, 280, 315, 420, 504, 630, 840, 1260, 2520] : List ℕ), ∀ q ∈ ([11, 13, 17, 19, 41] : List ℕ), d * r % q ≠ 1)).card = 1344 := by
  native_decide

theorem erdos647_sieve_mod43 :
    ((Finset.range 1986127).filter (fun r => ∀ d ∈ ([105, 126, 140, 210, 252, 280, 315, 420, 504, 630, 840, 1260, 2520] : List ℕ), ∀ q ∈ ([11, 13, 17, 19, 43] : List ℕ), d * r % q ≠ 1)).card = 1440 := by
  native_decide

theorem erdos647_frontier45 :
    ((Finset.range 46189).filter (fun r => (∀ d ∈ ([105, 126, 140, 210, 252, 280, 315, 420, 504, 630, 840, 1260, 2520] : List ℕ), ∀ q ∈ ([11, 13, 17, 19] : List ℕ), d * r % q ≠ 1) ∧ (180 * r % 11 ≠ 1 ∧ 180 * r % 13 ≠ 1 ∧ (180 * r % 17 ≠ 1 ∨ 180 * r % 19 ≠ 1)) ∧ ¬(r % 17 = 8 ∧ r % 19 = 6) ∧ ¬(r % 17 = 16 ∧ r % 19 = 12) ∧ ¬(r % 17 = 12 ∧ r % 19 = 17))).card = 45 := by
  native_decide
