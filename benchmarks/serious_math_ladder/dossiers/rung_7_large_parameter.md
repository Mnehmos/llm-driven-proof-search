# Rung 7 — Large / unbounded parameter (finite brute force impossible)

**Informal problem:** a statement quantified over ALL `n` (here `∀ n, n + 0 =
n`; in real use, a theorem over an unbounded parameter).

**Why this rung:** the top of the ladder. The domain is infinite, so
`decide`/`native_decide` cannot enumerate it *in principle*. Only a genuine
argument over the quantifier works.

**Allowed tactics:** `intro`, `simp`, `rfl`, `induction`. **native_decide
allowed:** no.

**Expected artifact shape:** single theorem (`Solve`) or module.

**Failure mode this rung exposes:** *an unbounded parameter defeats decide.*
This is the anti-brute-force rung: any approach that relies on finite
enumeration cannot even begin, which is the whole point of distinguishing
computational from structural proofs.
