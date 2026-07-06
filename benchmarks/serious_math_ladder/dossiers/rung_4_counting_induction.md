# Rung 4 — Counting identity backed by an inductive lemma

**Informal problem:** a closed-form counting function (`sumTo n = n(n+1)/2`)
with a recurrence/induction lemma, and a finite root instance.

**Why this rung:** counting arguments are where induction becomes unavoidable.
The finite root (`sumTo 3 = 6`) is a sanity check *of* the general lemma, which
is the actual mathematical claim.

**Allowed tactics:** `rfl`, `simp`, `induction`, `omega`. **native_decide
allowed:** no.

**Expected artifact shape:** `SubmitModule` (def + inductive lemma + root).

**Failure mode this rung exposes:** *a finite instance is not the theorem.*
Verifying `sumTo 3 = 6` says nothing about all `n`; only the inductive lemma
does. Brute force cannot reach the general statement.
