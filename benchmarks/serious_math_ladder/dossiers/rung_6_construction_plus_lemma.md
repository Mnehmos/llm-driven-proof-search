# Rung 6 — Construction + correctness lemma + root theorem

**Informal problem:** a three-part development — a construction (`triple`), a
general correctness lemma about it, and a root instance.

**Why this rung:** this is the shape of a real result: build an object, prove a
general property, then apply it. It exercises multi-item module assembly.

**Allowed tactics:** `rfl`, `simp`, `omega`. **native_decide allowed:** no.

**Expected artifact shape:** `SubmitModule` (≥2 module items + root).

**Failure mode this rung exposes:** *a one-liner is not a development.* An API
that can only submit a single tactic block cannot express construction + lemma +
application as one verified unit.
