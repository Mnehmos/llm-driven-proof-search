# Rung 5 — Structural invariant preserved by a lemma

**Informal problem:** an invariant (parity via `isEven`) plus a lemma that it is
preserved under a structural operation (here `+2`).

**Why this rung:** invariants are the archetypal structural argument — the proof
is about *why* a property is maintained, not about any single value.

**Allowed tactics:** `rfl`, `simp`, `decide`. **native_decide allowed:** no.

**Expected artifact shape:** `SubmitModule` (def + preservation lemma + root).

**Failure mode this rung exposes:** *brute-forcing one value misses the
invariant.* `isEven 4 = true` is a spot check; the mathematical content is the
preservation lemma, which no finite enumeration establishes.
