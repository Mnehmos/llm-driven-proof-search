# Rung 3 — Bijection / involution with a correctness lemma

**Informal problem:** a constructed map plus a proof it is its own inverse
(here `swap = not` on `Bool`, with `swap (swap b) = b`).

**Why this rung:** the real content is the *structural lemma* (`swap_involutive`),
not the single spot check. This is the first genuinely structural rung.

**Allowed tactics:** `rfl`, `cases`, `simp`. **native_decide allowed:** no —
the correctness claim is universally quantified over the domain.

**Expected artifact shape:** `SubmitModule` (def + lemma + root).

**Failure mode this rung exposes:** *enumeration is the wrong tool.* Checking one
input by brute force does not establish the involution; the universally-quantified
lemma does. On larger domains finite enumeration blows up or is undecidable.
