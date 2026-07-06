# Rung 1 — Finite computational sanity check

**Informal problem:** a closed finite arithmetic fact, e.g. `3 + 4 = 7`.

**Why this rung:** the floor of the ladder — a decidable, small, closed
statement. It exists to confirm the plumbing (problem → episode → step →
kernel verdict) works at all.

**Allowed tactics:** `decide`, `norm_num`, `rfl`. **native_decide allowed:**
**yes** — the statement is genuinely decidable and tiny.

**Expected artifact shape:** single theorem (`Solve`).

**Failure mode this rung exposes:** *native_decide gives false comfort.* Passing
here says nothing about structural math — it is exactly the kind of proof the
rest of the ladder is designed to move beyond. A system that only clears Rung 1
has not been forced into the shape of serious mathematics.
