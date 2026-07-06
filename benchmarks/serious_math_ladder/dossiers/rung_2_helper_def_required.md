# Rung 2 — Helper definition required

**Informal problem:** a claim about a defined object, e.g. `double 2 = 4` where
`double n = n + n`.

**Why this rung:** the statement names an object that does not exist until the
proof introduces it. This is the first rung a bare `Solve` cannot clear.

**Allowed tactics:** `rfl`, `simp`, `norm_num`. **native_decide allowed:** no.

**Expected artifact shape:** `SubmitModule` (one `def` + a root theorem).

**Failure mode this rung exposes:** *Solve alone cannot introduce the required
definition.* An API that only offers single-theorem submission cannot even
state, let alone prove, a claim about a constructed object. This is the rung
that motivated `SubmitModule`.
