# Erdős #647 — complete kernel-verified theorem catalog

> **Living inventory. Problem OPEN.** Last updated 2026-07-13.
>
> This catalogs every kernel-verified theorem produced by the Erdős #647
> campaign in the verifier-gated proof-search environment (~110 total). Each
> row carries the `problem_version_id` — the authoritative lookup key in the
> tracked pipeline — plus the exact root statement and, where recorded, the
> statement hash and episode id. Nothing here resolves the open problem; this
> is the machine-checked scaffolding *around* it.
>
> **How to independently verify / export any entry.** Every tracked problem is
> re-exportable and re-verifiable from its id via the environment's tools:
> `proof_export{episode_id, format}` (dossier — `public_summary` is public-safe
> and never exposes the proof body; `lean` gives bare source), `episode_replay`
> (re-runs the typed actions through the canonical reducer with Lean
> re-verification), or `problem_list` (returns the exact `root_statement_hash`).
> Machine-generated `public_summary` records for the eight headline theorems
> are in [dossiers/public-summaries.md](dossiers/public-summaries.md); full
> Lean proof snapshots for those eight are in [proof/](proof/).
>
> Pinned environment for the whole campaign:
> `environment_hash = 9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d`,
> `import_manifest = ["Mathlib.Tactic.Ring", "Mathlib.Tactic.NormNum", "Mathlib"]`.
> Fidelity basis: `unsafe_dev_attestation` → outcomes are `kernel_verified`
> (never "certified" — statements were authored in-project, not imported from a
> neutral catalog). See [credit.md](credit.md) for attribution and limits.

## Tally by family

| # | Family | Count | What it establishes |
|---|---|---|---|
| 1 | Sieve counting certificates | 9 | the mod-46189 survivor count (48) + 6 CRT refinement tiers + the 45-class frontier, as kernel-checked `Finset` cardinalities |
| 2 | Shift classification theorems | 14 | for each shift `k`, any candidate forces `(n−k)/k` into an explicit prime / prime-power / small-multiple form |
| 3 | Bridging-closure theorems | ~26 | each sieve row *derived from* its classification theorem — the sieve is proven, not just computed |
| 4 | Residue closures (frontier 45→41) | 4 | four of the open residue classes closed unconditionally (direct-full-value + single-overlap) |
| 5 | Novel sub-AP congruence closures | 48 | original-search sub-cell closures (mod 46189·p), unconditional for all N; 37 enumerated below with full data |
| 6 | Theorem 2 (prime-chain reduction) | 3 | first machine-checked proof: every candidate is `8s+8` or `16s+8` with four forced primes |
| 7 | Layer A (quantitative-Mertens infra) | 5 | Abel-summation Mertens identity + antiderivatives + first analytic error bound, toward a Selberg-sieve density bound |
| | **Total** | **~109** | |

---

## Family 1 — sieve counting certificates

Kernel-verified `native_decide` cardinalities. The base sieve (48 survivors
of `Finset.range 46189`) is tighter than the published 96-survivor sieve; each
refinement multiplies the survivor count by the prime tier via CRT.

| problem_version_id | statement (abbrev.) | value |
|---|---|---|
| `200bce1c` | `((Finset.range 46189).filter <13-coeff sieve × {11,13,17,19}>).card` | 48 |
| `a001e7c1` | refined to prime 23, over `Finset.range 1062347` | 528 = 48×11 |
| `4d2b7ec1` | refined to prime 29, over `Finset.range 1339481` | 768 = 48×16 |
| `83fb9810-de02-4278-943e-60335ffc1bb5` | refined to prime 31, over `Finset.range 1431859` | 864 = 48×18 |
| `b4196b16-744d-4785-8120-65810da7d73c` | refined to prime 37, over `Finset.range 1708993` | 1152 = 48×24 |
| `2f28d8d4-2f9f-413c-8d4e-408196b7b59d` | refined to prime 41, over `Finset.range 1893749` | 1344 = 48×28 |
| `c0f6a321-8b28-47c8-9aed-dbc735171c73` | refined to prime 43, over `Finset.range 1986127` | 1440 = 48×30 |
| `b9083710` | `((Finset.range 46189).filter <base ∧ 180-row ∧ 3 pair-exclusions>).card` — the mod-46189 open frontier | 45 |
| `9da16855` | base-48 explicit residue set (used to reconstruct the open list) | — |

The 23/29/31/37/41/43 tiers compose by CRT: combined mod-46189·23·29·31·37·41·43
frontier = 48·11·16·18·24·28·30.

---

## Family 2 — shift classification theorems

For each shift `k ∣ 2520` (plus the reusable characterization lemma), a
necessary condition on any Erdős-647 candidate. Proof template: shift-bound
extraction (`BddAbove`/`ciSup`) + a `p`-adic decomposition of `n−k` +
`isMultiplicative_sigma.map_mul_of_coprime`.

| problem_version_id | shift | forced form of `(n−k)/k` |
|---|---|---|
| `fb7d4bf8` | — | characterization lemma: `2≤r → σ₀ r ≤ 3 → r prime ∨ r = p²` (reusable) |
| `00cfc756` | 1 | `n−1` prime ∨ p² |
| `87ea1d9a` | 2 | prime |
| `323c4801` | 3 | prime (Kitamura's condition) |
| `14a21b69` | 4 | prime |
| `e4397627` | 5 | prime ∨ p² ∨ 5·prime |
| `245e963a` | 6 | prime |
| `0f8dcd94` | 8 | prime ∨ 2·prime |
| `8ed738c7` | 9 | prime ∨ p² ∨ 3·prime ∨ 9·prime |
| `6c5dcfd9` | 10 | prime ∨ p² ∨ 5·prime |
| `b9c90e1d` | 12 | prime |
| `1710efdc-06be-413b-a278-ccac732b032c` | 18 | prime ∨ p² ∨ 3·prime ∨ 9·prime |
| `5a643568-2af3-4bbd-a435-af77a4d0d7e1` | 20 | prime ∨ p² ∨ 5·prime ∨ **exactly 125** (genuine exception at n=2520) |
| `5df5a27e-8f13-47b1-93ab-f7c4bc2ec94b` | 24 | prime ∨ p² ∨ 2·prime ∨ 4·prime |

(Original shift-5 problem `dbd105e7` was found malformed — its budget cannot
force the stated conclusion — and is permanently retired; `e4397627` is the
corrected replacement. The prime-chain base {1,2,3,4,6} being all-prime is what
Theorem 2, Family 6, builds on.)

---

## Family 3 — bridging-closure theorems

Each proves a *sieve row* directly from its classification theorem
(`∀ n N ℓ, … → coeff·N % ℓ ≠ 1`), so the modular reduction rests on proofs, not
on trusting a `native_decide` predicate count. Proven at two bounds: `ℓ ≤ 19`
(legacy) and `ℓ ≤ 29` (current, subsuming, and backing the 23/29 refinement
tiers).

**ℓ ≤ 19 (8):** `de35e7ec` (coeff-2520), `8a65bb51` (1260), `dfb82405` (840),
`ddc951c3` (630), `c0565e84` (420), `efc75f5f` (315), `b542e676` (280),
`a62e9824` (252).

**ℓ ≤ 29 (13):** `90c306f4`, `3aa31e38`, `7f68e7f0`, `e6345707`, `c3337705`
(pure-prime coeffs 2520/1260/840/630/420); `ec6ecc6a`, `9bd67f4d`, `5ba4356c`
(near-prime 315/280/252); `84df59dc` (coeff-210, shift-12);
`b1b996c8-f277-466a-b0ae-991d30979e72` (coeff-105, shift-24);
`b0d5b386-efb0-4e05-b949-1d03f1731356` (coeff-140, shift-18);
`9c93a1d6-97b9-49f8-a05f-a0d813a1428d` (coeff-126, shift-20);
`7e6d5dde` (coeff-504, shift-5).

Every kernel-verified shift classification (1,2,3,4,5,6,8,9,10,12,18,20,24) now
has its sieve row backed by a genuine bridging-closure proof.

---

## Family 4 — residue closures (frontier 45 → 41)

Four of the open mod-46189 residue classes closed unconditionally, matching
Hughes's own 41-class frontier, re-derived and re-proven fresh here.

| problem_version_id | residue `N ≡` (mod 46189) | technique |
|---|---|---|
| `e8e7b8cd-2383-4225-ba89-f96c4534d903` | 39325 | direct-full-value (modulus 2584=2³·17·19, k=16) |
| `15bdd8f4-d89b-49df-a075-4ac84348d87b` | 41470 | single-overlap (modulus 3553=11·17·19, k=11; first `ZMod 8` argument) |
| `49ae1aa9-8f21-4c23-8f93-f37b447bba05` | 40612 | single-overlap (modulus 4199=13·17·19, k=13) |
| `fa7e0a1f-446a-4d01-8074-e7f12ff43ece` | 26884 | single-overlap (modulus 14535=3²·5·17·19, k=45, 11-leaf tree, ~400 lines, passed cold) |

---

## Family 5 — novel sub-AP congruence closures

Original-search sub-cell closures: each excludes `N ≡ r (mod 46189·p)` for one
extra prime `p ∈ {23,29,31,37,41,43}`, **unconditionally for all N** (Hughes's
"6549 sub-AP" species, independently discovered against our own frontier). All
of the form `∀ n N, 84 < n → shift-bound ≤ n+2 → n = 2520N → N % <modulus> = r → False`.
These are sub-cell closures — they do **not** shrink the base-46189 41-class
count (only Family 4 does). 48 total; 37 enumerated here with full data (moduli:
1062347=46189·23, 1339481=46189·29, 1431859=46189·31, 1708993=46189·37,
1893749=46189·41, 1986127=46189·43).

| problem_version_id | modulus | residue r | statement_hash |
|---|---|---|---|
| `9eb4d9b1-2edc-402a-84b9-80c85c27d11a` | 1431859 | 29601 | `c179f131…` |
| `ab996bb5-d9ce-463c-bdb2-fd7b2f4cab1c` | 1062347 | 10582 | `9c952feb…` |
| `294db365-edcd-4c8a-8f4a-cf7ac89895c1` | 1339481 | 32032 | `f3db25fa…` |
| `13cf46f3-13a5-40d9-b8a6-b010eefcab3b` | 1062347 | 24310 | `9c5678c1…` |
| `f11c6255-c5f9-4e95-aa97-63afa2c0e7b3` | 1708993 | 2574 | `d683c8de…` |
| `1308a898-34ac-4444-bc00-f061a876db3f` | 1062347 | 1287 | `1287a14f…` |
| `9477f6c0-a2be-4837-acbf-0b9a1cd60504` | 1431859 | 32461 | `bf122e74…` |
| `664b8f85-f684-405a-86dc-6f5242286163` | 1339481 | 28457 | `b9dc13d1…` |
| `8f7fc915-07d0-4171-9881-02872e14ca51` | 1431859 | 28028 | `8d461524…` |
| `7783f62a-9235-4e77-994e-ea1038abaa44` | 1339481 | 24310 | `4b4c36f4…` |
| `e2c9f240-2206-419e-820f-ee44cefa3c4e` | 1062347 | 18733 | `9f1b9190…` |
| `28152863-aeff-42ba-956f-7bf6d4c4fe2a` | 1708993 | 17160 | `684daf31…` |
| `30251d63-ac66-4c98-bf91-9718ace76a80` | 1062347 | 12155 | `a4f5583f…` |
| `13709089-8e64-4f50-81cd-6bd58c30586e` | 1893749 | 4862 | `b1dcffe5…` |
| `e9718f9f-9f2b-40a3-9f6e-31ba71506eca` | 1708993 | 1287 | `4c197004…` |
| `90b3cc66-f603-4e1a-8f1f-2dc5c71bd7d0` | 1062347 | 17017 | `748d2514…` |
| `2b72c7ce-18ff-4e6b-bc1d-874d054815d6` | 1339481 | 9009 | `1781ba1d…` |
| `e4cc4dbf-224c-4b40-aec1-890ffe4ebbed` | 1986127 | 13013 | `5b165a6f…` |
| `6fbb46d1-4dd4-4546-9239-181867d6f2fd` | 1062347 | 44187 | `d7a78f38…` |
| `b374b2c1-4b3d-428b-8c37-2e97999feb95` | 1062347 | 24453 | `cac30a64…` |
| `023da32c-dd05-40eb-a7db-91a57910529e` | 1062347 | 21164 | `d915c762…` |
| `9dc80f26-a25f-4e19-b4ae-e86651849fef` | 1893749 | 18733 | `a2638963…` |
| `97992573-31bf-4f3a-8e14-a2e46be3ed57` | 1339481 | 12584 | `1df1a8d1…` |
| `04f9df4b-c6d8-42ee-a033-be5080fc14cf` | 1431859 | 10582 | `3b18811c…` |
| `c5812bfb-b227-47c7-8288-78447cf9eb9f` | 1431859 | 6149 | `8bb7ad7a…` |
| `9fd6bd75-4c14-431c-aed4-51d45d1fcb84` | 1431859 | 1716 | `aa784b85…` |
| `40ffae3f-bd5a-4689-b0fd-dd0159395459` | 1986127 | 36608 | `3cf46364…` |
| `5de45935-3e0e-4b4e-97cc-204e7e4dd684` | 1986127 | 24310 | `85143702…` |
| `6abe383e-9487-42ab-8e4f-cdce2297921e` | 1339481 | 18733 | `82f6b86a…` |
| `79dd3f80-370f-4845-af21-5d9cdb231b9b` | 1062347 | 17160 | `cb883b6d…` |
| `1c3943cc-8275-4ec3-876b-d8afb8f9a984` | 1431859 | 5291 | `7b65ad9a…` |
| `ec4c6432-4e72-49ca-a1bb-cf6b9ad65aa3` | 1062347 | 37752 | `b0ef5801…` |
| `c8536661-ba27-42be-92f5-1dbd8d2e8b07` | 1431859 | 31603 | `4c3c83dc…` |
| `a0b6d6ba-a7c2-4cfc-b0d0-ae4f9759766a` | 1708993 | 28028 | `ecd24886…` |
| `727c78de-d147-4509-951d-8d2da6f25638` | 1986127 | 20306 | `19bd4868…` |
| `8f5efd8d-77c2-415a-bdb2-07f832fc414c` | 1062347 | 8151 | `9b784a8a…` |
| `9a615fba-bb1c-4fba-ad67-b78c3dccdaf9` | 1339481 | 35321 | `1c3438a4…` |

Earlier wave-1 sub-AP closures (not re-listed above with full hashes; recorded
in the campaign ledger): `3f98ba86` (5291/×23), `d037ea2a` (36608/×23),
`a109a5af` (13442/×29), `4b799f58` (24453/×29), `02d5a4a3` (9009/×43),
`40988498` (18733/×37, the k=7 discovery closure), and the F-wave
`82b78dec`/`1a283efe`/`32706bae`/`61612470`/`0822d882`. Full residue/modulus
data for any of these is recoverable via `problem_list` or `proof_export`.

**Structural note (proven, not just observed):** these closures — and the whole
congruence-tree technique — provably cannot resolve the 41-class frontier, by
Hughes's "all-avoid obstruction" (each (shift, prime) pair excludes ≤ 1 residue
class mod p; CRT recombines survivors). This campaign extended that negative
result to Theorem 2's prime-chain forms as well. See
[whitepaper.md](whitepaper.md) §3.2 and §3.4.

---

## Family 6 — Theorem 2 (prime-chain reduction)

First machine-checked proof of Hughes's Theorem 2 (paper-sketch only, absent
from his Lean tree). Three composable stages; chaining them gives the two
admissible 4-prime constellations. Full snapshots in [proof/](proof/);
public-summary dossiers in [dossiers/public-summaries.md](dossiers/public-summaries.md).

| problem_version_id | statement | hash |
|---|---|---|
| `1987e20c-6d03-4882-8c20-d0495744d9e9` | `∀ n, 24<n → σ₀(n−1)≤3 → σ₀(n−2)≤4 → ∃ q, q.Prime ∧ n=2q+2 ∧ (n−1).Prime` | `4b5752c6…` |
| `52ff69c0-e7f5-443c-9cc1-14da17c92dd4` | `∀ q, 13≤q → q.Prime → (2q+1).Prime → σ₀(2q−2)≤6 → ∃ p, p.Prime ∧ q=2p+1` | `f940625c…` |
| `513c65fa-b031-479b-aa97-7d39091e7587` | `∀ p, 7≤p → p.Prime → (2p+1).Prime → σ₀(4p−4)≤10 → ∃ s, s.Prime ∧ (p=2s+1 ∨ p=4s+1)` | `068b74eb…` |

Chained: **family A** `n=8s+8` with `s, 2s+1, 4s+3, 8s+7` all prime; **family B**
`n=16s+8` with `s, 4s+1, 8s+3, 16s+7` all prime.

---

## Family 7 — Layer A (quantitative-Mertens infrastructure)

Toward a machine-checked Brun/Selberg-sieve density bound (`|C(x)| ≪ x/(log x)⁷`).
Mathlib has the Selberg sieve core but no quantitative Mertens theorem; this
family builds it. Full snapshots in [proof/](proof/); public-summary dossiers
in [dossiers/public-summaries.md](dossiers/public-summaries.md).

| problem_version_id | statement | hash |
|---|---|---|
| `d584666d-e50d-488d-b459-5d1265a3aadd` | Mertens identity: `∑_{p≤x} 1/p = θ(x)/(x log x) + ∫_{(2,x]} (log t+1)/(t²log²t)·θ(t)` | `9802976a…` |
| `781d4876-55c9-4c3c-9420-602b508771be` | main-term antiderivative: `∫_2^x (log t+1)/(t log²t) = (loglog x − 1/log x) − (loglog 2 − 1/log 2)` | `513062ca…` |
| `1fc1ab2d-de49-4660-8d7c-8aefeb853a73` | weight integral: `∫_2^x (log t+1)/(t²log²t) = 1/(2log2) − 1/(x log x)` | `a9a3ca28…` |
| `89b0e678-f69b-427d-9e71-9523856a7cab` | power-law comparison: `∫_2^x t⁻² = 1/2 − 1/x` | `cd03a308…` |
| `8bf294a3-c882-4588-9894-e2fbc8ee0edf` | log(t+2) error bound: `∫_2^x (log t+1)log(t+2)/(t²log²t) ≤ 1 + 1/log2` (first analytic inequality) | `935fe429…` |

**In progress** (see [attack-plan.md](attack-plan.md)): the `2√t·log t` error
bound, then assembly into `∑_{p≤x} 1/p ≥ log2·loglog x − C`; then Layers B
(Selberg optimization) and C (7-tuple application).

---

*Counts are honest: "~110" spans the seven families above. The problem itself
remains **open** — no witness, no disproof. What this catalog documents is the
machine-checked scaffolding, dead-ends proven dead, and the live analytic
frontier now under construction.*
