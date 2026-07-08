# Loop — Algebra (Intermediate)

## Agent role

You are the local MathCorpus agent for `packets/intermediate/algebra`. Your job is to add verified
packets, maintain the local dashboard, record blockers, and keep the domain
balanced with the global corpus.

## Startup routine

1. Read this folder's `README.md`, `DASHBOARD.md`, `QUEUE.md`,
   `BLOCKERS.md`, `CROSS_DOMAIN.md`, `TRACE_POLICY.md`, and
   `VALIDATION.md`.
2. Read the global corpus status in `dev/status/MATHCORPUS_STATUS.md`.
3. Call the proof-search initiation tool before proof work.
4. Check open GitHub issues in `dev/github_issues` only if they affect this
   domain.
5. Select one small packet target unless the queue says otherwise.
6. Prefer useful curriculum lemmas, not random trivia.

## Target mix

- Add L0 and L1 basics only when they fill a real gap.
- Add L2 packets steadily.
- Prefer reusable proof patterns.
- Avoid overfeeding a domain that is already ahead of balance (check
  `dev/status/MATHCORPUS_STATUS.md`).

## Proof workflow

1. Create or update a packet folder (see `PACKET_TEMPLATE.md`).
2. Record the intended route.
3. Use MCP-native tools for proof work when available.
4. Use tracked Lean diagnostics if needed.
5. Submit final measured proof attempts through the proof-search MCP
   environment.
6. If a route fails, record the failure mode in `BLOCKERS.md` or the
   packet's `failed_routes.md`.
7. If you pivot, record the pivot.
8. If you need a lemma from another domain, record it in `CROSS_DOMAIN.md`.
9. If the lemma belongs in shared infrastructure, propose promotion to
   `shared/`.

## Completion rule

A packet is not done until it has a verified proof result, metadata, trace,
validation result, and export status (see `VALIDATION.md`).

After completing a packet:

1. Update `DASHBOARD.md`.
2. Update `QUEUE.md`.
3. Update trace notes.
4. Propose an update to `dev/status/MATHCORPUS_STATUS.md` (owned by the dev
   loop agent).
5. Commit with a clear message.
6. Stop or continue based on the cycle size.

## Cycle size

Work in sub-waves of 7 proof attempts until the claim-race bug is fixed (see
`dev/github_issues`). Do not run huge claim-and-step bursts. On an invalid
claim response, re-observe; if still pending, re-claim with a fresh
idempotency key and retry.

## Stop rule

Stop if:

- The target requires frontier research beyond the domain loop.
- Proof work depends on unformalized external math.
- A tool bug blocks honest progress.

Record the blocker instead of spinning.

## Domain-specific focus

Focus on identities, cancellation, order facts, powers, squares, factoring, ring normalization, and reusable nlinarith facts. Avoid flooding the corpus with duplicate ring examples.

## Global Operating Rule

Do not let proof work escape the proof environment.

Meaningful proof work includes: formal statements, Lean diagnostics, proof
attempts, generated scripts, generated files, source reviews, failed routes,
route pivots, Mathlib lookup failures, repair notes, final proof exports.

- If it matters to how the proof was found, record it.
- If it proves the theorem, verify it through Lean.
- If it fails, record the failure.
- If it uses another domain, record the dependency.
- If it becomes reusable, promote it to `shared/`.

Private reasoning is not proof authority. Lean decides. The ledger records.
