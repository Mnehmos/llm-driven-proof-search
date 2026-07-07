# ADR 0002: Canonical vs. Episode-Local Storage

## Status
Accepted

## Context
LLM-Driven Proof Search Environment transitions from a synchronous, single-path proof orchestrator to an RL environment where multiple concurrent models (episodes) will attempt to solve the same problem. This requires isolation so one model's failed search doesn't contaminate another model's context or the permanent database.

## Decision
We separate tables into two scopes: **Canonical Storage** (immutable facts and user-approved definitions) and **Episode-Local Storage** (mutable state scoped to a specific episode).

### 1. Canonical Storage
These tables hold the "ground truth" math. They do not have an `episode_id`.
*   `problem_versions`
*   `canonical_verified_lemmas` (promoted from episodes)
*   `canonical_certificates` (promoted from episodes)
*   `approved_formalizations` (user-approved inputs)
*   `schema_migrations`

### 2. Episode-Local Storage
These tables are prefixed or scoped, always containing an `episode_id` column.
*   `episodes`
*   `episode_obligations`
*   `episode_obligation_edges`
*   `episode_proposal_attempts`
*   `episode_verified_lemmas`
*   `episode_budget_ledger`
*   `episode_review_epochs`
*   `episode_review_proposals`
*   `episode_certificate_candidates`
*   `episode_drafts`
*   `episode_formalization_candidates`
*   `episode_fidelity_reviews`
*   `action_requests`
*   `action_attempts`
*   `model_call_leases`
*   `trajectory_events`

### 3. Migration Strategy (v0 to v1)
Since existing v0 records (`obligations`, `verified_lemmas`, etc.) do not have an `episode_id`, we will not indiscriminately bolt an `episode_id` onto them. 
Instead:
1.  **Rename existing tables** to their canonical forms (e.g., `verified_lemmas` -> `canonical_verified_lemmas`) where applicable.
2.  **Create the new episode-local tables** from scratch.
3.  Existing v0 proof runs are treated as legacy canonical data.
4.  No artificial episode IDs will be generated for existing legacy rows.

### 4. Promotion
When an episode reaches a `Terminated` outcome of `Certified`, a separate transaction:
1.  Re-verifies the root proof against the canonical environment.
2.  Copies approved proofs from `episode_verified_lemmas` to `canonical_verified_lemmas`.
3.  Copies the certificate to `canonical_certificates`.

## Consequences
*   **Isolation:** Training runs can operate freely without data corruption.
*   **Database safety:** Legacy data is not destroyed or arbitrarily linked to fake episodes.
*   **Storage cost:** More storage is consumed per attempt (a small price for safety).
