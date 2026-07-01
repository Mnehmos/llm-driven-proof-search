# ADR 0003: Hash-Chained Trajectory Events

## Status
Accepted

## Context
The RL environment must produce trajectories that are tamper-evident, ensuring that no training runs can be surreptitiously modified post-generation. Additionally, we need to ensure deterministic replay of actions to re-derive the state rather than trusting stored state deltas.

## Decision
1.  **Event Sequence:** Each event gets a monotonic `event_sequence_number` scoped to the `episode_id`. This correctly orders events occurring within the same logical step (e.g., Claimed -> VerificationStarted -> VerificationCompleted -> Committed).
2.  **Canonical Hashing:** All trajectory hashing will use RFC 8785 JSON Canonicalization Scheme (JCS).
3.  **Hash Chain:** Every event stores a `previous_event_hash` and an `event_hash`.
    *   `event_hash = sha256(canonical_json(envelope + payload_hash + previous_event_hash))`
4.  **Replay Mechanism:** Replay will not rebuild state by applying stored state deltas. Replay will:
    *   Load the immutable task.
    *   Create a clean episode.
    *   Read each committed typed action from the event payload.
    *   Route it through the exact same canonical reducer (`advance()` / `step()`) and re-verify Lean.
    *   Assert that the newly derived state matches the trajectory's `state_hash_after`.

## Consequences
*   **Security:** High tamper evidence for dataset integrity.
*   **Performance:** Hashing adds slight CPU overhead, but guarantees replay accuracy.
