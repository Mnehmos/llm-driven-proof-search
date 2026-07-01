# LLM-Native Design Practices

This document defines the best practices for AI-assisted development. It establishes the rules of engagement between the human developer, the AI proposer, and the verifying system.

## Trust AI to Propose, Verify Before Commit

The correct relationship with AI is **controlled delegation**. 

- **The Human Owns Intent:** The human decides what problem is being solved, the constraints, and what success looks like.
- **The Model Generates Proposals:** The AI acts as a fast, creative proposer. It drafts code, tests, schemas, and migrations.
- **The System Verifies:** Tests, linters, schemas, and contract checks form an automated gate. A proposal is not authoritative until it passes the gate.

**Rule:** The model is allowed to be creative before the gate. It is not allowed to be authoritative after the gate. Never accept AI-generated code without structural verification and personal understanding of what it does.

## The Repo is the Memory

The AI cannot propose effectively without context. The repository itself acts as the shared context and operational memory.

- **Schemas as Contracts:** Use explicit schemas (JSON Schema, Zod, OpenAPI) to define contracts. These schemas constrain the AI and make its output checkable.
- **Document the "Why":** Keep `README`s, architecture diagrams, and architectural decision records (ADRs) up to date. The AI uses these to understand the state and constraints of the system.
- **Agent Synch Protocol:** Externalize state continuously. Log bugs, index key files, and leave breadcrumbs so the AI (and future developers) have a continuous understanding of the project's history and current state.

## Git as a Time Machine

When generation is cheap, you must be able to explore safely and revert quickly.

- Commit frequently to capture known-good states.
- If an AI proposal leads down a confusing path, do not manually untangle it. Use Git to step back to the last known-good state and try again with better constraints or tests.
- Treat Git history as a ledger of verified states.

## Avoiding the "Looks Right" Trap

AI models produce confident, plausible output. Plausible wrongness is the most dangerous failure mode. 

- **Do I understand what this does?** Never commit code you cannot explain.
- **What did the model assume?** Look for hidden premises or hallucinations about the production environment.
- **What happens at the edge cases?** Verify that the generated code handles adversarial or unexpected inputs safely.
