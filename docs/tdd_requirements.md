# Test-Driven Development (TDD) Requirements

This document outlines the TDD guidelines and expectations for development within this environment. In an AI-assisted workflow, tests are the essential gate that separates generated proposals from trusted state.

## Core Philosophy: Tests Are Reflexes

Tests are not an afterthought; they are the primary mechanism for verifying correctness. When AI can generate code rapidly, the limiting factor is no longer writing the code, but verifying its correctness. 

- **Write Tests First:** Always write your tests before the implementation. The tests define the boundaries and expectations for the AI-generated code.
- **Fail Before Fix:** A test must fail before the implementation is added or a bug is fixed. This proves the test actually catches the intended condition.
- **Tests as a Gate:** Generated code is merely a proposal until the tests pass. Tests provide the structural judgment needed to safely accept AI output.

## Verification of Core Invariants

In complex systems (like the LLM-Driven Proof Search Environment proof core), core invariants must be strictly enforced.

- Define explicit boundaries and invariants for your modules.
- Write tests that aggressively challenge these invariants.
- Include negative fixtures and edge cases to ensure the system handles invalid input or unexpected states gracefully.
- Do not settle for "happy path" coverage. AI-generated code often handles the happy path perfectly but fails on edge cases. Your tests must cover the edge cases.

## The TDD Loop with AI

1. **Human defines intent:** Write the test cases that describe the expected behavior and constraints.
2. **AI proposes implementation:** Allow the AI to generate the implementation to satisfy the tests.
3. **System verifies:** Run the tests. If they pass, the proposal can be considered for review. If they fail, iterate on the implementation.
4. **Human applies final judgment:** Ensure the tests are actually testing the right things and that the code meets architectural standards before committing.
