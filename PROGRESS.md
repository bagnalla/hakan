# Progress Tracker

## Objective
Track implementation progress from current stability work through backend feature parity (Interpreter, JS backend, C backend).

## Snapshot (2026-02-07)
- Current phase: infrastructure hardening.
- Most recent completed item: fixture harness now includes backend execution suites (JS + C) with passing baseline parity cases.
- Known backend gap from current docs/code: C backend does not fully support typeclass-heavy programs.

## Milestones
| ID | Milestone | Status | Exit Criteria |
|---|---|---|---|
| M0 | Regression baseline | Done | `stack test` passes with fixture harness and baseline cases. |
| M1 | Fixture coverage expansion | In Progress | Add parser/typechecker/interpreter regression fixtures for core language features and known bugs (12 cases currently). |
| M2 | Diagnostics quality | Planned | Stable, actionable parse/type errors with fixture assertions on key messages. |
| M3 | JS backend confidence | In Progress | JS fixtures for representative programs; output/behavior checks in CI. |
| M4 | C backend feature parity | Planned | C backend supports the same targeted language subset as interpreter/JS (including agreed typeclass scope). |
| M5 | Release/CI hardening | Planned | CI runs build + tests + parity checks on every PR. |

## Backend Parity Matrix
Legend: `Done`, `Partial`, `Planned`, `Verify`.

| Feature Area | Interpreter | JS | C | Notes |
|---|---|---|---|---|
| Parse + typecheck pipeline | Done | Done | Done | Shared frontend pipeline. |
| Core lambda/let/app/eval | Done | Done | Done | Covered by backend fixture suite. |
| ADTs + pattern matching | Done | Done | Done | Covered by backend fixture suite. |
| Records | Done | Verify | Verify | Track with backend fixtures. |
| Typeclasses | Done | Partial | Partial | C backend is known incomplete for typeclass-heavy code. |
| Assertions/check commands | Done | Verify | Verify | Validate emitted backend behavior. |

## Immediate Next Actions
1. Add backend fixtures for records and assertions (currently not in backend green suite).
2. Reproduce and isolate the C mismatch seen on imported recursive list programs (for example `length` from `hk/base`).
3. Define the exact parity target for typeclasses in C (full parity vs scoped subset).

## Update Log
- 2026-02-07: Created tracker and seeded milestone state.
- 2026-02-07: Added fixture-driven tests in `test/Spec.hs` with initial cases under `test/fixtures/`.
- 2026-02-07: Expanded fixture suite to 12 cases (pass + fail + expected-error substrings); `stack test` passing.
- 2026-02-07: Fixed non-exhaustive pattern bug in `src/Ast.hs` (`commandTypeRec`/`commandTypeRecM`) exposed by new assert fixture.
- 2026-02-07: Added backend execution fixtures (JS + C) and runner integration in `test/Spec.hs`; `stack test` passing with backend suites.
- 2026-02-07: Observed C parity gap on an imported recursive list case (`length`), kept as follow-up parity work.
