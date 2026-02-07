# Progress Tracker

## Objective
Track implementation progress from current stability work through backend feature parity (Interpreter, JS backend, C backend).

## Snapshot (2026-02-07)
- Current phase: infrastructure hardening.
- Most recent completed item: backend suite now supports expected runtime-failure checks and validates failing `assert` behavior in both JS and C.
- Known backend gap from current docs/code: C backend does not fully support typeclass-heavy programs.

## Milestones
| ID | Milestone | Status | Exit Criteria |
|---|---|---|---|
| M0 | Regression baseline | Done | `stack test` passes with fixture harness and baseline cases. |
| M1 | Fixture coverage expansion | In Progress | Add parser/typechecker/interpreter regression fixtures for core language features and known bugs (12 cases currently). |
| M2 | Diagnostics quality | Planned | Stable, actionable parse/type errors with fixture assertions on key messages. |
| M3 | JS backend confidence | In Progress | JS fixtures for representative programs; output/behavior checks in CI. |
| M4 | C backend feature parity | In Progress | C backend supports the same targeted language subset as interpreter/JS (including agreed typeclass scope). |
| M5 | Release/CI hardening | Planned | CI runs build + tests + parity checks on every PR. |

## Backend Parity Matrix
Legend: `Done`, `Partial`, `Planned`, `Verify`.

| Feature Area | Interpreter | JS | C | Notes |
|---|---|---|---|---|
| Parse + typecheck pipeline | Done | Done | Done | Shared frontend pipeline. |
| Core lambda/let/app/eval | Done | Done | Done | Covered by backend fixture suite. |
| ADTs + pattern matching | Done | Done | Done | Covered by backend fixture suite. |
| Records | Done | Done | Done | Backend fixtures cover projection and record-pattern destructuring with bindings. |
| Typeclasses | Done | Partial | Partial | C backend is known incomplete for typeclass-heavy code. |
| Assertions/check commands | Done | Partial | Partial | `assert` now runs in JS + C; `check` remains frontend-only. |

## Immediate Next Actions
1. Define the exact parity target for typeclasses in C (full parity vs scoped subset).
2. Add focused backend fixtures for typeclass usages that are expected to be in scope for parity.
3. Decide whether backend behavior for `check` should remain frontend-only or gain runtime equivalents.

## Update Log
- 2026-02-07: Created tracker and seeded milestone state.
- 2026-02-07: Added fixture-driven tests in `test/Spec.hs` with initial cases under `test/fixtures/`.
- 2026-02-07: Expanded fixture suite to 12 cases (pass + fail + expected-error substrings); `stack test` passing.
- 2026-02-07: Fixed non-exhaustive pattern bug in `src/Ast.hs` (`commandTypeRec`/`commandTypeRecM`) exposed by new assert fixture.
- 2026-02-07: Added backend execution fixtures (JS + C) and runner integration in `test/Spec.hs`; `stack test` passing with backend suites.
- 2026-02-07: Observed C parity gap on an imported recursive list case (`length`), kept as follow-up parity work.
- 2026-02-07: Added dedicated expected-fail C parity suite (`test/fixtures/backend_known_fail_c_cases.txt`) so known C mismatches are tracked in CI.
- 2026-02-07: Minimized C mismatch to a small nested recursive-pattern case (`test/fixtures/backend_known_fail_nested_match.hk`); JS correct, C incorrect.
- 2026-02-07: Fixed C backend allocation/pattern codegen bug in `src/C.hs` and promoted nested-match reproducer to green backend suite (`test/fixtures/backend_nested_match.hk`).
- 2026-02-07: Added backend fixtures for `assert`, record projection, and constructor literal-argument pattern predicates (`backend_assert.hk`, `backend_record_proj.hk`, `backend_ctor_literal_args.hk`).
- 2026-02-07: Implemented JS backend handling for `assert` and fixed JS record accessor codegen spacing bug surfaced by new fixture (`src/JS.hs`).
- 2026-02-07: Implemented JS record-pattern bindings (`PRecord`) and added backend record-destruct fixture with variable bindings (`backend_record_destruct_bind.hk`).
- 2026-02-07: Extended backend fixture directives with `EXPECT-JS-STATUS` / `EXPECT-C-STATUS` and added failing-assert runtime fixture (`backend_assert_fail.hk`).
- 2026-02-07: Fixed C backend to include `CAssert` commands in generated `main` and corrected assert failure message format string in `src/C.hs`.
