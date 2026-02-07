# Progress Tracker

## Objective
Track implementation progress from current stability work through backend feature parity (Interpreter, JS backend, C backend).

## Snapshot (2026-02-07)
- Current phase: backend parity expansion.
- Most recent completed item: expanded differential fuzz generation with typeclass-backed `Int` scoring calls (dictionary-specialized path) and revalidated with a 20-seed green run.
- Known backend gap from current docs/code: no C-known-fail execution cases; no currently tracked interpreter-vs-backend differential known-fail cases.

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
| Typeclasses | Done | Partial | Partial | Direct calls, via-def usage, higher-order method values, superclass chains, imported hierarchy usage, constrained helper multi-call sites, and imported-module ADT pipeline coverage are in the green backend suite. |
| Assertions/check commands | Done | Partial | Partial | `assert` runs in JS + C; `check` is intentionally compile-time/typecheck-only (no backend runtime semantics). |

## Immediate Next Actions
1. Expand differential corpus coverage toward typeclass-heavy fixtures as interpreter/backend semantics converge.
2. Expand fuzz/property differential coverage toward typeclass dictionaries, records, and imported-module scenarios.
3. Keep `check` compile-time-only; do not add backend runtime behavior.

## Differential Testing Plan
1. Deterministic parity runner:
   Compare interpreter value output with JS/C runtime output on a shared fixture corpus, not only backend-specific expected output directives.
2. Property/fuzz generation:
   Generate typed, terminating programs for a constrained pure subset (no refs/assert side effects), then run interpreter/JS/C and require identical status/output.
3. Failure triage:
   Store minimized repros as fixtures; classify as backend bug vs unsupported feature; keep unsupported cases in known-fail lists with explicit rationale.
4. CI rollout:
   Run deterministic differential suite on every PR; run larger-seed fuzzing nightly with replayable seeds.

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
- 2026-02-07: Added scoped typeclass backend fixtures (`backend_typeclass_via_def.hk`, `backend_typeclass_direct_call.hk`) and updated backend runner so expected error status also accepts compile/build failures.
- 2026-02-07: Added higher-order typeclass backend fixture (`backend_typeclass_higher_order.hk`) to lock in scoped parity for method values passed as function arguments.
- 2026-02-07: Decided `check` remains compile-time/typecheck-only by design (no JS/C runtime emission).
- 2026-02-07: Fixed C typeclass direct-call gap by lambda-lifting `CEval`/`CAssert` terms in `src/LambdaLift.hs`, and promoted `backend_typeclass_direct_call.hk` to green (`EXPECT-C-OUT`).
- 2026-02-07: Added backend fixtures for mixed ADT+typeclass usage (`backend_typeclass_adt_match.hk`) and superclass-constrained class usage (`backend_typeclass_superclass.hk`).
- 2026-02-07: Reproduced a C-only compile crash for class-method use directly inside a match branch and added a tracked known-fail backend fixture (`backend_known_fail_typeclass_match_method.hk`).
- 2026-02-07: Fixed `patternVarTypes` to unwrap `TyConstructor` via `tycon_instantiated` in `src/Ast.hs`, resolving the C compile crash for class-method-in-match.
- 2026-02-07: Promoted class-method-in-match fixture to green backend suite (`backend_typeclass_match_method.hk`) and cleared the C known-fail case list.
- 2026-02-07: Added multi-level superclass backend fixture (`backend_typeclass_multilevel_superclass.hk`) and confirmed JS/C parity.
- 2026-02-07: Added higher-order + ADT typeclass backend fixture (`backend_typeclass_higher_order_adt.hk`) and confirmed JS/C parity.
- 2026-02-07: Added imported-module multi-level hierarchy backend fixture (`backend_import_typeclass_multilevel.hk`) and confirmed JS/C parity.
- 2026-02-07: Added constrained-helper multi-call fixture (`backend_typeclass_poly_helper_calls.hk`); JS passes but C codegen fails (invalid thunk local typing), now tracked in `backend_known_fail_c_cases.txt`.
- 2026-02-07: Fixed C thunk local declaration typing for non-CAF supercombinators in `src/C.hs` and tightened thunk type metadata during lambda lifting in `src/LambdaLift.hs`.
- 2026-02-07: Promoted constrained-helper multi-call fixture (`backend_typeclass_poly_helper_calls.hk`) to green backend suite and removed it from C known-fail tracking.
- 2026-02-07: Added mixed call-shape constrained-helper fixture (`backend_typeclass_poly_helper_partial_layer.hk`) and confirmed JS/C parity.
- 2026-02-07: Added imported-module typeclass+ADT pipeline fixture (`backend_import_typeclass_adt_pipeline.hk`); JS baseline passes but C currently returns `9` vs expected `8`, so it is tracked in `backend_known_fail_c_cases.txt`.
- 2026-02-07: Fixed C `TmMatch` codegen to initialize match result storage before branch dispatch, eliminating uninitialized-result drift and promoting `backend_import_typeclass_adt_pipeline.hk` to `test/fixtures/backend_cases.txt` (removed from known-fail).
- 2026-02-07: Added combined superclass + higher-order + pattern-matching backend fixture (`backend_typeclass_superclass_higher_order_match.hk`) and documented a staged interpreter-vs-JS/C differential testing plan.
- 2026-02-07: Implemented deterministic differential backend suite in `test/Spec.hs` and seeded interpreter-aligned corpus in `test/fixtures/backend_differential_cases.txt`; `stack test` now enforces interpreter-vs-JS-vs-C agreement on that corpus.
- 2026-02-07: Expanded differential corpus across backend fixtures, identified 4 typeclass-heavy interpreter mismatches, and split tracking into green corpus (`backend_differential_cases.txt`) plus explicit known-fail differential corpus (`backend_known_fail_differential_cases.txt`).
- 2026-02-07: Fixed spurious dictionary abstraction on unconstrained declared aliases in `src/Tycheck.hs` (`process_term` constraint pruning for unconstrained declarations) and promoted `backend_typeclass_via_def.hk` + `backend_typeclass_higher_order.hk` into the green differential corpus.
- 2026-02-07: Disambiguated nested `destruct` in remaining differential fixtures by parenthesizing inner matches (`test/fixtures/modules/typeclass_adt_pipeline.hk`, `test/fixtures/backend_typeclass_superclass_higher_order_match.hk`), then promoted both cases to green differential corpus and cleared differential known-fail entries.
- 2026-02-07: Added opt-in seeded differential fuzz harness in `test/Spec.hs` (`HAKAN_DIFF_FUZZ_CASES`, `HAKAN_DIFF_FUZZ_START_SEED`, `HAKAN_DIFF_FUZZ_MAX_DEPTH`, `HAKAN_DIFF_FUZZ_PROGRESS_EVERY`) for a constrained pure expression subset.
- 2026-02-07: Normalized differential backend outcome comparison for boolean stdout forms (`true`/`false` vs `1`/`0`) so cross-backend semantic-equal bool results compare correctly in fuzz runs.
- 2026-02-07: Expanded fuzz generator coverage to include first-class lambdas/applications (typed, terminating subset) in `test/Spec.hs`.
- 2026-02-07: Fixed JS codegen precedence bug by parenthesizing ternary and binary term emission in `src/JS.hs`; differential fuzz seed 9 now matches interpreter/C.
- 2026-02-07: Expanded differential fuzz generation with a small ADT subset (`FuzzOption` with constructor generation and pattern matching) in `test/Spec.hs`.
- 2026-02-07: Validated differential fuzz harness with `HAKAN_DIFF_FUZZ_CASES=20` (progress every 5 seeds); interpreter, JS backend, and C backend all agreed.
- 2026-02-07: Expanded differential fuzz generation with a small record subset (`FuzzRec` literals, projections, and record-pattern destructuring) in `test/Spec.hs`.
- 2026-02-07: Re-ran `HAKAN_DIFF_FUZZ_CASES=20` after record fuzz expansion; differential fuzz remained green across interpreter, JS, and C.
- 2026-02-07: Expanded differential fuzz generation with typeclass-backed score calls (`fuzzScoreInt`) to exercise constrained function specialization in generated programs.
- 2026-02-07: Tried dual monomorphic aliases (`fuzzScoreInt` + `fuzzScoreBool`) and observed generator-program typecheck conflicts; narrowed the fuzz prelude to the stable `Int`-only typeclass path.
- 2026-02-07: Re-ran `HAKAN_DIFF_FUZZ_CASES=20` after typeclass fuzz updates; differential fuzz remained green across interpreter, JS, and C.
