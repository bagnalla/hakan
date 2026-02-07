# Repository Guidelines

## Project Structure & Module Organization
- `src/` contains compiler/interpreter modules (`Ast`, `Lexer.x`, `Parser.y`, `Tycheck`, and backends like `JS` and `C`).
- `app/Main.hs` is the CLI entrypoint for `hakan-exe`.
- `test/Spec.hs` is the Haskell test-suite entrypoint (currently lightweight; extend here).
- `hk/` holds sample and regression programs used for manual checks.
- `out/` stores generated backend outputs and runtime assets (`Makefile`, `gc.a`, `closure_compiler.jar`).
- Root scripts `compileJS.sh` and `compileC.sh` compile `.hk` files to backend targets.

## Build, Test, and Development Commands
- `stack build`: build the library/executable and run required generators declared in cabal.
- `stack exec hakan-exe hk/monad.hk`: parse/typecheck and run a program.
- `stack test`: run `hakan-test` from `test/Spec.hs`.
- `./compileJS.sh hk/monad.hk`: emit `out/out.js`, minify it, then run with `make -C out js`.
- `./compileC.sh hk/ctest9.hk`: emit `out/out.c`; run `make -C out c` to compile and execute.

## Coding Style & Naming Conventions
- Target `Haskell2010`; keep changes warning-clean under `-Wall`.
- Follow existing formatting: 2-space indentation for `do` blocks/case branches, aligned patterns when useful.
- Module/file names use `UpperCamelCase` (for example, `Tycheck.hs`); functions/values use `camelCase`.
- Keep compiler passes and backends in focused `src/` modules rather than large multipurpose files.

## Testing Guidelines
- Add unit/property checks in `test/Spec.hs` (QuickCheck scaffolding exists but is mostly commented out).
- Add or update `.hk` regression inputs in `hk/` for parser, typechecker, or backend changes.
- Before opening a PR, run `stack build && stack test` and at least one relevant backend/manual command.
