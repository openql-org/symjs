# Contributing to symjs

symjs is a TypeScript port of SymPy (with the mpmath parts it needs). These
rules hold for every change, whether it is written by a person or an agent.

## Checks every change must pass

```sh
pnpm typecheck                                  # tsc --noEmit, no errors
pnpm lint                                       # oxlint --type-aware --deny-warnings, no warnings
pnpm test                                       # every test passes
pnpm coverage                                   # 100% coverage (see below)
pnpm compat                                     # SymPy doctest compatibility, writes compat/REPORT.md
pnpm build && node packages/symjs/scripts/size.mjs --check   # bundle sizes within budget
```

## Test coverage: 100%, no exclusions

- Every source file in `packages/*/src` must reach **100% statements,
  branches, functions and lines** in the full test run (`pnpm coverage`).
- Coverage-ignore comments (`/* v8 ignore */`, `c8 ignore`,
  `istanbul ignore`) and excluding files from the coverage configuration
  are not allowed.
- Code that cannot be reached is removed or restructured, not left
  uncovered. Defensive fallbacks for values that always exist use the
  checked helpers of `packages/symjs/src/core/guard.ts` (`at`, `first`,
  `last`, `defined`, `getOrThrow`, `cast`, `expectType`, `pair`), which
  throw `InvariantError` and are covered by their own tests. Say in the
  commit message why removed code could not be reached.
- A branch that only very expensive input reaches (a huge exponent, a
  25-digit factor, ...) is restructured so that a fast test reaches it, for
  example through an internal parameter or threshold. Each test should run
  in under 2 seconds, and no test may hang.
- A branch that needs a capability symjs does not have yet is preferably
  covered by porting that capability from SymPy. Otherwise the test asserts
  the documented current behaviour (left unevaluated, or
  `NotImplementedError`) and gives SymPy's result in a comment.

## Test files

- Tests mirror the source tree: the tests of `packages/<pkg>/src/<path>/<name>.ts` are in
  `packages/<pkg>/tests/<path>/<name>.test.ts`. A new test goes into the file of the source it
  exercises; names that describe how a test came about (such as `cov-*`) are not used.
- Aspect suffixes are used only when one file would be too large or must stay separate:
  `<name>.sympy.test.ts` for tables replayed from SymPy's test suites, `<name>.isolated.test.ts` for
  tests that must import only some modules.
- Tests that check the public API as a whole stay at the top of `tests/`: `golden`, `fuzz`,
  `exports`, `entries`, `api-report`, `api`, `api-results`, `results`, `regressions`,
  `sympy-extras`, `misc-compat` and `user-extensions` (and `extension.test.ts` in the extend
  package that builds on the base module).

## Expected values come from SymPy

- The reference is SymPy 1.14.0 (and mpmath 1.3.0 for `numeric/`).
  Expected values in tests are obtained by running SymPy or mpmath, never
  by copying what symjs currently prints. SymPy's own test suites
  (`sympy/*/tests`) are a good source of cases.
- Results match SymPy's `str()` output. A result in another form counts as
  compatible only when it is mathematically equal (see
  `compat/equivalence.ts`). A result left unevaluated where SymPy computes
  a value is a failure.
- **Mathematical correctness wins over SymPy's output.** When SymPy is
  wrong (a wrong value, a wrong sign, a claim that fails for some admissible
  value of a symbol), symjs keeps the correct result. The test states
  SymPy's answer and the counterexample in a comment. A SymPy doctest whose
  printed output is wrong is listed with its reason in `SYMPY_ERRATA` in
  `compat/harness.ts`.
- Deliberate differences from SymPy are allowed when they are documented
  the same way.
- Tests are self-contained: expected values are written in the test (or in
  a reference file in the repository). No file in the repository refers to
  local paths such as a home directory or a temporary directory, which can
  contain personal information.

## Code

- The public API uses camelCase names converted from SymPy's
  (`expand_log` -> `expandLog`); classes keep SymPy's names, except SymPy
  names that are JavaScript globals (`Symbol` -> `Sym`, `Number` ->
  `SymNumber`, `Function` -> `SymFunction`, `Array` -> `SymArray`).
  Each exported name has one definition. See
  [docs/api-policy.md](docs/api-policy.md).
- Public results are never `undefined` or `null`
  ([docs/api-policy.md](docs/api-policy.md)).
- Layers and import rules are enforced by Oxlint
  ([docs/architecture.md](docs/architecture.md)): no import cycles, no
  non-null assertions, no unchecked type assertions, no generic `Error`.
- Renaming or removing a public export keeps the old name as a deprecated
  alias until 1.0, and `packages/symjs/api-report.md` is regenerated.
- Code, comments and documentation are written in English.
- Ported code keeps a credit to its source. SymPy and mpmath are under the
  BSD 3-Clause license, whose notices are reproduced in the `LICENSE` files.

## Arbitrary-precision constants

Constants in `numeric/mpconst.ts` are computed by binary splitting. Each
constant has a table from precision to method and leaf size, chosen by
benchmark. Every method is tested against mpmath at the table boundaries.

## Branches and commits

- Work happens on `feature/<m.n.p>/<alpha|beta>` and is merged into
  `develop/<m.n>.x`, then into `main`. Nothing is committed directly to
  `develop/*` or `main`.
- Commit messages are in English and state what changed, and for
  compatibility work, the compatibility and coverage numbers.
