# Contributing to symjs

symjs is a TypeScript port of SymPy (with the mpmath parts it needs). These
rules hold for every change, whether it is written by a person or an agent.

## Checks every change must pass

```sh
bun run typecheck                              # tsc --noEmit, no errors
bun run lint                                   # oxlint --type-aware --deny-warnings, no warnings
bun run test                                   # every test passes
bun run coverage                               # 100% coverage (see below)
bun run compat                                 # SymPy doctest compatibility, writes compat/REPORT.md
bun run corpus:report                          # corpus tests, writes docs/compat-report.md
bun run build && bun scripts/size.mjs --check  # bundle sizes within budget
bun run test:package                           # built ESM/CJS, minification and consumer type resolution
```

## Test coverage: 100%, no exclusions

- Vitest enforces these thresholds per file; a coverage regression fails the command.
- Every source file in `packages/*/src` must reach **100% statements,
  branches, functions and lines** in the full test run (`bun run coverage`).
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

## Source files

- Outside `core/`, a module ports the SymPy module of the same path: `sympy/<package>/<module>.py`
  is ported in `packages/symjs/src/<package>/<module>.ts`, with the underscores of the module name
  removed (`zeta_functions.py` -> `functions/special/zetafunctions.ts`). New code goes into the file
  of the SymPy module it ports; the mapping, including the files that combine several SymPy modules,
  is in `docs/architecture.md`.

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
  (`sympy/*/tests`) are a good source of cases. Scripts that compute
  expected values with SymPy live in `tools/sympy-reference/generators/`
  (`gen_<name>.py`, writing `*.references.json` next to the tests); add a
  new one there rather than elsewhere.
- Results match SymPy's `str()` output. A result in another form counts as
  compatible only when it is mathematically equal (see
  `packages/symjs/tests/sympy-equivalent.ts`). A result left unevaluated where SymPy computes
  a value is a failure.
- **Mathematical correctness wins over SymPy's output.** When SymPy is
  wrong (a wrong value, a wrong sign, a claim that fails for some admissible
  value of a symbol), symjs keeps the correct result. The test states
  SymPy's answer and the counterexample in a comment. A SymPy doctest whose
  printed output is wrong is listed with its reason in `SYMPY_ERRATA` in
  `tools/sympy-corpus/harness.ts`.
- Deliberate differences from SymPy are allowed when they are documented
  the same way.
- SymPy doctests and API names that symjs does not support yet are listed in
  `compat/known-gaps.json`. A change may only shrink that list: `bun run compat`
  fails when an unlisted case stops passing and when a listed case starts
  passing. After fixing listed cases, rewrite the list with
  `UPDATE_KNOWN_GAPS=1 bunx vitest run --config compat/vitest.config.ts`
  and check that it only lost entries.
  Expanding the pinned reference scope or correcting an invalid measurement
  can establish a new baseline; the commit message records the old and new counts.
  Such a migration must distinguish new examples and corrected API-presence
  checks from behavior regressions, and replay the previous corpus without
  losing previously passing results. Ordinary implementation changes still
  only shrink the gap list. An adapter is not evidence of a public API:
  review its execution route in `tools/sympy-corpus/adapter-inventory.json`, and keep
  mathematical work in the library. Unreviewed adapters and translations are
  excluded from the report's verified public-call count.
- Tests are self-contained: expected values are written in the test (or in
  a reference file in the repository). No file in the repository refers to
  local paths such as a home directory or a temporary directory, which can
  contain personal information.

For corpus expansion, use `bun run compat:expand` with SymPy 1.14.0 installed.
It retains every existing case (including duplicate documented occurrences),
preserves anonymous Dummy names and the established external-sampler fixture,
and fails if another existing input or result changes or disappears. Public
functions defined in a selected module are measured even if they are not
re-exported at the top level. Multiline results remain measurable; outputs
containing process-local object addresses are recorded as extraction omissions.
When the extractor itself improves (a new serialization or a new omission
rule), `bun run compat:refresh` re-extracts every existing example in place: each
occurrence keeps its position and takes the current serialization, an example
the extractor now omits is dropped only with its recorded omission reason, and
any other disappearance still fails.
Run `bun run compat:test-extract` when changing the extractor. Newly revealed
failures go to `compat/known-gaps.json`; a lower agreement percentage after
adding previously unmeasured behavior is not itself an implementation
regression.

The compatibility command fails on behavior, API, base-scope or ODE regressions.
Its numerical equivalence checks use independent deterministic samples for each
symbol; ordered lists retain their order except for solution-list APIs.

## Code

- The public API uses camelCase names converted from SymPy's
  (`expand_log` -> `expandLog`); classes keep SymPy's names, except SymPy
  names that are JavaScript globals (`Symbol` -> `Sym`, `Number` ->
  `SymNumber`, `Function` -> `SymFunction`, `Array` -> `SymArray`, `Object` -> `SymObject`).
  Each exported name has one definition. See
  [docs/api-policy.md](docs/api-policy.md).
- Public results are never `undefined` or `null`
  ([docs/api-policy.md](docs/api-policy.md)).
- Every export and public class member has a TypeDoc documentation comment with
  its SymPy counterpart in `@see` and examples from the SymPy docstring
  ([docs/api-policy.md](docs/api-policy.md#documentation-comments)).
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

## SymPy unit-test corpus

The independent unit-test corpus covers the base package's 30 top-level SymPy
areas, including their nested test directories. `tools/sympy-reference/extract_tests.py`
contains file-level scope rules for printing, parsing, categories and utilities;
`compat/TESTS-REPORT.md` lists excluded files and technical reasons. Optional
dependencies and unsupported test constructs appear in the extraction audit.

```sh
bun run compat:extract-tests                       # SymPy 1.14.0, four isolated processes
bun run compat:extract-tests --only sets,geometry  # replace only these categories
bun run compat:extract-tests --only polys --jobs 2 # includes agca/domains/matrices/numberfields
bun run compat:test-extract
bunx vitest run --config compat/vitest.config.ts --project unit-geometry
UPDATE_KNOWN_GAPS=1 bunx vitest run --config compat/vitest.config.ts
```

`tools/sympy-corpus/tests-corpus/index.json` is the manifest. Each category has one or more
case arrays (one case per line, ASCII JSON escapes, no nonfinite JSON numbers,
at most 25 MB per shard) and an audit file containing omitted source locations
and test execution statuses. `--only` accepts comma-separated or repeated
category names, retains the other shards and updates the manifest. `--timeout`
sets the upstream per-test deadline (120 seconds by default). Tests that exceed
it contribute no partial observations. `--baseline <legacy-corpus.json>`
retains existing modules' cases exactly and preserves their audit counts while
extracting new modules, so migration does not discard machine-dependent observations.

Vitest runs one project/test per category with at most four workers. The
runner shares the doctest deserializer and adapters and limits synchronous
replay to 30 seconds per core/polys case and 5 seconds elsewhere. A replay
timeout is a measured failure. Exception class mismatches are counted
separately under the established exception assertion convention.

`tools/sympy-corpus/tests-known-gaps.json` is the independent unit-test ratchet. Existing
case IDs include the complete record, with its field order, and remain stable
when records move to shards. A full run writes `compat/TESTS-REPORT.md`, the
summary `compat/tests-report.json`, and per-category failure details in
`compat/tests-results/*.jsonl`. A single coordinator updates the ratchet after
all categories finish; partial project runs cannot replace the full report or
ratchet. When expanding scope, distinguish newly measured gaps from regressions
in existing cases. The doctest corpus and its ratchet remain independent.

Repeated omission records share a `count` in category audit files. Counts retain
every examined loop observation without repeating identical source metadata.
`bun run compat:extract-tests --compact-audits` losslessly repacks these audits
without changing case records or re-executing upstream tests.

Replay deadlines remain in the measured totals and failure groups. The ratchet
stores their IDs in `timeouts` as inconclusive observations. A deadline cannot
establish a correctness regression, and a completed result cannot resolve a
previously unfinished assertion as a confirmed fix. Completed assertions still
use the strict existing regression/fixed-case checks.

## Corpus tests

### From SymPy to vitest

Two tools connect SymPy's own examples to the symjs tests. The extractor runs
SymPy; the converter runs symjs. They exchange only the corpus files:

```
SymPy 1.14.0 (Python)
  │  tools/sympy-reference/extract.py        doctests in the docstrings
  │  tools/sympy-reference/extract_tests.py  assertions of SymPy's unit tests
  ▼
tools/sympy-corpus/corpus.json, tests-corpus/*.json
  │  each case: the call (function, serialized arguments), SymPy's printed result
  │
  │  tools/sympy-corpus/totests (bun run corpus:generate)
  │    1. replays the case through harness.ts with the symjs entry points traced
  │    2. prints the public calls that produced the result as TypeScript
  │    3. classifies the case: it / it.fails / it.todo
  ▼
packages/symjs/tests/**/<module>.corpus.test.ts
  │  bun run test, bun run coverage: run with the hand-written tests
  │  bun run corpus:report: rate per corpus and category
  ▼
docs/compat-report.md
```

- The **extractor** (Python) needs SymPy 1.14.0 and runs only when the
  reference changes: a new SymPy area, a fixed extraction rule, or a SymPy
  upgrade. It records what SymPy computes; it knows nothing about symjs.
- The **converter** (TypeScript) needs no Python. It runs after every change
  that alters a case's outcome: an implementation change, a public API change,
  a converter or harness change, or a new extraction. It records how the
  symjs public API reproduces each case.
- The **harness** (`tools/sympy-corpus/harness.ts`) is shared: it turns a
  serialized SymPy call into a symjs call. A case without an adapter becomes
  `it.todo` with the reason `no adapter for ...`.

### Kinds of generated tests

Every case becomes one test in the file of the module it exercises:

- `it`: symjs gives SymPy's result.
- `it.fails`: the case translates to the public API but the result differs.
- `it.todo`: the case does not translate yet; the comment above it holds the
  reason, the SymPy source and SymPy's result.

The generated files are not edited by hand. Cases whose code the public types
reject are recorded in `tools/sympy-corpus/totests/type-errors.json`, and cases
whose generated test disagrees with the replay in
`tools/sympy-corpus/totests/unreproduced.json`; the next run writes both as
`it.todo`. A run prints `type errors: N` and `unreproduced: N`; repeat it until
both are 0. One run takes about ten minutes.

`docs/compat-report.md` gives the compatibility rate per corpus and category:
the share of cases that are `it` and pass. An `it` that fails or an `it.fails`
that passes is listed as stale.

### Procedures

After an implementation change that fixes or breaks cases:

```sh
bun run corpus:report    # stale cases: an it.fails that now passes, an it that now fails
bun run corpus:generate  # rewrite the files; repeat until type errors and unreproduced are 0
bun run corpus:report    # the new rates
```

After re-extracting part of the reference (here SymPy's geometry unit tests):

```sh
bun run compat:extract-tests --only geometry  # SymPy 1.14.0 → tools/sympy-corpus/tests-corpus/
bun run compat:test-extract                   # the extractor's own tests
bun run corpus:generate                       # repeat until type errors and unreproduced are 0
bun run corpus:report
```

Doctests are re-extracted with `bun run compat:expand` (new modules) or
`bun run compat:refresh` (every existing example).

To look at the conversion of some cases without writing files:

```sh
ONLY=sympy.geometry SHOW=5 bunx vitest run --config tools/sympy-corpus/totests/vitest.config.ts tools/sympy-corpus/totests/generate.test.ts --silent=false
```

After a converter or harness change that may turn recorded cases into tests,
`CORPUS_RECHECK_TYPES=1 bun run corpus:generate` ignores both records and builds
them again.
