# Architecture of `@symjs/symjs`: layers

The base module is organized in layers. A module may import modules of its
own layer and of lower layers, never of a higher layer. A lower layer that
needs a feature of a higher layer reaches it through the late-bound
implementations in `core/nodes.ts` (`impl.diff`, `impl.fn`, `impl.simplify`,
`impl.integrate`, ...), which the higher layer registers when it is loaded.
Type-only imports are allowed in any direction.

This keeps "pay only for what you import" true: importing `Rational` does
not pull in the solvers, and an extend module can rely on the lower layers
without the higher ones.

| Layer | Contents | Paths (under `packages/symjs/src/`) |
|---|---|---|
| L0 kernel | expression tree, numbers (including the mpf arithmetic), symbols and assumptions, automatic evaluation, traversal and substitution, Sum/Product nodes, str/LaTeX printing | `core/`, `printing/`, `numeric/mpf.ts`, `numeric/mpfun.ts`, `numeric/complex.ts` |
| L1 functions | elementary and special functions, numeric evaluation (evalf, lambdify), parsing, differentiation, expansion and rewriting, propositional logic, number theory, iterable utilities | `functions/`, `logic/`, `ntheory/`, `utilities/`, `numeric/` (other files), `parsing/`, `concrete/node.ts`, `calculus/diff.ts`, `calculus/finitediff.ts`, `simplify/expand.ts`, `simplify/rewrite.ts` |
| L2 algebra | polynomials, simplification, matrices (including linear systems), series and limits, sets, sums and products, permutations, N-dimensional arrays | `polys/`, `combinatorics/`, `tensor/`, `simplify/`, `matrices/`, `series/`, `sets/`, `calculus/` (other files), `concrete/summations.ts` |
| L3 solvers and integration | equation solving, ODEs, recurrences, inequalities, integration, `doit`, Fourier and formal power series | `solvers/`, `integrals/`, `calculus/doit.ts`, `series/more.ts` |

The entry points (`src/*.ts`) may import every layer.

Extend modules (`packages/*` other than `symjs`) import the base module only
through its public entry points (`@symjs/symjs`, `@symjs/symjs/<entry>`),
never its source files.

The rules are enforced by `pnpm lint` (`no-restricted-imports` in
`.oxlintrc.json`). When a lower layer needs something from a higher one, add
a late-bound entry to `Impl` in `core/nodes.ts` and register it in the higher
layer, or move the shared code down to the lowest layer that uses it.

## Cycles and other lint rules

Modules of the same layer must not import each other in a cycle
(`import/no-cycle`). When two modules need each other, the lower one keeps a
small hook object that the other fills in when it is loaded (for example
`polyHooks` in `polys/poly.ts`, set by `simplify/rational.ts`), or the shared
code moves to its own module (`solvers/homogeneous.ts`).

`pnpm lint` (Oxlint, type-aware) also enforces, for `packages/*/src`:

| Rule | Purpose |
|---|---|
| `explicit-module-boundary-types` | exported functions declare their return types |
| `strict-boolean-expressions` | no truthiness test of a `Truth` (`'unknown'` is truthy) |
| `switch-exhaustiveness-check` | discriminated unions are handled completely |
| `consistent-type-imports` | type-only imports are marked (`import type`), so layering and bundling see only value dependencies |
| `no-deprecated` | deprecated aliases are not used internally (they are removed in 1.0) |
| `no-unnecessary-condition`, `no-unnecessary-type-assertion` | no dead checks and casts |
| `prefer-nullish-coalescing` (strings excepted), `prefer-optional-chain` | `??` and `?.` for undefined |
| `no-param-reassign` | parameters are not reassigned (copy them to a local) |
| `no-explicit-any`, `ban-ts-comment`, `no-console`, `only-throw-error` | kept at zero |
| `no-restricted-globals` (`Error`) | errors are specific classes: `TypeError`, `RangeError`, `SyntaxError`, or those of `core/errors.ts` (`NotImplementedError`, `PolynomialError`, `DomainError`, `ExactQuotientFailed`, `NotInvertible`, `MatrixError`, `NonSquareMatrixError`, `NonInvertibleMatrixError`, `NonlinearError`, `SympifyError`, `NotLoadedError`, `InvariantError`, ...) |
| `no-non-null-assertion`, `no-unsafe-type-assertion` | no `x!` and no unchecked `x as T`: values an algorithm guarantees are read through the checked helpers of `core/guard.ts` (`at`, `first`, `last`, `defined`, `getOrThrow`, `cast`, `expectType`, `pair`), which throw `InvariantError` when the guarantee is violated, or narrowed by the type system; the few remaining assertions carry an `oxlint-disable-next-line` comment giving the reason |
