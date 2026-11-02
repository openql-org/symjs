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
| L1 functions | elementary and special functions, numeric evaluation (evalf, lambdify), parsing, differentiation, expansion and rewriting | `functions/`, `numeric/` (other files), `parsing/`, `concrete/node.ts`, `calculus/diff.ts`, `calculus/finitediff.ts`, `simplify/expand.ts`, `simplify/rewrite.ts` |
| L2 algebra | polynomials, simplification, matrices (including linear systems), series and limits, sets, sums and products | `polys/`, `simplify/`, `matrices/`, `series/`, `sets/`, `calculus/` (other files), `concrete/summations.ts` |
| L3 solvers and integration | equation solving, ODEs, recurrences, inequalities, integration, `doit`, Fourier and formal power series | `solvers/`, `integrals/`, `calculus/doit.ts`, `series/more.ts` |

The entry points (`src/*.ts`) may import every layer.

Extend modules (`packages/*` other than `symjs`) import the base module only
through its public entry points (`@symjs/symjs`, `@symjs/symjs/<entry>`),
never its source files.

The rules are enforced by `pnpm lint` (`no-restricted-imports` in
`.oxlintrc.json`). When a lower layer needs something from a higher one, add
a late-bound entry to `Impl` in `core/nodes.ts` and register it in the higher
layer, or move the shared code down to the lowest layer that uses it.
