# symjs

A computer algebra system (CAS) for TypeScript that aims for result compatibility with [SymPy](https://www.sympy.org/).
It is intended as a general-purpose symbolic engine (in the spirit of Mathematica) for polynomial and symbolic computation, e.g. from [q5m.js](https://www.npmjs.com/package/@q5m/q5m).

- Results and string/LaTeX output are checked against SymPy (golden tests and SymPy's own doctests, see below)
- **Expressions**: immutable trees with SymPy's automatic evaluation, `oo`/`zoo`/`nan`, assumptions (real, positive, nonnegative, integer), undefined functions `SymFunction('f')` (SymPy `Function('f')`) and `Derivative`
- **Manipulation**: `expand` (with SymPy's hints), `factor` (multivariate), `simplify`, `trigsimp`, `powsimp`, `radsimp`, `collect`, `together`, `cancel` (multivariate), algebraic `subs`, `xreplace`, and `Expr` methods such as `coeff`, `as_independent`, `as_content_primitive`, `primitive`, `is_polynomial`
- **Functions**: elementary functions plus special/combinatorial functions (`gamma`, `polygamma`, `erf`, `Ei`, `Si`, `zeta`, `factorial`, `binomial`, `harmonic`, ...)
- **Calculus**: `diff`, `integrate` (indefinite and definite, including infinite limits), `limit`, `series`/`O`, `Sum`/`Product`/`summation`
- **Equations**: `solve`, `linsolve`, `nonlinsolve`, `solve_linear`, `solve_undetermined_coeffs`, `nsolve`, `dsolve` (first-order linear/separable, constant-coefficient linear ODEs of any order, undetermined coefficients, initial conditions, systems of linear first-order ODEs with constant coefficients)
- **Polynomials**: `Poly` with SymPy's generators/domains/printing, multivariate `gcd`/`lcm`/division, `roots`, `resultant`, `discriminant`, `interpolate`, `horner`
- **Statistics**: random symbols of continuous, discrete and finite distributions (SymPy `sympy.stats`), probabilities, expectations, densities, cumulative distribution and characteristic functions, moments, conditional distributions; joint distributions and marginals, matrix distributions, random matrix ensembles, stochastic processes (Markov chains, Bernoulli, Poisson, Wiener and gamma processes) and the expectation, variance and cross-covariance of random vectors
- **Linear algebra**: symbolic `Matrix` with determinant, inverse, `rref`, rank, null/column/row spaces, eigenvalues/eigenvectors, diagonalization, LU/QR/Cholesky/LDL, norms, singular values, pseudo-inverse, Kronecker product
- Numeric evaluation (`toComplex` / `evalf` / `lambdify`), a parser and the `ex` tagged template

## Usage

```ts
import { symbols, sin, cos, simplify, ex, expand, factor, latex, parse, diff, roots } from '@symjs/symjs';

const [theta, phi] = symbols('theta phi', { real: true });
const [x] = symbols('x');

simplify(sin(theta).pow(2).add(cos(theta).pow(2))).toString();                 // '1'
simplify(ex`cos(${theta})*cos(${phi}) - sin(${theta})*sin(${phi})`).toString(); // 'cos(phi + theta)'
expand(parse('(x + 1)**3')).toString();      // 'x**3 + 3*x**2 + 3*x + 1'
factor(parse('x**3 - x')).toString();        // 'x*(x - 1)*(x + 1)'
latex(parse('sin(x)**2/2'));                 // '\\frac{\\sin^{2}{\\left(x \\right)}}{2}'
diff(parse('x**x'), x).toString();           // 'x**x*(log(x) + 1)'
roots(parse('x**2 + x + 1'), x);             // Map { -1/2 - sqrt(3)*I/2 => 1, -1/2 + sqrt(3)*I/2 => 1 }
```

## Packages: base and extend modules

symjs is a pnpm monorepo. The general-purpose CAS is the **base module**; functionality for a specific application domain is published as separate **extend module** packages, so applications install only what they use:

| Package | Directory | Contents |
|---|---|---|
| [`@symjs/symjs`](packages/symjs) | `packages/symjs/` | Base module: expressions, numbers, printing and parsing, functions, simplification, polynomials, calculus, equation solving, matrices, sets |
| [`@symjs/physics-quantum`](packages/physics-quantum) | `packages/physics-quantum/` | Extend module for quantum physics (SymPy `sympy.physics.quantum`) |
| [`@symjs/mathjs`](packages/mathjs) | `packages/mathjs/` | Extend module: conversion to and from math.js (math.js is not a dependency) |

Extend modules depend only on the public API of the base module, which they declare as a peer dependency (`@symjs/symjs`), so every extend module installed in an application shares one copy of the base module. Which sub-packages belong to the base module and which become extend modules is to be decided by the community; `physics-quantum` is the first example.

```ts
import { Matrix } from '@symjs/symjs';
import { gates } from '@symjs/physics-quantum';

gates.H().mul(gates.H()).equals(Matrix.eye(2)); // true
```

The quantum package will be ported from `sympy.physics.quantum`; the current `gates` are provisional.

### Entry points and bundle size

`@symjs/symjs` imports the whole base module. Each feature area is also an entry point of its own, so that a bundler includes only what an application uses:

| Entry point | Contents |
|---|---|
| `@symjs/symjs/core` | Expressions, numbers and assumptions, symbols and undefined functions, elementary functions, substitution and matching, `diff`, `expand`, `evalf`, parsing, `str` and `latex` |
| `@symjs/symjs/special` | Special and combinatorial functions (Gamma, zeta, error functions, Bessel and Airy functions, ...) |
| `@symjs/symjs/simplify` | `simplify`, `trigsimp`, `powsimp`, `radsimp`, `together`, `cancel`, `rewrite`, ... |
| `@symjs/symjs/polys` | Polynomials: `factor`, `roots`, `CRootOf`, `groebner`, `apart`, `primitiveElement`, `toNumberField`, ... |
| `@symjs/symjs/calculus` | `integrate`, `limit`, `series`, `Sum`, `Product`, ... |
| `@symjs/symjs/solvers` | `solve`, `solveset`, `nonlinsolve`, `rsolve`, `dsolve`, `pdsolve`, `checkpdesol`, inequalities |
| `@symjs/symjs/combinatorics` | Permutations, permutation groups, stabilizer chains and named finite groups |
| `@symjs/symjs/tensor` | N-dimensional arrays, abstract tensor indices, slot symmetries and metric contraction |
| `@symjs/symjs/categories` | `SymObject`, morphisms, composition, categories and diagrams |
| `@symjs/symjs/sets` | Intervals, finite sets, image and condition sets |
| `@symjs/symjs/matrices` | `Matrix` and linear algebra |
| `@symjs/symjs/geometry` | Points, lines, planes, polygons, ellipses, curves and parabolas, `intersection`, `convexHull`, ... |
| `@symjs/symjs/vector` | `CoordSys3D`, vectors and dyadics, `Del`, `gradient`, `divergence`, `curl`, `express`, parametric and implicit regions, `vectorIntegrate`, ... |
| `@symjs/symjs/stats` | Random symbols (`Normal`, `Exponential`, `Poisson`, `Die`, `Binomial`, ... and handmade distributions), `P`, `expectation` (SymPy `E`), `density`, `given`, `where`, `cdf`, `variance`, `moment`, `covariance`, `median`, the `Probability`/`Expectation`/`Variance`/`Covariance` nodes, joint distributions (`MultivariateNormal`, `Dirichlet`, `Multinomial`, `JointRV`, `marginalDistribution`, ...), matrix distributions (`Wishart`, `MatrixNormal`, ...), random matrices (`GaussianUnitaryEnsemble`, `CircularEnsemble`, ...), stochastic processes (`DiscreteMarkovChain`, `ContinuousMarkovChain`, `PoissonProcess`, `WienerProcess`, ...), `ExpectationMatrix`, `VarianceMatrix`, `CrossCovarianceMatrix`, ... |

Category objects use `SymObject` to avoid the JavaScript `Object` global. Apply an abstract tensor head with `head.at(...indices)` and reverse index variance with `index.neg()`. The supported mathematical conditions are listed in [compat/capabilities.json](compat/capabilities.json).

Every entry point includes the core. The core does not depend on the other areas: methods such as `expr.simplify()` or `expr.integrate(x)` work once the area that implements them has been imported (from its entry point or from the root), and otherwise throw an error naming the entry point to import. The modules that register implementations on load are listed in the `sideEffects` field of `package.json` (kept up to date by `node scripts/side-effects.mjs`, checked by the tests). `node scripts/size.mjs --check` (after `pnpm build`) measures the minified bundle of typical imports against size budgets; the measured sizes and budgets are printed by `node packages/symjs/scripts/size.mjs`.

### Repository layout

```
packages/
  symjs/                @symjs/symjs (base module)
    src/                core/ numeric/ printing/ parsing/ functions/ simplify/ polys/
                        calculus/ series/ integrals/ solvers/ matrices/ concrete/ sets/
                        (outside core/, the paths follow SymPy's module tree, see docs/architecture.md)
    tests/              unit tests mirroring src/ (tests/<path>/<name>.test.ts for src/<path>/<name>.ts), cross-cutting tests and SymPy golden tests at the top
  physics-quantum/      @symjs/physics-quantum (extend module)
    src/  tests/
compat/                 SymPy doctest compatibility measurement of the base module
scripts/                golden test generation (SymPy)
```

To add an extend module, create `packages/<name>/` with its own `package.json` (`@symjs/symjs` as a peer dependency with `workspace:^`), `tsup.config.ts` (with `@symjs/symjs` as external) and `tsconfig.build.json`, and import the base module only through `@symjs/symjs`.

## SymPy compatibility

Compatibility has separate measurements; none is a whole-SymPy completion percentage:

- The pinned [scope inventory](compat/scope-inventory.json) lists **all 825 production modules of SymPy 1.14.0**, including partial, unimplemented, unassessed and explicitly excluded modules.
- **Corpus result agreement** measures extracted examples. The [extraction audit](compat/REPORT.md#extraction-audit) records omitted examples and their reasons.
- **Verified public-call results** count automatic public API calls and reviewed conversion adapters. Mathematical computations remaining in the harness and unreviewed translations are reported separately, even when their results match.
- **API presence** requires an actual exported function or member, with its concrete path recorded. It does not establish behavior or completeness. An adapter alone no longer counts as an API.
- [Capability conditions](compat/capabilities.json) link direct public-API tests to their mathematical conditions and remaining limitations.
- Unit coverage must reach 100% of statements, branches, functions and lines. This is a code-test metric, not SymPy compatibility.

The current counts are generated in [compat/REPORT.md](compat/REPORT.md).
Unmatched examples and names without a verified public counterpart are tracked in `compat/known-gaps.json`.
The regression baseline now includes previously unmeasured mathematics and
APIs incorrectly counted solely from adapter presence; changes within this
scope must shrink the gap list. Cases include an input/output digest so that
repeated doctest source lines with different inputs remain distinct.

```sh
pnpm compat           # run the tests with coverage and the corpus, write compat/REPORT.md
UPDATE_KNOWN_GAPS=1 npx vitest run --config compat/vitest.config.ts   # rewrite compat/known-gaps.json
pnpm compat:extract   # regenerate compat/corpus.json from the installed SymPy
```

See [compat/REPORT.md](compat/REPORT.md) for the current numbers and the highest-impact gaps.

## API design

- Operations are available both as fluent methods (`x.add(1).pow(2)`) and as functions (`add(x, 1)`, `pow(x, 2)`).
- Expressions are immutable. Equality is structural (`a.equals(b)`).
- `symbols('x y')` infers a tuple type of the right length from a string literal.
- Numbers may be given as `number` (integers become exact rationals, non-integers become `Float`) or `bigint`. Use `rational(1, 3)` for exact fractions.
- Results are never `undefined` or `null`: undecidable answers are `'unknown'` (`Truth`), a missing form is `NoMatch`, no closed form is `Unsolved`, no solution is `EmptySet` (see [docs/api-policy.md](docs/api-policy.md)).
- Names follow SymPy, converted to camelCase (`expand_log` -> `expandLog`); classes keep SymPy's names (`Symbol`, `Derivative`, `Piecewise`, `Interval`, ...). Results that are dicts in SymPy are `ExprMap`s, `Map`s whose expression keys compare structurally (`roots(f, x).get(1)`). See [docs/api-policy.md](docs/api-policy.md) and the generated [API report](packages/symjs/api-report.md) for the stability level of every export; renamed exports keep their old name as a deprecated alias during 0.x.

## Development

See [CONTRIBUTING.md](CONTRIBUTING.md) for the rules every change follows (100% test coverage, expected values from SymPy, mathematical correctness over SymPy's output, branches and commits).

```sh
pnpm install
pnpm test        # vitest (all packages; extend modules use the base module from source)
pnpm typecheck   # tsc --noEmit
pnpm lint        # oxlint with type-aware rules (see docs/api-policy.md)
pnpm build       # every package: ESM/CJS and matching .d.ts/.d.cts declaration graphs
pnpm test:package # built packages, all entry points, minification, NodeNext/Bundler consumers
node packages/symjs/scripts/size.mjs --check   # bundle sizes of typical imports against budgets
pnpm golden      # regenerate the SymPy expectations of the golden tests
```

## Custom expression nodes in extend modules

An extend module defines its own node types by subclassing `ExtensionExpr`
from `@symjs/symjs`. Implement `withArgs` (used by `subs`, `xreplace` and
other traversals) and override `printStr`, `printLatex`, `diffSelf`,
`adjointSelf`, `conjugateSelf` or `transposeSelf` as needed. Override
`isCommutative` to return `false` for operators and states. The hooks
`rewriteSelf` (SymPy `_eval_rewrite`), `expandSelf` (SymPy
`_eval_expand_<hint>`, called by `expand(e, { hint: true })`) and `isScalar`
cover the remaining customizations of a SymPy `Expr` subclass.

## User-defined functions

`defineFunction` is the counterpart of subclassing SymPy's `Function`:

```ts
import { cos, defineFunction, diff, fn, pi, rewrite, sub, symbols } from '@symjs/symjs';

const [x] = symbols('x');
const mysin = defineFunction('mysin', {
  eval: (a) => (a.equals(0) ? 0 : undefined),           // SymPy eval
  fdiff: ([a]) => cos(a!),                              // SymPy fdiff
  rewrite: { cos: (a) => fn('cos', [sub(pi.div(2), a)], { evaluate: false }) },
  evalf: Math.sin,                                      // numeric value
});
diff(mysin(x.pow(2)), x);   // 2*x*cos(x**2)
rewrite(mysin(x), 'cos');   // cos(-x + pi/2)
```

`implementedFunction(name, f)` attaches a numeric implementation to a
symbolic function (SymPy `implemented_function`). Objects of your own classes
are converted by `sympify` when they define a `[sympifyMethod]()` method or
are registered in `converter` (SymPy `_sympy_` and `converter`), and `parse`
accepts `locals` with values and functions by name.

## Current limitations

See [compat/REPORT.md](compat/REPORT.md) for the measured compatibility. Notable gaps:

- `simplify` is a lighter heuristic than SymPy's; results can differ in form
- `factor` over general algebraic extensions remains limited; number-field presentation constraints are recorded in `compat/capabilities.json`.
- Definite integration splits at polynomial singularities using one-sided limits; when their locations cannot be resolved, the integral is left unevaluated.
- Integration beyond the implemented heuristics (no Risch or Meijer G algorithms yet); `hyper` and `meijerg` are available as functions but are not used to integrate or to evaluate in closed form
- ODE solving follows SymPy's single-equation hints (separable, exact, linear, Bernoulli, Riccati special, homogeneous coefficients, linear coefficients, constant and Euler linear equations, undetermined coefficients, variation of parameters, Liouville, reducible order, Airy, Bessel); systems are solved when linear and first order (constant coefficients in closed form, 2x2 variable coefficients in terms of a particular solution like SymPy) or triangular (solved one function at a time); individual supported hints are recorded in the ODE checks
- JavaScript code printing (`jscode`) remains unimplemented, rather than excluded: exporting expressions to JavaScript is a separate capability from running the engine in JavaScript.
- Number-field embeddings use exact rational power bases for supported radical presentations; general `RootOf` embeddings, maximal orders and Galois groups remain incomplete.
- Permutation groups provide stabilizer-chain order/membership and basic subgroup operations; finitely presented groups and many advanced subgroup algorithms remain incomplete.
- Abstract tensors support Einstein multiplication, free-index complete symmetries and symmetric metric contraction; tensor sums and general Butler–Portugal canonicalization are not implemented.
- PDEs support first-order constant-coefficient linear equations and variable separation; higher-order solving, variable coefficients and boundary conditions remain incomplete.
- Category theory supports objects, morphisms, composition and diagrams. Diagram layout and Xy-pic output are unimplemented. Functors and natural transformations are outside the SymPy 1.14 implementation itself.
- `sympy.stats`: `JointDistribution.cdf` (which fails for every input in SymPy) is not ported
- Symbolic `Mod` (only integers and binomial coefficients modulo prime powers) and asymptotic series of nested exponentials are not implemented
- Intentional differences: where SymPy's result is mathematically wrong symjs returns the correct one, e.g. `dsolve([x' = x*y*sin(t), y' = y**2*sin(t)])` (SymPy's solution fails `checkodesol`); `rsolve` returns `Unsolved` instead of an incomplete solution when the hypergeometric solutions found do not span the solution space and no initial values fix it (SymPy returns e.g. `0` for `y(n+2) - n*y(n+1) - y(n)`)

## Not ported (out of scope)

Runtime-specific backends are deliberately excluded; mathematical modules remain in the inventory even when not implemented:

- Sampling of random variables in `sympy.stats` (`sample`, `sample_iter`, `sampling_density`, `sample_stochastic_process`, `numsamples=`, the `sample` methods of distributions, spaces and processes; `sympy/stats/sampling/`), which draws samples with numpy, scipy or pymc
- Plotting (`sympy.plotting`, the `plot`/`show` methods)
- The TensorFlow back end of `lambdify`

## License

MIT (see [LICENSE](LICENSE)). symjs is a port of [SymPy](https://www.sympy.org) and, for arbitrary-precision numerics, of [mpmath](https://mpmath.org); the ported code is also subject to their BSD 3-Clause licenses, whose notices are reproduced in the LICENSE file of each package that contains such code (`@symjs/symjs`: SymPy and mpmath; `@symjs/physics-quantum`: SymPy). symjs is an independent project and is not affiliated with or endorsed by the SymPy or mpmath developers.
