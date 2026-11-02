# symjs

A computer algebra system (CAS) for TypeScript that aims for result compatibility with [SymPy](https://www.sympy.org/).
It is intended as a general-purpose symbolic engine (in the spirit of Mathematica) for polynomial and symbolic computation, e.g. from [q5m.js](https://www.npmjs.com/package/@q5m/q5m).

- Results and string/LaTeX output are checked against SymPy (golden tests and SymPy's own doctests, see below)
- **Expressions**: immutable trees with SymPy's automatic evaluation, `oo`/`zoo`/`nan`, assumptions (real, positive, nonnegative, integer), undefined functions `Function('f')` and `Derivative`
- **Manipulation**: `expand` (with SymPy's hints), `factor` (multivariate), `simplify`, `trigsimp`, `powsimp`, `radsimp`, `collect`, `together`, `cancel` (multivariate), algebraic `subs`, `xreplace`, and `Expr` methods such as `coeff`, `as_independent`, `as_content_primitive`, `primitive`, `is_polynomial`
- **Functions**: elementary functions plus special/combinatorial functions (`gamma`, `polygamma`, `erf`, `Ei`, `Si`, `zeta`, `factorial`, `binomial`, `harmonic`, ...)
- **Calculus**: `diff`, `integrate` (indefinite and definite, including infinite limits), `limit`, `series`/`O`, `Sum`/`Product`/`summation`
- **Equations**: `solve`, `linsolve`, `nonlinsolve`, `solve_linear`, `solve_undetermined_coeffs`, `nsolve`, `dsolve` (first-order linear/separable, constant-coefficient linear ODEs of any order, undetermined coefficients, initial conditions, systems of linear first-order ODEs with constant coefficients)
- **Polynomials**: `Poly` with SymPy's generators/domains/printing, multivariate `gcd`/`lcm`/division, `roots`, `resultant`, `discriminant`, `interpolate`, `horner`
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
| `@symjs/symjs/polys` | Polynomials: `factor`, `roots`, `CRootOf`, `groebner`, `apart`, ... |
| `@symjs/symjs/calculus` | `integrate`, `limit`, `series`, `Sum`, `Product`, ... |
| `@symjs/symjs/solvers` | `solve`, `solveset`, `nonlinsolve`, `rsolve`, `dsolve`, inequalities |
| `@symjs/symjs/sets` | Intervals, finite sets, image and condition sets |
| `@symjs/symjs/matrices` | `Matrix` and linear algebra |

Every entry point includes the core. The core does not depend on the other areas: methods such as `expr.simplify()` or `expr.integrate(x)` work once the area that implements them has been imported (from its entry point or from the root), and otherwise throw an error naming the entry point to import. The modules that register implementations on load are listed in the `sideEffects` field of `package.json` (kept up to date by `node scripts/side-effects.mjs`, checked by the tests). `node scripts/size.mjs --check` (after `pnpm build`) measures the minified bundle of typical imports against size budgets; for example `import { parse, diff, str } from '@symjs/symjs/core'` is about 110 KiB minified (35 KiB gzip), and the whole base module about 390 KiB (130 KiB gzip).

### Repository layout

```
packages/
  symjs/                @symjs/symjs (base module)
    src/                core/ numeric/ printing/ parsing/ functions/ simplify/ polys/
                        calculus/ series/ integrals/ solvers/ matrices/ concrete/ sets/
    tests/              unit tests and SymPy golden tests
  physics-quantum/      @symjs/physics-quantum (extend module)
    src/  tests/
compat/                 SymPy doctest compatibility measurement of the base module
scripts/                golden test generation (SymPy)
```

To add an extend module, create `packages/<name>/` with its own `package.json` (`@symjs/symjs` as a peer dependency with `workspace:^`), `tsup.config.ts` (with `@symjs/symjs` as external) and `tsconfig.build.json`, and import the base module only through `@symjs/symjs`.

## SymPy compatibility

Compatibility is measured against SymPy's own doctests (`compat/`):

- **Behavior compatibility**: share of doctest examples of the in-scope public API (core, elementary functions, simplification, polynomials, solvers, ODEs, calculus, matrices, combinatorial/special functions) that symjs reproduces with identical `str()` output.
- **API coverage**: share of in-scope public SymPy names (including `Expr` and `Matrix` methods) with a symjs counterpart.

```sh
pnpm compat           # run the corpus and write compat/REPORT.md
pnpm compat:extract   # regenerate compat/corpus.json from the installed SymPy
```

See [compat/REPORT.md](compat/REPORT.md) for the current numbers and the highest-impact gaps.

## API design

- Operations are available both as fluent methods (`x.add(1).pow(2)`) and as functions (`add(x, 1)`, `pow(x, 2)`).
- Expressions are immutable. Equality is structural (`a.equals(b)`).
- `symbols('x y')` infers a tuple type of the right length from a string literal.
- Numbers may be given as `number` (integers become exact rationals, non-integers become `Float`) or `bigint`. Use `rational(1, 3)` for exact fractions.
- Names follow SymPy, converted to camelCase (`expand_log` -> `expandLog`); classes keep SymPy's names (`Symbol`, `Derivative`, `Piecewise`, `Interval`, ...). Results that are dicts in SymPy are `ExprMap`s, `Map`s whose expression keys compare structurally (`roots(f, x).get(1)`). See [docs/api-policy.md](docs/api-policy.md) and the generated [API report](packages/symjs/api-report.md) for the stability level of every export; renamed exports keep their old name as a deprecated alias during 0.x.

## Development

```sh
pnpm install
pnpm test        # vitest (all packages; extend modules use the base module from source)
pnpm typecheck   # tsc --noEmit
pnpm build       # every package: tsup (ESM/CJS, one file per module) + tsc (declarations)
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
- `factor` over general algebraic extensions (only `gaussian=` and simple `extension=` cases); algebraic numbers in `minimal_polynomial` and norms are limited to square roots and I
- Integration beyond the implemented heuristics (no Risch or Meijer G algorithms yet); `hyper` and `meijerg` are available as functions but are not used to integrate or to evaluate in closed form
- ODE solving follows SymPy's single-equation hints (separable, exact, linear, Bernoulli, Riccati special, constant and Euler linear equations, undetermined coefficients, variation of parameters, Liouville, reducible order, Airy, Bessel); systems are solved when linear and first order (constant coefficients in closed form, 2x2 variable coefficients in terms of a particular solution like SymPy) or triangular (solved one function at a time); `classify_ode` reports SymPy's hints, but homogeneous-coefficient, linear-coefficient, power series and Lie group solvers, nonlinear systems, PDEs and Diophantine equations are not ported yet (see the ODE checks in the report)
- Symbolic `Mod` (only integers and binomial coefficients modulo prime powers) and asymptotic series of nested exponentials are not implemented
- Intentional differences: where SymPy's result is mathematically wrong symjs returns the correct one, e.g. `dsolve([x' = x*y*sin(t), y' = y**2*sin(t)])` (SymPy's solution fails `checkodesol`)
