# symjs

A computer algebra system (CAS) for TypeScript that aims for result compatibility with [SymPy](https://www.sympy.org/).
It is intended as a general-purpose symbolic engine (in the spirit of Mathematica) for polynomial and symbolic computation, e.g. from [q5m.js](https://www.npmjs.com/package/@q5m/q5m).

- Results and string/LaTeX output are checked against SymPy (golden tests and SymPy's own doctests, see below)
- **Expressions**: immutable trees with SymPy's automatic evaluation, `oo`/`zoo`/`nan`, assumptions (real, positive, nonnegative, integer), undefined functions `Function('f')` and `Derivative`
- **Manipulation**: `expand` (with SymPy's hints), `factor` (multivariate), `simplify`, `trigsimp`, `powsimp`, `radsimp`, `collect`, `together`, `cancel` (multivariate), algebraic `subs`, `xreplace`, and `Expr` methods such as `coeff`, `as_independent`, `as_content_primitive`, `primitive`, `is_polynomial`
- **Functions**: elementary functions plus special/combinatorial functions (`gamma`, `polygamma`, `erf`, `Ei`, `Si`, `zeta`, `factorial`, `binomial`, `harmonic`, ...)
- **Calculus**: `diff`, `integrate` (indefinite and definite, including infinite limits), `limit`, `series`/`O`, `Sum`/`Product`/`summation`
- **Equations**: `solve`, `linsolve`, `nonlinsolve`, `solve_linear`, `solve_undetermined_coeffs`, `nsolve`, `dsolve` (first-order linear/separable, constant-coefficient linear ODEs of any order, undetermined coefficients, initial conditions)
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
roots(parse('x**2 + x + 1'), x).map(String); // ['-1/2 - sqrt(3)*I/2', '-1/2 + sqrt(3)*I/2']
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
- Compatibility targets results (computed values and printed output). Class names and return types follow TypeScript conventions (e.g. `roots` returns an array with multiplicities).

## Development

```sh
pnpm install
pnpm test        # vitest (all packages; extend modules use the base module from source)
pnpm typecheck   # tsc --noEmit
pnpm build       # every package: tsup (ESM/CJS) + tsc (declarations)
pnpm golden      # regenerate the SymPy expectations of the golden tests
```

## Current limitations

See [compat/REPORT.md](compat/REPORT.md) for the measured compatibility. Notable gaps:

- `simplify` is a lighter heuristic than SymPy's; results can differ in form
- Algebraic extensions and finite fields in `factor` (`extension=`, `gaussian=`, `modulus=`), `RootOf`/`RootSum`
- Integration beyond the implemented heuristics (no Risch or Meijer G algorithms yet)
- ODE solving covers a few hints only; systems, PDEs and Diophantine equations are not ported
- No public API yet for extend modules to register their own expression node types
- `adjoint`/`Dagger` and expression-level `transpose` are not in the base module yet
