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
| L0 kernel | expression tree, numbers (including the mpf arithmetic), symbols and assumptions, automatic evaluation, traversal and substitution, Sum/Product nodes, str/LaTeX printing | `core/`, `printing/`, `numeric/mpf.ts`, `numeric/mpfun.ts`, `numeric/mpconst.ts`, `numeric/complex.ts` |
| L1 functions | elementary and special functions, numeric evaluation (evalf, lambdify), parsing, differentiation, expansion and rewriting, propositional logic, number theory, discrete transforms and convolutions, iterable utilities, rewrite strategies and unification | `functions/`, `logic/`, `ntheory/`, `discrete/`, `utilities/`, `strategies/`, `unify/`, `numeric/` (other files), `parsing/`, `concrete/node.ts`, `calculus/diff.ts`, `calculus/finitediff.ts`, `simplify/expand.ts`, `simplify/rewrite.ts` |
| L2 algebra | polynomials, simplification, matrices (including linear systems), series and limits, sets, sums and products, permutations and groups, abstract tensors and N-dimensional arrays, categories, quaternions, the assumption helpers and the matrix handlers of `ask`, ciphers and cryptosystems, simple Lie algebras | `polys/`, `combinatorics/`, `tensor/`, `categories/`, `algebras/`, `simplify/`, `matrices/`, `series/`, `sets/`, `calculus/` (other files), `concrete/summations.ts`, `assumptions/`, `crypto/`, `liealgebras/` |
| L3 solvers and integration | equation solving, ODEs, recurrences, inequalities, integration, `doit`, Fourier and formal power series, holonomic functions, sums of Kronecker deltas and Gosper's summation (which solve equations) | `solvers/`, `integrals/`, `holonomic/`, `calculus/doit.ts`, `series/formal.ts`, `series/fourier.ts`, `concrete/delta.ts`, `concrete/gosper.ts` |
| L4 geometry | points, lines, planes, polygons, ellipses, curves and parabolas, which intersect by solving equations | `geometry/` |
| L5 vector | coordinate systems, vectors and dyadics, vector differential operators, integrals over parametric, implicit and geometric regions | `vector/` |
| L6 stats | random symbols, probability spaces and distributions (continuous, discrete, finite, compound, joint, matrix, random-matrix ensembles, stochastic processes), probabilities, expectations, densities and moments, which are integrals, sums and solutions of equations | `stats/` |

The entry points (`src/*.ts`) may import every layer. `@symjs/symjs/logic`
exports the assumption helpers of `assumptions/` (they use only the core), and
`@symjs/symjs/matrices` loads the matrix handlers of `ask`
(`assumptions/handlers/matrices.ts`, registered on load), so the core entry
stays free of the higher layers.

Extend modules (`packages/*` other than `symjs`) import the base module only
through its public entry points (`@symjs/symjs`, `@symjs/symjs/<entry>`),
never its source files.

The rules are enforced by `pnpm lint` (`no-restricted-imports` in
`.oxlintrc.json`). The patterns are relative import paths, so each one is
listed twice: `../<dir>/**` for the modules directly under `src/<area>/` and
`../../<dir>/**` for those one level deeper (`functions/elementary/`,
`functions/special/`, ...). When a lower layer needs something from a higher one, add
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

## Source layout and SymPy's module tree

Outside `core/`, a module ports the SymPy module of the same path: the
source of `sympy/<package>/<module>.py` is in `src/<package>/<module>.ts`,
and its tests are in `tests/<package>/<module>.test.ts`. File names are
SymPy's module names with the underscores removed (`zeta_functions.py` ->
`zetafunctions.ts`, `elliptic_integrals.py` -> `ellipticintegrals.ts`,
`cse_main.py` -> `csemain.ts`). A file that ports several SymPy modules
which could not be separated keeps a descriptive name in the package of
the SymPy modules it ports, and a file without a SymPy counterpart lives in
the package it belongs to; both are marked in the tables below.

### `core/`

`core/` is symjs's own design: the expression tree is a small set of
immutable node classes with canonicalizing constructors, and the features
of the higher layers are reached through the late-bound `impl` table. The
SymPy modules correspond to it as follows.

| SymPy module | symjs |
|---|---|
| `sympy/core/basic.py` | `core/nodes.ts` (`Expr` as the common base), `core/basic.ts` (the generic `Basic(*args)` node), `core/compare.ts` (`Basic.compare`, SymPy's class names and `args` order), `core/traverse.ts` (`subs`, `xreplace`, `atoms`, `free_symbols`), `core/match.ts` (`matches`, `replace`, `find`, `count_ops`), `simplify/rewrite.ts` (`rewrite`) |
| `sympy/core/expr.py` | `core/nodes.ts` (`Expr`), `core/methods.ts` (`coeff`, `as_independent`, `as_coeff_add`/`as_coeff_mul`, `primitive`, `as_content_primitive`, `extract_*`, `is_polynomial`, ...), `series/lseries.ts` (`lseries`, `dir`), `simplify/expand.ts` (`expand`) |
| `sympy/core/add.py`, `mul.py`, `power.py`, `operations.py` | `core/nodes.ts` (`Add`, `Mul`, `Pow`), `core/ops.ts` (their canonicalizing constructors `add`, `mul`, `pow`) |
| `sympy/core/numbers.py` | `core/nodes.ts` (`Rational`, `Float`, `Constant`, `Special`), `core/num.ts` (arithmetic on numbers), `core/numbers.ts` (bigint helpers), `core/numberutils.ts` (exact rationals from floats and decimal strings, `integer_log`), `numeric/` (mpf arithmetic) |
| `sympy/core/singleton.py` | `core/nodes.ts` (`S`) |
| `sympy/core/symbol.py` | `core/nodes.ts` (`Sym`, `Dummy`, `Wild`), `core.ts` (`symbols`), `core/numberutils.ts` (its range syntax) |
| `sympy/core/function.py` | `core/nodes.ts` (`Fn`, `Derivative`), `functions/elementary/elementary.ts` (`fn`, the evaluation of applied functions), `core/undef.ts` (undefined functions, `Derivative` construction), `core/defun.ts` (user-defined functions), `core/lambda.ts` (`Lambda`), `core/subsnode.ts` (`Subs`), `calculus/diff.ts` (`diff`), `simplify/expand.ts` (`expand` and its hints) |
| `sympy/core/relational.py`, `sympy/functions/elementary/piecewise.py` | `core/logic.ts` (relations, boolean constants, `Piecewise`) |
| `sympy/core/assumptions.py`, `facts.py`, `assumptions_generated.py` | `core/assumptions.ts` (three-valued queries), `core/facts.ts` (the deduction of the facts, `FactRules`/`FactKB`, with SymPy's compiled rule tables) |
| `sympy/assumptions/` | `core/refine.ts` (`Q`, `ask`, `refine`, handlers); `assumptions/sathandlers.ts`, `assumptions/wrapper.ts` and `assumptions/handlers/matrices.ts` port the modules of the same paths (L2) |
| `sympy/core/containers.py` | `core/containers.ts` |
| `sympy/core/exprtools.py` | `core/factors.ts` (`Factors`), `simplify/exprtools.ts` (`gcd_terms`, `factor_terms`, ...) |
| `sympy/core/mod.py` | `functions/mod.ts` |
| `sympy/core/sympify.py` | `core/sympify.ts`, `core/ops.ts` (`sympify` of numbers) |
| `sympy/core/kind.py` | `core/kind.ts` |
| `sympy/core/traversal.py` | `core/traverse.ts` |
| `sympy/core/sorting.py` | `printing/sortkey.ts` (`default_sort_key`), `core/match.ts` (`ordered`) |
| `sympy/core/evalf.py` | `numeric/evalf.ts` |
| the base classes of `sympy/core/numbers.py`, `basic.py`, `expr.py`, `function.py` as constructors (`Number`, `RealNumber`, `Atom`, `AtomicExpr`, `FunctionClass`), `UnevaluatedExpr` | `core/classes.ts` |
| `sympy/concrete/` (the `Sum`/`Product` nodes) | `core/concrete.ts` |
| `sympy/logic/boolalg.py` (the connectives used by relations) | `core/boolalg.ts` |
| `sympy/calculus/accumulationbounds.py` | `core/accumbounds.ts`, `functions/elementary/accumbounds.ts` (functions of an interval) |
| `sympy/tensor/indexed.py` | `core/indexed.ts` |
| SymPy exceptions (`PolynomialError`, `NotInvertible`, ...) | `core/errors.ts` |
| (none: symjs's own) | `core/guard.ts`, `core/exprmap.ts`, `core/callable.ts`, `core/truth.ts`, `core/public.ts` |

### `functions/`, `simplify/`, `series/`

| SymPy module | symjs | Note |
|---|---|---|
| `functions/elementary/exponential.py`, `trigonometric.py`, `hyperbolic.py`, `complexes.py` (`Abs`, `re`, `im`, `arg`, `conjugate`) | `functions/elementary/elementary.ts` | not split: the evaluator table and `fn` that every function module registers into, with sin, cos, tan, their inverses, sinh, cosh, tanh, log, Abs, re, im, arg and conjugate, which the table and `fn` use directly |
| `functions/elementary/trigonometric.py`, `hyperbolic.py` (the other functions) | `functions/elementary/trigext.ts` | not split: cot, sec, csc, acot, asec, acsc, sinc and the reciprocal and inverse hyperbolic functions are registered by one table whose rules connect the two families (sin(I*x) = I*sinh(x), shifts by I*pi/2) and wrap the evaluators of `elementary.ts` |
| `functions/elementary/complexes.py` (polar numbers), `exponential.py` (`exp_polar`) | `functions/elementary/complexes.ts` | `polar_lift`, `periodic_argument`, `principal_branch`, `unbranched_argument`, `unpolarify`, `exp_polar` and the branch rules of the exponential integrals |
| `functions/elementary/integers.py`, `miscellaneous.py` | `functions/special/special.ts` | `floor`, `ceiling`, `Min`, `Max` (see below); `frac` is in `functions/combinatorial/numbers.ts` |
| `calculus/accumulationbounds.py` (functions of an interval) | `functions/elementary/accumbounds.ts` | no module of its own in SymPy (the `_eval` methods of the functions) |
| `functions/combinatorial/numbers.py` | `functions/combinatorial/numbers.ts` | also the number-theoretic functions (`totient`, `mobius`, `primepi`, ...), `multigamma` and `frac`, registered by the same table |
| `functions/combinatorial/factorials.py`, `functions/special/gamma_functions.py`, `error_functions.py`, `beta_functions.py`, `zeta_functions.py` (`zeta`), `elementary/complexes.py` (`sign`), `integers.py`, `miscellaneous.py`, `elementary/trigonometric.py` (`atan2`) | `functions/special/special.ts` | not split: one specification table registers the evaluators, derivatives, numerics and conjugation rules of all of them, and the evaluators share helpers (factorials and Gamma at integers, the numeric kernels); also `expand_func` |
| `functions/special/bessel.py` | `functions/special/bessel.ts`, `functions/special/sphericalbessel.ts` | the spherical Bessel and Hankel functions, `jn_zeros` and the hypergeometric rewrites of the Airy functions are a separate module because they need `functions/special/hyper.ts`, which imports `bessel.ts` |
| `functions/special/hyper.py` | `functions/special/hyper.ts` | also `appellf1`, and `jn`/`yn` (SymPy `bessel.py`) and `KroneckerDelta` (SymPy `tensor_functions.py`), which are registered with the hypergeometric rewrites and `expand_func` rules here |
| `functions/special/elliptic_integrals.py` | `functions/special/ellipticintegrals.ts` | |
| `functions/special/mathieu_functions.py` | `functions/special/mathieufunctions.ts` | |
| `functions/special/polynomials.py` | `functions/special/polynomials.ts` | |
| `functions/special/spherical_harmonics.py` | `functions/special/sphericalharmonics.ts` | |
| `functions/special/tensor_functions.py` | `functions/special/tensorfunctions.ts` | `LeviCivita`/`Eijk`; `KroneckerDelta` is in `hyper.ts` |
| `functions/special/zeta_functions.py` | `functions/special/zetafunctions.ts` | `zeta` itself is in `special.ts` |
| `functions/special/delta_functions.py`, `singularity_functions.py` | `integrals/transforms/delta.ts` (`DiracDelta`, `Heaviside`, `SingularityFunction`) | not moved: outside the three trees of this layout (an L3 module); `integrals/singularityfunctions.ts` ports `sympy/integrals/singularityfunctions.py` |
| `core/mod.py` | `functions/mod.ts` | `Mod` uses `floor` and the factorial, which `core/` cannot import |
| `simplify/simplify.py` | `simplify/simplify.ts`, `simplify/besselsimp.ts`, `simplify/separatevars.ts`, `simplify/gammasimp.ts` (`hypersimp`, `hypersimilar`) | `besselsimp` and `separatevars` are separate modules |
| `simplify/trigsimp.py` | `simplify/trigsimp.ts` | |
| `simplify/fu.py` | `simplify/fu.ts` | |
| `simplify/powsimp.py` | `simplify/powsimp.ts` | also `logcombine` and `posify` (SymPy `simplify.py`) |
| `simplify/radsimp.py` | `simplify/radsimp.ts`, `simplify/sqrtdenest.ts`, `simplify/rational.ts` (`fraction`) | `radsimp` itself is in `sqrtdenest.ts` (the two call each other) |
| `simplify/sqrtdenest.py` | `simplify/sqrtdenest.ts` | |
| `simplify/gammasimp.py`, `combsimp.py` | `simplify/gammasimp.ts` | not split: `combsimp` runs the private core of `gammasimp` |
| `simplify/ratsimp.py` | `simplify/ratsimp.ts` (`ratsimpmodprime`), `simplify/rational.ts` (`ratsimp`) | `ratsimp` shares the generator ordering of `cancel` |
| `simplify/cse_main.py`, `cse_opts.py` | `simplify/csemain.ts` | |
| `simplify/epathtools.py` | `simplify/epathtools.ts` | |
| `simplify/hyperexpand.py` | `simplify/hyperexpand.ts` | also the `HyperRep` functions of `functions/special/hyper.py` |
| `polys/rationaltools.py` (`together`), `polys/polytools.py` (`cancel`) | `simplify/rational.ts` | kept in `simplify/`: `polys/poly.ts` reaches it through `polyHooks` |
| `core/exprtools.py` | `simplify/exprtools.ts` | an L2 module (it uses the polynomials) |
| `core/function.py` (`expand`), `core/basic.py` (`rewrite`) | `simplify/expand.ts`, `simplify/rewrite.ts` | L1 modules |
| (none) | `simplify/public.ts` | the public `NoMatch` forms of the simplification functions |
| `series/series.py`, `series/order.py` | `series/series.ts` | `series`, `O`, `leadterm` |
| `series/limits.py` | `series/limits.ts` | |
| `series/gruntz.py` | `series/gruntz.ts` | |
| `series/limitseq.py` | `series/limitseq.ts` | also `difference_delta` |
| `series/residues.py` | `series/residues.ts` | |
| `series/sequences.py` | `series/sequences.ts` | |
| `series/formal.py` | `series/formal.ts` | |
| `series/fourier.py` | `series/fourier.ts` | |
| `core/expr.py` (`Expr.lseries`, `Expr.dir`) | `series/lseries.ts` | no SymPy module of its own; built on `series` and `limit` |
| (none: `Expr.nseries` and the `_eval_nseries` methods) | `series/puiseux.ts` | the truncated Puiseux series engine of `series` and `limit`; SymPy's `polys/puiseux.py` is the unrelated ring used by `ring_series` |

### Other packages

Modules not listed here follow the path rule (`sympy/crypto/crypto.py` ->
`crypto/crypto.ts`, `sympy/liealgebras/type_a.py` -> `liealgebras/typea.ts`,
`sympy/polys/galoistools.py` -> `polys/galoistools.ts`, ...).

| SymPy module | symjs | Note |
|---|---|---|
| `calculus/util.py` (`continuous_domain`, `function_range`, `lcim`) | `solvers/calculusutil.ts` | an L3 module (it solves inequalities); the other functions of `calculus/util.py` are in `solvers/inequalities.ts` |
| `concrete/delta.py`, `concrete/gosper.py` | `concrete/delta.ts`, `concrete/gosper.ts` | L3 modules (they solve equations), unlike `concrete/summations.ts` |
| `liealgebras/cartan_type.py` | `liealgebras/cartantype.ts`, `liealgebras/standard.ts` | `standard.ts` holds `Standard_Cartan`, the base of the `type_*` modules, which `cartan_type.py` also defines |
| `polys/galoistools.py` (`csolve_prime`) | `ntheory/residue.ts` | `gf_csolve` of the number theory (L1) is built on it |
| `polys/polyerrors.py` | `core/errors.ts`, `polys/polyerrors.ts` | the exceptions the core raises are in `core/errors.ts` |
| `printing/repr.py`, `tree.py`, `dot.py` | `printing/repr.ts`, `printing/tree.ts`, `printing/dot.ts` | they share SymPy's view of the tree (`core/compare.ts`) |

### `geometry/`

| SymPy module | symjs | Note |
|---|---|---|
| `geometry/entity.py` | `geometry/entity.ts` | also the constructor registry through which the lower geometry modules build points |
| `geometry/exceptions.py` | `geometry/exceptions.ts` | also `Undecidable` (SymPy `utilities/misc.py`), which the geometry raises |
| `geometry/point.py` | `geometry/point.ts` | |
| `geometry/line.py` | `geometry/line.ts` | |
| `geometry/plane.py` | `geometry/plane.ts` | |
| `geometry/ellipse.py` | `geometry/ellipse.ts` | |
| `geometry/polygon.py` | `geometry/polygon.ts` | |
| `geometry/curve.py` | `geometry/curve.ts` | |
| `geometry/parabola.py` | `geometry/parabola.ts` | |
| `geometry/util.py` | `geometry/util.ts` | `convex_hull`, `centroid` and `are_coplanar` build segments, polygons and planes through constructors those modules register (they import `util.ts`) |
| (none: SymPy `solve` of the coordinate equations) | `geometry/solvehelp.ts` | the systems the geometry solves (`solve([...], [x, y], dict=True)`), with SymPy's checks of assumptions and denominators |

### `vector/`

| SymPy module | symjs | Note |
|---|---|---|
| `vector/basisdependent.py` | `vector/basisdependent.ts` | also the arithmetic of vectors and dyadics (`add`/`mul` build VectorAdd/VectorMul, SymPy `_op_priority`), `CoordSysBase` and `DelBase` (what the lower modules know of CoordSys3D and Del) and `vectorHooks`, through which `express`, `laplacian`, `directional_derivative` and BaseDyadic reach the modules below them |
| `vector/kind.py` | `vector/kind.ts` | `kindOf(v)` of `@symjs/symjs/tensor` gives VectorKind through `ExtensionExpr.kindSelf` |
| `vector/scalar.py` | `vector/scalar.ts` | a BaseScalar is a symbol (`Sym`) named `C.x` that equals only the scalar of the same index and system |
| `vector/vector.py` | `vector/vector.ts` | also the unicode pretty form of vectors and dyadics (SymPy `PrettyPrinter._print_BasisDependent`) and of Cross and Dot; `dot` and `cross` are the functions of `matrices/linalg.ts`, which call the ones registered here for vectors |
| `vector/dyadic.py` | `vector/dyadic.ts` | |
| `vector/orienters.py` | `vector/orienters.ts` | |
| `vector/point.py` | `vector/point.ts` | also `_path` of `vector/functions.py` (the path between two points or systems of a tree) |
| `vector/coordsysrect.py` | `vector/coordsysrect.ts` | |
| `vector/operators.py` | `vector/operators.ts` | |
| `vector/deloperator.py` | `vector/deloperator.ts` | |
| `vector/functions.py` | `vector/functions.ts` | |
| `vector/implicitregion.py` | `vector/implicitregion.ts` | |
| `vector/parametricregion.py` | `vector/parametricregion.ts` | |
| `vector/integrals.py` | `vector/integrals.ts` | |

### `stats/`

| SymPy module | symjs | Note |
|---|---|---|
| `stats/rv.py` | `stats/rv.ts` | a RandomSymbol is a symbol (`Sym`) that carries its probability space (subs reaches the space through `Sym.substituteInner`); a RandomIndexedSymbol is a RandomSymbol named like its Indexed or applied function, and a RandomMatrixSymbol a MatrixSymbol that carries its space; spaces, domains and distributions are expression nodes; `statsClasses` holds the constructors of the modules below that rv.py imports locally (product and conditional spaces of each kind, handmade distributions, compound spaces, the Expectation and Probability nodes) |
| `stats/rv_interface.py` | `stats/rvinterface.ts` | |
| `stats/crv.py` | `stats/crv.ts` | also the multiple integrals of the domains (SymPy Integral with several limits: nested Integrals) |
| `stats/crv_types.py` | `stats/crvtypes.ts` | |
| `stats/drv.py` | `stats/drv.ts` | |
| `stats/drv_types.py` | `stats/drvtypes.ts` | |
| `stats/frv.py` | `stats/frv.ts` | an element of a finite domain (SymPy frozenset of (symbol, value) pairs) is an array of pairs, and as a key of a density the FiniteSet of the (symbol, value) Tuples |
| `stats/frv_types.py` | `stats/frvtypes.ts` | |
| `stats/compound_rv.py` | `stats/compoundrv.ts` | |
| `stats/error_prop.py` | `stats/errorprop.ts` | |
| `stats/symbolic_probability.py` | `stats/symbolicprobability.ts` | |
| `stats/joint_rv.py` | `stats/jointrv.ts` | the components X[i] of a joint random symbol are `X.at(i)` (Indexed); the integration and summation variables of expectations and marginals are symbols named like the components that sort like SymPy's Indexed variables |
| `stats/joint_rv_types.py` | `stats/jointrvtypes.ts` | list and matrix parameters are ImmutableMatrix arguments, as in SymPy; `Normal` and `Laplace` of `crvtypes.ts` reach the multivariate distributions through `statsClasses` |
| `stats/matrix_distributions.py` | `stats/matrixdistributions.ts` | |
| `stats/random_matrix.py` | `stats/randommatrix.ts` | |
| `stats/random_matrix_models.py` | `stats/randommatrixmodels.ts` | |
| `stats/stochastic_process.py` | `stats/stochasticprocess.ts` | SymPy's `Distribution()` of a process without a distribution is `UnspecifiedDistribution` |
| `stats/stochastic_process_types.py` | `stats/stochasticprocesstypes.ts` | X[n] of a discrete-time process is `X.at(n)` and X(t) of a continuous-time one `X.call(t)`; the Markov chains derive from `MarkovProcess` only (no multiple inheritance) |
| `stats/symbolic_multivariate_probability.py` | `stats/symbolicmultivariateprobability.ts` | ExpectationMatrix, VarianceMatrix and CrossCovarianceMatrix are matrix expressions; `Expectation`, `Variance` and `Covariance` of a matrix give them through `statsClasses` |
| `stats/sampling/sample_numpy.py`, `sample_scipy.py`, `sample_pymc.py` (and `sample`, `sample_iter`, `sampling_density`, `sample_stochastic_process`, `numsamples=` of `stats/rv.py` and the `sample` methods of the other stats modules) | not ported (out of scope) | they draw samples with the external Python libraries numpy, scipy and pymc, which have no JavaScript counterpart in symjs; their doctests are listed in `OUT_OF_SCOPE` of `compat/compat.test.ts` |

### Additional mathematical foundations

| SymPy module | symjs | Scope |
|---|---|---|
| `categories/baseclasses.py` | `categories/baseclasses.ts` | objects, morphisms, categories and diagrams; drawing diagrams (`categories/diagram_drawing.py`) is deferred like plotting |
| `combinatorics/perm_groups.py`, `named_groups.py` | `combinatorics/permgroups.ts`, `namedgroups.ts` | Schreier-Sims bases, membership, orbits, blocks, series, centralizers, cosets, SymmetricPermutationGroup, Coset and the named groups (AbelianGroup, RubikGroup, ...) |
| `combinatorics/util.py`, `generators.py`, `group_constructs.py`, `polyhedron.py` | `combinatorics/util.ts`, `generators.ts`, `groupconstructs.ts`, `polyhedron.ts` | base and strong generating set helpers, the Rubik's cube generators, DirectProduct, Polyhedron |
| `polys/numberfields/subfield.py` | `polys/numberfields/subfield.ts` | exact radical power-basis embeddings and bounded primitive-element search |
| `tensor/tensor.py` | `tensor/tensor.ts` | full port: index types, indices, slot symmetries, tensor heads, products and sums, Butler-Portugal canonicalization (`canon_bp`), metric contraction, component arrays (`replace_with_arrays`), TensorElement, wild tensors and the commutation groups of TensorManager |
| `combinatorics/tensor_can.py` | `tensor/tensorcan.ts` | the Butler-Portugal canonicalization of tensors under slot and dummy symmetries (`canonicalize`, `double_coset_can_rep`, `canonical_free`, `riemann_bsgs`) |
| `solvers/pde.py` | `solvers/pde.ts` | first-order linear PDEs with constant and variable coefficients, explicit solution checking and variable separation |
| `solvers/solveset.py` | `solvers/solveset.ts` | nonlinear-system substitution, including dependent exponential ImageSet components |
| `polys/rings.py`, `polys/compatibility.py` | `polys/rings.ts`, `polys/compatibility.ts` | sparse polynomial rings (`PolyRing`, `PolyElement`, `ring`, `xring`, `vring`, `sring`) and the `IPolys` methods; `fields.py` (`FracField`) is not ported yet |
| `polys/densebasic.py`, `polys/distributedmodules.py`, `polys/polyoptions.py`, `polys/constructor.py` | `polys/densebasic.ts`, `polys/distributedmodules.ts`, `polys/polyoptions.ts`, `polys/constructor.ts` | |
| `polys/domains/*.py` | `polys/domains.ts` (ZZ, QQ, RR, EX and the polynomial rings and fraction fields), `polys/domains/*.ts` (finite fields, Gaussian domains, algebraic fields, CC, EXRAW) | `ANP` of `polys/polyclasses.py` is in `polys/domains/algebraicfield.ts`; `PythonMPQ` of `sympy/external/pythonmpq.py` in `polys/domains/pythonrational.ts` |
| `polys/matrices/ddm.py`, `sdm.py`, `dense.py`, `domainmatrix.py`, `domainscalar.py`, `exceptions.py`, `rref.py`, `normalforms.py` | `polys/matrices/<same name>.ts` | `polys/matrices/domainops.ts` holds the ring operations of the domains on the expression form of the matrix elements; `lll.py`, `linsolve.py`, `eigen.py` and the `dfm` modules are not ported |
| `matrices/normalforms.py` | `matrices/normalforms.ts` | also SymPy's `polys/matrices/normalforms.py` for DomainMatrix input (one function per SymPy name); `matrices/domainmatrix.ts` holds `to_DM` of `repmatrix.py` |
| `sets/ordinals.py` | `sets/ordinals.ts` | |
| `core/parameters.py`, `core/rules.py` | `core/parameters.ts`, `core/rules.ts` | `with evaluate(False)` is `evaluate(false, () => ...)` |
| `ntheory/elliptic_curve.py`, `ntheory/bbp_pi.py` | `ntheory/ellipticcurve.ts`, `ntheory/bbppi.ts` | |
| `assumptions/relation/binrel.py` | `assumptions/relation/binrel.ts` | `BinaryRelation` |
| `assumptions/satask.py`, `lra_satask.py`, `cnf.py`, `facts.py`, `ask_generated.py`, `logic/algorithms/lra_theory.py` | `assumptions/satask.ts`, `lrasatask.ts`, `cnf.ts`, `facts.ts`, `askgenerated.ts`, `logic/algorithms/lratheory.ts` | |
| `printing/pretty/pretty.py` (morphisms, categories and diagrams) | `categories/pretty.ts` | registered by the categories entry |
| `integrals/intpoly.py` | `integrals/intpoly.ts` | the helpers are members of the namespace `intpoly`; Polygon, Segment and Point are accepted by their structure (the integrals layer does not import geometry) |
| `concrete/guess.py`, `series/approximants.py` | `concrete/guess.ts`, `series/approximants.ts` | L2 modules |
| `parsing/mathematica.py` | `parsing/mathematica.ts` | `parse_mathematica`, `MathematicaParser`; exported by the simplify entry, which also registers `cancel` for `Cancel` through the parser hook; the deprecated `mathematica()` parser is not ported |
| `solvers/simplex.py`, `solvers/bivariate.py` | `solvers/simplex.ts`, `solvers/bivariate.ts` | `lpmin`, `lpmax`, `linprog`, `show_linprog`; `bivariate_type` (the Lambert W helpers stay in `solvers/solve.ts`) |
| `solvers/ode/single.py` | `solvers/ode/single.ts` (`SingleODEProblem`, `SingleODESolver`, `NthAlgebraic`), `solvers/dsolve.ts` (the hint solvers) | |

## Scope decisions

Every SymPy module has a status in `compat/scope-inventory.json`
(generated by `compat/inventory.py`): partial (a symjs counterpart exists),
unimplemented (with a note on where it is planned), excluded (with the
reason) or unassessed. Mathematical content is never excluded.

| SymPy modules | Decision |
|---|---|
| `printing/c.py`, `cxx.py`, `fortran.py`, `rust.py`, `octave.py`, `julia.py`, `maple.py`, `mathematica.py`, `glsl.py`, `rcode.py`, `smtlib.py`, `codeprinter.py`; the AST and node modules of `codegen/`; `utilities/codegen.py` | extend package `@symjs/codegen` (planned) |
| `codegen/cfunctions.py`, `rewriting.py`, `approximations.py`, `algorithms.py` | base module (not ported yet) |
| `printing/pycode.py`, `numpy.py`, `lambdarepr.py`, `python.py`, `codegen/pyutils.py`, `utilities/autowrap.py` | out of scope: they generate or compile Python code |
| `printing/jscode.py` | not ported: JavaScript code output is not needed for now |
| `parsing/latex/` | base module (not ported yet) |
| `parsing/maxima.py`, `autolev/`, `c/`, `fortran/`, `sym_expr.py` | extend package (planned) |
| `diffgeom/` | extend package (planned) |
| `physics/` | extend packages per field, in an order decided later; `physics/quantum/` is `@symjs/physics-quantum` (partial) |
| `plotting/`, `categories/diagram_drawing.py`, `printing/preview.py` | deferred (rendering and display) |
| test runners and helpers, caching, dispatch decorators, compilation helpers, release metadata, the gmpy2/python-flint ground-type back ends, SAT-solver bindings, typing protocols, REPL and display helpers | out of scope: Python-runtime tooling |

The condition-level scope and remaining limitations are maintained in
[`compat/capabilities.json`](../compat/capabilities.json). API existence and
source-file size do not establish full SymPy compatibility.
