# Public API policy of `@symjs/symjs`

Status: adopted (2026-11-02) and implemented; it may change by decision of the community.

## Conventions

1. **Names are camelCase.** SymPy functions keep their SymPy name converted mechanically from snake_case (`factor_list` -> `factorList`, `expand_log` -> `expandLog`).
2. **Classes use SymPy's names** (`Integer`, `Rational`, `Float`, `Add`, `Mul`, `Pow`, `Derivative`, `Integral`, `Piecewise`, `Interval`, `FiniteSet`, `And`, ...), **except names that are JavaScript globals**, which would shadow the global wherever they are imported: SymPy `Symbol` is `Sym`, `Number` is `SymNumber`, `Function` is `SymFunction`, `Array` is `SymArray` and `Set` is `SetExpr`. The SymPy spellings `Symbol`, `Number`, `Function` and `Array` remain as deprecated aliases during 0.x and are removed in 1.0.
3. **Functions are primary; methods are thin aliases.** `subs(e, ...)`, `expand(e)`, ... are the API. `e.subs(...)`, `e.expand()` call the same functions, so unused features stay out of bundles.
4. **Keyword arguments are a trailing options object** with camelCase keys (`factor(e, { deep: true })`, `solve(e, x, { cubics: false })`). Positional arguments follow SymPy's order.
5. **Inputs accept `ExprLike`** (expressions, numbers, bigints, strings parsed like `sympify`).
6. **Results have SymPy's structure:** lists are arrays, tuples are fixed-length arrays, dicts are `Map`s keyed by expressions, sets are `SetExpr`. Where SymPy returns either one value or a list (`dsolve`), symjs does the same.
7. **Failures behave like SymPy:** an error where SymPy raises, an unevaluated object where SymPy returns one (`Integral`, `ConditionSet`, ...).
8. **Mathematical correctness wins** where SymPy's output is wrong; such cases are documented.
9. **Results are never `undefined` or `null`** (see below).
10. **One definition per name.** A name means the same function or class in every entry point that exports it. Where SymPy has one name in two modules (`is_palindromic` of an integer in `ntheory` and of a sequence in `utilities.iterables`, `connected_components` of a graph and the `Matrix` method), the one function accepts both forms. `factorint` is exported by `ntheory` and the root entry only (the core entry keeps the deprecated `factorInt`).

## Results of the public computation API

The public computation API of symjs does not represent a missing result with `undefined` or `null`. An unevaluated computation is kept as an expression; an undecidable answer, a mismatch and the absence of a solution each have a type with a meaning. Invalid input is reported as a clear error according to the contract of each API.

symjs keeps SymPy's mathematical meaning while letting TypeScript handle the state of a result explicitly.

| Situation | SymPy | symjs |
|---|---|---|
| A computation that cannot be carried out | an unevaluated object | the unevaluated expression (`Integral`, `Limit`, `ConditionSet`, ...) |
| An undecidable predicate (`is_positive`, `ask`, `is_convergent`, `is_subset`, ...) | `None` | `Truth`: `true`, `false` or `'unknown'` |
| The expression does not have the requested form (`match`, `extract_additively`, `as_coefficient`, `hypersimp`, `homogeneous_order`, `periodicity`, ...) | `None` | `NoMatch` |
| The methods find no solution in closed form (`rsolve`, ...) | `None` | `Unsolved` (not a proof that none exists) |
| No solution exists (`linsolve`, `solveset`, ...) | `EmptySet` | `EmptySet` |
| Valid input that the implemented methods cannot handle (an ODE `dsolve` cannot solve, an equation `solve` cannot solve, ...) | `NotImplementedError` | a thrown `NotImplementedError` |
| Invalid input (a nonlinear system for `linear_eq_to_matrix`, a value that cannot be sympified, ...) | an exception | a thrown error (`NonlinearError`, `SympifyError`, `RangeError`, ...) |

`'unknown'` is truthy: test a `Truth` with `isTrue`, `isFalse` or `isUnknown` (or compare with `=== true`), never with `if (truth)`. `truthNot`, `truthAnd` and `truthOr` combine answers with three-valued logic.

Exceptions, which follow other contracts: the hooks of `ExtensionExpr` (`diffSelf`, `rewriteSelf`, ...) that extension authors implement, where `undefined` means "no override"; `ExprMap.get`, which keeps the standard `Map` contract; functions returning `void`.

The policy is enforced by:

- `tsconfig.json`: `strict` (including `strictNullChecks`), `noImplicitReturns`, `noUncheckedIndexedAccess`.
- `pnpm lint` (Oxlint with type-aware rules): `explicit-module-boundary-types` (exported functions declare their return type), `strict-boolean-expressions` (no truthiness test of a `Truth`), `switch-exhaustiveness-check`.
- `packages/symjs/tests/api-results.test.ts`: no public function or method of the base module or the extend modules has `undefined` or `null` in its return type.

## Stability levels

- **stable**: documented and covered by semantic versioning from 1.0 on.
- **experimental**: exported, but may change in a minor release (marked `@experimental`).
- **internal**: implementation details; to be removed from the public entry point.
- **deprecated**: kept as an alias of the new name during 0.x, removed in 1.0.

Renamed exports keep their old name as a `@deprecated` alias during 0.x; exports classified as internal are likewise deprecated during 0.x and removed from the entry points in 1.0. The public API is recorded in [packages/symjs/api-report.md](../packages/symjs/api-report.md) (every export of every entry point with its kind and level, from the `@experimental` and `@deprecated` JSDoc tags), generated and checked by `tests/api-report.test.ts`; changes to it are reviewed with every change.

Notes on the implementation:

- `Derivative` and `Piecewise` are the node classes and can also be called like SymPy's constructors (`Derivative(f(x), x, [y, 2])`, `Piecewise([x, Lt(x, 0)], [0, true])`).
- Results that are dicts in SymPy are `ExprMap`s: `Map`s whose expression keys compare structurally. `roots(f, x)` returns root -> multiplicity; `roots(f, x, { multiple: true })` returns the list.
- `div` is SymPy's polynomial division; the former arithmetic helper `div(a, b)` is `a.div(b)` (or `mul(a, pow(b, -1))`).
- `expandMul` is SymPy's `expand_mul`.
- `intersection` is SymPy's top-level `intersection` of geometric entities (`sympy.geometry.util`), exported by `@symjs/symjs/geometry`; given only sets it returns their `Intersection` (one function for both forms). The former deprecated set alias `intersection` of `@symjs/symjs/sets` is removed: SymPy's name for it is the class `Intersection`.
- `Curve` is SymPy's geometric `Curve` (`@symjs/symjs/geometry`), an expression node; `lineIntegrate` takes any curve with `functions` and `limits` (the `ParametricCurve` type of `@symjs/symjs/calculus`), so the calculus entry no longer exports a `Curve` class of its own.

## Entry points and tree-shaking

- The package has one entry point per feature area: `core`, `special`, `simplify`, `polys`, `calculus`, `solvers`, `sets`, `matrices`; the root `@symjs/symjs` re-exports all of them. Every export belongs to exactly one entry point.
- **The core does not import the other areas** (checked by `tests/entries.test.ts`). Where the core needs a feature of another area (`expr.simplify()`, `expr.integrate()`, `expr.series()`, `expr.rewrite()`), it calls a late-bound implementation that the area registers when loaded; without it the call throws an error naming the entry point to import. Core functions that merely use another area when available (for example `isConstant` simplifying a derivative) fall back to working without it.
- **Importing an entry point makes everything it contains available**, including late-bound implementations: entry points are listed as having side effects, and every entry point imports the core.
- Modules with top-level side effects (registrations into the core registries) are listed in `sideEffects` in `package.json`, generated by `scripts/side-effects.mjs`; all other modules are side-effect free. New registrations must live in such a module and the list must be regenerated (the tests fail otherwise).
- Conditional exports select ESM `.d.ts` or CommonJS `.d.cts` declarations with explicit relative extensions. `pnpm test:package` checks the published files with NodeNext and Bundler resolution, and executes ESM/CJS and minified consumers.
- The build keeps one output file per source module (ESM `.js` and CommonJS `.cjs`), so consumers' bundlers can drop unused modules and every entry point shares one copy of the classes and registries.
- Size budgets for typical imports are checked by `scripts/size.mjs --check`; a budget is raised only together with the change that needs it.

## Inventory (461 exports)

| Group | Count | Treatment |
|---|---:|---|
| Same name as a SymPy public name | 194 | stable |
| SymPy name after camelCase conversion | 53 | stable |
| SymPy method as a function | 62 | stable |
| symjs-specific or internal | 154 | classified below |

## Classification of symjs-specific and internal exports

| Export | Level | New name | Note |
|---|---|---|---|
| `Sym` | stable |  | SymPy `Symbol` (renamed: `Symbol` is a JavaScript global) |
| `Constant` | stable | `NumberSymbol` | pi, E, ... (SymPy NumberSymbol) |
| `Fn` | experimental | `AppliedFunction` | node class of known functions |
| `BoolAtom` | stable | `BooleanAtom` | SymPy class name |
| `Special` | internal |  | oo, zoo, nan are reached through S |
| `UndefFn` | stable | `AppliedUndef` | SymPy class name |
| `S` | stable |  | SymPy singleton registry |
| `compareExpr` | internal |  | use ordered/sortKey |
| `isRational` | stable |  | SymPy is_Rational |
| `isFloat` | stable |  | SymPy is_Float |
| `isSymbol` | stable |  | SymPy is_Symbol |
| `isAdd` | stable |  | SymPy is_Add |
| `isMul` | stable |  | SymPy is_Mul |
| `isPow` | stable |  | SymPy is_Pow |
| `isFn` | stable | `isFunction` | SymPy is_Function |
| `isInteger` | stable |  | SymPy is_Integer (type guard) |
| `isNum` | stable | `isNumber` | SymPy is_Number |
| `ExtensionExpr` | stable |  | base class for extend modules |
| `mul` | stable |  | arithmetic helper (SymPy Mul) |
| `sub` | stable |  | arithmetic helper |
| `neg` | stable |  | arithmetic helper |
| `rational` | deprecated | `Rational.of` |  |
| `splitCoeff` | internal |  | use asCoeffMul |
| `isReal` | stable |  | assumption query (SymPy is_real) |
| `isPositive` | stable |  | assumption query |
| `isNegative` | stable |  | assumption query |
| `isNonNegative` | stable |  | assumption query |
| `isNonZero` | stable |  | assumption query |
| `isZero` | stable |  | assumption query |
| `isIntegerQ` | stable | `isIntegerValued` | assumption query (SymPy is_integer) |
| `keepCoeff` | internal |  | SymPy _keep_coeff (private) |
| `argsCncSplit` | internal |  | use argsCnc |
| `asTwoTerms` | stable |  | SymPy as_two_terms |
| `freeSymbols` | stable |  | SymPy free_symbols |
| `mapBottomUp` | stable | `bottomUp` | SymPy bottom_up |
| `rebuild` | experimental |  | func(*args) for extension authors |
| `ordered` | stable |  | SymPy ordered |
| `countOpsVisual` | internal |  | countOps(e, { visual: true }) |
| `isInstance` | internal |  |  |
| `fn` | experimental |  | build a known function by name |
| `abs` | stable | `Abs` | SymPy class name (abs kept as alias) |
| `dagger` | experimental |  | SymPy physics Dagger |
| `beta` | stable |  | SymPy beta |
| `zeta` | stable |  | SymPy zeta |
| `besselj` | stable |  | SymPy besselj |
| `bessely` | stable |  | SymPy bessely |
| `besseli` | stable |  | SymPy besseli |
| `besselk` | stable |  | SymPy besselk |
| `airyai` | stable |  | SymPy airyai |
| `airybi` | stable |  | SymPy airybi |
| `airyaiprime` | stable |  | SymPy airyaiprime |
| `airybiprime` | stable |  | SymPy airybiprime |
| `functions` | internal |  | symbols(..., { cls: SymFunction }) |
| `derivative` | stable | `Derivative` | SymPy class name |
| `transformIntegral` | stable |  | Integral.transform |
| `principalValue` | stable |  | Integral.principal_value |
| `doitConcrete` | internal |  | use doit |
| `reverseOrder` | stable |  | Sum.reverse_order |
| `Concrete` | experimental |  | node class of Sum/Product |
| `rel` | internal |  | use Eq, Lt, ... |
| `piecewise` | stable | `Piecewise` | SymPy class name |
| `registerRewrite` | experimental |  | rewrite rules for extend modules |
| `rewriteRules` | internal |  |  |
| `keepCoeffSympy` | internal |  |  |
| `unevaluatedAdd` | internal |  |  |
| `rewriteExp` | internal |  | rewrite(e, 'exp') |
| `rewriteTrig` | internal |  | rewrite(e, 'cos') |
| `expsimp` | internal |  |  |
| `exptotrig` | internal |  |  |
| `combineExp` | internal |  |  |
| `UPoly` | internal |  | use Poly |
| `polyCoefficients` | internal |  | use Poly |
| `factorPoly` | internal |  | use factorList |
| `PolificationFailed` | stable |  | SymPy exception |
| `polyDiv` | stable | `div` | SymPy div |
| `sortGens` | internal |  |  |
| `mgcd` | internal |  | use gcd |
| `mlcm` | internal |  | use lcm |
| `divExact` | internal |  | use exquo |
| `CRootOf` | stable |  | SymPy CRootOf |
| `rootOf` | stable | `rootof` | SymPy rootof |
| `asEquation` | internal |  |  |
| `invertEquation` | internal |  | SymPy _invert (private) |
| `odeOrder` | stable |  | SymPy ode_order |
| `piecewiseIntegrate` | internal |  | integrate handles Piecewise |
| `sumIsConvergent` | stable | `isConvergent` | Sum.is_convergent |
| `sumIsAbsolutelyConvergent` | stable | `isAbsolutelyConvergent` | Sum.is_absolutely_convergent |
| `symmetrizeExpr` | internal |  | use symmetrize |
| `evalfPrec` | internal |  | evalf with a binary precision |
| `toComplex` | experimental |  | double-precision value |
| `lambdify` | stable |  | SymPy lambdify |
| `float` | stable |  | Float constructor helper |
| `precToDps` | stable |  | mpmath prec_to_dps |
| `dpsToPrec` | stable |  | mpmath dps_to_prec |
| `str` | stable | `sstr` | SymPy sstr (str kept as alias) |
| `orderedTerms` | stable | `asOrderedTerms` | SymPy as_ordered_terms |
| `orderedFactors` | stable | `asOrderedFactors` | SymPy as_ordered_factors |
| `compareKeys` | internal |  |  |
| `latex` | stable |  | SymPy latex |
| `parse` | stable | `parseExpr` | SymPy parse_expr (parse kept as alias) |
| `ex` | experimental |  | tagged template parser |
| `matrixExp` | stable |  | Matrix.exp |
| `matrixLog` | stable |  | Matrix.log |
| `ldl` | stable | `LDLdecomposition` | Matrix.LDLdecomposition |
| `luDecomposition` | stable | `LUdecomposition` | Matrix.LUdecomposition |
| `qrDecomposition` | stable | `QRdecomposition` | Matrix.QRdecomposition |
| `blockDiag` | stable |  | SymPy block_diag |
| `permanent` | stable |  | Matrix.permanent |
| `rationalFromFloat` | internal |  | Rational.fromFloat |
| `rationalFromString` | internal |  | Rational.fromString |
| `expandSymbolNames` | internal |  | symbols() parsing |
| `limitDenominator` | stable |  | Rational.limit_denominator |
| `factorInt` | stable | `factorint` | SymPy factorint |
| `extractLeadingOrder` | internal |  |  |
| `finiteDiffWeights` | stable |  | SymPy finite_diff_weights |
| `asFiniteDifference` | stable |  | Derivative.as_finite_difference |
| `SetExpr` | stable |  | SymPy Set (JavaScript Set is taken) |
| `Interval` | stable |  | SymPy Interval |
| `FiniteSet` | stable |  | SymPy FiniteSet |
| `SetOp` | internal |  | Union/Intersection/Complement nodes |
| `ImageSet` | stable |  | SymPy ImageSet |
| `ConditionSet` | stable |  | SymPy ConditionSet |
| `imageSet` | stable | `imageset` | SymPy imageset |
| `EmptySet` | stable |  | SymPy EmptySet |
| `Reals` | stable |  | SymPy Reals |
| `Integers` | stable |  | SymPy Integers |
| `Naturals` | stable |  | SymPy Naturals |
| `Naturals0` | stable |  | SymPy Naturals0 |
| `Complexes` | stable |  | SymPy Complexes |
| `interval` | deprecated | `Interval.of` |  |
| `openInterval` | deprecated | `Interval.open` | SymPy Interval.open |
| `Lopen` | deprecated | `Interval.Lopen` | SymPy Interval.Lopen |
| `Ropen` | deprecated | `Interval.Ropen` | SymPy Interval.Ropen |
| `finiteSet` | deprecated | `FiniteSet.of` |  |
| `union` | stable | `Union` | SymPy class name |
| `intersection` | stable |  | SymPy geometry `intersection` (`@symjs/symjs/geometry`); sets are intersected with `Intersection` |
| `complement` | stable | `Complement` | SymPy class name |
| `contains` | stable |  | Set.contains |
| `containsQ` | internal |  |  |
| `isSubset` | stable |  | Set.is_subset |
| `asRelational` | stable |  | Set.as_relational |
| `inf` | stable |  | Set.inf |
| `sup` | stable |  | Set.sup |
| `BoolOp` | internal |  | And/Or/Not nodes |
| `and` | stable | `And` | SymPy class name |
| `or` | stable | `Or` | SymPy class name |
| `not` | stable | `Not` | SymPy class name |
| `asExprSetPairs` | stable |  | Piecewise.as_expr_set_pairs |
| `isprime` | stable |  | SymPy isprime |
| `firstMotzkins` | experimental |  | motzkin.find_first_n_motzkins |
| `motzkinNumbersInRange` | experimental |  | motzkin.find_motzkin_numbers_in_range |
| `isMotzkin` | experimental |  | motzkin.is_motzkin |
| `factorSystemCond` | stable |  | SymPy factor_system_cond |
| `symbol` | stable |  | Symbol constructor helper |
| `expand_mul` | stable | `expandMul` | camelCase |
| `expand_multinomial` | stable | `expandMultinomial` | camelCase |
| `expand_power_exp` | stable | `expandPowerExp` | camelCase |
| `expand_power_base` | stable | `expandPowerBase` | camelCase |
| `expand_log` | stable | `expandLog` | camelCase |
| `expand_trig` | stable | `expandTrig` | camelCase |
| `expand_complex` | stable | `expandComplex` | camelCase |
