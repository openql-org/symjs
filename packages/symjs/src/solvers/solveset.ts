// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14 (solvers/solveset.py), BSD-3-Clause; see LICENSE.

import type { Expr, ExprLike, FnName } from '../core/nodes';
import { Add, Constant, Dummy, Fn, Mul, Pow, Rational, Rel, S, Special, Sym } from '../core/nodes';
import { isNegative, isNonNegative, isPositive } from '../core/assumptions';
import { at, defined } from '../core/guard';
import { add, mul, pow, sympify } from '../core/ops';
import { fn, log } from '../functions/elementary/elementary';
import { mapBottomUp, some, subs, xreplace } from '../core/traverse';
import { NonlinearError, NotImplementedError } from '../core/errors';
import { NoMatch, type NoMatchResult } from '../core/truth';
import { Complexes, ConditionSet, EmptySet, FiniteSet, ImageSet, Integers, Interval, Reals, SetOp, type SetExpr, complement, imageSet, intersection, productSet, union } from '../sets/sets';
import { factorTerms } from '../simplify/exprtools';
import { polyCoefficients, rootsCubicFormula } from '../polys/poly';
import { CRootOf } from '../polys/rootof';
import { isNonzero } from '../core/public';
import { expand, expand_log } from '../simplify/expand';
import { cancel } from '../simplify/rational';
import { asEquation, denoms, linearEqToMatrix, nonlinsolve as finiteNonlinsolve, solve, solveAugmented } from './solve';
import { periodicity, solveset } from './inequalities';
import { decompogen } from './decompogen';
import { functionRange } from './calculusutil';
import { Tuple } from '../core/containers';
import { and } from '../core/boolalg';
import { asNumerDenom, asRealImag } from '../core/methods';
import { integerLog } from '../core/numberutils';
import { compareKeys, sortKey } from '../printing/sortkey';
import { Eq, Ne } from '../core/logic';

/** Whether every subexpression is finite at the proposed solution. */
export function domainCheck(f: ExprLike, symbol: Sym, p: ExprLike): boolean {
  const point = sympify(p);
  if (point instanceof Special) return false;
  const check = (e: Expr): boolean => !(subs(e, [[symbol, point]]) instanceof Special) && e.args.every(check);
  return check(sympify(f));
}

/** Linear coefficients followed by the constant term; rejects nonlinear structure before expansion. */
export function linearCoeffs(eq: ExprLike, ...syms: Sym[]): Expr[] {
  if (new Set(syms.map((s) => s.key)).size !== syms.length) throw new RangeError('linearCoeffs: duplicate symbols');
  const zero = (): Expr[] => Array.from({ length: syms.length + 1 }, () => S.Zero);
  const visit = (e: Expr): Expr[] => {
    const i = syms.findIndex((s) => s.equals(e));
    if (i >= 0) { const out = zero(); out[i] = S.One; return out; }
    if (!syms.some((s) => e.has(s))) { const out = zero(); out[syms.length] = e; return out; }
    if (e instanceof Add) {
      const rows = e.args.map(visit);
      return zero().map((_, j) => add(...rows.map((r) => at(r, j))));
    }
    if (e instanceof Mul) {
      const dep = e.args.filter((a) => syms.some((s) => a.has(s)));
      if (dep.length !== 1) throw new NonlinearError('linearCoeffs: symbol-dependent cross-terms');
      const independent = mul(...e.args.filter((a) => !syms.some((s) => a.has(s))));
      return visit(at(dep, 0)).map((c) => mul(independent, c));
    }
    throw new NonlinearError('linearCoeffs: nonlinear in given generators');
  };
  return visit(asEquation(eq));
}

/** Solve over the real domain. */
export function solvesetReal(f: ExprLike, symbol: ExprLike): SetExpr {
  return solveset(f, symbol, Reals);
}

/** Solve over the complex domain. */
export function solvesetComplex(f: ExprLike, symbol: ExprLike): SetExpr {
  return solveset(f, symbol, Complexes);
}

/** Solve successive outer functions in a functional decomposition. */
export function solveDecomposition(f: ExprLike, symbol: Sym, domain: SetExpr): SetExpr {
  const expression = sympify(f);
  let values: SetExpr = FiniteSet.of(S.Zero);
  for (const g of decompogen(expression, symbol)) {
    const range = domain === Reals && g instanceof Fn && (g.name === 'sin' || g.name === 'cos') ? Interval.of(-1, 1) : functionRange(g, symbol, domain);
    values = range === Reals ? values : intersection(values, range);
    if (values === EmptySet) return EmptySet;
    const parts = values instanceof SetOp && values.op === 'Union' ? values.args : [values];
    const results: SetExpr[] = [];
    for (const part of parts) {
      if (part instanceof FiniteSet) {
        for (const value of part.args) results.push(solveset(add(g, mul(-1, value)), symbol, domain));
      } else if (part instanceof ImageSet) {
        const solutions = solveset(add(g, mul(-1, part.expr)), symbol, domain);
        const finite = solutions instanceof FiniteSet ? solutions : solutions instanceof SetOp && solutions.op === 'Intersection' ? solutions.args.find((s) => s instanceof FiniteSet) : undefined;
        if (finite instanceof FiniteSet) for (const value of finite.args) results.push(imageSet(part.variable, value, part.base));
        else return new ConditionSet(symbol, Eq(expression, 0), domain);
      } else return new ConditionSet(symbol, Eq(expression, 0), domain);
    }
    values = union(...results);
  }
  return values;
}

function invert(f: ExprLike, y: ExprLike, x: Sym, domain: SetExpr): [Expr, SetExpr] {
  const expression = sympify(f), value = sympify(y);
  if (![...expression.freeSymbols()].some((s) => s.equals(x)) || [...value.freeSymbols()].some((s) => s.equals(x))) throw new RangeError('invert: f must depend on x and y must be independent of x');
  const solutions = solveset(add(expression, mul(-1, value)), x, domain);
  return solutions instanceof ConditionSet ? [expression, FiniteSet.of(value)] : [x, solutions];
}

/** Invert f(x) = y over the complex numbers, retaining unresolved equations. */
export function invertComplex(f: ExprLike, y: ExprLike, x: Sym): [Expr, SetExpr] {
  return invert(f, y, x, Complexes);
}

/** Invert f(x) = y over the real numbers, retaining unresolved equations. */
export function invertReal(f: ExprLike, y: ExprLike, x: Sym): [Expr, SetExpr] {
  const expression = sympify(f), value = sympify(y);
  if (![...expression.freeSymbols()].some((s) => s.equals(x)) || [...value.freeSymbols()].some((s) => s.equals(x))) throw new RangeError('invert: f must depend on x and y must be independent of x');
  const visit = (e: Expr, values: readonly Expr[]): [Expr, SetExpr] => {
    if (e.equals(x) || values.length === 0) {
      const known = values.filter((v) => v instanceof Fn && v.name === 'acsch' && (isPositive(at(v.args, 0)) === true || isNegative(at(v.args, 0)) === true));
      return [x, union(FiniteSet.of(...known), intersection(FiniteSet.of(...values.filter((v) => !known.includes(v))), Reals))];
    }
    if (e instanceof Add || e instanceof Mul) {
      const independent = e.args.filter((a) => !a.has(x));
      if (independent.length) {
        const dependent = e.args.filter((a) => a.has(x));
        const c = e instanceof Add ? add(...independent) : mul(...independent);
        return visit(e instanceof Add ? add(...dependent) : mul(...dependent), values.map((v) => e instanceof Add ? add(v, mul(-1, c)) : mul(v, pow(c, -1))));
      }
    }
    if (e instanceof Fn) {
      const arg = at(e.args, 0);
      if (e.name === 'log') return visit(arg, values.map((v) => pow(S.E, v)));
      if (e.name === 'abs' && values.every((v) => isNonNegative(v) === true)) return visit(arg, values.flatMap((v) => [v, mul(-1, v)]));
      const inverse: Readonly<Partial<Record<FnName, FnName>>> = { sinh: 'asinh', cosh: 'acosh', tanh: 'atanh', coth: 'acoth', sech: 'asech', csch: 'acsch' };
      const name = inverse[e.name];
      if (name !== undefined) {
        return visit(arg, values.flatMap((v) => {
          const root = fn(name, [v]);
          return e.name === 'cosh' || e.name === 'sech' ? [mul(-1, root), root] : [root];
        }));
      }
    }
    if (e instanceof Pow && !e.base.has(x) && isPositive(e.base) === true) return visit(e.exp, values.filter((v) => !v.equals(S.Zero)).map((v) => mul(log(v), pow(log(e.base), -1))));
    if (e instanceof Pow && e.exp instanceof Constant && (e.exp.name === 'pi' || e.exp.name === 'E') && values.every((v) => isNegative(v) === true)) return [x, EmptySet];
    const results = values.map((v) => invert(e, v, x, Reals));
    if (results.every(([lhs]) => lhs.equals(x))) return [x, union(...results.map(([, rhs]) => rhs))];
    return [e, FiniteSet.of(...values)];
  };
  return visit(expression, [value]);
}

/** Finite solutions, or representatives in one period; NoMatch for other infinite sets. */
export function solvify(f: ExprLike, symbol: Sym, domain: SetExpr): Expr[] | NoMatchResult {
  const result = solveset(f, symbol, domain);
  if (result === EmptySet) return [];
  if (result instanceof ConditionSet) throw new NotImplementedError('solvify: solveset could not solve the equation');
  if (result instanceof FiniteSet) return [...result.args];
  const period = periodicity(f, symbol);
  const parts = result instanceof SetOp && result.op === 'Union' ? result.args : [result];
  if (period === undefined) {
    const finite = parts.flatMap((part) => part instanceof FiniteSet ? part.args : []);
    return finite.length ? finite : NoMatch;
  }
  if (parts.every((s) => s instanceof ImageSet)) {
    const window = Interval.Ropen(0, period);
    const principal = union(...parts.map((s) => intersection(s, window)));
    if (principal instanceof FiniteSet) return [...principal.args];
  }
  return NoMatch;
}

/**
 * Solve a nonlinear system over the complex numbers. Infinite solution
 * components are ImageSets, rather than a list of principal logarithms.
 * The remaining algebraic systems use polynomial elimination.
 */
export function nonlinsolve(system: readonly ExprLike[], symbols: readonly Expr[], options: { asSet: true }): SetExpr;
export function nonlinsolve(system: readonly ExprLike[], symbols: readonly Expr[]): Expr[][];
export function nonlinsolve(system: readonly ExprLike[], targets: readonly Expr[], options?: { asSet: true }): SetExpr | Expr[][] {
  if (system.length === 1 && targets.length === 1) {
    const target = at(targets, 0);
    const equation = sympify(at(system, 0));
    let solutions = solveset(equation, target);
    if (equation instanceof Rel && target instanceof Sym) {
      const poles = [...denoms(equation.lhs, target), ...denoms(equation.rhs, target)];
      solutions = complement(solutions, union(...poles.map((d) => solveset(d, target))));
    }
    const rows = solutions instanceof FiniteSet ? solutions.args.map((value) => [value]) : [[solutions]];
    return options ? FiniteSet.of(...rows.map((row) => Tuple(...row))) : rows;
  }
  const replacements = targets.filter((e) => !(e instanceof Sym)).map((e): [Expr, Sym] => [e, new Dummy('u')]);
  const symbols = targets.map((e) => e instanceof Sym ? e : defined(replacements.find(([old]) => old.equals(e)))[1]);
  const equations = system.map((e) => subs(sympify(e), replacements));
  const back = replacements.map(([original, variable]): [Expr, Expr] => [variable, original]);
  const exponential = exponentialSystem(equations, symbols);
  if (exponential) {
    const [indices, values] = exponential;
    const signature = Tuple(...indices);
    const coordinates = values.map((value) => xreplace(value, back));
    const image = (value: Expr): ImageSet => new ImageSet(signature, value, Integers, ...indices.slice(1).map(() => Integers));
    return options ? image(Tuple(...coordinates)) : [coordinates.map(image)];
  }
  let rows: Expr[][];
  try {
    rows = solveSystem(equations, symbols);
  } catch (error) {
    if (!options || !(error instanceof NotImplementedError)) throw error;
    if (symbols.length === 2 && replacements.length === 0 && equations.length === 2) {
      const reduced = conditionalFamilies(equations.map(asEquation), symbols);
      if (reduced) return reduced;
    }
    const condition = and(...system.map((e) => {
      const residual = asEquation(e);
      const [numerator, denominator] = asNumerDenom(residual);
      return Eq(denominator instanceof Rational ? numerator : residual, 0);
    }));
    return new ConditionSet(Tuple(...targets), condition, productSet(...targets.map(() => Complexes)));
  }
  const restored = rows.map((row) => row.map((v) => xreplace(v, back)));
  return options ? FiniteSet.of(...restored.map((row) => Tuple(...row))) : restored;
}

/** Parameterize one equation and impose the remaining equation on its free coordinate. */
function conditionalFamilies(system: readonly Expr[], symbols: readonly Sym[]): SetExpr | undefined {
  for (const [i, equation] of system.entries()) {
    const other = at(system, 1 - i);
    const product = factorTerms(equation);
    if (product instanceof Mul) {
      const families: SetExpr[] = [];
      for (const factor of product.args.filter((f) => !(f instanceof Pow && f.base.equals(S.E)) && isNonzero(f) !== true)) {
        let family: SetExpr | undefined;
        for (const [j, pivot] of symbols.entries()) {
          const coefficients = polyCoefficients(factor, pivot);
          if (!coefficients || [...coefficients.keys()].some((d) => d > 1)) continue;
          const slope = coefficients.get(1);
          if (!slope || isNonzero(slope) !== true) continue;
          const value = mul((coefficients.get(0) ?? S.Zero).neg(), pow(slope, -1));
          const free = at(symbols, 1 - j);
          const residual = subs(other, [[pivot, value]]);
          const domain = ConditionSet.of(free, Eq(residual, 0), Complexes);
          family = imageSet(free, Tuple(...symbols.map((s) => s === pivot ? value : free)), domain);
          break;
        }
        if (!family) { families.length = 0; break; }
        families.push(family);
      }
      if (families.length) return union(...families);
    }
    if (!(equation instanceof Add)) continue;
    for (const term of equation.args) {
      if (!(term instanceof Pow) || !(term.base instanceof Rational) || !term.base.isInteger || term.base.p <= 1n) continue;
      const j = symbols.findIndex((s) => s.equals(term.exp));
      if (j < 0) continue;
      const pivot = at(symbols, j), free = at(symbols, 1 - j);
      const value = add(...equation.args.filter((t) => t !== term)).neg();
      if (value.has(pivot)) continue;
      const base = term.base;
      const residual = mapBottomUp(other, (node) => {
        if (!(node instanceof Pow) || !node.exp.equals(pivot) || !(node.base instanceof Rational) || !node.base.isInteger || !node.base.isPositive) return node;
        const [degree, exact] = integerLog(node.base.p, base.p);
        return exact ? pow(value, degree) : node;
      });
      if (residual.has(pivot)) continue;
      const domain = ConditionSet.of(free, and(Ne(value, 0), Eq(residual, 0)), Complexes);
      const k = new Dummy('k', { integer: true });
      const root = mul(add(log(value), mul(2, S.I, S.Pi, k)), pow(log(base), -1));
      return new ImageSet(Tuple(k, free), Tuple(...symbols.map((s) => s === pivot ? root : free)), Integers, domain);
    }
  }
  return undefined;
}

/** Take logarithms of two nonzero exponential monomials, retaining every period of exp. */
function exponentialSystem(system: readonly Expr[], symbols: readonly Sym[]): [Sym[], Expr[]] | undefined {
  if (symbols.length < 2 || system.length !== symbols.length) return undefined;
  const indices: Sym[] = [], linear: Expr[] = [];
  for (const equation of system.map(asEquation)) {
    if (!(equation instanceof Add) || equation.args.length !== 2) return undefined;
    const logarithms: Expr[] = [];
    const signs: boolean[] = [];
    for (const term of equation.args) {
      const factors = term instanceof Mul ? term.args : [term];
      const coefficient = mul(...factors.filter((f) => f instanceof Rational));
      const powers = factors.filter((f) => !(f instanceof Rational));
      if (!powers.length || !powers.every((f): f is Pow => f instanceof Pow && isPositive(f.base) === true && !f.base.freeSymbols().size)) return undefined;
      const scalar = isNegative(coefficient) === true ? coefficient.neg() : coefficient;
      signs.push(!scalar.equals(coefficient));
      logarithms.push(add(expand_log(log(scalar)), ...powers.map((f) => mul(f.exp, expand_log(log(f.base))))));
    }
    const k = new Dummy('k' + indices.length, { integer: true });
    indices.push(k);
    const turns = signs[0] === signs[1] ? add(k, S.Half) : k;
    linear.push(add(at(logarithms, 0), at(logarithms, 1).neg(), mul(-2, S.Pi, S.I, turns)));
  }
  const matrix = linearEqToMatrix(linear, symbols);
  const values = matrix && solveAugmented(matrix[0].hstack(matrix[1]), symbols);
  return values && !values.some((v) => symbols.some((s) => v.has(s))) ? [indices, values] : undefined;
}

/** Expand Cardano's conjugate cube roots in polar form during substitution. */
function cubicSubstitutionRoots(values: FiniteSet, equation: Expr, pivot: Sym): Expr[] | undefined {
  if (values.args.length !== 3 || !values.args.every((v) => v instanceof CRootOf && v.isRealRoot)) return undefined;
  const coefficients = polyCoefficients(equation, pivot);
  if (!coefficients || Math.max(...coefficients.keys()) !== 3) return undefined;
  const coefficient = (degree: number) => coefficients.get(degree) ?? S.Zero;
  return rootsCubicFormula(coefficient(3), coefficient(2), coefficient(1), coefficient(0)).map((root) =>
    expand(mapBottomUp(root, (term) => {
      if (!(term instanceof Pow && term.exp instanceof Rational && term.exp.q === 3n)) return term;
      const [re, im] = asRealImag(term.base);
      const theta = mul(term.exp, fn('atan2', [im, re]));
      const radius = pow(add(pow(re, 2), pow(im, 2)), mul(term.exp, S.Half));
      return mul(radius, add(fn('cos', [theta]), mul(S.I, fn('sin', [theta]))));
    })));
}

function solveSystem(system: readonly ExprLike[], symbols: readonly Sym[]): Expr[][] {
  const eqs = system.map(asEquation);
  if (eqs.length === 0) return [];
  if (symbols.length === 0) {
    if (eqs.some((e) => e.freeSymbols().size > 0)) throw new RangeError('nonlinsolve: at least one unknown is required');
    return eqs.some((e) => !e.equals(S.Zero)) ? [] : [[]];
  }
  if (eqs.length === 1 && symbols.length > 1) {
    const families = quadraticFamilies(at(eqs, 0), symbols);
    if (families) return families;
  }
  if (symbols.length === 2 && eqs.length === 2) {
    const periodic = periodicProduct(eqs, symbols);
    if (periodic) return periodic;
    const one = eqs.findIndex((e) => symbols.filter((v) => e.has(v)).length === 1);
    if (one >= 0) {
      const equation = at(eqs, one);
      const v = defined(symbols.find((s) => equation.has(s)));
      const w = defined(symbols.find((s) => s !== v));
      const branches = quadraticFamilies(equation, [v]);
      const values = branches ? FiniteSet.of(...branches.map((row) => at(row, 0))) : solveset(equation, v);
      if (values.equals(EmptySet)) return [];
      const other = at(eqs, 1 - one);
      const tuple = (a: Expr, b: Expr): Expr[] => symbols.map((s) => s === v ? a : b);
      if (values instanceof ImageSet) {
        const real = solveset(equation, v, Reals);
        const roots = (e: Expr): readonly Expr[] => {
          const r = solveset(e, w);
          if (r instanceof FiniteSet) return r.args;
          if (r.equals(EmptySet)) return [];
          throw new NotImplementedError('nonlinsolve: an independent infinite or unresolved solution component requires another parameter');
        };
        const out: Expr[][] = [];
        if (real instanceof FiniteSet) {
          for (const a of real.args) for (const b of roots(subs(other, [[v, a]]))) out.push(tuple(a, b));
        }
        for (const b of roots(subs(other, [[v, values.expr]]))) {
          out.push(tuple(values, imageSet(values.variable, b, values.base)));
        }
        return out;
      }
      if (values instanceof FiniteSet) {
        const out: Expr[][] = [];
        let complete = true;
        const explicit = cubicSubstitutionRoots(values, equation, v);
        for (const a of explicit ?? values.args) {
          const residual = subs(other, [[v, a]]);
          const families = quadraticFamilies(residual, [w]);
          const rest = families ? FiniteSet.of(...families.map((row) => at(row, 0))) : solveset(residual, w);
          if (rest instanceof FiniteSet) {
            // Substitution combines the real and complex passes by structural equality.
            const real = explicit ? solveset(residual, w, Reals) : EmptySet;
            const roots = real instanceof FiniteSet ? FiniteSet.of(...rest.args, ...real.args).args : rest.args;
            for (const b of roots) out.push(tuple(a, b));
          }
          else if (rest instanceof ImageSet) out.push(tuple(a, rest));
          else if (!rest.equals(EmptySet)) complete = false;
        }
        if (out.some((t) => t.some((c) => c instanceof ImageSet))) {
          if (!complete) throw new NotImplementedError('nonlinsolve: some solution components remain unresolved');
          return out;
        }
        if (complete) return out;
      }
    }
  }
  try {
    // Solve over the complex domain even when an unknown has a real assumption.
    // Positive-dimensional polynomial elimination orders generators lexicographically.
    const ordered = [...symbols].sort((a, b) => compareKeys(sortKey(a), sortKey(b)));
    const generators = !ordered.every((s, i) => s === symbols[i]) && linearEqToMatrix(eqs, symbols) ? ordered : symbols;
    const solutions = finiteNonlinsolve(eqs, generators, { checkAssumptions: false })
      .map((row) => symbols.map((s) => at(row, generators.indexOf(s))));
    // A single equation describes a family through its parameter domain.
    // Elimination in a system represents dependent coordinates directly.
    return eqs.length === 1 ? excludeFinitePoles(eqs, symbols, solutions) : solutions.filter(isFiniteTuple);
  } catch (error) {
    if (!(error instanceof NotImplementedError)) throw error;
    return substituteFinite(eqs, symbols);
  }
}

/** Solve each zero factor over a period shared with the other equation. */
function periodicProduct(equations: readonly Expr[], symbols: readonly Sym[]): Expr[][] | undefined {
  const product = equations.find((e) => e instanceof Mul && e.args.every((a) => a instanceof Fn && (a.name === 'sin' || a.name === 'cos')));
  if (!product) return undefined;
  const other = at(equations, 1 - equations.indexOf(product));
  const rows = new Map<string, Expr[]>();
  for (const factor of product.args) {
    const index = symbols.findIndex((s) => factor.has(s));
    if (index < 0 || factor.has(at(symbols, 1 - index))) return undefined;
    const pivot = at(symbols, index), free = at(symbols, 1 - index);
    const period = periodicity(other, pivot);
    if (!period || period.equals(S.Zero)) return undefined;
    const roots = solveset(factor, pivot);
    const parts = roots instanceof SetOp && roots.op === 'Union' ? roots.args : [roots];
    for (const family of parts) {
      if (!(family instanceof ImageSet) || !(family.variable instanceof Sym)) return undefined;
      const step = linearCoeffs(family.expr, family.variable);
      const turns = cancel(mul(at(step, 0), pow(period, -1)));
      if (!(turns instanceof Rational && turns.isInteger)) return undefined;
      const values = solveset(subs(other, [[pivot, at(step, 1)]]), free);
      const components = values instanceof SetOp && values.op === 'Union' ? values.args : [values];
      for (const component of components) {
        if (!(component instanceof ImageSet)) return undefined;
        const row = index === 0 ? [family, component] : [component, family];
        rows.set(JSON.stringify(row.map((v) => v.asDummy().key)), row);
      }
    }
  }
  return [...rows.values()];
}

/** Invert a separated quadratic factor over both solver domains. */
function quadraticFamilies(equation: Expr, symbols: readonly Sym[]): Expr[][] | undefined {
  if (!some(equation, (e) => e instanceof Pow && e.exp.equals(S.Two) && symbols.some((s) => s.equals(e.base)))) return undefined;
  const product = factorTerms(equation);
  const factors = product instanceof Mul ? product.args : [product];
  const rows: Expr[][] = [];
  let quadratic = false;
  for (const factor of factors) {
    const variables = symbols.filter((s) => factor.has(s)).sort((a, b) => a.name.localeCompare(b.name));
    if (!variables.length) {
      if (isNonzero(factor) === true) continue;
      return undefined;
    }
    let roots: readonly Expr[] | undefined;
    let pivot = at(variables, 0);
    for (const v of variables) {
      const poly = polyCoefficients(factor, v);
      const leading = poly?.get(2), constant = poly?.get(0);
      if (poly?.size !== 2 || !leading || !constant || isNonzero(leading) !== true || !constant.freeSymbols().size) continue;
      const algebraic = solve(factor, v, { check: false });
      const root = pow(mul(constant.neg(), pow(leading, -1)), S.Half);
      roots = [...algebraic, root, root.neg()];
      pivot = v;
      quadratic = true;
      break;
    }
    if (!roots) {
      if (variables.length !== 1) return undefined;
      const solutions = solveset(factor, pivot);
      if (!(solutions instanceof FiniteSet)) return undefined;
      roots = solutions.args;
    }
    for (const value of roots) rows.push(symbols.map((s) => s === pivot ? value : s));
  }
  return quadratic ? excludeFinitePoles([equation], symbols, rows) : undefined;
}

function isFiniteTuple(values: readonly Expr[]): boolean {
  return !values.some((value) => some(value, (term) => term instanceof Special));
}

/** Eliminate one unknown at a time using the finite branches of solveset. */
function substituteFinite(system: readonly Expr[], symbols: readonly Sym[]): Expr[][] {
  const solveRemaining = (equations: readonly Expr[], remaining: readonly Sym[], values: readonly Expr[]): Expr[][] => {
    const pending = equations.filter((e) => !e.equals(S.Zero));
    if (!pending.length) return [[...values]];
    const withUnknowns = pending.map((e) => ({ e, vars: remaining.filter((s) => e.has(s)) }));
    if (withUnknowns.some(({ vars }) => !vars.length)) return [];
    withUnknowns.sort((a, b) => a.vars.length - b.vars.length);
    for (const { e, vars } of withUnknowns) {
      for (const symbol of vars) {
        const complex = solveset(e, symbol, Complexes);
        if (complex === EmptySet) return [];
        if (!(complex instanceof FiniteSet)) continue;
        const real = solveset(e, symbol, Reals);
        const candidates = new Map([...complex.args, ...(real instanceof FiniteSet ? real.args : [])].map((r) => [r.key, r]));
        return [...candidates.values()].flatMap((root) => {
          const replacement = [[symbol, root]] as const;
          const next = pending.filter((f) => f !== e).map((f) => cancel(xreplace(f, replacement)));
          return solveRemaining(next, remaining.filter((s) => !s.equals(symbol)), values.map((v) => xreplace(v, replacement)));
        });
      }
    }
    throw new NotImplementedError('nonlinsolve: nonlinear substitution has an unresolved solution set');
  };
  return excludeFinitePoles(system, symbols, solveRemaining(system, symbols, symbols));
}

function excludeFinitePoles(system: readonly Expr[], symbols: readonly Sym[], solutions: readonly Expr[][]): Expr[][] {
  const exclusions = system.flatMap((e) => [...denoms(e, ...symbols)]);
  const withExclusions = solutions.filter(isFiniteTuple).map((values) => {
    const mapping = symbols.map((s, i): [Expr, Expr] => [s, at(values, i)]);
    const forbidden = [...exclusions, ...values.flatMap((v) => [...denoms(v, ...symbols)])].map((d) => cancel(xreplace(d, mapping)));
    return { values, forbidden };
  });
  const admissible = withExclusions.filter(({ forbidden }) => !forbidden.some((d) => d.equals(S.Zero)));
  const accepted = new Map<string, Expr[]>();
  for (const { values, forbidden } of admissible) {
    const row = values.map((v) => {
      if (!(v instanceof Sym) || !symbols.some((s) => s.equals(v))) return v;
      const excluded = forbidden.filter((d) => d.has(v) && symbols.every((s) => s.equals(v) || !d.has(s))).map((d) => solveset(d, v));
      return excluded.some((set) => set !== EmptySet) ? complement(FiniteSet.of(v), union(...excluded)) : v;
    });
    accepted.set(JSON.stringify(row.map((v) => v.key)), row);
  }
  return [...accepted.values()];
}

/** SymPy substitution: extend known assignments by solving the remaining system. */
export function substitution(
  system: readonly ExprLike[],
  symbols: readonly Sym[],
  result: readonly ReadonlyMap<Sym, ExprLike>[] = [new Map()],
  _knownSymbols: readonly Sym[] = [],
  exclude: readonly ExprLike[] = [],
  allSymbols: readonly Sym[] = symbols,
): Expr[][] {
  if (system.length && !symbols.length && !result.some((known) => known.size)) throw new RangeError('substitution: at least one unknown is required');
  const out: Expr[][] = [];
  for (const known of result) {
    const entries = [...known].map(([k, v]): [Expr, Expr] => [k, sympify(v)]);
    const pending = system.map((e) => expand(subs(asEquation(e), entries))).filter((e) => !e.equals(S.Zero));
    const free = symbols.filter((v) => !entries.some(([k]) => k.equals(v)));
    if (system.length === 0) continue;
    const solutions = pending.length ? free.length ? nonlinsolve(pending, free) : [] : [free];
    for (const solution of solutions) {
      const assignments: [Expr, Expr][] = [...entries, ...free.map((v, i): [Expr, Expr] => [v, at(solution, i)])];
      if (exclude.some((e) => expand(subs(sympify(e), assignments)).equals(S.Zero))) continue;
      out.push(allSymbols.map((v) => {
        const value = assignments.find(([k]) => k.equals(v))?.[1] ?? v;
        const poles = system.flatMap((equation) => [...denoms(asEquation(equation), v)])
          .filter((d) => d.freeSymbols().size === 1 && d.has(v));
        return poles.length ? complement(FiniteSet.of(value), union(...poles.map((d) => solveset(d, v)))) : value;
      }));
    }
  }
  return out;
}
