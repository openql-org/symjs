// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// trigsimp, futrig, trigsimp_groebner, trigsimp_old and exptrigsimp are ported from
// SymPy 1.14 sympy/simplify/trigsimp.py (BSD 3-Clause, Copyright (c) SymPy Development Team).

/**
 * @file Trigonometric simplification (SymPy trigsimp.py): `trigsimp` with
 * the methods 'matching' (futrig, the default), 'groebner', 'combined',
 * 'fu' and 'old', and `exptrigsimp`. The exponential-form helpers at the
 * end (rewriteExp, rewriteTrig, expsimp, exptotrig, combineExp) are used
 * by simplify and integrate.
 */

import type { Expr, ExprLike, FnName } from '../core/nodes';
import { Add, Constant, Derivative, Dummy, Fn, Mul, Piecewise, Pow, Rational, S, Sym, Wild } from '../core/nodes';
import { add, couldExtractMinusSign, exp, mul, neg, pow, sub, sympify } from '../core/ops';
import { mapBottomUp, rebuild, some, subs, xreplace } from '../core/traverse';
import { countOps, match, ordered } from '../core/match';
import { argsCncSplit, asCoeffMul as asCoeffMulDeps, asIndependent, asNumerDenom, asPowersDict } from '../core/methods';
import { ExprMap } from '../core/exprmap';
import { isIntegerQ } from '../core/assumptions';
import { cos, fn, sin } from '../functions/elementary';
import { gcd as igcd } from '../core/numbers';
import { factor } from '../polys/sympoly';
import { groebner, reduced, type MonomialOrder } from '../polys/groebner';
import { expand, expandMul } from './expand';
import { rewrite } from './rewrite';
import { cancel } from './rational';
import { factorTerms } from './exprtools';
import { separatevars } from './separatevars';
import {
  TR1, TR10, TR10i, TR11, TR11Half, TR111, TR12, TR14, TR15, TR16, TR2, TR22, TR2i, TR3, TR5, TR6, TR8, TRmorrie,
  bottomUp, chain, choice, expandMulOnly, fu, greedy, hasF, hasHyperFunction, hasTrigFunction, hyperAsTrig, identity,
  isF, isHyperFunction, isTrigFunction, mexpand, nodeCount, normal, positive,
} from './fu';
import type { Measured, Rule } from './fu';
import { at, defined, first, getOrThrow } from '../core/guard';

const isE = (e: Expr): boolean => e instanceof Constant && e.name === 'E';
const isI = (e: Expr): boolean => e instanceof Constant && e.name === 'I';
const eq = (a: Expr, b: Expr): boolean => a.key === b.key;
const isZero = (e: Expr): boolean => e instanceof Rational && e.isZero;
/** SymPy is_Pow (exp(x) is not a Pow in SymPy). */
const isPowNode = (e: Expr): e is Pow => e instanceof Pow && !isE(e.base);
const isExpNode = (e: Expr): e is Pow => e instanceof Pow && isE(e.base);
/** SymPy e.has(TrigonometricFunction, HyperbolicFunction). */
const hasTrigs = (e: Expr): boolean => some(e, (x) => isTrigFunction(x) || isHyperFunction(x));
const isBooleanLike = (e: Expr): boolean => e.kind === 'Rel' || e.kind === 'Bool' || e.kind === 'BoolOp';

/**
 * @internal The ratsimpmodprime of the groebner method, registered by the
 * simplify entry point (a direct import would make an import cycle through
 * the linear solver).
 */
export const trigsimpHooks: { ratsimpmodprime?: (e: Expr, G: readonly Expr[], gens: readonly Sym[], opts: { order?: MonomialOrder; quick?: boolean }) => Expr } = {};

/** Options of trigsimp. */
export interface TrigsimpOptions {
  /** 'matching' (futrig, the default), 'groebner', 'combined', 'fu' or 'old'. */
  method?: 'matching' | 'groebner' | 'combined' | 'fu' | 'old';
  /** SymPy's old algorithm (trigsimp_old), with its options deep, recursive and method. */
  old?: boolean;
  /** Old algorithm: simplify inside the arguments of functions too. */
  deep?: boolean;
  /** Old algorithm: SymPy simplifies common subexpressions first (not implemented: ignored). */
  recursive?: boolean;
  /** Simplify inverse functions of trigonometric functions of the same argument (asin(sin(x)) -> x). */
  inverse?: boolean;
  /** Groebner method: hints (an integer n, function names, [function name, args...] or extra generators). */
  hints?: readonly (number | FnName | Expr | readonly [FnName, ...Expr[]])[];
  /** Groebner method: the monomial order (default 'grlex'). */
  order?: MonomialOrder;
  /** Groebner method: stop at the first good result (default false). */
  quick?: boolean;
  /** Groebner method: only reduce numerator and denominator (default false). */
  polynomial?: boolean;
  /** Fu method: the objective to minimize (default the number of trigonometric functions, then count_ops). */
  measure?: (e: Expr) => Measured;
}

// ---------------------------------------------------------------------------
// trigsimp
// ---------------------------------------------------------------------------

/**
 * Simplify expressions containing trigonometric (and hyperbolic) functions
 * (SymPy trigsimp). The default method 'matching' is SymPy's futrig: Fu's
 * transformation rules applied greedily, minimizing the number of
 * trigonometric functions, then count_ops.
 */
export function trigsimp(ex: ExprLike, opts: TrigsimpOptions = {}): Expr {
  const expr = sympify(ex);
  // (SymPy Relational._eval_trigsimp: both sides)
  if (expr.kind === 'Rel') return rebuild(expr, expr.args.map((a) => trigsimp(a, opts)));
  const method = opts.old ? 'old' : (opts.method ?? 'matching');
  let r: Expr;
  switch (method) {
    case 'fu':
      r = fu(expr, opts.measure ? { measure: opts.measure } : {});
      break;
    case 'groebner':
      r = groebnersimp(expr, true, opts);
      break;
    case 'combined':
      r = futrig(groebnersimp(expr, true, { ...opts, polynomial: true, hints: [2, 'tan'] }));
      break;
    case 'old':
      r = trigsimpOld(expr, opts);
      break;
    default:
      r = futrig(expr);
  }
  return opts.inverse ? trigsimpInverse(r) : r;
}

/** trigsimp_groebner applied to the arguments of functions and powers (when deep), then to the whole. */
function groebnersimp(ex: Expr, deep: boolean, opts: TrigsimpOptions): Expr {
  const traverse = (e: Expr): Expr => {
    if (e.args.length === 0) return e;
    let args = e.args.map(traverse);
    if (e instanceof Fn || e instanceof Pow) args = args.map((x) => trigsimpGroebner(x, opts));
    return rebuild(e, args);
  };
  // (relations are simplified side by side by trigsimp)
  return trigsimpGroebner(deep ? traverse(ex) : ex, opts);
}

/** @internal SymPy _trigsimp_inverse: f^-1(f(x)) -> x for the trigonometric functions, and atan2(sin(x), cos(x)) -> x. */
export function trigsimpInverse(rv: Expr): Expr {
  const INV: Partial<Record<FnName, FnName>> = { asin: 'sin', acos: 'cos', atan: 'tan', acot: 'cot', asec: 'sec', acsc: 'csc' };
  const f = (e: Expr): Expr => {
    if (e instanceof Fn) {
      const g = INV[e.name];
      if (g !== undefined && isF(first(e.args), g)) return first(first(e.args).args);
      if (e.name === 'atan2') {
        const [y, x] = [at(e.args, 0), at(e.args, 1)];
        if (couldExtractMinusSignCoeff(y)) return neg(f(fn('atan2', [neg(y), x])));
        if (couldExtractMinusSignCoeff(x)) return sub(S.Pi, f(fn('atan2', [y, neg(x)])));
        if (y instanceof Fn && x instanceof Fn && y.args.length > 0 && eq(first(x.args), first(y.args))) {
          if (y.name === 'sin' && x.name === 'cos') return first(x.args);
          if (y.name === 'cos' && x.name === 'sin') return sub(mul(S.Pi, S.Half), first(x.args));
        }
      }
    }
    return e;
  };
  return bottomUp(rv, f);
}

/** SymPy _coeff_isneg: a negative numeric coefficient. */
function couldExtractMinusSignCoeff(e: Expr): boolean {
  const c = e instanceof Mul ? first(e.args) : e;
  return c instanceof Rational ? c.isNegative : c.kind === 'Float' && c.toNumber() < 0;
}

// ---------------------------------------------------------------------------
// futrig
// ---------------------------------------------------------------------------

/**
 * SymPy futrig: Fu's rules applied bottom-up to every subexpression; with
 * hyper (the default), hyperbolic functions are simplified through their
 * trigonometric forms (Osborne's rule).
 */
export function futrig(eIn: ExprLike, opts: { hyper?: boolean } = {}): Expr {
  const old = sympify(eIn);
  if (old.args.length === 0) return old;
  let e = bottomUp(old, futrigNode);
  if ((opts.hyper ?? true) && hasHyperFunction(e)) {
    const [t, back] = hyperAsTrig(e);
    e = back(bottomUp(t, futrigNode));
  }
  if (!eq(e, old) && e instanceof Mul && first(e.args) instanceof Rational) {
    const [c, r] = [first(e.args), mul(...e.args.slice(1))];
    e = mul(c, r);
  }
  return e;
}

/** SymPy _is_Expr: an Expr whose arguments are all Exprs (Piecewise and relations are not). */
function isExprTree(e: Expr): boolean {
  if (e instanceof Derivative) return isExprTree(first(e.args));
  if (isBooleanLike(e) || e instanceof Piecewise) return false;
  return e.args.every(isExprTree);
}

/** SymPy _eapply: func applied to e, or to the arguments of a non-Expr that satisfy cond. */
function eapply(func: Rule, e: Expr, cond?: (x: Expr) => boolean): Expr {
  if (isBooleanLike(e) || e instanceof Piecewise) return e;
  // (an atom is an Expr tree)
  if (isExprTree(e)) return func(e);
  return rebuild(e, e.args.map((ei) => (cond === undefined || cond(ei) ? eapply(func, ei) : ei)));
}

const trigs = (x: Expr): boolean => hasTrigFunction(x);
const ea = (func: Rule): Rule => (x) => eapply(func, x, trigs);
const factorRule: Rule = (x) => factor(x);
const lops = (x: Expr): Measured => [
  countIf(x, isTrigFunction),
  countOps(x),
  nodeCount(x),
  x.args.length,
  x instanceof Add ? 1 : 0,
];

function countIf(e: Expr, pred: (x: Expr) => boolean): number {
  let n = 0;
  some(e, (x) => {
    if (pred(x)) n++;
    return false;
  });
  return n;
}

const FUTRIG_TREE = choice(
  identity,
  chain(
    (x) => TR3(x),
    (x) => TR1(x),
    (x) => TR12(x),
    ea(factorRule),
    (x) => TR2(x),
    choice(identity, ea(mexpand)),
    (x) => TR2i(x),
    ea((i) => factor(normal(i))),
    (x) => TR14(x),
    (x) => TR5(x),
    (x) => TR10(x),
    (x) => TR11(x),
    (x) => TR11Half(x),
    (x) => TR6(x),
    ea(factorRule),
    (x) => TR14(x),
    choice(identity, ea(mexpand)),
    (x) => TR10i(x),
    (x) => TRmorrie(x),
    choice(identity, (x) => TR8(x)),
    choice(identity, (x) => TR2i(TR2(x))),
    choice((x) => eapply(expandMulOnly, TR5(x), trigs), (x) => eapply(expandMulOnly, TR15(x), trigs)),
    choice((x) => eapply(expandMulOnly, TR6(x), trigs), (x) => eapply(expandMulOnly, TR16(x), trigs)),
    (x) => TR111(x),
    choice(identity, (x) => TR2i(x)),
    choice(identity, (x) => eapply(expandMulOnly, TR22(x), trigs)),
    (x) => TR1(x),
    (x) => TR2(x),
    (x) => TR2i(x),
    choice(identity, (x) => eapply((y) => factorTerms(y), TR12(x), trigs)),
  ),
);
const futrigRule = greedy(FUTRIG_TREE, lops);

/** SymPy _futrig: the rule tree applied to one node (its trigonometric-free factors split off). */
function futrigNode(e0: Expr): Expr {
  if (!hasTrigFunction(e0)) return e0;
  let coeff: Expr | undefined;
  let e = e0;
  if (e0 instanceof Mul) [coeff, e] = independentOfTrig(e0);
  const r = futrigRule(e);
  return coeff === undefined ? r : mul(coeff, r);
}

/** SymPy as_independent(TrigonometricFunction) of a product. */
function independentOfTrig(e: Mul): [Expr, Expr] {
  const [c, nc] = argsCncSplit(e, false);
  const depend = c.filter(hasTrigFunction);
  const indep = c.filter((a) => !hasTrigFunction(a));
  const i = nc.findIndex(hasTrigFunction);
  if (i >= 0) depend.push(...nc.slice(i));
  indep.push(...nc.slice(0, i >= 0 ? i : nc.length));
  return [mul(...indep), mul(...depend)];
}

// ---------------------------------------------------------------------------
// trigsimp_groebner
// ---------------------------------------------------------------------------

const TRIG_GENS: ReadonlySet<string> = new Set(['sin', 'cos', 'tan', 'sinh', 'cosh', 'tanh']);
type Fam = { c: FnName; s: FnName; t: FnName };
const FAMS: readonly Fam[] = [
  { c: 'cos', s: 'sin', t: 'tan' },
  { c: 'cosh', s: 'sinh', t: 'tanh' },
];
const F = (name: FnName, a: ExprLike): Expr => fn(name, [a]);

/**
 * SymPy trigsimp_groebner: simplification modulo the ideal of the
 * trigonometric relations (sin**2 + cos**2 = 1, tan*cos = sin, the
 * multiple-angle formulas) with ratsimpmodprime.
 */
export function trigsimpGroebner(exprIn: ExprLike, opts: TrigsimpOptions = {}): Expr {
  const order = opts.order ?? 'grlex';
  const quick = opts.quick ?? false;
  const polynomial = opts.polynomial ?? false;
  const myI = new Dummy('I');
  const expr = xreplace(sympify(exprIn), [[S.I, myI]]);
  const back = (e: Expr): Expr => xreplace(e, [[myI, S.I]]);
  const [num, denom] = asNumerDenom(cancel(expr));
  const gens0 = polyGens([num, denom]);
  // hints
  let n = 1;
  const funcs: FnName[] = [];
  const iterables: [FnName, Expr[]][] = [];
  const extra: Expr[] = [];
  for (const h of opts.hints ?? []) {
    if (typeof h === 'number') n = h;
    else if (typeof h === 'string') funcs.push(h);
    else if (isHintTuple(h)) {
      const [f0, ...args] = h;
      iterables.push([f0, args]);
      extra.push(...polyGens([...args.map((x) => F(f0, x)), F(f0, add(...args))]));
    } else extra.push(h);
  }
  const gens = uniq([...gens0, ...extra]);
  const trigterms = gens.filter((g): g is Fn => g instanceof Fn && TRIG_GENS.has(g.name));
  const freegens = gens.filter((g) => !(g instanceof Fn && TRIG_GENS.has(g.name)));
  const newgens: Expr[] = [];
  const ideal: Expr[] = [];
  const trigdict = new Map<string, [Expr, [Expr, FnName][]]>();
  for (const g of trigterms) {
    const [coeff, vars] = asCoeffMulDeps(first(g.args));
    const v = mul(...vars);
    const cur = trigdict.get(v.key);
    if (cur) cur[1].push([coeff, g.name]);
    else trigdict.set(v.key, [v, [[coeff, g.name]]]);
  }
  for (const [key, val] of trigdict.values()) {
    const fns = val.map((x) => x[1]);
    const coeffs = val.map((x) => x[0]);
    const gcd = coeffs.slice(1).reduce<Expr>((a, b) => Rational.of(igcd(asInt(a), asInt(b))), first(coeffs));
    const terms: [FnName, Expr][] = fns.map((f, i) => [f, mul(at(coeffs, i), pow(gcd, -1))]);
    const fs = new Set<FnName>([...funcs, ...fns]);
    for (const fam of FAMS) {
      if (fs.has(fam.c) || fs.has(fam.s) || fs.has(fam.t)) {
        fs.add(fam.c);
        fs.add(fam.s);
      }
    }
    for (const f of fs) for (let k = 1; k <= n; k++) terms.push([f, Rational.of(k)]);
    const more: [FnName, Expr][] = [];
    for (const [f, v] of terms) {
      if (f === 'tan') more.push(['sin', v], ['cos', v]);
      if ((f === 'sin' || f === 'cos') && fs.has('tan')) more.push(['tan', v]);
      if (f === 'tanh') more.push(['sinh', v], ['cosh', v]);
      if ((f === 'sinh' || f === 'cosh') && fs.has('tanh')) more.push(['tanh', v]);
    }
    terms.push(...more);
    const x = mul(gcd, key);
    ideal.push(...buildIdeal(x, terms));
    newgens.push(...terms.map(([f, v]) => F(f, mul(v, x))));
  }
  for (let i = 0; i < iterables.length; i++) {
    const [f, args] = at(iterables, i);
    if (f === 'tan') iterables.push(['sin', args], ['cos', args]);
    else if (f === 'tanh') iterables.push(['sinh', args], ['cosh', args]);
    else {
      const dummys = args.map(() => new Dummy('d'));
      const ex = xreplace(expand(F(f, add(...dummys)), { trig: true }), dummys.map((d, j) => [d, at(args, j)] as const));
      ideal.push(sub(F(f, add(...args)), ex));
    }
  }
  const allGens = uniq(newgens);
  let free = freegens;
  if (gens.some((g) => eq(g, myI))) {
    ideal.push(add(pow(myI, 2), 1));
    free = free.filter((g) => !eq(g, myI));
    allGens.push(myI);
  }
  const tgens = ordered(uniqExprs(allGens));
  if (tgens.length === 0) return expr;
  const idealU = uniqExprs(ideal);
  // generators as symbols
  const allPoly = [...free, ...tgens];
  const syms = allPoly.map((g): Sym => (g instanceof Sym ? g : new Dummy('g')));
  const toSym = allPoly.map((g, i) => [g, at(syms, i)] as const).filter(([g, s]) => !eq(g, s));
  const fromSym = toSym.map(([g, s]) => [s, g] as const);
  const symOf = (e: Expr): Expr => xreplace(e, toSym);
  const exprOf = (e: Expr): Expr => back(xreplace(e, fromSym));
  const tsyms = syms.slice(free.length);
  const fsyms = syms.slice(0, free.length);
  const G = groebner(idealU.map(symOf), tsyms, order).exprs;
  const rsimp = (e: Expr, G0: readonly Expr[], gs: readonly Sym[]): Expr => {
    if (polynomial) {
      const [nu, de] = asNumerDenom(cancel(e));
      return cancel(mul(reduced(nu, G0, gs, order)[1], pow(reduced(de, G0, gs, order)[1], -1)));
    }
    return defined(trigsimpHooks.ratsimpmodprime, "ratsimpmodprime (import '@symjs/symjs/simplify')")(e, G0, gs, { order, quick });
  };
  const sNum = symOf(num);
  const sDen = symOf(denom);
  const symsIn = (e: Expr): Set<string> => new Set([...e.freeSymbols()].map((s) => s.key));
  if (fsyms.length && [...symsIn(sDen)].every((k) => tsyms.some((t) => t.key === k))) {
    // the numerator as a polynomial in the free generators with coefficients in the trigonometric ones
    const res: Expr[] = [];
    for (const [monom, coeff] of termsIn(sNum, fsyms)) {
      const ours = new Set([...symsIn(coeff), ...symsIn(sDen)].filter((k) => tsyms.some((t) => t.key === k)));
      let changed = true;
      while (changed) {
        changed = false;
        for (const p of idealU.map(symOf)) {
          const pg = [...symsIn(p)];
          if (!pg.every((k) => ours.has(k)) && pg.some((k) => ours.has(k))) {
            changed = true;
            pg.forEach((k) => ours.add(k));
          }
        }
      }
      const realgens = tsyms.filter((t) => ours.has(t.key));
      const ourG = G.filter((g) => [...symsIn(g)].every((k) => ours.has(k)));
      res.push(mul(monom, rsimp(mul(coeff, pow(sDen, -1)), ourG, realgens)));
    }
    return exprOf(add(...res));
  }
  return exprOf(rsimp(symOf(expr), G, [...fsyms, ...tsyms]));
}

type Hint = NonNullable<TrigsimpOptions['hints']>[number];
const isHintTuple = (h: Hint): h is readonly [FnName, ...Expr[]] => Array.isArray(h);

function asInt(e: Expr): bigint {
  if (e instanceof Rational && e.q === 1n) return e.p;
  throw new TypeError('trigsimp_groebner: the coefficients of the arguments must be integers');
}

/** The ideal of the relations of the functions in terms (SymPy build_ideal). */
function buildIdeal(x: Expr, terms: readonly [FnName, Expr][]): Expr[] {
  const I: Expr[] = [];
  const y = new Dummy('y');
  for (const [f, coeff] of terms) {
    for (const fam of FAMS) {
      const rel = fam.c === 'cos' ? sub(add(pow(F('cos', x), 2), pow(F('sin', x), 2)), 1) : sub(sub(pow(F('cosh', x), 2), pow(F('sinh', x), 2)), 1);
      if (coeff instanceof Rational && coeff.isOne && (f === fam.c || f === fam.s)) I.push(rel);
      else if (f === fam.t) I.push(sub(mul(F(fam.t, mul(coeff, x)), F(fam.c, mul(coeff, x))), F(fam.s, mul(coeff, x))));
      else if (f === fam.c || f === fam.s) {
        const cn = xreplace(expand(F(f, mul(coeff, y)), { trig: true }), [[y, x]]);
        I.push(sub(F(f, mul(coeff, x)), cn));
      }
    }
  }
  return uniqExprs(I);
}

/** The generators of a polynomial view of exprs (SymPy parallel_poly_from_expr(...)[1].gens). */
function polyGens(exprs: readonly Expr[]): Expr[] {
  const out = new ExprMap<true>();
  const visit = (e: Expr): void => {
    if (e instanceof Rational || e.kind === 'Float') return;
    if (e instanceof Add || e instanceof Mul) {
      e.args.forEach(visit);
      return;
    }
    if (isPowNode(e) && e.exp instanceof Rational && e.exp.isInteger && e.exp.isPositive) {
      visit(e.base);
      return;
    }
    // (numerator and denominator have no negative powers: such a power is a generator, as in SymPy)
    out.set(e, true);
  };
  exprs.forEach(visit);
  return [...out.keys()];
}

/** The terms of e as a polynomial in gens: [monomial, coefficient]. */
function termsIn(e: Expr, gens: readonly Sym[]): [Expr, Expr][] {
  const out = new ExprMap<Expr>();
  for (const t of addTerms(expandMul(e))) {
    const [rest, dep] = asIndependent(t, gens);
    out.set(dep, add(out.get(dep) ?? S.Zero, rest));
  }
  return [...out];
}

const addTerms = (e: Expr): readonly Expr[] => (e instanceof Add ? e.args : [e]);
const uniq = (xs: readonly Expr[]): Expr[] => uniqExprs(xs);
function uniqExprs(xs: readonly Expr[]): Expr[] {
  const m = new ExprMap<true>();
  for (const x of xs) m.set(x, true);
  return [...m.keys()];
}

// ---------------------------------------------------------------------------
// trigsimp_old
// ---------------------------------------------------------------------------

function trigsimpOld(expr0: Expr, opts: TrigsimpOptions): Expr {
  let expr = expr0;
  if (!hasTrigs(expr)) return expr;
  const trigsyms = new ExprMap<true>();
  some(expr, (t) => {
    if (isTrigFunction(t) || isHyperFunction(t)) for (const s of t.freeSymbols()) trigsyms.set(s, true);
    return false;
  });
  if (trigsyms.size > 1) {
    const d = separatevars(expr);
    const dd = d instanceof Mul ? separatevars(d, { dict: true }) : undefined;
    // the pieces are simplified by trigsimp without old (SymPy passes the remaining options on)
    const inner = (v: Expr): Expr => trigsimp(v, { ...opts, old: false, method: opts.method === 'old' ? 'matching' : opts.method });
    if (dd instanceof Map) {
      let e: Expr = S.One;
      for (const v0 of dd.values()) {
        const v = expandMulOnly(v0);
        const vnew = inner(v);
        e = mul(e, eq(vnew, v) ? v0 : vnew);
      }
      expr = e;
    } else if (d instanceof Add) {
      for (const s of trigsyms.keys()) {
        const [r, e] = asIndependent(expr, [s]);
        if (!isZero(r)) {
          expr = add(r, inner(e));
          if (!(expr instanceof Add)) break;
        }
      }
    }
  }
  const deep = opts.deep ?? false;
  const method = opts.method === 'old' ? 'matching' : (opts.method ?? 'matching');
  switch (method) {
    case 'groebner':
      return groebnersimp(expr, deep, opts);
    case 'combined':
      return trigsimpMatch(groebnersimp(expr, deep, { ...opts, polynomial: true, hints: [2, 'tan'] }), deep);
    default:
      return trigsimpMatch(expr, deep);
  }
}

/** SymPy _dotrig: same head and both with trigonometric (or both with hyperbolic) functions. */
function dotrig(a: Expr, b: Expr): boolean {
  // (the patterns are sums and products, so the same kind is the same head)
  return a.kind === b.kind && ((hasTrigFunction(a) && hasTrigFunction(b)) || (hasHyperFunction(a) && hasHyperFunction(b)));
}

type Pats = {
  a: Wild;
  b: Wild;
  c: Wild;
  d: Wild;
  division: [Expr, Expr, Expr, Expr][];
  addm: [Expr, Expr][];
  identity: [Expr, Expr][];
  artifacts: [Expr, Expr, FnName][];
};
let PATS: Pats | undefined;

function trigpats(): Pats {
  if (PATS) return PATS;
  const a = new Wild('a');
  const b = new Wild('b');
  const c = new Wild('c');
  const d = new Wild('d', { commutative: false });
  const sn = (x: Expr): Expr => F('sin', x);
  const cs = (x: Expr): Expr => F('cos', x);
  const G = (name: FnName) => (x: Expr): Expr => F(name, x);
  const tn = G('tan');
  const ct = G('cot');
  const sh = G('sinh');
  const ch = G('cosh');
  const th = G('tanh');
  const cth = G('coth');
  const P = (x: Expr, y: ExprLike): Expr => pow(x, y);
  const inv = (x: Expr): Expr => pow(x, -1);
  const division: [Expr, Expr, Expr, Expr][] = [
    [mul(a, P(sn(b), c), inv(P(cs(b), c))), mul(a, P(tn(b), c)), sn(b), cs(b)],
    [mul(a, P(tn(b), c), P(cs(b), c)), mul(a, P(sn(b), c)), sn(b), cs(b)],
    [mul(a, P(ct(b), c), P(sn(b), c)), mul(a, P(cs(b), c)), sn(b), cs(b)],
    [mul(a, P(tn(b), c), inv(P(sn(b), c))), mul(a, inv(P(cs(b), c))), sn(b), cs(b)],
    [mul(a, P(ct(b), c), inv(P(cs(b), c))), mul(a, inv(P(sn(b), c))), sn(b), cs(b)],
    [mul(a, P(ct(b), c), P(tn(b), c)), a, sn(b), cs(b)],
    [mul(a, P(add(cs(b), 1), c), P(sub(cs(b), 1), c)), mul(a, P(neg(P(sn(b), 2)), c)), add(cs(b), 1), sub(cs(b), 1)],
    [mul(a, P(add(sn(b), 1), c), P(sub(sn(b), 1), c)), mul(a, P(neg(P(cs(b), 2)), c)), add(sn(b), 1), sub(sn(b), 1)],
    [mul(a, P(sh(b), c), inv(P(ch(b), c))), mul(a, P(th(b), c)), S.One, S.One],
    [mul(a, P(th(b), c), P(ch(b), c)), mul(a, P(sh(b), c)), S.One, S.One],
    [mul(a, P(cth(b), c), P(sh(b), c)), mul(a, P(ch(b), c)), S.One, S.One],
    [mul(a, P(th(b), c), inv(P(sh(b), c))), mul(a, inv(P(ch(b), c))), S.One, S.One],
    [mul(a, P(cth(b), c), inv(P(ch(b), c))), mul(a, inv(P(sh(b), c))), S.One, S.One],
    [mul(a, P(cth(b), c), P(th(b), c)), a, S.One, S.One],
    [mul(c, add(th(a), th(b)), inv(add(1, mul(th(a), th(b))))), mul(th(add(a, b)), c), S.One, S.One],
  ];
  const addm: [Expr, Expr][] = [
    [add(mul(c, sn(a), cs(b)), mul(c, cs(a), sn(b)), d), add(mul(sn(add(a, b)), c), d)],
    [add(mul(c, cs(a), cs(b)), mul(-1, c, sn(a), sn(b)), d), add(mul(cs(add(a, b)), c), d)],
    [add(mul(c, sn(a), cs(b)), mul(-1, c, cs(a), sn(b)), d), add(mul(sn(sub(a, b)), c), d)],
    [add(mul(c, cs(a), cs(b)), mul(c, sn(a), sn(b)), d), add(mul(cs(sub(a, b)), c), d)],
    [add(mul(c, sh(a), ch(b)), mul(c, sh(b), ch(a)), d), add(mul(sh(add(a, b)), c), d)],
    [add(mul(c, ch(a), ch(b)), mul(c, sh(a), sh(b)), d), add(mul(ch(add(a, b)), c), d)],
  ];
  const identityM: [Expr, Expr][] = [
    [mul(a, P(sn(b), 2)), sub(a, mul(a, P(cs(b), 2)))],
    [mul(a, P(tn(b), 2)), sub(mul(a, P(inv(cs(b)), 2)), a)],
    [mul(a, P(ct(b), 2)), sub(mul(a, P(inv(sn(b)), 2)), a)],
    [mul(a, sn(add(b, c))), mul(a, add(mul(sn(b), cs(c)), mul(sn(c), cs(b))))],
    [mul(a, cs(add(b, c))), mul(a, sub(mul(cs(b), cs(c)), mul(sn(b), sn(c))))],
    [mul(a, tn(add(b, c))), mul(a, mul(add(tn(b), tn(c)), inv(sub(1, mul(tn(b), tn(c))))))],
    [mul(a, P(sh(b), 2)), sub(mul(a, P(ch(b), 2)), a)],
    [mul(a, P(th(b), 2)), sub(a, mul(a, P(inv(ch(b)), 2)))],
    [mul(a, P(cth(b), 2)), add(a, mul(a, P(inv(sh(b)), 2)))],
    [mul(a, sh(add(b, c))), mul(a, add(mul(sh(b), ch(c)), mul(sh(c), ch(b))))],
    [mul(a, ch(add(b, c))), mul(a, add(mul(ch(b), ch(c)), mul(sh(b), sh(c))))],
    [mul(a, th(add(b, c))), mul(a, mul(add(th(b), th(c)), inv(add(1, mul(th(b), th(c))))))],
  ];
  const art = (x: Expr): [Expr, Expr][] => [
    [add(sub(x, mul(x, P(cs(b), 2))), c), add(mul(x, P(sn(b), 2)), c)],
    [add(sub(x, mul(x, P(inv(cs(b)), 2))), c), add(mul(-1, x, P(tn(b), 2)), c)],
    [add(sub(x, mul(x, P(inv(sn(b)), 2))), c), add(mul(-1, x, P(ct(b), 2)), c)],
    [add(sub(x, mul(x, P(ch(b), 2))), c), add(mul(-1, x, P(sh(b), 2)), c)],
    [add(sub(x, mul(x, P(inv(ch(b)), 2))), c), add(mul(x, P(th(b), 2)), c)],
    [add(x, mul(x, P(inv(sh(b)), 2)), c), add(mul(x, P(cth(b), 2)), c)],
  ];
  const exs: FnName[] = ['cos', 'cos', 'sin', 'cosh', 'cosh', 'sinh'];
  const artifacts: [Expr, Expr, FnName][] = [...art(a), ...art(mul(a, d))].map(([p, r], i) => [p, r, at(exs, i % 6)]);
  PATS = { a, b, c, d, division, addm, identity: identityM, artifacts };
  return PATS;
}

/** SymPy _replace_mul_fpowxgpow: f(b)**e1 * g(b)**e2 -> h(b)**e3 when e1 = rexp(e2). */
function replaceMulFpowxgpow(expr: Expr, f: FnName, g: FnName, rexp: (x: Expr) => Expr, h: FnName | undefined, rexph: (x: Expr) => Expr): Expr {
  const fargs = new ExprMap<Expr>();
  const gargs = new ExprMap<Expr>();
  const args: Expr[] = [];
  for (const x of expr.args) {
    if (isPowNode(x) || isF(x, f, g)) {
      const [b, e] = isPowNode(x) ? [x.base, x.exp] : [x, S.One];
      if (positive(b) === true || isIntegerQ(e) === true) {
        if (isF(b, f)) {
          fargs.set(first(b.args), add(fargs.get(first(b.args)) ?? S.Zero, e));
          continue;
        }
        if (isF(b, g)) {
          gargs.set(first(b.args), add(gargs.get(first(b.args)) ?? S.Zero, e));
          continue;
        }
      }
    }
    args.push(x);
  }
  let hit = false;
  for (const key of [...fargs.keys()]) {
    const ge = gargs.get(key);
    if (ge === undefined) continue;
    const fe = getOrThrow(fargs, key);
    if (eq(fe, rexp(ge))) {
      fargs.delete(key);
      gargs.delete(key);
      args.push(h === undefined ? S.One : pow(F(h, key), rexph(fe)));
      hit = true;
    }
  }
  if (!hit) return expr;
  for (const [key, e] of fargs) args.push(pow(F(f, key), e));
  for (const [key, e] of gargs) args.push(pow(F(g, key), e));
  return mul(...args);
}

const idn = (x: Expr): Expr => x;
const midn = (x: Expr): Expr => neg(x);

/** SymPy _match_div_rewrite: the division rules 0-5 and 8-13 without pattern matching. */
function matchDivRewrite(expr: Expr, i: number): Expr | undefined {
  const table: Partial<Record<number, [FnName, FnName, (x: Expr) => Expr, FnName | undefined]>> = {
    0: ['sin', 'cos', midn, 'tan'],
    1: ['tan', 'cos', idn, 'sin'],
    2: ['cot', 'sin', idn, 'cos'],
    3: ['tan', 'sin', midn, 'cos'],
    4: ['cot', 'cos', midn, 'sin'],
    5: ['cot', 'tan', idn, undefined],
    8: ['sinh', 'cosh', midn, 'tanh'],
    9: ['tanh', 'cosh', idn, 'sinh'],
    10: ['coth', 'sinh', idn, 'cosh'],
    11: ['tanh', 'sinh', midn, 'cosh'],
    12: ['coth', 'cosh', midn, 'sinh'],
    13: ['coth', 'tanh', idn, undefined],
  };
  const r = table[i];
  if (r === undefined) return undefined;
  const [f, g, rexp, h] = r;
  return replaceMulFpowxgpow(expr, f, g, rexp, h, [3, 4, 11, 12].includes(i) ? midn : idn);
}

/** SymPy _trigsimp: the pattern-matching algorithm of trigsimp_old. */
function trigsimpMatch(expr: Expr, deep: boolean): Expr {
  return hasTrigs(expr) ? trigsimpMatchImpl(expr, deep) : expr;
}

/** The match as a map (empty when there is no match: then every wild is unassigned). */
const matchMap = (e: Expr, p: Expr): Map<Sym, Expr> => match(e, p) ?? new Map<Sym, Expr>();
const getW = (m: Map<Sym, Expr>, w: Wild): Expr | undefined => [...m].find(([k]) => k.key === w.key)?.[1];
const getWOr = (m: Map<Sym, Expr>, w: Wild, d: Expr): Expr => getW(m, w) ?? d;
const getWReq = (m: Map<Sym, Expr>, w: Wild): Expr => defined(getW(m, w), 'a wild of the pattern');

function trigsimpMatchImpl(expr0: Expr, deep: boolean): Expr {
  const P = trigpats();
  const { a, b, c, d } = P;
  let expr = expr0;
  if (expr instanceof Mul) {
    if (!expr.isCommutative) {
      const [com, nc] = argsCncSplit(expr);
      expr = mul(trigsimpMatch(mul(...com), deep), ...nc);
    } else {
      for (const [i, [pattern, simp, ok1, ok2]] of P.division.entries()) {
        if (!dotrig(expr, pattern)) continue;
        const newexpr = matchDivRewrite(expr, i);
        if (newexpr !== undefined) {
          if (!eq(newexpr, expr)) {
            expr = newexpr;
            break;
          }
          continue;
        }
        const res = matchMap(expr, pattern);
        const rc = getWOr(res, c, S.Zero);
        if (isZero(rc)) continue;
        if (isIntegerQ(rc) !== true) {
          if (positive(subs(ok1, res)) !== true) continue;
          if (positive(subs(ok2, res)) !== true) continue;
        }
        const ra = getWOr(res, a, S.One);
        const rb = getWReq(res, b);
        if (some(ra, (w) => (isTrigFunction(w) || isHyperFunction(w)) && eq(first(w.args), rb))) continue;
        expr = subs(simp, res);
        break;
      }
    }
  }
  if (expr instanceof Add) {
    const args: Expr[] = [];
    for (const term0 of expr.args) {
      let term = term0;
      let nc: Expr = S.One;
      if (!term.isCommutative) {
        const [com, ncs] = argsCncSplit(term);
        nc = mul(...ncs);
        term = mul(...com);
      }
      term = trigsimpMatch(term, deep);
      for (const [pattern, result] of P.identity) {
        const res = match(term, pattern);
        if (res !== undefined) {
          term = subs(result, res);
          break;
        }
      }
      args.push(mul(term, nc));
    }
    if (args.length !== expr.args.length || args.some((x, i) => !eq(x, at(expr.args, i)))) {
      const e1 = add(...args);
      const e2 = expand(e1);
      expr = countOps(e2) < countOps(e1) ? e2 : e1;
    }
    if (expr instanceof Add) {
      for (const [pattern, result] of P.addm) {
        if (!dotrig(expr, pattern)) continue;
        expr = TR10i(expr);
        if (hasHyperFunction(expr)) {
          const res = matchMap(expr, pattern);
          const ra = getW(res, a);
          const rb = getW(res, b);
          if (ra === undefined || rb === undefined) continue;
          const rd = getWOr(res, d, S.Zero);
          if (some(rd, (w) => (isTrigFunction(w) || isHyperFunction(w)) && (eq(first(w.args), ra) || eq(first(w.args), rb)))) continue;
          expr = subs(result, res);
          break;
        }
      }
    }
    for (const [pattern0, result0, ex] of P.artifacts) {
      if (!dotrig(expr, pattern0)) continue;
      const at_ = new Wild('a', { properties: [(e: Expr) => !hasF(e, ex)] });
      const pattern = xreplace(pattern0, [[a, at_]]);
      const result = xreplace(result0, [[a, at_]]);
      let m = match(expr, pattern);
      let was: Expr | undefined;
      while (m !== undefined && (was === undefined || !eq(was, expr))) {
        was = expr;
        const ma = getWOr(m, at_, S.Zero);
        const mc = getWOr(m, c, S.Zero);
        const md = getW(m, d);
        if (isZero(ma) || mc.args.some((x) => eq(x, neg(ma))) || isZero(add(ma, mc)) || (md !== undefined && isZero(add(mul(ma, md), mc)))) break;
        const full = new Map(m);
        full.set(c, mc);
        expr = subs(result, full);
        m = match(expr, pattern);
      }
    }
  } else if (expr instanceof Mul || expr instanceof Pow || (deep && expr.args.length > 0)) {
    expr = rebuild(expr, expr.args.map((x) => trigsimpMatch(x, deep)));
  }
  if (hasTrigs(expr)) {
    const exps = expAtoms(expr);
    let nw = rewrite(expr, 'exp', { deep });
    const fnew = factor(nw);
    if (!eq(fnew, nw)) nw = countOps(fnew) < countOps(nw) ? fnew : nw;
    if ([...expAtoms(nw).keys()].every((x) => exps.has(x))) expr = nw;
  }
  return expr;
}

/** The exp(...) subexpressions (SymPy atoms(exp)). */
function expAtoms(e: Expr): ExprMap<true> {
  const out = new ExprMap<true>();
  some(e, (x) => {
    if (isExpNode(x)) out.set(x, true);
    return false;
  });
  return out;
}

// ---------------------------------------------------------------------------
// exptrigsimp
// ---------------------------------------------------------------------------

/**
 * Simplify exponential, trigonometric and hyperbolic functions (SymPy
 * exptrigsimp): every subexpression is replaced by the shortest of itself
 * and its forms in exp and cos, and products of sums with exponentials
 * are recombined into cosh, sinh and tanh.
 */
export function exptrigsimp(ex: ExprLike): Expr {
  const expr = sympify(ex);
  const expTrig = (e: Expr): Expr => {
    const choices = [e];
    if (hasTrigs(e)) choices.push(rewrite(e, 'exp'));
    // (E itself is rewritten too, as SymPy Exp1: E.rewrite(cos) = sinh(1) + cosh(1))
    choices.push(rewrite(unevaluatedE(e), 'cos'));
    let best = first(choices);
    for (const x of choices.slice(1)) if (countOps(x) < countOps(best)) best = x;
    return best;
  };
  let newexpr = bottomUp(expr, expTrig);
  const f = (rv: Expr): Expr => {
    if (!(rv instanceof Mul)) return rv;
    const [cpart, ncpart] = argsCncSplit(rv);
    if (ncpart.length > 1) return mul(f(mul(...cpart)), ...ncpart);
    const rvd = asPowersDict(rv);
    const newd = new ExprMap<Expr>(rvd);
    const get = (k: Expr): Expr => newd.get(k) ?? S.Zero;
    const inc = (k: Expr, v: Expr): void => {
      newd.set(k, add(get(k), v));
    };
    const signlog = (e: Expr, sign: Expr = S.One): [Expr, Expr] | undefined => {
      if (isE(e)) return [sign, S.One];
      if (isExpNode(e)) return [sign, e.exp];
      if (sign === S.One) return signlog(neg(e), S.NegOne);
      return undefined;
    };
    let ee = rvd.get(S.E) ?? S.Zero;
    for (const k of rvd.keys()) {
      if (!(k instanceof Add && k.args.length === 2)) continue;
      const c = at(k.args, 0);
      const sl = signlog(mul(at(k.args, 1), pow(c, -1)));
      if (sl === undefined) continue;
      const [sign, x] = sl;
      const m = getOrThrow(rvd, k);
      inc(k, neg(m));
      const plus = sign === S.One;
      if (eq(ee, mul(-1, x, m, S.Half))) {
        inc(S.E, neg(ee));
        ee = S.Zero;
        if (plus) inc(mul(2, c, F('cosh', mul(x, S.Half))), m);
        else inc(mul(-2, c, F('sinh', mul(x, S.Half))), m);
      } else {
        const other = sub(1, mul(sign, exp(x)));
        if (eq(get(other), neg(m))) {
          newd.delete(other);
          if (plus) inc(mul(neg(c), pow(F('tanh', mul(x, S.Half)), -1)), m);
          else inc(mul(neg(c), F('tanh', mul(x, S.Half))), m);
        } else {
          inc(add(1, mul(sign, exp(x))), m);
          inc(c, m);
        }
      }
    }
    return mul(...[...newd].map(([k, v]) => pow(k, v)));
  };
  newexpr = bottomUp(newexpr, f);
  if (hasHyperFunction(newexpr)) {
    const [e, back] = hyperAsTrig(newexpr);
    newexpr = back(TR2i(e));
  }
  if (hasTrigFunction(newexpr)) newexpr = TR2i(newexpr);
  // can we ever generate an I where there was none previously?
  // (SymPy keeps the input when the result has an I that the input did not have)
  return at([newexpr, expr], Number(some(newexpr, isI) && !some(expr, isI)));
}

/** e with every E that is not the base of a power written as exp(1) (unevaluated). */
function unevaluatedE(e: Expr): Expr {
  if (isE(e)) return new Pow(S.E, S.One);
  if (e.args.length === 0 || isExpNode(e)) return e;
  return rebuild(e, e.args.map(unevaluatedE));
}

// ---------------------------------------------------------------------------
// exponential-form helpers (used by simplify and integrate)
// ---------------------------------------------------------------------------

const isTrigFn = (x: Expr) => x instanceof Fn && (x.name === 'sin' || x.name === 'cos' || x.name === 'tan');

/** Contains sin/cos/tan. */
export const hasTrigFunctions = (e: Expr): boolean => some(e, isTrigFn);

/** Contains sin/cos/tan or exp. */
export const hasTrig = (e: Expr): boolean => some(e, (x) => isTrigFn(x) || (x instanceof Pow && isE(x.base)));

/** Combine all exp() factors of each product into a single exp (SymPy `powsimp` for exp). */
export function combineExp(ex: ExprLike): Expr {
  return mapBottomUp(sympify(ex), (e) => {
    if (!(e instanceof Mul)) return e;
    const exps = e.args.filter((f): f is Pow => f instanceof Pow && isE(f.base));
    if (exps.length < 2) return e;
    const others = e.args.filter((f) => !(f instanceof Pow && isE(f.base)));
    return mul(...others, exp(expandMul(add(...exps.map((f) => f.exp)))));
  });
}

/** Rewrite sin, cos (and tan) in terms of exp. */
export function rewriteExp(ex: ExprLike): Expr {
  return mapBottomUp(sympify(ex), (e) => {
    if (!(e instanceof Fn)) return e;
    const u = first(e.args);
    const ep = exp(mul(S.I, u));
    const em = exp(mul(-1, S.I, u));
    if (e.name === 'cos') return mul(S.Half, add(ep, em));
    if (e.name === 'sin') return mul(neg(S.I), S.Half, add(ep, mul(-1, em)));
    if (e.name === 'tan') return mul(neg(S.I), add(ep, mul(-1, em)), add(ep, em).pow(-1));
    return e;
  });
}

/** If e = exp(I*y) with I-free y, return y. */
function imaginaryExponent(e: Expr): Expr | undefined {
  if (!(e instanceof Pow && isE(e.base))) return undefined;
  const y = expandMul(mul(-1, S.I, e.exp));
  if (some(y, isI)) return undefined;
  return y;
}

/** Rewrite exp(I*y) as cos(y) + I*sin(y) (y chosen with a canonical sign). */
export function rewriteTrig(ex: ExprLike): Expr {
  return mapBottomUp(sympify(ex), (e) => {
    const y = imaginaryExponent(e);
    if (y === undefined) return e;
    if (couldExtractMinusSign(y)) {
      const z = neg(y);
      return add(cos(z), mul(-1, S.I, sin(z)));
    }
    return add(cos(y), mul(S.I, sin(y)));
  });
}

/** Rewrite to trigonometric form via exponentials (exp(I*y) -> cos(y) + I*sin(y)). */
export function exptotrig(ex: ExprLike): Expr {
  return expandMul(rewriteTrig(expsimp(ex)));
}

/** Exponential form: sin/cos rewritten as exponentials, expanded and combined. */
export function expsimp(ex: ExprLike): Expr {
  return combineExp(expandMul(rewriteExp(sympify(ex))));
}
