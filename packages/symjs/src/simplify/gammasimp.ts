// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file SymPy `gammasimp` and `combsimp`, ported from SymPy 1.14
 * (sympy/simplify/gammasimp.py and sympy/simplify/combsimp.py, BSD 3-Clause).
 * Factorials, binomials, rising/falling factorials, Beta and Catalan numbers
 * are written with Gamma; Gamma arguments are reduced to integer shifts
 * (the `_rf` denesting), ratios of Gamma factors are simplified, and (for
 * gammasimp) the reflection, duplication and multiplication theorems are
 * applied before factors are absorbed into the Gamma functions. combsimp
 * then writes the result with factorials and binomials again.
 */

import type { Expr, ExprLike } from '../core/nodes';
import { Add, Dummy, Fn, Mul, Piecewise, Pow, Rational, S, Sym, UndefFn } from '../core/nodes';
import { polyCoefficients } from '../polys/poly';
import { powsimp } from './powsimp';
import { cancel, fraction } from './rational';
import { add, mul, pow, sqrt, sympify } from '../core/ops';
import { boundSymbols, freeSymbols, mapBottomUp, rebuild, xreplace } from '../core/traverse';
import { at, expectType, first, pair } from '../core/guard';

/** A value known to be a Rational. */
const asRat = (v: Expr): Rational => expectType(v, (x): x is Rational => x instanceof Rational, 'a rational shift');
import { isIntegerQ, isNegative as isNegativeQ, isNonNegative, isPositive, isZero as isZeroQ } from '../core/assumptions';
import { argsCncSplit, asNumerDenom, asPowersDict } from '../core/methods';
import { countOps, ordered } from '../core/match';
import { compareKeys, sortKey } from '../printing/sortkey';
import { Ge, Gt, piecewise } from '../core/logic';
import { expandFunc } from '../functions/special';
import { fn } from '../functions/elementary';
import { expand } from './expand';
import { rewrite } from './rewrite';
import { factor } from '../polys/sympoly';

const gamma = (x: Expr) => fn('gamma', [x]);
const isGamma = (e: Expr): e is Fn => e instanceof Fn && e.name === 'gamma';
const hasGamma = (e: Expr): boolean => isGamma(e) || e.args.some(hasGamma);
const countGamma = (e: Expr): number => (isGamma(e) ? 1 : 0) + e.args.reduce((s, a) => s + countGamma(a), 0);
const isInt = (e: Expr): e is Rational => e instanceof Rational && e.q === 1n;
const isExpPow = (e: Expr): e is Pow => e instanceof Pow && e.base.key === S.E.key;
const mulArgs = (e: Expr): readonly Expr[] => (e instanceof Mul ? e.args : [e]);
const range = (n: number): number[] => Array.from({ length: n }, (_, i) => i);
/** SymPy list.remove: drop the first element equal to x. */
const remove = (xs: Expr[], x: Expr): void => {
  xs.splice(
    xs.findIndex((y) => y.key === x.key),
    1,
  );
};

/** x <= 0 is known (SymPy (x <= 0) == True). */
const knownNonPositive = (x: Expr): boolean => isNegativeQ(x) === true || isZeroQ(x) === true;

/** Piecewise((pos, cond), (neg, True)) where `known` is the truth value of cond, when known. */
const branch = (pos: Expr, neg: Expr, known: boolean | undefined, cond: Expr): Expr => (known === undefined ? piecewise([pos, cond], [neg, true]) : known ? pos : neg);

/**
 * Factorial, binomial, rf, ff, beta and catalan written with gamma (SymPy
 * rewrite(gamma)). With piecewise (SymPy's default) rf and ff become
 * Piecewise expressions on the sign of their first argument; without it
 * (SymPy piecewise=False), rf(x, k) for x <= 0 and ff(x, k) for x < 0 use
 * the reflected form, so that rf(0, k) does not become gamma(k)/gamma(0) = 0.
 */
export function toGamma(e: Expr, piecewiseForm = false): Expr {
  return mapBottomUp(e, (x) => {
    if (!(x instanceof Fn)) return x;
    switch (x.name) {
      case 'rf': {
        const [a, b] = pair(x.args);
        const pos = mul(gamma(add(a, b)), pow(gamma(a), -1));
        const neg = mul(pow(-1, b), gamma(add(1, mul(-1, a))), pow(gamma(add(1, mul(-1, a), mul(-1, b))), -1));
        // Piecewise((pos, a > 0), (neg, True)), its condition decided by the assumptions on a
        if (piecewiseForm) return branch(pos, neg, isPositive(a), Gt(a, 0));
        return knownNonPositive(a) ? neg : pos;
      }
      case 'ff': {
        const [a, b] = pair(x.args);
        const pos = mul(gamma(add(a, 1)), pow(gamma(add(a, mul(-1, b), 1)), -1));
        const neg = mul(pow(-1, b), gamma(add(b, mul(-1, a))), pow(gamma(mul(-1, a)), -1));
        if (piecewiseForm) return branch(pos, neg, isNonNegative(a), Ge(a, 0));
        return isNegativeQ(a) === true ? neg : pos;
      }
      case 'beta': {
        const [a, b] = pair(x.args);
        return mul(gamma(a), gamma(b), pow(gamma(add(a, b)), -1));
      }
      case 'factorial':
      case 'binomial':
      case 'catalan':
        return rewrite(x, 'gamma', { deep: false });
      default:
        return x;
    }
  });
}

/** SymPy `as_coeff_Add`: [the rational constant term, the rest]. */
function coeffAdd(e: Expr): [Rational, Expr] {
  if (e instanceof Rational) return [e, S.Zero];
  const c = e instanceof Add ? first(e.args) : undefined;
  if (e instanceof Add && c instanceof Rational) return [c, add(...e.args.slice(1))];
  return [S.Zero, e];
}

/** The rising factorial a*(a + 1)*...*(a + n - 1), n >= 1. */
const rising = (a: Expr, n: Rational): Expr => mul(...range(Number(n.p)).map((i) => add(a, i)));

/**
 * gamma(n) through SymPy's `_rf(1, n - 1)`: the integer part c of the
 * argument is split off, gamma(r + 1 + c) = gamma(r + 1)*rf(r + 1, c).
 */
function denest(n: Expr): Expr {
  const b = expand(add(n, -1));
  const [c, r] = coeffAdd(b);
  if (isInt(c) && c.p > 0n) return mul(gamma(add(r, 1)), rising(add(r, 1), c));
  if (isInt(c) && c.p < 0n) return mul(gamma(add(r, 1)), pow(rising(add(r, 1, c), Rational.of(-c.p)), -1));
  return gamma(add(b, 1));
}

const denestAll = (e: Expr): Expr => mapBottomUp(e, (x) => (isGamma(x) ? denest(first(x.args)) : x));

/** SymPy `_gammasimp(expr, as_comb)`; `level0` is the level rule_gamma starts at. */
function gammasimpCore(exprIn: Expr, asComb: boolean, level0 = 0): Expr {
  const expr0 = denestAll(exprIn);

  /** Return True if there is a gamma factor in shallow args. */
  const gammaFactor = (x: Expr): boolean => {
    if (isGamma(x)) return true;
    if (x instanceof Add || x instanceof Mul) return x.args.some(gammaFactor);
    if (x instanceof Pow && (isIntegerQ(x.exp) === true || isPositive(x.base) === true)) return gammaFactor(x.base);
    return false;
  };

  /** Simplify ratios of gammas. */
  const gammaRat = (x: Expr): Expr => {
    const xx = denestAll(x);
    return countGamma(xx) < countGamma(x) ? xx : x;
  };

  const ruleGamma = (exprIn: Expr, levelIn = 0): Expr => {
    let expr = exprIn;
    let level = levelIn;
    if (expr.args.length === 0) return expr;
    // recursion step (a Piecewise holds (expr, cond) pairs in SymPy, which are not products)
    if (level === 0) {
      if (!(expr instanceof Piecewise)) expr = rebuild(expr, expr.args.map((x) => ruleGamma(x, 1)));
      level += 1;
    }
    if (!(expr instanceof Mul)) return expr;
    // non-commutative step
    if (level === 1) {
      const [c, nc] = argsCncSplit(expr);
      if (!c.length) return expr;
      if (nc.length) return mul(ruleGamma(mul(...c), 2), ...nc);
      level += 1;
    }
    // pure gamma handling, not factor absorption
    if (level === 2) {
      const T = expr.args.filter(gammaFactor);
      const gammaInd = mul(...expr.args.filter((a) => !gammaFactor(a)));
      let [nd, dd] = asNumerDenom(mul(...T));
      for (let ipass = 0; ipass < 2; ipass++) {
        const args = ordered(mulArgs(nd));
        for (let i = 0; i < args.length; i++) {
          const ni = args[i];
          if (ni instanceof Add) {
            const den = dd;
            [args[i], dd] = asNumerDenom(add(...ni.args.map((a) => ruleGamma(gammaRat(mul(a, pow(den, -1))), level + 1))));
            if (!hasGamma(dd)) break;
          }
        }
        nd = mul(...args);
        if (ipass === 0 && !gammaFactor(nd)) break;
        [nd, dd] = [dd, nd]; // now process in reversed order
      }
      expr = mul(gammaInd, nd, pow(dd, -1));
      if (!(expr instanceof Mul && (gammaFactor(dd) || gammaFactor(nd)))) return expr;
      level += 1;
    }
    // iteration until constant
    if (level === 3) {
      for (;;) {
        const was = expr;
        expr = ruleGamma(expr, 4);
        if (expr.key === was.key) return expr;
      }
    }
    return gammaProduct(expr);
  };

  /** The level >= 4 work on a product: gamma theorems and factor absorption. */
  const gammaProduct = (expr: Expr): Expr => {
    const numerGammas: Expr[] = [];
    const denomGammas: Expr[] = [];
    const numerOthers: Expr[] = [];
    const denomOthers: Expr[] = [];
    const explicate = (p: Expr, gammas: Expr[], others: Expr[]): void => {
      if (p.key === S.One.key) return;
      const [b, e] = p instanceof Pow ? [p.base, p.exp] : [p, S.One];
      if (isInt(e)) {
        const k = Number(e.p);
        if (isGamma(b)) gammas.push(...range(k).map(() => first(b.args)));
        else others.push(...range(k).map(() => b));
      } else others.push(p);
    };
    for (const a of ordered(expr.args).reverse()) {
      const [n, d] = asNumerDenom(a);
      explicate(n, numerGammas, numerOthers);
      explicate(d, denomGammas, denomOthers);
    }

    if (!asComb) {
      reflection(numerGammas, numerOthers, denomOthers);
      reflection(denomGammas, denomOthers, numerOthers);
      duplication(numerGammas, denomGammas, numerOthers, denomOthers);
      duplication(denomGammas, numerGammas, denomOthers, numerOthers);
      multiplicationTheorem(numerGammas, numerOthers);
      multiplicationTheorem(denomGammas, denomOthers);
    }
    absorb(numerGammas, denomGammas, numerOthers, denomOthers);

    return mul(
      ...numerGammas.map(gamma),
      pow(mul(...denomGammas.map(gamma)), -1),
      ...numerOthers,
      pow(mul(...denomOthers), -1),
    );
  };

  const was = factor(expr0);
  let expr = ruleGamma(was, level0);
  if (expr.key !== was.key) expr = factor(expr);
  return mapBottomUp(expr, (x) => (isGamma(x) && first(x.args) instanceof Rational ? expandFunc(x) : x));
}

/** The reflection formula gamma(x)*gamma(1 - x) = pi/sin(pi*x) (SymPy updates `gammas` in place). */
function reflection(gammas: Expr[], numer: Expr[], denom: Expr[]): void {
  const out: Expr[] = [];
  for (let g1 = gammas.pop(); g1 !== undefined; g1 = gammas.pop()) {
    if (isIntegerQ(g1) === true) {
      out.push(g1);
      continue;
    }
    const x = g1;
    const i = gammas.findIndex((g2) => isInt(add(x, g2, -1)));
    if (i < 0) {
      out.push(x);
      continue;
    }
    const n = Number(asRat(add(x, first(gammas.splice(i, 1)), -1)).p);
    numer.push(S.Pi);
    denom.push(fn('sin', [mul(S.Pi, x)]));
    if (n > 0) numer.push(...range(n).map((k) => add(1, mul(-1, x), k)));
    else denom.push(...range(-n).map((k) => add(mul(-1, x), -k)));
  }
  gammas.push(...out);
}

/**
 * The duplication theorem cancelling an upper and a lower gamma:
 * gamma(2*s)/gamma(s) = 2**(2*s + 1)/(4*sqrt(pi))*gamma(s + 1/2).
 */
function duplication(ng: Expr[], dg: Expr[], no: Expr[], dn: Expr[]): void {
  for (;;) {
    let hit: [Expr, Expr, Rational] | undefined;
    for (const x of ng) {
      for (const y of dg) {
        const n = add(x, mul(-2, y));
        if (isInt(n)) {
          hit = [x, y, n];
          break;
        }
      }
      if (hit) break;
    }
    if (!hit) return;
    const [x, y, n] = hit;
    remove(ng, x);
    remove(dg, y);
    const k = Number(n.p);
    if (k > 0) no.push(...range(k).map((i) => add(mul(2, y), i)));
    else dn.push(...range(-k).map((i) => add(mul(2, y), -1, -i)));
    ng.push(add(y, S.Half));
    no.push(pow(2, add(mul(2, y), -1)));
    dn.push(sqrt(S.Pi));
  }
}

/** (a - b) mod 1 for rationals a > b (the coefficients are sorted). */
function mod1(a: Rational, b: Rational): Rational {
  const d = asRat(add(a, mul(-1, b)));
  return asRat(add(d, Rational.of(-(d.p / d.q))));
}

/**
 * SymPy `_run`: a run of coefficients whose differences (mod 1) are
 * 1/n, 2/n, ..., (n - 1)/n; its members are removed from coeffs.
 */
function findRun(coeffs: Rational[]): [number, Rational, Rational[]] | undefined {
  const u: Rational[] = [];
  for (const c of coeffs) if (!u.some((v) => v.key === c.key)) u.push(c);
  for (let i = 0; i < u.length; i++) {
    const ui = at(u, i);
    const dj = range(u.length - i - 1).map((t): [Rational, number] => [mod1(at(u, i + 1 + t), ui), i + 1 + t]);
    for (const [one] of dj) {
      if (!(one.p === 1n && one.q !== 1n)) continue;
      const n = Number(one.q);
      const got = [i];
      const get = range(n - 1).map((t) => t + 1);
      for (const [d, j] of dj) {
        const m = mul(n, d);
        const at = isInt(m) ? get.indexOf(Number(m.p)) : -1;
        if (at >= 0) {
          get.splice(at, 1);
          got.push(j);
          if (!get.length) break;
        }
      }
      if (get.length) continue;
      const cs = got.map((j) => at(u, j));
      for (const c of cs) coeffs.splice(coeffs.findIndex((v) => v.key === c.key), 1);
      return [n, first(cs), cs.slice(1)];
    }
  }
  return undefined;
}

/**
 * The multiplication theorem, used when n gammas with arguments differing by
 * 1/n mod 1 are found: gamma(x)*gamma(x + 1/n)*...*gamma(x + (n - 1)/n) =
 * (2*pi)**((n - 1)/2)*n**(1/2 - n*x)*gamma(n*x).
 */
function multiplicationTheorem(gammas: Expr[], numer: Expr[]): void {
  const rats = new Map<string, [Expr, Rational[]]>();
  for (const g of gammas) {
    const [c, resid] = coeffAdd(g);
    const cur = rats.get(resid.key);
    if (cur) cur[1].push(c);
    else rats.set(resid.key, [resid, [c]]);
  }
  const keys = [...rats.values()].sort((a, b) => compareKeys(sortKey(a[0]), sortKey(b[0])));
  const out: Expr[] = [];
  for (const entry of keys) {
    const resid = entry[0];
    const coeffs = entry[1].sort((a, b) => Number(a.p * b.q - b.p * a.q));
    const fresh: Expr[] = [];
    for (let run = findRun(coeffs); run; run = findRun(coeffs)) {
      const [n, ui, other] = run;
      for (const u of other) {
        const con = add(resid, u, -1);
        const d = asRat(add(u, mul(-1, ui)));
        for (let k = 0; k < Number(d.p / d.q); k++) numer.push(add(con, -k));
      }
      const con = mul(n, add(resid, ui));
      numer.push(mul(pow(mul(2, S.Pi), Rational.of(n - 1, 2)), pow(n, add(S.Half, mul(-1, con)))));
      fresh.push(con);
    }
    out.push(...coeffs.map((c) => add(resid, c)), ...fresh);
  }
  gammas.splice(0, gammas.length, ...out);
}

/** Functions and exponents of an expression (SymPy atoms(Function) | {e.exp for e in atoms(Pow)}). */
function functionParts(e: Expr): Set<string> {
  const out = new Set<string>();
  const go = (x: Expr): void => {
    if (x instanceof Fn || x instanceof UndefFn || x instanceof Piecewise || isExpPow(x)) out.add(x.key);
    else if (x instanceof Pow) out.add(`^${x.exp.key}`);
    x.args.forEach(go);
  };
  go(e);
  return out;
}

const sameSet = (a: Set<string>, b: Set<string>): boolean => a.size === b.size && [...a].every((x) => b.has(x));
const symKeys = (e: Expr): Set<string> => new Set([...freeSymbols(e)].map((s) => s.key));

/** Absorb factors into the gammas: x*gamma(x) -> gamma(x + 1) and gamma(x)/(x - 1) -> gamma(x - 1). */
function absorb(numerGammas: Expr[], denomGammas: Expr[], numerOthers: Expr[], denomOthers: Expr[]): void {
  // invariants of every factor and gamma argument: its free symbols and its functional components
  const inv = new Map<string, [Set<string>, Set<string>]>();
  const computeST = (x: Expr): [Set<string>, Set<string>] => inv.get(x.key) ?? [symKeys(x), functionParts(x)];
  const updateST = (x: Expr): void => {
    inv.set(x.key, computeST(x));
  };
  for (const x of [...numerGammas, ...denomGammas, ...numerOthers, ...denomOthers]) updateST(x);
  const findFuzzy = (l: Expr[], x: Expr): Expr | undefined => {
    const [S1, T1] = computeST(x);
    for (const y of l) {
      const [S2, T2] = computeST(y);
      if (!sameSet(T1, T2) || (![...S1].some((s) => S2.has(s)) && (S1.size > 0 || S2.size > 0))) continue;
      const a = freeSymbols(cancel(mul(x, pow(y, -1)))).size;
      if (a === 0 && (S1.size > 0 || S2.size > 0)) return y;
    }
    return undefined;
  };
  for (const [gammas, numer, denom] of [
    [numerGammas, numerOthers, denomOthers],
    [denomGammas, denomOthers, numerOthers],
  ] as const) {
    const out: Expr[] = [];
    for (let g0 = gammas.pop(); g0 !== undefined; g0 = gammas.pop()) {
      let g = g0;
      let cont = true;
      while (cont) {
        cont = false;
        let y = findFuzzy(numer, g);
        if (y !== undefined) {
          remove(numer, y);
          if (y.key !== g.key) {
            const r = mul(y, pow(g, -1));
            numer.push(r);
            updateST(r);
          }
          g = add(g, 1);
          cont = true;
        }
        const gm = add(g, -1);
        y = findFuzzy(denom, gm);
        if (y !== undefined) {
          remove(denom, y);
          if (y.key !== gm.key) {
            const r = mul(gm, pow(y, -1));
            numer.push(r);
            updateST(r);
          }
          g = gm;
          cont = true;
        }
      }
      out.push(g);
    }
    gammas.push(...out);
  }
}

/** Is the node a function application (SymPy Function, which includes exp and Piecewise)? */
const isFunctionNode = (x: Expr): boolean => x instanceof Fn || x instanceof UndefFn || x instanceof Piecewise || isExpPow(x);

/**
 * SymPy `gammasimp`: simplify expressions with gamma functions, minimizing
 * the number of gamma functions and the size of their arguments.
 */
export function gammasimp(exIn: ExprLike): Expr {
  const expr = toGamma(sympify(exIn), true);
  if (!hasGamma(expr)) return expr; // avoid side effects like factoring
  // non-gamma functions are masked, so that their arguments are simplified separately (SymPy issue 22606)
  const funcs = new Map<string, Expr>();
  const collect = (x: Expr, bound: ReadonlySet<string>): void => {
    // functions with bound symbols are not masked (SymPy f & expr.as_dummy().atoms(Function))
    if (isFunctionNode(x) && !isGamma(x) && ![...freeSymbols(x)].some((s) => bound.has(s.key))) funcs.set(x.key, x);
    const bs = boundSymbols(x);
    const inner = bs.length ? new Set([...bound, ...bs.map((b) => b.key)]) : bound;
    x.args.forEach((a) => collect(a, inner));
  };
  collect(expr, new Set());
  if (!funcs.size) return gammasimpCore(expr, false);
  const fs = ordered([...funcs.values()]);
  const dums = fs.map(() => new Dummy());
  const simp = fs.map((f) => {
    if (f instanceof Piecewise) return piecewise(...f.pairs.map(([e, c]): [Expr, Expr] => [gammasimpCore(e, false, 1), c]));
    if (isExpPow(f)) return pow(S.E, gammasimpCore(f.exp, false));
    return rebuild(f, f.args.map((a) => gammasimpCore(a, false)));
  });
  const d = xreplace(
    expr,
    fs.map((f, i) => [f, at(dums, i)]),
  );
  return xreplace(
    gammasimpCore(d, false),
    dums.map((dm, i) => [dm, at(simp, i)]),
  );
}

/** SymPy `_gamma_as_comb`: rewrite in terms of factorials and binomials. */
function gammaAsComb(e: Expr): Expr {
  const f = (rv: Expr): Expr => {
    if (!(rv instanceof Mul)) return rv;
    const rvd = asPowersDict(rv);
    const nd: [Expr[], Expr[]] = [[], []];
    for (const [k, v] of rvd) {
      if (k instanceof Fn && k.name === 'factorial' && isInt(v)) {
        const c = Number(v.p);
        if (c > 0) nd[0].push(...range(c).map(() => first(k.args)));
        else nd[1].push(...range(-c).map(() => first(k.args)));
        rvd.set(k, S.Zero);
      }
    }
    if (!nd[0].length || !nd[1].length) return rv;
    let hit = false;
    for (const m of [0, 1] as const) {
      const xs = nd[m];
      const other = m === 0 ? nd[1] : nd[0];
      let i = 0;
      while (i < xs.length) {
        const ai = at(xs, i);
        // the first later term whose sum with ai is on the other side
        const j = xs.findIndex((aj, k) => k > i && other.some((o) => o.key === add(ai, aj).key));
        if (j < 0) {
          i += 1;
          continue;
        }
        const aj = at(xs, j);
        const sum = add(ai, aj);
        hit = true;
        remove(other, sum);
        xs.splice(j, 1);
        xs.splice(i, 1);
        const b = fn('binomial', [sum, countOps(ai) < countOps(aj) ? ai : aj]);
        rvd.set(b, add(rvd.get(b) ?? S.Zero, m === 0 ? -1 : 1));
      }
    }
    if (!hit) return rv;
    return mul(
      ...[...rvd].map(([k, v]) => pow(k, v)),
      ...nd[0].map((k) => fn('factorial', [k])),
      pow(mul(...nd[1].map((k) => fn('factorial', [k]))), -1),
    );
  };
  return mapBottomUp(rewrite(e, 'factorial'), f);
}

/**
 * SymPy `combsimp`: simplify combinatorial expressions (factorials,
 * binomials, rising and falling factorials), keeping integer arguments;
 * the result is written with factorials and binomials. An expression with
 * a gamma of a non-integer argument is passed to gammasimp.
 */
export function combsimp(exIn: ExprLike): Expr {
  const ex = toGamma(sympify(exIn));
  const nonInteger = (x: Expr): boolean => (isGamma(x) && isIntegerQ(first(x.args)) !== true) || x.args.some(nonInteger);
  if (nonInteger(ex)) return gammasimp(ex);
  return gammaAsComb(gammasimpCore(ex, true));
}

/**
 * SymPy hypersimp(f, k): the term ratio f(k + 1)/f(k) simplified, when it is
 * a rational function of k (f is hypergeometric); undefined otherwise.
 */
export function hypersimp(fIn: ExprLike, k: Expr): Expr | undefined {
  const f = sympify(fIn);
  const ratio = mul(f.subs(k, add(k, 1)), pow(f, -1));
  let r = combsimp(ratio);
  try {
    r = factor(cancel(powsimp(r)));
  } catch {
    // keep the combined ratio
  }
  const [n, d] = fraction(r);
  return isPolyIn(n, k) && isPolyIn(d, k) ? r : undefined;
}

/** Is e a polynomial in k (k need not be a symbol: it is replaced by a dummy first)? */
function isPolyIn(e: Expr, k: Expr): boolean {
  if (!e.has(k)) return true;
  if (k instanceof Sym) return polyCoefficients(expand(e), k) !== undefined;
  const d = new Dummy('k');
  return polyCoefficients(xreplace(expand(e), [[k, d]]), d) !== undefined;
}

/** SymPy Expr.is_hypergeometric(k). */
export function isHypergeometric(f: ExprLike, k: Expr): boolean {
  return hypersimp(f, k) !== undefined;
}

/** SymPy hypersimilar(f, g, k): is f/g a rational function of k (after combinatorial simplification)? */
export function hypersimilar(f: ExprLike, g: ExprLike, k: Expr): boolean {
  const r = combsimp(mul(sympify(f), pow(sympify(g), -1)));
  const [n, d] = fraction(cancel(r));
  return isPolyIn(n, k) && isPolyIn(d, k);
}
