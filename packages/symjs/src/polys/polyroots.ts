// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
/** Factors obtained from the explicit roots of a univariate polynomial. */
import type { ComplexValue, Expr, ExprLike } from '../core/nodes';
import { Rational, S, Sym } from '../core/nodes';
import { add, mul, pow, sqrt } from '../core/ops';
import { freeSymbols } from '../core/traverse';
import { isNegative } from '../core/assumptions';
import { fact } from '../core/exprfacts';
import { PolynomialError } from '../core/errors';
import { cos, sin } from '../functions/elementary/elementary';
import { at, cast, first, last } from '../core/guard';
import { ordered } from '../core/match';
import { evalf, toComplex } from '../numeric/evalf';
import { c, cadd, cmul, cneg, cabs } from '../numeric/complex';
import { expand } from '../simplify/expand';
import { powsimp } from '../simplify/powsimp';
import { cancel, fraction, together } from '../simplify/rational';
import { polyHooks, roots, rootsCubicFormula, type RootOptions } from './poly';
import { Poly } from './sympoly';
import { PolyQuintic } from './polyquinticconst';
import { cyclotomicPoly } from './specialpolys';

/**
 * Linear root factors, with a residual factor when explicit roots are incomplete.
 *
 * @param f - Polynomial to operate on.
 * @param x - Polynomial generator.
 * @param filter - Domain restriction on the roots.
 * @returns Linear root factors, with a residual factor when explicit roots are incomplete.
 * @throws RangeError when the polynomial is not univariate.
 * @see SymPy `sympy.polys.polyroots.root_factors`
 * @example
 * ```ts
 * import { ex, rootFactors, symbols } from '@symjs/symjs';
 *
 * const [x] = symbols('x');
 * rootFactors(ex`x**2 - y`, x); // => [x - sqrt(y), x + sqrt(y)]
 * ```
 */
export function rootFactors(f: Poly, x?: Sym, filter?: RootOptions['filter']): Poly[];
/**
 * Linear root factors, with a residual factor when explicit roots are incomplete.
 *
 * @param f - Polynomial to operate on.
 * @param x - Polynomial generator.
 * @param filter - Domain restriction on the roots.
 * @returns Linear root factors, with a residual factor when explicit roots are incomplete.
 * @throws RangeError when the polynomial is not univariate.
 * @see SymPy `sympy.polys.polyroots.root_factors`
 */
export function rootFactors(f: ExprLike, x?: Sym, filter?: RootOptions['filter']): Expr[];
export function rootFactors(f: Poly | ExprLike, x?: Sym, filter?: RootOptions['filter']): Poly[] | Expr[] {
  const p = f instanceof Poly ? f : Poly.from(f, x === undefined ? undefined : [x]);
  if (p.gens.length !== 1) throw new RangeError('root_factors requires a univariate polynomial');
  const gen = cast(p.gen, Sym);
  const zeros = ordered(roots(p.asExpr(), gen, { skipQuintic: true, filter }));
  const factors = zeros.map((r) => Poly.from(add(gen, mul(-1, r)), [gen]));
  if (factors.length === 0) factors.push(p);
  else if (factors.length < p.degree()) factors.push(p.quo(factors.reduce((a,b) => a.mul(b))));
  return f instanceof Poly ? factors : factors.map((factor) => factor.asExpr());
}

const quinticSimplify = (e: Expr): Expr => together(cancel(powsimp(e)));
const numeric = (e: Expr): ComplexValue => toComplex(evalf(e, 40));
const difference = (a: ComplexValue, b: ComplexValue): number => cabs(cadd(a, cneg(b)));

/**
 * Exact radical roots of a solvable irreducible rational quintic; otherwise an empty list.
 *
 * @param poly - Polynomial to represent or transform.
 * @returns Exact radical roots of a solvable irreducible rational quintic; otherwise an empty list.
 * @throws RangeError when the input is not a univariate quintic.
 * @see SymPy `sympy.polys.polyroots.roots_quintic`
 */
export function rootsQuintic(poly: Poly): Expr[] {
  if (poly.degree() !== 5 || !poly.isUnivariate) throw new RangeError('rootsQuintic requires a univariate quintic');
  if (!poly.allCoeffs().every(c => c instanceof Rational)) return [];
  const monic = poly.monic();
  const shift = mul(at(monic.allCoeffs(), 1), Rational.of(-1, 5));
  const f = monic.shift(shift);
  if (!f.isIrreducible) return [];
  const quintic = new PolyQuintic(f);
  const linear = quintic.f20.factorList()[1].find(([factor]) => factor.degree() === 1);
  if (linear === undefined) return [];
  const cs = linear[0].allCoeffs();
  const theta = mul(-1, at(cs, 1), pow(first(cs), -1));
  const d = f.discriminant();
  const delta = sqrt(d);
  const T = quintic.T(theta, d);
  const alpha = add(at(T, 1), mul(at(T, 2), delta));
  const alphaBar = add(at(T, 1), mul(-1, at(T, 2), delta));
  const beta = add(at(T, 3), mul(at(T, 4), delta));
  const betaBar = add(at(T, 3), mul(-1, at(T, 4), delta));
  const discriminant = sqrt(expand(add(pow(alpha, 2), mul(-4, beta))));
  const discriminantBar = sqrt(expand(add(pow(alphaBar, 2), mul(-4, betaBar))));
  const half = Rational.of(1, 2);
  const l1 = quinticSimplify(mul(half, add(mul(-1, alpha), discriminant)));
  const l4 = quinticSimplify(mul(half, add(mul(-1, alpha), mul(-1, discriminant))));
  let l2 = quinticSimplify(mul(half, add(mul(-1, alphaBar), discriminantBar)));
  let l3 = quinticSimplify(mul(half, add(mul(-1, alphaBar), mul(-1, discriminantBar))));
  const expectedOrder = numeric(mul(quintic.order(theta, d), delta));
  const actualOrder = numeric(mul(add(l1, mul(-1, l4)), add(l2, mul(-1, l3))));
  if (difference(expectedOrder, actualOrder) > 1e-10 * Math.max(cabs(expectedOrder), cabs(actualOrder))) [l2, l3] = [l3, l2];

  const l0 = quintic.l0(theta);
  const zeta = quintic.zeta;
  const resolvents = [[l1, l2, l3, l4], [l3, l1, l4, l2], [l2, l4, l1, l3], [l4, l3, l2, l1]]
    .map(ls => quinticSimplify(add(l0, ...ls.map((l, i) => mul(l, at(zeta, i))))));
  // SymPy's order of fifth-root branches: 1, zeta**3, zeta**2, zeta**4, zeta.
  const units = [S.One, quintic.zeta3, quintic.zeta2, quintic.zeta4, quintic.zeta1];
  const candidates = resolvents.map(r => units.map(u => mul(pow(r, Rational.of(1, 5)), u)));
  const values = candidates.map(row => row.map(numeric));
  const r1 = first(first(candidates));
  const r1n = first(first(values));
  // Conjugacy guarantees a real product. Choose the closest branch, avoiding
  // an absolute cutoff that is sensitive to the scale of the quintic.
  const r4index = first(at(values, 3).map((v, i) => [Math.abs(cmul(r1n, v).im), i] as const)
    .sort((a, b) => a[0] - b[0]))[1];
  const r4 = at(at(candidates, 3), r4index);
  const r4n = at(at(values, 3), r4index);
  const [u, v] = quintic.uv(theta, d);
  const plus = numeric(add(u, mul(v, delta, sqrt(5))));
  const minus = numeric(add(u, mul(-1, v, delta, sqrt(5))));
  const coefficients = f.allCoeffs().map(numeric);
  const unity = [S.One, ...zeta];
  const unityValues = unity.map(numeric);
  for (let i = 0; i < 5; i++) {
    for (let j = 0; j < 5; j++) {
      const r2n = at(at(values, 1), i);
      const r3n = at(at(values, 2), j);
      const testPlus = cadd(cmul(r1n, cmul(r2n, r2n)), cmul(r4n, cmul(r3n, r3n)));
      const testMinus = cadd(cmul(r3n, cmul(r1n, r1n)), cmul(r2n, cmul(r4n, r4n)));
      if (difference(testPlus, plus) > 1e-10 || difference(testMinus, minus) > 1e-10) continue;
      const selectedValues = [r1n, r2n, r3n, r4n];
      const rootValues = Array.from({ length: 5 }, (_, k) => cmul(c(1 / 5),
        selectedValues.reduce((sum, r, n) => cadd(sum, cmul(r, at(unityValues, ((5 - k) * (n + 1)) % 5))), c(0))));
      // The two cubic identities do not determine the branches when resolvents
      // vanish (for example x**5 + 5*x**3 + 5*x - 1). Check every Vieta
      // coefficient; merely rejecting duplicate roots, as SymPy does, can
      // accept five distinct values that are not roots of the quintic.
      let recovered = [c(1)];
      for (const r of rootValues) {
        const next = [first(recovered)];
        for (let k = 1; k < recovered.length; k++) next.push(cadd(at(recovered, k), cneg(cmul(r, at(recovered, k - 1)))));
        next.push(cneg(cmul(r, last(recovered))));
        recovered = next;
      }
      const scale = Math.max(...rootValues.map(cabs));
      // Normalize errors by the root scale: an absolute tolerance would accept
      // arbitrary branches when all roots (and hence all coefficients) are tiny.
      if (!recovered.every((value, k) => difference(value, at(coefficients, k)) / scale ** k <= 1e-8)) continue;
      const rs = [r1, at(at(candidates, 1), i), at(at(candidates, 2), j), r4];
      const result = Array.from({ length: 5 }, (_, k) => mul(Rational.of(1, 5),
        add(...rs.map((r, n) => mul(r, at(unity, ((5 - k) * (n + 1)) % 5))))));
      return result.map(r => add(r, shift));
    }
  }
  return [];
}

polyHooks.quintic = (e, x) => rootsQuintic(Poly.from(e, [x]));

/**
 * Roots of a binomial, repeated by multiplicity in canonical root order.
 *
 * @param f - Polynomial to operate on.
 * @returns Roots of a binomial, repeated by multiplicity in canonical root order.
 * @throws PolynomialError when the polynomial has no roots.
 * @see SymPy `sympy.polys.polyroots.roots_binomial`
 */
export function rootsBinomial(f: Poly): Expr[] {
  const n = f.degree();
  if (n < 1) throw new PolynomialError('Polynomial has no roots.');
  const base = mul(-1, cancel(mul(f.nth(0), pow(f.nth(n), -1))));
  const root = pow(base, Rational.of(1, n));
  const alpha = freeSymbols(root).size === 0 ? expand(root, { complex: true }) : root;
  const negative = isNegative(base) === true;
  const ks: number[] = [];
  let imax = Math.floor(n / 2);
  if (n % 2 === 0) { ks.push(imax); imax--; }
  if (!negative) ks.push(0);
  for (let i = imax; i > 0; i--) ks.push(...(negative ? [i, -i] : [-i, i]));
  if (negative) ks.push(0);
  return ks.map(k => {
    const angle = mul(Rational.of(2 * k, n), S.Pi);
    return expand(mul(alpha, add(cos(angle), mul(S.I, sin(angle)))), { powerBase: false });
  });
}

/**
 * Roots of a quadratic, including repeated and zero roots.
 *
 * @param f - Polynomial to operate on.
 * @returns Roots of a quadratic, including repeated and zero roots.
 * @see SymPy `sympy.polys.polyroots.roots_quadratic`
 */
export function rootsQuadratic(f: Poly): Expr[] {
  return roots(fraction(together(f.asExpr()))[0], cast(f.gen, Sym)).map(r => cancel(r));
}

/**
 * Roots of a cubic, including repeated roots.
 *
 * @param f - Polynomial to operate on.
 * @param trig - Use trigonometric forms for real roots when available.
 * @returns Roots of a cubic, including repeated roots.
 * @throws PolynomialError when the polynomial is not cubic.
 * @see SymPy `sympy.polys.polyroots.roots_cubic`
 */
export function rootsCubic(f: Poly, trig = false): Expr[] {
  if (f.degree() !== 3) throw new PolynomialError('a cubic polynomial is required');
  return rootsCubicFormula(f.nth(3), f.nth(2), f.nth(1), f.nth(0), trig);
}

polyHooks.cyclotomic = (e, x) => {
  const f = Poly.from(e, [x]);
  const cs = f.allCoeffs();
  return cs.every((c, i) => c.key === at(cs, -i - 1).key) && f.isCyclotomic ? rootsCyclotomic(f) : [];
};

const rootDomainFacts = { Z: 'integer', Q: 'rational', I: 'imaginary' } as const;
polyHooks.matchRootDomain = (root, filter) => fact(root, rootDomainFacts[filter]) === true;

/**
 * Roots of a cyclotomic polynomial, real parts followed by imaginary parts.
 *
 * @param f - Polynomial to operate on.
 * @param factor - Return one factor per root.
 * @returns Roots of a cyclotomic polynomial, real parts followed by imaginary parts.
 * @throws RangeError when the polynomial is not cyclotomic.
 * @see SymPy `sympy.polys.polyroots.roots_cyclotomic`
 */
export function rootsCyclotomic(f: Poly, factor = false): Expr[] {
  const degree = f.degree();
  // phi(n) >= sqrt(n/2), so n <= 2*degree**2 bounds the inverse search.
  let n = 1;
  for (; n <= 2 * degree ** 2; n++) {
    if (expand(cyclotomicPoly(n, f.gen)).equals(f.asExpr())) break;
  }
  if (n > 2 * degree ** 2) throw new RangeError('expected a cyclotomic polynomial');
  if (factor) {
    const extension = pow(-1, Rational.of(1, n));
    const fs = Poly.from(f.asExpr(), f.gens, { extension }).factorList()[1];
    return ordered(fs.map(([p]) => p.asExpr())).map(p => mul(-1, Poly.from(p, f.gens).TC()));
  }
  const coprime = (aIn: number, bIn: number): boolean => {
    let a = aIn, b = bIn;
    while (b !== 0) [a, b] = [b, a % b];
    return a === 1;
  };
  const ks = Array.from({ length: n }, (_, i) => i + 1).filter(k => coprime(k, n));
  const rank = (k: number): number => k <= n / 2 ? k : n - k;
  ks.sort((a, b) => rank(a) - rank(b) || a - b).reverse();
  return ks.map(k => {
    const angle = mul(Rational.of(2 * k, n), S.Pi);
    return expand(add(cos(angle), mul(S.I, sin(angle))));
  });
}
