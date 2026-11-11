// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
/** Factors obtained from the explicit roots of a univariate polynomial. */
import type { ComplexValue, Expr, ExprLike } from '../core/nodes';
import { Rational, S, Sym } from '../core/nodes';
import { add, mul, pow, sqrt } from '../core/ops';
import { at, cast, first, last } from '../core/guard';
import { ordered } from '../core/match';
import { evalf, toComplex } from '../numeric/evalf';
import { c, cadd, cmul, cneg, cabs } from '../numeric/complex';
import { expand } from '../simplify/expand';
import { powsimp } from '../simplify/powsimp';
import { cancel, together } from '../simplify/rational';
import { polyHooks, roots } from './poly';
import { Poly } from './sympoly';
import { PolyQuintic } from './polyquinticconst';

/** Linear root factors, with a residual factor when explicit roots are incomplete. */
export function rootFactors(f: Poly, x?: Sym): Poly[];
export function rootFactors(f: ExprLike, x?: Sym): Expr[];
export function rootFactors(f: Poly | ExprLike, x?: Sym): Poly[] | Expr[] {
  const p = f instanceof Poly ? f : Poly.from(f, x === undefined ? undefined : [x]);
  if (p.gens.length !== 1) throw new RangeError('root_factors requires a univariate polynomial');
  const gen = cast(p.gen, Sym);
  const zeros = ordered(roots(p.asExpr(), gen, { skipQuintic: true }));
  const factors = zeros.map((r) => Poly.from(add(gen, mul(-1, r)), [gen]));
  if (factors.length === 0) factors.push(p);
  else if (factors.length < p.degree()) factors.push(p.quo(factors.reduce((a,b) => a.mul(b))));
  return f instanceof Poly ? factors : factors.map((factor) => factor.asExpr());
}

const quinticSimplify = (e: Expr): Expr => together(cancel(powsimp(e)));
const numeric = (e: Expr): ComplexValue => toComplex(evalf(e, 40));
const difference = (a: ComplexValue, b: ComplexValue): number => cabs(cadd(a, cneg(b)));

/** Exact radical roots of a solvable irreducible rational quintic; otherwise an empty list. */
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
