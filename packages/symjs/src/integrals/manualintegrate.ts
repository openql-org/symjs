// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14 (sympy/integrals/manualintegrate.py), BSD 3-Clause
// License, Copyright (c) 2006-2023 SymPy Development Team.

/**
 * @file SymPy manualintegrate's sqrt_quadratic_rule for a polynomial times an
 * odd power of the square root of a quadratic:
 * the recursion of SqrtQuadraticDenomRule, the logarithm of
 * ReciprocalSqrtQuadraticRule (with the perfect-square case of
 * NestedPowRule) and the degenerate cases of a vanishing leading coefficient
 * (sqrt_linear_rule).
 */

import { isNegative, isPositive, isNonZero, isReal } from '../core/assumptions';
import { lcm } from '../core/numbers';
import { at, defined, getOrThrow } from '../core/guard';
import { Ne, piecewise } from '../core/logic';
import { asIndependent, asNumerDenom, isRationalFunction } from '../core/methods';
import type { ExprLike } from '../core/nodes';
import { Add, Derivative, Expr, Dummy, Fn, Integral, Mul, Piecewise, Pow, Rational, S, Special, Sym, impl } from '../core/nodes';
import { add, exp, mul, pow, sqrt, sympify } from '../core/ops';
import { mapBottomUp, preorderTraversal, subs, xreplace } from '../core/traverse';
import { asin, atan, cos, cosh, fn, log, sin, sinh, tan } from '../functions/elementary/elementary';
import { asinh } from '../functions/elementary/trigext';
import { diff } from '../calculus/diff';
import { factor } from '../polys/sympoly';
import { polyCoefficients } from '../polys/poly';
import { DiracDelta, Heaviside, isDiracDelta, isHeaviside } from './transforms/delta';
import { expand, expandMul, expand_trig } from '../simplify/expand';
import { cancel } from '../simplify/rational';

const isZero = (e: Expr): boolean => e instanceof Rational && e.isZero;

/**
 * Elementary antiderivatives using the shared substitution, parts and polynomial rules.
 * Preserve the manual tangent rule's logarithm of cosine; unresolved inputs remain Integrals.
 */
export function manualintegrate(f: ExprLike, x: Sym): Expr {
  const e = sympify(f);
  const assumed = mapBottomUp(e, (t) => t instanceof Sym && t.assumptions.zero === true ? S.Zero : t);
  if (assumed.key !== e.key) return manualintegrate(assumed, x);
  if (!e.has(x)) return mul(e, x);
  if (e instanceof Add) return add(...e.args.map((t) => manualintegrate(t, x)));
  const [constant, dependent] = asIndependent(e, [x]);
  if (!constant.equals(S.One)) return mul(constant, manualintegrate(dependent, x));
  if (e instanceof Derivative) {
    const counts = e.variableCount;
    const index = counts.findIndex(([v]) => v.equals(x));
    if (index >= 0) {
      const args: Expr[] = [e.expr];
      counts.forEach(([v, n], i) => { if (n - Number(i === index) > 0) args.push(v, sympify(n - Number(i === index))); });
      return args.length === 1 ? e.expr : new Derivative(args);
    }
  }
  // Split a linear numerator into a multiple of the quadratic derivative and a constant.
  if (e instanceof Mul) {
    const reciprocal = e.args.find((t): t is Pow => t instanceof Pow && t.exp.equals(S.NegOne));
    if (reciprocal !== undefined) {
      const q = polyCoefficients(reciprocal.base, x);
      const p = polyCoefficients(mul(...e.args.filter(t => t !== reciprocal)), x);
      if (q !== undefined && Math.max(...q.keys()) === 2 && p !== undefined && Math.max(...p.keys()) === 1) {
        const a = getOrThrow(q, 2), b = q.get(1) ?? S.Zero, c = q.get(0) ?? S.Zero;
        const discriminant = add(mul(4, a, c), mul(-1, pow(b, 2)));
        if (isPositive(discriminant) === true && isNonZero(a) === true) {
          const scale = mul(getOrThrow(p, 1), pow(mul(2, a), -1));
          const remainder = add(p.get(0) ?? S.Zero, mul(-1, b, scale)), h = sqrt(discriminant);
          return add(mul(scale, log(reciprocal.base)), mul(2, remainder, pow(h, -1), atan(mul(add(mul(2, a, x), b), pow(h, -1)))));
        }
      }
    }
  }
  // DiracDeltaRule preserves the original affine argument and its zero-slope case.
  if (isDiracDelta(e)) {
    const argument = at(e.args, 0), pc = polyCoefficients(argument, x);
    if (pc !== undefined && Math.max(...pc.keys()) === 1) {
      const slope = getOrThrow(pc, 1), order = e.args[1] ?? S.Zero;
      const primitive = mul(order.equals(S.Zero) ? Heaviside(argument) : DiracDelta(argument, add(order, -1)), pow(slope, -1));
      return piecewise([primitive, Ne(slope, 0)], [mul(x, DiracDelta(pc.get(0) ?? S.Zero, order)), true]);
    }
  }
  // HeavisideRule subtracts the boundary value to make the primitive continuous.
  const factors = e instanceof Mul ? e.args : [e];
  const heaviside = [...factors].reverse().find(isHeaviside);
  if (heaviside !== undefined) {
    const argument = at(heaviside.args, 0);
    const coefficients = polyCoefficients(argument, x);
    if (coefficients !== undefined && Math.max(...coefficients.keys()) === 1) {
      const slope = getOrThrow(coefficients, 1);
      const boundary = mul(-1, coefficients.get(0) ?? S.Zero, pow(slope, -1));
      const primitive = manualintegrate(mul(...factors.filter((t) => t !== heaviside)), x);
      return mul(heaviside, add(primitive, mul(-1, xreplace(primitive, [[x, boundary]]))));
    }
  }
  const secant = factors.find((v): v is Fn => v instanceof Fn && v.name === 'sec');
  if (secant !== undefined) {
    const v = at(secant.args, 0), trig = mul(...factors.filter((g) => g !== secant));
    if (trig instanceof Fn && (trig.name === 'sin' || trig.name === 'cos')) {
      const multiple = cancel(mul(at(trig.args, 0), pow(v, -1)));
      if (multiple instanceof Rational && multiple.isInteger && multiple.p > 1n) {
        const expanded = expandMul(mul(expand_trig(trig), pow(cos(v), -1)));
        return manualintegrate(expanded, x);
      }
    }
  }
  // An odd sine power over cosine becomes a rational polynomial in u = cos(v)**2.
  if (e instanceof Mul && factors.length === 2) {
    const odd = factors.find((g): g is Pow => g instanceof Pow && g.base instanceof Fn && g.base.name === 'sin' && g.exp instanceof Rational && g.exp.isInteger && g.exp.p > 1n && g.exp.p % 2n === 1n);
    if (odd && odd.exp instanceof Rational) {
      const v = at(odd.base.args, 0), slope = diff(v, x);
      if (e.equals(mul(odd, pow(cos(v), -1))) && !slope.has(x) && isNonZero(slope) === true) {
        const u = new Dummy('u'), numerator = pow(add(1, mul(-1, u)), (odd.exp.p - 1n) / 2n);
        const primitive = impl.integrate(expand(mul(numerator, pow(u, -1))), u);
        return expandMul(mul(S.NegHalf, pow(slope, -1), xreplace(primitive, [[u, pow(cos(v), 2)]])));
      }
    }
  }
  // Rational powers of proportional affine forms have one common radical.
  const radicals = [...preorderTraversal(e)].filter((g): g is Pow & { exp: Rational } => g instanceof Pow && g.exp instanceof Rational && !g.exp.isInteger && g.base.has(x));
  if (radicals.length > 1) {
    const base = radicals.reduce((a, b) => a.exp.q >= b.exp.q ? a : b).base, pc = polyCoefficients(base, x);
    if (pc && Math.max(...pc.keys()) === 1) {
      const ratios = radicals.map(r => cancel(mul(r.base, pow(base, -1))));
      if (ratios.every(r => r instanceof Rational && r.isPositive)) {
        const degree = radicals.reduce((d, r) => lcm(d, r.exp.q), 1n);
        const u = new Dummy('u'), slope = getOrThrow(pc, 1);
        const replacements: [Expr, Expr][] = radicals.map((r, i) => [r, mul(pow(at(ratios, i), r.exp), pow(u, mul(degree, r.exp)))]);
        replacements.push([x, mul(add(pow(u, degree), mul(-1, pc.get(0) ?? S.Zero)), pow(slope, -1))]);
        const transformed = expandMul(mul(degree, pow(u, degree - 1n), xreplace(e, replacements)));
        if (isRationalFunction(transformed, [u]) && isNonZero(slope) === true) {
          const terms = transformed instanceof Add ? transformed.args : [transformed];
          const primitive = add(...terms.map(t => {
            const [c, f] = asIndependent(t, [u], { asAdd: false });
            return mul(c, impl.integrate(f, u));
          }));
          return xreplace(expandMul(mul(pow(slope, -1), primitive)), [[u, pow(base, Rational.of(1n, degree))]]);
        }
      }
    }
  }
  // SqrtLinearRule substitutes u = sqrt(a + b*x), producing a rational integrand.
  const root = factors.find((t) => t instanceof Pow && t.exp instanceof Rational && t.exp.q === 2n);
  if (root instanceof Pow && root.exp instanceof Rational) {
    const pc = polyCoefficients(root.base, x);
    const rest = mul(...factors.filter((t) => t !== root));
    if (pc !== undefined && Math.max(...pc.keys()) === 1 && isRationalFunction(rest, [x])) {
      const a = pc.get(0) ?? S.Zero, b = getOrThrow(pc, 1), u = new Dummy('u');
      const transformed = expand(mul(2, pow(b, -1), pow(u, Number(root.exp.p) + 1), xreplace(rest, [[x, mul(add(pow(u, 2), mul(-1, a)), pow(b, -1))]])));
      const primitive = xreplace(expand(impl.integrate(transformed, u)), [[u, sqrt(root.base)]]);
      return piecewise([primitive, Ne(b, 0)], [mul(pow(a, root.exp), manualintegrate(rest, x)), true]);
    }
  }
  if (root instanceof Pow && root.exp instanceof Rational && e instanceof Mul) {
    const q = polyCoefficients(root.base, x);
    const rest = mul(...factors.filter((v) => v !== root));
    if (q?.size === 2 && q.has(0) && q.has(2) && rest instanceof Pow && rest.base.equals(x) && rest.exp instanceof Rational) {
      const a = getOrThrow(q, 0), b = getOrThrow(q, 2), k = rest.exp;
      // u = sqrt(a+b*x**2) gives x*dx = u*du/b.
      if (k.isInteger && k.p > 0n && k.p % 2n === 1n && isNonZero(b) === true) {
        const u = new Dummy('u');
        const transformed = expand(mul(pow(b, -1), pow(u, root.exp.p + 1n), pow(mul(add(pow(u, 2), mul(-1, a)), pow(b, -1)), (k.p - 1n) / 2n)));
        const primitive = impl.integrate(transformed, u);
        return xreplace(primitive, [[u, sqrt(root.base)]]);
      }
      if (k.equals(S.NegOne) && root.exp.equals(S.Half) && isNegative(a) === true) {
        const h = sqrt(mul(-1, a));
        return add(root, mul(-1, h, atan(mul(root, pow(h, -1)))));
      }
      if (k.equals(Rational.of(-4)) && root.exp.equals(S.NegHalf) && isNonZero(a) === true) {
        const u = mul(sqrt(root.base), pow(x, -1));
        return mul(pow(a, -2), add(mul(b, u), mul(Rational.of(-1, 3), pow(u, 3))));
      }
    }
  }
  if (e instanceof Mul) {
    const exponential = factors.find((t): t is Pow => t instanceof Pow && t.base.equals(S.E));
    if (exponential !== undefined) {
      const other = mul(...factors.filter((t) => t !== exponential));
      // u = x**m turns x**(m-1)*exp(x**(2*m)) into a Gaussian.
      const exponent = exponential.exp;
      if (exponent instanceof Pow && exponent.base.equals(x) && exponent.exp instanceof Rational && exponent.exp.isInteger && exponent.exp.p > 0n && exponent.exp.p % 2n === 0n) {
        const m = exponent.exp.p / 2n;
        if (other.equals(pow(x, m - 1n))) return mul(-1, S.I, sqrt(S.Pi), Rational.of(1, 2n * m), fn('erf', [mul(S.I, pow(x, m))]));
      }
      // u = exp(a*x+b) turns sqrt(c+d*exp(2*a*x+2*b))*du into a quadratic radical.
      if (other instanceof Pow && other.exp.equals(S.Half)) {
        const rate = diff(exponent, x);
        if (!rate.has(x) && isNonZero(rate) === true) {
          const u = new Dummy('u');
          const radicand = xreplace(other.base, [[exp(mul(2, exponent)), pow(u, 2)]]);
          if (!radicand.has(x)) return mul(pow(rate, -1), xreplace(impl.integrate(sqrt(radicand), u), [[u, exponential]]));
        }
      }
    }
  }
  // Substitute the innermost affine radical first in a nested quadratic radical.
  if (e instanceof Pow && e.exp instanceof Rational && e.exp.q === 2n && e.base instanceof Add) {
    for (const term of preorderTraversal(e.base)) {
      if (!(term instanceof Pow && term.exp.equals(S.Half))) continue;
      const pc = polyCoefficients(term.base, x);
      if (pc === undefined || Math.max(...pc.keys()) !== 1) continue;
      const b = getOrThrow(pc, 1), a = pc.get(0) ?? S.Zero, u = new Dummy('u');
      if (isNonZero(b) !== true) continue;
      const argument = mul(add(pow(u, 2), mul(-1, a)), pow(b, -1));
      const radicand = expand(xreplace(e.base, [[term, u], [x, argument]]));
      const n = e.exp.p;
      if (n < 1n || polyCoefficients(radicand, u) === undefined) continue;
      const transformed = mul(2, u, pow(b, -1), pow(radicand, (n - 1n) / 2n));
      const primitive = sqrtQuadraticRule(mul(expand(transformed), sqrt(radicand)), u, true);
      if (primitive !== undefined) return xreplace(primitive, [[u, term]]);
    }
  }
  const special = specialRule(e, x);
  if (special !== undefined) return special;
  // For u = sqrt(c + b*exp(k*x)), dx/u = 2*du/(k*(u**2-c)).
  if (e instanceof Pow && e.exp.equals(S.NegHalf) && e.base instanceof Add) {
    const [c, dependent] = asIndependent(e.base, [x], { asAdd: true });
    const rate = cancel(mul(diff(dependent, x), pow(dependent, -1)));
    if (isNonZero(c) === true && !rate.has(x) && !isZero(rate)) {
      const u = sqrt(e.base), h = sqrt(c);
      return mul(pow(mul(rate, h), -1), add(log(add(u, mul(-1, h))), mul(-1, log(add(u, h)))));
    }
  }
  // With u = log(x), exp(P(log(x)))*dx becomes exp(P(u)+u)*du.
  if (e instanceof Pow && e.base.equals(S.E) && e.exp.has(log(x))) {
    const u = new Dummy('u'), exponent = add(u, xreplace(e.exp, [[log(x), u]]));
    const pc = polyCoefficients(exponent, u);
    if (!exponent.has(x) && pc !== undefined && Math.max(...pc.keys()) === 2) {
      return xreplace(manualintegrate(exp(exponent), u), [[u, log(x)]]);
    }
  }
  // x**n/log(x) is the exponential integral after u = (n+1)*log(x).
  const logarithm = log(x);
  if (e instanceof Mul && e.has(pow(logarithm, -1))) {
    const power = mul(e, logarithm);
    const exponent = power.equals(x) ? S.One : power instanceof Pow && power.base.equals(x) ? power.exp : undefined;
    if (exponent !== undefined && !exponent.has(x)) {
      const rate = add(exponent, 1);
      return piecewise([fn('Ei', [mul(rate, logarithm)]), Ne(rate, 0)], [log(logarithm), true]);
    }
  }
  // URule: keep the substituted power intact before polynomial expansion.
  if (e instanceof Pow && e.exp instanceof Rational && !e.exp.equals(S.NegOne)) {
    const slope = diff(e.base, x);
    if (!slope.has(x) && !isZero(slope)) return mul(pow(e.base, add(e.exp, 1)), pow(mul(slope, add(e.exp, 1)), -1));
  }
  // TrigRule and HyperbolicRule, followed by the reverse chain rule.
  for (const t of preorderTraversal(e)) {
    if (!(t instanceof Fn)) continue;
    const u = at(t.args, 0);
    let primitive: Expr;
    let kernel: Expr = t;
    switch (t.name) {
      case 'tan': primitive = mul(-1, log(cos(u))); break;
      case 'cot': primitive = log(sin(u)); break;
      case 'sec':
        if (e.has(pow(t, 2))) { kernel = pow(t, 2); primitive = tan(u); }
        else primitive = log(add(tan(u), t));
        break;
      case 'csc':
        if (e.has(pow(t, 2))) { kernel = pow(t, 2); primitive = mul(-1, fn('cot', [u])); }
        else primitive = mul(-1, log(add(fn('cot', [u]), t)));
        break;
      case 'tanh': primitive = log(cosh(u)); break;
      case 'coth': primitive = log(sinh(u)); break;
      case 'sech': primitive = mul(2, atan(fn('tanh', [mul(S.Half, u)]))); break;
      case 'csch': primitive = log(fn('tanh', [mul(S.Half, u)])); break;
      default: continue;
    }
    const du = diff(u, x);
    if (isZero(du)) continue;
    const ratio = cancel(mul(e, pow(mul(kernel, du), -1)));
    if (!ratio.has(x) && !(ratio instanceof Special)) return mul(ratio, primitive);
  }
  // PartsRule reduces a polynomial multiplying a derivative until the polynomial vanishes.
  if (e instanceof Mul) {
    for (const t of preorderTraversal(e)) {
      let primitive: Expr;
      if (t instanceof Derivative && t.variableCount.some(([v]) => v.equals(x))) primitive = manualintegrate(t, x);
      else if (t instanceof Fn && t.name === 'sec' && e.has(pow(t, 2))) primitive = tan(at(t.args, 0));
      else if (t instanceof Fn && (t.name === 'sec' || t.name === 'tan')) primitive = t;
      else continue;
      const derivative = t instanceof Derivative ? t : manualDiff(primitive, x);
      const p = cancel(mul(e, pow(derivative, -1)));
      const pc = polyCoefficients(p, x);
      if (pc !== undefined && Math.max(...pc.keys()) >= 1) {
        return add(mul(p, primitive), mul(-1, manualintegrate(mul(diff(p, x), primitive), x)));
      }
    }
  }
  if (e instanceof Pow && (e.base instanceof Pow || e.base instanceof Mul)) {
    for (const base of preorderTraversal(e.base)) {
      const pc = base instanceof Add || base instanceof Mul ? polyCoefficients(base, x) : undefined;
      if (pc === undefined || Math.max(...pc.keys()) !== 1) continue;
      const a = pc.get(0) ?? S.Zero, b = getOrThrow(pc, 1), shift = add(mul(a, pow(b, -1)), x);
      const degree = affineDegree(e, base, x);
      if (degree !== undefined) {
        const primitive = piecewise([mul(e, shift, pow(add(degree, 1), -1)), Ne(degree, -1)], [mul(e, shift, log(shift)), true]);
        return piecewise([primitive, Ne(b, 0)], [mul(x, subs(e, [[x, S.Zero]])), true]);
      }
    }
  }
  // NestedPowRule preserves branch-sensitive powers while using their logarithmic derivative.
  if (e instanceof Pow || factors.some((t) => t instanceof Pow && t.base instanceof Pow)) {
    const degree = cancel(mul(x, diff(e, x), pow(e, -1)));
    if (degree instanceof Rational) return degree.equals(S.NegOne)
      ? mul(x, e, log(x)) : mul(x, e, pow(add(degree, 1), -1));
  }
  if (e instanceof Pow && e.exp.equals(S.NegOne)) {
    const pc = polyCoefficients(e.base, x);
    if (pc !== undefined && Math.max(...pc.keys()) === 2 && !pc.has(1)) {
      const a = getOrThrow(pc, 0), b = getOrThrow(pc, 2), ratio = cancel(mul(a, pow(b, -1)));
      if (isPositive(ratio) === true || (!(a instanceof Rational) && isNegative(a) === true)) return mul(atan(mul(x, pow(sqrt(ratio), -1))), pow(mul(b, sqrt(ratio)), -1));
    }
  }
  const quadratic = sqrtQuadraticRule(e, x, true);
  if (quadratic !== undefined) return quadratic;
  // Reverse the chain rule for c*u'/(1 + u**2) before rational integration
  // introduces logarithms of complex roots.
  for (const u of preorderTraversal(e)) {
    if (!(u instanceof Fn || u instanceof Pow) || !u.has(x)) continue;
    const ratio = cancel(mul(e, add(1, pow(u, 2)), pow(diff(u, x), -1)));
    if (!ratio.has(x) && !(ratio instanceof Special)) return mul(ratio, atan(u));
  }
  // A repeated irreducible quadratic with a linear term has no manual
  // inverse-tangent rule. Try substitution, then distribute an affine numerator.
  const [num, den] = asNumerDenom(e);
  const numer = polyCoefficients(num, x), denom = polyCoefficients(den, x);
  if (numer && Math.max(...numer.keys()) <= 1 && denom && Math.max(...denom.keys()) > 2) {
    const repeated = factor(den);
    if (repeated instanceof Pow && repeated.exp instanceof Rational && repeated.exp.isInteger) {
      const base = polyCoefficients(repeated.base, x);
      if (base?.has(1) && Math.max(...base.keys()) === 2) {
        const scale = cancel(mul(num, pow(diff(repeated.base, x), -1)));
        if (!scale.has(x)) {
          const power = add(1, mul(-1, repeated.exp));
          return mul(scale, pow(repeated.base, power), pow(power, -1));
        }
        if (num instanceof Add) return manualintegrate(expand(e), x);
        return new Integral([e, x]);
      }
    }
  }
  const result = impl.integrate(e, x);
  if (result instanceof Integral && e instanceof Mul) {
    const expanded = expandMul(e);
    if (expanded instanceof Add) return manualintegrate(expanded, x);
  }
  return result;
}

/** Degree in an affine base, retaining nested powers on their original branches. */
function affineDegree(e: Expr, base: Expr, x: Sym): Expr | undefined {
  if (e.equals(base)) return S.One;
  if (!e.has(x)) return S.Zero;
  if (e instanceof Pow && !e.exp.has(x)) {
    const degree = affineDegree(e.base, base, x);
    return degree === undefined ? undefined : mul(e.exp, degree);
  }
  if (e instanceof Mul) {
    const degrees = e.args.map((t) => affineDegree(t, base, x));
    if (degrees.every((t): t is Expr => t !== undefined)) return add(...degrees);
  }
  return undefined;
}

/** SymPy's special_function_rule patterns and their evaluated rules. */
function specialRule(e: Expr, x: Sym): Expr | undefined {
  if (e instanceof Pow && e.exp.equals(S.NegOne) && e.base instanceof Fn && e.base.name === 'log') {
    const u = at(e.base.args, 0), slope = diff(u, x);
    if (!slope.has(x) && !isZero(slope)) return mul(fn('li', [u]), pow(slope, -1));
  }
  if (e instanceof Mul) {
    const logarithm = e.args.find((v): v is Fn => v instanceof Fn && v.name === 'log');
    if (logarithm !== undefined) {
      const z = add(1, mul(-1, at(logarithm.args, 0)));
      const dz = diff(z, x);
      if (!isZero(dz)) {
        const ratio = cancel(mul(...e.args.filter((v) => v !== logarithm), z, pow(dz, -1)));
        if (!ratio.has(x)) return mul(-1, ratio, fn('polylog', [S.Two, z]));
      }
    }
  }
  const timesX = cancel(mul(e, x));
  const isExponential = (t: Expr): t is Pow => t instanceof Pow && t.base.equals(S.E);
  if (timesX instanceof Fn || isExponential(timesX)) {
    const u = timesX instanceof Fn ? at(timesX.args, 0) : timesX.exp;
    const pc = polyCoefficients(u, x);
    if (timesX instanceof Fn && timesX.name === 'polylog' && !u.has(x)) {
      const z = at(timesX.args, 1);
      if (!cancel(mul(z, pow(x, -1))).has(x)) return fn('polylog', [add(u, 1), z]);
    }
    if (timesX instanceof Fn && (timesX.name === 'sin' || timesX.name === 'cos' || timesX.name === 'sinh' || timesX.name === 'cosh')) {
      const degree = cancel(mul(x, diff(u, x), pow(u, -1)));
      if (degree instanceof Rational && !degree.isZero) {
        const name = timesX.name === 'sin' ? 'Si' : timesX.name === 'cos' ? 'Ci' : timesX.name === 'sinh' ? 'Shi' : 'Chi';
        return mul(fn(name, [u]), pow(degree, -1));
      }
    }
    if (pc !== undefined && Math.max(...pc.keys()) === 1) {
      const a = getOrThrow(pc, 1), b = pc.get(0) ?? S.Zero, ax = mul(a, x);
      if (isExponential(timesX)) return mul(exp(b), fn('Ei', [ax]));
      switch (timesX.name) {
        case 'sin': return add(mul(sin(b), fn('Ci', [ax])), mul(cos(b), fn('Si', [ax])));
        case 'cos': return add(mul(cos(b), fn('Ci', [ax])), mul(-1, sin(b), fn('Si', [ax])));
        case 'sinh': return add(mul(sinh(b), fn('Chi', [ax])), mul(cosh(b), fn('Shi', [ax])));
        case 'cosh': return add(mul(cosh(b), fn('Chi', [ax])), mul(sinh(b), fn('Shi', [ax])));
        default: break;
      }
    }
  }
  if (e instanceof Fn && (e.name === 'sin' || e.name === 'cos') || isExponential(e)) {
    const u = e instanceof Fn ? at(e.args, 0) : e.exp;
    const pc = polyCoefficients(u, x);
    if (pc !== undefined && Math.max(...pc.keys()) === 2) {
      const a = getOrThrow(pc, 2), b = pc.get(1) ?? S.Zero, c = pc.get(0) ?? S.Zero;
      const shift = add(mul(pow(b, 2), pow(mul(4, a), -1)), mul(-1, c));
      if (isExponential(e)) {
        const k = isNegative(a) === true ? mul(-1, a) : a;
        const arg = mul(add(mul(2, a, x), b), pow(mul(2, sqrt(k)), -1), isNegative(a) === true ? -1 : 1);
        return mul(sqrt(S.Pi), pow(mul(2, sqrt(k)), -1), exp(mul(-1, shift)), fn(isNegative(a) === true ? 'erf' : 'erfi', [arg]));
      }
      const z = mul(add(mul(2, a, x), b), pow(sqrt(mul(2, a, S.Pi)), -1));
      const fs = fn('fresnels', [z]), fc = fn('fresnelc', [z]);
      return mul(sqrt(S.Pi), pow(sqrt(mul(2, a)), -1), e.name === 'sin'
        ? add(mul(cos(shift), fs), mul(-1, sin(shift), fc))
        : add(mul(cos(shift), fc), mul(sin(shift), fs)));
    }
  }
  const factors = e instanceof Mul ? e.args : [e];
  const exponential = factors.find(isExponential);
  if (exponential instanceof Pow) {
    const a = cancel(mul(exponential.exp, pow(x, -1)));
    const power = mul(...factors.filter((t) => t !== exponential));
    if (!a.has(x) && power instanceof Pow && power.base.equals(x) && power.exp instanceof Rational && power.exp.q !== 1n) {
      const n = power.exp;
      return mul(power, pow(mul(-1, a, x), mul(-1, n)), fn('uppergamma', [add(n, 1), mul(-1, a, x)]), pow(a, -1));
    }
  }
  if (e instanceof Pow && e.exp instanceof Rational && e.exp.q === 2n && (e.exp.p === 1n || e.exp.p === -1n)) {
    const t = pow(sin(x), 2), pc = polyCoefficients(e.base, t);
    if (pc !== undefined && Math.max(...pc.keys()) === 1) {
      const a = pc.get(0) ?? S.Zero, d = mul(-1, getOrThrow(pc, 1));
      if (!a.has(x) && !d.has(x) && !isZero(a) && !a.equals(d)) return mul(fn(e.exp.p === 1n ? 'elliptic_e' : 'elliptic_f', [x, mul(d, pow(a, -1))]), pow(a, e.exp));
    }
  }
  return undefined;
}

/** Reject malformed substitution arguments with the same range error as SymPy. */
function substitutionExpr(value: ExprLike | ReadonlyMap<ExprLike, ExprLike> | readonly (readonly [Expr, Expr])[]): Expr {
  if (value instanceof Expr || typeof value === 'number' || typeof value === 'bigint') return sympify(value);
  throw new RangeError('expected an expression');
}

/** Substitute expressions, also replacing powers of the argument of a logarithm. */
export function manualSubs(expr: ExprLike, ...args: readonly (ExprLike | ReadonlyMap<ExprLike, ExprLike> | readonly (readonly [Expr, Expr])[])[]): Expr {
  let sequence: readonly (readonly [Expr, Expr])[];
  if (args.length === 2) sequence = [[substitutionExpr(at(args, 0)), substitutionExpr(at(args, 1))]];
  else if (args.length === 1 && args[0] instanceof Map) sequence = [...args[0]].map(([a, b]) => [sympify(a), sympify(b)]);
  else if (args.length === 1 && Array.isArray(args[0])) sequence = args[0];
  else throw new RangeError('subs accepts a sequence of pairs or an old and new expression');
  let result = sympify(expr);
  const extra: [Expr, Expr][] = [];
  for (const [old, replacement] of sequence) {
    if (old instanceof Fn && old.name === 'log') {
      const base = at(old.args, 0);
      result = mapBottomUp(result, (e) => e instanceof Pow && e.base.equals(base) ? exp(mul(e.exp, replacement)) : e);
      extra.push([base, exp(replacement)]);
    }
  }
  return subs(result, [...sequence, ...extra]);
}

/** The derivative identities used by the manual trigonometric substitution rules. */
function manualDiff(e: Expr, x: Sym): Expr {
  if (e instanceof Add) return add(...e.args.map((t) => manualDiff(t, x)));
  if (e instanceof Fn && (e.name === 'tan' || e.name === 'cot')) {
    return mul(e.name === 'tan' ? 1 : -1, pow(fn(e.name === 'tan' ? 'sec' : 'csc', e.args), 2), diff(at(e.args, 0), x));
  }
  return diff(e, x);
}

/** Find substitutions whose derivative divides the integrand and eliminates the integration variable. */
export function findSubstitutions(f: ExprLike, x: Sym, u: Sym): [Expr, Expr, Expr][] {
  const e = sympify(f), results: [Expr, Expr, Expr][] = [];
  const seen = new Set<string>();
  for (const candidate of preorderTraversal(e)) {
    if (candidate.equals(x) || !candidate.has(x) || seen.has(candidate.key)) continue;
    seen.add(candidate.key);
    const derivative = manualDiff(candidate, x);
    if (isZero(derivative)) continue;
    const transformed = cancel(manualSubs(cancel(mul(e, pow(derivative, -1))), candidate, u));
    if (transformed.has(x) || transformed.equals(subs(e, [[x, u]]))) continue;
    const [coefficient, integrand] = asIndependent(transformed, [u], { asAdd: false });
    results.push([candidate, coefficient, integrand]);
  }
  return results;
}

/** The integral of a polynomial (coefficients cancelled) term by term. */
function polyIntegral(p: Expr, x: Sym): Expr {
  const pc = defined(polyCoefficients(expand(p), x), 'polynomial');
  return add(...[...pc].map(([k, c]) => mul(cancel(c), Rational.of(1, k + 1), pow(x, k + 1))));
}

/** The integral of 1/sqrt(a + b*x + c*x**2) with c != 0 (inverse_trig_rule with degenerate=False). */
function reciprocalSqrt(a: Expr, b: Expr, c: Expr, x: Sym): Expr {
  const h = mul(-1, b, pow(mul(2, c), -1));
  const k = add(a, mul(-1, pow(b, 2), pow(mul(4, c), -1)));
  const shifted = add(x, mul(-1, h));
  if (isPositive(k) === true) {
    if (isPositive(c) === true) return mul(asinh(mul(sqrt(mul(c, pow(k, -1))), shifted)), pow(sqrt(c), -1));
    if (isNegative(c) === true) return mul(asin(mul(sqrt(mul(-1, c, pow(k, -1))), shifted)), pow(sqrt(mul(-1, c)), -1));
  }
  const generic = mul(log(add(mul(2, sqrt(c), sqrt(add(a, mul(b, x), mul(c, pow(x, 2))))), b, mul(2, c, x))), pow(sqrt(c), -1));
  // a perfect square: (x - h)*log(x - h)/sqrt(c*(x - h)**2) (NestedPowRule)
  const xh = add(x, mul(-1, h));
  const square = mul(xh, pow(sqrt(mul(c, pow(xh, 2))), -1), log(xh));
  return piecewise([generic, Ne(k, 0)], [square, true]);
}

/** The integral of poly/sqrt(a + b*x + c*x**2) for coefficients coeffs of degree 2 or more (SqrtQuadraticDenomRule). */
function sqrtQuadraticDenom(a: Expr, b: Expr, c: Expr, coeffs0: readonly Expr[], x: Sym): Expr {
  const coeffs = [...coeffs0];
  const result: Expr[] = [];
  for (let i = 0; i < coeffs.length - 2; i++) {
    const n = coeffs.length - 1 - i;
    const coeff = mul(at(coeffs, i), pow(mul(c, n), -1));
    result.push(coeff);
    coeffs[i + 1] = add(at(coeffs, i + 1), mul(-1, 2 * n - 1, b, S.Half, coeff));
    coeffs[i + 2] = add(at(coeffs, i + 2), mul(-1, n - 1, a, coeff));
  }
  const d = at(coeffs, coeffs.length - 1);
  const e = coeffs.length > 1 ? at(coeffs, coeffs.length - 2) : S.Zero;
  const s = sqrt(add(a, mul(b, x), mul(c, pow(x, 2))));
  const constant = add(d, mul(-1, b, e, pow(mul(2, c), -1)));
  const I0 = isZero(constant) ? S.Zero : mul(constant, reciprocalSqrt(a, b, c, x));
  return add(mul(add(...result.map((r, i) => mul(r, pow(x, coeffs.length - 2 - i))), mul(e, pow(c, -1))), s), I0);
}

/** The integral of f*sqrt(a + b*x)**n, b != 0 (sqrt_linear_rule: u = sqrt(a + b*x)), with its degenerate case b = 0. */
function sqrtLinear(f: Expr, a: Expr, b: Expr, n: number, x: Sym): Expr {
  if (isZero(b)) return mul(pow(sqrt(a), n), polyIntegral(f, x));
  const u = new Dummy('u');
  const sub = mul(xreplace(f, [[x, mul(add(pow(u, 2), mul(-1, a)), pow(b, -1))]]), pow(u, n + 1), 2, pow(b, -1));
  const [coeff, rest] = asIndependent(sub, [u]);
  const step = xreplace(mul(coeff, polyIntegral(rest, u)), [[u, sqrt(add(a, mul(b, x)))]]);
  return piecewise([step, Ne(b, 0)], [mul(pow(sqrt(a), n), polyIntegral(f, x)), true]);
}

/**
 * SymPy sqrt_quadratic_rule: the integral of f = p(x)*sqrt(a + b*x + c*x**2)**n
 * for a polynomial p and n = 1 or n = -1. Real coefficients select asin
 * and asinh by their signs; symbolic coefficients retain degenerate cases.
 * Undefined otherwise.
 *
 * @example
 * sqrtQuadraticRule(parse('x*sqrt(x**2 + a*x + b)'), x)
 */
export function sqrtQuadraticRule(f: Expr, x: Sym, manual = false): Expr | undefined {
  const factors = f instanceof Mul ? f.args : [f];
  const root = factors.find((t) => t instanceof Pow && t.exp instanceof Rational && t.exp.q === 2n && t.base.has(x));
  if (!(root instanceof Pow) || !(root.exp instanceof Rational)) return undefined;
  const n = Number(root.exp.p);
  const pc = polyCoefficients(root.base, x);
  if (pc === undefined || Math.max(...pc.keys()) !== 2 || Math.abs(n) !== 1) return undefined;
  const [a, b, c] = [pc.get(0) ?? S.Zero, pc.get(1) ?? S.Zero, getOrThrow(pc, 2)];
  const p = mul(...factors.filter((t) => t !== root));
  if (polyCoefficients(p, x) === undefined) return undefined;
  const k = add(a, mul(-1, pow(b, 2), pow(mul(4, c), -1)));
  if (!manual && n === 1 && (isZero(b) || (!p.has(x) && isReal(k) === true && isReal(c) === true))) return undefined;
  if (isNegative(c) === true && isPositive(k) !== true && !isZero(k)) return undefined;
  const numer = defined(polyCoefficients(expand(mul(p, pow(root.base, (n + 1) / 2))), x), 'polynomial');
  const deg = Math.max(...numer.keys());
  const coeffs = Array.from({ length: deg + 1 }, (_, i) => numer.get(deg - i) ?? S.Zero);
  const generic = sqrtQuadraticDenom(a, b, c, coeffs, x);
  if (isNonZero(c) === true) return generic;
  const linear = sqrtLinear(p, a, b, n, x);
  return piecewise([generic, Ne(c, 0)], ...(linear instanceof Piecewise ? linear.pairs : [[linear, S.true] as const]));
}
