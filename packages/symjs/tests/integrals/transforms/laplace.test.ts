// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/integrals/transforms/laplace.ts.
// The Laplace transform. Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import {
  type Expr,
  Eq,
  SymFunction,
  Ge,
  Gt,
  Le,
  Lt,
  Matrix,
  Ne,
  Piecewise,
  Sym,
  UndefFn,
  abs,
  add,
  and,
  diff,
  exp,
  mapBottomUp,
  mul,
  parse,
  pow,
  sin,
  solve,
  sub,
  symbols,
  DiracDelta,
  Heaviside,
  laplaceTransform,
  symbol,
  LaplaceTransform,
  or,
} from '../../../src';
import {
  cosineTransform,
  fourierTransform,
  hankelTransform,
  inverseCosineTransform,
  inverseFourierTransform,
  inverseHankelTransform,
  inverseLaplaceTransform,
  inverseMellinTransform,
  inverseSineTransform,
  laplaceCorrespondence,
  laplaceInitialConds,
  mellinTransform,
  sineTransform,
} from '../../../src/integrals/transforms';
import { simplifyConds, laplaceDeepCollect } from '../../../src/integrals/transforms/laplace';

/** str of a result; tuples print like SymPy's. */
const show = (v: unknown): string => (Array.isArray(v) ? `(${v.map(show).join(', ')})` : String(v));

/**
 * Cases of SymPy's test_laplace.py and test_transforms.py whose results
 * symjs reproduces exactly: [function, args, hints, assumptions, str(result)].
 */
type Row = [string, (string | string[])[], Record<string, unknown>, Record<string, Record<string, boolean>>, string];
const ROWS: Row[] = [
  ["ILT", ["F(s)*exp(-a*s)", "s", "t"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}, "t": {"real": true}}, "InverseLaplaceTransform(F(s), s, -a + t, _None)"],
  ["ILT", ["2", "s", "t"], {}, {"t": {"real": true}}, "2*DiracDelta(t)"],
  ["ILT", ["1/s", "s", "t"], {}, {"t": {"real": true}}, "Heaviside(t)"],
  ["ILT", ["s**(-2)", "s", "t"], {}, {"t": {"real": true}}, "t*Heaviside(t)"],
  ["ILT", ["s**(-5)", "s", "t"], {}, {"t": {"real": true}}, "t**4*Heaviside(t)/24"],
  ["ILT", ["s**(-n)", "s", "t"], {}, {"n": {"real": true}, "t": {"real": true}}, "t**(n - 1)*Heaviside(t)/gamma(n)"],
  ["ILT", ["a/(a + s)", "s", "t"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}, "t": {"real": true}}, "a*exp(-a*t)*Heaviside(t)"],
  ["ILT", ["s/(a + s)", "s", "t"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}, "t": {"real": true}}, "-a*exp(-a*t)*Heaviside(t) + DiracDelta(t)"],
  ["ILT", ["b*s/(a + s)**2", "s", "t"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}, "b": {"negative": false, "nonzero": true, "positive": true, "real": true}, "t": {"real": true}}, "b*(-a*t*exp(-a*t)*Heaviside(t) + exp(-a*t)*Heaviside(t))"],
  ["ILT", ["1/(s*(a + s)**3)", "s", "t"], {"simplify": true}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}, "t": {"real": true}}, "(-a**2*t**2 - 2*a*t + 2*exp(a*t) - 2)*exp(-a*t)*Heaviside(t)/(2*a**3)"],
  ["ILT", ["(-a + s)**(-b)", "s", "t"], {}, {"b": {"negative": false, "nonzero": true, "positive": true, "real": true}, "a": {"negative": false, "nonzero": true, "positive": true, "real": true}, "t": {"real": true}}, "t**(b - 1)*exp(a*t)*Heaviside(t)/gamma(b)"],
  ["ILT", ["(a + s)**(-2)", "s", "t"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}, "t": {"real": true}}, "t*exp(-a*t)*Heaviside(t)"],
  ["ILT", ["(a + s)**(-5)", "s", "t"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}, "t": {"real": true}}, "t**4*exp(-a*t)*Heaviside(t)/24"],
  ["ILT", ["s**2/(s**2 + 1)", "s", "t"], {}, {"t": {"real": true}}, "-sin(t)*Heaviside(t) + DiracDelta(t)"],
  ["ILT", ["1 - 1/(s**2 + 1)", "s", "t"], {}, {"t": {"real": true}}, "-sin(t)*Heaviside(t) + DiracDelta(t)"],
  ["ILT", ["a/(a**2 + s**2)", "s", "t"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}, "t": {"real": true}}, "sin(a*t)*Heaviside(t)"],
  ["ILT", ["s/(a**2 + s**2)", "s", "t"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}, "t": {"real": true}}, "cos(a*t)*Heaviside(t)"],
  ["ILT", ["b/(b**2 + (a + s)**2)", "s", "t"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}, "b": {"negative": false, "nonzero": true, "positive": true, "real": true}, "t": {"real": true}}, "exp(-a*t)*sin(b*t)*Heaviside(t)"],
  ["ILT", ["b*s/(b**2 + (a + s)**2)", "s", "t"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}, "b": {"negative": false, "nonzero": true, "positive": true, "real": true}, "t": {"real": true}}, "b*(-a*exp(-a*t)*sin(b*t)/b + exp(-a*t)*cos(b*t))*Heaviside(t)"],
  ["ILT", ["1/(s**2*(s**2 + 1))", "s", "t"], {}, {"t": {"real": true}}, "t*Heaviside(t) - sin(t)*Heaviside(t)"],
  ["ILT", ["b/(-a**2 + s**2)", "s", "t"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}, "b": {"negative": false, "nonzero": true, "positive": true, "real": true}, "t": {"real": true}}, "b*(exp(a*t)*Heaviside(t)/(2*a) - exp(-a*t)*Heaviside(t)/(2*a))"],
  ["ILT", ["b/(s*(a + s))", "s", "t"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}, "b": {"negative": false, "nonzero": true, "positive": true, "real": true}, "t": {"real": true}}, "b*(Heaviside(t)/a - exp(-a*t)*Heaviside(t)/a)"],
  ["ILT", ["1/(a*s**2 + b*s + c)", "s", "t"], {}, {"b": {"negative": false, "nonzero": true, "positive": true, "real": true}, "c": {"negative": false, "nonzero": true, "positive": true, "real": true}, "a": {"negative": false, "nonzero": true, "positive": true, "real": true}, "t": {"real": true}}, "2*exp(-b*t/(2*a))*sin(t*sqrt(4*a*c - b**2)/(2*a))*Heaviside(t)/sqrt(4*a*c - b**2)"],
  ["ILT", ["1/(s*sqrt(k*s)*(-a + c*s))", "s", "t"], {}, {"k": {"real": true}, "a": {"negative": false, "nonzero": true, "positive": true, "real": true}, "c": {"negative": false, "nonzero": true, "positive": true, "real": true}, "t": {"real": true}}, "(-2*c*sqrt(t)/(sqrt(pi)*a) + c**(3/2)*exp(a*t/c)*erf(sqrt(a)*sqrt(t)/sqrt(c))/a**(3/2))*Heaviside(t)/(c*sqrt(k))"],
  ["ILT", ["1/(a + sqrt(c)*sqrt(s))", "s", "t"], {}, {"c": {"negative": false, "nonzero": true, "positive": true, "real": true}, "a": {"negative": false, "nonzero": true, "positive": true, "real": true}, "t": {"real": true}}, "(-a*exp(a**2*t/c)*erfc(a*sqrt(t)/sqrt(c))/c + 1/(sqrt(pi)*sqrt(c)*sqrt(t)))*Heaviside(t)"],
  ["ILT", ["a/(s*(a + b*sqrt(s)))", "s", "t"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}, "b": {"negative": false, "nonzero": true, "positive": true, "real": true}, "t": {"real": true}}, "(-exp(a**2*t/b**2)*erfc(a*sqrt(t)/b) + 1)*Heaviside(t)"],
  // SymPy 1.14 (and its test of Bateman 5.3 (6)) has erfc(sqrt(b)*sqrt(t)), which is wrong; see inverse-laplace.ts
  ["ILT", ["sqrt(s)*(a - b)/((sqrt(a) + sqrt(s))*(-b + s))", "s", "t"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}, "b": {"negative": false, "nonzero": true, "positive": true, "real": true}, "t": {"real": true}}, "(sqrt(a)*sqrt(b)*exp(b*t)*erf(sqrt(b)*sqrt(t)) + a*exp(a*t)*erfc(sqrt(a)*sqrt(t)) - b*exp(b*t))*Heaviside(t)"],
  ["ILT", ["a**2/(s**(3/2)*(a + sqrt(s)))", "s", "t"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}, "t": {"real": true}}, "(2*a*sqrt(t)/sqrt(pi) + exp(a**2*t)*erfc(a*sqrt(t)) - 1)*Heaviside(t)"],
  ["ILT", ["sqrt(b)*(a - b)/(sqrt(s)*(sqrt(a) + sqrt(s))*(-b + s))", "s", "t"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}, "b": {"negative": false, "nonzero": true, "positive": true, "real": true}, "t": {"real": true}}, "(sqrt(a)*exp(b*t)*erf(sqrt(b)*sqrt(t)) + sqrt(b)*exp(a*t)*erfc(sqrt(a)*sqrt(t)) - sqrt(b)*exp(b*t))*Heaviside(t)"],
  ["ILT", ["(sqrt(a) + sqrt(s))**(-2)", "s", "t"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}, "t": {"real": true}}, "(-2*sqrt(a)*sqrt(t)/sqrt(pi) + (-2*a*t + 1)*(erf(sqrt(a)*sqrt(t)) - 1)*exp(a*t) + 1)*Heaviside(t)"],
  ["ILT", ["1/(s*(sqrt(a) + sqrt(s))**2)", "s", "t"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}, "t": {"real": true}}, "((2*t - 1/a)*exp(a*t)*erfc(sqrt(a)*sqrt(t)) + 1/a - 2*sqrt(t)/(sqrt(pi)*sqrt(a)))*Heaviside(t)"],
  ["ILT", ["1/(sqrt(s)*(a + sqrt(s))**2)", "s", "t"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}, "t": {"real": true}}, "(-2*a*t*exp(a**2*t)*erfc(a*sqrt(t)) + 2*sqrt(t)/sqrt(pi))*Heaviside(t)"],
  ["ILT", ["(a + sqrt(s))**(-3)", "s", "t"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}, "t": {"real": true}}, "(-a*t*(2*a**2*t + 3)*exp(a**2*t)*erfc(a*sqrt(t)) + 2*sqrt(t)*(a**2*t + 1)/sqrt(pi))*Heaviside(t)"],
  ["ILT", ["sqrt(s)/(a + sqrt(s))**3", "s", "t"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}, "t": {"real": true}}, "(-2*a*sqrt(t)*(a**2*t + 2)/sqrt(pi) + (2*a**4*t**2 + 5*a**2*t + 1)*exp(a**2*t)*erfc(a*sqrt(t)))*Heaviside(t)"],
  ["ILT", ["1/(sqrt(s)*(a + sqrt(s))**3)", "s", "t"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}, "t": {"real": true}}, "(-2*a*t**(3/2)/sqrt(pi) + t*(2*a**2*t + 1)*exp(a**2*t)*erfc(a*sqrt(t)))*Heaviside(t)"],
  ["ILT", ["3/(a + sqrt(s))**4", "s", "t"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}, "t": {"real": true}}, "3*(-2*a**3*t**(5/2)*(2*a**2*t + 5)/(3*sqrt(pi)) + t*(4*a**4*t**2 + 12*a**2*t + 3)*exp(a**2*t)*erfc(a*sqrt(t))/3)*Heaviside(t)"],
  ["ILT", ["(-a + sqrt(s))/(s*(a + sqrt(s)))", "s", "t"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}, "t": {"real": true}}, "(2*exp(a**2*t)*erfc(a*sqrt(t)) - 1)*Heaviside(t)"],
  ["ILT", ["(-a + sqrt(s))**2/(s*(a + sqrt(s))**2)", "s", "t"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}, "t": {"real": true}}, "(8*a**2*t*exp(a**2*t)*erfc(a*sqrt(t)) - 8*a*sqrt(t)/sqrt(pi) + 1)*Heaviside(t)"],
  ["ILT", ["(-a + sqrt(s))**3/(s*(a + sqrt(s))**3)", "s", "t"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}, "t": {"real": true}}, "(-8*a*sqrt(t)*(2*a**2*t + 1)/sqrt(pi) + (16*a**4*t**2 + 16*a**2*t + 2)*exp(a**2*t)*erfc(a*sqrt(t)) - 1)*Heaviside(t)"],
  ["ILT", ["sqrt(a + s)/(b + s)", "s", "t"], {}, {"b": {"negative": false, "nonzero": true, "positive": true, "real": true}, "a": {"negative": false, "nonzero": true, "positive": true, "real": true}, "t": {"real": true}}, "(sqrt(a - b)*exp(-b*t)*erf(sqrt(t)*sqrt(a - b)) + exp(-a*t)/(sqrt(pi)*sqrt(t)))*Heaviside(t)"],
  ["ILT", ["(s**2*exp(2*s) + 4*exp(s) - 4)*exp(-2*s)/(s*(s**2 + 1))", "s", "t"], {}, {"t": {"real": true}}, "cos(t)*Heaviside(t) + 4*cos(t - 2)*Heaviside(t - 2) - 4*cos(t - 1)*Heaviside(t - 1) - 4*Heaviside(t - 2) + 4*Heaviside(t - 1)"],
  ["ILT", ["F(s)", "s", "t"], {}, {}, "InverseLaplaceTransform(F(s), s, t, _None)"],
  ["ILT", ["exp(-a*s)/s", "s", "t"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}}, "Heaviside(-a + t)"],
  ["ILT", ["exp(-a*s)/(b + s)", "s", "t"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}, "b": {"negative": false, "nonzero": true, "positive": true, "real": true}}, "exp(-b*(-a + t))*Heaviside(-a + t)"],
  ["ILT", ["(b + s)/(a**2 + (b + s)**2)", "s", "t"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}, "b": {"negative": false, "nonzero": true, "positive": true, "real": true}}, "exp(-b*t)*cos(a*t)*Heaviside(t)"],
  ["ILT", ["exp(-a*s)/s**b", "s", "t"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}, "b": {"negative": false, "nonzero": true, "positive": true, "real": true}}, "(-a + t)**(b - 1)*Heaviside(-a + t)/gamma(b)"],
  ["ILT", ["s**42*f(s)", "s", "t"], {}, {}, "Derivative(InverseLaplaceTransform(f(s), s, t, _None), (t, 42))"],
  ["ILT", ["cos(s)", "s", "t"], {}, {}, "InverseLaplaceTransform(cos(s), s, t, _None)"],
  ["ILT", ["5*s**3 + 3*s**2 + 2*s + 1", "s", "t"], {}, {}, "DiracDelta(t) + 2*DiracDelta(t, 1) + 3*DiracDelta(t, 2) + 5*DiracDelta(t, 3)"],
  ["ILT", ["exp(-3*s)*cos(sin(7)/2)", "s", "t"], {}, {}, "cos(sin(7)/2)*DiracDelta(t - 3)"],
  ["ILT", ["exp(2*s)", "s", "t"], {}, {}, "InverseLaplaceTransform(exp(2*s), s, t, _None)"],
  ["ILT", ["exp(r*s)", "s", "t"], {}, {"r": {"real": true}}, "InverseLaplaceTransform(exp(r*s), s, t, _None)"],
  ["ILT", ["s**2/(s**2 + cos(sin(7)/2)**2)", "s", "t"], {}, {}, "-sin(t*cos(sin(7)/2))*cos(sin(7)/2)*Heaviside(t) + DiracDelta(t)"],
  ["ILT", ["exp(r*s)", "s", "t"], {"noconds": false}, {"r": {"real": true}}, "(InverseLaplaceTransform(exp(r*s), s, t, _None), True)"],
  ["ILT", ["exp(s*z)", "s", "t"], {"noconds": false}, {"z": {"integer": false, "negative": false, "nonzero": false, "positive": false, "real": false}}, "(InverseLaplaceTransform(exp(s*z), s, t, _None), True)"],
  ["LT", ["a*t + t**(5/2) + t**2", "t", "s"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}}, "(a/s**2 + 2/s**3 + 15*sqrt(pi)/(8*s**(7/2)), 0, True)"],
  ["LT", ["b/(a + t)", "t", "s"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}, "b": {"negative": false, "nonzero": true, "positive": true, "real": true}}, "(-b*exp(-a*s)*Ei(-a*s), 0, True)"],
  ["LT", ["1/sqrt(a + t)", "t", "s"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}}, "(sqrt(pi)*sqrt(1/s)*exp(a*s)*erfc(sqrt(a)*sqrt(s)), 0, True)"],
  ["LT", ["sqrt(t)/(a + t)", "t", "s"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}}, "(-pi*sqrt(a)*exp(a*s)*erfc(sqrt(a)*sqrt(s)) + sqrt(pi)*sqrt(1/s), 0, True)"],
  ["LT", ["(a + t)**(-3/2)", "t", "s"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}}, "(-2*sqrt(pi)*sqrt(s)*exp(a*s)*erfc(sqrt(a)*sqrt(s)) + 2/sqrt(a), 0, True)"],
  ["LT", ["1/(a*sqrt(t) + t**1.5)", "t", "s"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}}, "(pi*sqrt(a)*exp(a*s)*erfc(sqrt(a)*sqrt(s)), 0, True)"],
  ["LT", ["(a + t)**b", "t", "s"], {}, {"b": {"negative": false, "nonzero": true, "positive": true, "real": true}, "a": {"negative": false, "nonzero": true, "positive": true, "real": true}}, "(s**(-b - 1)*exp(-a*s)*uppergamma(b + 1, a*s), 0, True)"],
  ["LT", ["t**5/(a + t)", "t", "s"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}}, "(120*expint(6, a*s)/s**5, 0, True)"],
  ["LT", ["exp(t)", "t", "s"], {}, {}, "(1/(s - 1), 1, True)"],
  ["LT", ["exp(2*t)", "t", "s"], {}, {}, "(1/(s - 2), 2, True)"],
  ["LT", ["exp(a*t)", "t", "s"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}}, "(1/(-a + s), a, True)"],
  ["LT", ["exp(a*(-b + t))", "t", "s"], {}, {"b": {"negative": false, "nonzero": true, "positive": true, "real": true}, "a": {"negative": false, "nonzero": true, "positive": true, "real": true}}, "(exp(-a*b)/(-a + s), a, True)"],
  ["LT", ["t*exp(-a*t)", "t", "s"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}}, "((a + s)**(-2), -a, True)"],
  ["LT", ["t*exp(-a*(-b + t))", "t", "s"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}, "b": {"negative": false, "nonzero": true, "positive": true, "real": true}}, "(exp(a*b)/(a + s)**2, -a, True)"],
  ["LT", ["b*t*exp(-a*t)", "t", "s"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}, "b": {"negative": false, "nonzero": true, "positive": true, "real": true}}, "(b/(a + s)**2, -a, True)"],
  ["LT", ["exp(-a*exp(-t))", "t", "s"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}}, "(lowergamma(s, a)/a**s, 0, True)"],
  ["LT", ["exp(-a*exp(t))", "t", "s"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}}, "(a**s*uppergamma(-s, a), 0, True)"],
  ["LT", ["t**(7/4)*exp(-8*t)/gamma(11/4)", "t", "s"], {}, {}, "((s + 8)**(-11/4), -8, True)"],
  ["LT", ["t**(3/2)*exp(-8*t)", "t", "s"], {}, {}, "(3*sqrt(pi)/(4*(s + 8)**(5/2)), -8, True)"],
  ["LT", ["t**a*exp(-a*t)", "t", "s"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}}, "((a + s)**(-a - 1)*gamma(a + 1), -a, True)"],
  ["LT", ["b*exp(-a*t**2)", "t", "s"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}, "b": {"negative": false, "nonzero": true, "positive": true, "real": true}}, "(sqrt(pi)*b*exp(s**2/(4*a))*erfc(s/(2*sqrt(a)))/(2*sqrt(a)), 0, True)"],
  ["LT", ["exp(-2*t**2)", "t", "s"], {}, {}, "(sqrt(2)*sqrt(pi)*exp(s**2/8)*erfc(sqrt(2)*s/4)/4, 0, True)"],
  ["LT", ["b*exp(2*t**2)", "t", "s"], {}, {"b": {"negative": false, "nonzero": true, "positive": true, "real": true}}, "(b*LaplaceTransform(exp(2*t**2), t, s), -oo, True)"],
  ["LT", ["t*exp(-a*t**2)", "t", "s"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}}, "(1/(2*a) - s*erfc(s/(2*sqrt(a)))/(4*sqrt(pi)*a**(3/2)), 0, True)"],
  ["LT", ["exp(-a/t)", "t", "s"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}}, "(2*sqrt(a)*sqrt(1/s)*besselk(1, 2*sqrt(a)*sqrt(s)), 0, True)"],
  ["LT", ["sqrt(t)*exp(-a/t)", "t", "s"], {"simplify": true}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}}, "(sqrt(pi)*(sqrt(a)*sqrt(s) + 1/2)*sqrt(s**(-3))*exp(-2*sqrt(a)*sqrt(s)), 0, True)"],
  ["LT", ["exp(-a/t)/sqrt(t)", "t", "s"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}}, "(sqrt(pi)*sqrt(1/s)*exp(-2*sqrt(a)*sqrt(s)), 0, True)"],
  ["LT", ["exp(-a/t)/t**(3/2)", "t", "s"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}}, "(sqrt(pi)*exp(-2*sqrt(a)*sqrt(s))/sqrt(a), 0, True)"],
  ["LT", ["t**4*exp(-2/t)", "t", "s"], {}, {}, "(8*sqrt(2)*(1/s)**(5/2)*besselk(5, 2*sqrt(2)*sqrt(s)), 0, True)"],
  ["LT", ["sinh(a*t)", "t", "s"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}}, "(a/(-a**2 + s**2), a, True)"],
  ["LT", ["b*sinh(a*t)**2", "t", "s"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}, "b": {"negative": false, "nonzero": true, "positive": true, "real": true}}, "(2*a**2*b/(-4*a**2*s + s**3), 2*a, True)"],
  ["LT", ["cosh(2*t)", "t", "s"], {}, {}, "(s/(s**2 - 4), 2, True)"],
  ["LT", ["cosh(a*t)", "t", "s"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}}, "(s/(-a**2 + s**2), a, True)"],
  ["LT", ["sinh(x + 3)", "x", "s"], {"simplify": true}, {}, "((s*sinh(3) + cosh(3))/(s**2 - 1), 1, True)"],
  ["LT", ["42*sin(t*w + x)**2", "t", "s"], {}, {}, "(42*(-s*cos(2*x)/2 + w*sin(2*x))/(s**2 + 4*w**2) + 21/s, 2*Abs(im(w)), True)"],
  ["LT", ["sinh(a*t)*cosh(a*t)", "t", "s"], {"simplify": true}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}}, "(a/(-4*a**2 + s**2), 2*a, True)"],
  ["LT", ["sinh(a*t)/t", "t", "s"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}}, "(log((a + s)/(-a + s))/2, a, True)"],
  ["LT", ["sinh(a*t)/t**(3/2)", "t", "s"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}}, "(-sqrt(pi)*(sqrt(-a + s) - sqrt(a + s)), a, True)"],
  ["LT", ["t**(3/7)*cosh(a*t)", "t", "s"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}}, "(((a + s)**(-10/7) + (-a + s)**(-10/7))*gamma(10/7)/2, a, True)"],
  ["LT", ["log(a*t + 1)", "t", "s"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}}, "(-exp(s/a)*Ei(-s/a)/s, 0, True)"],
  ["LT", ["log(a + t)", "t", "s"], {"simplify": true}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}}, "((s*log(a) - exp(s/a)*Ei(-s/a))/s**2, 0, True)"],
  ["LT", ["t**3*log(t)", "t", "s"], {"noconds": true, "simplify": true}, {}, "(-6*log(s) - 6*EulerGamma + 11)/s**4"],
  ["LT", ["sin(a*t)", "t", "s"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}}, "(a/(a**2 + s**2), 0, True)"],
  ["LT", ["Abs(sin(a*t))", "t", "s"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}}, "(a*coth(pi*s/(2*a))/(a**2 + s**2), 0, True)"],
  ["LT", ["sin(a*t)/t", "t", "s"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}}, "(atan(a/s), 0, True)"],
  ["LT", ["sin(a*t)**2/t", "t", "s"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}}, "(log(4*a**2/s**2 + 1)/4, 0, True)"],
  ["LT", ["sin(a*t)**2/t**2", "t", "s"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}}, "(a*atan(2*a/s) - s*log(4*a**2/s**2 + 1)/4, 0, True)"],
  ["LT", ["cos(a*t)", "t", "s"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}}, "(s/(a**2 + s**2), 0, True)"],
  ["LT", ["cos(a*t)**2", "t", "s"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}}, "((2*a**2 + s**2)/(s*(4*a**2 + s**2)), 0, True)"],
  ["LT", ["sin(a*t)*sin(b*t)", "t", "s"], {}, {"b": {"negative": false, "nonzero": true, "positive": true, "real": true}, "a": {"negative": false, "nonzero": true, "positive": true, "real": true}}, "(2*a*b*s/((s**2 + (a - b)**2)*(s**2 + (a + b)**2)), 0, True)"],
  ["LT", ["sin(b*t)*cos(a*t)", "t", "s"], {}, {"b": {"negative": false, "nonzero": true, "positive": true, "real": true}, "a": {"negative": false, "nonzero": true, "positive": true, "real": true}}, "(b*(-a**2 + b**2 + s**2)/((s**2 + (a - b)**2)*(s**2 + (a + b)**2)), 0, True)"],
  ["LT", ["cos(a*t)*cos(b*t)", "t", "s"], {}, {"b": {"negative": false, "nonzero": true, "positive": true, "real": true}, "a": {"negative": false, "nonzero": true, "positive": true, "real": true}}, "(s*(a**2 + b**2 + s**2)/((s**2 + (a - b)**2)*(s**2 + (a + b)**2)), 0, True)"],
  ["LT", ["-a*t*cos(a*t) + sin(a*t)", "t", "s"], {"simplify": true}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}}, "(2*a**3/(a**4 + 2*a**2*s**2 + s**4), 0, True)"],
  ["LT", ["c*exp(-b*t)*sin(a*t)", "t", "s"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}, "c": {"negative": false, "nonzero": true, "positive": true, "real": true}, "b": {"negative": false, "nonzero": true, "positive": true, "real": true}}, "(a*c/(a**2 + (b + s)**2), -b, True)"],
  ["LT", ["c*exp(-b*t)*cos(a*t)", "t", "s"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}, "c": {"negative": false, "nonzero": true, "positive": true, "real": true}, "b": {"negative": false, "nonzero": true, "positive": true, "real": true}}, "(c*(b + s)/(a**2 + (b + s)**2), -b, True)"],
  ["LT", ["cos(x + 3)", "x", "s"], {"simplify": true}, {}, "((s*cos(3) - sin(3))/(s**2 + 1), 0, True)"],
  ["LT", ["erf(a*t)", "t", "s"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}}, "(exp(s**2/(4*a**2))*erfc(s/(2*a))/s, 0, True)"],
  ["LT", ["besselj(0, a*t)", "t", "s"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}}, "(1/sqrt(a**2 + s**2), 0, True)"],
  ["LT", ["besselj(2, a*t)", "t", "s"], {"simplify": true}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}}, "(a**2/(sqrt(a**2 + s**2)*(s + sqrt(a**2 + s**2))**2), 0, True)"],
  ["LT", ["t*besselj(0, a*t)", "t", "s"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}}, "(s/(a**2 + s**2)**(3/2), 0, True)"],
  ["LT", ["t*besselj(1, a*t)", "t", "s"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}}, "(a/(a**2 + s**2)**(3/2), 0, True)"],
  ["LT", ["t**2*besselj(2, a*t)", "t", "s"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}}, "(3*a**2/(a**2 + s**2)**(5/2), 0, True)"],
  ["LT", ["besselj(0, a*sqrt(b*t + t**2))", "t", "s"], {"simplify": true}, {"b": {"negative": false, "nonzero": true, "positive": true, "real": true}, "a": {"negative": false, "nonzero": true, "positive": true, "real": true}}, "(exp(b*(s - sqrt(a**2 + s**2)))/sqrt(a**2 + s**2), 0, True)"],
  ["LT", ["besseli(0, a*t)", "t", "s"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}}, "(1/sqrt(-a**2 + s**2), a, True)"],
  ["LT", ["besseli(2, a*t)", "t", "s"], {"simplify": true}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}}, "(a**2/(sqrt(-a**2 + s**2)*(s + sqrt(-a**2 + s**2))**2), a, True)"],
  ["LT", ["t*besseli(0, a*t)", "t", "s"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}}, "(s/(-a**2 + s**2)**(3/2), a, True)"],
  ["LT", ["t*besseli(1, a*t)", "t", "s"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}}, "(a/(-a**2 + s**2)**(3/2), a, True)"],
  ["LT", ["t**2*besseli(2, a*t)", "t", "s"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}}, "(3*a**2/(-a**2 + s**2)**(5/2), a, True)"],
  ["LT", ["bessely(0, a*t)", "t", "s"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}}, "(-2*asinh(s/a)/(pi*sqrt(a**2 + s**2)), 0, True)"],
  ["LT", ["besselk(0, a*t)", "t", "s"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}}, "(log((s + sqrt(-a**2 + s**2))/a)/sqrt(-a**2 + s**2), -a, True)"],
  ["LT", ["cos(t - 1)*Heaviside(t - 1)", "t", "s"], {}, {}, "(s*exp(-s)/(s**2 + 1), 0, True)"],
  ["LT", ["a*f(t)", "t", "w"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}}, "(a*LaplaceTransform(f(t), t, w), -oo, True)"],
  ["LT", ["a*f(t + 1)*Heaviside(t + 1)", "t", "s"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}}, "(a*LaplaceTransform(f(t + 1), t, s), -oo, True)"],
  ["LT", ["b*f(t/a)", "t", "s"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}, "b": {"negative": false, "nonzero": true, "positive": true, "real": true}}, "(a*b*LaplaceTransform(f(t), t, a*s), -oo, True)"],
  ["LT", ["exp(-t*f(x))", "t", "s"], {}, {}, "(1/(s + f(x)), -re(f(x)), True)"],
  ["LT", ["f(t)*exp(-a*t)", "t", "s"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}}, "(LaplaceTransform(f(t), t, a + s), -oo, True)"],
  ["LT", ["f(t)*sinh(a*t)", "t", "s"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}}, "(LaplaceTransform(f(t), t, -a + s)/2 - LaplaceTransform(f(t), t, a + s)/2, -oo, True)"],
  ["LT", ["f(t)*cosh(a*t)", "t", "s"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}}, "(LaplaceTransform(f(t), t, -a + s)/2 + LaplaceTransform(f(t), t, a + s)/2, -oo, True)"],
  ["LT", ["f(t)*sin(a*t)", "t", "s"], {"simplify": true}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}}, "(I*(-LaplaceTransform(f(t), t, -I*a + s) + LaplaceTransform(f(t), t, I*a + s))/2, -oo, True)"],
  ["LT", ["sin(f(t))", "t", "s"], {}, {}, "(LaplaceTransform(sin(f(t)), t, s), -oo, True)"],
  ["LT", ["f(t)*cos(a*t)", "t", "s"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}}, "(LaplaceTransform(f(t), t, -I*a + s)/2 + LaplaceTransform(f(t), t, I*a + s)/2, -oo, True)"],
  ["LT", ["t**2*exp(-t**2)", "t", "s"], {}, {}, "(sqrt(pi)*s**2*exp(s**2/4)*erfc(s/2)/8 - s/4 + sqrt(pi)*exp(s**2/4)*erfc(s/2)/4, 0, True)"],
  ["LT", ["(a*t**2 + b*t + c)*f(t)", "t", "s"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}, "c": {"negative": false, "nonzero": true, "positive": true, "real": true}, "b": {"negative": false, "nonzero": true, "positive": true, "real": true}}, "(a*Derivative(LaplaceTransform(f(t), t, s), (s, 2)) - b*Derivative(LaplaceTransform(f(t), t, s), s) + c*LaplaceTransform(f(t), t, s), -oo, True)"],
  ["ILT", ["1/s - exp(-s)/s", "s", "t"], {}, {}, "Heaviside(t) - Heaviside(t - 1)"],
  ["ILT", ["(exp(2*s) - 2*exp(s) + 1)*exp(-2*s)/s**2", "s", "t"], {}, {}, "t*Heaviside(t) + (t - 2)*Heaviside(t - 2) - 2*(t - 1)*Heaviside(t - 1)"],
  ["ILT", ["exp(-1)*exp(-s)/(s + 1) + 1/s - exp(-s)/s", "s", "t"], {}, {}, "exp(-1)*exp(1 - t)*Heaviside(t - 1) + Heaviside(t) - Heaviside(t - 1)"],
  ["LT", ["Heaviside(t)*besseli(0, sqrt(b)*t/sqrt(a))/sqrt(a)", "t", "s"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}, "b": {"negative": false, "nonzero": true, "positive": true, "real": true}}, "(1/(sqrt(a)*sqrt(s**2 - b/a)), sqrt(b)/sqrt(a), True)"],
  ["LT", ["Derivative(f(t), t)", "t", "s"], {"noconds": true}, {}, "s*LaplaceTransform(f(t), t, s) - f(0)"],
  ["LT", ["10*Derivative(f(t), t)", "t", "s"], {"noconds": true}, {}, "10*s*LaplaceTransform(f(t), t, s) - 10*f(0)"],
  ["LT", ["a*f(b*t) + g(c*t)", "t", "s"], {"noconds": true}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}, "c": {"negative": false, "nonzero": true, "positive": true, "real": true}, "b": {"negative": false, "nonzero": true, "positive": true, "real": true}}, "a*LaplaceTransform(f(t), t, s/b)/b + LaplaceTransform(g(t), t, s/c)/c"],
  ["LT", ["f(t)*g(t)", "t", "s"], {"noconds": true}, {}, "LaplaceTransform(f(t)*g(t), t, s)"],
  ["LT", ["b*f(a*t)", "t", "s"], {"noconds": true}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}, "b": {"negative": false, "nonzero": true, "positive": true, "real": true}}, "b*LaplaceTransform(f(t), t, s/a)/a"],
  ["LT", ["3*exp(t)*Heaviside(t)", "t", "s"], {}, {}, "(3/(s - 1), 1, True)"],
  ["LT", ["2*sin(t)*Heaviside(t)", "t", "s"], {"simplify": true}, {}, "(2/(s**2 + 1), 0, True)"],
  ["LT", ["(-Heaviside(t - 2) + Heaviside(t - 0.25))*sin(pi*(4*t - 4))*DiracDelta(t - 1)/(t - 1)", "t", "s"], {}, {}, "(4*pi*exp(-s), -oo, True)"],
  ["LT", ["(-a + t)**b*exp(-c*(-a + t))*Heaviside(-a + t)", "t", "s"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}, "c": {"negative": false, "nonzero": true, "positive": true, "real": true}, "b": {"negative": false, "nonzero": true, "positive": true, "real": true}}, "((c + s)**(-b - 1)*exp(-a*s)*gamma(b + 1), -c, True)"],
  ["LT", ["DiracDelta(t)", "t", "s"], {}, {}, "(1, -oo, True)"],
  ["LT", ["DiracDelta(a*t)", "t", "s"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}}, "(1/a, -oo, True)"],
  ["LT", ["DiracDelta(t/42)", "t", "s"], {}, {}, "(42, -oo, True)"],
  ["LT", ["DiracDelta(t + 42)", "t", "s"], {}, {}, "(0, -oo, True)"],
  ["LT", ["DiracDelta(t) + DiracDelta(t - 42)", "t", "s"], {}, {}, "(1 + exp(-42*s), -oo, True)"],
  ["LT", ["-a*exp(-a*t) + DiracDelta(t)", "t", "s"], {"simplify": true}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}}, "(s/(a + s), -a, True)"],
  ["LT", ["(DiracDelta(t) + DiracDelta(t - 42))*exp(-t)", "t", "s"], {"simplify": true}, {}, "(exp(-42*s - 42) + 1, -oo, True)"],
  ["LT", ["f(t)*DiracDelta(t - 42)", "t", "s"], {}, {}, "(f(42)*exp(-42*s), -oo, True)"],
  ["LT", ["f(t)*DiracDelta(-a + b*t)", "t", "s"], {}, {"b": {"negative": false, "nonzero": true, "positive": true, "real": true}, "a": {"negative": false, "nonzero": true, "positive": true, "real": true}}, "(f(a/b)*exp(-a*s/b)/b, -oo, True)"],
  ["LT", ["f(t)*DiracDelta(a + b*t)", "t", "s"], {}, {"b": {"negative": false, "nonzero": true, "positive": true, "real": true}, "a": {"negative": false, "nonzero": true, "positive": true, "real": true}}, "(0, -oo, True)"],
  ["LT", ["SingularityFunction(t, a, x)", "t", "s"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}}, "(LaplaceTransform(SingularityFunction(t, a, x), t, s), -oo, True)"],
  ["LT", ["DiracDelta(t**2)", "t", "s"], {"noconds": true}, {}, "LaplaceTransform(DiracDelta(t**2), t, s)"],
  ["LT", ["DiracDelta(t**2 - 1)", "t", "s"], {}, {}, "(exp(-s)/2, -oo, True)"],
  // SymPy 1.14: (1 - exp(-s), -oo, True); delta(t*(1 - t)) = delta(t) + delta(t - 1), each divided by |d/dt t*(1 - t)| = 1
  ["LT", ["DiracDelta(t*(1 - t))", "t", "s"], {}, {}, "(1 + exp(-s), -oo, True)"],
  ["LT", ["(DiracDelta(t) + 1)*(DiracDelta(t - 1) + 1)", "t", "s"], {}, {}, "(LaplaceTransform(DiracDelta(t)*DiracDelta(t - 1), t, s) + 1 + exp(-s) + 1/s, 0, True)"],
  ["LT", ["DiracDelta(2*t - 2*exp(a))", "t", "s"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}}, "(exp(-s*exp(a))/2, -oo, True)"],
  ["LT", ["DiracDelta(-2*t + 2*exp(a))", "t", "s"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}}, "(exp(-s*exp(a))/2, -oo, True)"],
  ["LT", ["Heaviside(t)", "t", "s"], {}, {}, "(1/s, 0, True)"],
  ["LT", ["Heaviside(-a + t)", "t", "s"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}}, "(exp(-a*s)/s, 0, True)"],
  ["LT", ["Heaviside(t - 1)", "t", "s"], {}, {}, "(exp(-s)/s, 0, True)"],
  ["LT", ["Heaviside(2*t - 4)", "t", "s"], {}, {}, "(exp(-2*s)/s, 0, True)"],
  ["LT", ["Heaviside(2*t + 4)", "t", "s"], {}, {}, "(1/s, 0, True)"],
  ["LT", ["g(t)*Heaviside(t - w)", "t", "s"], {}, {}, "(LaplaceTransform(g(t)*Heaviside(t - w), t, s), -oo, True)"],
  ["LT", ["g(t)*Heaviside(a + t)", "t", "s"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}}, "(LaplaceTransform(g(t), t, s), -oo, True)"],
  ["LT", ["g(t)*Heaviside(-a - t)", "t", "s"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}}, "(0, 0, True)"],
  ["mellin_transform", ["f(x)", "x", "s"], {}, {}, "MellinTransform(f(x), x, s)"],
  ["fourier_transform", ["f(x)", "x", "s"], {}, {}, "FourierTransform(f(x), x, s)"],
  ["inverse_mellin_transform", ["f(s)", "s", "x", ["a", "b"]], {}, {}, "InverseMellinTransform(f(s), s, x, a, b)"],
  ["inverse_fourier_transform", ["f(s)", "s", "x"], {}, {}, "InverseFourierTransform(f(s), s, x)"],
  ["cosine_transform", ["f(t)", "t", "w"], {}, {}, "CosineTransform(f(t), t, w)"],
  ["inverse_cosine_transform", ["f(w)", "w", "t"], {}, {}, "InverseCosineTransform(f(w), w, t)"],
  ["cosine_transform", ["1/sqrt(t)", "t", "w"], {}, {}, "1/sqrt(w)"],
  ["inverse_cosine_transform", ["1/sqrt(w)", "w", "t"], {}, {}, "1/sqrt(t)"],
  ["cosine_transform", ["1/(a**2 + t**2)", "t", "w"], {}, {}, "sqrt(2)*sqrt(pi)*exp(-a*w)/(2*a)"],
  ["cosine_transform", ["t**(-a)", "t", "w"], {}, {}, "2**(1/2 - a)*w**(a - 1)*gamma(1/2 - a/2)/gamma(a/2)"],
  ["inverse_cosine_transform", ["2**(1/2 - a)*w**(a - 1)*gamma(1/2 - a/2)/gamma(a/2)", "w", "t"], {}, {}, "t**(-a)"],
  ["cosine_transform", ["exp(-a*t)", "t", "w"], {}, {}, "sqrt(2)*a/(sqrt(pi)*(a**2 + w**2))"],
  ["inverse_cosine_transform", ["sqrt(2)*a/(sqrt(pi)*(a**2 + w**2))", "w", "t"], {}, {}, "exp(-a*t)"],
  ["cosine_transform", ["exp(-a*sqrt(t))*cos(a*sqrt(t))", "t", "w"], {}, {}, "a*exp(-a**2/(2*w))/(2*w**(3/2))"],
  ["fourier_transform", ["f(x)", "x", "k"], {}, {"k": {"real": true}}, "FourierTransform(f(x), x, k)"],
  ["inverse_fourier_transform", ["f(k)", "k", "x"], {}, {"k": {"real": true}}, "InverseFourierTransform(f(k), k, x)"],
  ["fourier_transform", ["exp(-a*x)*Heaviside(x)", "x", "k"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}, "k": {"real": true}}, "1/(a + 2*I*pi*k)"],
  ["fourier_transform", ["x*exp(-a*x)*Heaviside(x)", "x", "k"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}, "k": {"real": true}}, "(a + 2*I*pi*k)**(-2)"],
  ["fourier_transform", ["exp(-a*x**2)", "x", "k"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}, "k": {"real": true}}, "sqrt(pi)*exp(-pi**2*k**2/a)/sqrt(a)"],
  ["inverse_fourier_transform", ["sqrt(pi)*exp(-pi**2*k**2/a)/sqrt(a)", "k", "x"], {}, {"k": {"real": true}, "a": {"negative": false, "nonzero": true, "positive": true, "real": true}}, "exp(-a*x**2)"],
  ["fourier_transform", ["exp(-a*Abs(x))", "x", "k"], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}, "k": {"real": true}}, "2*a/(a**2 + 4*pi**2*k**2)"],
  ["mellin_transform", ["a*f(x)", "x", "s"], {}, {}, "a*MellinTransform(f(x), x, s)"],
  ["hankel_transform", ["1/r", "r", "k", "0"], {}, {}, "1/k"],
  ["inverse_hankel_transform", ["1/k", "k", "r", "0"], {}, {}, "1/r"],
  ["inverse_hankel_transform", ["2**(1 - m)*k**(m - 2)*gamma(1 - m/2)/gamma(m/2)", "k", "r", "0"], {}, {}, "r**(-m)"],
  ["hankel_transform", ["r**(-m)", "r", "k", "nu"], {}, {}, "2*k**(m - 2)*gamma(-m/2 + nu/2 + 1)/(2**m*gamma(m/2 + nu/2))"],
  ["inverse_hankel_transform", ["2**(1 - m)*k**(m - 2)*gamma(-m/2 + nu/2 + 1)/gamma(m/2 + nu/2)", "k", "r", "nu"], {}, {}, "r**(-m)"],
  ["inverse_hankel_transform", ["2**(nu + 1)*a*k**(-nu - 3)*(a**2/k**2 + 1)**(-nu - 3/2)*gamma(nu + 3/2)/sqrt(pi)", "k", "r", "nu"], {}, {}, "r**nu*exp(-a*r)"],
  ["inverse_mellin_transform", ["gamma(s)", "s", "x", ["0", "oo"]], {}, {}, "exp(-x)"],
  ["inverse_mellin_transform", ["gamma(-s)", "s", "x", ["-oo", "0"]], {}, {}, "exp(-1/x)"],
  ["inverse_mellin_transform", ["s/(2*s**2 - 2)", "s", "x", ["2", "oo"]], {}, {}, "(x**2/2 + 1/2)*Heaviside(1 - x)/(2*x)"],
  ["inverse_mellin_transform", ["1/(s**2 - 1)", "s", "x", ["-1", "None"]], {}, {}, "-x*Heaviside(1 - x)/2 - Heaviside(x - 1)/(2*x)"],
  ["inverse_mellin_transform", ["1/(s**2 - 1)", "s", "x", ["None", "1"]], {}, {}, "-x*Heaviside(1 - x)/2 - Heaviside(x - 1)/(2*x)"],
  ["inverse_mellin_transform", ["gamma(s) + gamma(s - 1)", "s", "x", ["1", "oo"]], {}, {}, "(x + 1)*exp(-x)/x"],
  ["inverse_mellin_transform", ["factorial(s/a)/(b**(s/a)*s)", "s", "x", ["0", "oo"]], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}, "b": {"negative": false, "nonzero": true, "positive": true, "real": true}}, "exp(-b*x**a)"],
  ["inverse_mellin_transform", ["factorial(a/b + s/b)/(a + s)", "s", "x", ["-a", "oo"]], {}, {"a": {"negative": false, "nonzero": true, "positive": true, "real": true}, "b": {"negative": false, "nonzero": true, "positive": true, "real": true}}, "x**a*exp(-x**b)"],
  ["inverse_mellin_transform", ["-1/(nu + s)", "s", "x", ["-oo", "None"]], {}, {"nu": {"real": true}}, "x**nu*Heaviside(x - 1)"],
  ["inverse_mellin_transform", ["1/(nu + s)", "s", "x", ["None", "oo"]], {}, {"nu": {"real": true}}, "x**nu*Heaviside(1 - x)"],
  ["inverse_mellin_transform", ["gamma(beta)*gamma(s)/gamma(beta + s)", "s", "x", ["0", "oo"]], {}, {}, "(1 - x)**(beta - 1)*Heaviside(1 - x)"],
  ["inverse_mellin_transform", ["gamma(beta)*gamma(-beta - s + 1)/gamma(1 - s)", "s", "x", ["-oo", "None"]], {}, {}, "x**(beta - 1)*(1 - 1/x)**(beta - 1)*Heaviside(x - 1)"],
  ["inverse_mellin_transform", ["gamma(s)*gamma(rho - s)/gamma(rho)", "s", "x", ["0", "None"]], {}, {}, "(x + 1)**(-rho)"],
  ["inverse_mellin_transform", ["24/s**5", "s", "x", ["0", "oo"]], {}, {}, "log(x)**4*Heaviside(1 - x)"],
  ["inverse_mellin_transform", ["pi/cos(pi*s)", "s", "x", ["0", "1/2"]], {}, {}, "sqrt(x)/(x + 1)"],
  ["fourier_transform", ["exp(x)", "x", "y"], {}, {"x": {"real": true}, "y": {"real": true}}, "FourierTransform(exp(x), x, y)"],
  ["mellin_transform", ["1/(1 - x)", "x", "s"], {}, {}, "MellinTransform(1/(1 - x), x, s)"],
  ["mellin_transform", ["x**nu*Heaviside(x - 1)", "x", "s"], {}, {}, "(-1/(nu + s), (-oo, -re(nu)), True)"],
  ["mellin_transform", ["x**nu*Heaviside(1 - x)", "x", "s"], {}, {}, "(1/(nu + s), (-re(nu), oo), True)"],
  ["mellin_transform", ["(1 - x)**(beta - 1)*Heaviside(1 - x)", "x", "s"], {}, {}, "(gamma(beta)*gamma(s)/gamma(beta + s), (0, oo), re(beta) > 0)"],
  ["mellin_transform", ["(x - 1)**(beta - 1)*Heaviside(x - 1)", "x", "s"], {}, {}, "(gamma(beta)*gamma(-beta - s + 1)/gamma(1 - s), (-oo, 1 - re(beta)), re(beta) > 0)"],
  ["mellin_transform", ["(x + 1)**(-rho)", "x", "s"], {}, {}, "(gamma(s)*gamma(rho - s)/gamma(rho), (0, re(rho)), True)"],
  ["mellin_transform", ["exp(-x)", "x", "s"], {}, {}, "(gamma(s), (0, oo), True)"],
  ["mellin_transform", ["exp(-1/x)", "x", "s"], {}, {}, "(gamma(-s), (-oo, 0), True)"],
  ["sine_transform", ["f(t)", "t", "w"], {}, {}, "SineTransform(f(t), t, w)"],
  ["inverse_sine_transform", ["f(w)", "w", "t"], {}, {}, "InverseSineTransform(f(w), w, t)"],
  ["sine_transform", ["1/sqrt(t)", "t", "w"], {}, {}, "1/sqrt(w)"],
  ["inverse_sine_transform", ["1/sqrt(w)", "w", "t"], {}, {}, "1/sqrt(t)"],
  ["sine_transform", ["t**(-3/2)", "t", "w"], {}, {}, "2*sqrt(w)"],
  ["sine_transform", ["t**(-a)", "t", "w"], {}, {}, "2**(1/2 - a)*w**(a - 1)*gamma(1 - a/2)/gamma(a/2 + 1/2)"],
  ["inverse_sine_transform", ["2**(1/2 - a)*w**(a - 1)*gamma(1 - a/2)/gamma(a/2 + 1/2)", "w", "t"], {}, {}, "t**(-a)"],
  ["sine_transform", ["exp(-a*t)", "t", "w"], {}, {}, "sqrt(2)*w/(sqrt(pi)*(a**2 + w**2))"],
  ["inverse_sine_transform", ["sqrt(2)*w/(sqrt(pi)*(a**2 + w**2))", "w", "t"], {}, {}, "exp(-a*t)"],
  ["sine_transform", ["t*exp(-a*t**2)", "t", "w"], {}, {}, "sqrt(2)*w*exp(-w**2/(4*a))/(4*a**(3/2))"],
  ["inverse_sine_transform", ["sqrt(2)*w*exp(-w**2/(4*a))/(4*a**(3/2))", "w", "t"], {}, {}, "t*exp(-a*t**2)"],
];

const fixFunctions = (e: Expr): Expr =>
  mapBottomUp(e, (x) => {
    if (x instanceof UndefFn && x.name === 'Heaviside') return Heaviside(x.args[0]!, x.args[1]);
    if (x instanceof UndefFn && x.name === 'DiracDelta') return DiracDelta(x.args[0]!, x.args[1]);
    return x;
  });

const FNS: Record<string, (...a: never[]) => unknown> = {
  LT: laplaceTransform,
  ILT: inverseLaplaceTransform,
  mellin_transform: mellinTransform,
  inverse_mellin_transform: inverseMellinTransform,
  fourier_transform: fourierTransform,
  inverse_fourier_transform: inverseFourierTransform,
  sine_transform: sineTransform,
  inverse_sine_transform: inverseSineTransform,
  cosine_transform: cosineTransform,
  inverse_cosine_transform: inverseCosineTransform,
  hankel_transform: hankelTransform,
  inverse_hankel_transform: inverseHankelTransform,
};

describe('sympy.integrals.transforms doctests', () => {
  it('IntegralTransform: LaplaceTransform._name', () => {
    expect(LaplaceTransform.transformName).toBe('Laplace');
  });

});

describe('sympy.integrals.laplace doctests', () => {
  it('_simplifyconds', () => {
    const x = new Sym('x');
    expect(String(simplifyConds(Lt(abs(pow(x, 2)), 1), x, 1))).toBe('False');
    expect(String(simplifyConds(Lt(abs(pow(x, 2)), 1), x, 2))).toBe('False');
    // symjs evaluates Abs(x**2) to Abs(x)**2 where SymPy keeps Abs(x**2)
    expect(String(simplifyConds(Lt(abs(pow(x, 2)), 1), x, 0))).toBe('Abs(x)**2 < 1');
    expect(String(simplifyConds(Lt(abs(pow(x, -2)), 1), x, 1))).toBe('True');
    expect(String(simplifyConds(Lt(1, abs(x)), x, 1))).toBe('True');
    expect(String(simplifyConds(Lt(1, abs(pow(x, -1))), x, 1))).toBe('False');
    expect(String(simplifyConds(Ne(1, pow(x, 3)), x, 1))).toBe('True');
    expect(String(simplifyConds(Ne(1, pow(x, 3)), x, 2))).toBe('True');
    expect(String(simplifyConds(Ne(1, pow(x, 3)), x, 0))).toBe('Ne(1, x**3)');
  });

  it('laplace_correspondence', () => {
    const [t, s] = symbols('t s');
    const [y, Y, z, Z] = [SymFunction('y'), SymFunction('Y'), SymFunction('z'), SymFunction('Z')];
    const f = laplaceTransform(add(diff(y(t), t), z(t)), t, s, { noconds: true });
    expect(String(laplaceCorrespondence(f, new Map([[y, Y], [z, Z]])))).toBe('s*Y(s) + Z(s) - y(0)');
    const g = inverseLaplaceTransform(Y(s), s, t);
    expect(String(laplaceCorrespondence(g, new Map([[y, Y]])))).toBe('y(t)');
  });

  it('laplace_initial_conds', () => {
    const [t, s] = symbols('t s');
    const [y, Y] = [SymFunction('y'), SymFunction('Y')];
    const f = laplaceTransform(diff(y(t), t, 3), t, s, { noconds: true });
    const g = laplaceCorrespondence(f, new Map([[y, Y]]));
    expect(String(laplaceInitialConds(g, t, new Map([[y, [2, 4, 8, 16, 32]]])))).toBe('s**3*Y(s) - 2*s**2 - 4*s - 8');
  });

  it('laplace_transform', () => {
    const [t, s, a] = symbols('t s a');
    expect(show(laplaceTransform(pow(t, 4), t, s))).toBe('(24/s**5, 0, True)');
    expect(show(laplaceTransform(pow(t, a), t, s))).toBe('(gamma(a + 1)/(s*s**a), 0, re(a) > -1)');
    expect(show(laplaceTransform(add(DiracDelta(t), mul(-1, a, exp(mul(-1, a, t)))), t, s, { simplify: true }))).toBe('(s/(a + s), -re(a), True)');
  });

  it("laplace_transform: solving m*x''(t) + d*x'(t) + k*x(t) = 0", () => {
    const [t, s, d, k, m, v] = symbols('t s d k m v');
    const [x, X] = [SymFunction('x'), SymFunction('X')];
    const f = add(mul(m, diff(x(t), t, 2)), mul(d, diff(x(t), t)), mul(k, x(t)));
    let F = laplaceTransform(f, t, s, { noconds: true });
    F = laplaceCorrespondence(F, new Map([[x, X]]));
    F = laplaceInitialConds(F, t, new Map([[x, [0, v]]]));
    expect(String(F)).toBe('d*s*X(s) + k*X(s) + m*(s**2*X(s) - v)');
    const Xs = solve(F, X(s))[0]!;
    expect(String(Xs)).toBe('m*v/(d*s + k + m*s**2)');
    expect(String(inverseLaplaceTransform(Xs, s, t))).toBe('2*v*exp(-d*t/(2*m))*sin(t*sqrt((-d**2 + 4*k*m)/m**2)/2)*Heaviside(t)/sqrt((-d**2 + 4*k*m)/m**2)');
  });
});

describe('unevaluated transforms', () => {
  const [t, s] = symbols('t s x k nu');

  it('matrices (SymPy legacy_matrix=False)', () => {
    expect(show(laplaceTransform(Matrix.of([[t, exp(t)], [sin(t), 1]]), t, s))).toBe('(Matrix([[s**(-2), 1/(s - 1)], [1/(s**2 + 1), 1/s]]), 1, True)');
    expect(String(laplaceTransform(Matrix.of([[t]]), t, s, { noconds: true }))).toBe('Matrix([[s**(-2)]])');
    expect(String(inverseLaplaceTransform(Matrix.of([[pow(s, -1)]]), s, t))).toBe('Matrix([[Heaviside(t)]])');
  });
});

describe('piecewise functions and derivatives (test_laplace.py)', () => {
  const [s, t, x, w, a] = symbols('s t x w a');
  const [F, f] = [SymFunction('F'), SymFunction('f')];
  it('Piecewise is written with Heaviside', () => {
    expect(show(laplaceTransform(Piecewise([0, Le(t, 0)], [1, Le(t, 1)], [0, true]), t, s))).toBe('(1/s - exp(-s)/s, 0, True)');
    expect(show(laplaceTransform(Piecewise([0, Le(t, 0)], [t, Le(t, 1)], [sub(2, t), Le(t, 2)], [0, true]), t, s))).toBe('(s**(-2) - 2*exp(-s)/s**2 + exp(-2*s)/s**2, 0, True)');
    expect(show(laplaceTransform(Piecewise([exp(t), Le(t, 0)], [1, Le(t, 1)], [exp(t.neg()), true]), t, s))).toBe('(exp(-1)*exp(-s)/(s + 1) + 1/s - exp(-s)/s, 0, True)');
    expect(show(laplaceTransform(Piecewise([0, Le(x, 0)], [1, Le(x, 1)], [0, true]), t, s))).toBe('(Piecewise((0, x <= 0), (1, x <= 1), (0, True))/s, 0, True)');
    const want = '(2*a*(1 - exp(-s))/s + a*exp(-s)/s + a*exp(-3*s)/s, 0, True)';
    expect(show(laplaceTransform(mul(a, Piecewise([1, and(Le(t, 3), Gt(t, 1))], [2, true])), t, s))).toBe(want);
    expect(show(laplaceTransform(mul(a, Piecewise([1, and(Ge(t, 1), Lt(t, 3))], [2, true])), t, s))).toBe(want);
    expect(show(laplaceTransform(Piecewise([1, Eq(t, 1)], [2, true]), t, s))).toBe('(LaplaceTransform(Piecewise((1, Eq(t, 1)), (2, True)), t, s), -oo, True)');
  });
  it('derivatives in time and frequency', () => {
    expect(String(inverseLaplaceTransform(diff(F(s), s, 3), s, t))).toBe('-t**3*InverseLaplaceTransform(F(s), s, t, _None)');
    expect(String(inverseLaplaceTransform(diff(F(s), s, 4), s, t))).toBe('t**4*InverseLaplaceTransform(F(s), s, t, _None)');
    expect(String(laplaceTransform(diff(f(t), t), t, s, { noconds: true }))).toBe('s*LaplaceTransform(f(t), t, s) - f(0)');
    expect(String(laplaceTransform(diff(f(t), t, 3), t, s, { noconds: true }))).toBe(
      's**3*LaplaceTransform(f(t), t, s) - s**2*f(0) - s*Subs(Derivative(f(t), t), t, 0) - Subs(Derivative(f(t), (t, 2)), t, 0)',
    );
    expect(show(laplaceTransform(diff(f(x, t, w), t, 2), t, s))).toBe('(s**2*LaplaceTransform(f(x, t, w), t, s) - s*f(x, 0, w) - Subs(Derivative(f(x, t, w), t), t, 0), -oo, True)');
    expect(String(laplaceTransform(mul(10, diff(f(t), t)), t, s, { noconds: true }))).toBe('10*s*LaplaceTransform(f(t), t, s) - 10*f(0)');
  });
});

describe("SymPy's test suites (exact matches)", () => {
  it.each(ROWS.map((r, i) => [i, ...r] as const))('%i %s %j', (_i, fn, args, hints, syms, want) => {
    const table: Record<string, Expr> = {};
    for (const [n, a] of Object.entries(syms)) table[n] = new Sym(n, a);
    const conv = (a: string | string[]): unknown => (Array.isArray(a) ? a.map(conv) : a === 'None' ? undefined : fixFunctions(parse(a, { symbols: table })));
    const vals = args.map(conv);
    // inverse_laplace_transform takes the plane as its fourth argument
    if (fn === 'ILT' && vals.length === 3) vals.push(undefined);
    const r = (FNS[fn] as (...a: unknown[]) => unknown)(...vals, hints);
    expect(show(r)).toBe(want);
  });
});

// Expected values are the str() forms printed by SymPy 1.14.

const P = (s: string) => parse(s, { locals: { Heaviside, DiracDelta } });
const Qs = (s: string, syms: Sym[]) => parse(s, { symbols: syms, locals: { Heaviside, DiracDelta } });
/** The variable argument as a symbol. */
const V = (e: Expr): Sym => {
  if (!(e instanceof Sym)) throw new TypeError('a symbol expected');
  return e;
};

describe("Laplace transforms: SymPy 1.14 test_laplace cases", () => {
  const cases: [string, () => unknown, string][] = [
    ["laplaceTransform(Qs(\"a*t + t**(5/2) + t**2\", [symbol(\"a\", { positive: true })]), V(Qs(\"t\", [symbol(\"a\", { positive: true })])), Qs(\"s\", [symbol(\"a\", { positive: true })]))", () => laplaceTransform(Qs("a*t + t**(5/2) + t**2", [symbol("a", { positive: true })]), V(Qs("t", [symbol("a", { positive: true })])), Qs("s", [symbol("a", { positive: true })])), "(a/s**2 + 2/s**3 + 15*sqrt(pi)/(8*s**(7/2)), 0, True)"],
    ["laplaceTransform(Qs(\"b/(a + t)\", [symbol(\"b\", { positive: true }), symbol(\"a\", { positive: true })]), V(Qs(\"t\", [symbol(\"b\", { positive: true }), symbol(\"a\", { positive: true })])), Qs(\"s\", [symbol(\"b\", { positive: true }), symbol(\"a\", { positive: true })]))", () => laplaceTransform(Qs("b/(a + t)", [symbol("b", { positive: true }), symbol("a", { positive: true })]), V(Qs("t", [symbol("b", { positive: true }), symbol("a", { positive: true })])), Qs("s", [symbol("b", { positive: true }), symbol("a", { positive: true })])), "(-b*exp(-a*s)*Ei(-a*s), 0, True)"],
    ["laplaceTransform(Qs(\"1/sqrt(a + t)\", [symbol(\"a\", { positive: true })]), V(Qs(\"t\", [symbol(\"a\", { positive: true })])), Qs(\"s\", [symbol(\"a\", { positive: true })]))", () => laplaceTransform(Qs("1/sqrt(a + t)", [symbol("a", { positive: true })]), V(Qs("t", [symbol("a", { positive: true })])), Qs("s", [symbol("a", { positive: true })])), "(sqrt(pi)*sqrt(1/s)*exp(a*s)*erfc(sqrt(a)*sqrt(s)), 0, True)"],
    ["laplaceTransform(Qs(\"sqrt(t)/(a + t)\", [symbol(\"a\", { positive: true })]), V(Qs(\"t\", [symbol(\"a\", { positive: true })])), Qs(\"s\", [symbol(\"a\", { positive: true })]))", () => laplaceTransform(Qs("sqrt(t)/(a + t)", [symbol("a", { positive: true })]), V(Qs("t", [symbol("a", { positive: true })])), Qs("s", [symbol("a", { positive: true })])), "(-pi*sqrt(a)*exp(a*s)*erfc(sqrt(a)*sqrt(s)) + sqrt(pi)*sqrt(1/s), 0, True)"],
    ["laplaceTransform(Qs(\"(a + t)**(-3/2)\", [symbol(\"a\", { positive: true })]), V(Qs(\"t\", [symbol(\"a\", { positive: true })])), Qs(\"s\", [symbol(\"a\", { positive: true })]))", () => laplaceTransform(Qs("(a + t)**(-3/2)", [symbol("a", { positive: true })]), V(Qs("t", [symbol("a", { positive: true })])), Qs("s", [symbol("a", { positive: true })])), "(-2*sqrt(pi)*sqrt(s)*exp(a*s)*erfc(sqrt(a)*sqrt(s)) + 2/sqrt(a), 0, True)"],
    ["laplaceTransform(Qs(\"(a + t)**b\", [symbol(\"b\", { positive: true }), symbol(\"a\", { positive: true })]), V(Qs(\"t\", [symbol(\"b\", { positive: true }), symbol(\"a\", { positive: true })])), Qs(\"s\", [symbol(\"b\", { positive: true }), symbol(\"a\", { positive: true })]))", () => laplaceTransform(Qs("(a + t)**b", [symbol("b", { positive: true }), symbol("a", { positive: true })]), V(Qs("t", [symbol("b", { positive: true }), symbol("a", { positive: true })])), Qs("s", [symbol("b", { positive: true }), symbol("a", { positive: true })])), "(s**(-b - 1)*exp(-a*s)*uppergamma(b + 1, a*s), 0, True)"],
    ["laplaceTransform(Qs(\"t**5/(a + t)\", [symbol(\"a\", { positive: true })]), V(Qs(\"t\", [symbol(\"a\", { positive: true })])), Qs(\"s\", [symbol(\"a\", { positive: true })]))", () => laplaceTransform(Qs("t**5/(a + t)", [symbol("a", { positive: true })]), V(Qs("t", [symbol("a", { positive: true })])), Qs("s", [symbol("a", { positive: true })])), "(120*expint(6, a*s)/s**5, 0, True)"],
    ["laplaceTransform(P(\"exp(t)\"), V(P(\"t\")), P(\"s\"))", () => laplaceTransform(P("exp(t)"), V(P("t")), P("s")), "(1/(s - 1), 1, True)"],
    ["laplaceTransform(P(\"exp(2*t)\"), V(P(\"t\")), P(\"s\"))", () => laplaceTransform(P("exp(2*t)"), V(P("t")), P("s")), "(1/(s - 2), 2, True)"],
    ["laplaceTransform(Qs(\"exp(a*t)\", [symbol(\"a\", { positive: true })]), V(Qs(\"t\", [symbol(\"a\", { positive: true })])), Qs(\"s\", [symbol(\"a\", { positive: true })]))", () => laplaceTransform(Qs("exp(a*t)", [symbol("a", { positive: true })]), V(Qs("t", [symbol("a", { positive: true })])), Qs("s", [symbol("a", { positive: true })])), "(1/(-a + s), a, True)"],
    ["laplaceTransform(Qs(\"exp(a*(-b + t))\", [symbol(\"b\", { positive: true }), symbol(\"a\", { positive: true })]), V(Qs(\"t\", [symbol(\"b\", { positive: true }), symbol(\"a\", { positive: true })])), Qs(\"s\", [symbol(\"b\", { positive: true }), symbol(\"a\", { positive: true })]))", () => laplaceTransform(Qs("exp(a*(-b + t))", [symbol("b", { positive: true }), symbol("a", { positive: true })]), V(Qs("t", [symbol("b", { positive: true }), symbol("a", { positive: true })])), Qs("s", [symbol("b", { positive: true }), symbol("a", { positive: true })])), "(exp(-a*b)/(-a + s), a, True)"],
    ["laplaceTransform(Qs(\"t*exp(-a*t)\", [symbol(\"a\", { positive: true })]), V(Qs(\"t\", [symbol(\"a\", { positive: true })])), Qs(\"s\", [symbol(\"a\", { positive: true })]))", () => laplaceTransform(Qs("t*exp(-a*t)", [symbol("a", { positive: true })]), V(Qs("t", [symbol("a", { positive: true })])), Qs("s", [symbol("a", { positive: true })])), "((a + s)**(-2), -a, True)"],
    ["laplaceTransform(Qs(\"t*exp(-a*(-b + t))\", [symbol(\"b\", { positive: true }), symbol(\"a\", { positive: true })]), V(Qs(\"t\", [symbol(\"b\", { positive: true }), symbol(\"a\", { positive: true })])), Qs(\"s\", [symbol(\"b\", { positive: true }), symbol(\"a\", { positive: true })]))", () => laplaceTransform(Qs("t*exp(-a*(-b + t))", [symbol("b", { positive: true }), symbol("a", { positive: true })]), V(Qs("t", [symbol("b", { positive: true }), symbol("a", { positive: true })])), Qs("s", [symbol("b", { positive: true }), symbol("a", { positive: true })])), "(exp(a*b)/(a + s)**2, -a, True)"],
    ["laplaceTransform(Qs(\"b*t*exp(-a*t)\", [symbol(\"b\", { positive: true }), symbol(\"a\", { positive: true })]), V(Qs(\"t\", [symbol(\"b\", { positive: true }), symbol(\"a\", { positive: true })])), Qs(\"s\", [symbol(\"b\", { positive: true }), symbol(\"a\", { positive: true })]))", () => laplaceTransform(Qs("b*t*exp(-a*t)", [symbol("b", { positive: true }), symbol("a", { positive: true })]), V(Qs("t", [symbol("b", { positive: true }), symbol("a", { positive: true })])), Qs("s", [symbol("b", { positive: true }), symbol("a", { positive: true })])), "(b/(a + s)**2, -a, True)"],
    ["laplaceTransform(Qs(\"exp(-a*exp(-t))\", [symbol(\"a\", { positive: true })]), V(Qs(\"t\", [symbol(\"a\", { positive: true })])), Qs(\"s\", [symbol(\"a\", { positive: true })]))", () => laplaceTransform(Qs("exp(-a*exp(-t))", [symbol("a", { positive: true })]), V(Qs("t", [symbol("a", { positive: true })])), Qs("s", [symbol("a", { positive: true })])), "(lowergamma(s, a)/a**s, 0, True)"],
    ["laplaceTransform(Qs(\"exp(-a*exp(t))\", [symbol(\"a\", { positive: true })]), V(Qs(\"t\", [symbol(\"a\", { positive: true })])), Qs(\"s\", [symbol(\"a\", { positive: true })]))", () => laplaceTransform(Qs("exp(-a*exp(t))", [symbol("a", { positive: true })]), V(Qs("t", [symbol("a", { positive: true })])), Qs("s", [symbol("a", { positive: true })])), "(a**s*uppergamma(-s, a), 0, True)"],
    ["laplaceTransform(P(\"t**(7/4)*exp(-8*t)/gamma(11/4)\"), V(P(\"t\")), P(\"s\"))", () => laplaceTransform(P("t**(7/4)*exp(-8*t)/gamma(11/4)"), V(P("t")), P("s")), "((s + 8)**(-11/4), -8, True)"],
    ["laplaceTransform(P(\"t**(3/2)*exp(-8*t)\"), V(P(\"t\")), P(\"s\"))", () => laplaceTransform(P("t**(3/2)*exp(-8*t)"), V(P("t")), P("s")), "(3*sqrt(pi)/(4*(s + 8)**(5/2)), -8, True)"],
    ["laplaceTransform(Qs(\"t**a*exp(-a*t)\", [symbol(\"a\", { positive: true })]), V(Qs(\"t\", [symbol(\"a\", { positive: true })])), Qs(\"s\", [symbol(\"a\", { positive: true })]))", () => laplaceTransform(Qs("t**a*exp(-a*t)", [symbol("a", { positive: true })]), V(Qs("t", [symbol("a", { positive: true })])), Qs("s", [symbol("a", { positive: true })])), "((a + s)**(-a - 1)*gamma(a + 1), -a, True)"],
    ["laplaceTransform(Qs(\"b*exp(-a*t**2)\", [symbol(\"b\", { positive: true }), symbol(\"a\", { positive: true })]), V(Qs(\"t\", [symbol(\"b\", { positive: true }), symbol(\"a\", { positive: true })])), Qs(\"s\", [symbol(\"b\", { positive: true }), symbol(\"a\", { positive: true })]))", () => laplaceTransform(Qs("b*exp(-a*t**2)", [symbol("b", { positive: true }), symbol("a", { positive: true })]), V(Qs("t", [symbol("b", { positive: true }), symbol("a", { positive: true })])), Qs("s", [symbol("b", { positive: true }), symbol("a", { positive: true })])), "(sqrt(pi)*b*exp(s**2/(4*a))*erfc(s/(2*sqrt(a)))/(2*sqrt(a)), 0, True)"],
    ["laplaceTransform(P(\"exp(-2*t**2)\"), V(P(\"t\")), P(\"s\"))", () => laplaceTransform(P("exp(-2*t**2)"), V(P("t")), P("s")), "(sqrt(2)*sqrt(pi)*exp(s**2/8)*erfc(sqrt(2)*s/4)/4, 0, True)"],
    ["laplaceTransform(Qs(\"b*exp(2*t**2)\", [symbol(\"b\", { positive: true })]), V(Qs(\"t\", [symbol(\"b\", { positive: true })])), Qs(\"s\", [symbol(\"b\", { positive: true })]))", () => laplaceTransform(Qs("b*exp(2*t**2)", [symbol("b", { positive: true })]), V(Qs("t", [symbol("b", { positive: true })])), Qs("s", [symbol("b", { positive: true })])), "(b*LaplaceTransform(exp(2*t**2), t, s), -oo, True)"],
    ["laplaceTransform(Qs(\"t*exp(-a*t**2)\", [symbol(\"a\", { positive: true })]), V(Qs(\"t\", [symbol(\"a\", { positive: true })])), Qs(\"s\", [symbol(\"a\", { positive: true })]))", () => laplaceTransform(Qs("t*exp(-a*t**2)", [symbol("a", { positive: true })]), V(Qs("t", [symbol("a", { positive: true })])), Qs("s", [symbol("a", { positive: true })])), "(1/(2*a) - s*erfc(s/(2*sqrt(a)))/(4*sqrt(pi)*a**(3/2)), 0, True)"],
    ["laplaceTransform(Qs(\"exp(-a/t)\", [symbol(\"a\", { positive: true })]), V(Qs(\"t\", [symbol(\"a\", { positive: true })])), Qs(\"s\", [symbol(\"a\", { positive: true })]))", () => laplaceTransform(Qs("exp(-a/t)", [symbol("a", { positive: true })]), V(Qs("t", [symbol("a", { positive: true })])), Qs("s", [symbol("a", { positive: true })])), "(2*sqrt(a)*sqrt(1/s)*besselk(1, 2*sqrt(a)*sqrt(s)), 0, True)"],
    ["laplaceTransform(Qs(\"sqrt(t)*exp(-a/t)\", [symbol(\"a\", { positive: true })]), V(Qs(\"t\", [symbol(\"a\", { positive: true })])), Qs(\"s\", [symbol(\"a\", { positive: true })]), { simplify: true })", () => laplaceTransform(Qs("sqrt(t)*exp(-a/t)", [symbol("a", { positive: true })]), V(Qs("t", [symbol("a", { positive: true })])), Qs("s", [symbol("a", { positive: true })]), { simplify: true }), "(sqrt(pi)*(sqrt(a)*sqrt(s) + 1/2)*sqrt(s**(-3))*exp(-2*sqrt(a)*sqrt(s)), 0, True)"],
    ["laplaceTransform(Qs(\"exp(-a/t)/sqrt(t)\", [symbol(\"a\", { positive: true })]), V(Qs(\"t\", [symbol(\"a\", { positive: true })])), Qs(\"s\", [symbol(\"a\", { positive: true })]))", () => laplaceTransform(Qs("exp(-a/t)/sqrt(t)", [symbol("a", { positive: true })]), V(Qs("t", [symbol("a", { positive: true })])), Qs("s", [symbol("a", { positive: true })])), "(sqrt(pi)*sqrt(1/s)*exp(-2*sqrt(a)*sqrt(s)), 0, True)"],
    ["laplaceTransform(Qs(\"exp(-a/t)/t**(3/2)\", [symbol(\"a\", { positive: true })]), V(Qs(\"t\", [symbol(\"a\", { positive: true })])), Qs(\"s\", [symbol(\"a\", { positive: true })]))", () => laplaceTransform(Qs("exp(-a/t)/t**(3/2)", [symbol("a", { positive: true })]), V(Qs("t", [symbol("a", { positive: true })])), Qs("s", [symbol("a", { positive: true })])), "(sqrt(pi)*exp(-2*sqrt(a)*sqrt(s))/sqrt(a), 0, True)"],
    ["laplaceTransform(P(\"t**4*exp(-2/t)\"), V(P(\"t\")), P(\"s\"))", () => laplaceTransform(P("t**4*exp(-2/t)"), V(P("t")), P("s")), "(8*sqrt(2)*(1/s)**(5/2)*besselk(5, 2*sqrt(2)*sqrt(s)), 0, True)"],
    ["laplaceTransform(Qs(\"sinh(a*t)\", [symbol(\"a\", { positive: true })]), V(Qs(\"t\", [symbol(\"a\", { positive: true })])), Qs(\"s\", [symbol(\"a\", { positive: true })]))", () => laplaceTransform(Qs("sinh(a*t)", [symbol("a", { positive: true })]), V(Qs("t", [symbol("a", { positive: true })])), Qs("s", [symbol("a", { positive: true })])), "(a/(-a**2 + s**2), a, True)"],
    ["laplaceTransform(Qs(\"b*sinh(a*t)**2\", [symbol(\"b\", { positive: true }), symbol(\"a\", { positive: true })]), V(Qs(\"t\", [symbol(\"b\", { positive: true }), symbol(\"a\", { positive: true })])), Qs(\"s\", [symbol(\"b\", { positive: true }), symbol(\"a\", { positive: true })]))", () => laplaceTransform(Qs("b*sinh(a*t)**2", [symbol("b", { positive: true }), symbol("a", { positive: true })]), V(Qs("t", [symbol("b", { positive: true }), symbol("a", { positive: true })])), Qs("s", [symbol("b", { positive: true }), symbol("a", { positive: true })])), "(2*a**2*b/(-4*a**2*s + s**3), 2*a, True)"],
    ["laplaceTransform(P(\"cosh(2*t)\"), V(P(\"t\")), P(\"s\"))", () => laplaceTransform(P("cosh(2*t)"), V(P("t")), P("s")), "(s/(s**2 - 4), 2, True)"],
    ["laplaceTransform(Qs(\"cosh(a*t)\", [symbol(\"a\", { positive: true })]), V(Qs(\"t\", [symbol(\"a\", { positive: true })])), Qs(\"s\", [symbol(\"a\", { positive: true })]))", () => laplaceTransform(Qs("cosh(a*t)", [symbol("a", { positive: true })]), V(Qs("t", [symbol("a", { positive: true })])), Qs("s", [symbol("a", { positive: true })])), "(s/(-a**2 + s**2), a, True)"],
    ["laplaceTransform(P(\"sinh(x + 3)\"), V(P(\"x\")), P(\"s\"), { simplify: true })", () => laplaceTransform(P("sinh(x + 3)"), V(P("x")), P("s"), { simplify: true }), "((s*sinh(3) + cosh(3))/(s**2 - 1), 1, True)"],
    ["laplaceTransform(P(\"42*sin(t*w + x)**2\"), V(P(\"t\")), P(\"s\"))", () => laplaceTransform(P("42*sin(t*w + x)**2"), V(P("t")), P("s")), "(42*(-s*cos(2*x)/2 + w*sin(2*x))/(s**2 + 4*w**2) + 21/s, 2*Abs(im(w)), True)"],
    ["laplaceTransform(Qs(\"sinh(a*t)*cosh(a*t)\", [symbol(\"a\", { positive: true })]), V(Qs(\"t\", [symbol(\"a\", { positive: true })])), Qs(\"s\", [symbol(\"a\", { positive: true })]), { simplify: true })", () => laplaceTransform(Qs("sinh(a*t)*cosh(a*t)", [symbol("a", { positive: true })]), V(Qs("t", [symbol("a", { positive: true })])), Qs("s", [symbol("a", { positive: true })]), { simplify: true }), "(a/(-4*a**2 + s**2), 2*a, True)"],
    ["laplaceTransform(Qs(\"sinh(a*t)/t\", [symbol(\"a\", { positive: true })]), V(Qs(\"t\", [symbol(\"a\", { positive: true })])), Qs(\"s\", [symbol(\"a\", { positive: true })]))", () => laplaceTransform(Qs("sinh(a*t)/t", [symbol("a", { positive: true })]), V(Qs("t", [symbol("a", { positive: true })])), Qs("s", [symbol("a", { positive: true })])), "(log((a + s)/(-a + s))/2, a, True)"],
    ["laplaceTransform(Qs(\"sinh(a*t)/t**(3/2)\", [symbol(\"a\", { positive: true })]), V(Qs(\"t\", [symbol(\"a\", { positive: true })])), Qs(\"s\", [symbol(\"a\", { positive: true })]))", () => laplaceTransform(Qs("sinh(a*t)/t**(3/2)", [symbol("a", { positive: true })]), V(Qs("t", [symbol("a", { positive: true })])), Qs("s", [symbol("a", { positive: true })])), "(-sqrt(pi)*(sqrt(-a + s) - sqrt(a + s)), a, True)"],
    ["laplaceTransform(Qs(\"t**(3/7)*cosh(a*t)\", [symbol(\"a\", { positive: true })]), V(Qs(\"t\", [symbol(\"a\", { positive: true })])), Qs(\"s\", [symbol(\"a\", { positive: true })]))", () => laplaceTransform(Qs("t**(3/7)*cosh(a*t)", [symbol("a", { positive: true })]), V(Qs("t", [symbol("a", { positive: true })])), Qs("s", [symbol("a", { positive: true })])), "(((a + s)**(-10/7) + (-a + s)**(-10/7))*gamma(10/7)/2, a, True)"],
    ["laplaceTransform(Qs(\"log(a*t + 1)\", [symbol(\"a\", { positive: true })]), V(Qs(\"t\", [symbol(\"a\", { positive: true })])), Qs(\"s\", [symbol(\"a\", { positive: true })]))", () => laplaceTransform(Qs("log(a*t + 1)", [symbol("a", { positive: true })]), V(Qs("t", [symbol("a", { positive: true })])), Qs("s", [symbol("a", { positive: true })])), "(-exp(s/a)*Ei(-s/a)/s, 0, True)"],
    ["laplaceTransform(Qs(\"log(a + t)\", [symbol(\"a\", { positive: true })]), V(Qs(\"t\", [symbol(\"a\", { positive: true })])), Qs(\"s\", [symbol(\"a\", { positive: true })]), { simplify: true })", () => laplaceTransform(Qs("log(a + t)", [symbol("a", { positive: true })]), V(Qs("t", [symbol("a", { positive: true })])), Qs("s", [symbol("a", { positive: true })]), { simplify: true }), "((s*log(a) - exp(s/a)*Ei(-s/a))/s**2, 0, True)"],
    ["laplaceTransform(P(\"t**3*log(t)\"), V(P(\"t\")), P(\"s\"), { noconds: true, simplify: true })", () => laplaceTransform(P("t**3*log(t)"), V(P("t")), P("s"), { noconds: true, simplify: true }), "(-6*log(s) - 6*EulerGamma + 11)/s**4"],
    ["laplaceTransform(Qs(\"sin(a*t)\", [symbol(\"a\", { positive: true })]), V(Qs(\"t\", [symbol(\"a\", { positive: true })])), Qs(\"s\", [symbol(\"a\", { positive: true })]))", () => laplaceTransform(Qs("sin(a*t)", [symbol("a", { positive: true })]), V(Qs("t", [symbol("a", { positive: true })])), Qs("s", [symbol("a", { positive: true })])), "(a/(a**2 + s**2), 0, True)"],
    ["laplaceTransform(Qs(\"Abs(sin(a*t))\", [symbol(\"a\", { positive: true })]), V(Qs(\"t\", [symbol(\"a\", { positive: true })])), Qs(\"s\", [symbol(\"a\", { positive: true })]))", () => laplaceTransform(Qs("Abs(sin(a*t))", [symbol("a", { positive: true })]), V(Qs("t", [symbol("a", { positive: true })])), Qs("s", [symbol("a", { positive: true })])), "(a*coth(pi*s/(2*a))/(a**2 + s**2), 0, True)"],
    ["laplaceTransform(Qs(\"sin(a*t)/t\", [symbol(\"a\", { positive: true })]), V(Qs(\"t\", [symbol(\"a\", { positive: true })])), Qs(\"s\", [symbol(\"a\", { positive: true })]))", () => laplaceTransform(Qs("sin(a*t)/t", [symbol("a", { positive: true })]), V(Qs("t", [symbol("a", { positive: true })])), Qs("s", [symbol("a", { positive: true })])), "(atan(a/s), 0, True)"],
    ["laplaceTransform(Qs(\"sin(a*t)**2/t\", [symbol(\"a\", { positive: true })]), V(Qs(\"t\", [symbol(\"a\", { positive: true })])), Qs(\"s\", [symbol(\"a\", { positive: true })]))", () => laplaceTransform(Qs("sin(a*t)**2/t", [symbol("a", { positive: true })]), V(Qs("t", [symbol("a", { positive: true })])), Qs("s", [symbol("a", { positive: true })])), "(log(4*a**2/s**2 + 1)/4, 0, True)"],
    ["laplaceTransform(Qs(\"sin(a*t)**2/t**2\", [symbol(\"a\", { positive: true })]), V(Qs(\"t\", [symbol(\"a\", { positive: true })])), Qs(\"s\", [symbol(\"a\", { positive: true })]))", () => laplaceTransform(Qs("sin(a*t)**2/t**2", [symbol("a", { positive: true })]), V(Qs("t", [symbol("a", { positive: true })])), Qs("s", [symbol("a", { positive: true })])), "(a*atan(2*a/s) - s*log(4*a**2/s**2 + 1)/4, 0, True)"],
    ["laplaceTransform(Qs(\"cos(a*t)\", [symbol(\"a\", { positive: true })]), V(Qs(\"t\", [symbol(\"a\", { positive: true })])), Qs(\"s\", [symbol(\"a\", { positive: true })]))", () => laplaceTransform(Qs("cos(a*t)", [symbol("a", { positive: true })]), V(Qs("t", [symbol("a", { positive: true })])), Qs("s", [symbol("a", { positive: true })])), "(s/(a**2 + s**2), 0, True)"],
    ["laplaceTransform(Qs(\"cos(a*t)**2\", [symbol(\"a\", { positive: true })]), V(Qs(\"t\", [symbol(\"a\", { positive: true })])), Qs(\"s\", [symbol(\"a\", { positive: true })]))", () => laplaceTransform(Qs("cos(a*t)**2", [symbol("a", { positive: true })]), V(Qs("t", [symbol("a", { positive: true })])), Qs("s", [symbol("a", { positive: true })])), "((2*a**2 + s**2)/(s*(4*a**2 + s**2)), 0, True)"],
    ["laplaceTransform(Qs(\"sin(a*t)*sin(b*t)\", [symbol(\"b\", { positive: true }), symbol(\"a\", { positive: true })]), V(Qs(\"t\", [symbol(\"b\", { positive: true }), symbol(\"a\", { positive: true })])), Qs(\"s\", [symbol(\"b\", { positive: true }), symbol(\"a\", { positive: true })]))", () => laplaceTransform(Qs("sin(a*t)*sin(b*t)", [symbol("b", { positive: true }), symbol("a", { positive: true })]), V(Qs("t", [symbol("b", { positive: true }), symbol("a", { positive: true })])), Qs("s", [symbol("b", { positive: true }), symbol("a", { positive: true })])), "(2*a*b*s/((s**2 + (a - b)**2)*(s**2 + (a + b)**2)), 0, True)"],
    ["laplaceTransform(Qs(\"sin(b*t)*cos(a*t)\", [symbol(\"b\", { positive: true }), symbol(\"a\", { positive: true })]), V(Qs(\"t\", [symbol(\"b\", { positive: true }), symbol(\"a\", { positive: true })])), Qs(\"s\", [symbol(\"b\", { positive: true }), symbol(\"a\", { positive: true })]))", () => laplaceTransform(Qs("sin(b*t)*cos(a*t)", [symbol("b", { positive: true }), symbol("a", { positive: true })]), V(Qs("t", [symbol("b", { positive: true }), symbol("a", { positive: true })])), Qs("s", [symbol("b", { positive: true }), symbol("a", { positive: true })])), "(b*(-a**2 + b**2 + s**2)/((s**2 + (a - b)**2)*(s**2 + (a + b)**2)), 0, True)"],
    ["laplaceTransform(Qs(\"cos(a*t)*cos(b*t)\", [symbol(\"b\", { positive: true }), symbol(\"a\", { positive: true })]), V(Qs(\"t\", [symbol(\"b\", { positive: true }), symbol(\"a\", { positive: true })])), Qs(\"s\", [symbol(\"b\", { positive: true }), symbol(\"a\", { positive: true })]))", () => laplaceTransform(Qs("cos(a*t)*cos(b*t)", [symbol("b", { positive: true }), symbol("a", { positive: true })]), V(Qs("t", [symbol("b", { positive: true }), symbol("a", { positive: true })])), Qs("s", [symbol("b", { positive: true }), symbol("a", { positive: true })])), "(s*(a**2 + b**2 + s**2)/((s**2 + (a - b)**2)*(s**2 + (a + b)**2)), 0, True)"],
    ["laplaceTransform(Qs(\"-a*t*cos(a*t) + sin(a*t)\", [symbol(\"a\", { positive: true })]), V(Qs(\"t\", [symbol(\"a\", { positive: true })])), Qs(\"s\", [symbol(\"a\", { positive: true })]), { simplify: true })", () => laplaceTransform(Qs("-a*t*cos(a*t) + sin(a*t)", [symbol("a", { positive: true })]), V(Qs("t", [symbol("a", { positive: true })])), Qs("s", [symbol("a", { positive: true })]), { simplify: true }), "(2*a**3/(a**4 + 2*a**2*s**2 + s**4), 0, True)"],
    ["laplaceTransform(Qs(\"c*exp(-b*t)*sin(a*t)\", [symbol(\"b\", { positive: true }), symbol(\"a\", { positive: true }), symbol(\"c\", { positive: true })]), V(Qs(\"t\", [symbol(\"b\", { positive: true }), symbol(\"a\", { positive: true }), symbol(\"c\", { positive: true })])), Qs(\"s\", [symbol(\"b\", { positive: true }), symbol(\"a\", { positive: true }), symbol(\"c\", { positive: true })]))", () => laplaceTransform(Qs("c*exp(-b*t)*sin(a*t)", [symbol("b", { positive: true }), symbol("a", { positive: true }), symbol("c", { positive: true })]), V(Qs("t", [symbol("b", { positive: true }), symbol("a", { positive: true }), symbol("c", { positive: true })])), Qs("s", [symbol("b", { positive: true }), symbol("a", { positive: true }), symbol("c", { positive: true })])), "(a*c/(a**2 + (b + s)**2), -b, True)"],
    ["laplaceTransform(Qs(\"c*exp(-b*t)*cos(a*t)\", [symbol(\"b\", { positive: true }), symbol(\"a\", { positive: true }), symbol(\"c\", { positive: true })]), V(Qs(\"t\", [symbol(\"b\", { positive: true }), symbol(\"a\", { positive: true }), symbol(\"c\", { positive: true })])), Qs(\"s\", [symbol(\"b\", { positive: true }), symbol(\"a\", { positive: true }), symbol(\"c\", { positive: true })]))", () => laplaceTransform(Qs("c*exp(-b*t)*cos(a*t)", [symbol("b", { positive: true }), symbol("a", { positive: true }), symbol("c", { positive: true })]), V(Qs("t", [symbol("b", { positive: true }), symbol("a", { positive: true }), symbol("c", { positive: true })])), Qs("s", [symbol("b", { positive: true }), symbol("a", { positive: true }), symbol("c", { positive: true })])), "(c*(b + s)/(a**2 + (b + s)**2), -b, True)"],
    ["laplaceTransform(P(\"cos(x + 3)\"), V(P(\"x\")), P(\"s\"), { simplify: true })", () => laplaceTransform(P("cos(x + 3)"), V(P("x")), P("s"), { simplify: true }), "((s*cos(3) - sin(3))/(s**2 + 1), 0, True)"],
    ["laplaceTransform(Qs(\"erf(a*t)\", [symbol(\"a\", { positive: true })]), V(Qs(\"t\", [symbol(\"a\", { positive: true })])), Qs(\"s\", [symbol(\"a\", { positive: true })]))", () => laplaceTransform(Qs("erf(a*t)", [symbol("a", { positive: true })]), V(Qs("t", [symbol("a", { positive: true })])), Qs("s", [symbol("a", { positive: true })])), "(exp(s**2/(4*a**2))*erfc(s/(2*a))/s, 0, True)"],
    ["laplaceTransform(Qs(\"besselj(0, a*t)\", [symbol(\"a\", { positive: true })]), V(Qs(\"t\", [symbol(\"a\", { positive: true })])), Qs(\"s\", [symbol(\"a\", { positive: true })]))", () => laplaceTransform(Qs("besselj(0, a*t)", [symbol("a", { positive: true })]), V(Qs("t", [symbol("a", { positive: true })])), Qs("s", [symbol("a", { positive: true })])), "(1/sqrt(a**2 + s**2), 0, True)"],
    ["laplaceTransform(Qs(\"besselj(2, a*t)\", [symbol(\"a\", { positive: true })]), V(Qs(\"t\", [symbol(\"a\", { positive: true })])), Qs(\"s\", [symbol(\"a\", { positive: true })]), { simplify: true })", () => laplaceTransform(Qs("besselj(2, a*t)", [symbol("a", { positive: true })]), V(Qs("t", [symbol("a", { positive: true })])), Qs("s", [symbol("a", { positive: true })]), { simplify: true }), "(a**2/(sqrt(a**2 + s**2)*(s + sqrt(a**2 + s**2))**2), 0, True)"],
    ["laplaceTransform(Qs(\"t*besselj(0, a*t)\", [symbol(\"a\", { positive: true })]), V(Qs(\"t\", [symbol(\"a\", { positive: true })])), Qs(\"s\", [symbol(\"a\", { positive: true })]))", () => laplaceTransform(Qs("t*besselj(0, a*t)", [symbol("a", { positive: true })]), V(Qs("t", [symbol("a", { positive: true })])), Qs("s", [symbol("a", { positive: true })])), "(s/(a**2 + s**2)**(3/2), 0, True)"],
    ["laplaceTransform(Qs(\"t*besselj(1, a*t)\", [symbol(\"a\", { positive: true })]), V(Qs(\"t\", [symbol(\"a\", { positive: true })])), Qs(\"s\", [symbol(\"a\", { positive: true })]))", () => laplaceTransform(Qs("t*besselj(1, a*t)", [symbol("a", { positive: true })]), V(Qs("t", [symbol("a", { positive: true })])), Qs("s", [symbol("a", { positive: true })])), "(a/(a**2 + s**2)**(3/2), 0, True)"],
    ["laplaceTransform(Qs(\"t**2*besselj(2, a*t)\", [symbol(\"a\", { positive: true })]), V(Qs(\"t\", [symbol(\"a\", { positive: true })])), Qs(\"s\", [symbol(\"a\", { positive: true })]))", () => laplaceTransform(Qs("t**2*besselj(2, a*t)", [symbol("a", { positive: true })]), V(Qs("t", [symbol("a", { positive: true })])), Qs("s", [symbol("a", { positive: true })])), "(3*a**2/(a**2 + s**2)**(5/2), 0, True)"],
    ["laplaceTransform(Qs(\"besselj(0, a*sqrt(b*t + t**2))\", [symbol(\"b\", { positive: true }), symbol(\"a\", { positive: true })]), V(Qs(\"t\", [symbol(\"b\", { positive: true }), symbol(\"a\", { positive: true })])), Qs(\"s\", [symbol(\"b\", { positive: true }), symbol(\"a\", { positive: true })]), { simplify: true })", () => laplaceTransform(Qs("besselj(0, a*sqrt(b*t + t**2))", [symbol("b", { positive: true }), symbol("a", { positive: true })]), V(Qs("t", [symbol("b", { positive: true }), symbol("a", { positive: true })])), Qs("s", [symbol("b", { positive: true }), symbol("a", { positive: true })]), { simplify: true }), "(exp(b*(s - sqrt(a**2 + s**2)))/sqrt(a**2 + s**2), 0, True)"],
    ["laplaceTransform(Qs(\"besseli(0, a*t)\", [symbol(\"a\", { positive: true })]), V(Qs(\"t\", [symbol(\"a\", { positive: true })])), Qs(\"s\", [symbol(\"a\", { positive: true })]))", () => laplaceTransform(Qs("besseli(0, a*t)", [symbol("a", { positive: true })]), V(Qs("t", [symbol("a", { positive: true })])), Qs("s", [symbol("a", { positive: true })])), "(1/sqrt(-a**2 + s**2), a, True)"],
    ["laplaceTransform(Qs(\"besseli(2, a*t)\", [symbol(\"a\", { positive: true })]), V(Qs(\"t\", [symbol(\"a\", { positive: true })])), Qs(\"s\", [symbol(\"a\", { positive: true })]), { simplify: true })", () => laplaceTransform(Qs("besseli(2, a*t)", [symbol("a", { positive: true })]), V(Qs("t", [symbol("a", { positive: true })])), Qs("s", [symbol("a", { positive: true })]), { simplify: true }), "(a**2/(sqrt(-a**2 + s**2)*(s + sqrt(-a**2 + s**2))**2), a, True)"],
    ["laplaceTransform(Qs(\"t*besseli(0, a*t)\", [symbol(\"a\", { positive: true })]), V(Qs(\"t\", [symbol(\"a\", { positive: true })])), Qs(\"s\", [symbol(\"a\", { positive: true })]))", () => laplaceTransform(Qs("t*besseli(0, a*t)", [symbol("a", { positive: true })]), V(Qs("t", [symbol("a", { positive: true })])), Qs("s", [symbol("a", { positive: true })])), "(s/(-a**2 + s**2)**(3/2), a, True)"],
    ["laplaceTransform(Qs(\"t*besseli(1, a*t)\", [symbol(\"a\", { positive: true })]), V(Qs(\"t\", [symbol(\"a\", { positive: true })])), Qs(\"s\", [symbol(\"a\", { positive: true })]))", () => laplaceTransform(Qs("t*besseli(1, a*t)", [symbol("a", { positive: true })]), V(Qs("t", [symbol("a", { positive: true })])), Qs("s", [symbol("a", { positive: true })])), "(a/(-a**2 + s**2)**(3/2), a, True)"],
    ["laplaceTransform(Qs(\"t**2*besseli(2, a*t)\", [symbol(\"a\", { positive: true })]), V(Qs(\"t\", [symbol(\"a\", { positive: true })])), Qs(\"s\", [symbol(\"a\", { positive: true })]))", () => laplaceTransform(Qs("t**2*besseli(2, a*t)", [symbol("a", { positive: true })]), V(Qs("t", [symbol("a", { positive: true })])), Qs("s", [symbol("a", { positive: true })])), "(3*a**2/(-a**2 + s**2)**(5/2), a, True)"],
    ["laplaceTransform(Qs(\"bessely(0, a*t)\", [symbol(\"a\", { positive: true })]), V(Qs(\"t\", [symbol(\"a\", { positive: true })])), Qs(\"s\", [symbol(\"a\", { positive: true })]))", () => laplaceTransform(Qs("bessely(0, a*t)", [symbol("a", { positive: true })]), V(Qs("t", [symbol("a", { positive: true })])), Qs("s", [symbol("a", { positive: true })])), "(-2*asinh(s/a)/(pi*sqrt(a**2 + s**2)), 0, True)"],
    ["laplaceTransform(Qs(\"besselk(0, a*t)\", [symbol(\"a\", { positive: true })]), V(Qs(\"t\", [symbol(\"a\", { positive: true })])), Qs(\"s\", [symbol(\"a\", { positive: true })]))", () => laplaceTransform(Qs("besselk(0, a*t)", [symbol("a", { positive: true })]), V(Qs("t", [symbol("a", { positive: true })])), Qs("s", [symbol("a", { positive: true })])), "(log((s + sqrt(-a**2 + s**2))/a)/sqrt(-a**2 + s**2), -a, True)"],
    ["laplaceTransform(P(\"cos(t - 1)*Heaviside(t - 1)\"), V(P(\"t\")), P(\"s\"))", () => laplaceTransform(P("cos(t - 1)*Heaviside(t - 1)"), V(P("t")), P("s")), "(s*exp(-s)/(s**2 + 1), 0, True)"],
    ["laplaceTransform(Qs(\"a*f(t)\", [symbol(\"a\", { positive: true })]), V(Qs(\"t\", [symbol(\"a\", { positive: true })])), Qs(\"w\", [symbol(\"a\", { positive: true })]))", () => laplaceTransform(Qs("a*f(t)", [symbol("a", { positive: true })]), V(Qs("t", [symbol("a", { positive: true })])), Qs("w", [symbol("a", { positive: true })])), "(a*LaplaceTransform(f(t), t, w), -oo, True)"],
    ["laplaceTransform(Qs(\"a*f(t + 1)*Heaviside(t + 1)\", [symbol(\"a\", { positive: true })]), V(Qs(\"t\", [symbol(\"a\", { positive: true })])), Qs(\"s\", [symbol(\"a\", { positive: true })]))", () => laplaceTransform(Qs("a*f(t + 1)*Heaviside(t + 1)", [symbol("a", { positive: true })]), V(Qs("t", [symbol("a", { positive: true })])), Qs("s", [symbol("a", { positive: true })])), "(a*LaplaceTransform(f(t + 1), t, s), -oo, True)"],
    ["laplaceTransform(Qs(\"b*f(t/a)\", [symbol(\"b\", { positive: true }), symbol(\"a\", { positive: true })]), V(Qs(\"t\", [symbol(\"b\", { positive: true }), symbol(\"a\", { positive: true })])), Qs(\"s\", [symbol(\"b\", { positive: true }), symbol(\"a\", { positive: true })]))", () => laplaceTransform(Qs("b*f(t/a)", [symbol("b", { positive: true }), symbol("a", { positive: true })]), V(Qs("t", [symbol("b", { positive: true }), symbol("a", { positive: true })])), Qs("s", [symbol("b", { positive: true }), symbol("a", { positive: true })])), "(a*b*LaplaceTransform(f(t), t, a*s), -oo, True)"],
    ["laplaceTransform(P(\"exp(-t*f(x))\"), V(P(\"t\")), P(\"s\"))", () => laplaceTransform(P("exp(-t*f(x))"), V(P("t")), P("s")), "(1/(s + f(x)), -re(f(x)), True)"],
    ["laplaceTransform(Qs(\"f(t)*exp(-a*t)\", [symbol(\"a\", { positive: true })]), V(Qs(\"t\", [symbol(\"a\", { positive: true })])), Qs(\"s\", [symbol(\"a\", { positive: true })]))", () => laplaceTransform(Qs("f(t)*exp(-a*t)", [symbol("a", { positive: true })]), V(Qs("t", [symbol("a", { positive: true })])), Qs("s", [symbol("a", { positive: true })])), "(LaplaceTransform(f(t), t, a + s), -oo, True)"],
    ["laplaceTransform(Qs(\"f(t)*sinh(a*t)\", [symbol(\"a\", { positive: true })]), V(Qs(\"t\", [symbol(\"a\", { positive: true })])), Qs(\"s\", [symbol(\"a\", { positive: true })]))", () => laplaceTransform(Qs("f(t)*sinh(a*t)", [symbol("a", { positive: true })]), V(Qs("t", [symbol("a", { positive: true })])), Qs("s", [symbol("a", { positive: true })])), "(LaplaceTransform(f(t), t, -a + s)/2 - LaplaceTransform(f(t), t, a + s)/2, -oo, True)"],
    ["laplaceTransform(Qs(\"f(t)*cosh(a*t)\", [symbol(\"a\", { positive: true })]), V(Qs(\"t\", [symbol(\"a\", { positive: true })])), Qs(\"s\", [symbol(\"a\", { positive: true })]))", () => laplaceTransform(Qs("f(t)*cosh(a*t)", [symbol("a", { positive: true })]), V(Qs("t", [symbol("a", { positive: true })])), Qs("s", [symbol("a", { positive: true })])), "(LaplaceTransform(f(t), t, -a + s)/2 + LaplaceTransform(f(t), t, a + s)/2, -oo, True)"],
    ["laplaceTransform(Qs(\"f(t)*sin(a*t)\", [symbol(\"a\", { positive: true })]), V(Qs(\"t\", [symbol(\"a\", { positive: true })])), Qs(\"s\", [symbol(\"a\", { positive: true })]), { simplify: true })", () => laplaceTransform(Qs("f(t)*sin(a*t)", [symbol("a", { positive: true })]), V(Qs("t", [symbol("a", { positive: true })])), Qs("s", [symbol("a", { positive: true })]), { simplify: true }), "(I*(-LaplaceTransform(f(t), t, -I*a + s) + LaplaceTransform(f(t), t, I*a + s))/2, -oo, True)"],
    ["laplaceTransform(P(\"sin(f(t))\"), V(P(\"t\")), P(\"s\"))", () => laplaceTransform(P("sin(f(t))"), V(P("t")), P("s")), "(LaplaceTransform(sin(f(t)), t, s), -oo, True)"],
    ["laplaceTransform(Qs(\"f(t)*cos(a*t)\", [symbol(\"a\", { positive: true })]), V(Qs(\"t\", [symbol(\"a\", { positive: true })])), Qs(\"s\", [symbol(\"a\", { positive: true })]))", () => laplaceTransform(Qs("f(t)*cos(a*t)", [symbol("a", { positive: true })]), V(Qs("t", [symbol("a", { positive: true })])), Qs("s", [symbol("a", { positive: true })])), "(LaplaceTransform(f(t), t, -I*a + s)/2 + LaplaceTransform(f(t), t, I*a + s)/2, -oo, True)"],
    ["laplaceTransform(P(\"t**2*exp(-t**2)\"), V(P(\"t\")), P(\"s\"))", () => laplaceTransform(P("t**2*exp(-t**2)"), V(P("t")), P("s")), "(sqrt(pi)*s**2*exp(s**2/4)*erfc(s/2)/8 - s/4 + sqrt(pi)*exp(s**2/4)*erfc(s/2)/4, 0, True)"],
    ["laplaceTransform(Qs(\"(a*t**2 + b*t + c)*f(t)\", [symbol(\"b\", { positive: true }), symbol(\"a\", { positive: true }), symbol(\"c\", { positive: true })]), V(Qs(\"t\", [symbol(\"b\", { positive: true }), symbol(\"a\", { positive: true }), symbol(\"c\", { positive: true })])), Qs(\"s\", [symbol(\"b\", { positive: true }), symbol(\"a\", { positive: true }), symbol(\"c\", { positive: true })]))", () => laplaceTransform(Qs("(a*t**2 + b*t + c)*f(t)", [symbol("b", { positive: true }), symbol("a", { positive: true }), symbol("c", { positive: true })]), V(Qs("t", [symbol("b", { positive: true }), symbol("a", { positive: true }), symbol("c", { positive: true })])), Qs("s", [symbol("b", { positive: true }), symbol("a", { positive: true }), symbol("c", { positive: true })])), "(a*Derivative(LaplaceTransform(f(t), t, s), (s, 2)) - b*Derivative(LaplaceTransform(f(t), t, s), s) + c*LaplaceTransform(f(t), t, s), -oo, True)"],
    ["laplaceTransform(Qs(\"Heaviside(t)*besseli(0, sqrt(b)*t/sqrt(a))/sqrt(a)\", [symbol(\"b\", { positive: true }), symbol(\"a\", { positive: true })]), V(Qs(\"t\", [symbol(\"b\", { positive: true }), symbol(\"a\", { positive: true })])), Qs(\"s\", [symbol(\"b\", { positive: true }), symbol(\"a\", { positive: true })]))", () => laplaceTransform(Qs("Heaviside(t)*besseli(0, sqrt(b)*t/sqrt(a))/sqrt(a)", [symbol("b", { positive: true }), symbol("a", { positive: true })]), V(Qs("t", [symbol("b", { positive: true }), symbol("a", { positive: true })])), Qs("s", [symbol("b", { positive: true }), symbol("a", { positive: true })])), "(1/(sqrt(a)*sqrt(s**2 - b/a)), sqrt(b)/sqrt(a), True)"],
    ["laplaceTransform(P(\"Derivative(f(t), t)\"), V(P(\"t\")), P(\"s\"), { noconds: true })", () => laplaceTransform(P("Derivative(f(t), t)"), V(P("t")), P("s"), { noconds: true }), "s*LaplaceTransform(f(t), t, s) - f(0)"],
    ["laplaceTransform(P(\"10*Derivative(f(t), t)\"), V(P(\"t\")), P(\"s\"), { noconds: true })", () => laplaceTransform(P("10*Derivative(f(t), t)"), V(P("t")), P("s"), { noconds: true }), "10*s*LaplaceTransform(f(t), t, s) - 10*f(0)"],
    ["laplaceTransform(Qs(\"a*f(b*t) + g(c*t)\", [symbol(\"b\", { positive: true }), symbol(\"a\", { positive: true }), symbol(\"c\", { positive: true })]), V(Qs(\"t\", [symbol(\"b\", { positive: true }), symbol(\"a\", { positive: true }), symbol(\"c\", { positive: true })])), Qs(\"s\", [symbol(\"b\", { positive: true }), symbol(\"a\", { positive: true }), symbol(\"c\", { positive: true })]), { noconds: true })", () => laplaceTransform(Qs("a*f(b*t) + g(c*t)", [symbol("b", { positive: true }), symbol("a", { positive: true }), symbol("c", { positive: true })]), V(Qs("t", [symbol("b", { positive: true }), symbol("a", { positive: true }), symbol("c", { positive: true })])), Qs("s", [symbol("b", { positive: true }), symbol("a", { positive: true }), symbol("c", { positive: true })]), { noconds: true }), "a*LaplaceTransform(f(t), t, s/b)/b + LaplaceTransform(g(t), t, s/c)/c"],
    ["laplaceTransform(P(\"f(t)*g(t)\"), V(P(\"t\")), P(\"s\"), { noconds: true })", () => laplaceTransform(P("f(t)*g(t)"), V(P("t")), P("s"), { noconds: true }), "LaplaceTransform(f(t)*g(t), t, s)"],
    ["laplaceTransform(Qs(\"b*f(a*t)\", [symbol(\"b\", { positive: true }), symbol(\"a\", { positive: true })]), V(Qs(\"t\", [symbol(\"b\", { positive: true }), symbol(\"a\", { positive: true })])), Qs(\"s\", [symbol(\"b\", { positive: true }), symbol(\"a\", { positive: true })]), { noconds: true })", () => laplaceTransform(Qs("b*f(a*t)", [symbol("b", { positive: true }), symbol("a", { positive: true })]), V(Qs("t", [symbol("b", { positive: true }), symbol("a", { positive: true })])), Qs("s", [symbol("b", { positive: true }), symbol("a", { positive: true })]), { noconds: true }), "b*LaplaceTransform(f(t), t, s/a)/a"],
    ["laplaceTransform(P(\"3*exp(t)*Heaviside(t)\"), V(P(\"t\")), P(\"s\"))", () => laplaceTransform(P("3*exp(t)*Heaviside(t)"), V(P("t")), P("s")), "(3/(s - 1), 1, True)"],
    ["laplaceTransform(P(\"2*sin(t)*Heaviside(t)\"), V(P(\"t\")), P(\"s\"), { simplify: true })", () => laplaceTransform(P("2*sin(t)*Heaviside(t)"), V(P("t")), P("s"), { simplify: true }), "(2/(s**2 + 1), 0, True)"],
    ["laplaceTransform(Qs(\"(-a + t)**b*exp(-c*(-a + t))*Heaviside(-a + t)\", [symbol(\"b\", { positive: true }), symbol(\"a\", { positive: true }), symbol(\"c\", { positive: true })]), V(Qs(\"t\", [symbol(\"b\", { positive: true }), symbol(\"a\", { positive: true }), symbol(\"c\", { positive: true })])), Qs(\"s\", [symbol(\"b\", { positive: true }), symbol(\"a\", { positive: true }), symbol(\"c\", { positive: true })]))", () => laplaceTransform(Qs("(-a + t)**b*exp(-c*(-a + t))*Heaviside(-a + t)", [symbol("b", { positive: true }), symbol("a", { positive: true }), symbol("c", { positive: true })]), V(Qs("t", [symbol("b", { positive: true }), symbol("a", { positive: true }), symbol("c", { positive: true })])), Qs("s", [symbol("b", { positive: true }), symbol("a", { positive: true }), symbol("c", { positive: true })])), "((c + s)**(-b - 1)*exp(-a*s)*gamma(b + 1), -c, True)"],
    ["laplaceTransform(P(\"DiracDelta(t)\"), V(P(\"t\")), P(\"s\"))", () => laplaceTransform(P("DiracDelta(t)"), V(P("t")), P("s")), "(1, -oo, True)"],
    ["laplaceTransform(Qs(\"DiracDelta(a*t)\", [symbol(\"a\", { positive: true })]), V(Qs(\"t\", [symbol(\"a\", { positive: true })])), Qs(\"s\", [symbol(\"a\", { positive: true })]))", () => laplaceTransform(Qs("DiracDelta(a*t)", [symbol("a", { positive: true })]), V(Qs("t", [symbol("a", { positive: true })])), Qs("s", [symbol("a", { positive: true })])), "(1/a, -oo, True)"],
    ["laplaceTransform(P(\"DiracDelta(t/42)\"), V(P(\"t\")), P(\"s\"))", () => laplaceTransform(P("DiracDelta(t/42)"), V(P("t")), P("s")), "(42, -oo, True)"],
    ["laplaceTransform(P(\"DiracDelta(t + 42)\"), V(P(\"t\")), P(\"s\"))", () => laplaceTransform(P("DiracDelta(t + 42)"), V(P("t")), P("s")), "(0, -oo, True)"],
    ["laplaceTransform(P(\"DiracDelta(t) + DiracDelta(t - 42)\"), V(P(\"t\")), P(\"s\"))", () => laplaceTransform(P("DiracDelta(t) + DiracDelta(t - 42)"), V(P("t")), P("s")), "(1 + exp(-42*s), -oo, True)"],
    ["laplaceTransform(Qs(\"-a*exp(-a*t) + DiracDelta(t)\", [symbol(\"a\", { positive: true })]), V(Qs(\"t\", [symbol(\"a\", { positive: true })])), Qs(\"s\", [symbol(\"a\", { positive: true })]), { simplify: true })", () => laplaceTransform(Qs("-a*exp(-a*t) + DiracDelta(t)", [symbol("a", { positive: true })]), V(Qs("t", [symbol("a", { positive: true })])), Qs("s", [symbol("a", { positive: true })]), { simplify: true }), "(s/(a + s), -a, True)"],
    ["laplaceTransform(P(\"(DiracDelta(t) + DiracDelta(t - 42))*exp(-t)\"), V(P(\"t\")), P(\"s\"), { simplify: true })", () => laplaceTransform(P("(DiracDelta(t) + DiracDelta(t - 42))*exp(-t)"), V(P("t")), P("s"), { simplify: true }), "(exp(-42*s - 42) + 1, -oo, True)"],
    ["laplaceTransform(P(\"f(t)*DiracDelta(t - 42)\"), V(P(\"t\")), P(\"s\"))", () => laplaceTransform(P("f(t)*DiracDelta(t - 42)"), V(P("t")), P("s")), "(f(42)*exp(-42*s), -oo, True)"],
    ["laplaceTransform(Qs(\"f(t)*DiracDelta(-a + b*t)\", [symbol(\"b\", { positive: true }), symbol(\"a\", { positive: true })]), V(Qs(\"t\", [symbol(\"b\", { positive: true }), symbol(\"a\", { positive: true })])), Qs(\"s\", [symbol(\"b\", { positive: true }), symbol(\"a\", { positive: true })]))", () => laplaceTransform(Qs("f(t)*DiracDelta(-a + b*t)", [symbol("b", { positive: true }), symbol("a", { positive: true })]), V(Qs("t", [symbol("b", { positive: true }), symbol("a", { positive: true })])), Qs("s", [symbol("b", { positive: true }), symbol("a", { positive: true })])), "(f(a/b)*exp(-a*s/b)/b, -oo, True)"],
    ["laplaceTransform(Qs(\"f(t)*DiracDelta(a + b*t)\", [symbol(\"b\", { positive: true }), symbol(\"a\", { positive: true })]), V(Qs(\"t\", [symbol(\"b\", { positive: true }), symbol(\"a\", { positive: true })])), Qs(\"s\", [symbol(\"b\", { positive: true }), symbol(\"a\", { positive: true })]))", () => laplaceTransform(Qs("f(t)*DiracDelta(a + b*t)", [symbol("b", { positive: true }), symbol("a", { positive: true })]), V(Qs("t", [symbol("b", { positive: true }), symbol("a", { positive: true })])), Qs("s", [symbol("b", { positive: true }), symbol("a", { positive: true })])), "(0, -oo, True)"],
    ["laplaceTransform(Qs(\"SingularityFunction(t, a, x)\", [symbol(\"a\", { positive: true })]), V(Qs(\"t\", [symbol(\"a\", { positive: true })])), Qs(\"s\", [symbol(\"a\", { positive: true })]))", () => laplaceTransform(Qs("SingularityFunction(t, a, x)", [symbol("a", { positive: true })]), V(Qs("t", [symbol("a", { positive: true })])), Qs("s", [symbol("a", { positive: true })])), "(LaplaceTransform(SingularityFunction(t, a, x), t, s), -oo, True)"],
    ["laplaceTransform(P(\"DiracDelta(t**2)\"), V(P(\"t\")), P(\"s\"), { noconds: true })", () => laplaceTransform(P("DiracDelta(t**2)"), V(P("t")), P("s"), { noconds: true }), "LaplaceTransform(DiracDelta(t**2), t, s)"],
    ["laplaceTransform(P(\"DiracDelta(t**2 - 1)\"), V(P(\"t\")), P(\"s\"))", () => laplaceTransform(P("DiracDelta(t**2 - 1)"), V(P("t")), P("s")), "(exp(-s)/2, -oo, True)"],
    // SymPy 1.14: (1 - exp(-s), -oo, True); delta(t*(1 - t)) = delta(t) + delta(t - 1), each divided by |d/dt t*(1 - t)| = 1
    ["laplaceTransform(P(\"DiracDelta(t*(1 - t))\"), V(P(\"t\")), P(\"s\"))", () => laplaceTransform(P("DiracDelta(t*(1 - t))"), V(P("t")), P("s")), "(1 + exp(-s), -oo, True)"],
    ["laplaceTransform(P(\"(DiracDelta(t) + 1)*(DiracDelta(t - 1) + 1)\"), V(P(\"t\")), P(\"s\"))", () => laplaceTransform(P("(DiracDelta(t) + 1)*(DiracDelta(t - 1) + 1)"), V(P("t")), P("s")), "(LaplaceTransform(DiracDelta(t)*DiracDelta(t - 1), t, s) + 1 + exp(-s) + 1/s, 0, True)"],
    ["laplaceTransform(Qs(\"DiracDelta(2*t - 2*exp(a))\", [symbol(\"a\", { positive: true })]), V(Qs(\"t\", [symbol(\"a\", { positive: true })])), Qs(\"s\", [symbol(\"a\", { positive: true })]))", () => laplaceTransform(Qs("DiracDelta(2*t - 2*exp(a))", [symbol("a", { positive: true })]), V(Qs("t", [symbol("a", { positive: true })])), Qs("s", [symbol("a", { positive: true })])), "(exp(-s*exp(a))/2, -oo, True)"],
    ["laplaceTransform(Qs(\"DiracDelta(-2*t + 2*exp(a))\", [symbol(\"a\", { positive: true })]), V(Qs(\"t\", [symbol(\"a\", { positive: true })])), Qs(\"s\", [symbol(\"a\", { positive: true })]))", () => laplaceTransform(Qs("DiracDelta(-2*t + 2*exp(a))", [symbol("a", { positive: true })]), V(Qs("t", [symbol("a", { positive: true })])), Qs("s", [symbol("a", { positive: true })])), "(exp(-s*exp(a))/2, -oo, True)"],
    ["laplaceTransform(P(\"Heaviside(t)\"), V(P(\"t\")), P(\"s\"))", () => laplaceTransform(P("Heaviside(t)"), V(P("t")), P("s")), "(1/s, 0, True)"],
    ["laplaceTransform(Qs(\"Heaviside(-a + t)\", [symbol(\"a\", { positive: true })]), V(Qs(\"t\", [symbol(\"a\", { positive: true })])), Qs(\"s\", [symbol(\"a\", { positive: true })]))", () => laplaceTransform(Qs("Heaviside(-a + t)", [symbol("a", { positive: true })]), V(Qs("t", [symbol("a", { positive: true })])), Qs("s", [symbol("a", { positive: true })])), "(exp(-a*s)/s, 0, True)"],
    ["laplaceTransform(P(\"Heaviside(t - 1)\"), V(P(\"t\")), P(\"s\"))", () => laplaceTransform(P("Heaviside(t - 1)"), V(P("t")), P("s")), "(exp(-s)/s, 0, True)"],
    ["laplaceTransform(P(\"Heaviside(2*t - 4)\"), V(P(\"t\")), P(\"s\"))", () => laplaceTransform(P("Heaviside(2*t - 4)"), V(P("t")), P("s")), "(exp(-2*s)/s, 0, True)"],
    ["laplaceTransform(P(\"Heaviside(2*t + 4)\"), V(P(\"t\")), P(\"s\"))", () => laplaceTransform(P("Heaviside(2*t + 4)"), V(P("t")), P("s")), "(1/s, 0, True)"],
    ["laplaceTransform(P(\"g(t)*Heaviside(t - w)\"), V(P(\"t\")), P(\"s\"))", () => laplaceTransform(P("g(t)*Heaviside(t - w)"), V(P("t")), P("s")), "(LaplaceTransform(g(t)*Heaviside(t - w), t, s), -oo, True)"],
    ["laplaceTransform(Qs(\"g(t)*Heaviside(a + t)\", [symbol(\"a\", { positive: true })]), V(Qs(\"t\", [symbol(\"a\", { positive: true })])), Qs(\"s\", [symbol(\"a\", { positive: true })]))", () => laplaceTransform(Qs("g(t)*Heaviside(a + t)", [symbol("a", { positive: true })]), V(Qs("t", [symbol("a", { positive: true })])), Qs("s", [symbol("a", { positive: true })])), "(LaplaceTransform(g(t), t, s), -oo, True)"],
    ["laplaceTransform(Qs(\"g(t)*Heaviside(-a - t)\", [symbol(\"a\", { positive: true })]), V(Qs(\"t\", [symbol(\"a\", { positive: true })])), Qs(\"s\", [symbol(\"a\", { positive: true })]))", () => laplaceTransform(Qs("g(t)*Heaviside(-a - t)", [symbol("a", { positive: true })]), V(Qs("t", [symbol("a", { positive: true })])), Qs("s", [symbol("a", { positive: true })])), "(0, 0, True)"],
  ];

  it.each(cases)('%s', (_name, run, want) => {
    expect(show(run())).toBe(want);
  });
});

// Coverage of integrals/transforms/laplace.ts. Expected values are the str() forms printed by
// SymPy 1.14 unless a comment says otherwise.

const a = symbol('a', { positive: true });
const b = symbol('b', { real: true });
const [t, s, x, y] = symbols('t s x y');
const p = symbol('p', { positive: true });
const n = symbol('n', { integer: true, positive: true });
const Ps = (e: string) => parse(e, { symbols: [a, b, p, n, t, s, x, y], locals: { Heaviside, DiracDelta, Eq, Ne } });
const L = (e: string): string => show(laplaceTransform(Ps(e), t, s));
const LE = (e: Expr): string => show(laplaceTransform(e, t, s));

describe('laplace: simplifyConds and laplaceDeepCollect', () => {
  it('_simplifyconds cases', () => {
    const cases: [string, number, string][] = [
      ['Abs(x)*Abs(y) < 1', 1, 'Abs(x*y) < 1'],
      ['Abs(x)*p < 1', 1, 'p*Abs(x) < 1'],
      ['1 < Abs(2*x)', 1, '1 < 2*Abs(x)'],
      ['Abs(x**2) > 1', 1, 'True'],
      ['1 > Abs(x**2)', 1, 'False'],
      ['x < 1', 1, 'x < 1'],
      ['Abs(x) <= 1', 1, 'Abs(x) <= 1'],
      ['Eq(x, 1)', 1, 'Eq(x, 1)'],
      ['1 < Abs(x**I)', 1, '1 < Abs(x**I)'],
      ['Ne(1, 2*x)', 1, 'Ne(1, 2*x)'],
      ['1 < Abs(y)**2', 1, '1 < Abs(y)**2'],
      ['Ne(x, 0)', 1, 'True'],
      ['Ne(x, x**2)', 1, 'Ne(x, x**2)'],
    ];
    for (const [e, A, want] of cases) expect(String(simplifyConds(Ps(e), x, A)), e).toBe(want);
    // symjs writes Abs(x**2) as Abs(x)**2 and Abs(1/x) as 1/Abs(x) (SymPy: Abs(x) < Abs(x**2), 1 < Abs(1/x))
    expect(String(simplifyConds(Ps('Abs(x) < Abs(x**2)'), x, 1))).toBe('Abs(x) < Abs(x)**2');
    expect(String(simplifyConds(Ps('1 < Abs(1/x)'), x, 0))).toBe('1 < 1/Abs(x)');
  });
  it('an atom that is not a polynomial is kept', () => {
    expect(String(laplaceDeepCollect(Ps('oo'), t))).toBe('oo');
  });
});

describe('laplace: rule table', () => {
  it('table entries', () => {
    const cases: [string, string][] = [
      ['1/(a*sqrt(t)+t**1.5)', '(pi*sqrt(a)*exp(a*s)*erfc(sqrt(a)*sqrt(s)), 0, True)'],
      ['log(a*t)', '(-log(s*exp(EulerGamma)/a)/s, 0, True)'],
      ['log(2*t)', '(-log(s*exp(EulerGamma)/2)/s, 0, True)'],
      // 4.6.9 is skipped as in SymPy; 4.6.11 with n = -1/2 applies
      ['log(t)/sqrt(t)', '(sqrt(pi)*(-log(s) - 2*log(2) - EulerGamma)/sqrt(s), 0, True)'],
      ['log(a*t)**2', '((log(s*exp(EulerGamma)/a)**2 + pi**2/6)/s, 0, True)'],
      ['log(t)**2', '((log(s*exp(EulerGamma))**2 + pi**2/6)/s, 0, True)'],
      ['cosh(a*t)**2', '((-2*a**2 + s**2)/(-4*a**2*s + s**3), 2*a, True)'],
      ['cosh(b*t)**2', '((-2*b**2 + s**2)/(-4*b**2*s + s**3), 2*Abs(b), True)'],
    ];
    for (const [e, want] of cases) expect(L(e), e).toBe(want);
  });
  it('the rational exponent 3/2 of 4.2.18b', () => {
    // SymPy writes the pattern with the float 1.5 and leaves the rational form unevaluated
    // (LaplaceTransform(1/(a*sqrt(t) + t**(3/2)), t, s), -oo, True); the integral has the same value
    expect(L('1/(a*sqrt(t)+t**(3/2))')).toBe('(pi*sqrt(a)*exp(a*s)*erfc(sqrt(a)*sqrt(s)), 0, True)');
  });
});

describe('laplace: DiracDelta and Heaviside', () => {
  it('delta rules', () => {
    const cases: [string, string][] = [
      ['DiracDelta(t**2-1)', '(exp(-s)/2, -oo, True)'],
      ['DiracDelta(t**2+1)*t', '(0, -oo, True)'],
      ['DiracDelta((t-1)**2)*t', '(-Derivative(LaplaceTransform(DiracDelta(t**2 - 2*t + 1), t, s), s), -oo, True)'],
      ['DiracDelta(t**5-t-1)*t', '(-Derivative(LaplaceTransform(DiracDelta(t**5 - t - 1), t, s), s), -oo, True)'],
      ['DiracDelta(t+1)*t', '(0, -oo, True)'],
      ['DiracDelta(-2*t-2)*t', '(0, -oo, True)'],
      ['DiracDelta(t-I)*t', '(0, -oo, True)'],
      ['DiracDelta(t-1)*cos(t)', '(exp(-s)*cos(1), -oo, True)'],
      ['DiracDelta(t-1)*sin(t-1)/(t-1)', '(exp(-s), -oo, True)'],
      ['DiracDelta(t-1)/(t-1)', '(LaplaceTransform(DiracDelta(t - 1)/(t - 1), t, s), -oo, True)'],
      ['DiracDelta(exp(t)-2)*t', '(-Derivative(LaplaceTransform(DiracDelta(exp(t) - 2), t, s), s), -oo, True)'],
      ['DiracDelta(2-2*t)', '(exp(-s)/2, -oo, True)'],
    ];
    for (const [e, want] of cases) expect(L(e), e).toBe(want);
  });
  it('delta rules where SymPy 1.14 is wrong', () => {
    // integral of t*delta(t**2 - 1)*exp(-s*t) = 1*exp(-s)/|2*1|; SymPy gives s*exp(-s)/2
    expect(L('DiracDelta(t**2-1)*t')).toBe('(exp(-s)/2, -oo, True)');
    // delta(1 - t**2) = delta(t**2 - 1); SymPy gives -s*exp(-s)/2
    expect(L('DiracDelta(1-t**2)*t')).toBe('(exp(-s)/2, -oo, True)');
    // delta(2 - 2*t) = delta(t - 1)/2; SymPy gives -exp(-s)/2 and -E*exp(-s)/2
    expect(L('DiracDelta(-2*t+2)*t')).toBe('(exp(-s)/2, -oo, True)');
    expect(L('DiracDelta(2-2*t)*exp(t)')).toBe('(E*exp(-s)/2, -oo, True)');
  });
  it('a delta at an undecided point stays unevaluated', () => {
    // SymPy raises TypeError: cannot determine truth value of Relational: b >= 0
    expect(L('DiracDelta(t-b)')).toBe('(LaplaceTransform(DiracDelta(-b + t), t, s), -oo, True)');
    expect(L('DiracDelta(t-b)*t')).toBe('(-Derivative(LaplaceTransform(DiracDelta(-b + t), t, s), s), -oo, True)');
  });
  it('Heaviside rules', () => {
    // SymPy raises AttributeError ('int' object has no attribute 'xreplace') on the first two;
    // the step vanishes for t > 0
    expect(L('Heaviside(-t-1)')).toBe('(0, 0, True)');
    expect(L('Heaviside(-2*t-3)*t')).toBe('(0, 0, True)');
    expect(L('Heaviside(1-t)*t')).toBe('(-exp(-s)/s + s**(-2) - exp(-s)/s**2, 0, True)');
    expect(L('Heaviside(-1-t)*t')).toBe('(0, 0, True)');
    expect(L('Heaviside((t+1)**2-t**2-2*t)')).toBe('(1/s, 0, True)');
  });
});

describe('laplace: program rules', () => {
  it('time scaling, trigonometric factors, derivatives, polynomial factors', () => {
    const cases: [string, string][] = [
      ['f(2*t)', '(LaplaceTransform(f(t), t, s/2)/2, -oo, True)'],
      ['besselk(1,2*t)', '(LaplaceTransform(besselk(1, 2*t), t, s), -oo, True)'],
      ['sin(t)*sinh(t)', '(2*s/(s**4 + 4), 1, True)'],
      ['cos(t)*cosh(t)', '(s**3/(s**4 + 4), 1, True)'],
      ['t*Derivative(f(t),t)', '(-Derivative(s*LaplaceTransform(f(t), t, s) - f(0), s), -oo, True)'],
      ['Derivative(f(t,x),x)', '(LaplaceTransform(Derivative(f(t, x), x), t, s), -oo, True)'],
      ['Derivative(f(t,t),t)', '(LaplaceTransform(Derivative(f(t, t), t), t, s), -oo, True)'],
      ['Derivative(f(t)*g(t),t)', '(LaplaceTransform(Derivative(f(t)*g(t), t), t, s), -oo, True)'],
      ['((t+1)**2-t**2-2*t)*besselk(1,t)', '(LaplaceTransform(besselk(1, t), t, s), -oo, True)'],
      ['t*besselk(1,t)', '(-Derivative(LaplaceTransform(besselk(1, t), t, s), s), -oo, True)'],
      ['t*DiracDelta(t)', '(0, -oo, True)'],
      ['(t+1)*DiracDelta(t)', '(1, -oo, True)'],
    ];
    for (const [e, want] of cases) expect(L(e), e).toBe(want);
  });
  it('expansion', () => {
    const cases: [string, string][] = [
      // SymPy prints the same terms in the order 2*LaplaceTransform(sqrt(t)*f(t), t, s) + LaplaceTransform(f(t), t, s)
      // - Derivative(LaplaceTransform(f(t), t, s), s) (the str printer's term order is not laplace's)
      ['f(t)*(sqrt(t)+1)**2', '(-Derivative(LaplaceTransform(f(t), t, s), s) + 2*LaplaceTransform(sqrt(t)*f(t), t, s) + LaplaceTransform(f(t), t, s), -oo, True)'],
      // SymPy's match picks the factor exp(t**2), which is not exp(a*t), and gives
      // (LaplaceTransform(f(t)*exp(t)*exp(t**2), t, s), -oo, True); symjs takes exp(t) and shifts s
      ['f(t)*exp(t*(t+1))', '(LaplaceTransform(f(t)*exp(t**2), t, s - 1), -oo, True)'],
      ['f(t)*sin(t**2+t)', '(LaplaceTransform(f(t)*sin(t)*cos(t**2), t, s) + LaplaceTransform(f(t)*sin(t**2)*cos(t), t, s), -oo, True)'],
      ['f(t)*log(2*(t+1))', '(LaplaceTransform(f(t)*log(2*t + 2), t, s), -oo, True)'],
    ];
    for (const [e, want] of cases) expect(L(e), e).toBe(want);
  });
  it('expansion of a logarithm of a positive variable', () => {
    const tp = symbol('t', { positive: true });
    // SymPy prints the second term as LaplaceTransform(f(t), t, s)*log(2) (the str printer's factor order)
    expect(show(laplaceTransform(parse('f(t)*log(2*t)', { symbols: [tp] }), tp, s))).toBe('(LaplaceTransform(f(t)*log(t), t, s) + log(2)*LaplaceTransform(f(t), t, s), -oo, True)');
  });
  it('a symbolic power of t', () => {
    // SymPy: ((-1)**n*Derivative(LaplaceTransform(besselk(1, t), t, s), (s, n)), -oo, True); symjs's
    // Derivative needs a numeric order, so the transform stays unevaluated
    expect(L('t**n*besselk(1,t)')).toBe('(LaplaceTransform(t**n*besselk(1, t), t, s), -oo, True)');
    // SymPy integrates with the Meijer G method: (4*2**(m - 3)*meijerg(((-m/2, 1 - m/2), ()), ((0, 1/2), ()),
    // polar_lift(s)**2)/sqrt(pi), 0, (re(m) > -3) & ...); symjs has no Meijer G integration here
    expect(L('t**y*besselk(1,t)')).toBe('(LaplaceTransform(t**y*besselk(1, t), t, s), -oo, True)');
  });
});

describe('laplace: Piecewise input', () => {
  it('conditions written in any orientation, and linear in t', () => {
    // SymPy's Piecewise canonicalizes 2 < t to t > 2 and 2*t > 5 to t > 5/2
    expect(LE(Piecewise([1, or(Lt(2, t), Lt(t, 1))], [0, true]))).toBe('((1 - exp(-s))/s + exp(-2*s)/s, 0, True)');
    expect(LE(Piecewise([1, and(Lt(1, t), Lt(t, 2))], [0, true]))).toBe('(exp(-s)/s - exp(-2*s)/s, 0, True)');
    expect(LE(Piecewise([1, and(Gt(2, t), Ge(t, 1))], [0, true]))).toBe('(exp(-s)/s - exp(-2*s)/s, 0, True)');
    expect(LE(Piecewise([1, or(Lt(t, 1), Gt(mul(2, t), 5))], [0, true]))).toBe('((1 - exp(-s))/s + exp(-5*s/2)/s, 0, True)');
    expect(LE(Piecewise([1, and(Gt(t, 1), Lt(mul(2, t), 5))], [0, true]))).toBe('(exp(-s)/s - exp(-5*s/2)/s, 0, True)');
    expect(LE(Piecewise([1, Gt(mul(2, t), 1)], [0, true]))).toBe('(exp(-s/2)/s, 0, True)');
  });
  it('a first piece that never applies', () => {
    // SymPy 1.14 gives (0, 0, True): piecewise_exclusive returns t, whose (empty) args
    // _piecewise_to_heaviside turns into 0; the function is t for t > 0
    expect(LE(Piecewise([1, and(Gt(t, 1), Lt(t, 0))], [t, true]))).toBe('(s**(-2), 0, True)');
  });
  it('conditions left to the integration', () => {
    const unevaluated = (e: Expr): string => `(LaplaceTransform(${String(e)}, t, s), -oo, True)`;
    // SymPy integrates to (0, -oo, True) (a single point)
    const eq = Piecewise([1, Eq(t, 1)], [0, true]);
    expect(LE(eq)).toBe(unevaluated(eq));
    // SymPy raises AttributeError: 'Equality' object has no attribute 'gts' (and 'Unequality')
    for (const e of [Piecewise([1, or(Eq(t, 1), Gt(t, 2))], [0, true]), Piecewise([1, and(Ne(t, 1), Lt(t, 2))], [0, true])]) expect(LE(e)).toBe(unevaluated(e));
    // SymPy writes the indicator of t > 2 as Heaviside(t - 1) - Heaviside(2 - t), which is wrong
    const same = Piecewise([1, and(Gt(t, 1), Gt(t, 2))], [0, true]);
    expect(LE(same)).toBe(unevaluated(same));
    // three conditions and a condition that is not linear: SymPy also returns f to the integration
    const three = Piecewise([1, and(Lt(1, t), Lt(t, 2), Le(t, 3))], [0, true]);
    expect(LE(three)).toBe(unevaluated(three));
    const quad = Piecewise([1, Gt(mul(t, t), 1)], [0, true]);
    expect(LE(quad)).toBe(unevaluated(quad));
    // SymPy: (exp(-s*y)/s, 0, True) for y > 0 and unevaluated for (y > 2) | (t < 1); symjs's
    // piecewise_exclusive takes conditions in t only
    const yp = symbol('y', { positive: true });
    for (const e of [Piecewise([1, Gt(t, yp)], [0, true]), Piecewise([1, or(Lt(t, 1), Gt(yp, 2))], [0, true])]) expect(LE(e)).toBe(unevaluated(e));
  });
});

describe('laplace: integration and the LaplaceTransform class', () => {
  it('powers of t whose integral diverges at 0', () => {
    expect(L('1/t')).toBe('(LaplaceTransform(1/t, t, s), -oo, True)');
    expect(L('t**(-3/2)')).toBe('(LaplaceTransform(t**(-3/2), t, s), -oo, True)');
  });
  it('a rule check that cannot be decided', () => {
    // re(zoo) is nan, which cannot be ordered: the rule for besselj is skipped (SymPy raises
    // TypeError: Invalid NaN comparison)
    expect(L('besselj(zoo, t)')).toBe('(LaplaceTransform(besselj(zoo, t), t, s), -oo, True)');
  });
  it('a Heaviside factor with an undecided sign', () => {
    expect(L('Heaviside(y-t)*besselk(1,t)')).toBe('(LaplaceTransform(besselk(1, t)*Heaviside(-t + y), t, s), -oo, True)');
  });
  it('transformName and doit', () => {
    const F = new LaplaceTransform(Ps('t**2'), t, s);
    expect(F.transformName).toBe('Laplace');
    expect(show(F.doit({ noconds: false }))).toBe('(2/s**3, 0, True)');
    // a function variable that is not a symbol leaves the transform unevaluated
    // (SymPy evaluates LaplaceTransform(2, 2, s).doit() to s**(-2))
    const G = new LaplaceTransform(2, 2, s);
    expect(String(G.doit())).toBe('LaplaceTransform(2, 2, s)');
  });
});
