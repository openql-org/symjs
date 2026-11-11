// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/integrals/public.ts: the public forms of the integrator helpers. Expected values are those of
// the doctests of SymPy 1.14 (sympy.integrals.rationaltools, trigonometry, deltafunctions, meijerint, heurisch).

import { describe, expect, it } from 'vitest';
import { DiracDelta, Heaviside, Poly, S, Sym, isNoMatch, parse, sstr, type Expr } from '../../src';
import {
  changeMul,
  components,
  deltaintegrate,
  heurisch,
  heurischWrapper,
  logToReal,
  meijerintDefinite,
  meijerintIndefinite,
  meijerintInversion,
  ratint,
  ratintLogpart,
  trigintegrate,
} from '../../src/integrals/public';

const [x, y, z, n, t] = [new Sym('x'), new Sym('y'), new Sym('z'), new Sym('n'), new Sym('t')];
const P = (q: string): Expr => parse(q, { symbols: [x, y, z, n, t], locals: { DiracDelta, Heaviside } });
const show = (v: unknown): string => (isNoMatch(v) ? 'None' : Array.isArray(v) ? `(${v.map(show).join(', ')})` : sstr(v as Expr));

describe('rationaltools', () => {
  it('ratint', () => {
    expect(show(ratint(P('36/(x**5 - 2*x**4 - 2*x**3 + 4*x**2 + x - 2)'), x))).toBe('(12*x + 6)/(x**2 - 1) + 4*log(x - 2) - 4*log(x + 1)');
    expect(show(ratint(P('sin(x)'), x))).toBe('None');
  });
  it('ratint_logpart with a new Dummy t', () => {
    const [[h, q]] = ratintLogpart(Poly.from(P('12'), [x]), Poly.from(P('x**2 - x - 2'), [x]), x) as [[Poly, Poly]];
    expect(sstr(h.asExpr())).toBe('-3*_t/8 + x - 1/2');
    expect(sstr(q.asExpr())).toBe('16 - _t**2');
  });
  it('log_to_real', () => {
    expect(show(logToReal(Poly.from(P('x**2 - 1'), [x]), Poly.from(P('-2*y + 1'), [y]), x, y))).toBe('log(x**2 - 1)/2');
    // the real roots of an irreducible cubic are not written here (SymPy: None)
    expect(show(logToReal(Poly.from(P('x - y'), [x]), Poly.from(P('y**3 + y + 1'), [y]), x, y))).toBe('None');
  });
});

describe('trigintegrate', () => {
  it('rewrites tan, cot, sec and csc with sin and cos', () => {
    expect(show(trigintegrate(P('sin(x)*cos(x)'), x))).toBe('sin(x)**2/2');
    expect(show(trigintegrate(P('tan(x)*sec(x)'), x))).toBe('1/cos(x)');
    expect(show(trigintegrate(P('sin(x)*tan(x)'), x))).toBe('-log(sin(x) - 1)/2 + log(sin(x) + 1)/2 - sin(x)');
    expect(show(trigintegrate(P('cot(x)*csc(x)'), x))).toBe('-1/sin(x)');
  });
  it('gives None for other integrands', () => {
    expect(show(trigintegrate(P('log(x)*sin(x)'), x))).toBe('None');
    expect(show(trigintegrate(P('atan2(x, y)'), x))).toBe('None');
  });
});

describe('deltafunctions', () => {
  it('deltaintegrate', () => {
    expect(show(deltaintegrate(P('x*sin(x)*cos(x)*DiracDelta(x - 1)'), x))).toBe('sin(1)*cos(1)*Heaviside(x - 1)');
    expect(show(deltaintegrate(P('x'), x))).toBe('None');
  });
  it('change_mul', () => {
    expect(show(changeMul(P('x*y*DiracDelta(x)*cos(x)'), x))).toBe('(DiracDelta(x), x*y*cos(x))');
    expect(show(changeMul(P('x*y*DiracDelta(cos(x))*cos(x)'), x))).toBe('(None, None)');
  });
});

describe('meijerint', () => {
  it('meijerint_definite', () => {
    expect(show(meijerintDefinite(P('exp(-x**2)'), x, S.NegativeInfinity, S.Infinity))).toBe('(sqrt(pi), True)');
    expect(show(meijerintDefinite(P('DiracDelta(x)'), x, 0, 1))).toBe('None');
  });
  it('meijerint_indefinite', () => {
    expect(show(meijerintIndefinite(P('sin(x)'), x))).toBe('-cos(x)');
    expect(show(meijerintIndefinite(P('exp(exp(x))'), x))).toBe('None');
  });
  it('meijerint_inversion', () => {
    expect(show(meijerintInversion(P('1/x'), x, t))).toBe('Heaviside(t)');
    expect(show(meijerintInversion(P('Heaviside(x)'), x, t))).toBe('None');
  });
});

describe('heurisch', () => {
  it('components', () => {
    expect(components(P('sin(x)*cos(x)**2'), x).args.map((e) => sstr(e)).sort()).toEqual(['cos(x)', 'sin(x)', 'x']);
  });
  it('heurisch and heurisch_wrapper', () => {
    expect(show(heurisch(P('y*tan(x)'), x))).toBe('y*log(tan(x)**2 + 1)/2');
    expect(show(heurisch(P('cos(n*x)'), x))).toBe('sin(n*x)/n');
    expect(show(heurischWrapper(P('cos(n*x)'), x))).toBe('Piecewise((sin(n*x)/n, Ne(n, 0)), (x, True))');
    expect(show(heurisch(P('Abs(x)'), x))).toBe('None');
    expect(show(heurischWrapper(P('Abs(x)'), x))).toBe('None');
  });
});
