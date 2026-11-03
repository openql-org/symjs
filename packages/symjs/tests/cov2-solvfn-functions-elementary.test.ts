// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Coverage of functions/elementary.ts (and the cot/sec/csc reductions of trigext.ts).
// Expected values are str() results of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { AccumBounds, Float, cosh, S, Sym, abs, add, adjoint, arg, conjugate, fn, hyper, mul, parse, pow, sin, transpose } from '../src';

const x = new Sym('x');
const r = new Sym('r', { real: true });

const cases: [string, string][] = [
  // rational multiples of pi outside the tables (SymPy sin/cos/tan.eval reductions)
  ['sin(8*pi/7)', '-sin(pi/7)'],
  ['sin(-8*pi/7)', 'sin(pi/7)'],
  ['sin(5*pi/7)', 'sin(2*pi/7)'],
  ['sin(pi/7)', 'sin(pi/7)'],
  ['sin(13*pi/7)', '-sin(pi/7)'],
  ['sin(15*pi/7)', 'sin(pi/7)'],
  ['cos(8*pi/7)', '-cos(pi/7)'],
  ['cos(-5*pi/7)', '-cos(2*pi/7)'],
  ['cos(5*pi/7)', '-cos(2*pi/7)'],
  ['cos(13*pi/7)', 'cos(pi/7)'],
  ['cos(15*pi/7)', 'cos(15*pi/7)'],
  ['cos(23*pi/7)', '-cos(2*pi/7)'],
  ['tan(5*pi/7)', '-tan(2*pi/7)'],
  ['tan(-8*pi/7)', '-tan(pi/7)'],
  ['tan(13*pi/7)', '-tan(pi/7)'],
  ['tan(-pi/7)', '-tan(pi/7)'],
  ['tan(pi/7)', 'tan(pi/7)'],
  ['tan(pi/2)', 'zoo'],
  ['tan(3*pi/2)', 'zoo'],
  // _peeloff_pi: the multiple of pi/2 taken out of a sum
  ['sin(x + 8*pi/7)', '-sin(x + pi/7)'],
  ['sin(x - pi/3)', '-cos(x + pi/6)'],
  ['sin(x + 5*pi/4)', '-sin(x + pi/4)'],
  ['sin(-x - pi/3)', '-sin(x + pi/3)'],
  ['cos(x - pi/3)', 'sin(x + pi/6)'],
  ['cos(x + 2*pi)', 'cos(x)'],
  ['cos(x + 3*pi/2)', 'sin(x)'],
  ['cos(x + 5*pi/7)', '-sin(x + 3*pi/14)'],
  ['cot(9*pi/7)', 'cot(2*pi/7)'],
  ['cot(5*pi/7)', '-cot(2*pi/7)'],
  ['cot(pi/7)', 'cot(pi/7)'],
  ['cot(23*pi/7)', 'cot(2*pi/7)'],
  ['sec(23*pi/7)', '-sec(2*pi/7)'],
  ['csc(23*pi/7)', '-csc(2*pi/7)'],
  ['sec(5*pi/7)', '-sec(2*pi/7)'],
  ['csc(5*pi/7)', 'csc(2*pi/7)'],
  ['log(0)', 'zoo'],
  ['Abs(I*y + 1)', 'Abs(I*y + 1)'],
  ['Abs(f(1))', 'Abs(f(1))'],
  ['re((-1)**(1/7))', 'cos(pi/7)'],
  ['im((-1)**(1/7))', 'sin(pi/7)'],
  ['re(I**(1/7))', 'cos(pi/14)'],
  ['re(x*y)', 're(x*y)'],
  ['im(x*y)', 'im(x*y)'],
  ['re(2*I*y)', '-2*im(y)'],
  ['im(2*I*y)', '2*re(y)'],
  ['arg(I*(pi-3))', 'pi/2'],
  ['arg(pi - 3 + I)', 'atan(1/(-3 + pi))'],
  ['arg(-(pi-3)+I)', 'atan(1/(3 - pi)) + pi'],
  ['arg(-I*(pi-3))', '-pi/2'],
  ['arg(3-pi - I)', '-pi - atan(1/(3 - pi))'],
  ['f(1.5)', 'f(1.5)'],
  ['sin(1 + 2.5*I)', '5.1601436675797 + 3.26893943207955*I'],
  ['sin(1.5 + 2*I)', '3.7527713404793 + 0.256553956090482*I'],
];

describe('elementary evaluation', () => {
  it.each(cases)('%s', (src, want) => {
    expect(String(parse(src))).toBe(want);
  });
  it('Abs of a power of a real base', () => {
    // SymPy Abs(r**-3), Abs(r**5), Abs(1/r), Abs(r**3) for real r
    expect(String(abs(pow(r, -3)))).toBe('1/(r**2*Abs(r))');
    expect(String(abs(pow(r, 5)))).toBe('r**4*Abs(r)');
    expect(String(abs(pow(r, -1)))).toBe('1/Abs(r)');
    expect(String(abs(pow(r, 3)))).toBe('r**2*Abs(r)');
  });
  it('re with a real factor and I', () => {
    // SymPy re(2*r*I*y) = -2*r*im(y), im(2*r*I*y) = 2*r*re(y)
    const y = new Sym('y');
    expect(String(parse('re(2*I*y)'))).toBe('-2*im(y)');
    expect(String(mul(2, r, S.I, y))).toBe('2*I*r*y');
    expect(String(parse('re(2*I*r*y)', { locals: { r } }))).toBe('-2*r*im(y)');
  });
  it('functions of an AccumBounds', () => {
    // SymPy sin(AccumBounds(0, 1)) = AccumBounds(0, sin(1)); cosh(AccumBounds(0, 1)) stays
    const ab = AccumBounds(0, 1);
    expect(String(sin(ab))).toBe('AccumBounds(0, sin(1))');
    expect(String(cosh(ab))).toBe('cosh(AccumBounds(0, 1))');
  });
  it('unevaluated calls', () => {
    // SymPy sin(0, evaluate=False)
    expect(String(fn('sin', [0], { evaluate: false }))).toBe('sin(0)');
  });
  it('functions without a numeric value', () => {
    // SymPy lucas(1.5) and Abs(lucas(1.5)) stay unevaluated
    expect(String(fn('lucas', [new Float(1.5)]))).toBe('lucas(1.5)');
    expect(String(abs(fn('lucas', [new Float(1.5)])))).toBe('Abs(lucas(1.5))');
  });
  it('arg of complex numbers with a Float part', () => {
    // SymPy arg(2.0 + 3*I), arg(2 + 3.0*I)
    expect(String(arg(add(new Float(2), mul(3, S.I))))).toBe('0.982793723247329');
    expect(String(arg(add(2, mul(new Float(3), S.I))))).toBe('0.982793723247329');
  });
  it('arg when the sign of the real part cannot be decided', () => {
    // the real part is zero (sqrt(5 + 2*sqrt(6)) = sqrt(2) + sqrt(3)) but is neither decided nor
    // decidable numerically; SymPy gives pi/2 and nan here, symjs keeps arg unevaluated
    expect(String(parse('arg(sqrt(2)+sqrt(3)-sqrt(5+2*sqrt(6)) + I)'))).toBe('arg(-sqrt(2*sqrt(6) + 5) + sqrt(2) + sqrt(3) + I)');
    expect(String(parse('arg(I*(sqrt(2)+sqrt(3)-sqrt(5+2*sqrt(6))))'))).toBe('arg(I*(-sqrt(2*sqrt(6) + 5) + sqrt(2) + sqrt(3)))');
  });
  it('conjugate, transpose and adjoint of hyper and of non-commutative sums', () => {
    // SymPy: conjugate(hyper((1,), (2,), x)) stays, transpose is the identity, adjoint is the conjugate
    const h = hyper([1], [2], x);
    expect(String(conjugate(h))).toBe('conjugate(hyper((1,), (2,), x))');
    expect(String(transpose(h))).toBe('hyper((1,), (2,), x)');
    expect(String(adjoint(h))).toBe('conjugate(hyper((1,), (2,), x))');
    const A = new Sym('A', { commutative: false });
    const B = new Sym('B', { commutative: false });
    expect(String(transpose(add(A, B)))).toBe('transpose(A) + transpose(B)');
    // SymPy adjoint(sin(A)) = transpose(sin(conjugate(A))); transpose(sin(A)) and adjoint(f(A)) stay
    expect(String(adjoint(sin(A)))).toBe('transpose(sin(conjugate(A)))');
    expect(String(transpose(sin(A)))).toBe('transpose(sin(A))');
    // adjoint(f(A)) stays for an undefined f: SymPy adjoint(lucas(A))
    expect(String(adjoint(fn('lucas', [A])))).toBe('adjoint(lucas(A))');
  });
});
