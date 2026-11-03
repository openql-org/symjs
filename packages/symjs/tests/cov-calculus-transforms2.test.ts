// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Expected values are the str() forms printed by SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { DiracDelta, Heaviside, cosineTransform, fourierTransform, hankelTransform, inverseHankelTransform, inverseMellinTransform, mellinTransform, parse, sineTransform, symbol, symbols } from '../src';

const [x, s, t, k, a, b] = symbols('x s t k a b');
const nu = symbol('nu');
const p = symbol('p', { positive: true });
const P = (q: string) => parse(q, { symbols: [x, s, t, k, a, b, nu, p], locals: { Heaviside, DiracDelta } });

const show = (v: unknown): string => (Array.isArray(v) ? `(${v.map(show).join(', ')})` : String(v));

describe("integral transforms: more SymPy 1.14 cases", () => {
  const cases: [string, () => unknown, string][] = [
    ["mellinTransform(P('sin(x)'), x, s)", () => mellinTransform(P('sin(x)'), x, s), "(2**s*sqrt(pi)*gamma(s/2 + 1/2)/(2*gamma(1 - s/2)), (-1, 1), True)"],
    ["mellinTransform(P('cos(x)'), x, s)", () => mellinTransform(P('cos(x)'), x, s), "(2**s*sqrt(pi)*gamma(s/2)/(2*gamma(1/2 - s/2)), (0, 1), True)"],
    ["mellinTransform(P('sin(p*x)'), x, s)", () => mellinTransform(P('sin(p*x)'), x, s), "(2**s*sqrt(pi)*gamma(s/2 + 1/2)/(2*p**s*gamma(1 - s/2)), (-1, 1), True)"],
    ["mellinTransform(P('x**a/(x + 1)'), x, s)", () => mellinTransform(P('x**a/(x + 1)'), x, s), "(pi/sin(pi*(a + s)), (-re(a), 1 - re(a)), True)"],
    ["mellinTransform(P('exp(-x**2)'), x, s)", () => mellinTransform(P('exp(-x**2)'), x, s), "(gamma(s/2)/2, (0, oo), True)"],
    ["mellinTransform(P('Heaviside(1 - x)'), x, s)", () => mellinTransform(P('Heaviside(1 - x)'), x, s), "(1/s, (0, oo), True)"],
    ["mellinTransform(P('Heaviside(x - 1)'), x, s)", () => mellinTransform(P('Heaviside(x - 1)'), x, s), "(-1/s, (-oo, 0), True)"],
    ["mellinTransform(P('x**2*Heaviside(1 - x)'), x, s)", () => mellinTransform(P('x**2*Heaviside(1 - x)'), x, s), "(1/(s + 2), (-2, oo), True)"],
    ["mellinTransform(P('(1 - x)*Heaviside(1 - x)'), x, s)", () => mellinTransform(P('(1 - x)*Heaviside(1 - x)'), x, s), "(1/(s*(s + 1)), (0, oo), True)"],
    ["mellinTransform(P('exp(-x)*x'), x, s)", () => mellinTransform(P('exp(-x)*x'), x, s), "(gamma(s + 1), (-1, oo), True)"],
    ["inverseMellinTransform(P('gamma(s)'), s, x, [P('0'), P('oo')])", () => inverseMellinTransform(P('gamma(s)'), s, x, [P('0'), P('oo')]), "exp(-x)"],
    ["inverseMellinTransform(P('gamma(2*s)'), s, x, [P('0'), P('oo')])", () => inverseMellinTransform(P('gamma(2*s)'), s, x, [P('0'), P('oo')]), "exp(-sqrt(x))/2"],
    ["inverseMellinTransform(P('gamma(s)*gamma(1 - s)'), s, x, [P('0'), P('1')])", () => inverseMellinTransform(P('gamma(s)*gamma(1 - s)'), s, x, [P('0'), P('1')]), "1/(x + 1)"],
    ["inverseMellinTransform(P('gamma(s/2)'), s, x, [P('0'), P('oo')])", () => inverseMellinTransform(P('gamma(s/2)'), s, x, [P('0'), P('oo')]), "2*exp(-x**2)"],
    ["inverseMellinTransform(P('1/s'), s, x, [P('0'), P('oo')])", () => inverseMellinTransform(P('1/s'), s, x, [P('0'), P('oo')]), "Heaviside(1 - x)"],
    ["inverseMellinTransform(P('gamma(s)/gamma(s + 1/2)'), s, x, [P('0'), P('oo')])", () => inverseMellinTransform(P('gamma(s)/gamma(s + 1/2)'), s, x, [P('0'), P('oo')]), "InverseMellinTransform(gamma(s)/gamma(s + 1/2), s, x, 0, oo)"],
    ["inverseMellinTransform(P('pi/sin(pi*s)'), s, x, [P('0'), P('1')])", () => inverseMellinTransform(P('pi/sin(pi*s)'), s, x, [P('0'), P('1')]), "1/(x + 1)"],
    ["inverseMellinTransform(P('gamma(s)**2'), s, x, [P('0'), P('oo')])", () => inverseMellinTransform(P('gamma(s)**2'), s, x, [P('0'), P('oo')]), "meijerg(((1, 1), ()), ((), ()), 1/x)"],
    ["inverseMellinTransform(P('2**s*gamma(s)'), s, x, [P('0'), P('oo')])", () => inverseMellinTransform(P('2**s*gamma(s)'), s, x, [P('0'), P('oo')]), "exp(-x/2)"],
    ["inverseMellinTransform(P('gamma(s + 1)'), s, x, [P('-1'), P('oo')])", () => inverseMellinTransform(P('gamma(s + 1)'), s, x, [P('-1'), P('oo')]), "x*exp(-x)"],
    ["inverseMellinTransform(P('gamma(1 - s)'), s, x, [P('-oo'), P('1')])", () => inverseMellinTransform(P('gamma(1 - s)'), s, x, [P('-oo'), P('1')]), "exp(-1/x)/x"],
    ["fourierTransform(P('exp(-x**2)'), x, k)", () => fourierTransform(P('exp(-x**2)'), x, k), "sqrt(pi)*exp(-pi**2*k**2)"],
    ["fourierTransform(P('exp(-p*x**2)'), x, k)", () => fourierTransform(P('exp(-p*x**2)'), x, k), "sqrt(pi)*exp(-pi**2*k**2/p)/sqrt(p)"],
    ["fourierTransform(P('exp(-Abs(x))'), x, k)", () => fourierTransform(P('exp(-Abs(x))'), x, k), "2/(4*pi**2*k**2 + 1)"],
    ["fourierTransform(P('Heaviside(x)*exp(-x)'), x, k)", () => fourierTransform(P('Heaviside(x)*exp(-x)'), x, k), "1/(2*I*pi*k + 1)"],
    ["fourierTransform(P('x*exp(-x**2)'), x, k)", () => fourierTransform(P('x*exp(-x**2)'), x, k), "-I*pi**(3/2)*k*exp(-pi**2*k**2)"],
    ["fourierTransform(P('DiracDelta(x)'), x, k)", () => fourierTransform(P('DiracDelta(x)'), x, k), "1"],
    ["fourierTransform(P('DiracDelta(x - 1)'), x, k)", () => fourierTransform(P('DiracDelta(x - 1)'), x, k), "exp(-2*I*pi*k)"],
    ["fourierTransform(P('exp(-x)*Heaviside(x)*x'), x, k)", () => fourierTransform(P('exp(-x)*Heaviside(x)*x'), x, k), "(2*I*pi*k + 1)**(-2)"],
    ["sineTransform(P('exp(-x)'), x, k)", () => sineTransform(P('exp(-x)'), x, k), "sqrt(2)*k/(sqrt(pi)*(k**2 + 1))"],
    ["cosineTransform(P('exp(-x)'), x, k)", () => cosineTransform(P('exp(-x)'), x, k), "sqrt(2)/(sqrt(pi)*(k**2 + 1))"],
    ["sineTransform(P('x*exp(-x)'), x, k)", () => sineTransform(P('x*exp(-x)'), x, k), "2*sqrt(2)*k/(sqrt(pi)*(k**2 + 1)**2)"],
    ["sineTransform(P('1/x'), x, k)", () => sineTransform(P('1/x'), x, k), "sqrt(2)*sqrt(pi)/2"],
    ["sineTransform(P('exp(-p*x)'), x, k)", () => sineTransform(P('exp(-p*x)'), x, k), "sqrt(2)*k/(sqrt(pi)*(k**2 + p**2))"],
    ["cosineTransform(P('exp(-p*x)'), x, k)", () => cosineTransform(P('exp(-p*x)'), x, k), "sqrt(2)*p/(sqrt(pi)*(k**2 + p**2))"],
    ["sineTransform(P('x/(x**2 + 1)'), x, k)", () => sineTransform(P('x/(x**2 + 1)'), x, k), "sqrt(2)*sqrt(pi)*exp(-k)/2"],
    ["sineTransform(P('1/sqrt(x)'), x, k)", () => sineTransform(P('1/sqrt(x)'), x, k), "1/sqrt(k)"],
    ["cosineTransform(P('1/sqrt(x)'), x, k)", () => cosineTransform(P('1/sqrt(x)'), x, k), "1/sqrt(k)"],
    ["cosineTransform(P('exp(-x**2)'), x, k)", () => cosineTransform(P('exp(-x**2)'), x, k), "sqrt(2)*exp(-k**2/4)/2"],
    ["hankelTransform(P('1/x'), x, k, 0)", () => hankelTransform(P('1/x'), x, k, 0), "1/k"],
    ["inverseHankelTransform(P('1/x'), x, k, 0)", () => inverseHankelTransform(P('1/x'), x, k, 0), "1/k"],
    ["hankelTransform(P('exp(-x**2)'), x, k, 0)", () => hankelTransform(P('exp(-x**2)'), x, k, 0), "exp(-k**2/4)/2"],
    ["inverseHankelTransform(P('exp(-x**2)'), x, k, 0)", () => inverseHankelTransform(P('exp(-x**2)'), x, k, 0), "exp(-k**2/4)/2"],
    ["hankelTransform(P('1/sqrt(x**2 + 1)'), x, k, 0)", () => hankelTransform(P('1/sqrt(x**2 + 1)'), x, k, 0), "exp(-k)/k"],
    ["inverseHankelTransform(P('1/sqrt(x**2 + 1)'), x, k, 0)", () => inverseHankelTransform(P('1/sqrt(x**2 + 1)'), x, k, 0), "exp(-k)/k"],
  ];
  it.each(cases)('%s', (_name, run, want) => {
    expect(show(run())).toBe(want);
  });
});
