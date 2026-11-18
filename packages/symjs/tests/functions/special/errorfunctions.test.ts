// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

import { expect, it } from 'vitest';
import { parse, rewrite } from '../../../src';

// SymPy 1.14 rewrite identities, including complex arguments and branch factors.
const cases = [
  [
    "erf(z)",
    "erf",
    "erf(z)"
  ],
  [
    "erf(z)",
    "erfc",
    "1 - erfc(z)"
  ],
  [
    "erf(z)",
    "erfi",
    "-I*erfi(I*z)"
  ],
  [
    "erf(z)",
    "fresnels",
    "(1 + I)*(fresnelc(z*(1 - I)/sqrt(pi)) - I*fresnels(z*(1 - I)/sqrt(pi)))"
  ],
  [
    "erf(z)",
    "fresnelc",
    "(1 + I)*(fresnelc(z*(1 - I)/sqrt(pi)) - I*fresnels(z*(1 - I)/sqrt(pi)))"
  ],
  [
    "erf(z)",
    "hyper",
    "2*z*hyper((1/2,), (3/2,), -z**2)/sqrt(pi)"
  ],
  [
    "erf(z)",
    "meijerg",
    "z*meijerg(((1/2,), ()), ((0,), (-1/2,)), z**2)/sqrt(pi)"
  ],
  [
    "erf(z)",
    "uppergamma",
    "(1 - erfc(sqrt(z**2)))*sqrt(z**2)/z"
  ],
  [
    "erf(z)",
    "expint",
    "-z*erfc(sqrt(z**2))/sqrt(z**2) + sqrt(z**2)/z"
  ],
  [
    "erfc(z)",
    "erf",
    "1 - erf(z)"
  ],
  [
    "erfc(z)",
    "erfc",
    "erfc(z)"
  ],
  [
    "erfc(z)",
    "erfi",
    "I*erfi(I*z) + 1"
  ],
  [
    "erfc(z)",
    "fresnels",
    "-(1 + I)*(fresnelc(z*(1 - I)/sqrt(pi)) - I*fresnels(z*(1 - I)/sqrt(pi))) + 1"
  ],
  [
    "erfc(z)",
    "fresnelc",
    "-(1 + I)*(fresnelc(z*(1 - I)/sqrt(pi)) - I*fresnels(z*(1 - I)/sqrt(pi))) + 1"
  ],
  [
    "erfc(z)",
    "hyper",
    "-2*z*hyper((1/2,), (3/2,), -z**2)/sqrt(pi) + 1"
  ],
  [
    "erfc(z)",
    "meijerg",
    "-z*meijerg(((1/2,), ()), ((0,), (-1/2,)), z**2)/sqrt(pi) + 1"
  ],
  [
    "erfc(z)",
    "uppergamma",
    "1 - (1 - erfc(sqrt(z**2)))*sqrt(z**2)/z"
  ],
  [
    "erfc(z)",
    "expint",
    "z*erfc(sqrt(z**2))/sqrt(z**2) + 1 - sqrt(z**2)/z"
  ],
  [
    "erfi(z)",
    "erf",
    "-I*erf(I*z)"
  ],
  [
    "erfi(z)",
    "erfc",
    "I*erfc(I*z) - I"
  ],
  [
    "erfi(z)",
    "erfi",
    "erfi(z)"
  ],
  [
    "erfi(z)",
    "fresnels",
    "(1 - I)*(fresnelc(z*(1 + I)/sqrt(pi)) - I*fresnels(z*(1 + I)/sqrt(pi)))"
  ],
  [
    "erfi(z)",
    "fresnelc",
    "(1 - I)*(fresnelc(z*(1 + I)/sqrt(pi)) - I*fresnels(z*(1 + I)/sqrt(pi)))"
  ],
  [
    "erfi(z)",
    "hyper",
    "2*z*hyper((1/2,), (3/2,), z**2)/sqrt(pi)"
  ],
  [
    "erfi(z)",
    "meijerg",
    "z*meijerg(((1/2,), ()), ((0,), (-1/2,)), -z**2)/sqrt(pi)"
  ],
  [
    "erfi(z)",
    "uppergamma",
    "sqrt(-z**2)*(erfc(sqrt(-z**2)) - 1)/z"
  ],
  [
    "erfi(z)",
    "expint",
    "-z*erfc(sqrt(-z**2))/sqrt(-z**2) - sqrt(-z**2)/z"
  ],
  [
    "erf2(x, y)",
    "erf",
    "-erf(x) + erf(y)"
  ],
  [
    "erf2(x, y)",
    "erfc",
    "erfc(x) - erfc(y)"
  ],
  [
    "erf2(x, y)",
    "erfi",
    "I*(erfi(I*x) - erfi(I*y))"
  ],
  [
    "erf2(x, y)",
    "fresnels",
    "-(1 + I)*(fresnelc(x*(1 - I)/sqrt(pi)) - I*fresnels(x*(1 - I)/sqrt(pi))) + (1 + I)*(fresnelc(y*(1 - I)/sqrt(pi)) - I*fresnels(y*(1 - I)/sqrt(pi)))"
  ],
  [
    "erf2(x, y)",
    "fresnelc",
    "-(1 + I)*(fresnelc(x*(1 - I)/sqrt(pi)) - I*fresnels(x*(1 - I)/sqrt(pi))) + (1 + I)*(fresnelc(y*(1 - I)/sqrt(pi)) - I*fresnels(y*(1 - I)/sqrt(pi)))"
  ],
  [
    "erf2(x, y)",
    "hyper",
    "-2*x*hyper((1/2,), (3/2,), -x**2)/sqrt(pi) + 2*y*hyper((1/2,), (3/2,), -y**2)/sqrt(pi)"
  ],
  [
    "erf2(x, y)",
    "meijerg",
    "-x*meijerg(((1/2,), ()), ((0,), (-1/2,)), x**2)/sqrt(pi) + y*meijerg(((1/2,), ()), ((0,), (-1/2,)), y**2)/sqrt(pi)"
  ],
  [
    "erf2(x, y)",
    "uppergamma",
    "(1 - erfc(sqrt(y**2)))*sqrt(y**2)/y - (1 - erfc(sqrt(x**2)))*sqrt(x**2)/x"
  ],
  [
    "erf2(x, y)",
    "expint",
    "x*erfc(sqrt(x**2))/sqrt(x**2) - y*erfc(sqrt(y**2))/sqrt(y**2) + sqrt(y**2)/y - sqrt(x**2)/x"
  ],
  [
    "fresnels(z)",
    "erf",
    "(1/4 + I/4)*(-I*erf(sqrt(pi)*z*(1/2 - I/2)) + erf(sqrt(pi)*z*(1/2 + I/2)))"
  ],
  [
    "fresnels(z)",
    "hyper",
    "pi*z**3*hyper((3/4,), (3/2, 7/4), -pi**2*z**4/16)/6"
  ],
  [
    "fresnels(z)",
    "meijerg",
    "sqrt(2)*pi*z**(9/4)*meijerg(((), (1,)), ((3/4,), (0, 1/4)), -pi**2*z**4/16)/(2*(-z)**(3/4)*(z**2)**(3/4))"
  ],
  [
    "fresnelc(z)",
    "erf",
    "(1/4 - I/4)*(I*erf(sqrt(pi)*z*(1/2 - I/2)) + erf(sqrt(pi)*z*(1/2 + I/2)))"
  ],
  [
    "fresnelc(z)",
    "hyper",
    "z*hyper((1/4,), (1/2, 5/4), -pi**2*z**4/16)"
  ],
  [
    "fresnelc(z)",
    "meijerg",
    "sqrt(2)*pi*z**(3/4)*meijerg(((), (1,)), ((1/4,), (0, 3/4)), -pi**2*z**4/16)/(2*(-z)**(1/4)*(z**2)**(1/4))"
  ],
  [
    "erfinv(z)",
    "erfcinv",
    "erfcinv(1 - z)"
  ],
  [
    "erfcinv(z)",
    "erfinv",
    "erfinv(1 - z)"
  ]
] as const;
it.each(cases)('%s.rewrite(%s)', (source, target, expected) => {
  expect(String(rewrite(parse(source), target))).toBe(expected);
});

it('preserves erfi numerically when rewriting with the exponential integral', async () => {
  const { erfi, rewrite, Sym, toComplex } = await import('../../../src');
  const z = new Sym('z');
  const rewritten = rewrite(erfi(z), 'expint');
  for (const value of [1, -1, { re: 1, im: 2 }, { re: -1, im: 2 }]) {
    const actual = toComplex(rewritten, { z: value });
    const expected = toComplex(erfi(z), { z: value });
    expect(actual.re).toBeCloseTo(expected.re, 10);
    expect(actual.im).toBeCloseTo(expected.im, 10);
  }
});
