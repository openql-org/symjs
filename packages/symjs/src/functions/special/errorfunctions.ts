// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14 (sympy/functions/special/error_functions.py),
// BSD 3-Clause License, Copyright (c) 2006-2023 SymPy Development Team.

/** @file Rewrites of the error functions and Fresnel integrals. */
import type { Expr } from '../../core/nodes';
import { Rational, S } from '../../core/nodes';
import { defined, first, pair } from '../../core/guard';
import { add, mul, neg, pow, sqrt } from '../../core/ops';
import { fn } from '../elementary/elementary';
import { hyper, meijerg } from './hyper';
import { expandMul } from '../../simplify/expand';
import { registerRewrite } from '../../simplify/rewrite';

const R = (p: number, q: number): Rational => Rational.of(p, q);
const invSqrtPi = pow(S.Pi, S.NegHalf);
const erfRewrites: Record<string, (z: Expr) => Expr> = {
  erf: (z) => fn('erf', [z]),
  erfc: (z) => add(1, neg(fn('erfc', [z]))),
  erfi: (z) => mul(-1, S.I, fn('erfi', [mul(S.I, z)])),
  fresnels: (z) => {
    const a = mul(add(1, neg(S.I)), z, invSqrtPi);
    return mul(add(1, S.I), add(fn('fresnelc', [a]), mul(-1, S.I, fn('fresnels', [a]))));
  },
  hyper: (z) => mul(2, z, invSqrtPi, hyper([S.Half], [R(3, 2)], neg(pow(z, 2)))),
  meijerg: (z) => mul(z, invSqrtPi, meijerg([S.Half], [], [S.Zero], [S.NegHalf], pow(z, 2))),
  uppergamma: (z) => mul(sqrt(pow(z, 2)), pow(z, -1), add(1, neg(mul(invSqrtPi, fn('uppergamma', [S.Half, pow(z, 2)]))))),
  expint: (z) => add(mul(sqrt(pow(z, 2)), pow(z, -1)), neg(mul(z, invSqrtPi, fn('expint', [S.Half, pow(z, 2)])))),
};
erfRewrites.fresnelc = defined(erfRewrites.fresnels);
for (const [target, rule] of Object.entries(erfRewrites)) {
  registerRewrite('erf', target, (args) => rule(first(args)));
  registerRewrite('erfc', target, (args) => add(1, neg(rule(first(args)))));
  registerRewrite('erf2', target, (args) => {
    const [x, y] = pair(args);
    return add(rule(y), neg(rule(x)));
  });
}
registerRewrite('erf2', 'erfi', (args) => {
  const [x, y] = pair(args);
  return mul(S.I, add(fn('erfi', [mul(S.I, x)]), neg(fn('erfi', [mul(S.I, y)]))));
});
registerRewrite('erfi', 'erf', (args) => mul(-1, S.I, fn('erf', [mul(S.I, first(args))])));
registerRewrite('erfi', 'erfc', (args) => add(mul(S.I, fn('erfc', [mul(S.I, first(args))])), neg(S.I)));
for (const target of ['fresnels', 'fresnelc']) registerRewrite('erfi', target, (args) => {
  const z = first(args), a = mul(add(1, S.I), z, invSqrtPi);
  return mul(add(1, neg(S.I)), add(fn('fresnelc', [a]), mul(-1, S.I, fn('fresnels', [a]))));
});
registerRewrite('erfi', 'hyper', (args) => {
  const z = first(args);
  return mul(2, z, invSqrtPi, hyper([S.Half], [R(3, 2)], pow(z, 2)));
});
registerRewrite('erfi', 'meijerg', (args) => {
  const z = first(args);
  return mul(z, invSqrtPi, meijerg([S.Half], [], [S.Zero], [S.NegHalf], neg(pow(z, 2))));
});
registerRewrite('erfi', 'uppergamma', (args) => {
  const z = first(args), z2 = neg(pow(z, 2));
  return mul(sqrt(z2), pow(z, -1), add(mul(invSqrtPi, fn('uppergamma', [S.Half, z2])), -1));
});
registerRewrite('erfi', 'expint', (args) => {
  const z = first(args), z2 = neg(pow(z, 2));
  return add(neg(mul(sqrt(z2), pow(z, -1))), neg(mul(z, invSqrtPi, fn('expint', [S.Half, z2]))));
});
registerRewrite('erfinv', 'erfcinv', (args) => fn('erfcinv', [add(1, neg(first(args)))]));
registerRewrite('erfcinv', 'erfinv', (args) => fn('erfinv', [add(1, neg(first(args)))]));
for (const name of ['fresnels', 'fresnelc'] as const) {
  const s = name === 'fresnels';
  registerRewrite(name, 'erf', (args) => {
    const z = first(args), plus = add(S.Half, mul(S.Half, S.I)), minus = add(S.Half, mul(S.NegHalf, S.I));
    return mul(expandMul(mul(S.Half, s ? plus : minus)), add(fn('erf', [mul(plus, sqrt(S.Pi), z)]), mul(s ? neg(S.I) : S.I, fn('erf', [mul(minus, sqrt(S.Pi), z)]))));
  });
  registerRewrite(name, 'hyper', (args) => {
    const z = first(args), a = mul(R(-1, 16), pow(S.Pi, 2), pow(z, 4));
    return s ? mul(S.Pi, pow(z, 3), R(1, 6), hyper([R(3, 4)], [R(3, 2), R(7, 4)], a))
      : mul(z, hyper([R(1, 4)], [S.Half, R(5, 4)], a));
  });
  registerRewrite(name, 'meijerg', (args) => {
    const z = first(args), a = mul(R(-1, 16), pow(S.Pi, 2), pow(z, 4)), p = s ? R(3, 4) : R(1, 4);
    return mul(S.Pi, pow(z, s ? R(9, 4) : R(3, 4)), pow(2, S.NegHalf), pow(pow(z, 2), neg(p)), pow(neg(z), neg(p)), meijerg([], [S.One], [p], [S.Zero, s ? R(1, 4) : R(3, 4)], a));
  });
}
