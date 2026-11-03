// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/polys/fromexpr.ts: conversion of expressions to polynomials, reached through multivariate gcd, exact division and factorization; expected values from SymPy 1.14.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';

const { parse } = sj;
const [x, y] = sj.symbols('x y') as [sj.Sym, sj.Sym];
const show = (r: unknown): string => (Array.isArray(r) ? `[${r.map(show).join(', ')}]` : String(r));

describe('multivariate gcd, exact division and factorization (polys/mpoly)', () => {
  it('polyFromExpr with generators', () => {
    const [p, opts] = sj.polyFromExpr(parse('x*y + 1'), [y, x]);
    expect(String(p)).toBe("Poly(y*x + 1, y, x, domain='ZZ')");
    expect(show(opts.gens)).toBe('[y, x]');
    expect(opts.domain).toBe('ZZ');
    expect(String(sj.polyFromExpr(parse('x**2 + 1'))[0])).toBe("Poly(x**2 + 1, x, domain='ZZ')");
  });
});
