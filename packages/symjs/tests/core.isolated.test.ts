// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/core.ts.

// The core entry alone (this file must not import the root entry): features of the other
// areas are late-bound and report that their entry point is not loaded.

import { describe, expect, it } from 'vitest';
import * as core from '../src/core';
import { NotLoadedError } from '../src/core/errors';

const [x] = core.symbols('x');

describe('core entry without the other feature areas', () => {
  it('reports that simplification, integration, limits and series are not loaded', () => {
    expect(() => x.simplify()).toThrow("simplify is not available: import '@symjs/symjs/simplify'");
    expect(() => x.limit(x, 0)).toThrow("limit is not available: import '@symjs/symjs/calculus'");
    expect(() => x.series(x)).toThrow("series is not available: import '@symjs/symjs/calculus'");
    expect(() => x.integrate(x)).toThrow(NotLoadedError);
    expect(() => x.integrate(x)).toThrow("integrate is not available: import '@symjs/symjs/calculus'");
  });
  it('reports that sets are not loaded for AccumBounds intersections', () => {
    const a = core.AccumBounds(1, 2) as core.AccumBoundsNode;
    const b = core.AccumBounds(3, 4) as core.AccumBoundsNode;
    expect(() => a.intersection(b)).toThrow(NotLoadedError);
    expect(() => a.intersection(x)).toThrow("import '@symjs/symjs/sets'");
  });
});

describe('var', () => {
  it('returns the symbols (SymPy var also binds them in the namespace)', () => {
    const [p, q] = core.var('p q', { positive: true });
    expect([String(p), String(q)]).toEqual(['p', 'q']);
    expect(core.isPositive(p)).toBe(true);
    expect(String(core.var('r')[0])).toBe('r');
  });
});
