// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * The core entry point works on its own (without the other feature areas),
 * the core does not import them, and package.json lists every module with
 * top-level side effects.
 */

import { readFileSync, readdirSync } from 'node:fs';
import { dirname, join, relative, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { describe, expect, it } from 'vitest';
import * as sj from '../src/core';
// @ts-expect-error untyped build script
import { sideEffectsField } from '../scripts/side-effects.mjs';

const root = fileURLToPath(new URL('..', import.meta.url));
const src = join(root, 'src');

describe('core entry on its own', () => {
  const x = sj.symbol('x');
  it('parses, prints, differentiates, expands and evaluates', () => {
    expect(sj.str(sj.parse('sin(pi/6) + cos(pi/4) + Abs(-3*x)'))).toBe('3*Abs(x) + 1/2 + sqrt(2)/2');
    expect(sj.str(sj.diff(sj.parse('sin(x)*exp(x**2)'), x))).toBe('2*x*exp(x**2)*sin(x) + exp(x**2)*cos(x)');
    expect(sj.str(sj.expand(sj.parse('(x + 1)**2')))).toBe('x**2 + 2*x + 1');
    expect(sj.latex(sj.parse('sqrt(x)/(1 + x**2)'))).toBe('\\frac{\\sqrt{x}}{x^{2} + 1}');
    expect(sj.str(sj.evalf(sj.parse('sin(1) + atan(2)'), 20))).toBe('1.9486197026019870097');
    expect(sj.str(sj.subs(sj.parse('x**2 + 1'), [[x, sj.Rational.of(3)]]))).toBe('10');
  });
  it('reports a feature area that is not imported', () => {
    expect(() => sj.parse('x + x').simplify()).toThrow("import '@symjs/symjs/simplify'");
    expect(() => x.integrate(x)).toThrow("import '@symjs/symjs/calculus'");
    expect(() => sj.parse('exp(x)').series(x)).toThrow("import '@symjs/symjs/calculus'");
    expect(() => sj.sin(x).rewrite('exp')).toThrow("import '@symjs/symjs/simplify'");
  });
});

/** Relative module imports (not `import type`) of a source file. */
function imports(file: string): string[] {
  const text = readFileSync(join(src, file), 'utf8');
  const out: string[] = [];
  for (const m of text.matchAll(/^(?:import|export)\s+(?!type\b)(?:[^;]*?from\s+)?'(\.[^']+)'/gms)) {
    out.push(relative(src, resolve(dirname(join(src, file)), m[1]!)).replace(/\\/g, '/') + '.ts');
  }
  return out;
}

describe('module layering', () => {
  it('the core entry reaches only core modules', () => {
    const CORE_DIRS = ['core/', 'numeric/', 'printing/', 'parsing/'];
    const CORE_FILES = ['core.ts', 'functions/elementary/elementary.ts', 'functions/elementary/accumbounds.ts', 'functions/elementary/trigext.ts', 'calculus/diff.ts', 'simplify/expand.ts', 'concrete/node.ts'];
    const isCore = (f: string) => CORE_FILES.includes(f) || CORE_DIRS.some((d) => f.startsWith(d) && f !== 'numeric/mpspecial.ts' && f !== 'numeric/mpspecialfns.ts');
    const seen = new Set<string>();
    const outside: string[] = [];
    const visit = (f: string, from: string) => {
      if (seen.has(f)) return;
      seen.add(f);
      if (!isCore(f)) outside.push(`${from} -> ${f}`);
      for (const d of imports(f)) visit(d, f);
    };
    visit('core.ts', '');
    expect(outside).toEqual([]);
  });

  it('package.json sideEffects lists every module with top-level code', () => {
    const pkg = JSON.parse(readFileSync(join(root, 'package.json'), 'utf8'));
    expect(pkg.sideEffects).toEqual(sideEffectsField());
  });

  it('every entry point is exported by package.json', () => {
    const pkg = JSON.parse(readFileSync(join(root, 'package.json'), 'utf8'));
    const entries = readdirSync(src).filter((f) => f.endsWith('.ts') && f !== 'index.ts').map((f) => `./${f.slice(0, -3)}`);
    expect(Object.keys(pkg.exports).filter((k) => k !== '.' && k !== './package.json').sort()).toEqual(entries.sort());
  });
});
