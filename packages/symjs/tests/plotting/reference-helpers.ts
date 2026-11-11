import { expect } from 'vitest';
import { readFileSync } from 'node:fs';
import { parse, symbol } from '../../src/core';
import * as plotting from '../../src/plotting';
export interface Fixture { cls: string; exprs: string[]; ranges: [string, string, string][]; options: Record<string, unknown>; data: unknown; label: string; n: number[]; }
export const reference = JSON.parse(readFileSync(new URL('./reference-data.json', import.meta.url), 'utf8')) as { series: Fixture[]; text: { expr: string; a: number; b: number; width: number; height: number; lines: string[] }[] };
export function numericEqual(actual: unknown, expected: unknown): void {
  if (Array.isArray(expected)) { expect(Array.isArray(actual)).toBe(true); const values = actual as unknown[]; expect(values.length).toBe(expected.length); expected.forEach((v, i) => numericEqual(values[i], v)); }
  else if (typeof expected === 'number') { expect(typeof actual).toBe('number'); expect(Math.abs(Number(actual) - expected)).toBeLessThanOrEqual(1e-9 * Math.max(1, Math.abs(expected))); }
  else if (expected === 'NaN') expect(Number.isNaN(actual)).toBe(true);
  else if (expected === 'Infinity' || expected === '-Infinity') expect(actual).toBe(Number(expected));
  else expect(actual).toEqual(expected);
}
export function fromFixture(f: Fixture): plotting.BaseSeries {
  const options: Record<string, unknown> = Object.fromEntries(Object.entries(f.options).map(([k, v]) => [k.replace(/_([a-z])/g, (_, c: string) => c.toUpperCase()), v]));
  if (options['params']) options['params'] = new Map(Object.entries(options['params'] as Record<string, string>).map(([k, v]) => [symbol(k), parse(v)]));
  for (const key of ['colorFunc', 'lineColor', 'surfaceColor']) {
    const value = options[key];
    if (value === 'sum') options[key] = (x: number, y: number) => x + y;
    if (value === 'parameter') options[key] = (p: number) => p * p;
    if (value === 'z') options[key] = (_x: number, _y: number, z: number) => z;
    if (value === 'symbolic') options[key] = parse('a*x');
  }
  for (const key of ['tx', 'ty', 'tz', 'tp']) if (options[key]) options[key] = (v: number) => 2 * v + 1;
  const ctor = (plotting as unknown as Record<string, new (...args: unknown[]) => plotting.BaseSeries>)[f.cls]!;
  return new ctor(...f.exprs.map((e) => parse(e)), ...f.ranges.map(([s, a, b]) => [symbol(s), parse(a), parse(b)]), 'reference', options);
}
