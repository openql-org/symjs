import { readFileSync } from 'node:fs';
import { parse, symbol, lambdify, NoMatch } from '../../src/core';
export interface FactoryFixture { test: string; factory: string; args: unknown[]; options: Record<string, unknown>; series: { class: string; label: string; ranges: unknown[][]; renderingKw: Record<string, unknown>; data: unknown }[]; }
export const upstream = JSON.parse(readFileSync(new URL('./upstream-arguments.json', import.meta.url), 'utf8')) as { factories: FactoryFixture[]; texts: { test: string; expr: string; a: number; b: number; width: number; height: number; lines: string[] }[] };
export function decode(value: unknown): any {
  if (Array.isArray(value)) {
    const result = value.map(decode);
    if (result.length === 3 && typeof result[0] === 'string' && typeof result[1] === 'number' && typeof result[2] === 'number') result[0] = symbol(result[0]);
    return result;
  }
  if (value && typeof value === 'object') {
    if ('automaticLabel' in value) return NoMatch;
    if ('map' in value) return new Map((value.map as [unknown, unknown][]).map(([k, v]) => [decode(k), decode(v)]));
    if ('expr' in value) return parse(String(value.expr));
    if ('callback' in value && 'parameters' in value) {
      const vars = (value.parameters as string[]).map((s) => symbol(s)), fn = lambdify(parse(String(value.callback)), vars);
      const callback = (...args: number[]) => fn(...args);
      Object.defineProperty(callback, 'length', { value: vars.length });
      return callback;
    }
    return Object.fromEntries(Object.entries(value).map(([k, v]) => [k.replace(/_([a-z])/g, (_, c: string) => c.toUpperCase()), decode(v)]));
  }
  return value;
}
export const upstreamSeries = JSON.parse(readFileSync(new URL('./upstream-series.json', import.meta.url), 'utf8')) as { fixtures: { test: string; class: string; args: unknown[]; options: Record<string, unknown>; expected: Record<string, unknown>; str: string }[] };
