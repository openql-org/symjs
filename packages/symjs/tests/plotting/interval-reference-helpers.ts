// Operators used only by the mechanically translated SymPy interval tests.
import { Expr, Rel, symbol, rel } from '../../src/core';
import { intervalmath as li } from '../../src/plotting';
import { intervalEvaluate } from '../../src/plotting/series';
export function iv(...args: any[]): li.interval { const opts = args.at(-1); const hasOptions = typeof opts === 'object' && opts !== null && !(opts instanceof li.interval); if (hasOptions) args.pop(); if (args.length < 1 || args.length > 2) throw new RangeError('Interval arity'); return new li.interval(args[0], args[1], hasOptions ? opts : {}); }
export function membership(...args: any[]): li.intervalMembership { if (args.length !== 2) throw new TypeError('Membership arity'); return new li.intervalMembership(args[0], args[1]); }
export function op(name: string, a: any, b: any): any {
  if (name === 'is') return a === b;
  if (name === 'in' || name === 'notIn') return name === 'in' ? b.contains(a) : !b.contains(a);
  if (a instanceof li.intervalMembership && (name === 'eq' || name === 'ne')) return name === 'eq' ? a.equals(b) : !a.equals(b);
  if (a instanceof li.intervalMembership) return (a as any)[name](b);
  if (a instanceof Expr || b instanceof Expr) return rel(({ gt: 'Gt', ge: 'Ge', lt: 'Lt', le: 'Le', eq: 'Eq', ne: 'Ne' } as const)[name as 'gt']!, a, b);
  if (a instanceof li.interval || b instanceof li.interval) {
    if (name === 'pow' && typeof a === 'number') return b.rpow(a);
    const left = a instanceof li.interval ? a : iv(a);
    return (left as any)[name](b);
  }
  switch (name) { case 'add': return a + b; case 'sub': return a - b; case 'mul': return a * b; case 'div': return a / b; case 'pow': return a ** b; case 'eq': return a === b; case 'ne': return a !== b; case 'lt': return a < b; case 'le': return a <= b; case 'gt': return a > b; case 'ge': return a >= b; default: throw new TypeError(name); }
}
export function unary(name: string, value: any): any { if (name === 'Not') return !bool(value); if (name === 'Invert') return value.not(); return value instanceof li.interval ? value.neg() : -value; }
export function bool(v: unknown): boolean { return Boolean(v); }
export function item(v: any, i: number): any { return v instanceof li.intervalMembership ? v.get(i) : v[i]; }
export function lengthOf(v: any): number { return v.length; }
export function iterator(v: any): Iterator<unknown> { return v[Symbol.iterator](); }
export function nextItem(v: Iterator<unknown>): unknown { const n = v.next(); if (n.done) throw new RangeError('StopIteration'); return n.value; }
export function range(n: number): number[] { return Array.from({ length: n }, (_, i) => i); }
export function hashInterval(v: li.interval): string { return JSON.stringify([v.start, v.end, v.isValid]); }
export function intervalLambda(vars: ReturnType<typeof symbol>[], expr: Rel): (value: li.interval) => unknown { return (value) => intervalEvaluate(expr, new Map([[vars[0]!.key, value]])); }
