// SPDX-License-Identifier: MIT
/** Argument conversion and dispatch only; all mathematics runs in public APIs. */
import * as dg from '@symjs/diffgeom';
import * as sj from '@symjs/symjs';
import { deserialize, JsDict, JsList, JsTuple, JsLambda, Unsupported, withExtension, runCase } from '../../harness';
import type { Tree, Adapter, Case, HarnessExtension, Outcome } from '../../harness';
import { runTestCase } from '../../tests-harness';
import type { TestCase, TestOutcome } from '../../tests-harness';

const camel = (name: string): string => name.replace(/_([a-zA-Z0-9])/g, (_, c: string) => c.toUpperCase());
const namespace: Record<string, unknown> = dg;

function plain(value: unknown): unknown {
  if (value instanceof JsList || value instanceof JsTuple) return value.items.map(plain);
  if (value instanceof JsDict) return new Map(value.entries.map(([k, v]) => [plain(k), plain(v)]));
  if (value instanceof JsLambda) {
    const body = plain(value.body);
    return sj.Lambda(value.vars, Array.isArray(body) ? new sj.Tuple(body) : body as sj.Expr);
  }
  return value;
}
const integer = (v: unknown): number => Number(String(v));
function construct(name: string, args: unknown[], kwargs: Record<string, unknown> = {}): unknown {
  const fn = namespace[camel(name)];
  if (typeof fn !== 'function') throw new Unsupported(`diffgeom export ${name}`);
  const a = args.map(plain);
  if (['Manifold', 'CoordinateSymbol', 'BaseScalarField', 'BaseVectorField', 'BaseCovarDerivativeOp'].includes(name)) a[1] = integer(a[1]);
  if (name === 'CoordSystem' && Object.keys(kwargs).length) {
    a[2] = a[2] ?? plain(kwargs['symbols'] ?? kwargs['names']);
    a[3] = a[3] ?? plain(kwargs['relations']);
  }
  if (name === 'intcurve_series') {
    a[3] = integer(a[3] ?? kwargs['n'] ?? 6);
    a[4] = { coordSys: a[4] ?? kwargs['coord_sys'], coeffs: a[5] ?? kwargs['coeffs'] ?? false };
    a.length = 5;
  }
  if (name === 'intcurve_diffequ') a[3] = a[3] ?? kwargs['coord_sys'];
  const result = /^class[\s{]/.test(Function.prototype.toString.call(fn)) ? Reflect.construct(fn, a) : fn(...a);
  return name === 'intcurve_diffequ' ? new JsTuple((result as unknown[][]).map(xs => new JsList(xs))) : result;
}

const extension: HarnessExtension = {
  deserialize(tree: Tree): unknown {
    if ('ref' in tree) return namespace[camel(String(tree['ref']))];
    return construct(String(tree['cls']), (tree['args'] as Tree[]).map(deserialize));
  },
  adapter(c: Case): Adapter | undefined {
    if (!c.fn.startsWith('.') && camel(c.fn) in namespace) return (args, kw) => construct(c.fn, args, kw);
    if (c.fn.startsWith('.__') && c.fn !== '.__call__' || c.fn.startsWith('.is_')) return undefined;
    if (c.fn === '.rcall' || c.fn === '.__call__') return (args, _kw, self) => {
      if (!(self instanceof sj.Expr)) throw new Unsupported('not a callable field');
      return sj.rcall(self, ...args.map(plain) as (sj.ExprLike | null)[]);
    };
    if (c.fn === '.rewrite' && c.self?.t === 'Extension' && c.self['cls'] === 'CoordinateSymbol') return (args, _kw, self) => (self as dg.CoordinateSymbol).rewrite(args[0] as dg.CoordSystem);
    if (c.self?.t !== 'Extension') return undefined;
    const method = camel(c.fn.slice(1));
    return (args, kw, self) => {
      if (self === undefined || self === null) throw new Unsupported('missing receiver');
      const member: unknown = Reflect.get(self, method);
      const a = args.map(plain);
      if (['baseScalar', 'baseVector', 'baseOneform', 'coordFunction'].includes(method)) a[0] = integer(a[0]);
      if (method === 'connectTo') a[3] = { inverse: kw['inverse'], fillInGaps: kw['fill_in_gaps'] };
      if (member === undefined) throw new Unsupported(`diffgeom method ${method}`);
      const result = typeof member === 'function' ? Reflect.apply(member, self, a)
        : member instanceof sj.Expr && 'call' in member ? sj.rcall(member, ...a as (sj.ExprLike | null)[]) : member;
      return method === 'symbols' ? new JsTuple(result as unknown[]) : result;
    };
  },
};

export function runDiffgeomCase(c: Case): Outcome { return withExtension(extension, () => runCase(c)); }
export function runDiffgeomTestCase(c: TestCase): TestOutcome {
  const result = withExtension(extension, () => runTestCase(c));
  return result.exceptionMismatch === undefined ? result
    : { status: 'fail', got: `${result.exceptionMismatch.actual}; expected ${result.exceptionMismatch.expected}` };
}
