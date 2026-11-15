// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Records the public-API calls that a replayed case makes.
 *
 * The exports of the symjs entry points are wrapped in proxies. Every call,
 * construction, method call and property read that goes through them becomes
 * a node of a program; objects that come out of the library are wrapped as
 * well, so later calls on them are recorded too. `program.ts` prints the nodes
 * that a result depends on as TypeScript.
 */

export type Node =
  | { k: 'ref'; module: string; name: string }
  | { k: 'call'; fn: Node; args: unknown[] }
  | { k: 'new'; cls: Node; args: unknown[] }
  | { k: 'get'; obj: Node; name: string | symbol }
  | { k: 'method'; obj: Node; name: string | symbol; args: unknown[] }
  | { k: 'param'; fn: CallbackInfo; index: number };

/** A function that the replay passed into the library (a callback). */
export interface CallbackInfo {
  params: number;
  /** The nodes created while the library ran the callback, by invocation. */
  bodies: { created: Node[]; result: unknown }[];
}

/** An argument as it was when the call was made: the node that last produced the object. */
export class Snap {
  constructor(readonly node: Node) {}
}

const nodeOf = new WeakMap<object, Node>();
const targetOf = new WeakMap<object, object>();
const proxyOf = new WeakMap<object, object>();
const callbackOf = new WeakMap<Function, CallbackInfo>();
const sourceOf = new WeakMap<Function, Function>();

// Function sources are read for parameter names; a wrapper reports the source of what it wraps.
const toSource = Function.prototype.toString;
Function.prototype.toString = function (this: Function): string {
  return toSource.call(sourceOf.get(this) ?? (targetOf.get(this) as Function | undefined) ?? this);
};

let log: Node[] | undefined;
let depth = 0;

/** The node that produced a value, if the value came out of the library. */
export function provenance(v: unknown): Node | undefined {
  return (typeof v === 'object' && v !== null) || typeof v === 'function' ? nodeOf.get(v as object) : undefined;
}

export function unwrap<T>(v: T): T {
  if ((typeof v === 'object' && v !== null) || typeof v === 'function') {
    const t = targetOf.get(v as object);
    if (t !== undefined) return t as T;
  }
  return v;
}

export function callbackInfo(f: Function): CallbackInfo | undefined {
  return callbackOf.get(f);
}

/** Run f without recording (the generator's own uses of the library). */
export function quiet<T>(f: () => T): T {
  depth++;
  try {
    return f();
  } finally {
    depth--;
  }
}

/** Run f and return the nodes recorded while it ran (only the outermost recording collects). */
export function record<T>(f: () => T): { value: T; nodes: Node[] } {
  const saved = log;
  log = [];
  try {
    return { value: f(), nodes: log };
  } finally {
    log = saved;
  }
}

function note(n: Node): Node {
  if (depth === 0) log?.push(n);
  return n;
}

const isObjectLike = (v: unknown): v is object => (typeof v === 'object' && v !== null) || typeof v === 'function';

/** Values the library returns to the replay are wrapped so that later uses are recorded. */
function wrapOut(v: unknown, n: Node): unknown {
  if (!isObjectLike(v)) return v;
  if (targetOf.has(v)) return v;
  // plain containers are left as they are; their items are registered by identity
  if (Array.isArray(v)) {
    nodeOf.set(v, n);
    v.forEach((item, i) => { if (isObjectLike(item)) setNode(item, { k: 'get', obj: n, name: String(i) }); });
    return v;
  }
  if (v instanceof Promise || v instanceof Set || v instanceof WeakMap || v instanceof RegExp) return v;
  if (v instanceof Map) {
    nodeOf.set(v, n);
    for (const [key, item] of v) if (isObjectLike(item)) setNode(item, { k: 'method', obj: n, name: 'get', args: [snap(key)] });
    return v;
  }
  const p = proxyFor(v);
  setNode(v, n);
  return p;
}

function proxyFor(v: object): object {
  const cached = proxyOf.get(v);
  if (cached !== undefined) return cached;
  const p = new Proxy(v, handler);
  proxyOf.set(v, p);
  targetOf.set(p, v);
  return p;
}

/** An object that comes out of the library again gets the newer provenance (exports keep their name). */
function setNode(item: object, n: Node): void {
  const t = targetOf.get(item) ?? item;
  if (nodeOf.get(t)?.k === 'ref') return;
  nodeOf.set(t, n);
  const p = proxyOf.get(t);
  if (p !== undefined) nodeOf.set(p, n);
}

/** The arguments of a call as they are now: library objects become snapshots of their provenance. */
function snap(v: unknown): unknown {
  if (typeof v === 'function' && callbackOf.has(v)) return v;
  if (isObjectLike(v)) {
    const n = nodeOf.get(v);
    if (n !== undefined && !Array.isArray(v) && !(v instanceof Map)) return new Snap(n);
    if (Array.isArray(v)) return n !== undefined && targetOf.has(v) ? new Snap(n) : v.map(snap);
    if (v instanceof Map) return new Map([...v].map(([a, b]) => [snap(a), snap(b)]));
    if (v instanceof Set) return new Set([...v].map(snap));
    if (Object.getPrototypeOf(v) === Object.prototype) {
      const o: Record<string, unknown> = {};
      for (const [k, x] of Object.entries(v)) o[k] = snap(x);
      return o;
    }
  }
  return v;
}

/** Arguments the replay passes into the library are unwrapped; callbacks are recorded. */
function unwrapIn(v: unknown): unknown {
  if (typeof v === 'function' && !targetOf.has(v)) return traceCallback(v as (...a: unknown[]) => unknown);
  if (Array.isArray(v)) {
    const t = targetOf.get(v);
    return t ?? v.map(unwrapIn);
  }
  if (isObjectLike(v)) {
    const t = targetOf.get(v);
    if (t !== undefined) return t;
    if (Object.getPrototypeOf(v) === Object.prototype) {
      const o: Record<string, unknown> = {};
      for (const [k, x] of Object.entries(v)) o[k] = unwrapIn(x);
      return o;
    }
  }
  return v;
}

function traceCallback(f: (...a: unknown[]) => unknown): (...a: unknown[]) => unknown {
  const info: CallbackInfo = { params: f.length, bodies: [] };
  const g = function (this: unknown, ...args: unknown[]): unknown {
    const savedDepth = depth;
    const savedLog = log;
    depth = 0;
    const created: Node[] = [];
    log = created;
    try {
      const wrapped = args.map((a, i) => wrapOut(a, { k: 'param', fn: info, index: i }));
      const result = f.apply(this, wrapped);
      info.bodies.push({ created, result });
      return unwrapIn(result);
    } finally {
      depth = savedDepth;
      log = savedLog;
    }
  };
  Object.defineProperty(g, 'length', { value: f.length });
  Object.defineProperty(g, 'name', { value: f.name });
  sourceOf.set(g, f);
  callbackOf.set(g, info);
  nodeOf.set(g, { k: 'param', fn: info, index: -1 });
  return g;
}

function argsIn(args: unknown[]): unknown[] {
  return args.map(unwrapIn);
}

/** The arguments with the replay's functions replaced by their recorded wrappers. */
function withCallbacks(args: unknown[], real: unknown[]): unknown[] {
  return args.map((a, i) => (typeof a === 'function' && !targetOf.has(a) ? real[i] : a));
}

function recorded(args: unknown[]): unknown[] {
  return args.map(snap);
}

/** The library calls of the current recording with their results, in order. */
export const results: { node: Node; value: unknown }[] = [];
/** The library call that threw last, with its error. */
export let thrown: { node: Node; error: unknown } | undefined;

export function resetResults(): void {
  results.length = 0;
  thrown = undefined;
}

function invoke<T>(n: Node, run: () => T): unknown {
  // calls made by the library itself are not part of the program
  depth++;
  let out: T;
  try {
    out = run();
  } catch (e) {
    depth--;
    if (depth === 0) thrown = { node: n, error: e };
    throw e;
  }
  depth--;
  note(n);
  if (depth === 0) results.push({ node: n, value: out });
  return wrapOut(out, n);
}

const handler: ProxyHandler<object> = {
  get(target, prop) {
    const v: unknown = Reflect.get(target, prop, target);
    const self = nodeOf.get(target);
    if (self === undefined || depth > 0 || prop === 'then' || typeof prop === 'symbol' || prop === 'prototype' || prop === 'constructor') return v;
    if (typeof v === 'function') {
      if (proxyOf.has(v as object) || targetOf.has(v as object)) return v;
      const method = v as (...a: unknown[]) => unknown;
      // classes stored as properties (S.Integers is an object, Q.even a function) keep their identity
      const bound = function (this: unknown, ...args: unknown[]): unknown {
        const real = argsIn(args);
        return invoke({ k: 'method', obj: self, name: prop, args: recorded(withCallbacks(args, real)) }, () => method.apply(target, real));
      };
      Object.defineProperty(bound, 'name', { value: method.name });
      Object.defineProperty(bound, 'length', { value: method.length });
      sourceOf.set(bound, method);
      return bound;
    }
    if (!isObjectLike(v)) {
      // a primitive attribute (is_integer, p, name) read from a library object
      results.push({ node: { k: 'get', obj: self, name: prop }, value: v });
      return v;
    }
    const known = nodeOf.get(v);
    if (known?.k === 'ref') return wrapOut(v, known);
    return wrapOut(v, { k: 'get', obj: self, name: prop });
  },
  apply(target, thisArg, args) {
    const self = nodeOf.get(target);
    if (/^class[\s{]/.test(Function.prototype.toString.call(target))) return handler.construct!(target, args, target as Function);
    if (self === undefined || depth > 0) return Reflect.apply(target as (...a: unknown[]) => unknown, unwrap(thisArg), argsIn(args));
    const real = argsIn(args);
    return invoke({ k: 'call', fn: self, args: recorded(withCallbacks(args, real)) }, () => Reflect.apply(target as (...a: unknown[]) => unknown, unwrap(thisArg), real));
  },
  construct(target, args, newTarget) {
    const self = nodeOf.get(target);
    const real = argsIn(args);
    const nt = newTarget === proxyOf.get(target) ? target : newTarget;
    if (self === undefined || depth > 0) return Reflect.construct(target as new (...a: unknown[]) => object, real, nt as new (...a: unknown[]) => object);
    return invoke({ k: 'new', cls: self, args: recorded(withCallbacks(args, real)) }, () => Reflect.construct(target as new (...a: unknown[]) => object, real, nt as new (...a: unknown[]) => object)) as object;
  },
};

/** The exports of an entry point, each wrapped so that its uses are recorded. */
export function traceModule(ns: Record<string, unknown>, module: string): Record<string, unknown> {
  const out: Record<string, unknown> = {};
  for (const [name, v] of Object.entries(ns)) {
    if (!isObjectLike(v)) {
      out[name] = v;
      continue;
    }
    const ref: Node = { k: 'ref', module, name };
    const cached = proxyOf.get(v);
    if (cached !== undefined) {
      out[name] = cached;
      continue;
    }
    const p = new Proxy(v, handler);
    proxyOf.set(v, p);
    targetOf.set(p, v);
    nodeOf.set(p, ref);
    nodeOf.set(v, ref);
    out[name] = p;
  }
  // the replay looks names up dynamically; a missing name reads as undefined like a namespace object's
  return new Proxy(out, { has: () => true, get: (t, k) => Reflect.get(t, k) });
}
