// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Prints recorded public-API calls (trace.ts) as TypeScript statements.
 */

import { callbackInfo, provenance, Snap, type CallbackInfo, type Node } from './trace';

export class Unprintable extends Error {}

/** A primitive result, printed as the library call that returned it. */
export class ResultOf {
  constructor(readonly node: Node) {}
}

const IDENT = /^[A-Za-z_$][\w$]*$/;
const RESERVED = new Set(['break', 'case', 'catch', 'class', 'const', 'continue', 'debugger', 'default', 'delete', 'do', 'else', 'enum', 'export', 'extends', 'false', 'finally', 'for', 'function', 'if', 'import', 'in', 'instanceof', 'new', 'null', 'return', 'super', 'switch', 'this', 'throw', 'true', 'try', 'typeof', 'var', 'void', 'while', 'with', 'yield', 'let', 'static', 'implements', 'interface', 'package', 'private', 'protected', 'public', 'await']);

/** Functions whose arguments accept plain numbers for integers (ExprLike). */
const EXPR_LIKE = new Set(['add', 'mul', 'pow', 'sub', 'div', 'neg', 'sqrt', 'exp', 'log', 'sin', 'cos', 'tan', 'Eq', 'Ne', 'Lt', 'Le', 'Gt', 'Ge', 'rel']);

const isObjectLike = (v: unknown): v is object => (typeof v === 'object' && v !== null) || typeof v === 'function';

/** A program under construction: the imports it needs and its statements. */
export class Program {
  readonly imports = new Map<string, Set<string>>();
  readonly lines: string[] = [];
  /** Helpers of tests/sympy-str.ts that the program uses. */
  readonly helpers = new Set<string>();
  private readonly names = new Map<Node, string>();
  private readonly uses = new Map<Node, number>();
  private readonly params = new Map<CallbackInfo, string[]>();
  private counter = 0;
  private readonly active = new Set<Node>();
  private readonly symbols = new Map<string, { token: string; name: string; assume: Record<string, boolean> }>();
  private indent = '';

  /** Count how often each node is referenced from the values that will be printed. */
  count(v: unknown, seen = new Set<unknown>()): void {
    const n = v instanceof ResultOf || v instanceof Snap ? v.node : provenanceOf(v);
    if (n !== undefined) {
      this.countNode(n, seen);
      return;
    }
    if (Array.isArray(v)) v.forEach((x) => this.count(x, seen));
    else if (v instanceof Map) for (const [a, b] of v) { this.count(a, seen); this.count(b, seen); }
    else if (v instanceof Set) for (const a of v) this.count(a, seen);
    else if (isPlain(v)) Object.values(v).forEach((x) => this.count(x, seen));
  }

  private countNode(n: Node, seen: Set<unknown>): void {
    this.uses.set(n, (this.uses.get(n) ?? 0) + 1);
    if (seen.has(n)) return;
    seen.add(n);
    switch (n.k) {
      case 'call': this.countNode(n.fn, seen); n.args.forEach((a) => this.count(a, seen)); break;
      case 'new': this.countNode(n.cls, seen); n.args.forEach((a) => this.count(a, seen)); break;
      case 'get': this.countNode(n.obj, seen); break;
      case 'method': this.countNode(n.obj, seen); n.args.forEach((a) => this.count(a, seen)); break;
      default: break;
    }
  }

  /** A node whose object the printed values use (directly or through a property). */
  uses_(n: Node): boolean {
    for (let m: Node | undefined = n; m !== undefined; m = m.k === 'get' || m.k === 'method' ? m.obj : undefined) {
      if ((this.uses.get(m) ?? 0) > 0) return true;
    }
    return false;
  }

  /** A call made for its effect on an object the program uses (a mutating method returning nothing). */
  effect(n: Node): void {
    if (n.k !== 'method') return;
    // the receiver is bound to a constant so that the effect applies to the same object
    this.uses.set(n.obj, (this.uses.get(n.obj) ?? 0) + 2);
    n.args.forEach((a) => this.count(a));
    this.lines.push(`${this.indent}${this.nodeText(n)};`);
  }

  /** The expression of a value; nodes used more than once are bound to constants first. */
  expr(v: unknown): string {
    const n = v instanceof ResultOf || v instanceof Snap ? v.node : provenanceOf(v);
    if (n !== undefined) return this.node(n);
    return this.literal(v);
  }

  private literal(v: unknown): string {
    if (v === undefined) return 'undefined';
    if (v === null) return 'null';
    if (typeof v === 'boolean') return String(v);
    if (typeof v === 'bigint') return `${v}n`;
    if (typeof v === 'number') {
      if (Number.isNaN(v)) return 'NaN';
      if (v === Infinity) return 'Infinity';
      if (v === -Infinity) return '-Infinity';
      if (Object.is(v, -0)) return '-0';
      return String(v);
    }
    if (typeof v === 'string') return quote(v);
    if (Array.isArray(v)) return `[${v.map((x) => this.expr(x)).join(', ')}]`;
    if (v instanceof Map) return `new Map(${v.size ? `[${[...v].map(([a, b]) => `[${this.expr(a)}, ${this.expr(b)}]`).join(', ')}]` : ''})`;
    if (v instanceof Set) return `new Set(${v.size ? `[${[...v].map((a) => this.expr(a)).join(', ')}]` : ''})`;
    if (typeof v === 'function') {
      const info = callbackInfo(v);
      if (info !== undefined) return this.callback(info);
      throw new Unprintable('a function that did not come from the library');
    }
    if (isPlain(v)) {
      const entries = Object.entries(v).filter(([, x]) => x !== undefined);
      return entries.length ? `{ ${entries.map(([k, x]) => `${IDENT.test(k) ? k : quote(k)}: ${this.expr(x)}`).join(', ')} }` : '{}';
    }
    throw new Unprintable(`a value without provenance (${Object.prototype.toString.call(v)} ${(v as object).constructor?.name ?? ''})`);
  }

  private node(n: Node): string {
    const bound = this.names.get(n);
    if (bound !== undefined) return bound;
    if (n.k === 'ref') return this.ref(n.module, n.name);
    if (n.k === 'param') {
      const ps = this.params.get(n.fn);
      if (ps === undefined || n.index < 0) throw new Unprintable('a callback parameter outside its callback');
      return ps[n.index] ?? 'undefined';
    }
    if (this.active.has(n)) throw new Unprintable('a value that depends on itself');
    this.active.add(n);
    let text: string;
    try {
      text = this.nodeText(n);
    } finally {
      this.active.delete(n);
    }
    if ((this.uses.get(n) ?? 0) > 1 && n.k !== 'get') {
      const name = `v${++this.counter}`;
      this.lines.push(`${this.indent}const ${name} = ${text};`);
      this.names.set(n, name);
      return name;
    }
    return text;
  }

  private nodeText(n: Node): string {
    const special = this.construction(n);
    if (special !== undefined) return special;
    switch (n.k) {
      case 'call': return `${this.callee(n.fn)}(${this.args(n.args, n.fn.k === 'ref' && EXPR_LIKE.has(n.fn.name))})`;
      case 'new': return `new ${this.callee(n.cls)}(${this.args(n.args)})`;
      case 'get':
        if (typeof n.name === 'string' && /^\d+$/.test(n.name)) {
          this.helpers.add('at');
          return `at(${this.node(n.obj)}, ${n.name})`;
        }
        return member(this.node(n.obj), n.name);
      case 'method': return `${member(this.node(n.obj), n.name)}(${this.args(n.args)})`;
      default: throw new Unprintable(n.k);
    }
  }

  /** Symbols and numbers as they are written in tests (`x`, `rational(1, 2)`). */
  private construction(n: Node, exprLike = false): string | undefined {
    if (n.k === 'new' && n.cls.k === 'ref' && n.cls.name === 'Sym' && typeof n.args[0] === 'string' && n.args.length <= 2) {
      const assume = n.args[1] ?? {};
      if (!isPlain(assume) || Object.values(assume).some((v) => typeof v !== 'boolean')) return undefined;
      return this.symbol(n.args[0], assume as Record<string, boolean>);
    }
    if (n.k === 'method' && n.obj.k === 'ref' && n.obj.name === 'Rational' && n.name === 'of' && n.args.length === 2 && n.args.every((a) => typeof a === 'bigint')) {
      const [p, q] = n.args as [bigint, bigint];
      const lit = (v: bigint): string => (v >= -(2n ** 53n) && v <= 2n ** 53n ? String(v) : `${v}n`);
      if (q === 1n && exprLike) return lit(p);
      return `${this.ref('index', 'rational')}(${q === 1n ? lit(p) : `${lit(p)}, ${lit(q)}`})`;
    }
    return undefined;
  }

  private symbol(name: string, assume: Record<string, boolean>): string {
    const key = `${name}\u0000${JSON.stringify(Object.entries(assume).sort())}`;
    let s = this.symbols.get(key);
    if (s === undefined) {
      s = { token: `\u0001${this.symbols.size}\u0001`, name, assume };
      this.symbols.set(key, s);
    }
    return s.token;
  }

  /** The symbols the program declares: their names in the code and how to rebuild them. */
  declaredSymbols(): { token: string; name: string; assume: Record<string, boolean> }[] {
    return [...this.symbols.values()];
  }

  /** The statements of the test: symbol declarations first, then the program with the symbols named. */
  finish(statements: string[]): string[] {
    const taken = new Set<string>([...this.imports.values()].flatMap((set) => [...set]));
    const plain: string[] = [];
    const named = new Map<string, string>();
    const decls: string[] = [];
    for (const s of this.symbols.values()) {
      let v = IDENT.test(s.name) && !RESERVED.has(s.name) ? s.name : `sym${named.size}`;
      while (taken.has(v) || /^v\d+$/.test(v) || v === 'sympyStr' || v === 'p0') v = `${v}_`;
      taken.add(v);
      named.set(s.token, v);
      const entries = Object.entries(s.assume);
      if (!entries.length && v === s.name && !/[\s,:]/.test(s.name)) plain.push(v);
      else decls.push(`const ${v} = new ${this.ref('index', 'Sym')}(${quote(s.name)}${entries.length ? `, { ${entries.map(([k, b]) => `${k}: ${b}`).join(', ')} }` : ''});`);
    }
    if (plain.length === 1) decls.unshift(`const ${plain[0]} = new ${this.ref('index', 'Sym')}(${quote(plain[0]!)});`);
    else if (plain.length > 1) decls.unshift(`const [${plain.join(', ')}] = ${this.ref('index', 'symbols')}(${quote(plain.join(' '))});`);
    const fill = (line: string): string => line.replace(/\u0001\d+\u0001/g, (t) => named.get(t) ?? t);
    return [...decls, ...statements.map(fill)];
  }

  private callee(n: Node): string {
    const s = this.node(n);
    return n.k === 'ref' || n.k === 'get' || n.k === 'param' || /^v\d+$/.test(s) ? s : `(${s})`;
  }

  private args(args: unknown[], exprLike = false): string {
    const out = args.map((a) => this.argExpr(a, exprLike));
    while (out.length && out[out.length - 1] === 'undefined') out.pop();
    return out.join(', ');
  }

  importName(module: string, name: string): string {
    return this.ref(module, name);
  }

  private argExpr(a: unknown, exprLike: boolean): string {
    if (exprLike && a instanceof Snap && this.names.get(a.node) === undefined) {
      const c = this.construction(a.node, true);
      if (c !== undefined) return c;
    }
    return this.expr(a);
  }

  private ref(module: string, name: string): string {
    let set = this.imports.get(module);
    if (set === undefined) this.imports.set(module, (set = new Set()));
    set.add(name);
    return name;
  }

  private callback(info: CallbackInfo): string {
    const body = info.bodies[0];
    const names = Array.from({ length: info.params }, (_, i) => `p${i}`);
    this.params.set(info, names);
    if (body === undefined) return `(${names.join(', ')}) => undefined`;
    const saved = this.indent;
    const savedLines = this.lines.length;
    this.indent += '  ';
    const sub = new Set<unknown>();
    this.count(body.result, sub);
    const result = this.expr(body.result);
    const inner = this.lines.splice(savedLines);
    this.indent = saved;
    if (!inner.length) return `(${names.join(', ')}) => ${result.startsWith('{') ? `(${result})` : result}`;
    return `(${names.join(', ')}) => {\n${inner.join('\n')}\n${saved}  return ${result};\n${saved}}`;
  }
}

function provenanceOf(v: unknown): Node | undefined {
  return isObjectLike(v) ? provenance(v) : undefined;
}

function isPlain(v: unknown): v is Record<string, unknown> {
  return typeof v === 'object' && v !== null && Object.getPrototypeOf(v) === Object.prototype;
}

function member(obj: string, name: string | symbol): string {
  if (typeof name === 'symbol') throw new Unprintable('symbol property');
  if (/^\d+$/.test(name)) return `${obj}[${name}]`;
  return IDENT.test(name) && !RESERVED.has(name) ? `${obj}.${name}` : `${obj}[${quote(name)}]`;
}

export function quote(s: string): string {
  return `'${s.replace(/\\/g, '\\\\').replace(/'/g, "\\'").replace(/\n/g, '\\n').replace(/\r/g, '\\r').replace(/\t/g, '\\t').replace(/[\u0000-\u001f\u007f-\uffff]/g, (c) => `\\u${c.charCodeAt(0).toString(16).padStart(4, '0')}`)}'`;
}
