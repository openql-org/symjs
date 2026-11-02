// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Extend module `@symjs/mathjs`: conversion between symjs and
 * math.js. math.js is not a dependency: the functions that create math.js
 * objects take your math.js instance (`import * as math from 'mathjs'` or
 * `create(all, config)`), and math.js objects are read by their structure.
 *
 * Floats: symjs Floats are binary (mpmath precision), math.js BigNumbers
 * decimal; converting rounds to the decimal digits of the Float's precision.
 */

import {
  Add,
  AppliedFunction,
  Expr,
  Float,
  Function as UndefinedFunctionOf,
  Matrix,
  Mul,
  NumberSymbol,
  Pow,
  Rational,
  Rel,
  AppliedUndef,
  S,
  Symbol as SymbolExpr,
  add,
  float,
  fn,
  freeSymbols,
  mul,
  pow,
  rel,
  str,
  sub,
  And,
  Or,
  Not,
  Xor,
} from '@symjs/symjs';
import type { ExprLike } from '@symjs/symjs';

// ---------------------------------------------------------------------------
// Structural types of the math.js objects used (no dependency on math.js)
// ---------------------------------------------------------------------------

/** A math.js expression node (math.parse result), read by its `type`. */
export interface MathNode {
  readonly type: string;
  readonly value?: unknown;
  readonly name?: string;
  readonly op?: string;
  readonly fn?: string | MathNode;
  readonly args?: readonly MathNode[];
  readonly content?: MathNode;
  readonly items?: readonly MathNode[];
  readonly conditionals?: readonly string[];
  readonly params?: readonly MathNode[];
}

/** A math.js BigNumber (decimal.js). */
export interface MathBigNumber {
  readonly isBigNumber: true;
  toString(): string;
  precision?(includeZeros?: boolean): number;
}
/** A math.js Fraction (fraction.js): sign, numerator, denominator. */
export interface MathFraction {
  readonly isFraction?: true;
  readonly s: number | bigint;
  readonly n: number | bigint;
  readonly d: number | bigint;
}
/** A math.js Complex. */
export interface MathComplex {
  readonly isComplex: true;
  readonly re: number;
  readonly im: number;
}
/** A math.js Matrix. */
export interface MathMatrix {
  readonly isMatrix: true;
  toArray(): unknown[];
}
/** A math.js scalar value. */
export type MathValue = number | boolean | MathBigNumber | MathFraction | MathComplex;

/** The parts of a math.js instance this module calls. */
export interface MathInstance {
  parse(expr: string): MathNode;
  bignumber(value: string): MathBigNumber;
  fraction(numerator: number | string, denominator?: number | string): MathFraction;
  complex(re: number, im: number): MathComplex;
  matrix(data: unknown[]): MathMatrix;
}

// ---------------------------------------------------------------------------
// Names
// ---------------------------------------------------------------------------

/** symjs function name -> math.js function name (where they differ or are known to match). */
const TO_MATHJS: Readonly<Record<string, string>> = {
  abs: 'abs',
  sin: 'sin',
  cos: 'cos',
  tan: 'tan',
  cot: 'cot',
  sec: 'sec',
  csc: 'csc',
  asin: 'asin',
  acos: 'acos',
  atan: 'atan',
  acot: 'acot',
  asec: 'asec',
  acsc: 'acsc',
  atan2: 'atan2',
  sinh: 'sinh',
  cosh: 'cosh',
  tanh: 'tanh',
  coth: 'coth',
  sech: 'sech',
  csch: 'csch',
  asinh: 'asinh',
  acosh: 'acosh',
  atanh: 'atanh',
  acoth: 'acoth',
  asech: 'asech',
  acsch: 'acsch',
  log: 'log',
  re: 're',
  im: 'im',
  arg: 'arg',
  conjugate: 'conj',
  sign: 'sign',
  floor: 'floor',
  ceiling: 'ceil',
  factorial: 'factorial',
  gamma: 'gamma',
  lgamma: 'lgamma',
  loggamma: 'lgamma',
  erf: 'erf',
  zeta: 'zeta',
  binomial: 'combinations',
  Min: 'min',
  Max: 'max',
};
const FROM_MATHJS: Readonly<Record<string, string>> = Object.fromEntries([...Object.entries(TO_MATHJS).map(([a, b]) => [b, a]), ['ceil', 'ceiling'], ['conj', 'conjugate']]);

/** symjs constant -> math.js symbol. */
const CONSTANTS_TO: Readonly<Record<string, string>> = { pi: 'pi', E: 'e', I: 'i', GoldenRatio: 'phi', oo: 'Infinity', '-oo': '-Infinity', nan: 'NaN', zoo: 'Infinity' };

// ---------------------------------------------------------------------------
// symjs -> math.js
// ---------------------------------------------------------------------------

const fail = (what: string): never => {
  throw new TypeError(`@symjs/mathjs: ${what}`);
};

/**
 * An expression in math.js syntax (fully parenthesized, `^` for powers,
 * math.js function names), e.g. `((2 * x) + sin(y))`.
 */
export function toMathjsString(expr: ExprLike): string {
  const e = expr instanceof Expr ? expr : (add(expr, 0) as Expr);
  return printNode(e);
}

function printNode(e: Expr): string {
  if (e instanceof Rational) return e.q === 1n ? (e.p < 0n ? `(${e.p})` : `${e.p}`) : `(${e.p} / ${e.q})`;
  if (e instanceof Float) {
    const s = str(e);
    return s.startsWith('-') ? `(${s})` : s;
  }
  if (e instanceof SymbolExpr) return e.name;
  if (e instanceof NumberSymbol) return CONSTANTS_TO[e.name] ?? fail(`no math.js constant for ${e.name}`);
  const special = CONSTANTS_TO[str(e)];
  if (e.args.length === 0 && special) return special.startsWith('-') ? `(${special})` : special;
  if (e.kind === 'Bool') return str(e) === 'True' ? 'true' : 'false';
  if (e instanceof Add) return `(${e.args.map(printNode).join(' + ')})`;
  if (e instanceof Mul) return `(${e.args.map(printNode).join(' * ')})`;
  if (e instanceof Pow) {
    const b = e.base;
    if (b instanceof NumberSymbol && b.name === 'E') return `exp(${printNode(e.exp)})`;
    return `(${printNode(b)} ^ ${printNode(e.exp)})`;
  }
  if (e instanceof Rel) {
    const op = ({ Eq: '==', Ne: '!=', Lt: '<', Le: '<=', Gt: '>', Ge: '>=' } as Record<string, string>)[e.op] ?? fail(`relation ${e.op}`);
    return `(${printNode(e.args[0]!)} ${op} ${printNode(e.args[1]!)})`;
  }
  if (e.kind === 'BoolOp') {
    const head = (e as unknown as { op: string }).op;
    if (head === 'Not') return `(not ${printNode(e.args[0]!)})`;
    if (head === 'And' || head === 'Or' || head === 'Xor') return `(${e.args.map(printNode).join(` ${head.toLowerCase()} `)})`;
  }
  if (e instanceof AppliedFunction || e instanceof AppliedUndef) {
    const name = TO_MATHJS[e.name] ?? e.name;
    return `${name}(${e.args.map(printNode).join(', ')})`;
  }
  return fail(`cannot convert ${str(e)} to math.js syntax`);
}

/** The expression as a math.js expression tree (math.parse of toMathjsString). */
export function toMathjs(expr: ExprLike, math: Pick<MathInstance, 'parse'>): MathNode {
  return math.parse(toMathjsString(expr));
}

/**
 * A number as a math.js value: integers and Floats as JS numbers (or
 * BigNumbers with `{ bignumber: true }`), non-integer rationals as
 * Fractions with `{ fraction: true }` (else numbers), complex numbers as
 * Complex.
 */
export function toMathjsValue(expr: ExprLike, math: Pick<MathInstance, 'bignumber' | 'fraction' | 'complex'>, opts: { bignumber?: boolean; fraction?: boolean } = {}): MathValue {
  const e = expr instanceof Expr ? expr : (add(expr, 0) as Expr);
  if (e instanceof Rational) {
    if (e.q !== 1n && opts.fraction === true) return math.fraction(e.p.toString(), e.q.toString());
    if (opts.bignumber === true) return e.q === 1n ? math.bignumber(e.p.toString()) : math.bignumber(str(float(e, 30)));
    return e.toNumber();
  }
  if (e instanceof Float) return opts.bignumber === true ? math.bignumber(str(e).replace(/\.$/, '')) : e.toNumber();
  if (e.kind === 'Bool') return str(e) === 'True';
  if (freeSymbols(e).size !== 0) return fail(`${str(e)} is not a number`);
  const c = e.toComplex();
  return c.im === 0 ? c.re : math.complex(c.re, c.im);
}

/** A matrix of numbers as a math.js Matrix (entries by toMathjsValue). */
export function toMathjsMatrix(m: Matrix, math: Pick<MathInstance, 'matrix' | 'bignumber' | 'fraction' | 'complex'>, opts: { bignumber?: boolean; fraction?: boolean } = {}): MathMatrix {
  return math.matrix(m.toArray().map((row) => row.map((v) => toMathjsValue(v, math, opts))));
}

// ---------------------------------------------------------------------------
// math.js -> symjs
// ---------------------------------------------------------------------------

const isObject = (v: unknown): v is Record<string, unknown> => typeof v === 'object' && v !== null;

/** Options of fromMathjs. */
export interface FromMathjsOptions {
  /** Symbols to use by name (default: new symbols). */
  symbols?: Readonly<Record<string, Expr>>;
  /** Functions to use by math.js name (default: SymPy-named functions, else undefined functions). */
  functions?: Readonly<Record<string, (...args: Expr[]) => Expr>>;
}

/**
 * A math.js value as an expression: integers become exact Rationals, other
 * numbers Floats, BigNumbers Floats with their decimal precision,
 * Fractions Rationals, Complex values a + b*I.
 */
export function fromMathjsValue(v: unknown): Expr {
  if (typeof v === 'number') {
    if (Number.isInteger(v)) return Rational.of(BigInt(v));
    if (Number.isNaN(v)) return S.NaN;
    if (!Number.isFinite(v)) return v > 0 ? S.Infinity : S.NegativeInfinity;
    return new Float(v);
  }
  if (typeof v === 'bigint') return Rational.of(v);
  if (typeof v === 'boolean') return v ? S.true : S.false;
  if (isObject(v)) {
    if (v['isBigNumber'] === true) {
      const s = (v as unknown as MathBigNumber).toString();
      if (/^-?\d+$/.test(s)) return Rational.of(BigInt(s));
      if (s === 'NaN') return S.NaN;
      if (s === 'Infinity' || s === '-Infinity') return s === 'Infinity' ? S.Infinity : S.NegativeInfinity;
      const digits = s.replace(/^-/, '').replace(/e.*$/i, '').replace('.', '').replace(/^0+/, '').length;
      return float(s, Math.max(15, digits));
    }
    if (v['isFraction'] === true || ('n' in v && 'd' in v && 's' in v)) {
      const sgn = BigInt(v['s'] as number | bigint);
      return Rational.of(sgn * BigInt(v['n'] as number | bigint), BigInt(v['d'] as number | bigint));
    }
    if (v['isComplex'] === true) return add(fromMathjsValue(v['re']), mul(fromMathjsValue(v['im']), S.I));
  }
  return fail(`cannot convert the math.js value ${typeof v === 'object' ? JSON.stringify(v) : typeof v === 'symbol' || typeof v === 'function' ? typeof v : `${v as string | number | boolean | bigint | undefined}`}`);
}

const OPERATORS: Readonly<Record<string, (args: Expr[]) => Expr>> = {
  add: (a) => add(...a),
  subtract: ([a, b]) => sub(a!, b!),
  multiply: (a) => mul(...a),
  divide: ([a, b]) => mul(a!, pow(b!, -1)),
  pow: ([a, b]) => pow(a!, b!),
  dotPow: ([a, b]) => pow(a!, b!),
  unaryMinus: ([a]) => mul(-1, a!),
  unaryPlus: ([a]) => a!,
  mod: ([a, m]) => (a instanceof Rational && m instanceof Rational && a.q === 1n && m.q === 1n && m.p !== 0n ? Rational.of(((a.p % m.p) + m.p) % m.p) : UndefinedFunctionOf('mod')(a!, m!)),
  factorial: (a) => fn('factorial', a),
  equal: ([a, b]) => rel('Eq', a!, b!),
  unequal: ([a, b]) => rel('Ne', a!, b!),
  smaller: ([a, b]) => rel('Lt', a!, b!),
  smallerEq: ([a, b]) => rel('Le', a!, b!),
  larger: ([a, b]) => rel('Gt', a!, b!),
  largerEq: ([a, b]) => rel('Ge', a!, b!),
  and: (a) => And(...a),
  or: (a) => Or(...a),
  xor: (a) => Xor(...a),
  not: ([a]) => Not(a!),
};
const RELATIONS: Readonly<Record<string, string>> = { equal: 'Eq', unequal: 'Ne', smaller: 'Lt', smallerEq: 'Le', larger: 'Gt', largerEq: 'Ge' };

const SYMBOLS_FROM: Readonly<Record<string, () => Expr>> = {
  pi: () => S.Pi,
  e: () => S.E,
  E: () => S.E,
  i: () => S.I,
  phi: () => S.GoldenRatio,
  Infinity: () => S.Infinity,
  NaN: () => S.NaN,
  true: () => S.true,
  false: () => S.false,
};

/** A math.js expression tree (math.parse result) as an expression. */
export function fromMathjs(node: MathNode, opts: FromMathjsOptions = {}): Expr {
  const go = (n: MathNode): Expr => {
    switch (n.type) {
      case 'ConstantNode':
        return fromMathjsValue(n.value);
      case 'SymbolNode': {
        const name = n.name ?? fail('SymbolNode without a name');
        const known = opts.symbols?.[name];
        if (known) return known;
        const c = SYMBOLS_FROM[name];
        return c ? c() : new SymbolExpr(name);
      }
      case 'ParenthesisNode':
        return go(n.content ?? fail('ParenthesisNode without content'));
      case 'OperatorNode': {
        const f = typeof n.fn === 'string' ? n.fn : fail('OperatorNode without fn');
        const op = OPERATORS[f] ?? fail(`unsupported operator ${f}`);
        return op((n.args ?? []).map(go));
      }
      case 'FunctionNode': {
        const name = typeof n.fn === 'object' && n.fn.name !== undefined ? n.fn.name : typeof n.name === 'string' ? n.name : fail('FunctionNode without a name');
        const args = (n.args ?? []).map(go);
        const user = opts.functions?.[name];
        if (user) return user(...args);
        if (name === 'exp') return pow(S.E, args[0]!);
        if (name === 'sqrt') return pow(args[0]!, Rational.of(1n, 2n));
        if (name === 'cbrt') return pow(args[0]!, Rational.of(1n, 3n));
        if (name === 'nthRoot') return pow(args[0]!, pow(args[1]!, -1));
        if (name === 'log' && args.length === 2) return mul(fn('log', [args[0]!]), pow(fn('log', [args[1]!]), -1));
        if (name === 'log10') return mul(fn('log', [args[0]!]), pow(fn('log', [10]), -1));
        if (name === 'log2') return mul(fn('log', [args[0]!]), pow(fn('log', [2]), -1));
        const sympyName = FROM_MATHJS[name];
        if (sympyName) return fn(sympyName as Parameters<typeof fn>[0], args);
        return UndefinedFunctionOf(name)(...args);
      }
      case 'RelationalNode': {
        const params = (n.params ?? []).map(go);
        const parts = (n.conditionals ?? []).map((c, i) => rel((RELATIONS[c] ?? fail(`relation ${c}`)) as never, params[i]!, params[i + 1]!));
        return And(...parts);
      }
      default:
        return fail(`unsupported math.js node ${n.type}`);
    }
  };
  return go(node);
}

/** math.parse(text) converted to an expression. */
export function fromMathjsString(text: string, math: Pick<MathInstance, 'parse'>, opts: FromMathjsOptions = {}): Expr {
  return fromMathjs(math.parse(text), opts);
}

/** A math.js Matrix (or nested array) of values as a Matrix; a vector becomes a column. */
export function fromMathjsMatrix(m: MathMatrix | readonly unknown[]): Matrix {
  const data = Array.isArray(m) ? (m as unknown[]) : (m as MathMatrix).toArray();
  const rows = data.map((r) => (Array.isArray(r) ? (r as unknown[]).map(fromMathjsValue) : [fromMathjsValue(r)]));
  return Matrix.of(rows);
}
