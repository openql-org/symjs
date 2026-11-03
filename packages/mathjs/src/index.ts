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
  SymFunction as UndefinedFunctionOf,
  Matrix,
  Mul,
  NumberSymbol,
  Pow,
  Rational,
  Rel,
  AppliedUndef,
  S,
  Sym as SymbolExpr,
  add,
  float,
  fn,
  freeSymbols,
  mul,
  pow,
  Eq,
  Ne,
  Lt,
  Le,
  Gt,
  Ge,
  str,
  sub,
  And,
  Or,
  Not,
  Xor,
} from '@symjs/symjs';
import type { ExprLike, FnName, RelOp } from '@symjs/symjs';

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
const TO_MATHJS_PAIRS: readonly (readonly [FnName, string])[] = [
  ['abs', 'abs'],
  ['sin', 'sin'],
  ['cos', 'cos'],
  ['tan', 'tan'],
  ['cot', 'cot'],
  ['sec', 'sec'],
  ['csc', 'csc'],
  ['asin', 'asin'],
  ['acos', 'acos'],
  ['atan', 'atan'],
  ['acot', 'acot'],
  ['asec', 'asec'],
  ['acsc', 'acsc'],
  ['atan2', 'atan2'],
  ['sinh', 'sinh'],
  ['cosh', 'cosh'],
  ['tanh', 'tanh'],
  ['coth', 'coth'],
  ['sech', 'sech'],
  ['csch', 'csch'],
  ['asinh', 'asinh'],
  ['acosh', 'acosh'],
  ['atanh', 'atanh'],
  ['acoth', 'acoth'],
  ['asech', 'asech'],
  ['acsch', 'acsch'],
  ['log', 'log'],
  ['re', 're'],
  ['im', 'im'],
  ['arg', 'arg'],
  ['conjugate', 'conj'],
  ['sign', 'sign'],
  ['floor', 'floor'],
  ['ceiling', 'ceil'],
  ['factorial', 'factorial'],
  ['gamma', 'gamma'],
  ['loggamma', 'lgamma'],
  ['erf', 'erf'],
  ['zeta', 'zeta'],
  ['binomial', 'combinations'],
  ['Min', 'min'],
  ['Max', 'max'],
];
const TO_MATHJS: Readonly<Record<string, string>> = Object.fromEntries([...TO_MATHJS_PAIRS, ['lgamma', 'lgamma']]);
/** math.js function name -> symjs function name. */
const FROM_MATHJS: ReadonlyMap<string, FnName> = new Map<string, FnName>([...TO_MATHJS_PAIRS.map(([a, b]): [string, FnName] => [b, a]), ['ceil', 'ceiling'], ['conj', 'conjugate']]);

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
  const e = expr instanceof Expr ? expr : (add(expr, 0));
  return printNode(e);
}

const REL_TO_MATHJS: Record<RelOp, string> = { Eq: '==', Ne: '!=', Lt: '<', Le: '<=', Gt: '>', Ge: '>=' };

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
    const op = REL_TO_MATHJS[e.op];
    return `(${printNode(e.args[0])} ${op} ${printNode(e.args[1])})`;
  }
  if (e.kind === 'BoolOp' && 'op' in e && typeof e.op === 'string') {
    const head = e.op;
    if (head === 'Not') return `(not ${e.args.map(printNode).join(', ')})`;
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
  const e = expr instanceof Expr ? expr : (add(expr, 0));
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
const isArray = (v: unknown): v is readonly unknown[] => Array.isArray(v);
const isBigNumber = (v: Record<string, unknown>): v is Record<string, unknown> & MathBigNumber => v['isBigNumber'] === true;
/** A fraction.js field (sign, numerator or denominator) as a BigInt argument. */
const fractionPart = (x: unknown): number | bigint | string => (typeof x === 'number' || typeof x === 'bigint' || typeof x === 'string' ? x : fail(`invalid math.js Fraction field ${typeof x}`));
/** A math.js value for an error message. */
function describeValue(v: unknown): string {
  switch (typeof v) {
    case 'object':
      return JSON.stringify(v);
    case 'symbol':
    case 'function':
      return typeof v;
    case 'string':
    case 'number':
    case 'bigint':
    case 'boolean':
    case 'undefined':
      return `${v}`;
  }
}

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
    if (isBigNumber(v)) {
      const s = v.toString();
      if (/^-?\d+$/.test(s)) return Rational.of(BigInt(s));
      if (s === 'NaN') return S.NaN;
      if (s === 'Infinity' || s === '-Infinity') return s === 'Infinity' ? S.Infinity : S.NegativeInfinity;
      const digits = s.replace(/^-/, '').replace(/e.*$/i, '').replace('.', '').replace(/^0+/, '').length;
      return float(s, Math.max(15, digits));
    }
    if (v['isFraction'] === true || ('n' in v && 'd' in v && 's' in v)) {
      const sgn = BigInt(fractionPart(v['s']));
      return Rational.of(sgn * BigInt(fractionPart(v['n'])), BigInt(fractionPart(v['d'])));
    }
    if (v['isComplex'] === true) return add(fromMathjsValue(v['re']), mul(fromMathjsValue(v['im']), S.I));
  }
  return fail(`cannot convert the math.js value ${describeValue(v)}`);
}

/** An operand of a math.js operator; throws when the node has too few arguments. */
const opd = (x: Expr | undefined): Expr => x ?? fail('operator with too few arguments');
const OPERATORS: Readonly<Record<string, (args: Expr[]) => Expr>> = {
  add: (a) => add(...a),
  subtract: ([a, b]) => sub(opd(a), opd(b)),
  multiply: (a) => mul(...a),
  divide: ([a, b]) => mul(opd(a), pow(opd(b), -1)),
  pow: ([a, b]) => pow(opd(a), opd(b)),
  dotPow: ([a, b]) => pow(opd(a), opd(b)),
  unaryMinus: ([a]) => mul(-1, opd(a)),
  unaryPlus: ([a]) => opd(a),
  mod: ([a, m]) => (a instanceof Rational && m instanceof Rational && a.q === 1n && m.q === 1n && m.p !== 0n ? Rational.of(((a.p % m.p) + m.p) % m.p) : UndefinedFunctionOf('mod')(opd(a), opd(m))),
  factorial: (a) => fn('factorial', a),
  equal: ([a, b]) => Eq(opd(a), opd(b)),
  unequal: ([a, b]) => Ne(opd(a), opd(b)),
  smaller: ([a, b]) => Lt(opd(a), opd(b)),
  smallerEq: ([a, b]) => Le(opd(a), opd(b)),
  larger: ([a, b]) => Gt(opd(a), opd(b)),
  largerEq: ([a, b]) => Ge(opd(a), opd(b)),
  and: (a) => And(...a),
  or: (a) => Or(...a),
  xor: (a) => Xor(...a),
  not: ([a]) => Not(opd(a)),
};
const RELATIONS: Readonly<Record<string, (a: Expr, b: Expr) => Expr>> = { equal: Eq, unequal: Ne, smaller: Lt, smallerEq: Le, larger: Gt, largerEq: Ge };

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
        const arg = (xs: readonly Expr[], i: number): Expr => xs[i] ?? fail(`${name} needs ${i + 1} arguments`);
        const user = opts.functions?.[name];
        if (user) return user(...args);
        if (name === 'exp') return pow(S.E, arg(args, 0));
        if (name === 'sqrt') return pow(arg(args, 0), Rational.of(1n, 2n));
        if (name === 'cbrt') return pow(arg(args, 0), Rational.of(1n, 3n));
        if (name === 'nthRoot') return pow(arg(args, 0), pow(arg(args, 1), -1));
        if (name === 'log' && args.length === 2) return mul(fn('log', [arg(args, 0)]), pow(fn('log', [arg(args, 1)]), -1));
        if (name === 'log10') return mul(fn('log', [arg(args, 0)]), pow(fn('log', [10]), -1));
        if (name === 'log2') return mul(fn('log', [arg(args, 0)]), pow(fn('log', [2]), -1));
        const sympyName = FROM_MATHJS.get(name);
        if (sympyName !== undefined) return fn(sympyName, args);
        return UndefinedFunctionOf(name)(...args);
      }
      case 'RelationalNode': {
        const params = (n.params ?? []).map(go);
        const parts = (n.conditionals ?? []).map((c, i) => (RELATIONS[c] ?? fail(`relation ${c}`))(params[i] ?? fail('relation without an operand'), params[i + 1] ?? fail('relation without an operand')));
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
  const data: readonly unknown[] = isArray(m) ? m : m.toArray();
  const rows = data.map((r) => (isArray(r) ? r.map((x) => fromMathjsValue(x)) : [fromMathjsValue(r)]));
  return Matrix.of(rows);
}
