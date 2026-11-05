// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Expression parser and the `ex` tagged template.
 *
 * Grammar (precedence low -> high):
 *   sum     := product (('+' | '-') product)*
 *   product := unary (('*' | '/') unary)*
 *   unary   := ('-' | '+') unary | power
 *   power   := atom (('^' | '**') unary)?       (right associative)
 *   atom    := number | name | name '(' args ')' | '(' sum ')' | interpolated value
 *   arg     := sum | '(' sum (',' sum)* ')'       (a tuple, for the limits of Integral, Sum, ...)
 */

import type { Assumptions, Expr, ExprLike, FnName, RelOp, SpecialFnName } from '../core/nodes';
import { Add, BoolAtom, Float, Integral, Mul, Order, Pow, Rational, Rel, S, Sym, impl } from '../core/nodes';
import { NotImplementedError } from '../core/errors';
import { Product, Sum } from '../core/concrete';
import { Subs } from '../core/subsnode';
import { float } from '../numeric/floatctor';
import { BoolOp, and, not, or, xor } from '../core/boolalg';
import { add, div, exp, mul, neg, pow, sqrt, sub, sympify } from '../core/ops';
import { fn } from '../functions/elementary/elementary';
import { at, defined } from '../core/guard';
import { piecewise, rel } from '../core/logic';
import { SymFunction, derivative } from '../core/undef';

export interface ParseOptions {
  /** Predefined symbols (by name). */
  symbols?: Readonly<Record<string, Expr>> | readonly Sym[];
  /** Assumptions for symbols created implicitly by the parser. */
  assumptions?: Assumptions;
  /** false: keep the arithmetic unevaluated (SymPy evaluate=False). */
  evaluate?: boolean;
  /** false: '^' is logical Xor instead of power (SymPy convert_xor=False). */
  convertXor?: boolean;
  /**
   * SymPy parse_expr transformations: 'implicit' allows implicit
   * multiplication (2x, x y, x(y + 1)), function application without
   * parentheses (sin x) and function exponentiation (sin**2(x) is
   * sin(x)**2); 'all' also splits unknown names into one-letter symbols
   * (xyz is x*y*z; names of Greek letters and names with an underscore are
   * kept, as SymPy's split_symbols does).
   */
  transformations?: 'standard' | 'implicit' | 'all';
  /** true: '=' is an equation (SymPy's convert_equals_signs transformation): 1*2 = x is Eq(2, x). */
  convertEqualsSigns?: boolean;
  /**
   * Names to use while parsing (SymPy locals / local_dict): an expression
   * replaces the name, a function is called with the parsed arguments.
   */
  locals?: Readonly<Record<string, ExprLike | ((...args: Expr[]) => ExprLike)>>;
}

type Token =
  | { t: 'num'; v: string; pos: number }
  | { t: 'name'; v: string; pos: number }
  | { t: 'op'; v: string; pos: number }
  | { t: 'value'; v: Expr; pos: number }
  | { t: 'end'; pos: number };

/** SymPy repeating decimals: '1.2[3]' = 1.2333... = 37/30. */
function repeatingDecimal(s: string): Rational {
  // the tokenizer only passes strings of this form, so every group is present
  const [, int = '', frac = '', rep = ''] = defined(/^(\d*)\.(\d*)\[(\d+)\]$/.exec(s), 'repeating decimal');
  const fixed = BigInt((int || '0') + frac);
  const scale = 10n ** BigInt(frac.length);
  const nines = 10n ** BigInt(rep.length) - 1n;
  // fixed/scale + rep/(nines*scale)
  return Rational.of(fixed * nines + BigInt(rep), nines * scale);
}

function tokenize(src: string, offset: number, out: Token[]): void {
  const re = /\s*(?:(\d*\.\d*\[\d+\])|(\d+(?:\.\d*)?(?:[eE][+-]?\d+)?|\.\d+(?:[eE][+-]?\d+)?)|([A-Za-z_Ͱ-Ͽ][A-Za-z0-9_Ͱ-Ͽ']*)|(\*\*|<=|>=|[-+*/^(),&|~<>=]))/y;
  let i = 0;
  while (i < src.length) {
    if (/^\s*$/.test(src.slice(i))) return;
    re.lastIndex = i;
    const m = re.exec(src);
    if (!m) throw new SyntaxError(`Unexpected character '${src[i]?.trim() || src.slice(i).trim()[0]}' at ${offset + i}`);
    const pos = offset + i + (m[0].length - m[0].trimStart().length);
    if (m[1] !== undefined) out.push({ t: 'value', v: repeatingDecimal(m[1]), pos });
    else if (m[2] !== undefined) out.push({ t: 'num', v: m[2], pos });
    else if (m[3] !== undefined) out.push({ t: 'name', v: m[3], pos });
    else out.push({ t: 'op', v: defined(m[4], 'operator token'), pos });
    i = re.lastIndex;
  }
}

const SPECIAL_NAMES: SpecialFnName[] = [
  'factorial',
  'factorial2',
  'binomial',
  'ff',
  'rf',
  'subfactorial',
  'harmonic',
  'catalan',
  'gamma',
  'loggamma',
  'polygamma',
  'lowergamma',
  'uppergamma',
  'beta',
  'zeta',
  'erf',
  'erfc',
  'erfi',
  'erf2',
  'erfinv',
  'erfcinv',
  'erf2inv',
  'Ei',
  'LambertW',
  'besselj',
  'bessely',
  'besseli',
  'besselk',
  'airyai',
  'airybi',
  'airyaiprime',
  'airybiprime',
  'hankel1',
  'hankel2',
  'hn1',
  'hn2',
  'marcumq',
  'Ynm',
  'Znm',
  'mathieus',
  'mathieuc',
  'mathieusprime',
  'mathieucprime',
  'li',
  'Li',
  'Si',
  'Ci',
  'Shi',
  'Chi',
  'expint',
  'fresnels',
  'fresnelc',
  'sign',
  'floor',
  'ceiling',
  'atan2',
  'Min',
  'Max',
  'jacobi',
  'gegenbauer',
  'chebyshevt',
  'chebyshevu',
  'legendre',
  'assoc_legendre',
  'hermite',
  'hermite_prob',
  'laguerre',
  'assoc_laguerre',
  'polylog',
  'lerchphi',
  'dirichlet_eta',
  'riemann_xi',
  'stieltjes',
  'betainc',
  'betainc_regularized',
  'elliptic_k',
  'elliptic_e',
  'elliptic_f',
  'elliptic_pi',
  'appellf1',
];

/**
 * The argument at index i of a parsed call; a SyntaxError when the call has
 * too few (a call has at least one argument, so only for i > 0).
 */
function argAt(args: readonly Expr[], i: number, name: string): Expr {
  const a = args[i];
  if (a === undefined) throw new SyntaxError(`${name}() takes at least ${i + 1} arguments`);
  return a;
}

/** The exact value of a number argument of Rational() and Integer() (a Float by its binary value, as SymPy's Python floats). */
function exactNumber(e: Expr, name: string): Rational {
  if (e instanceof Rational) return e;
  if (e instanceof Float) {
    const { man, exp } = e.mpf;
    return exp >= 0 ? Rational.of(man << BigInt(exp)) : Rational.of(man, 1n << BigInt(-exp));
  }
  throw new TypeError(name === 'Integer' ? `Argument of Integer should be of numeric type, got ${e.toString()}.` : `invalid input: ${e.toString()}`);
}

/** SymPy Float(num, dps): the precision is a nonnegative integer. */
function floatArgs(args: readonly Expr[]): Expr {
  const [num, dps] = [argAt(args, 0, 'Float'), args[1]];
  if (dps === undefined) return float(num);
  if (!(dps instanceof Rational && dps.isInteger)) throw new TypeError(`Float(): the precision ${dps.toString()} is not an integer`);
  return float(num, Number(dps.p));
}

/** SymPy Integer(x): x truncated toward zero. */
function integerArg(args: readonly Expr[]): Expr {
  const r = exactNumber(argAt(args, 0, 'Integer'), 'Integer');
  return Rational.of(r.p / r.q);
}

/** SymPy Rational(p, q) of numbers (Floats are taken exactly). */
function rationalArgs(args: readonly Expr[]): Expr {
  const p = exactNumber(argAt(args, 0, 'Rational'), 'Rational');
  const q = args[1];
  return q === undefined ? p : div(p, exactNumber(q, 'Rational'));
}

/** Relationals by SymPy's function and class names. */
const RELATIONS: Record<string, RelOp> = {
  Eq: 'Eq',
  Equality: 'Eq',
  Ne: 'Ne',
  Unequality: 'Ne',
  Lt: 'Lt',
  StrictLessThan: 'Lt',
  Le: 'Le',
  LessThan: 'Le',
  Gt: 'Gt',
  StrictGreaterThan: 'Gt',
  Ge: 'Ge',
  GreaterThan: 'Ge',
};

const FUNCTIONS: Record<string, (args: Expr[]) => Expr> = {
  sqrt: (args) => sqrt(argAt(args, 0, 'sqrt')),
  exp: (args) => exp(argAt(args, 0, 'exp')),
  ...Object.fromEntries(
    (['sin', 'cos', 'tan', 'asin', 'acos', 'atan', 'sinh', 'cosh', 'tanh', 'log', 'abs', 're', 'im', 'arg', 'conjugate', 'cot', 'sec', 'csc', 'acot', 'asec', 'acsc', 'coth', 'sech', 'csch', 'asinh', 'acosh', 'atanh', 'acoth', 'asech', 'acsch', 'sinc'] as FnName[]).map(
      (n) => [n, (args: Expr[]) => fn(n, args)],
    ),
  ),
  ln: (args) => fn('log', [argAt(args, 0, 'ln')]),
  Abs: (args) => fn('abs', [argAt(args, 0, 'Abs')]),
  ...Object.fromEntries(SPECIAL_NAMES.map((n) => [n, (args: Expr[]) => fn(n, args)])),
  digamma: (args) => fn('polygamma', [0, argAt(args, 0, 'digamma')]),
  trigamma: (args) => fn('polygamma', [1, argAt(args, 0, 'trigamma')]),
  E1: (args) => fn('expint', [1, argAt(args, 0, 'E1')]),
  RisingFactorial: (args) => fn('rf', args),
  // SymPy 1.14 relationals require both sides (Eq(x) is a TypeError)
  ...Object.fromEntries(Object.entries(RELATIONS).map(([n, op]) => [n, (args: Expr[]) => rel(op, argAt(args, 0, n), argAt(args, 1, n))])),
  And: (args) => and(...args),
  Or: (args) => or(...args),
  Not: (args) => not(argAt(args, 0, 'Not')),
  Xor: (args) => xor(...args),
  Float: floatArgs,
  Integer: integerArg,
  Rational: rationalArgs,
  frac: (args) => fn('frac', [argAt(args, 0, 'frac')]),
  FallingFactorial: (args) => fn('ff', args),
};

/** A parsed call argument: an expression or a tuple (a, b, ...). */
type Arg = Expr | readonly Expr[];

const isTuple = (a: Arg): a is readonly Expr[] => Array.isArray(a);

/** The arguments of a call that does not take tuples. */
function plainArgs(args: readonly Arg[], name: string): Expr[] {
  return args.map((a) => {
    if (isTuple(a)) throw new SyntaxError(`${name}() does not take a tuple argument`);
    return a;
  });
}

/** The first argument (a call has at least one) and the others. */
function splitArgs(args: readonly Arg[], name: string): [Expr, Arg[]] {
  const e = at(args, 0);
  if (isTuple(e)) throw new SyntaxError(`${name}() does not take a tuple as its first argument`);
  return [e, args.slice(1)];
}

function asSym(e: Expr, name: string): Sym {
  if (!(e instanceof Sym)) throw new SyntaxError(`${name}(): ${e.toString()} is not a symbol`);
  return e;
}

/** The variable of a function of one free symbol (SymPy diff(x**2) is 2*x). */
function onlySymbol(e: Expr, name: string): Sym {
  const syms = [...e.freeSymbols()];
  const [v] = syms;
  if (v === undefined || syms.length > 1) throw new SyntaxError(`${name}() takes at least 2 arguments when the expression has not exactly one free symbol`);
  return v;
}

const isCount = (n: Expr | undefined): n is Rational => n instanceof Rational && n.isInteger && n.p >= 0n;

/**
 * SymPy variable_count: Derivative(f, x, y, 2, (z, 3)) has the variables x, y
 * (twice) and z (three times); a variable counted 0 times is dropped.
 */
function variableCounts(e: Expr, args: readonly Arg[], name: string): [Expr, number][] {
  if (!args.length) return [[onlySymbol(e, name), 1]];
  const vc: [Expr, number][] = [];
  for (const a of args) {
    const prev = vc.at(-1);
    if (isTuple(a)) {
      const [v, n] = a;
      if (v === undefined || a.length !== 2 || !isCount(n)) throw new SyntaxError(`${name}(): expected (variable, count)`);
      vc.push([v, Number(n.p)]);
    } else if (a instanceof Rational && a.isInteger && prev) {
      if (!isCount(a)) throw new SyntaxError(`${name}(): expected (variable, count)`);
      prev[1] += Number(a.p) - 1;
    } else vc.push([a, 1]);
  }
  return vc.filter(([, n]) => n > 0);
}

/** The limits (k, a, b) of Sum and Product. */
function concreteLimits(args: readonly Arg[], name: string): [Sym, Expr, Expr][] {
  if (!args.length) throw new SyntaxError(`${name}() needs limits (k, a, b)`);
  return args.map((a) => {
    const t = isTuple(a) ? a : [];
    const [k, lo, hi] = t;
    if (k === undefined || lo === undefined || hi === undefined || t.length !== 3) throw new SyntaxError(`${name}(): expected limits (k, a, b)`);
    return [asSym(k, name), lo, hi];
  });
}

/** Integral(f), Integral(f, x), Integral(f, (x,)), Integral(f, (x, a, b)), ...: the innermost first. */
function integral(args: readonly Arg[]): Expr {
  const [f, lims] = splitArgs(args, 'Integral');
  let e = f;
  for (const l of lims.length ? lims : [onlySymbol(f, 'Integral')]) {
    const [v, a, b] = isTuple(l) ? l : [l];
    const n = isTuple(l) ? l.length : 1;
    if (v === undefined || (n !== 1 && n !== 3)) throw new SyntaxError('Integral(): expected x, (x,) or (x, a, b)');
    const x = asSym(v, 'Integral');
    e = a !== undefined && b !== undefined ? new Integral([e, x, a, b]) : new Integral([e, x]);
  }
  return e;
}

/**
 * Constructors of higher layers that the parser uses when they are loaded
 * (registered by those modules). @internal
 */
export const parserHooks: {
  /** SymPy Order(e, *variables, point), the argument reduced to its leading term. */
  order?: (e: Expr, variables: readonly Sym[], point: Expr) => Expr;
  /** Classes of higher layers called by name, e.g. Quaternion(1, 2, 3, 4) (SymPy sympify of the class name). */
  readonly constructors: Map<string, (args: readonly Expr[]) => Expr>;
} = { constructors: new Map() };

/** O(e), O(e, x), O(e, x, y), O(e, (x, p)), O(e, (x, p), (y, p)). */
function order(args: readonly Arg[]): Expr {
  const [e, rest] = splitArgs(args, 'O');
  const vars: Sym[] = [];
  const points: Expr[] = [];
  for (const a of rest) {
    const [v, p] = isTuple(a) ? a : [a, S.Zero];
    if (v === undefined || p === undefined || (isTuple(a) && a.length !== 2)) throw new SyntaxError('O(): expected x or (x, point)');
    vars.push(asSym(v, 'O'));
    points.push(p);
  }
  const point = points[0] ?? S.Zero;
  // SymPy: NotImplementedError for points that differ
  if (points.some((p) => p.key !== point.key)) throw new NotImplementedError('Order at different points for the variables is not supported');
  if (parserHooks.order) return parserHooks.order(e, vars, point);
  // unreduced (SymPy reduces O(x + x**2) to O(x))
  const [v] = vars;
  if (vars.length > 1) return new Order([e, ...vars, point]);
  return v === undefined || (point instanceof Rational && point.isZero) ? new Order([e]) : new Order([e, v, point]);
}

/** Functions taking tuple arguments (the limits of SymPy's Integral, Sum, Derivative, ...). */
const TUPLE_FUNCTIONS: Record<string, (args: readonly Arg[]) => Expr> = {
  Derivative: (args) => {
    const [e, vs] = splitArgs(args, 'Derivative');
    const vc = variableCounts(e, vs, 'Derivative');
    return vc.length ? derivative(e, vc) : e;
  },
  diff: (args) => {
    const [e, vs] = splitArgs(args, 'diff');
    return variableCounts(e, vs, 'diff').reduce((acc, [v, n]) => impl.diff(acc, v, n), e);
  },
  Integral: integral,
  Sum: (args) => {
    const [f, lims] = splitArgs(args, 'Sum');
    return Sum(f, ...concreteLimits(lims, 'Sum'));
  },
  Product: (args) => {
    const [f, lims] = splitArgs(args, 'Product');
    return Product(f, ...concreteLimits(lims, 'Product'));
  },
  Subs: (args) => {
    const [e, [vs, ps, ...more]] = splitArgs(args, 'Subs');
    if (vs === undefined || ps === undefined || more.length) throw new SyntaxError('Subs() takes an expression, variables and points');
    return Subs(e, vs, ps);
  },
  O: order,
  Order: order,
  Piecewise: (args) =>
    piecewise(
      ...args.map((a): [Expr, Expr] => {
        const [e, cond, ...more] = isTuple(a) ? a : [];
        if (e === undefined || cond === undefined || more.length) throw new SyntaxError('Piecewise(): expected (expression, condition) pairs');
        return [e, cond];
      }),
    ),
};

const GREEK = new Set(['alpha', 'beta', 'gamma', 'delta', 'epsilon', 'zeta', 'eta', 'theta', 'iota', 'kappa', 'lamda', 'mu', 'nu', 'xi', 'omicron', 'pi', 'rho', 'sigma', 'tau', 'upsilon', 'phi', 'chi', 'psi', 'omega']);
/** SymPy _token_splittable: a name of letters only, not the name of a Greek letter. */
const splittable = (name: string): boolean => name.length > 1 && /^[A-Za-z]+$/.test(name) && !GREEK.has(name.toLowerCase());

const CONSTANTS: Record<string, Expr> = {
  pi: S.Pi,
  E: S.E,
  I: S.I,
  oo: S.Infinity,
  zoo: S.ComplexInfinity,
  nan: S.NaN,
  EulerGamma: S.EulerGamma,
  Catalan: S.Catalan,
  GoldenRatio: S.GoldenRatio,
  TribonacciConstant: S.TribonacciConstant,
  True: S.true,
  False: S.false,
};

const isSymbolList = (s: ParseOptions['symbols']): s is readonly Sym[] => Array.isArray(s);

function parseNumber(s: string): Expr {
  if (/^\d+$/.test(s)) return Rational.of(BigInt(s));
  // SymPy auto_number: Float(s), with at least 15 digits or as many as written
  return float(s);
}

class Parser {
  private i = 0;
  private readonly symbols = new Map<string, Expr>();

  constructor(private readonly tokens: Token[], private readonly opts: ParseOptions) {
    const s = opts.symbols;
    if (isSymbolList(s)) for (const sym of s) this.symbols.set(sym.name, sym);
    else if (s) for (const [k, v] of Object.entries(s)) this.symbols.set(k, v);
    for (const [k, v] of Object.entries(opts.locals ?? {})) {
      if (typeof v === 'function') this.localFns.set(k, v);
      else this.symbols.set(k, sympify(v));
    }
  }
  private readonly localFns = new Map<string, (...args: Expr[]) => ExprLike>();

  private peek(): Token {
    // the end token stops every rule, so the parser never reads past it
    return at(this.tokens, this.i);
  }
  private next(): Token {
    const t = this.peek();
    this.i++;
    return t;
  }
  private isOp(v: string): boolean {
    const t = this.peek();
    return t.t === 'op' && t.v === v;
  }
  private expect(v: string): void {
    const t = this.next();
    if (t.t !== 'op' || t.v !== v) throw new SyntaxError(`Expected '${v}' at ${t.pos}`);
  }

  private get implicit(): boolean {
    return this.opts.transformations === 'implicit' || this.opts.transformations === 'all';
  }
  private get raw(): boolean {
    return this.opts.evaluate === false;
  }
  // unevaluated arithmetic (SymPy evaluate=False): nodes built as written, sums and products flattened
  private add2(a: Expr, b: Expr): Expr {
    if (!this.raw) return add(a, b);
    return new Add([...(a instanceof Add ? a.args : [a]), ...(b instanceof Add ? b.args : [b])]);
  }
  private mul2(a: Expr, b: Expr): Expr {
    if (!this.raw) return mul(a, b);
    return new Mul([...(a instanceof Mul ? a.args : [a]), ...(b instanceof Mul ? b.args : [b])]);
  }
  private pow2(a: Expr, b: Expr): Expr {
    return this.raw ? new Pow(a, b) : pow(a, b);
  }

  parse(): Expr {
    const e = this.equation();
    const t = this.peek();
    if (t.t !== 'end') {
      const hint = t.t === 'name' || t.t === 'num' || (t.t === 'op' && t.v === '(') || t.t === 'value' ? ' (implicit multiplication is not supported; use *)' : '';
      throw new SyntaxError(`Unexpected token at ${t.pos}${hint}`);
    }
    return e;
  }

  /** a = b = ... as nested equations (convert_equals_signs), the lowest precedence. */
  private equation(): Expr {
    let e = this.boolOr();
    while (this.opts.convertEqualsSigns === true && this.isOp('=')) {
      this.next();
      const r = this.boolOr();
      // an equation of truth values (Eq(Eq(2, x), False)) stays as written
      const bool = (x: Expr): boolean => x instanceof Rel || x instanceof BoolAtom || x instanceof BoolOp;
      e = bool(e) || bool(r) ? new Rel('Eq', e, r) : rel('Eq', e, r);
    }
    return e;
  }

  // logical operators: | then ^ (Xor, without convert_xor) then & then ~
  private boolOr(): Expr {
    let e = this.boolXor();
    while (this.isOp('|')) {
      this.next();
      e = or(e, this.boolXor());
    }
    return e;
  }
  private boolXor(): Expr {
    let e = this.boolAnd();
    while (this.opts.convertXor === false && this.isOp('^')) {
      this.next();
      e = xor(e, this.boolAnd());
    }
    return e;
  }
  private boolAnd(): Expr {
    let e = this.boolNot();
    while (this.isOp('&')) {
      this.next();
      e = and(e, this.boolNot());
    }
    return e;
  }
  private boolNot(): Expr {
    if (this.isOp('~')) {
      this.next();
      return not(this.boolNot());
    }
    return this.relation();
  }

  /** a < b, a <= b, a > b, a >= b */
  private relation(): Expr {
    const lhs = this.sum();
    const ops: Record<string, RelOp> = { '<': 'Lt', '<=': 'Le', '>': 'Gt', '>=': 'Ge' };
    const t = this.peek();
    const op = t.t === 'op' ? ops[t.v] : undefined;
    if (op) {
      this.next();
      return rel(op, lhs, this.sum());
    }
    return lhs;
  }

  private sum(): Expr {
    let e = this.product();
    for (;;) {
      if (this.isOp('+')) {
        this.next();
        e = this.add2(e, this.product());
      } else if (this.isOp('-')) {
        this.next();
        const t = this.product();
        e = this.raw ? this.add2(e, this.mul2(Rational.of(-1n), t)) : sub(e, t);
      } else return e;
    }
  }

  /** Can the next token start a factor of an implicit product? */
  private startsFactor(): boolean {
    const t = this.peek();
    return t.t === 'num' || t.t === 'name' || t.t === 'value' || (t.t === 'op' && t.v === '(');
  }

  private product(): Expr {
    let e = this.unary();
    for (;;) {
      if (this.isOp('*')) {
        this.next();
        e = this.mul2(e, this.unary());
      } else if (this.isOp('/')) {
        this.next();
        const d = this.unary();
        e = this.raw ? this.mul2(e, new Pow(d, Rational.of(-1n))) : div(e, d);
      } else if (this.implicit && this.startsFactor()) {
        e = this.mul2(e, this.unary());
      } else return e;
    }
  }

  private unary(): Expr {
    if (this.isOp('-')) {
      this.next();
      const u = this.unary();
      if (this.raw) return u instanceof Rational || u instanceof Float ? neg(u) : new Mul([Rational.of(-1n), u]);
      return neg(u);
    }
    if (this.isOp('+')) {
      this.next();
      return this.unary();
    }
    return this.power();
  }

  private power(): Expr {
    const base = this.atom();
    if ((this.isOp('^') && this.opts.convertXor !== false) || this.isOp('**')) {
      this.next();
      return this.pow2(base, this.unary());
    }
    return base;
  }

  /** A call argument: an expression, or a tuple (a, b, ...) in parentheses. */
  private arg(): Arg {
    const start = this.i;
    if (this.isOp('(')) {
      this.next();
      const first = this.boolOr();
      if (this.isOp(',')) {
        const items = [first];
        while (this.isOp(',')) {
          this.next();
          // a trailing comma: (x,)
          if (this.isOp(')')) break;
          items.push(this.boolOr());
        }
        this.expect(')');
        return items;
      }
      // a parenthesized expression: parse the whole argument again
      this.i = start;
    }
    return this.sum();
  }

  /** The symbol (or constant) of a name. */
  private symbolOf(name: string): Expr {
    const known = this.symbols.get(name) ?? CONSTANTS[name];
    if (known) return known;
    const s = new Sym(name, this.opts.assumptions ?? {});
    this.symbols.set(name, s);
    return s;
  }

  private atom(): Expr {
    const t = this.next();
    switch (t.t) {
      case 'num':
        return parseNumber(t.v);
      case 'value':
        return t.v;
      case 'name': {
        // implicit application: sin x
        const knownFn = FUNCTIONS[t.v] ?? parserHooks.constructors.get(t.v);
        // function exponentiation: sin**2(x) and sin**2 x are sin(x)**2
        if (this.implicit && knownFn && this.isOp('**')) {
          this.next();
          const e = this.atom();
          const arg = this.isOp('(') ? this.atom() : this.power();
          return this.pow2(knownFn([arg]), e);
        }
        if (this.implicit && knownFn && !this.isOp('(') && this.startsFactor()) return knownFn([this.power()]);
        // split_symbols: an unknown name of several letters is a product of one-letter symbols
        if (this.opts.transformations === 'all' && !knownFn && !this.isOp('(') && splittable(t.v) && !this.symbols.has(t.v) && CONSTANTS[t.v] === undefined) {
          return t.v.split('').map((c) => this.symbolOf(c)).reduce((a, b) => this.mul2(a, b));
        }
        // with implicit multiplication a known symbol before '(' multiplies (x(y + 1))
        const tupleFn = this.localFns.has(t.v) ? undefined : TUPLE_FUNCTIONS[t.v];
        const asSymbol = this.implicit && !knownFn && !tupleFn && !this.localFns.has(t.v) && this.isOp('(');
        if (this.isOp('(') && !asSymbol) {
          // unknown names applied to arguments are undefined functions (like SymPy's parse_expr)
          const local = this.localFns.get(t.v);
          const f = local ? (args: Expr[]) => sympify(local(...args)) : (knownFn ?? ((args: Expr[]) => SymFunction(t.v)(...args)));
          this.next();
          const args: Arg[] = [this.arg()];
          while (this.isOp(',')) {
            this.next();
            args.push(this.arg());
          }
          this.expect(')');
          return tupleFn ? tupleFn(args) : f(plainArgs(args, t.v));
        }
        return this.symbolOf(t.v);
      }
      case 'op':
        if (t.v === '(') {
          const e = this.equation();
          this.expect(')');
          return e;
        }
        throw new SyntaxError(`Unexpected '${t.v}' at ${t.pos}`);
      case 'end':
        throw new SyntaxError('Unexpected end of input');
    }
  }
}

/**
 * Parse a string into an expression.
 *
 * @example
 * parse('cos(theta/2)^2 + sin(theta/2)^2', { assumptions: { real: true } })
 */
export function parse(src: string, opts: ParseOptions = {}): Expr {
  const tokens: Token[] = [];
  tokenize(src, 0, tokens);
  tokens.push({ t: 'end', pos: src.length });
  return new Parser(tokens, opts).parse();
}

/**
 * Tagged template for writing expressions inline; interpolated values may be
 * expressions or numbers.
 *
 * @example
 * const t = symbol('theta', { real: true });
 * ex`cos(${t}/2) - I*sin(${t}/2)`
 *
 * @experimental May change in a minor release.
 */
export function ex(strings: TemplateStringsArray, ...values: ExprLike[]): Expr {
  const tokens: Token[] = [];
  const symbols: Record<string, Expr> = {};
  let offset = 0;
  strings.forEach((s, i) => {
    tokenize(s, offset, tokens);
    offset += s.length;
    const value = values[i];
    if (value !== undefined) {
      const v = sympify(value);
      // bare names in the template refer to the interpolated symbols of the same name
      if (v instanceof Sym) symbols[v.name] = v;
      tokens.push({ t: 'value', v, pos: offset });
    }
  });
  tokens.push({ t: 'end', pos: offset });
  return new Parser(tokens, { symbols }).parse();
}
