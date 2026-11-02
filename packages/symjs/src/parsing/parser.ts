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
 */

import type { Assumptions, Expr, ExprLike, FnName, RelOp, SpecialFnName } from '../core/nodes';
import { Add, Mul, Pow, Rational, S, Sym, impl } from '../core/nodes';
import { and, not, or, xor } from '../core/boolalg';
import { add, div, exp, mul, neg, pow, sqrt, sub, sympify } from '../core/ops';
import { fn } from '../functions/elementary';
import { defined } from '../core/guard';
import { Eq, rel } from '../core/logic';
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
   * multiplication (2x, x y, x(y + 1)) and function application without
   * parentheses (sin x); 'all' is the same here.
   */
  transformations?: 'standard' | 'implicit' | 'all';
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
  const re = /\s*(?:(\d*\.\d*\[\d+\])|(\d+(?:\.\d*)?(?:[eE][+-]?\d+)?|\.\d+(?:[eE][+-]?\d+)?)|([A-Za-z_Ͱ-Ͽ][A-Za-z0-9_Ͱ-Ͽ']*)|(\*\*|<=|>=|[-+*/^(),&|~<>]))/y;
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
];

/** The argument at index i of a parsed call; a SyntaxError when the call has too few. */
function argAt(args: readonly Expr[], i: number, name: string): Expr {
  const a = args[i];
  if (a === undefined) throw new SyntaxError(`${name}() takes at least ${i + 1} argument${i === 0 ? '' : 's'}`);
  return a;
}

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
  Derivative: (args) => {
    const e = argAt(args, 0, 'Derivative');
    // Derivative(f, x, y, ...) with repeated variables, or Derivative(f, x, n) with an integer order
    const vc: [Expr, number][] = [];
    for (const a of args.slice(1)) {
      const prev = vc.at(-1);
      if (a instanceof Rational && a.isInteger && prev) prev[1] += Number(a.p) - 1;
      else vc.push([a, 1]);
    }
    return derivative(e, vc);
  },
  diff: (args) => {
    const n = args[2];
    return impl.diff(argAt(args, 0, 'diff'), argAt(args, 1, 'diff'), n instanceof Rational ? Number(n.p) : 1);
  },
  Eq: (args) => Eq(argAt(args, 0, 'Eq'), args[1] ?? 0),
  FallingFactorial: (args) => fn('ff', args),
};

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
};

const isSymbolList = (s: ParseOptions['symbols']): s is readonly Sym[] => Array.isArray(s);

function parseNumber(s: string): Expr {
  if (/^\d+$/.test(s)) return Rational.of(BigInt(s));
  return sympify(Number(s));
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
    const t = this.tokens[this.i];
    if (t === undefined) throw new SyntaxError('unexpected end of input');
    return t;
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
    const e = this.boolOr();
    const t = this.peek();
    if (t.t !== 'end') {
      const hint = t.t === 'name' || t.t === 'num' || (t.t === 'op' && t.v === '(') || t.t === 'value' ? ' (implicit multiplication is not supported; use *)' : '';
      throw new SyntaxError(`Unexpected token at ${t.pos}${hint}`);
    }
    return e;
  }

  // logical operators (lowest precedence): | then ^ (Xor, without convert_xor) then & then ~
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
      if (this.raw) return u instanceof Rational ? Rational.of(-u.p, u.q) : new Mul([Rational.of(-1n), u]);
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

  private atom(): Expr {
    const t = this.next();
    switch (t.t) {
      case 'num':
        return parseNumber(t.v);
      case 'value':
        return t.v;
      case 'name': {
        // implicit application: sin x
        const knownFn = FUNCTIONS[t.v];
        if (this.implicit && knownFn && !this.isOp('(') && this.startsFactor()) return knownFn([this.power()]);
        // with implicit multiplication a known symbol before '(' multiplies (x(y + 1))
        const asSymbol = this.implicit && !FUNCTIONS[t.v] && !this.localFns.has(t.v) && this.isOp('(');
        if (this.isOp('(') && !asSymbol) {
          // unknown names applied to arguments are undefined functions (like SymPy's parse_expr)
          const local = this.localFns.get(t.v);
          const f = local ? (args: Expr[]) => sympify(local(...args)) : (FUNCTIONS[t.v] ?? ((args: Expr[]) => SymFunction(t.v)(...args)));
          this.next();
          const args: Expr[] = [this.sum()];
          while (this.isOp(',')) {
            this.next();
            args.push(this.sum());
          }
          this.expect(')');
          return f(args);
        }
        const known = this.symbols.get(t.v) ?? CONSTANTS[t.v];
        if (known) return known;
        const s = new Sym(t.v, this.opts.assumptions ?? {});
        this.symbols.set(t.v, s);
        return s;
      }
      case 'op':
        if (t.v === '(') {
          const e = this.boolOr();
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
