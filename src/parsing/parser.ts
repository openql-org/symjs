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

import { Assumptions, Expr, ExprLike, FnName, Rational, S, Sym } from '../core/nodes';
import { add, div, exp, mul, neg, pow, sqrt, sub, sympify } from '../core/ops';
import { fn } from '../functions/elementary';

export interface ParseOptions {
  /** Predefined symbols (by name). */
  symbols?: Readonly<Record<string, Expr>> | readonly Sym[];
  /** Assumptions for symbols created implicitly by the parser. */
  assumptions?: Assumptions;
}

type Token =
  | { t: 'num'; v: string; pos: number }
  | { t: 'name'; v: string; pos: number }
  | { t: 'op'; v: string; pos: number }
  | { t: 'value'; v: Expr; pos: number }
  | { t: 'end'; pos: number };

function tokenize(src: string, offset: number, out: Token[]): void {
  const re = /\s*(?:(\d+(?:\.\d*)?(?:[eE][+-]?\d+)?|\.\d+(?:[eE][+-]?\d+)?)|([A-Za-z_Ͱ-Ͽ][A-Za-z0-9_Ͱ-Ͽ']*)|(\*\*|[-+*/^(),]))/y;
  let i = 0;
  while (i < src.length) {
    if (/^\s*$/.test(src.slice(i))) return;
    re.lastIndex = i;
    const m = re.exec(src);
    if (!m) throw new SyntaxError(`Unexpected character '${src[i]?.trim() || src.slice(i).trim()[0]}' at ${offset + i}`);
    const pos = offset + i + (m[0].length - m[0].trimStart().length);
    if (m[1] !== undefined) out.push({ t: 'num', v: m[1], pos });
    else if (m[2] !== undefined) out.push({ t: 'name', v: m[2], pos });
    else out.push({ t: 'op', v: m[3]!, pos });
    i = re.lastIndex;
  }
}

const FUNCTIONS: Record<string, (args: Expr[]) => Expr> = {
  sqrt: ([x]) => sqrt(x!),
  exp: ([x]) => exp(x!),
  ...Object.fromEntries(
    (['sin', 'cos', 'tan', 'asin', 'acos', 'atan', 'sinh', 'cosh', 'tanh', 'log', 'abs', 're', 'im', 'arg', 'conjugate'] as FnName[]).map(
      (n) => [n, (args: Expr[]) => fn(n, args)],
    ),
  ),
  ln: ([x]) => fn('log', [x!]),
  Abs: ([x]) => fn('abs', [x!]),
};

const CONSTANTS: Record<string, Expr> = { pi: S.Pi, E: S.E, I: S.I };

function parseNumber(s: string): Expr {
  if (/^\d+$/.test(s)) return Rational.of(BigInt(s));
  return sympify(Number(s));
}

class Parser {
  private i = 0;
  private readonly symbols = new Map<string, Expr>();

  constructor(private readonly tokens: Token[], private readonly opts: ParseOptions) {
    const s = opts.symbols;
    if (Array.isArray(s)) for (const sym of s as readonly Sym[]) this.symbols.set(sym.name, sym);
    else if (s) for (const [k, v] of Object.entries(s as Record<string, Expr>)) this.symbols.set(k, v);
  }

  private peek(): Token {
    return this.tokens[this.i]!;
  }
  private next(): Token {
    return this.tokens[this.i++]!;
  }
  private isOp(v: string): boolean {
    const t = this.peek();
    return t.t === 'op' && t.v === v;
  }
  private expect(v: string): void {
    const t = this.next();
    if (t.t !== 'op' || t.v !== v) throw new SyntaxError(`Expected '${v}' at ${t.pos}`);
  }

  parse(): Expr {
    const e = this.sum();
    const t = this.peek();
    if (t.t !== 'end') {
      const hint = t.t === 'name' || t.t === 'num' || (t.t === 'op' && t.v === '(') || t.t === 'value' ? ' (implicit multiplication is not supported; use *)' : '';
      throw new SyntaxError(`Unexpected token at ${t.pos}${hint}`);
    }
    return e;
  }

  private sum(): Expr {
    let e = this.product();
    for (;;) {
      if (this.isOp('+')) {
        this.next();
        e = add(e, this.product());
      } else if (this.isOp('-')) {
        this.next();
        e = sub(e, this.product());
      } else return e;
    }
  }

  private product(): Expr {
    let e = this.unary();
    for (;;) {
      if (this.isOp('*')) {
        this.next();
        e = mul(e, this.unary());
      } else if (this.isOp('/')) {
        this.next();
        e = div(e, this.unary());
      } else return e;
    }
  }

  private unary(): Expr {
    if (this.isOp('-')) {
      this.next();
      return neg(this.unary());
    }
    if (this.isOp('+')) {
      this.next();
      return this.unary();
    }
    return this.power();
  }

  private power(): Expr {
    const base = this.atom();
    if (this.isOp('^') || this.isOp('**')) {
      this.next();
      return pow(base, this.unary());
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
        if (this.isOp('(')) {
          const f = FUNCTIONS[t.v];
          if (!f) throw new SyntaxError(`Unknown function '${t.v}' at ${t.pos}`);
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
          const e = this.sum();
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
 */
export function ex(strings: TemplateStringsArray, ...values: ExprLike[]): Expr {
  const tokens: Token[] = [];
  const symbols: Record<string, Expr> = {};
  let offset = 0;
  strings.forEach((s, i) => {
    tokenize(s, offset, tokens);
    offset += s.length;
    if (i < values.length) {
      const v = sympify(values[i]!);
      // bare names in the template refer to the interpolated symbols of the same name
      if (v instanceof Sym) symbols[v.name] = v;
      tokens.push({ t: 'value', v, pos: offset });
    }
  });
  tokens.push({ t: 'end', pos: offset });
  return new Parser(tokens, { symbols }).parse();
}
