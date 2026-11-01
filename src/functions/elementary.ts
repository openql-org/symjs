// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Elementary functions with automatic evaluation of special values.
 */

import { isNegative, isNonNegative, isPositive, isReal } from '../core/assumptions';
import {
  Add,
  Constant,
  Expr,
  ExprLike,
  Fn,
  FnName,
  Mul,
  Pow,
  Rational,
  S,
  impl,
  isNum,
} from '../core/nodes';
import { numAbs, numNeg, ratMod } from '../core/num';
import { add, couldExtractMinusSign, mul, neg, pow, splitCoeff, sqrt, sympify } from '../core/ops';

type Evaluator = (x: Expr) => Expr | undefined;

const isI = (e: Expr) => e instanceof Constant && e.name === 'I';
const isPi = (e: Expr) => e instanceof Constant && e.name === 'pi';

/** If x = c*pi with rational c, return c. */
function piCoeff(x: Expr): Rational | undefined {
  if (isPi(x)) return S.One;
  if (x instanceof Rational && x.isZero) return S.Zero;
  const [c, rest] = splitCoeff(x);
  if (c instanceof Rational && isPi(rest)) return c;
  return undefined;
}

/** Split x = a + c*pi where c is rational (c may be zero). */
function splitPiTerm(x: Expr): [Expr, Rational] {
  const c = piCoeff(x);
  if (c) return [S.Zero, c];
  if (x instanceof Add) {
    for (let i = 0; i < x.args.length; i++) {
      const ci = piCoeff(x.args[i]!);
      if (ci) return [add(...x.args.filter((_, j) => j !== i)), ci];
    }
  }
  return [x, S.Zero];
}

const r = (p: number, q = 1) => Rational.of(p, q);

/** sin(k*pi/12 ... ) table for multiples of pi in [0, 2): key = c.key */
function sinOfPiMultiple(c: Rational): Expr | undefined {
  // reduce to [0, 2)
  const m = ratMod(c, S.Two);
  // use symmetry: sin(pi + t) = -sin(t)
  if (m.p * 1n >= m.q) {
    const v = sinOfPiMultiple(Rational.of(m.p - m.q, m.q));
    return v === undefined ? undefined : neg(v);
  }
  // m in [0, 1): sin(pi - t) = sin(t)
  const t = m.p * 2n > m.q ? Rational.of(m.q - m.p, m.q) : m; // t in [0, 1/2]
  const table: Record<string, () => Expr> = {
    '0': () => S.Zero,
    '1/2': () => S.One,
    '1/6': () => S.Half,
    '1/4': () => mul(S.Half, sqrt(2)),
    '1/3': () => mul(S.Half, sqrt(3)),
    '1/12': () => mul(r(1, 4), add(sqrt(6), neg(sqrt(2)))),
    '5/12': () => mul(r(1, 4), add(sqrt(6), sqrt(2))),
  };
  return table[t.key]?.();
}

function cosOfPiMultiple(c: Rational): Expr | undefined {
  // cos(x) = sin(x + pi/2)
  return sinOfPiMultiple(Rational.of(c.p * 2n + c.q, c.q * 2n));
}

// ---------------------------------------------------------------------------
// Evaluators
// ---------------------------------------------------------------------------

const evalSin: Evaluator = (x) => {
  if (x instanceof Rational && x.isZero) return S.Zero;
  const [rest, c] = splitPiTerm(x);
  if (rest instanceof Rational && rest.isZero) return sinOfPiMultiple(c);
  if (!c.isZero) {
    // reduce shift modulo 2*pi and use quarter-period symmetries
    const m = ratMod(c, S.Two);
    const twice = Rational.of(m.p * 2n, m.q);
    if (twice.isInteger) {
      switch (twice.p) {
        case 0n:
          return sin(rest);
        case 1n:
          return cos(rest);
        case 2n:
          return neg(sin(rest));
        case 3n:
          return neg(cos(rest));
      }
    }
    if (!m.equals(c)) return sin(add(rest, mul(m, S.Pi)));
  }
  if (couldExtractMinusSign(x)) return neg(sin(neg(x)));
  if (x instanceof Fn && x.name === 'asin') return x.args[0];
  return undefined;
};

const evalCos: Evaluator = (x) => {
  if (x instanceof Rational && x.isZero) return S.One;
  const [rest, c] = splitPiTerm(x);
  if (rest instanceof Rational && rest.isZero) return cosOfPiMultiple(c);
  if (!c.isZero) {
    const m = ratMod(c, S.Two);
    const twice = Rational.of(m.p * 2n, m.q);
    if (twice.isInteger) {
      switch (twice.p) {
        case 0n:
          return cos(rest);
        case 1n:
          return neg(sin(rest));
        case 2n:
          return neg(cos(rest));
        case 3n:
          return sin(rest);
      }
    }
    if (!m.equals(c)) return cos(add(rest, mul(m, S.Pi)));
  }
  if (couldExtractMinusSign(x)) return cos(neg(x));
  if (x instanceof Fn && x.name === 'acos') return x.args[0];
  return undefined;
};

const evalTan: Evaluator = (x) => {
  if (x instanceof Rational && x.isZero) return S.Zero;
  const [rest, c] = splitPiTerm(x);
  if (rest instanceof Rational && rest.isZero) {
    const s = sinOfPiMultiple(c);
    const co = cosOfPiMultiple(c);
    if (s && co) {
      if (co instanceof Rational && co.isZero) throw new RangeError('tan: pole at odd multiple of pi/2');
      return mul(s, pow(co, -1));
    }
  }
  if (!c.isZero) {
    const m = ratMod(c, S.One);
    if (m.isZero) return tan(rest);
    if (!m.equals(c)) return tan(add(rest, mul(m, S.Pi)));
  }
  if (couldExtractMinusSign(x)) return neg(tan(neg(x)));
  if (x instanceof Fn && x.name === 'atan') return x.args[0];
  return undefined;
};

const evalAsin: Evaluator = (x) => {
  const table: Record<string, Expr> = {
    '0': S.Zero,
    '1': mul(S.Half, S.Pi),
    '1/2': mul(r(1, 6), S.Pi),
  };
  if (x.key in table) return table[x.key];
  if (x.equals(mul(S.Half, sqrt(2)))) return mul(r(1, 4), S.Pi);
  if (x.equals(mul(S.Half, sqrt(3)))) return mul(r(1, 3), S.Pi);
  if (couldExtractMinusSign(x)) return neg(asin(neg(x)));
  return undefined;
};

const evalAcos: Evaluator = (x) => {
  const v = evalAsin(x);
  if (v === undefined || v instanceof Fn) return undefined;
  return add(mul(S.Half, S.Pi), neg(v));
};

const evalAtan: Evaluator = (x) => {
  if (x instanceof Rational && x.isZero) return S.Zero;
  if (x instanceof Rational && x.isOne) return mul(r(1, 4), S.Pi);
  if (x.equals(sqrt(3))) return mul(r(1, 3), S.Pi);
  if (x.equals(mul(r(1, 3), sqrt(3)))) return mul(r(1, 6), S.Pi);
  if (couldExtractMinusSign(x)) return neg(atan(neg(x)));
  return undefined;
};

const evalSinh: Evaluator = (x) => {
  if (x instanceof Rational && x.isZero) return S.Zero;
  if (couldExtractMinusSign(x)) return neg(sinh(neg(x)));
  return undefined;
};
const evalCosh: Evaluator = (x) => {
  if (x instanceof Rational && x.isZero) return S.One;
  if (couldExtractMinusSign(x)) return cosh(neg(x));
  return undefined;
};
const evalTanh: Evaluator = (x) => {
  if (x instanceof Rational && x.isZero) return S.Zero;
  if (couldExtractMinusSign(x)) return neg(tanh(neg(x)));
  return undefined;
};

const evalLog: Evaluator = (x) => {
  if (x instanceof Rational) {
    if (x.isOne) return S.Zero;
    if (x.isZero) throw new RangeError('log(0) is undefined');
    if (x.isNegative) return add(log(numNeg(x)), mul(S.I, S.Pi));
  }
  if (x instanceof Constant && x.name === 'E') return S.One;
  if (isI(x)) return mul(S.Half, S.I, S.Pi);
  if (x instanceof Pow && x.base instanceof Constant && x.base.name === 'E' && isReal(x.exp)) return x.exp;
  return undefined;
};

const evalAbs: Evaluator = (x) => {
  if (isNum(x)) return numAbs(x);
  if (isI(x)) return S.One;
  if (isNonNegative(x)) return x;
  if (isNegative(x)) return neg(x);
  if (x instanceof Mul) return mul(...x.args.map(abs));
  if (x instanceof Pow) {
    const [b, e] = x.args;
    if (b instanceof Constant && b.name === 'E') return pow(b, re(e));
    if (isReal(e)) return pow(abs(b), e);
  }
  if (x instanceof Fn && (x.name === 'abs' || x.name === 'conjugate')) return abs(x.args[0]!);
  // a + b*I with real a, b
  const [a, b] = reIm(x);
  if (!(b instanceof Rational && b.isZero) && !hasReIm(a) && !hasReIm(b)) {
    return sqrt(add(pow(a, 2), pow(b, 2)));
  }
  return undefined;
};

const hasReIm = (e: Expr): boolean =>
  (e instanceof Fn && (e.name === 're' || e.name === 'im')) || e.args.some(hasReIm);

/** Decompose into real and imaginary parts when possible (fallback: re()/im() nodes). */
function reIm(x: Expr): [Expr, Expr] {
  return [re(x), im(x)];
}

const evalRe: Evaluator = (x) => {
  if (isReal(x)) return x;
  if (isI(x)) return S.Zero;
  if (x instanceof Add) return add(...x.args.map(re));
  if (x instanceof Mul) {
    const real = x.args.filter((a) => isReal(a) === true);
    const others = x.args.filter((a) => isReal(a) !== true);
    if (real.length > 0) {
      const o = mul(...others);
      if (isI(o)) return S.Zero;
      if (o instanceof Mul && o.args.some(isI) && o.args.filter(isI).length === 1) {
        const w = mul(...o.args.filter((a) => !isI(a)));
        return mul(...real, neg(im(w)));
      }
      return mul(...real, re(o));
    }
    if (x.args.some(isI)) {
      const w = mul(...x.args.filter((a) => !isI(a)));
      return neg(im(w));
    }
  }
  if (x instanceof Fn && x.name === 're') return x;
  if (x instanceof Fn && x.name === 'conjugate') return re(x.args[0]!);
  return undefined;
};

const evalIm: Evaluator = (x) => {
  if (isReal(x)) return S.Zero;
  if (isI(x)) return S.One;
  if (x instanceof Add) return add(...x.args.map(im));
  if (x instanceof Mul) {
    const real = x.args.filter((a) => isReal(a) === true);
    const others = x.args.filter((a) => isReal(a) !== true);
    if (real.length > 0) {
      const o = mul(...others);
      if (isI(o)) return mul(...real);
      if (o instanceof Mul && o.args.filter(isI).length === 1) {
        const w = mul(...o.args.filter((a) => !isI(a)));
        return mul(...real, re(w));
      }
      return mul(...real, im(o));
    }
    if (x.args.some(isI)) {
      const w = mul(...x.args.filter((a) => !isI(a)));
      return re(w);
    }
  }
  if (x instanceof Fn && x.name === 'conjugate') return neg(im(x.args[0]!));
  return undefined;
};

const evalArg: Evaluator = (x) => {
  if (isPositive(x)) return S.Zero;
  if (isNegative(x)) return S.Pi;
  if (isI(x)) return mul(S.Half, S.Pi);
  if (x instanceof Pow && x.base instanceof Constant && x.base.name === 'E') {
    const t = im(x.exp);
    // only safe when the angle lies in (-pi, pi]; leave unevaluated otherwise
    if (t instanceof Rational && Math.abs(t.value) < Math.PI) return t;
  }
  return undefined;
};

/** Complex conjugate, pushed through the expression tree. */
export function conjugate(xx: ExprLike): Expr {
  const x = sympify(xx);
  if (isReal(x)) return x;
  if (isI(x)) return neg(S.I);
  if (x instanceof Add) return add(...x.args.map(conjugate));
  if (x instanceof Mul) return mul(...x.args.map(conjugate));
  if (x instanceof Pow) {
    const [b, e] = x.args;
    if (isReal(e) && (isNonNegative(b) || (e instanceof Rational && e.isInteger))) return pow(conjugate(b), e);
    if (b instanceof Constant && b.name === 'E') return pow(b, conjugate(e));
  }
  if (x instanceof Fn) {
    switch (x.name) {
      case 'conjugate':
        return x.args[0]!;
      case 'sin':
      case 'cos':
      case 'tan':
      case 'sinh':
      case 'cosh':
      case 'tanh':
        return fn(x.name, [conjugate(x.args[0]!)]);
      case 're':
      case 'im':
      case 'abs':
      case 'arg':
        return x;
      default:
        break;
    }
  }
  return new Fn('conjugate', [x]);
}

const evaluators: Record<FnName, Evaluator> = {
  sin: evalSin,
  cos: evalCos,
  tan: evalTan,
  asin: evalAsin,
  acos: evalAcos,
  atan: evalAtan,
  sinh: evalSinh,
  cosh: evalCosh,
  tanh: evalTanh,
  log: evalLog,
  abs: evalAbs,
  re: evalRe,
  im: evalIm,
  arg: evalArg,
  conjugate: (x) => {
    const c = conjugate(x);
    return c instanceof Fn && c.name === 'conjugate' && c.args[0] === x ? undefined : c;
  },
};

/** Apply a named function with automatic evaluation. */
export function fn(name: FnName, args: readonly ExprLike[]): Expr {
  const xs = args.map(sympify);
  const ev = evaluators[name];
  const v = ev(xs[0]!);
  if (v !== undefined) return v;
  return new Fn(name, xs);
}

export const sin = (x: ExprLike): Expr => fn('sin', [x]);
export const cos = (x: ExprLike): Expr => fn('cos', [x]);
export const tan = (x: ExprLike): Expr => fn('tan', [x]);
export const asin = (x: ExprLike): Expr => fn('asin', [x]);
export const acos = (x: ExprLike): Expr => fn('acos', [x]);
export const atan = (x: ExprLike): Expr => fn('atan', [x]);
export const sinh = (x: ExprLike): Expr => fn('sinh', [x]);
export const cosh = (x: ExprLike): Expr => fn('cosh', [x]);
export const tanh = (x: ExprLike): Expr => fn('tanh', [x]);
export const log = (x: ExprLike): Expr => fn('log', [x]);
export const abs = (x: ExprLike): Expr => fn('abs', [x]);
export const re = (x: ExprLike): Expr => fn('re', [x]);
export const im = (x: ExprLike): Expr => fn('im', [x]);
export const arg = (x: ExprLike): Expr => fn('arg', [x]);

/** Hermitian adjoint of a scalar is its conjugate. */
export const dagger = conjugate;

impl.conjugate = conjugate;
impl.abs = abs;
