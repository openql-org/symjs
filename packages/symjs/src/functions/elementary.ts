// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Elementary functions with automatic evaluation of special values.
 */

import { precToDps } from '../numeric/mpf';
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
  Float,
  Rational,
  S,
  Special,
  impl,
  isNum,
  ExtensionExpr,
} from '../core/nodes';
import { numAbs, numNeg, ratMod } from '../core/num';
import { add, couldExtractMinusSign, mul, neg, pow, splitCoeff, sqrt, sympify } from '../core/ops';

export type Evaluator = (x: Expr, ...rest: Expr[]) => Expr | undefined;

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
export function splitPiTerm(x: Expr): [Expr, Rational] {
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
    '1/10': () => add(r(-1, 4), mul(r(1, 4), sqrt(5))),
    '3/10': () => add(r(1, 4), mul(r(1, 4), sqrt(5))),
    '1/5': () => sqrt(add(r(5, 8), mul(r(-1, 8), sqrt(5)))),
    '2/5': () => sqrt(add(r(5, 8), mul(r(1, 8), sqrt(5)))),
    '1/8': () => sqrt(add(r(1, 2), mul(r(-1, 4), sqrt(2)))),
    '3/8': () => sqrt(add(r(1, 2), mul(r(1, 4), sqrt(2)))),
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
      if (co instanceof Rational && co.isZero) return S.ComplexInfinity;
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
  if (x instanceof Special && x.name === 'oo') return mul(-1, S.I, S.Infinity);
  if (x instanceof Special && x.name === '-oo') return mul(S.I, S.Infinity);
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
  if (x instanceof Special && x.name === 'oo') return mul(S.I, S.Infinity);
  if (x instanceof Special && x.name === '-oo') return mul(-1, S.I, S.Infinity);
  const v = evalAsin(x);
  // only exact values; acos(-u) stays (SymPy does not rewrite it through asin)
  const hasAsin = (t: Expr): boolean => (t instanceof Fn && t.name === 'asin') || t.args.some(hasAsin);
  if (v === undefined || hasAsin(v)) return undefined;
  return add(mul(S.Half, S.Pi), neg(v));
};

const evalAtan: Evaluator = (x) => {
  if (x instanceof Special && x.name === 'oo') return mul(S.Half, S.Pi);
  if (x instanceof Special && x.name === '-oo') return mul(S.NegHalf, S.Pi);
  if (x instanceof Rational && x.isZero) return S.Zero;
  if (x instanceof Rational && x.isOne) return mul(r(1, 4), S.Pi);
  if (x.equals(sqrt(3))) return mul(r(1, 3), S.Pi);
  if (x.equals(mul(r(1, 3), sqrt(3)))) return mul(r(1, 6), S.Pi);
  if (couldExtractMinusSign(x)) return neg(atan(neg(x)));
  return undefined;
};

const evalSinh: Evaluator = (x) => {
  if (x instanceof Special && (x.name === 'oo' || x.name === '-oo')) return x;
  if (x instanceof Rational && x.isZero) return S.Zero;
  if (couldExtractMinusSign(x)) return neg(sinh(neg(x)));
  return undefined;
};
const evalCosh: Evaluator = (x) => {
  if (x instanceof Special && (x.name === 'oo' || x.name === '-oo')) return S.Infinity;
  if (x instanceof Rational && x.isZero) return S.One;
  if (couldExtractMinusSign(x)) return cosh(neg(x));
  return undefined;
};
const evalTanh: Evaluator = (x) => {
  if (x instanceof Special && x.name === 'oo') return S.One;
  if (x instanceof Special && x.name === '-oo') return S.NegOne;
  if (x instanceof Rational && x.isZero) return S.Zero;
  if (couldExtractMinusSign(x)) return neg(tanh(neg(x)));
  return undefined;
};

const evalLog: Evaluator = (x) => {
  if (x instanceof Special) return x.name === 'nan' ? S.NaN : S.Infinity;
  if (x instanceof Rational) {
    if (x.isOne) return S.Zero;
    if (x.isZero) return S.ComplexInfinity;
    if (x.isNegative) return add(log(numNeg(x)), mul(S.I, S.Pi));
    if (x.p === 1n && x.q !== 1n) return neg(log(Rational.of(x.q, 1n)));
  }
  if (x instanceof Constant && x.name === 'E') return S.One;
  if (isI(x)) return mul(S.Half, S.I, S.Pi);
  if (x instanceof Pow && x.base instanceof Constant && x.base.name === 'E' && isReal(x.exp)) return x.exp;
  if (x instanceof Add && x.freeSymbols().size === 0 && !isReal(x) && !x.args.some((a) => a instanceof Float)) {
    const t = arg(x);
    if (!(t instanceof Fn)) return add(log(abs(x)), mul(S.I, t));
  }
  return undefined;
};

const evalAbs: Evaluator = (x) => {
  if (isNum(x)) return numAbs(x);
  if (x instanceof Special) return x.name === 'nan' ? S.NaN : S.Infinity;
  if (isI(x)) return S.One;
  if (isNonNegative(x)) return x;
  if (isNegative(x)) return neg(x);
  if (x instanceof Mul) {
    // SymPy: factors whose Abs evaluates come out, the rest stay inside a single Abs
    const known: Expr[] = [];
    const unknown: Expr[] = [];
    for (const t of x.args) {
      const v = evalAbs(t);
      if (v === undefined) unknown.push(t);
      else known.push(v);
    }
    if (known.length === 0) return undefined;
    return mul(...known, ...(unknown.length ? [new Fn('abs', [mul(...unknown)])] : []));
  }
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

/** (-1)**r for rational r: [cos(pi r), sin(pi r)] when both evaluate. */
function unitRoot(x: Expr): [Expr, Expr] | undefined {
  if (!(x instanceof Pow && x.exp instanceof Rational)) return undefined;
  const negOne = x.base instanceof Rational && x.base.p === -1n && x.base.q === 1n;
  if (!negOne && !isI(x.base)) return undefined;
  // I**r = (-1)**(r/2)
  const ang = mul(negOne ? x.exp : mul(x.exp, S.Half), S.Pi);
  const c = cos(ang);
  const s = sin(ang);
  if (c instanceof Fn || s instanceof Fn) return undefined;
  return [c, s];
}

const evalRe: Evaluator = (x) => {
  if (isReal(x)) return x;
  if (isI(x)) return S.Zero;
  const ur = unitRoot(x);
  if (ur) return ur[0];
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
  const ur = unitRoot(x);
  if (ur) return ur[1];
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
  // SymPy: arg(arg(arg(...))) is nan, and so is arg(arg(r)) for real r
  {
    let a = x;
    let depth = 0;
    while (depth < 3 && a instanceof Fn && a.name === 'arg') {
      a = a.args[0]!;
      depth++;
    }
    if (depth === 3 || (depth === 2 && isReal(a) === true)) return S.NaN;
  }
  if (isPositive(x)) return S.Zero;
  // a + b*I with real numeric a, b
  if (x.freeSymbols().size === 0 && !isReal(x)) {
    const a = re(x);
    const b = im(x);
    if (isNum(a) && isNum(b) && (a instanceof Float || b instanceof Float)) {
      return new Float(Math.atan2(b instanceof Rational ? b.value : (b as Float).value, a instanceof Rational ? a.value : (a as Float).value));
    }
    if (!(a instanceof Fn) && !(b instanceof Fn) && a.freeSymbols().size === 0) {
      const sa = isPositive(a) ? 1 : isNegative(a) ? -1 : 0;
      if (a instanceof Rational && a.isZero) {
        if (isPositive(b)) return mul(S.Half, S.Pi);
        if (isNegative(b)) return mul(S.NegHalf, S.Pi);
      }
      const t = atan(mul(b, pow(a, -1)));
      if (sa === 1) return t;
      if (sa === -1) return isNegative(b) ? add(t, neg(S.Pi)) : add(t, S.Pi);
    }
  }
  if (isNegative(x)) return S.Pi;
  if (isI(x)) return mul(S.Half, S.Pi);
  if (x instanceof Pow && x.base instanceof Constant && x.base.name === 'E') {
    const t = im(x.exp);
    // only safe when the angle lies in (-pi, pi]; leave unevaluated otherwise
    if (t instanceof Rational && Math.abs(t.value) < Math.PI) return t;
  }
  return undefined;
};

/** Functions with f(conjugate(z)) = conjugate(f(z)) (real on the real axis); filled by special.ts. */
export const conjugateCommutes = new Set<string>();

/** Complex conjugate, pushed through the expression tree. */
export function conjugate(xx: ExprLike): Expr {
  const x = sympify(xx);
  if (x instanceof ExtensionExpr) {
    const r = x.conjugateSelf();
    if (r !== undefined) return r;
  }
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
        if (conjugateCommutes.has(x.name)) return fn(x.name, x.args.map(conjugate));
        break;
    }
  }
  return new Fn('conjugate', [x]);
}

/**
 * Hermitian adjoint (SymPy adjoint): conjugate of commutative factors,
 * reversed product order for non-commutative ones.
 */
export function adjoint(xx: ExprLike): Expr {
  const x = sympify(xx);
  if (x instanceof ExtensionExpr) {
    const r = x.adjointSelf();
    if (r !== undefined) return r;
  }
  if (x.isCommutative) return conjugate(x);
  if (x instanceof Add) return add(...x.args.map(adjoint));
  if (x instanceof Mul) return mul(...[...x.args].reverse().map(adjoint));
  if (x instanceof Pow && x.exp.isCommutative && isReal(x.exp)) return pow(adjoint(x.base), x.exp);
  if (x instanceof Fn) {
    if (x.name === 'adjoint') return x.args[0]!;
    if (x.name === 'conjugate') return transpose(x.args[0]!);
    if (x.name === 'transpose') return conjugate(x.args[0]!);
  }
  if (x instanceof Pow && x.base instanceof Constant && x.base.name === 'E') return pow(x.base, adjoint(x.exp));
  return new Fn('adjoint', [x]);
}

/** Transpose (SymPy transpose): commutative scalars are unchanged, products reverse. */
export function transpose(xx: ExprLike): Expr {
  const x = sympify(xx);
  if (x instanceof ExtensionExpr) {
    const r = x.transposeSelf();
    if (r !== undefined) return r;
  }
  if (x.isCommutative) return x;
  if (x instanceof Add) return add(...x.args.map(transpose));
  if (x instanceof Mul) return mul(...[...x.args].reverse().map(transpose));
  if (x instanceof Pow && x.exp.isCommutative && isReal(x.exp)) return pow(transpose(x.base), x.exp);
  if (x instanceof Fn) {
    if (x.name === 'transpose') return x.args[0]!;
    if (x.name === 'conjugate') return adjoint(x.args[0]!);
    if (x.name === 'adjoint') return conjugate(x.args[0]!);
  }
  if (x instanceof Pow && x.base instanceof Constant && x.base.name === 'E') return pow(x.base, transpose(x.exp));
  return new Fn('transpose', [x]);
}

export const evaluators: Partial<Record<FnName, Evaluator>> = {
  adjoint: (x) => {
    const c = adjoint(x);
    return c instanceof Fn && c.name === 'adjoint' && c.args[0] === x ? undefined : c;
  },
  transpose: (x) => {
    const c = transpose(x);
    return c instanceof Fn && c.name === 'transpose' && c.args[0] === x ? undefined : c;
  },
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
  const v = ev ? ev(xs[0]!, ...xs.slice(1)) : undefined;
  if (v !== undefined) return v;
  const f = new Fn(name, xs);
  // SymPy Function.__new__: evaluate numerically when every argument is a Float
  if (xs.length > 0) {
    const precs = xs.map(shouldEvalf);
    if (Math.min(...precs) > 0) {
      try {
        return impl.evalf(f, precToDps(Math.max(...precs)));
      } catch {
        return f;
      }
    }
  }
  return f;
}

/** SymPy Function._should_evalf: the precision of a Float (or pure complex Float) argument, else -1. */
function shouldEvalf(a: Expr): number {
  if (a instanceof Float) return a.prec;
  if (!(a instanceof Add) || a.args.length !== 2) return -1;
  const [r, t] = a.args;
  const im = t instanceof Mul && t.args.length === 2 && t.args[1] === S.I ? t.args[0] : undefined;
  if (!isNum(r!) || im === undefined || !isNum(im)) return -1;
  return Math.max(r instanceof Float ? r.prec : -1, im instanceof Float ? im.prec : -1);
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
/**
 * Natural logarithm, or log(x, base) = log(x)/log(base) like SymPy
 * (pulling out integer powers of a rational base first).
 */
export function log(x: ExprLike, base?: ExprLike): Expr {
  if (base === undefined) return fn('log', [x]);
  const b = sympify(base);
  const a = sympify(x);
  if (b instanceof Constant && b.name === 'E') return fn('log', [a]);
  if (b instanceof Rational && b.isOne) return a instanceof Rational && a.isOne ? S.NaN : S.ComplexInfinity;
  if (b instanceof Rational && b.isInteger && b.p > 1n && a instanceof Rational && !a.isZero) {
    const count = (v: bigint) => {
      let m = 0;
      let w = v < 0n ? -v : v;
      while (w % b.p === 0n) { w /= b.p; m++; }
      return m;
    };
    let m = count(a.p);
    if (m === 0) m = -count(a.q);
    if (m !== 0) return add(m, mul(fn('log', [mul(a, pow(b, -m))]), pow(fn('log', [b]), -1)));
  }
  return mul(fn('log', [a]), pow(fn('log', [b]), -1));
}
export const abs = (x: ExprLike): Expr => fn('abs', [x]);
export const re = (x: ExprLike): Expr => fn('re', [x]);
export const im = (x: ExprLike): Expr => fn('im', [x]);
export const arg = (x: ExprLike): Expr => fn('arg', [x]);

/** Hermitian adjoint of a scalar is its conjugate. */
export const dagger = conjugate;

impl.conjugate = conjugate;
impl.abs = abs;
impl.cos = (e) => cos(e);
impl.sin = (e) => sin(e);
