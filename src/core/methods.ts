// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Structural Expr methods ported from SymPy (coeff, as_independent,
 * as_coeff_add/mul, primitive, as_content_primitive, extract_*, is_polynomial, ...).
 */

import { isZero as isZeroQ } from './assumptions';
import { Add, Constant, Expr, ExprLike, Float, Fn, Mul, Pow, Rational, S, Special, Sym, isNum } from './nodes';
import { gcd, lcm } from './numbers';
import { add, mul, pow, splitCoeff, sympify } from './ops';
import { freeSymbols } from './traverse';
import { diff } from '../calculus/diff';
import { abs, arg, im, log, re } from '../functions/elementary';
import { asRealImagExpand, expandMul } from '../simplify/expand';
import { simplify } from '../simplify/simplify';

const isOne = (e: Expr) => e instanceof Rational && e.isOne;
const isZeroE = (e: Expr) => e instanceof Rational && e.isZero;
const addArgs = (e: Expr): readonly Expr[] => (e instanceof Add ? e.args : [e]);
const mulArgs = (e: Expr): readonly Expr[] => (e instanceof Mul ? e.args : [e]);

/** SymPy `_keep_coeff`: coeff*factors without distributing a Rational over a sum. */
export function keepCoeff(coeff: Expr, factors: Expr): Expr {
  if (!coeff.isNumber) {
    if (factors.isNumber) [coeff, factors] = [factors, coeff];
    else return mul(coeff, factors);
  }
  if (isOne(factors)) return coeff;
  if (isOne(coeff)) return factors;
  if (coeff instanceof Rational && coeff.p === -1n && coeff.q === 1n) return mul(-1, factors);
  if (factors instanceof Add) return new Mul([coeff, factors]);
  if (factors instanceof Mul) {
    const margs = [...factors.args];
    if (margs[0]!.isNumber) {
      margs[0] = mul(margs[0]!, coeff);
      if (isOne(margs[0]!)) margs.shift();
    } else margs.unshift(coeff);
    return margs.length === 1 ? margs[0]! : new Mul(margs);
  }
  const m = mul(coeff, factors);
  if (m.isNumber && !factors.isNumber) return new Mul([coeff, factors]);
  return m;
}

/** SymPy `args_cnc`: commutative factors (a negative coefficient is split into -1 and its absolute value). */
export function argsCnc(e: Expr, split1 = true): Expr[] {
  const c = [...mulArgs(e)];
  const first = c[0];
  if (split1 && first !== undefined) {
    if (isNum(first) && first.isNegative && !(first instanceof Rational && first.p === -1n && first.q === 1n)) {
      c.splice(0, 1, S.NegOne, mul(-1, first));
    } else if (first instanceof Special && first.name === '-oo') {
      c.splice(0, 1, S.NegOne, S.Infinity);
    }
  }
  return c;
}

/** SymPy `Expr.coeff(x, n)` (commutative case). */
export function coeff(eIn: ExprLike, xIn: ExprLike, n = 1): Expr {
  const e = sympify(eIn);
  let x = sympify(xIn);
  if (isZeroE(x)) return S.Zero;
  if (x.key === e.key) return n === 1 ? S.One : S.Zero;
  if (isOne(x)) {
    const co = addArgs(e).filter((a) => isOne(splitCoeff(a)[0]));
    return co.length ? add(...co) : S.Zero;
  }
  if (n === 0) {
    if (x instanceof Add && e instanceof Add) {
      const c = coeff(e, x);
      if (isZeroE(c)) return S.Zero;
      return add(e, mul(-1, add(...addArgs(c).map((a) => mul(a, x)))));
    }
    return asIndependent(e, [x], { asAdd: true })[0];
  }
  x = pow(x, n);
  const xargs = new Map(argsCnc(x).map((a) => [a.key, a]));
  const co: Expr[] = [];
  for (const a of addArgs(e)) {
    const margs = argsCnc(a);
    const mset = new Map(margs.map((m) => [m.key, m]));
    if (xargs.size > mset.size) continue;
    const resid = [...mset.values()].filter((m) => !xargs.has(m.key));
    if (resid.length + xargs.size === mset.size) co.push(mul(...resid));
  }
  return co.length ? add(...co) : S.Zero;
}

/** SymPy `as_independent(*deps, as_Add=...)`: [independent, dependent]. */
export function asIndependent(eIn: ExprLike, deps: readonly Expr[], opts: { asAdd?: boolean } = {}): [Expr, Expr] {
  const e = sympify(eIn);
  if (isZeroE(e)) return [e, e];
  const wantAdd = opts.asAdd ?? e instanceof Add;
  const syms = deps.filter((d): d is Sym => d instanceof Sym);
  const other = deps.filter((d) => !(d instanceof Sym));
  const has = (x: Expr): boolean => {
    if (other.some((o) => x.has(o))) return true;
    if (syms.length === 0) return false;
    const fs = freeSymbols(x);
    return syms.some((s) => [...fs].some((f) => f.key === s.key));
  };
  const isWant = wantAdd ? e instanceof Add : e instanceof Mul;
  if (!isWant) {
    const identity = wantAdd ? S.Zero : S.One;
    return has(e) ? [identity, e] : [e, identity];
  }
  const args = e.args;
  const depend = args.filter(has);
  const indep = args.filter((a) => !has(a));
  if (e instanceof Add) return [add(...indep), depend.length === 0 ? S.Zero : depend.length === 1 ? depend[0]! : new Add(depend)];
  return [mul(...indep), depend.length === 0 ? S.One : depend.length === 1 ? depend[0]! : new Mul(depend)];
}

/** SymPy `as_coeff_add(*deps)`. */
export function asCoeffAdd(eIn: ExprLike, deps: readonly Expr[] = []): [Expr, Expr[]] {
  const e = sympify(eIn);
  if (deps.length) {
    if (!(e instanceof Add)) return deps.some((d) => e.has(d)) ? [S.Zero, [e]] : [e, []];
    const dep = e.args.filter((a) => deps.some((d) => a.has(d)));
    const ind = e.args.filter((a) => !deps.some((d) => a.has(d)));
    return [add(...ind), dep];
  }
  if (isNum(e)) return [e, []];
  if (e instanceof Add && e.args[0]!.isNumber) return [e.args[0]!, [...e.args.slice(1)]];
  return [S.Zero, e instanceof Add ? [...e.args] : [e]];
}

/** SymPy `as_coeff_mul(*deps)`. */
export function asCoeffMul(eIn: ExprLike, deps: readonly Expr[] = []): [Expr, Expr[]] {
  const e = sympify(eIn);
  if (deps.length) {
    if (!(e instanceof Mul)) return deps.some((d) => e.has(d)) ? [S.One, [e]] : [e, []];
    const dep = e.args.filter((a) => deps.some((d) => a.has(d)));
    const ind = e.args.filter((a) => !deps.some((d) => a.has(d)));
    return [mul(...ind), dep];
  }
  if (isNum(e)) return [e, []];
  if (e instanceof Mul && e.args[0]!.isNumber) return [e.args[0]!, [...e.args.slice(1)]];
  return [S.One, [e]];
}

/** SymPy `primitive()`: [content, primitive] with rational content. */
export function primitive(eIn: ExprLike): [Rational, Expr] {
  const e = sympify(eIn);
  if (e instanceof Add) {
    const terms = e.args.map((a) => {
      const [c, m] = splitCoeff(a);
      return c instanceof Rational ? { p: c.p, q: c.q, m } : { p: 1n, q: 1n, m: a };
    });
    let ngcd = 0n;
    let dlcm = 1n;
    for (const t of terms) {
      ngcd = gcd(ngcd, t.p);
      dlcm = lcm(dlcm, t.q);
    }
    if (ngcd === 1n && dlcm === 1n) return [S.One, e];
    const newTerms = terms.map((t) => keepCoeff(Rational.of((t.p / ngcd) * (dlcm / t.q)), t.m));
    return [Rational.of(ngcd, dlcm), add(...newTerms)];
  }
  if (isZeroE(e)) return [S.One, S.Zero];
  let [c, r] = splitCoeff(e);
  if (!(c instanceof Rational)) return [S.One, e];
  if (c.isNegative) {
    c = Rational.of(-c.p, c.q);
    r = mul(-1, r);
  }
  return [c, r];
}

/** SymPy `as_content_primitive(radical=False, clear=True)`. */
export function asContentPrimitive(eIn: ExprLike, opts: { clear?: boolean } = {}): [Rational, Expr] {
  const e = sympify(eIn);
  const clear = opts.clear ?? true;
  if (e instanceof Rational) {
    if (e.isZero) return [S.One, e];
    return e.isPositive ? [e, S.One] : [Rational.of(-e.p, e.q), S.NegOne];
  }
  if (e instanceof Add) {
    const inner = add(...e.args.map((a) => keepCoeff(...asContentPrimitive(a, opts))));
    let [con, prim] = primitive(inner);
    if (!clear && !con.isInteger && prim instanceof Add) {
      const d = Rational.of(con.q);
      const p2 = mul(prim, pow(d, -1));
      if (addArgs(p2).some((a) => { const c = splitCoeff(a)[0]; return c instanceof Rational && c.isInteger; })) {
        prim = p2;
        con = Rational.of(con.p);
      }
    }
    return [con, prim];
  }
  if (e instanceof Mul) {
    let coef: Rational = S.One;
    const args: Expr[] = [];
    for (const a of e.args) {
      const [c, p] = asContentPrimitive(a, opts);
      coef = mul(coef, c) as Rational;
      if (!isOne(p)) args.push(p);
    }
    return [coef, mul(...args)];
  }
  if (e instanceof Pow) {
    const [b0, x0] = e.args;
    const b = keepCoeff(...asContentPrimitive(b0, opts));
    const [ce, pe] = asContentPrimitive(x0, opts);
    if (b instanceof Rational && !b.isZero) {
      const [h, t] = splitAddRational(pe);
      if (h instanceof Rational) {
        const ceh = mul(ce, h) as Rational;
        let c = pow(b, ceh);
        let r: Expr = S.Zero;
        if (!(c instanceof Rational)) {
          const iceh = ceh.p / ceh.q - (ceh.p % ceh.q !== 0n && ceh.p < 0n ? 1n : 0n);
          const rem = ceh.p - iceh * ceh.q;
          r = Rational.of(rem);
          c = pow(b, Rational.of(iceh));
        }
        if (c instanceof Rational) {
          return [c, pow(b, keepCoeff(ce, add(t, mul(r, pow(ce, -1), Rational.of(1n, ceh.q)))))];
        }
      }
    }
    const ex = keepCoeff(ce, pe);
    if (ex instanceof Rational && b instanceof Mul) {
      const [h, t] = asContentPrimitive(b, opts);
      const cm = pow(h, ex);
      const [c, m] = splitCoeff(cm);
      if (c instanceof Rational && (isOne(m) || (m instanceof Pow && m.exp.key === ex.key))) {
        const mb = m instanceof Pow ? m.base : m;
        return [c, pow(keepCoeff(mb, t), ex)];
      }
    }
    return [S.One, pow(b, ex)];
  }
  return [S.One, e];
}

function splitAddRational(e: Expr): [Expr, Expr] {
  if (e instanceof Rational) return [e, S.Zero];
  if (e instanceof Add && e.args[0] instanceof Rational) return [e.args[0], add(...e.args.slice(1))];
  return [S.Zero, e];
}

/** SymPy `extract_multiplicatively(c)`; undefined when not possible. */
export function extractMultiplicatively(eIn: ExprLike, cIn: ExprLike): Expr | undefined {
  const e = sympify(eIn);
  let c = sympify(cIn);
  if (e instanceof Special && e.name === 'nan') return undefined;
  if (isOne(c)) return e;
  if (c.key === e.key) return S.One;
  if (c instanceof Add) {
    const [cc, pc] = primitive(c);
    if (!cc.isOne) c = new Mul([cc, pc]);
  }
  if (c instanceof Mul) {
    const [a, ...rest] = c.args;
    const b = rest.length === 1 ? rest[0]! : new Mul(rest);
    const x = extractMultiplicatively(e, a!);
    return x === undefined ? undefined : extractMultiplicatively(x, b);
  }
  const quotient = mul(e, pow(c, -1));
  if (isNum(e)) {
    if (e instanceof Rational) {
      if (!(quotient instanceof Rational)) return undefined;
      if (e.isInteger && !quotient.isInteger) return undefined;
      if (e.isPositive && quotient.isNegative) return undefined;
      return quotient;
    }
    if (!(quotient instanceof Float)) return undefined;
    if (e.isPositive && quotient.isNegative) return undefined;
    return quotient;
  }
  if (e instanceof Special) {
    if (e.name === 'oo' && isPos(c)) return S.Infinity;
    return undefined;
  }
  if (e instanceof Sym || e instanceof Constant) {
    if (quotient instanceof Mul && quotient.args.length === 2) {
      const [q0, q1] = quotient.args;
      if (q0 instanceof Rational && q0.isInteger && q0.isPositive && q1!.key === e.key) return quotient;
    } else if (quotient instanceof Rational && quotient.isInteger && c.isNumber) return quotient;
    return undefined;
  }
  if (e instanceof Add) {
    const [cs, ps] = primitive(e);
    if (isNum(c) && !(c instanceof Rational && c.p === -1n && c.q === 1n)) {
      if (!cs.isOne) {
        let xc: Expr | undefined;
        if (c.isNegative) {
          xc = extractMultiplicatively(cs, mul(-1, c));
          if (xc !== undefined) xc = mul(-1, xc);
        } else xc = extractMultiplicatively(cs, c);
        if (xc !== undefined) return mul(xc, ps);
      }
      return undefined;
    }
    if (c.key === ps.key) return cs;
    const newargs: Expr[] = [];
    for (const arg of addArgs(ps)) {
      const n = extractMultiplicatively(arg, c);
      if (n === undefined) return undefined;
      newargs.push(n);
    }
    if (!cs.isOne) return new Add(newargs.map((t) => mul(cs, t)));
    return add(...newargs);
  }
  if (e instanceof Mul) {
    const args = [...e.args];
    for (let i = 0; i < args.length; i++) {
      const n = extractMultiplicatively(args[i]!, c);
      if (n !== undefined) {
        args[i] = n;
        return mul(...args);
      }
    }
    return undefined;
  }
  if (e instanceof Pow) {
    const [sb, se] = e.args;
    const [cb, ce] = c instanceof Pow ? c.args : [c, S.One];
    if (cb.key === sb.key) {
      const ne = extractAdditively(se, ce);
      if (ne !== undefined) return pow(sb, ne);
    } else if (c.key === sb.key) {
      const ne = extractAdditively(se, S.One);
      if (ne !== undefined) return pow(sb, ne);
    }
  }
  return undefined;
}

const isPos = (e: Expr) => isNum(e) && e.isPositive;

/** SymPy `extract_additively(c)` (main cases). */
export function extractAdditively(eIn: ExprLike, cIn: ExprLike): Expr | undefined {
  const e = sympify(eIn);
  const c = sympify(cIn);
  if (e instanceof Special && e.name === 'nan') return undefined;
  if (isZeroQ(c) === true) return e;
  if (c.key === e.key) return S.Zero;
  if (isZeroE(e)) return undefined;
  if (isNum(e)) {
    if (!isNum(c)) return undefined;
    const d = add(e, mul(-1, c));
    if (!isNum(d)) return undefined;
    const co = e;
    if ((co.isPositive && !d.isNegative && cmpNum(d, co) < 0) || (co.isNegative && !d.isPositive && cmpNum(d, co) > 0)) return d;
    return undefined;
  }
  if (isNum(c)) {
    const [co, t] = splitAddRational(e);
    const xa = extractAdditively(co, c);
    return xa === undefined ? undefined : add(xa, t);
  }
  if (c instanceof Add && c.args[0]!.isNumber) {
    const co = coeff(e, c);
    const xa0 = mul(extractAdditively(co, 1) ?? S.Zero, c);
    if (!isZeroE(xa0)) {
      const diff_ = add(e, mul(-1, co, c));
      const r = add(xa0, extractAdditively(diff_, c) ?? diff_);
      return isZeroE(r) ? undefined : r;
    }
    const [h, t] = splitAddRational(c);
    const [sh, st] = splitAddRational(e);
    const xa = extractAdditively(sh, h);
    if (xa === undefined) return undefined;
    const xa2 = extractAdditively(st, t);
    if (xa2 === undefined) return undefined;
    return add(xa, xa2);
  }
  // corem: e = co*c + diff
  const coTerms: Expr[] = [];
  const diffTerms: Expr[] = [];
  for (const term of addArgs(e)) {
    const ci = coeff(term, c);
    if (isZeroE(ci)) diffTerms.push(term);
    else coTerms.push(ci);
  }
  const co = add(...coTerms);
  const diff_ = add(...diffTerms);
  const xa0 = mul(extractAdditively(co, 1) ?? S.Zero, c);
  if (!isZeroE(xa0)) {
    const r = add(xa0, extractAdditively(diff_, c) ?? diff_);
    return isZeroE(r) ? undefined : r;
  }
  let self = e;
  const coeffs: Expr[] = [];
  for (const a of addArgs(c)) {
    const [ac, at] = splitCoeff(a);
    const co2 = coeff(self, at);
    if (isZeroE(co2)) return undefined;
    const [coc, cot] = splitAddRational(co2);
    const xa = extractAdditively(coc, ac);
    if (xa === undefined) return undefined;
    self = add(self, mul(-1, co2, at));
    coeffs.push(mul(add(cot, xa), at));
  }
  coeffs.push(self);
  return add(...coeffs);
}

const cmpNum = (a: Expr, b: Expr): number => {
  const d = add(a, mul(-1, b));
  return isNum(d) ? (d.isNegative ? -1 : d.isZero ? 0 : 1) : 0;
};

/** SymPy `as_coefficient(expr)`. */
export function asCoefficient(e: ExprLike, x: ExprLike): Expr | undefined {
  const r = extractMultiplicatively(e, x);
  if (r !== undefined && !isZeroE(r) && !r.has(sympify(x))) return r;
  return undefined;
}

function symsOrAll(e: Expr, syms: readonly Expr[]): Expr[] {
  return syms.length ? [...syms] : [...freeSymbols(e)];
}

/** SymPy `is_polynomial(*syms)`. */
export function isPolynomial(eIn: ExprLike, syms: readonly Expr[] = []): boolean {
  const e = sympify(eIn);
  const s = symsOrAll(e, syms);
  if (s.length === 0) return true;
  const inSyms = (x: Expr) => s.some((y) => y.key === x.key);
  const hasAny = (x: Expr) => s.some((y) => x.has(y));
  const go = (x: Expr): boolean => {
    if (inSyms(x)) return true;
    if (!hasAny(x)) return true;
    if (x instanceof Add || x instanceof Mul) return x.args.every(go);
    if (x instanceof Pow) {
      if (hasAny(x.exp)) return false;
      return go(x.base) && x.exp instanceof Rational && x.exp.isInteger && !x.exp.isNegative;
    }
    return false;
  };
  return go(e);
}

/** SymPy `is_rational_function(*syms)`. */
export function isRationalFunction(eIn: ExprLike, syms: readonly Expr[] = []): boolean {
  const e = sympify(eIn);
  if (e instanceof Special) return false;
  const s = symsOrAll(e, syms);
  if (s.length === 0) return true;
  const inSyms = (x: Expr) => s.some((y) => y.key === x.key);
  const hasAny = (x: Expr) => s.some((y) => x.has(y));
  const go = (x: Expr): boolean => {
    if (inSyms(x) || !hasAny(x)) return true;
    if (x instanceof Add || x instanceof Mul) return x.args.every(go);
    if (x instanceof Pow) {
      if (hasAny(x.exp)) return false;
      return go(x.base) && x.exp instanceof Rational && x.exp.isInteger;
    }
    return false;
  };
  return go(e);
}

/** SymPy `is_constant(*wrt)` (symbolic check via derivatives). */
export function isConstant(eIn: ExprLike, wrt: readonly Sym[] = []): boolean {
  const e = sympify(eIn);
  const free = [...freeSymbols(e)];
  const vars = wrt.length ? free.filter((f) => wrt.some((w) => w.key === f.key)) : free;
  if (vars.length === 0) return true;
  if (e instanceof Sym) return false;
  for (const v of vars) {
    let d: Expr;
    try {
      d = simplify(diff(e, v));
    } catch {
      return false;
    }
    if (!isZeroE(d)) return false;
  }
  return true;
}

/** SymPy `as_real_imag()`. */
export function asRealImag(eIn: ExprLike): [Expr, Expr] {
  const e0 = sympify(eIn);
  if (e0 instanceof Fn && e0.name === 'log') {
    const a = e0.args[0]!;
    return [log(abs(a)), arg(a)];
  }
  if ((e0 instanceof Pow && e0.base instanceof Constant && e0.base.name === 'E') || e0 instanceof Fn) {
    return asRealImagExpand(e0);
  }
  const e = expandMul(e0);
  return [re(e), im(e)];
}

/** SymPy `as_numer_denom()`. */
export function asNumerDenom(eIn: ExprLike): [Expr, Expr] {
  const e = sympify(eIn);
  const n: Expr[] = [];
  const d: Expr[] = [];
  for (const f of mulArgs(e)) {
    if (f instanceof Rational) {
      n.push(Rational.of(f.p));
      d.push(Rational.of(f.q));
    } else if (f instanceof Pow && splitCoeff(f.exp)[0].isNegative) d.push(pow(f.base, mul(-1, f.exp)));
    else n.push(f);
  }
  return [mul(...n), mul(...d)];
}

/** Atoms of the expression, optionally filtered by a predicate. */
export function atoms(eIn: ExprLike, pred: (a: Expr) => boolean = () => true): Expr[] {
  const e = sympify(eIn);
  const out = new Map<string, Expr>();
  const go = (x: Expr) => {
    if (x.args.length === 0) {
      if (pred(x)) out.set(x.key, x);
      return;
    }
    x.args.forEach(go);
  };
  go(e);
  return [...out.values()];
}

