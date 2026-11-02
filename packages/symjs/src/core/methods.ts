// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Structural Expr methods ported from SymPy (coeff, as_independent,
 * as_coeff_add/mul, primitive, as_content_primitive, extract_*, is_polynomial, ...).
 */

import { isIntegerQ, isNegative as isNegativeQ, isPositive, isReal, isZero as isZeroQ } from './assumptions';
import type { ExprLike, FnName } from './nodes';
import { Add, Constant, Expr, Float, Fn, Mul, Pow, Rational, S, Special, Sym, UndefFn, asRational, impl, isNum } from './nodes';
import { gcd, lcm } from './numbers';
import { add, asBaseExp, couldExtractMinusSign, mul, pow, splitCoeff, sympify } from './ops';
import { ExprMap } from './exprmap';
import { freeSymbols, xreplace as xreplaceM } from './traverse';
import { at, getOrThrow } from './guard';
import { InvariantError } from './errors';

// Higher layers are reached through impl (docs/architecture.md: the core imports no other layer)
const diff = (e: Expr, x: Expr): Expr => impl.diff(e, x, 1);
const applyFn = (name: FnName) => (a: Expr): Expr => {
  if (impl.fn === undefined) throw new InvariantError('function constructors are not registered');
  return impl.fn(name, [a]);
};
const abs = applyFn('abs');
const arg = applyFn('arg');
const im = applyFn('im');
const log = applyFn('log');
const re = applyFn('re');
const expandMul = (e: Expr): Expr => {
  if (impl.expandMul === undefined) throw new InvariantError('expandMul is not registered');
  return impl.expandMul(e);
};
const asRealImagExpand = (e: Expr): [Expr, Expr] => {
  if (impl.asRealImagExpand === undefined) throw new InvariantError('asRealImagExpand is not registered');
  return impl.asRealImagExpand(e);
};

const isOne = (e: Expr) => e instanceof Rational && e.isOne;
const isZeroE = (e: Expr) => e instanceof Rational && e.isZero;
const addArgs = (e: Expr): readonly Expr[] => (e instanceof Add ? e.args : [e]);
const mulArgs = (e: Expr): readonly Expr[] => (e instanceof Mul ? e.args : [e]);

/** SymPy `_keep_coeff`: coeff*factors without distributing a Rational over a sum. */
export function keepCoeff(coeffIn: Expr, factorsIn: Expr): Expr {
  let coeff = coeffIn;
  let factors = factorsIn;
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
    if (at(margs, 0).isNumber) {
      margs[0] = mul(at(margs, 0), coeff);
      if (isOne(margs[0])) margs.shift();
    } else margs.unshift(coeff);
    return margs.length === 1 ? at(margs, 0) : new Mul(margs);
  }
  const m = mul(coeff, factors);
  if (m.isNumber && !factors.isNumber) return new Mul([coeff, factors]);
  return m;
}

/** SymPy `args_cnc`: commutative factors (a negative coefficient is split into -1 and its absolute value). */
export function argsCnc(e: Expr, split1 = true): Expr[] {
  return argsCncSplit(e, split1)[0];
}

/** SymPy `args_cnc`: [commutative factors, non-commutative factors in order]. */
export function argsCncSplit(e: Expr, split1 = true): [Expr[], Expr[]] {
  const all = [...mulArgs(e)];
  const nc = all.filter((a) => !a.isCommutative);
  const c = all.filter((a) => a.isCommutative);
  return [argsCncCommutative(c, split1), nc];
}

function argsCncCommutative(c: Expr[], split1: boolean): Expr[] {
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
export function coeff(eIn: ExprLike, xIn: ExprLike, n = 1, right = false, first = true): Expr {
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
      const c = coeff(e, x, 1, right);
      if (isZeroE(c)) return S.Zero;
      return add(e, mul(-1, add(...addArgs(c).map((a) => (right ? mul(x, a) : mul(a, x))))));
    }
    return asIndependent(e, [x], { asAdd: true })[0];
  }
  x = pow(x, n);
  const selfC = e.isCommutative;
  const xC = x.isCommutative;
  if (selfC && !xC) return S.Zero;
  const same = (a: readonly Expr[], b: readonly Expr[]) => a.length === b.length && a.every((t, i) => t.key === at(b, i).key);
  if (first && e instanceof Add && !selfC && !xC) {
    // the part that depends on x exactly
    const xargs = [...mulArgs(x)];
    const d = add(...addArgs(e).filter((i) => xargs.every((xi) => [...mulArgs(i)].some((m) => m.key === xi.key))));
    const rv = coeff(d, x, 1, right, false);
    if (!(rv instanceof Add) || !right) return rv;
    const parts = rv.args.map((i) => argsCncSplit(i));
    const c0 = at(parts, 0)[0];
    if (parts.some(([c]) => !same(c, c0))) return rv;
    return add(...parts.map(([, nc]) => mul(...nc)));
  }
  const oneC = selfC || xC;
  const [xcList, nx] = argsCncSplit(x);
  const xargs = new Map(xcList.map((a) => [a.key, a]));
  const co2: Expr[] = [];
  const co: [Expr[], Expr[]][] = [];
  for (const a of addArgs(e)) {
    const [mc, nc] = argsCncSplit(a);
    const margs = new Map(mc.map((m) => [m.key, m]));
    if (xargs.size > margs.size) continue;
    const resid = [...margs.values()].filter((m) => !xargs.has(m.key));
    if (resid.length + xargs.size === margs.size) {
      if (oneC) co2.push(mul(...resid, ...nc));
      else co.push([resid, nc]);
    }
  }
  if (oneC) return co2.length ? add(...co2) : S.Zero;
  // both non-commutative: compare the non-commutative parts
  if (!co.length) return S.Zero;
  const find = (l: readonly Expr[], sub: readonly Expr[], fromLeft: boolean): number | undefined => {
    if (!sub.length || !l.length || sub.length > l.length) return undefined;
    const k = sub.length;
    const L = fromLeft ? l : [...l].reverse();
    const T = fromLeft ? sub : [...sub].reverse();
    for (let i = 0; i <= L.length - k; i++) {
      if (T.every((t, j) => at(L, i + j).key === t.key)) return fromLeft ? i : L.length - (i + k);
    }
    return undefined;
  };
  const incommon = (l1: readonly Expr[], l2: readonly Expr[]): Expr[] => {
    if (!l1.length || !l2.length) return [];
    const m = Math.min(l1.length, l2.length);
    for (let i = 0; i < m; i++) if (at(l1, i).key !== at(l2, i).key) return l1.slice(0, i);
    return [...l1];
  };
  const fromLeft = !right;
  if (co.every(([, nc]) => same(nc, at(co, 0)[1]))) {
    const ii = find(at(co, 0)[1], nx, fromLeft);
    if (ii !== undefined) {
      if (!right) return mul(add(...co.map(([r]) => mul(...r))), mul(...at(co, 0)[1].slice(0, ii)));
      return mul(...at(co, 0)[1].slice(ii + nx.length));
    }
  }
  const beg = co.map(([, nc]) => nc).reduce((a, b) => incommon(a, b));
  if (beg.length) {
    const ii = find(beg, nx, fromLeft);
    if (ii !== undefined) {
      if (!right) {
        let gcdc = at(co, 0)[0];
        for (let i = 1; i < co.length && gcdc.length; i++) gcdc = gcdc.filter((g) => at(co, i)[0].some((h) => h.key === g.key));
        return mul(...gcdc, ...beg.slice(0, ii));
      }
      const m = ii + nx.length;
      return add(...co.map(([r, nc]) => mul(...r, ...nc.slice(m))));
    }
  }
  const end = co.map(([, nc]) => [...nc].reverse()).reduce((a, b) => incommon(a, b)).reverse();
  if (end.length) {
    const ii = find(end, nx, fromLeft);
    if (ii !== undefined) {
      if (!right) return add(...co.map(([r, nc]) => mul(...r, ...nc.slice(0, -end.length + ii))));
      return mul(...end.slice(ii + nx.length));
    }
  }
  // a single match
  let hit: [number, Expr[], Expr[]] | undefined;
  for (const [r, nc] of co) {
    const ii = find(nc, nx, fromLeft);
    if (ii !== undefined) {
      if (hit) return S.Zero;
      hit = [ii, r, nc];
    }
  }
  if (hit) {
    const [ii, r, nc] = hit;
    return right ? mul(...nc.slice(ii + nx.length)) : mul(...r, ...nc.slice(0, ii));
  }
  return S.Zero;
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
  if (e instanceof Mul && !e.isCommutative) {
    // non-commutative factors: everything from the first dependent one on is dependent
    const [c, nc] = argsCncSplit(e, false);
    const depend = c.filter(has);
    const indep = c.filter((a) => !has(a));
    const i = nc.findIndex(has);
    if (i >= 0) depend.push(...nc.slice(i));
    indep.push(...nc.slice(0, i >= 0 ? i : nc.length));
    return [mul(...indep), mul(...depend)];
  }
  const depend = args.filter(has);
  const indep = args.filter((a) => !has(a));
  if (e instanceof Add) return [add(...indep), depend.length === 0 ? S.Zero : depend.length === 1 ? at(depend, 0) : new Add(depend)];
  return [mul(...indep), depend.length === 0 ? S.One : depend.length === 1 ? at(depend, 0) : new Mul(depend)];
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
  if (e instanceof Add && at(e.args, 0).isNumber) return [at(e.args, 0), [...e.args.slice(1)]];
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
  if (e instanceof Mul && at(e.args, 0).isNumber) return [at(e.args, 0), [...e.args.slice(1)]];
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
export function asContentPrimitive(eIn: ExprLike, opts: { clear?: boolean; radical?: boolean } = {}): [Rational, Expr] {
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
    if (opts.radical && prim instanceof Add) prim = extractCommonRadical(prim);
    return [con, prim];
  }
  if (e instanceof Mul) {
    let coef: Rational = S.One;
    const args: Expr[] = [];
    for (const a of e.args) {
      const [c, p] = asContentPrimitive(a, opts);
      coef = asRational(mul(coef, c));
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
        const ceh = asRational(mul(ce, h));
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
    if (a === undefined) return undefined;
    const b = rest.length === 1 ? at(rest, 0) : new Mul(rest);
    const x = extractMultiplicatively(e, a);
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
      if (q0 instanceof Rational && q0.isInteger && q0.isPositive && q1?.key === e.key) return quotient;
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
      const n = extractMultiplicatively(at(args, i), c);
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
  if (c instanceof Add && at(c.args, 0).isNumber) {
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
    const [ac, aRest] = splitCoeff(a);
    const co2 = coeff(self, aRest);
    if (isZeroE(co2)) return undefined;
    const [coc, cot] = splitAddRational(co2);
    const xa = extractAdditively(coc, ac);
    if (xa === undefined) return undefined;
    self = add(self, mul(-1, co2, aRest));
    coeffs.push(mul(add(cot, xa), aRest));
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
      // simplify is late-bound so that the core does not depend on the simplification modules
      d = diff(e, v);
      try {
        d = impl.simplify(d);
      } catch {
        // simplification not loaded: decide on the derivative as it is
      }
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
    const a = at(e0.args, 0);
    return [log(abs(a)), arg(a)];
  }
  if ((e0 instanceof Pow && e0.base instanceof Constant && e0.base.name === 'E') || e0 instanceof Fn) {
    return asRealImagExpand(e0);
  }
  const e = expandMul(e0);
  return [re(e), im(e)];
}

/** SymPy `as_numer_denom()` (port of the Add, Mul and Pow methods). */
export function asNumerDenom(eIn: ExprLike): [Expr, Expr] {
  const e = sympify(eIn);
  if (!e.isCommutative) return [e, S.One];
  if (e instanceof Rational) return [Rational.of(e.p), Rational.of(e.q)];
  if (e instanceof Mul) {
    const ns: Expr[] = [];
    const ds: Expr[] = [];
    for (const f of e.args) {
      const [ni, di] = asNumerDenom(f);
      ns.push(ni);
      ds.push(di);
    }
    return [mul(...ns), mul(...ds)];
  }
  if (e instanceof Pow) {
    let ex = e.exp;
    const base = e.base;
    if (base instanceof Constant && base.name === 'E') {
      // exp(x).as_numer_denom(): a negative exponent goes to the denominator
      const neg = isNegativeQ(ex) === true || (ex instanceof Mul && isNegativeQ(ex) === undefined && isPositive(ex) === undefined && couldExtractMinusSign(ex));
      return neg ? [S.One, pow(base, mul(-1, ex))] : [e, S.One];
    }
    let [n, d] = asNumerDenom(base);
    let negExp = isNegativeQ(ex) === true;
    if (ex instanceof Mul && !negExp && isPositive(ex) !== true) negExp = couldExtractMinusSign(ex);
    const intExp = isIntegerQ(ex) === true;
    if (!(isReal(d) === true || intExp)) {
      n = base;
      d = S.One;
    }
    const dnonpos = isNegativeQ(d) === true || isZeroQ(d) === true ? true : isPositive(d) === true ? false : undefined;
    if (dnonpos === true) {
      n = mul(-1, n);
      d = mul(-1, d);
    } else if (dnonpos === undefined && !intExp) {
      n = base;
      d = S.One;
    }
    if (negExp) {
      [n, d] = [d, n];
      ex = mul(-1, ex);
    }
    return [pow(n, ex), pow(d, ex)];
  }
  if (e instanceof Add) {
    const [content, expr] = primitive(e);
    if (!(expr instanceof Add)) return asNumerDenom(mul(content, expr));
    const ncon = Rational.of(content.p);
    const dcon = Rational.of(content.q);
    const nd = new Map<string, [Expr, Expr[]]>();
    for (const f of expr.args) {
      const [ni, di] = asNumerDenom(f);
      const cur = nd.get(di.key);
      if (cur) cur[1].push(ni);
      else nd.set(di.key, [di, [ni]]);
    }
    const groups = [...nd.values()];
    if (groups.length === 1) {
      const [d, ns] = at(groups, 0);
      return [add(...ns.map((ni) => keepCoeff(ncon, ni))), keepCoeff(dcon, d)];
    }
    const denoms = groups.map(([d]) => d);
    const numers = groups.map(([, ns]) => (ns.length === 1 ? at(ns, 0) : add(...ns)));
    const n = add(...numers.map((ni, i) => mul(...denoms.slice(0, i), ni, ...denoms.slice(i + 1))));
    return [keepCoeff(ncon, n), keepCoeff(dcon, mul(...denoms))];
  }
  return [e, S.One];
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


/**
 * SymPy `has_free(*patterns)`: does the expression contain any of the
 * patterns as a free subexpression (a free symbol, an applied function of
 * the given name, or a subexpression)?
 */
export function hasFree(eIn: ExprLike, ...patterns: (ExprLike | { fn: string })[]): boolean {
  const e = sympify(eIn);
  const free = freeSymbols(e);
  return patterns.some((p) => {
    if (typeof p === 'object' && !(p instanceof Expr)) {
      const name = p.fn;
      const go = (x: Expr): boolean => (x instanceof UndefFn && x.name === name) || x.args.some(go);
      return go(e);
    }
    const q = sympify(p);
    if (q.kind === 'Symbol') return [...free].some((s) => s.key === q.key);
    if (e.has(q)) return true;
    // a sub-sum or sub-product of an Add/Mul also counts (x + y + 1 has y + 1)
    const qs = q instanceof Add ? q.args : q instanceof Mul ? q.args : undefined;
    if (!qs) return false;
    const go = (x: Expr): boolean => {
      if (x.kind === q.kind && qs.every((a) => x.args.some((b) => b.key === a.key))) return true;
      return x.args.some(go);
    };
    return go(e);
  });
}

/** sqrt(2) + 2*sqrt(10) -> sqrt(2)*(1 + 2*sqrt(5)): the square root of the gcd of the radicands. */
function extractCommonRadical(e: Add): Expr {
  const radicand = (t: Expr): bigint | undefined => {
    for (const f of mulArgs(t)) {
      if (f instanceof Pow && f.base instanceof Rational && f.base.q === 1n && f.exp instanceof Rational && f.exp.p === 1n && f.exp.q === 2n) return f.base.p;
    }
    return undefined;
  };
  let g = 0n;
  for (const t of e.args) {
    const r = radicand(t);
    if (r === undefined) return e;
    g = gcd(g, r);
  }
  if (g <= 1n) return e;
  const s = pow(Rational.of(g), S.Half);
  return mul(s, add(...e.args.map((t) => mul(t, pow(s, -1)))));
}

/** SymPy as_coeff_exponent(x): [c, e] with self = c*x**e and c free of x, else [self, 0]. */
export function asCoeffExponent(eIn: ExprLike, x: Expr): [Expr, Expr] {
  const e = sympify(eIn);
  const cs: Expr[] = [];
  const es: Expr[] = [];
  for (const f of mulArgs(e)) {
    if (f.key === x.key) es.push(S.One);
    else if (f instanceof Pow && f.base.key === x.key && !f.exp.has(x)) es.push(f.exp);
    else if (f.has(x)) return [e, S.Zero];
    else cs.push(f);
  }
  return [mul(...cs), add(...es)];
}

/** SymPy as_powers_dict: base -> exponent of the factors of a product. */
export function asPowersDict(eIn: ExprLike): ExprMap<Expr> {
  const e = sympify(eIn);
  const out = new ExprMap<Expr>();
  for (const f of mulArgs(e)) {
    const [b, x] = f instanceof Pow ? [f.base, f.exp] : [f, S.One];
    out.set(b, add(out.get(b) ?? S.Zero, x));
  }
  return out;
}

/** SymPy `as_coefficients_dict(*syms)`: term -> coefficient. */
export function asCoefficientsDict(eIn: ExprLike, syms: readonly Expr[] = []): ExprMap<Expr> {
  const e = sympify(eIn);
  const out = new Map<string, [Expr, Expr[]]>();
  const put = (k: Expr, v: Expr) => {
    const cur = out.get(k.key);
    if (cur) cur[1].push(v);
    else out.set(k.key, [k, [v]]);
  };
  if (!syms.length) {
    for (const a of e instanceof Add ? e.args : [e]) {
      const [c, m] = splitCoeff(a);
      put(m, c);
    }
    return new ExprMap([...out.values()].map(([k, v]) => [k, v.length === 1 ? at(v, 0) : add(...v)]));
  }
  const [ind, dep] = asIndependent(e, syms, { asAdd: true });
  for (const i of dep instanceof Add ? dep.args : [dep]) {
    if (isZeroE(i)) continue;
    if (i instanceof Mul) {
      const c = mul(...i.args.filter((a) => !syms.some((s) => a.has(s))));
      const x = i.args.filter((a) => syms.some((s) => a.has(s)));
      if (c instanceof Rational && c.isOne) put(i, c);
      else put(x.length === 1 ? at(x, 0) : new Mul(x), c);
    } else put(i, S.One);
  }
  const res = new ExprMap<Expr>([...out.values()].map(([k, v]) => [k, add(...v)]));
  if (!isZeroE(ind)) res.set(S.One, ind);
  return res;
}

/** SymPy as_two_terms: (head, tail) of an Add or Mul. */
export function asTwoTerms(eIn: ExprLike): [Expr, Expr] {
  const e = sympify(eIn);
  if (e instanceof Add) return [at(e.args, 0), add(...e.args.slice(1))];
  if (e instanceof Mul) return [at(e.args, 0), mul(...e.args.slice(1))];
  return [S.One, e];
}

/** SymPy has_xfree(set): does any given expression occur as a node? */
export function hasXfree(eIn: ExprLike, items: readonly Expr[]): boolean {
  const e = sympify(eIn);
  const keys = new Set(items.map((i) => i.key));
  const go = (x: Expr): boolean => keys.has(x.key) || x.args.some(go);
  return go(e);
}

/** SymPy is_algebraic_expr(*syms): built from the symbols with +, *, and rational powers. */
export function isAlgebraicExpr(eIn: ExprLike, syms: readonly Expr[] = []): boolean {
  const e = sympify(eIn);
  const s = syms.length ? [...syms] : [...freeSymbols(e)];
  const go = (x: Expr): boolean => {
    if (!s.some((y) => x.has(y))) return true;
    if (s.some((y) => y.key === x.key)) return true;
    if (x instanceof Add || x instanceof Mul) return x.args.every(go);
    if (x instanceof Pow) return x.exp instanceof Rational && go(x.base);
    return false;
  };
  return go(e);
}

/** SymPy dummy_eq: equality up to renaming the single dummy symbol. */
export function dummyEq(aIn: ExprLike, bIn: ExprLike, symbol?: Expr): boolean {
  const a = sympify(aIn);
  const b = sympify(bIn);
  const dummies = [...freeSymbols(a)].filter((s) => s.constructor.name === 'Dummy');
  if (dummies.length === 0) return a.key === b.key;
  if (dummies.length > 1) return false;
  const d = at(dummies, 0);
  let target = symbol;
  if (!target) {
    const cand = [...freeSymbols(b)].filter((s) => ![...freeSymbols(a)].some((t) => t.key === s.key));
    if (cand.length !== 1) return false;
    target = at(cand, 0);
  }
  return xreplaceM(a, [[d, target]]).key === b.key;
}

/** Singular points of one-argument functions (SymPy Function._singularities). */
const SINGULARITIES: Record<string, string[]> = {
  log: ['0', 'zoo'],
  sin: ['zoo'],
  cos: ['zoo'],
  sinh: ['zoo'],
  cosh: ['zoo'],
  erf: ['zoo'],
};

/** SymPy is_meromorphic(x, a): true/false/undefined. */
export function isMeromorphic(eIn: ExprLike, x: Expr, a: ExprLike): boolean | undefined {
  const e = sympify(eIn);
  const point = sympify(a);
  const subsAt = (t: Expr) => xreplaceM(t, [[x, point]]);
  const isZoo = (t: Expr) => t instanceof Special && (t.name === 'zoo' || t.name === 'oo' || t.name === '-oo');
  const go = (t: Expr): boolean | undefined => {
    if (!t.has(x)) return true;
    if (t.key === x.key) return true;
    if (t instanceof Add || t instanceof Mul) {
      const rs = t.args.map(go);
      if (rs.some((r) => r === false)) return false;
      return rs.every((r) => r === true) ? true : undefined;
    }
    if (t instanceof Pow) {
      const baseM = go(t.base);
      const expInt = t.exp instanceof Rational && t.exp.isInteger;
      if (expInt) return baseM;
      const expM = go(t.exp);
      if (baseM === false) return expM ? false : undefined;
      if (baseM === undefined) return undefined;
      const b = subsAt(t.base);
      if ((b instanceof Rational && b.isZero) || isZoo(b)) return false;
      if (b.freeSymbols().size) return undefined;
      if (!expM) return expM;
      return !isZoo(subsAt(t.exp));
    }
    if (t instanceof Fn) {
      if (t.args.slice(1).some((u) => u.has(x))) return undefined;
      const arg0 = at(t.args, 0);
      if (!go(arg0)) return undefined;
      const sing = SINGULARITIES[t.name];
      if (!sing) return undefined;
      const v = subsAt(arg0);
      const k = v instanceof Special ? v.name === 'zoo' || v.name === 'oo' || v.name === '-oo' ? 'zoo' : v.name : v instanceof Rational ? v.toString() : undefined;
      if (k === undefined) return undefined;
      return !sing.includes(k);
    }
    return undefined;
  };
  return go(e);
}

/**
 * SymPy Basic.is_same(a, b, approx): structural equality where the numbers
 * are compared with `approx` when it is given (e.g. equalValued). Objects
 * other than expressions (matrices) compare by their own isSame.
 */
export function isSame(a: unknown, b: unknown, approx?: (x: Expr, y: Expr) => boolean): boolean {
  if (a instanceof Expr && b instanceof Expr) {
    const same = (x: Expr, y: Expr): boolean =>
      x.isNumber && y.isNumber && x.args.length === 0 && y.args.length === 0 && approx
        ? approx(x, y)
        : x.kind === y.kind && x.args.length === y.args.length && (x.args.length ? x.args.every((u, i) => same(u, at(y.args, i))) : x.key === y.key);
    return same(a, b);
  }
  if (typeof a === 'object' && a !== null && 'isSame' in a && typeof a.isSame === 'function') return Boolean(a.isSame(b, approx));
  return a === b;
}

/** The exact value of a Rational or Float as a Rational, else undefined. */
function exactRational(e: Expr): Rational | undefined {
  if (e instanceof Rational) return e;
  if (e instanceof Float) {
    const { man, exp } = e.mpf;
    return exp >= 0 ? Rational.of(man << BigInt(exp)) : Rational.of(man, 1n << BigInt(-exp));
  }
  return undefined;
}

/** SymPy equal_valued: two numbers with exactly the same value (Float(2.0) and 2). */
export function equalValued(x: ExprLike, y: ExprLike): boolean {
  const a = sympify(x);
  const b = sympify(y);
  const ra = exactRational(a);
  const rb = exactRational(b);
  return ra !== undefined && rb !== undefined ? ra.key === rb.key : a.key === b.key;
}

/** Base and integer exponent of a factor (SymPy decompose_power): x**(3/2) -> [sqrt(x), 3]. */
function decomposePower(e: Expr): [Expr, number] {
  const [b, ex] = asBaseExp(e);
  if (ex instanceof Rational) {
    if (ex.q === 1n) return [b, Number(ex.p)];
    return [pow(b, Rational.of(1n, ex.q)), Number(ex.p)];
  }
  // a symbolic exponent c*t: the integer coefficient c moves to the exponent
  const [c, rest] = splitCoeff(ex);
  if (c instanceof Rational && c.q === 1n && !(c.p === 1n)) return [pow(b, rest), Number(c.p)];
  return [e, 1];
}

/**
 * SymPy Expr.as_terms: the terms with their complex coefficient
 * [re, im], exponent vector over the generators and noncommutative part,
 * and the sorted generators.
 */
export function asTerms(eIn: ExprLike): [[Expr, [[number, number], number[], Expr[]]][], Expr[]] {
  const e = sympify(eIn);
  const gens: Expr[] = [];
  const terms: [Expr, [number, number], Map<string, [Expr, number]>, Expr[]][] = [];
  for (const term of e instanceof Add ? e.args : [e]) {
    const [c0, rest] = splitCoeff(term);
    let coeff = { re: c0.toNumber(), im: 0 };
    const cpart = new Map<string, [Expr, number]>();
    const nc: Expr[] = [];
    if (!(rest instanceof Rational && rest.p === 1n && rest.q === 1n)) {
      for (const f of rest instanceof Mul ? rest.args : [rest]) {
        if (impl.freeSymbols(f).size === 0) {
          try {
            const v = f.toComplex();
            coeff = { re: coeff.re * v.re - coeff.im * v.im, im: coeff.re * v.im + coeff.im * v.re };
            continue;
          } catch {
            // not a numeric value: kept as a generator
          }
        }
        if (f.isCommutative) {
          const [b, k] = decomposePower(f);
          cpart.set(b.key, [b, k]);
          if (!gens.some((g) => g.key === b.key)) gens.push(b);
        } else nc.push(f);
      }
    }
    terms.push([term, [coeff.re, coeff.im], cpart, nc]);
  }
  const sorted = impl.ordered ? impl.ordered(gens) : gens;
  const index = new Map(sorted.map((g, i) => [g.key, i]));
  const out = terms.map(([term, coeff, cpart, nc]) => {
    const monom = sorted.map(() => 0);
    for (const [k, [, ex]] of cpart) monom[getOrThrow(index, k)] = ex;
    return [term, [coeff, monom, nc]] as [Expr, [[number, number], number[], Expr[]]];
  });
  return [out, sorted];
}
