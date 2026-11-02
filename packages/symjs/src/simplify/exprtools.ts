// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Term-wise common factor extraction (a port of SymPy's exprtools:
 * _keep_coeff, Term/Factors, gcd_terms, factor_terms) and the helpers
 * built on it (collect_const, signsimp).
 */

import { Add, Constant, Expr, ExprLike, Float, Mul, Pow, Rational, S, Special, impl } from '../core/nodes';
import { add, mul, pow, splitCoeff, sympify } from '../core/ops';
import { asContentPrimitive, asIndependent, primitive } from '../core/methods';
import { rebuild, xreplace } from '../core/traverse';
import { Concrete } from '../concrete/node';
import { Dummy } from '../core/nodes';
import { gcd as igcd, lcm as ilcm } from '../core/numbers';

const isNumber = (e: Expr): e is Rational | Float => e instanceof Rational || e instanceof Float;
const isOneE = (e: Expr) => e instanceof Rational && e.isOne;
const isNegOneE = (e: Expr) => e instanceof Rational && e.p === -1n && e.q === 1n;
const isExpPow = (e: Expr): boolean => e instanceof Pow && e.base instanceof Constant && e.base.name === 'E';

/** An unevaluated product (SymPy Mul(..., evaluate=False) / Mul._from_args). */
function rawMul(args: Expr[]): Expr {
  const xs = args.flatMap((a) => (a instanceof Mul ? [...a.args] : [a]));
  if (xs.length === 0) return S.One;
  if (xs.length === 1) return xs[0]!;
  return new Mul(xs);
}
function rawAdd(args: Expr[]): Expr {
  if (args.length === 0) return S.Zero;
  if (args.length === 1) return args[0]!;
  return new Add(args);
}

/** SymPy _keep_coeff(coeff, factors, clear, sign). */
export function keepCoeff(coeff: Expr, factors: Expr, clear = true, sign = false): Expr {
  if (!isNumber(coeff)) {
    if (isNumber(factors)) [factors, coeff] = [coeff, factors];
    else return mul(coeff, factors);
  }
  if (isOneE(factors)) return coeff;
  if (isOneE(coeff)) return factors;
  if (isNegOneE(coeff) && !sign) return mul(-1, factors);
  if (factors instanceof Add) {
    if (!clear && coeff instanceof Rational && coeff.q !== 1n) {
      const args = factors.args.map((i) => {
        const [c, m] = splitCoeff(i);
        return [keepCoeff(c, coeff), m] as const;
      });
      if (args.some(([c]) => c instanceof Rational && c.isInteger)) {
        return rawAdd(args.map(([c, m]) => (isOneE(c) ? m : rawMul([c, m]))));
      }
    }
    return new Mul([coeff, factors]);
  }
  if (factors instanceof Mul) {
    const margs = [...factors.args];
    if (isNumber(margs[0]!)) {
      margs[0] = mul(margs[0]!, coeff);
      if (isOneE(margs[0]!)) margs.shift();
    } else margs.unshift(coeff);
    return rawMul(margs);
  }
  const m = mul(coeff, factors);
  if (isNumber(m) && !isNumber(factors)) return new Mul([coeff, factors]);
  return m;
}

/** SymPy decompose_power: expr = base**e with integer e. */
export function decomposePower(e: Expr): [Expr, number] {
  if (isExpPow(e)) {
    const [c, tail] = splitCoeff((e as Pow).exp);
    if (c instanceof Rational && c.q === 1n && !isOneE(c)) return [pow(S.E, tail), Number(c.p)];
    return [e, 1];
  }
  if (!(e instanceof Pow)) return [e, 1];
  const b = e.base;
  const x = e.exp;
  if (isNumber(x)) {
    if (x instanceof Rational) {
      const base = x.isInteger ? b : pow(b, Rational.of(1n, x.q));
      return [base, Number(x.p)];
    }
    return [e, 1];
  }
  const [c, tail] = splitCoeff(x);
  if (c instanceof Rational && isNegOneE(c)) return [pow(b, tail), -1];
  if (c instanceof Rational && !isOneE(c)) {
    return [pow(b, keepCoeff(Rational.of(1n, c.q), tail)), Number(c.p)];
  }
  return [e, 1];
}

/** Factor -> exponent map. */
class Factors {
  constructor(readonly f: Map<string, [Expr, number]> = new Map()) {}
  static of(entries: [Expr, number][]): Factors {
    const m = new Map<string, [Expr, number]>();
    for (const [b, e] of entries) {
      const cur = m.get(b.key);
      const ne = (cur?.[1] ?? 0) + e;
      if (ne) m.set(b.key, [b, ne]);
      else m.delete(b.key);
    }
    return new Factors(m);
  }
  mul(o: Factors): Factors {
    return Factors.of([...this.f.values(), ...o.f.values()]);
  }
  gcd(o: Factors): Factors {
    const out: [Expr, number][] = [];
    for (const [k, [b, e]] of this.f) {
      const oe = o.f.get(k);
      if (oe) out.push([b, Math.min(e, oe[1])]);
    }
    return Factors.of(out);
  }
  lcm(o: Factors): Factors {
    const m = new Map(this.f);
    for (const [k, [b, e]] of o.f) {
      const cur = m.get(k);
      m.set(k, [b, Math.max(cur?.[1] ?? 0, e)]);
    }
    return new Factors(m);
  }
  /** Cancel common factors with another factor set. */
  normal(o: Factors): [Factors, Factors] {
    const a = new Map(this.f);
    const b = new Map(o.f);
    for (const [k, [base, se]] of this.f) {
      const oe = o.f.get(k);
      if (!oe) continue;
      const d = se - oe[1];
      if (d === 0) {
        a.delete(k);
        b.delete(k);
      } else if (d > 0) {
        a.set(k, [base, d]);
        b.delete(k);
      } else {
        a.delete(k);
        b.set(k, [base, -d]);
      }
    }
    return [new Factors(a), new Factors(b)];
  }
  quo(o: Factors): Factors {
    return this.normal(o)[0];
  }
  asExpr(): Expr {
    const args: Expr[] = [];
    for (const [b, e] of this.f.values()) {
      if (e !== 1) {
        const [bb, ee] = b instanceof Pow && !isExpPow(b) ? [b.base, b.exp] : isExpPow(b) ? [S.E, (b as Pow).exp] : [b, S.One];
        args.push(pow(bb, keepCoeff(Rational.of(BigInt(e)), ee)));
      } else args.push(b);
    }
    return mul(...args);
  }
}

class Term {
  constructor(
    readonly coeff: Rational | Float,
    readonly numer: Factors,
    readonly denom: Factors,
  ) {}
  static of(term: Expr): Term {
    let [coeff, rest] = splitCoeff(term);
    const numer: [Expr, number][] = [];
    const denom: [Expr, number][] = [];
    for (const factor of rest instanceof Mul ? rest.args : isOneE(rest) ? [] : [rest]) {
      let [base, e] = decomposePower(factor);
      if (base instanceof Add) {
        const [cont, prim] = primitive(base);
        coeff = mul(coeff, pow(cont, e)) as Rational;
        base = prim;
      }
      if (e > 0) numer.push([base, e]);
      else denom.push([base, -e]);
    }
    return new Term(coeff, Factors.of(numer), Factors.of(denom));
  }
  asExpr(): Expr {
    return mul(this.coeff, this.numer.asExpr(), pow(this.denom.asExpr(), -1));
  }
  mul(o: Term): Term {
    const coeff = mul(this.coeff, o.coeff) as Rational;
    const [n, d] = this.numer.mul(o.numer).normal(this.denom.mul(o.denom));
    return new Term(coeff, n, d);
  }
  inv(): Term {
    return new Term(pow(this.coeff, -1) as Rational, this.denom, this.numer);
  }
  quo(o: Term): Term {
    return this.mul(o.inv());
  }
  gcd(o: Term): Term {
    return new Term(numGcd(this.coeff, o.coeff), this.numer.gcd(o.numer), this.denom.gcd(o.denom));
  }
}

/** Rational.gcd: gcd of numerators over lcm of denominators. */
function numGcd(a: Rational | Float, b: Rational | Float): Rational {
  if (!(a instanceof Rational) || !(b instanceof Rational)) return S.One;
  return Rational.of(igcd(a.p, b.p), ilcm(a.q, b.q));
}

function gcdTermsCore(terms0: Expr[], isprimitive: boolean, fraction: boolean): [Expr, Expr, Expr] {
  const terms = terms0.filter((t) => !(t instanceof Rational && t.isZero)).map(Term.of);
  if (terms.length === 0) return [S.Zero, S.Zero, S.One];
  let cont: Expr;
  let numer: Expr;
  let denom: Expr;
  if (terms.length === 1) {
    cont = terms[0]!.coeff;
    numer = terms[0]!.numer.asExpr();
    denom = terms[0]!.denom.asExpr();
  } else {
    let c = terms[0]!;
    for (const t of terms.slice(1)) c = c.gcd(t);
    const qs = terms.map((t) => t.quo(c));
    let numers: Expr[];
    let den: Factors;
    if (fraction) {
      den = qs[0]!.denom;
      for (const t of qs.slice(1)) den = den.lcm(t.denom);
      numers = qs.map((t) => mul(t.coeff, t.numer.mul(den.quo(t.denom)).asExpr()));
    } else {
      numers = qs.map((t) => t.asExpr());
      den = new Factors();
    }
    cont = c.asExpr();
    numer = add(...numers);
    denom = den.asExpr();
  }
  if (!isprimitive && numer instanceof Add) {
    const [c2, p] = primitive(numer);
    cont = mul(cont, c2);
    numer = p;
  }
  return [cont, numer, denom];
}

/** SymPy gcd_terms: factor out common terms of a sum, recursing into other nodes. */
export function gcdTerms(termsIn: ExprLike, opts: { isprimitive?: boolean; clear?: boolean; fraction?: boolean } = {}): Expr {
  const terms = sympify(termsIn);
  const clear = opts.clear ?? true;
  if (terms instanceof Add) return gcdTermsOf([...terms.args], opts);
  if (terms.args.length === 0) return terms;
  if (terms instanceof Mul) {
    const [c, rest] = splitCoeff(terms);
    const args = rest instanceof Mul ? rest.args : [rest];
    return keepCoeff(c, mul(...args.map((i) => gcdTerms(i, opts))), clear);
  }
  return rebuild(terms, terms.args.map((a) => gcdTerms(a, opts)));
}

/** gcd_terms applied to a list of terms (an Add that has not been combined). */
export function gcdTermsOf(termsList: readonly Expr[], opts: { isprimitive?: boolean; clear?: boolean; fraction?: boolean } = {}): Expr {
  const isprimitive = opts.isprimitive ?? false;
  const clear = opts.clear ?? true;
  const fraction = opts.fraction ?? true;
  {
    const [cont, numer0, denom] = gcdTermsCore([...termsList], isprimitive, fraction);
    let numer = numer0;
    let [coeff, factors] = splitCoeff(cont) as [Expr, Expr];
    if (!clear) {
      const [c, _coeff] = splitCoeff(coeff);
      if (!(c instanceof Rational && c.isInteger) && numer instanceof Add && c instanceof Rational) {
        const n = Rational.of(c.p);
        const d = Rational.of(c.q);
        const _numer = mul(numer, pow(d, -1));
        if ((_numer instanceof Add ? _numer.args : [_numer]).some((a) => { const k = splitCoeff(a)[0]; return k instanceof Rational && k.isInteger; })) {
          numer = _numer;
          coeff = mul(n, _coeff);
        }
      }
    }
    return keepCoeff(coeff, mul(factors, numer, pow(denom, -1)), clear);
  }
}

/** SymPy factor_terms: pull out common factors and content from terms, recursively. */
export function factorTerms(
  exprIn: ExprLike,
  opts: { radical?: boolean; clear?: boolean; fraction?: boolean; sign?: boolean } = {},
): Expr {
  const clear = opts.clear ?? false;
  const fraction = opts.fraction ?? false;
  const sign = opts.sign ?? true;
  const doit = (expr: Expr): Expr => {
    if (expr.args.length === 0) return expr;
    if (expr instanceof Pow || expr.kind === 'Fn' || expr.kind === 'Undef' || expr.kind === 'Rel') {
      const newargs = expr.args.map(doit);
      if (newargs.every((a, i) => a.key === expr.args[i]!.key)) return expr;
      return rebuild(expr, newargs);
    }
    if (expr instanceof Concrete && expr.kind2 === 'Sum') return factorSum(expr, doit);
    let [cont, p] = asContentPrimitive(expr, { clear }) as [Expr, Expr];
    if (p instanceof Add) {
      let listArgs = p.args.map(doit);
      // a common negative sign (if any) is not removed by gcd_terms
      if (listArgs.every((a) => { const c = splitCoeff(a)[0]; return c.isNegative; })) {
        cont = mul(-1, cont);
        listArgs = listArgs.map((a) => mul(-1, a));
      }
      const special: [Expr, Expr][] = [];
      listArgs = listArgs.map((a) => {
        const e = a instanceof Pow ? a.exp : S.One;
        if (e instanceof Mul && e.key !== mul(...e.args).key) {
          const d = new Dummy();
          special.push([d, a]);
          return d;
        }
        return a;
      });
      p = add(...listArgs);
      p = gcdTerms(p, { isprimitive: true, clear, fraction });
      if (special.length) p = xreplace(p, special);
    } else if (p.args.length) {
      p = rebuild(p, p.args.map(doit));
    }
    return keepCoeff(cont, p, clear, sign);
  };
  return doit(sympify(exprIn));
}

/** SymPy factor_sum: pull terms independent of the summation variables out of a Sum. */
function factorSum(s: Concrete, doit: (e: Expr) => Expr): Expr {
  const result = s.function;
  if (result instanceof Rational && result.isZero) return S.Zero;
  const vars = s.limits.map(([k]) => k);
  const retv = doit(result);
  const [i, d] = asIndependent(retv, vars);
  const lims = s.args.slice(1);
  if (retv instanceof Add) return add(mul(i, new Concrete('Sum', [S.One, ...lims])), new Concrete('Sum', [d, ...lims]));
  return mul(i, new Concrete('Sum', [d, ...lims]));
}

/** SymPy Factors(expr).factors for a product: base -> exponent, rationals split into p and 1/q. */
function factorsOf(e: Expr): Map<string, [Expr, Expr]> {
  const out = new Map<string, [Expr, Expr]>();
  const put = (b: Expr, x: Expr) => {
    const cur = out.get(b.key);
    const nx = cur ? add(cur[1], x) : x;
    if (nx instanceof Rational && nx.isZero) out.delete(b.key);
    else out.set(b.key, [b, nx]);
  };
  for (const f of e instanceof Mul ? e.args : [e]) {
    if (f instanceof Rational && !f.isInteger) {
      if (f.p !== 1n) putNumber(put, Rational.of(f.p), S.One);
      put(Rational.of(f.q), S.NegOne);
    } else if (f instanceof Rational) {
      putNumber(put, f, S.One);
    } else if (f instanceof Pow && !isExpPow(f)) put(f.base, f.exp);
    else put(f, S.One);
  }
  return out;
}

/** Negative integers are split into -1 and the absolute value (SymPy's special factors). */
function putNumber(put: (b: Expr, x: Expr) => void, n: Rational, x: Expr): void {
  if (n.isNegative) {
    put(S.NegOne, S.One);
    if (!(n.p === -1n)) put(Rational.of(-n.p), x);
  } else if (!n.isOne) put(n, x);
}

/** Factors.div: [quotient, remainder] factor maps. */
function factorsDiv(a: Map<string, [Expr, Expr]>, b: Map<string, [Expr, Expr]>): [Map<string, [Expr, Expr]>, Map<string, [Expr, Expr]>] {
  const quo = new Map(a);
  const rem = new Map<string, [Expr, Expr]>();
  for (const [k, [base, x]] of b) {
    const cur = quo.get(k);
    if (cur) {
      const d = add(cur[1], mul(-1, x));
      if (d instanceof Rational) {
        if (d.isNegative || d.isZero) quo.delete(k);
        if (!d.isNegative) {
          if (!d.isZero) quo.set(k, [base, d]);
          continue;
        }
        rem.set(k, [base, mul(-1, d)]);
        continue;
      }
    }
    rem.set(k, [base, x]);
  }
  return [quo, rem];
}

function factorsExpr(f: Map<string, [Expr, Expr]>): Expr {
  return mul(...[...f.values()].map(([b, x]) => pow(b, x)));
}

/** SymPy collect_const: collect terms sharing a numeric (or given) factor. */
export function collectConst(exprIn: ExprLike, varsIn: readonly Expr[] = [], opts: { numbers?: boolean } = {}): Expr {
  let expr = sympify(exprIn);
  const numbers = opts.numbers ?? true;
  if (!(expr instanceof Add)) return expr;
  let recurse = false;
  let vars: Expr[];
  if (!varsIn.length) {
    recurse = true;
    const set = new Map<string, Expr>();
    for (const a of expr.args) for (const m of a instanceof Mul ? a.args : [a]) if (m.freeSymbols().size === 0 && !(m instanceof Special)) set.set(m.key, m);
    vars = [...set.values()];
  } else vars = varsIn.map((v) => sympify(v));
  if (!numbers) vars = vars.filter((v) => !(v instanceof Rational || v instanceof Float));
  vars = orderedExprs(vars);
  for (let vi = 0; vi < vars.length; vi++) {
    const v = vars[vi]!;
    const Fv = factorsOf(v);
    const terms = new Map<string, [Expr, Expr[]]>();
    for (const m of expr instanceof Add ? expr.args : [expr]) {
      const f = factorsOf(m);
      const [q, r] = factorsDiv(f, Fv);
      if (r.size === 0) {
        const changed = [...q].some(([k, [, x]]) => {
          const was = f.get(k)?.[1];
          return was instanceof Rational && was.isInteger && !(x instanceof Rational && x.isInteger);
        });
        if (!changed) {
          if (!terms.has(v.key)) terms.set(v.key, [v, []]);
          terms.get(v.key)![1].push(factorsExpr(q));
          continue;
        }
      }
      if (!terms.has(S.One.key)) terms.set(S.One.key, [S.One, []]);
      terms.get(S.One.key)![1].push(m);
    }
    const args: Expr[] = [];
    let hit = false;
    let uneval = false;
    for (const [k, list] of orderedEntries(terms)) {
      if (k instanceof Rational && k.isOne) {
        args.push(...list);
        continue;
      }
      let w: Expr;
      if (list.length > 1) {
        w = add(...list);
        hit = true;
        if (recurse && w.key !== expr.key) vars.push(w);
      } else w = list[0]!;
      if (numbers && (k instanceof Rational || k instanceof Float) && w instanceof Add) {
        args.push(keepCoeff(k, w, true, true));
        uneval = true;
      } else args.push(mul(k, w));
    }
    if (hit) {
      expr = uneval ? unevaluatedAdd(args) : add(...args);
      if (!(expr instanceof Add)) break;
    }
  }
  return expr;
}

function orderedEntries(terms: Map<string, [Expr, Expr[]]>): [Expr, Expr[]][] {
  const ks = orderedExprs([...terms.values()].map(([k]) => k));
  return ks.map((k) => terms.get(k.key)!);
}

/** SymPy ordered(): node count, then the default sort key. */
function orderedExprs(xs: Expr[]): Expr[] {
  return impl.ordered ? impl.ordered(xs) : xs;
}

/** SymPy _unevaluated_Add: flatten, collect numbers first, keep products unevaluated. */
export function unevaluatedAdd(argsIn: Expr[]): Expr {
  const args = [...argsIn];
  const out: Expr[] = [];
  let co: Expr = S.Zero;
  while (args.length) {
    const a = args.pop()!;
    if (a instanceof Add) args.push(...a.args);
    else if (a instanceof Rational || a instanceof Float) co = add(co, a);
    else out.push(a);
  }
  if (!(co instanceof Rational && co.isZero)) out.unshift(co);
  if (out.length === 0) return S.Zero;
  return out.length === 1 ? out[0]! : new Add(out);
}

const couldNeg = (e: Expr): boolean => impl.couldExtractMinusSign!(e);

/** SymPy signsimp: write sums with a leading minus sign as -(...). */
export function signsimp(exprIn: ExprLike, evaluate = true): Expr {
  const expr = sympify(exprIn);
  if (expr.args.length === 0) return expr;
  let e = subPre(expr);
  if (e.args.length === 0) return e;
  if (e instanceof Add) {
    const rv = add(...e.args.map((a) => signsimp(a)));
    if (!evaluate && rv instanceof Add && couldNeg(rv)) return new Mul([S.NegOne, mul(-1, rv)]);
    return rv;
  }
  if (evaluate) e = reevaluate(e);
  return e;
}

/** Replace every Add that could extract a minus sign by Mul(-1, -a) (unevaluated), bottom-up. */
function subPre(e: Expr): Expr {
  if (e.args.length === 0) return e;
  const args = e.args.map(subPre);
  let out = args.every((a, i) => a === e.args[i]) ? e : rebuildKeep(e, args);
  if (out instanceof Add && couldNeg(out)) {
    const na = mul(-1, out);
    if (!(na instanceof Mul)) out = new Mul([S.NegOne, na]);
  }
  return out;
}

/** Rebuild a node; a Pow keeps an unevaluated exponent. */
function rebuildKeep(e: Expr, args: Expr[]): Expr {
  if (e instanceof Pow) return new Pow(args[0]!, args[1]!);
  return rebuild(e, args);
}

function reevaluate(e: Expr): Expr {
  if (e.args.length === 0) return e;
  const args = e.args.map(reevaluate);
  if (e instanceof Mul) return mul(...args);
  return rebuild(e, args);
}
impl.gcdTermsOf = (terms) => gcdTermsOf(terms);
