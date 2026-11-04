// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file The Risch algorithm for transcendental elementary integrands,
 * ported from SymPy's `sympy/integrals/risch.py` (Aaron Meurer,
 * following Bronstein, "Symbolic Integration I: Transcendental
 * Functions"): the construction of the differential extension (the tower
 * of exp and log monomials, with the structure theorems deciding whether a
 * new monomial is needed), the integration of hyperexponential and
 * primitive monomials, and risch_integrate, which either returns an
 * elementary antiderivative or proves that none exists
 * (NonElementaryIntegral).
 *
 * Hypertangent (tan) monomials and the nonlinear cases are not supported,
 * as in SymPy, which raises NotImplementedError for them.
 */

import { at, cast as castTo, defined, expectType } from '../core/guard';
import { NotImplementedError } from '../core/errors';
import type { ExprLike } from '../core/nodes';
import { Constant, Dummy, Expr, Fn, Integral, Pow, Rational, S, Sym } from '../core/nodes';
import { Ne, piecewise } from '../core/logic';
import { add, exp, mul, pow, sympify } from '../core/ops';
import { isRationalFunction } from '../core/methods';
import { lcm as ilcm } from '../core/numbers';
import { subs, xreplace } from '../core/traverse';
import { Lambda } from '../core/lambda';
import { compareKeys, sortKey } from '../printing/sortkey';
import { log } from '../functions/elementary/elementary';
import { rewrite } from '../simplify/rewrite';
import { cancel } from '../simplify/rational';
import { rischDEOrNone } from './rde';
import { isDerivK, isLogDerivKTRadical, limitedIntegrate } from './prde';
import type { ExtensionSpec } from './rischbase';
import {
  DiffExtension,
  NonElementaryIntegral,
  asPoly1t,
  decrementLevel,
  derivation,
  hermiteReduce,
  residueReduce,
  residueReduceDerivation,
  residueReduceToBasic,
} from './rischbase';
import { KPoly, exprDiff, fracIn, kCancel } from './rischpoly';

export { NonElementaryIntegral } from './rischbase';

/** The integrator of rational functions used in the base case (set by integrals/integrate). */
export const rischHooks: { integrate?: (f: Expr, x: Sym) => Expr } = {};

const isE = (e: Expr): boolean => e instanceof Constant && e.name === 'E';
const isExp = (e: Expr): e is Pow => e instanceof Pow && isE(e.base);
const isLog = (e: Expr): e is Fn => e instanceof Fn && e.name === 'log';
const TRIG = new Set(['sin', 'cos', 'tan', 'atan', 'asin', 'acos']);

/** Subexpressions satisfying pred, without repetitions. */
function subexprs(e: Expr, pred: (e: Expr) => boolean): Map<string, Expr> {
  const out = new Map<string, Expr>();
  const go = (x: Expr): void => {
    if (pred(x)) out.set(x.key, x);
    x.args.forEach(go);
  };
  go(e);
  return out;
}

const nodes = (e: Expr): number => 1 + e.args.reduce((s, a) => s + nodes(a), 0);

/** SymPy ordered(): by the number of nodes, then by default_sort_key. */
function ordered(es: Iterable<Expr>): Expr[] {
  return [...es].sort((a, b) => nodes(a) - nodes(b) || compareKeys(sortKey(a), sortKey(b)));
}

/**
 * The terms grouped by rational multiples (SymPy integer_powers):
 * [(base, [(term, integer multiple)])], ordered by the base.
 */
export function integerPowers(exprs: readonly Expr[]): [Expr, [Expr, Rational][]][] {
  const terms: [Expr, [Expr, Rational][]][] = [];
  for (const term of exprs) {
    const found = terms.find(([trm]) => cancel(mul(term, pow(trm, -1))) instanceof Rational);
    if (found) found[1].push([term, rat(cancel(mul(term, pow(found[0], -1))))]);
    else terms.push([term, [[term, S.One]]]);
  }
  const out: [Expr, [Expr, Rational][]][] = terms.map(([term, list]) => {
    let den = 1n;
    for (const [, i] of list) den = ilcm(den, i.q);
    const c = Rational.of(den);
    return [mul(term, pow(c, -1)), list.map(([i, j]): [Expr, Rational] => [i, rat(mul(j, c))])];
  });
  return out.sort((a, b) => compareKeys(sortKey(a[0]), sortKey(b[0])));
}

/** A rational multiple (the terms are grouped by rational ratios). */
const rat = (e: Expr): Rational => expectType(e, (v): v is Rational => v instanceof Rational, 'a rational multiple');

/** SymPy update_sets: the old elements still present, plus the new ones satisfying func. */
function updateSets(seq: readonly Expr[], atoms: Map<string, Expr>, func: (e: Expr) => boolean): Expr[] {
  const keep = new Map<string, Expr>();
  for (const s of seq) if (atoms.has(s.key)) keep.set(s.key, s);
  for (const [k, a] of atoms) if (!keep.has(k) && func(a)) keep.set(k, a);
  return [...keep.values()];
}

const isSpec = (f: ExprLike | ExtensionSpec): f is ExtensionSpec => typeof f === 'object' && !(f instanceof Expr) && 'D' in f;

/** Options of the construction of a differential extension. */
export interface DifferentialExtensionOptions {
  /** Which kind of monomial to look for first: 'log' (default) or 'exp'. */
  handleFirst?: 'log' | 'exp';
  /** Name the monomials with Dummy symbols (risch_integrate does). */
  dummy?: boolean;
  /** Rewrite trigonometric functions in exp and log (default: when the integrand contains I). */
  rewriteComplex?: boolean;
}

/**
 * A differential extension of K(x) containing an integrand (SymPy
 * DifferentialExtension): the monomials T = [x, t0, t1, ...], their
 * derivations D, the integrand as fa/fd in the top monomial, and the back
 * substitutions. A manual extension is given as an {@link ExtensionSpec}.
 */
export class DifferentialExtension extends DiffExtension {
  private readonly dummy: boolean;
  private ts: Generator<Sym, never>;

  constructor(f: ExprLike | ExtensionSpec, x?: Sym, opts: DifferentialExtensionOptions = {}) {
    if (!isSpec(f)) {
      const fe = sympify(f);
      const xs = defined(x, 'the integration variable');
      super({ D: [KPoly.one(xs)] });
      this.dummy = opts.dummy ?? false;
      this.ts = this.symbols();
      this.f = fe;
      this.x = xs;
      this.build(opts.handleFirst ?? 'log', opts.rewriteComplex);
    } else {
      super(f);
      this.dummy = false;
      this.ts = this.symbols();
    }
  }

  private *symbols(): Generator<Sym, never> {
    for (let i = 0; ; i++) yield this.dummy ? new Dummy(`t${i}`) : new Sym(`t${i}`);
  }

  /** Start over with the current integrand (SymPy reset). */
  private reset(): void {
    this.t = this.x;
    this.T = [this.x];
    this.D = [KPoly.one(this.x)];
    this.level = -1;
    this.exts = ['none'];
    this.extargs = [S.Zero];
    this.ts = this.symbols();
    this.backsubs = [];
    this.Tfuncs = [];
    this.newf = this.f;
  }

  private hasT(e: Expr): boolean {
    return this.T.some((s) => e.has(s));
  }

  private ratT(e: Expr): boolean {
    return isRationalFunction(e, this.T);
  }

  private build(handleFirst: 'log' | 'exp', rewriteComplexIn: boolean | undefined): void {
    const x = this.x;
    this.reset();
    let expNew: boolean | undefined = true;
    let logNew = true;
    const rewriteComplex = rewriteComplexIn ?? this.f.has(S.I);
    if (rewriteComplex) {
      let g = this.newf;
      for (const name of ['sin', 'cos', 'cot', 'tan', 'sinh', 'cosh', 'coth', 'tanh']) g = rewrite(g, 'exp', { pattern: [name] });
      for (const name of ['asin', 'acos', 'acot', 'atan']) g = rewrite(g, 'log', { pattern: [name] });
      this.newf = cancel(g);
    } else if ([...subexprs(this.f, (e) => e instanceof Fn && TRIG.has(e.name)).values()].some((e) => e.has(x))) {
      throw new NotImplementedError('Trigonometric extensions are not supported (yet!)');
    }
    let exps: Expr[] = [];
    let pows: Expr[] = [];
    let numpows: Expr[] = [];
    let sympows: Expr[] = [];
    let logs: Expr[] = [];
    let symlogs: Expr[] = [];
    for (;;) {
      if (this.ratT(this.newf)) break;
      if (expNew === false && !logNew) {
        throw new NotImplementedError(`Couldn't find an elementary transcendental extension for ${String(this.f)}.  Try using a manual extension with the extension flag.`);
      }
      [exps, pows, numpows, sympows, logNew] = this.rewriteExpsPows(exps, pows, numpows, sympows, logNew);
      [logs, symlogs] = this.rewriteLogs(logs, symlogs);
      if (handleFirst === 'exp' || !logNew) {
        expNew = this.expPart(exps);
        if (expNew === undefined) {
          this.f = this.newf;
          this.reset();
          expNew = true;
          continue;
        }
      }
      if (handleFirst === 'log' || !expNew) logNew = this.logPart(logs);
    }
    [this.fa, this.fd] = fracIn(this.newf, this.t);
    this.autoAttrs();
  }

  private expAtoms(): Map<string, Expr> {
    return subexprs(this.newf, isExp);
  }

  private expFilter = (i: Expr): boolean => isExp(i) && this.ratT(i.exp) && this.hasT(i.exp);

  private rewriteExpsPows(exps0: Expr[], pows0: Expr[], numpows0: Expr[], sympows0: Expr[], logNew0: boolean): [Expr[], Expr[], Expr[], Expr[], boolean] {
    let logNew = logNew0;
    const ratpows = [...subexprs(this.newf, (i) => i instanceof Pow && isExp(i.base) && i.exp instanceof Rational).values()];
    for (const i of ratpows) {
      const p = castTo(i, Pow);
      const repl = exp(mul(p.exp, castTo(p.base, Pow).exp));
      this.backsubs.push([repl, i]);
      this.newf = xreplace(this.newf, [[i, repl]]);
    }
    let exps = updateSets(exps0, this.expAtoms(), this.expFilter);
    const powAtoms = subexprs(this.newf, (i) => i instanceof Pow && !isE(i.base));
    const pows = updateSets(pows0, powAtoms, (i) => i instanceof Pow && this.ratT(i.exp) && this.hasT(i.exp));
    const powMap = new Map(pows.map((p) => [p.key, p]));
    const numpows = updateSets(numpows0, powMap, (i) => !this.hasT(castTo(i, Pow).base));
    const rest = new Map([...powMap].filter(([k]) => !numpows.some((n) => n.key === k)));
    // (the exponents contain a monomial: they are not integers)
    const sympows = updateSets(sympows0, rest, (i) => this.ratT(castTo(i, Pow).base));
    for (const i of ordered(pows)) {
      const p = castTo(i, Pow);
      const old = i;
      const nw = exp(mul(p.exp, log(p.base)));
      let newterm: Expr;
      if (sympows.some((s) => s.key === i.key)) {
        const [basea, based] = fracIn(p.base, this.t);
        const A = isDerivK(basea, based, this);
        if (A === undefined) {
          this.newf = xreplace(this.newf, [[old, nw]]);
          this.backsubs.push([nw, old]);
          logNew = this.logPart([log(p.base)]);
          exps = updateSets(exps, this.expAtoms(), this.expFilter);
          continue;
        }
        const [, u, cst] = A;
        newterm = exp(mul(p.exp, add(log(cst), u)));
        this.newf = xreplace(this.newf, [[i, newterm]]);
      } else if (!numpows.some((s) => s.key === i.key)) {
        continue;
      } else {
        newterm = nw;
      }
      this.backsubs.push([nw, old]);
      this.newf = xreplace(this.newf, [[old, newterm]]);
      exps.push(newterm);
    }
    return [exps, pows, numpows, sympows, logNew];
  }

  private rewriteLogs(logs0: Expr[], symlogs0: Expr[]): [Expr[], Expr[]] {
    const atoms = subexprs(this.newf, isLog);
    const logs = updateSets(logs0, atoms, (i) => this.ratT(at(i.args, 0)) && this.hasT(at(i.args, 0)));
    const symlogs = updateSets(symlogs0, atoms, (i) => {
      const a = at(i.args, 0);
      return this.hasT(i) && a instanceof Pow && !isE(a.base) && this.ratT(a.base) && !(a.exp instanceof Rational && a.exp.isInteger);
    });
    for (const i of ordered(symlogs)) {
      const a = castTo(at(i.args, 0), Pow);
      const lbase = log(a.base);
      logs.push(lbase);
      const nw = mul(a.exp, lbase);
      this.newf = xreplace(this.newf, [[i, nw]]);
      this.backsubs.push([nw, i]);
    }
    const uniq = new Map(logs.map((l) => [l.key, l]));
    return [[...uniq.values()].sort((a, b) => compareKeys(sortKey(a), sortKey(b))), symlogs];
  }

  /** The derivative of arg = arga/argd as an expression. */
  private dArg(arg: Expr): [KPoly, KPoly] {
    const [arga, argd] = fracIn(arg, this.t);
    const darga = argd.mul(derivation(arga, this)).sub(arga.mul(derivation(argd, this)));
    return kCancel(darga, argd.mul(argd));
  }

  private newMonomial(kind: 'exp' | 'log', arg: Expr, D: (t: Sym) => KPoly): Sym {
    const t = this.ts.next().value;
    this.t = t;
    this.T.push(t);
    this.extargs.push(arg);
    this.exts.push(kind);
    this.D.push(D(t));
    const i = this.dummy ? new Dummy('i') : new Sym('i');
    const ai = xreplace(arg, [[this.x, i]]);
    this.Tfuncs.push(Lambda(i, kind === 'exp' ? exp(ai) : log(ai)));
    return t;
  }

  /** Exponential monomials (SymPy _exp_part); undefined asks for a restart. */
  private expPart(exps: readonly Expr[]): boolean | undefined {
    let newExtension = false;
    const ip = integerPowers(exps.map((i) => castTo(i, Pow).exp));
    for (const [arg, others] of ip) {
      others.sort((a, b) => a[1].toNumber() - b[1].toNumber());
      const [arga, argd] = fracIn(arg, this.t);
      const A = isLogDerivKTRadical(arga, argd, this);
      if (A !== undefined) {
        // (SymPy also handles n = -1, but n is a positive common denominator)
        const [ans, , n, cst] = A;
        if (n.key === S.One.key) {
          const prod = mul(...ans.map(([b, e]) => pow(b, e)));
          this.newf = xreplace(this.newf, [[exp(arg), mul(exp(cst), prod)]]);
          this.newf = xreplace(
            this.newf,
            others.map(([e, p]): [Expr, Expr] => [exp(mul(p, e)), mul(exp(mul(cst, p)), prod)]),
          );
          continue;
        }
        if (!(cst instanceof Rational && cst.isZero) || ans.length > 1) {
          const rad = mul(...ans.map(([term, power]) => pow(term, mul(power, pow(n, -1)))));
          this.newf = xreplace(
            this.newf,
            others.map(([e, p]): [Expr, Expr] => [exp(mul(p, e)), mul(exp(mul(cst, p)), rad)]),
          );
          this.newf = xreplace(this.newf, this.backSubstitution());
          return undefined;
        }
        throw new NotImplementedError('Cannot integrate over algebraic extensions.');
      }
      const [da, dd] = this.dArg(arg);
      const darg = mul(da.asExpr(), pow(dd.asExpr(), -1));
      const t = this.newMonomial('exp', arg, (tt) => KPoly.of(mul(darg, tt), tt));
      this.newf = xreplace(
        this.newf,
        others.map(([e, p]): [Expr, Expr] => [exp(e), pow(t, p)]),
      );
      newExtension = true;
    }
    return newExtension;
  }

  /** Logarithmic monomials (SymPy _log_part). */
  private logPart(logs: readonly Expr[]): boolean {
    let newExtension = false;
    for (const arg of ordered(logs.map((i) => at(i.args, 0)))) {
      const [arga, argd] = fracIn(arg, this.t);
      const A = isDerivK(arga, argd, this);
      if (A !== undefined) {
        const [, u, cst] = A;
        this.newf = xreplace(this.newf, [[log(arg), add(log(cst), u)]]);
        continue;
      }
      const [da, dd] = this.dArg(arg);
      const darg = mul(da.asExpr(), pow(dd.asExpr(), -1));
      const t = this.newMonomial('log', arg, (tt) => KPoly.of(cancel(mul(darg, pow(arg, -1))), tt));
      this.newf = xreplace(this.newf, [[log(arg), t]]);
      newExtension = true;
    }
    return newExtension;
  }

  override toString(): string {
    return `DifferentialExtension({fa=${String(this.fa)}, fd=${String(this.fd)}, D=[${this.D.map(String).join(', ')}]})`;
  }
}

/** [q, remainder, b]: p = Dq + remainder with remainder in k when b (SymPy integrate_primitive_polynomial). */
export function integratePrimitivePolynomial(p0: KPoly, DE: DiffExtension): [KPoly, KPoly, boolean] {
  const t = DE.t;
  let q = KPoly.zero(t);
  let p = p0;
  for (;;) {
    if (!p.has(t)) return [q, p, true];
    const [Dta, Dtb] = fracIn(DE.d.asExpr(), at(DE.T, DE.T.length + DE.level - 1));
    // (SymPy catches NonElementaryIntegralException, which limited_integrate does not raise)
    const rv = decrementLevel(DE, () => {
      const [aa, ad] = fracIn(p.LC(), DE.t);
      return limitedIntegrate(aa, ad, [[Dta, Dtb]], DE);
    });
    if (rv === undefined) return [q, p, false];
    const [[ba, bd], c] = rv;
    const m = p.degree;
    const q0 = KPoly.monomial(mul(at(c, 0), Rational.of(1, m + 1)), m + 1, t).add(KPoly.monomial(mul(ba.asExpr(), pow(bd.asExpr(), -1)), m, t));
    p = p.sub(derivation(q0, DE));
    q = q.add(q0);
  }
}

const fracExpr = ([a, d]: readonly [KPoly, KPoly]): Expr => mul(a.asExpr(), pow(d.asExpr(), -1));

/** The derivative of the fraction g as an expression. */
function dFrac([ga, gd]: readonly [KPoly, KPoly], DE: DiffExtension): Expr {
  return mul(gd.mul(derivation(ga, DE)).sub(ga.mul(derivation(gd, DE))).asExpr(), pow(gd.mul(gd).asExpr(), -1));
}

const subsAll = (e: Expr, s: readonly [Expr, Expr][]): Expr => s.reduce((acc, pr) => xreplace(acc, [pr]), e);

/** The integral of a/d in a primitive monomial (SymPy integrate_primitive): [elementary part, remaining integrand, b]. */
export function integratePrimitive(a: KPoly, d: KPoly, DE: DiffExtension, z: Sym = new Dummy('z')): [Expr, Expr, boolean] {
  const s = DE.backSubstitution();
  const [g1, h, r] = hermiteReduce(a, d, DE);
  const [g2, b] = residueReduce(h[0], h[1], DE, z);
  if (!b) {
    const i = cancel(add(fracExpr([a, d]), mul(-1, dFrac(g1, DE)), mul(-1, residueReduceDerivation(g2, DE, z))));
    return [add(subsAll(fracExpr(g1), s), residueReduceToBasic(g2, DE, z)), new NonElementaryIntegral([subsAll(cancel(i), s), DE.x]), b];
  }
  const pe = cancel(add(fracExpr(h), mul(-1, residueReduceDerivation(g2, DE, z)), fracExpr(r)));
  const [q, i, b2] = integratePrimitivePolynomial(KPoly.of(pe, DE.t), DE);
  const ret = add(subsAll(add(fracExpr(g1), q.asExpr()), s), residueReduceToBasic(g2, DE, z));
  if (!b2) return [ret, new NonElementaryIntegral([subsAll(cancel(i.asExpr()), s), DE.x]), b2];
  return [ret, cancel(i.asExpr()), b2];
}

/** The derivative of qa/qd for expressions in t and 1/t. */
function dExprFrac(qa: Expr, qd: Expr, DE: DiffExtension): Expr {
  const D = (e: Expr): Expr => add(...DE.T.map((v, k) => mul(at(DE.D, k).asExpr(), exprDiff(e, v))));
  return mul(add(mul(qd, D(qa)), mul(-1, qa, D(qd))), pow(qd, -2));
}

/** The integral of a Laurent polynomial in a hyperexponential monomial (SymPy integrate_hyperexponential_polynomial). */
export function integrateHyperexponentialPolynomial(pt: KPoly, pz: KPoly, DE: DiffExtension): [Expr, Expr, boolean] {
  const t1 = DE.t;
  const dtt = DE.d.exquo(KPoly.monomial(1, 1, t1));
  let qa: Expr = S.Zero;
  let qd: Expr = S.One;
  let b = true;
  if (pt.isZero && pz.isZero) return [qa, qd, b];
  const lo = pz.isZero ? 0 : pz.degree;
  const hi = pt.isZero ? 0 : pt.degree;
  decrementLevel(DE, () => {
    for (let i = -lo; i <= hi; i++) {
      if (i === 0) continue;
      const a = i < 0 ? pz.nth(-i) : pt.nth(i);
      const [aa, ad] = fracIn(a, DE.t, { cancel: true });
      const [iDta, iDtd] = fracIn(dtt.mulGround(i).asExpr(), DE.t);
      const v = rischDEOrNone(iDta, iDtd, aa, ad, DE);
      if (v === undefined) {
        b = false;
        continue;
      }
      const [va, vd] = fracIn(v, t1, { cancel: true });
      qa = add(mul(qa, vd.asExpr()), mul(va.asExpr(), pow(t1, i), qd));
      qd = mul(qd, vd.asExpr());
    }
  });
  return [qa, qd, b];
}

/** The integral of a/d in a hyperexponential monomial (SymPy integrate_hyperexponential). */
export function integrateHyperexponential(a: KPoly, d: KPoly, DE: DiffExtension, z: Sym = new Dummy('z'), conds: 'piecewise' | 'none' = 'piecewise'): [Expr, Expr, boolean] {
  const s = DE.backSubstitution();
  const [g1, h, r] = hermiteReduce(a, d, DE);
  const [g2, b] = residueReduce(h[0], h[1], DE, z);
  if (!b) {
    const i = cancel(add(fracExpr([a, d]), mul(-1, dFrac(g1, DE)), mul(-1, residueReduceDerivation(g2, DE, z))));
    return [add(subsAll(fracExpr(g1), s), residueReduceToBasic(g2, DE, z)), new NonElementaryIntegral([cancel(subsAll(i, s)), DE.x]), b];
  }
  const p = cancel(add(fracExpr(h), mul(-1, residueReduceDerivation(g2, DE, z)), fracExpr(r)));
  const [pt, pz] = asPoly1t(p, DE.t, z);
  const [qa, qd, b2] = integrateHyperexponentialPolynomial(pt, pz, DE);
  const i0 = pt.nth(0);
  let ret = add(subsAll(fracExpr(g1), s), residueReduceToBasic(g2, DE, z));
  const qas = subsAll(qa, s);
  const qds = subsAll(qd, s);
  if (conds === 'piecewise' && !qds.has(DE.x)) {
    const other = (): Expr => defined(rischHooks.integrate, 'rischHooks.integrate (integrals/integrate)')(subsAll(xreplace(add(p, mul(-1, i0)), [[DE.t, S.One]]), s), DE.x);
    const cond = Ne(qds, 0);
    ret = add(ret, cond === S.true ? mul(qas, pow(qds, -1)) : piecewise([mul(qas, pow(qds, -1)), cond], [other(), true]));
  } else {
    ret = add(ret, mul(qas, pow(qds, -1)));
  }
  if (!b2) {
    const i = add(p, mul(-1, dExprFrac(qa, qd, DE)));
    return [ret, new NonElementaryIntegral([subsAll(cancel(i), s), DE.x]), b2];
  }
  return [ret, i0, b2];
}

/** Options of {@link rischIntegrate}. */
export interface RischIntegrateOptions extends DifferentialExtensionOptions {
  /** A differential extension to use instead of building one. */
  extension?: DifferentialExtension;
  /** Return [elementary part, nonelementary integral (or 0)] instead of their sum. */
  separateIntegral?: boolean;
  conds?: 'piecewise' | 'none';
}

/**
 * The Risch algorithm (SymPy risch_integrate): an elementary antiderivative
 * of f, or an elementary part plus a NonElementaryIntegral, which proves
 * that the rest has no elementary antiderivative. Raises
 * NotImplementedError for integrands outside the supported transcendental
 * cases (trigonometric or algebraic functions).
 */
export function rischIntegrate(f: ExprLike, x: Sym, opts: RischIntegrateOptions & { separateIntegral: true }): [Expr, Expr];
export function rischIntegrate(f: ExprLike, x: Sym, opts?: RischIntegrateOptions): Expr;
export function rischIntegrate(fIn: ExprLike, x: Sym, opts: RischIntegrateOptions = {}): Expr | [Expr, Expr] {
  const f = sympify(fIn);
  const DE = opts.extension ?? new DifferentialExtension(f, x, { handleFirst: opts.handleFirst, dummy: true, rewriteComplex: opts.rewriteComplex });
  let [fa, fd] = [DE.fa, DE.fd];
  let result: Expr = S.Zero;
  for (;;) {
    const kase = DE.case;
    if (!fa.has(DE.t) && !fd.has(DE.t) && kase !== 'base') {
      DE.decrementLevel();
      [fa, fd] = fracIn([fa, fd], DE.t);
      continue;
    }
    [fa, fd] = kCancel(fa.as(DE.t), fd.as(DE.t));
    let ans: Expr;
    let i: Expr;
    let b: boolean;
    if (kase === 'exp') [ans, i, b] = integrateHyperexponential(fa, fd, DE, undefined, opts.conds);
    else if (kase === 'primitive') [ans, i, b] = integratePrimitive(fa, fd, DE);
    else if (kase === 'base') {
      ans = defined(rischHooks.integrate, 'rischHooks.integrate (integrals/integrate)')(fracExpr([fa, fd]), DE.x);
      b = false;
      i = S.Zero;
    } else throw new NotImplementedError('Only exponential and logarithmic extensions are currently supported.');
    result = add(result, ans);
    if (b) {
      DE.decrementLevel();
      [fa, fd] = fracIn(i, DE.t);
      continue;
    }
    result = subs(result, DE.backsubs);
    if (i instanceof Integral) i = new NonElementaryIntegral([subs(i.integrand, DE.backsubs), ...i.args.slice(1)]);
    if (opts.separateIntegral !== true) return add(result, i);
    return [result, i instanceof NonElementaryIntegral ? i : S.Zero];
  }
}
