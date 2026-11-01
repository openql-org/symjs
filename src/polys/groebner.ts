// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Groebner bases (Buchberger's algorithm with reduction) over the
 * rationals for lex, grlex and grevlex orders, multivariate division and
 * ideal membership (SymPy groebner / GroebnerBasis).
 */

import { Expr, ExprLike, Rational, S, Sym } from '../core/nodes';
import { add, mul, pow, sympify } from '../core/ops';
import { Poly } from './sympoly';

export type MonomialOrder = 'lex' | 'grlex' | 'grevlex';

type Monom = number[];
/** Sparse polynomial: monomial key -> [monomial, coefficient]. */
type SP = Map<string, [Monom, Rational]>;

const mkey = (m: Monom) => m.join(',');

function cmpMonom(a: Monom, b: Monom, order: MonomialOrder): number {
  const lex = (x: Monom, y: Monom) => {
    for (let i = 0; i < x.length; i++) if (x[i] !== y[i]) return x[i]! - y[i]!;
    return 0;
  };
  if (order === 'lex') return lex(a, b);
  const da = a.reduce((s, v) => s + v, 0);
  const db = b.reduce((s, v) => s + v, 0);
  if (da !== db) return da - db;
  if (order === 'grlex') return lex(a, b);
  // grevlex: the smaller last exponent wins
  for (let i = a.length - 1; i >= 0; i--) if (a[i] !== b[i]) return b[i]! - a[i]!;
  return 0;
}

const radd = (a: Rational, b: Rational) => add(a, b) as Rational;
const rmul = (a: Rational, b: Rational) => mul(a, b) as Rational;
const rdiv = (a: Rational, b: Rational) => mul(a, pow(b, -1)) as Rational;

function lead(p: SP, order: MonomialOrder): [Monom, Rational] | undefined {
  let best: [Monom, Rational] | undefined;
  for (const t of p.values()) if (!best || cmpMonom(t[0], best[0], order) > 0) best = t;
  return best;
}

function addTerm(p: SP, m: Monom, c: Rational): void {
  const k = mkey(m);
  const cur = p.get(k);
  const v = cur ? radd(cur[1], c) : c;
  if (v.isZero) p.delete(k);
  else p.set(k, [m, v]);
}

/** p - c * x^m * q */
function subMul(p: SP, c: Rational, m: Monom, q: SP): SP {
  const out: SP = new Map(p);
  for (const [qm, qc] of q.values()) addTerm(out, qm.map((e, i) => e + m[i]!), rmul(rmul(c, qc), Rational.of(-1n)));
  return out;
}

const divides = (a: Monom, b: Monom) => a.every((e, i) => e <= b[i]!);

/** Full reduction of p by G: [quotients, remainder]. */
function divide(p0: SP, G: SP[], order: MonomialOrder): [SP[], SP] {
  let p: SP = new Map(p0);
  const qs: SP[] = G.map(() => new Map());
  const r: SP = new Map();
  while (p.size) {
    const [lm, lc] = lead(p, order)!;
    let done = false;
    for (let i = 0; i < G.length; i++) {
      const [gm, gc] = lead(G[i]!, order)!;
      if (divides(gm, lm)) {
        const m = lm.map((e, j) => e - gm[j]!);
        const c = rdiv(lc, gc);
        addTerm(qs[i]!, m, c);
        p = subMul(p, c, m, G[i]!);
        done = true;
        break;
      }
    }
    if (!done) {
      addTerm(r, lm, lc);
      p.delete(mkey(lm));
    }
  }
  return [qs, r];
}

function spoly(f: SP, g: SP, order: MonomialOrder): SP {
  const [fm, fc] = lead(f, order)!;
  const [gm, gc] = lead(g, order)!;
  const l = fm.map((e, i) => Math.max(e, gm[i]!));
  let out: SP = new Map();
  for (const [m, c] of f.values()) addTerm(out, m.map((e, i) => e + l[i]! - fm[i]!), rdiv(c, fc));
  out = subMul(out, rdiv(S.One as Rational, gc), l.map((e, i) => e - gm[i]!), g);
  return out;
}

function monic(p: SP, order: MonomialOrder): SP {
  const [, lc] = lead(p, order)!;
  const out: SP = new Map();
  for (const [m, c] of p.values()) out.set(mkey(m), [m, rdiv(c, lc)]);
  return out;
}

function fromExpr(e: Expr, gens: readonly Sym[]): SP {
  const p = Poly.from(e, gens);
  const out: SP = new Map();
  for (const [m, c] of p.terms()) {
    if (!(c instanceof Rational)) throw new Error('groebner: rational coefficients expected');
    if (!c.isZero) out.set(mkey(m), [m, c]);
  }
  return out;
}

function toExpr(p: SP, gens: readonly Sym[]): Expr {
  return add(...[...p.values()].map(([m, c]) => mul(c, ...m.map((k, i) => pow(gens[i]!, k)))));
}

/** Reduced Groebner basis (monic over QQ). */
function buchberger(F: SP[], order: MonomialOrder): SP[] {
  let G = F.filter((f) => f.size).map((f) => monic(f, order));
  const pairs: [number, number][] = [];
  for (let i = 0; i < G.length; i++) for (let j = 0; j < i; j++) pairs.push([j, i]);
  while (pairs.length) {
    const [i, j] = pairs.shift()!;
    const [li] = lead(G[i]!, order)!;
    const [lj] = lead(G[j]!, order)!;
    // Buchberger's first criterion: coprime leading monomials
    if (li.every((e, k) => e === 0 || lj[k] === 0)) continue;
    const [, r] = divide(spoly(G[i]!, G[j]!, order), G, order);
    if (r.size) {
      G.push(monic(r, order));
      for (let k = 0; k < G.length - 1; k++) pairs.push([k, G.length - 1]);
    }
  }
  // minimize
  G = G.filter((g, i) => {
    const [lg] = lead(g, order)!;
    return !G.some((h, j) => j !== i && divides(lead(h, order)![0], lg) && (mkey(lead(h, order)![0]) !== mkey(lg) || j < i));
  });
  // reduce
  G = G.map((g, i) => monic(divide(g, G.filter((_, j) => j !== i), order)[1], order));
  return G.sort((a, b) => cmpMonom(lead(b, order)![0], lead(a, order)![0], order));
}

/** A Groebner basis with its generators, domain and order (SymPy GroebnerBasis). */
export class GroebnerBasis {
  constructor(
    readonly exprs: readonly Expr[],
    readonly gens: readonly Sym[],
    readonly domain: string,
    readonly order: MonomialOrder,
  ) {}
  /** Is f in the ideal? */
  contains(f: ExprLike): boolean {
    return this.reduce(f)[1] instanceof Rational && (this.reduce(f)[1] as Rational).isZero;
  }
  /** Division of f by the basis: [quotients, remainder]. */
  reduce(f: ExprLike): [Expr[], Expr] {
    const G = this.exprs.map((e) => fromExpr(e, this.gens));
    const [qs, r] = divide(fromExpr(sympify(f), this.gens), G, this.order);
    return [qs.map((q) => toExpr(q, this.gens)), toExpr(r, this.gens)];
  }
  toString(): string {
    return `GroebnerBasis([${this.exprs.map((e) => e.toString()).join(', ')}], ${this.gens.map((g) => g.toString()).join(', ')}, domain='${this.domain}', order='${this.order}')`;
  }
}

/** Reduced Groebner basis of polynomials (SymPy groebner). */
export function groebner(F: readonly ExprLike[], gens: readonly Sym[], order: MonomialOrder = 'lex'): GroebnerBasis {
  const polys = F.map((f) => fromExpr(sympify(f), gens));
  const domainQQ = F.some((f) => Poly.from(sympify(f), gens).domain === 'QQ');
  const G = buchberger(polys, order);
  const exprs = G.map((g) => {
    if (domainQQ) return toExpr(g, gens);
    // over ZZ: clear denominators and make primitive
    const p = Poly.from(toExpr(g, gens), gens);
    const [, prim] = p.clearDenoms(true);
    const [, pp] = prim.primitive();
    return pp.asExpr();
  });
  return new GroebnerBasis(exprs, gens, domainQQ ? 'QQ' : 'ZZ', order);
}
