// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Groebner bases (Buchberger's algorithm with reduction) over the
 * rationals for lex, grlex and grevlex orders, multivariate division and
 * ideal membership (SymPy groebner / GroebnerBasis).
 */

import { DomainError, PolynomialError } from '../core/errors';
import { at, defined } from '../core/guard';
import type { Expr, ExprLike, Sym } from '../core/nodes';
import { Rational, S, impl } from '../core/nodes';
import { add, mul, pow, sympify } from '../core/ops';
import { str } from '../printing/str';
import { Poly, sortGens } from './sympoly';

export type MonomialOrder = 'lex' | 'grlex' | 'grevlex';

type Monom = number[];
/** Sparse polynomial: monomial key -> [monomial, coefficient]. */
type SP = Map<string, [Monom, Rational]>;

const mkey = (m: Monom) => m.join(',');

function cmpMonom(a: Monom, b: Monom, order: MonomialOrder): number {
  // monomials of one polynomial ring have the same length
  const lex = (x: Monom, y: Monom) => {
    for (let i = 0; i < x.length - 1; i++) {
      const d = at(x, i) - at(y, i);
      if (d !== 0) return d;
    }
    return at(x, -1) - at(y, -1);
  };
  if (order === 'lex') return lex(a, b);
  const da = a.reduce((s, v) => s + v, 0);
  const db = b.reduce((s, v) => s + v, 0);
  if (da !== db) return da - db;
  if (order === 'grlex') return lex(a, b);
  // grevlex: the smaller last differing exponent wins
  let i = a.length - 1;
  while (i > 0 && at(a, i) === at(b, i)) i--;
  return at(b, i) - at(a, i);
}

const radd = (a: Rational, b: Rational): Rational => Rational.of(a.p * b.q + b.p * a.q, a.q * b.q);
const rmul = (a: Rational, b: Rational): Rational => Rational.of(a.p * b.p, a.q * b.q);
const rdiv = (a: Rational, b: Rational): Rational => Rational.of(a.p * b.q, a.q * b.p);

function leadOrUndefined(p: SP, order: MonomialOrder): [Monom, Rational] | undefined {
  let best: [Monom, Rational] | undefined;
  for (const t of p.values()) if (!best || cmpMonom(t[0], best[0], order) > 0) best = t;
  return best;
}

/** The leading term of a nonzero polynomial. */
const lead = (p: SP, order: MonomialOrder): [Monom, Rational] => defined(leadOrUndefined(p, order), 'leading term');

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
  for (const [qm, qc] of q.values()) addTerm(out, qm.map((e, i) => e + at(m, i)), rmul(rmul(c, qc), Rational.of(-1n)));
  return out;
}

const divides = (a: Monom, b: Monom) => a.every((e, i) => e <= at(b, i));

/** Full reduction of p by G: [quotients, remainder]. */
function divide(p0: SP, G: SP[], order: MonomialOrder): [SP[], SP] {
  let p: SP = new Map(p0);
  const qs: SP[] = G.map(() => new Map());
  const r: SP = new Map();
  while (p.size) {
    const [lm, lc] = lead(p, order);
    let done = false;
    for (const [i, g] of G.entries()) {
      const [gm, gc] = lead(g, order);
      if (divides(gm, lm)) {
        const m = lm.map((e, j) => e - at(gm, j));
        const c = rdiv(lc, gc);
        addTerm(defined(qs[i]), m, c);
        p = subMul(p, c, m, g);
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
  const [fm, fc] = lead(f, order);
  const [gm, gc] = lead(g, order);
  const l = fm.map((e, i) => Math.max(e, at(gm, i)));
  const shift = l.map((e, i) => e - at(fm, i));
  let out: SP = new Map();
  for (const [m, c] of f.values()) addTerm(out, m.map((e, i) => e + at(shift, i)), rdiv(c, fc));
  out = subMul(out, rdiv(S.One, gc), l.map((e, i) => e - at(gm, i)), g);
  return out;
}

function monic(p: SP, order: MonomialOrder): SP {
  const [, lc] = lead(p, order);
  const out: SP = new Map();
  for (const [m, c] of p.values()) out.set(mkey(m), [m, rdiv(c, lc)]);
  return out;
}

function fromExpr(e: Expr, gens: readonly Expr[]): SP {
  const p = Poly.from(e, gens);
  const out: SP = new Map();
  for (const [m, c] of p.terms()) {
    if (!(c instanceof Rational)) throw new DomainError('groebner: rational coefficients expected');
    if (!c.isZero) out.set(mkey(m), [m, c]);
  }
  return out;
}

function toExpr(p: SP, gens: readonly Expr[]): Expr {
  return add(...[...p.values()].map(([m, c]) => mul(c, ...gens.map((g, i) => pow(g, defined(m[i], 'exponent'))))));
}

/** Reduced Groebner basis (monic over QQ). */
function buchberger(F: SP[], order: MonomialOrder): SP[] {
  let G = F.filter((f) => f.size).map((f) => monic(f, order));
  const pairs: [number, number][] = [];
  for (let i = 0; i < G.length; i++) for (let j = 0; j < i; j++) pairs.push([j, i]);
  while (pairs.length) {
    const [i, j] = defined(pairs.shift());
    const gi = defined(G[i]);
    const gj = defined(G[j]);
    const [li] = lead(gi, order);
    const [lj] = lead(gj, order);
    // Buchberger's first criterion: coprime leading monomials
    if (li.every((e, k) => e === 0 || lj[k] === 0)) continue;
    const [, r] = divide(spoly(gi, gj, order), G, order);
    if (r.size) {
      G.push(monic(r, order));
      for (let k = 0; k < G.length - 1; k++) pairs.push([k, G.length - 1]);
    }
  }
  // minimize
  G = G.filter((g, i) => {
    const [lg] = lead(g, order);
    return !G.some((h, j) => {
      if (j === i) return false;
      const [lh] = lead(h, order);
      return divides(lh, lg) && (mkey(lh) !== mkey(lg) || j < i);
    });
  });
  // reduce
  G = G.map((g, i) => monic(divide(g, G.filter((_, j) => j !== i), order)[1], order));
  return G.sort((a, b) => cmpMonom(lead(b, order)[0], lead(a, order)[0], order));
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
    const r = this.reduce(f)[1];
    return r instanceof Rational && r.isZero;
  }
  /** Division of f by the basis: [quotients, remainder]. */
  reduce(f: ExprLike): [Expr[], Expr] {
    const G = this.exprs.map((e) => fromExpr(e, this.gens));
    const [qs, r] = divide(fromExpr(sympify(f), this.gens), G, this.order);
    return [qs.map((q) => toExpr(q, this.gens)), toExpr(r, this.gens)];
  }
  /**
   * SymPy str: each polynomial printed with its terms in the monomial order
   * of the basis, over the generators in their default (sorted) order.
   */
  toString(): string {
    const gens = sortGens(this.gens);
    const printOrdered = (e: Expr): string => {
      const terms = [...fromExpr(e, gens).values()].sort((a, b) => cmpMonom(b[0], a[0], this.order));
      return terms
        .map(([m, c], i) => {
          const t = str(mul(c, ...gens.map((g, j) => pow(g, defined(m[j], 'exponent')))));
          if (i === 0) return t;
          return t.startsWith('-') ? ` - ${t.slice(1)}` : ` + ${t}`;
        })
        .join('');
    };
    return `GroebnerBasis([${this.exprs.map(printOrdered).join(', ')}], ${this.gens.map((g) => g.toString()).join(', ')}, domain='${this.domain}', order='${this.order}')`;
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

impl.polyReduce = (f, g, gens) => {
  const [qs, r] = divide(fromExpr(f, gens), [fromExpr(g, gens)], 'lex');
  return [toExpr(defined(qs[0], 'quotient'), gens), toExpr(r, gens)];
};

/** SymPy reduced(f, G, *gens): multivariate division of f by G, returning [quotients, remainder]. */
export function reduced(f: ExprLike, G: readonly ExprLike[], gens: readonly Sym[], order: MonomialOrder = 'lex'): [Expr[], Expr] {
  const [qs, r] = divide(
    fromExpr(sympify(f), gens),
    G.map((g) => fromExpr(sympify(g), gens)),
    order,
  );
  return [qs.map((q) => toExpr(q, gens)), toExpr(r, gens)];
}

/** The leading monomial (exponent vector) of a polynomial in the given generators and order. */
export function leadingMonomial(f: ExprLike, gens: readonly Sym[], order: MonomialOrder = 'lex'): number[] {
  const l = leadOrUndefined(fromExpr(sympify(f), gens), order);
  if (!l) throw new PolynomialError('leading monomial of zero');
  return l[0];
}
