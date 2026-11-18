// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14 polys/euclidtools.py (primitive PRS GCD),
// Copyright (c) 2006-2023 SymPy Development Team, BSD-3-Clause; see LICENSE.

import { DomainError, ExactQuotientFailed } from '../core/errors';
import { at, first } from '../core/guard';
import type { Expr } from '../core/nodes';
import { add, mul, pow } from '../core/ops';
import { domainArith, domainNeg, type Domain } from './domains';

/** @internal A sparse polynomial over a field, with native domain coefficients. */
export class FieldPoly {
  readonly terms: readonly (readonly [readonly number[], unknown])[];
  constructor(readonly K: Domain, readonly nvars: number, terms: Iterable<readonly [readonly number[], unknown]>) {
    if (!K.isField) throw new DomainError('polynomial coefficient domain must be a field');
    const data = new Map<string, [readonly number[], unknown]>();
    for (const [m, value] of terms) {
      if (m.length !== nvars || m.some((e) => !Number.isSafeInteger(e) || e < 0)) throw new RangeError('invalid polynomial monomial');
      const key = m.join(','), previous = data.get(key);
      const c = previous === undefined ? K.convert(value) : domainArith(K, 'add', previous[1], value);
      if (K.isZero(c)) data.delete(key);
      else data.set(key, [[...m], c]);
    }
    this.terms = [...data.values()].sort(([a], [b]) => b.reduce((r, e, i) => r || e - at(a, i), 0));
  }
  get isZero(): boolean { return this.terms.length === 0; }
  get zero(): FieldPoly { return new FieldPoly(this.K, this.nvars, []); }
  get one(): FieldPoly { return this.constant(this.K.one); }
  constant(c: unknown): FieldPoly { return this.make([[Array<number>(this.nvars).fill(0), c]]); }
  private make(terms: Iterable<readonly [readonly number[], unknown]>): FieldPoly { return new FieldPoly(this.K, this.nvars, terms); }
  private compatible(g: FieldPoly): void {
    if (this.nvars !== g.nvars || !this.K.equals(g.K)) throw new DomainError('incompatible polynomial rings');
  }
  add(g: FieldPoly): FieldPoly { this.compatible(g); return this.make([...this.terms, ...g.terms]); }
  neg(): FieldPoly { return this.make(this.terms.map(([m, c]) => [m, domainNeg(this.K, c)])); }
  sub(g: FieldPoly): FieldPoly { return this.add(g.neg()); }
  mul(g: FieldPoly): FieldPoly {
    this.compatible(g);
    return this.make(this.terms.flatMap(([m,c]) => g.terms.map(([n,d]) => [m.map((e,i) => e + at(n,i)), domainArith(this.K, 'mul', c, d)] as const)));
  }
  scale(c: unknown): FieldPoly { return this.make(this.terms.map(([m,a]) => [m, domainArith(this.K,'mul',a,c)])); }
  pow(n: number): FieldPoly {
    if (!Number.isSafeInteger(n) || n < 0) throw new RangeError('polynomial power must be a nonnegative integer');
    let p: FieldPoly = this, r = this.one;
    for (let k = n; k; k = Math.floor(k/2)) { if (k % 2) r = r.mul(p); p = p.mul(p); }
    return r;
  }
  monic(): FieldPoly {
    return this.isZero ? this : this.scale(domainArith(this.K,'quo',this.K.one,first(this.terms)[1]));
  }
  /** Multivariate division in lexicographic order, with coefficients divided in K. */
  div(g: FieldPoly): [FieldPoly, FieldPoly] {
    this.compatible(g);
    if (g.isZero) throw new RangeError('polynomial division by zero');
    const [n,d] = first(g.terms);
    let f: FieldPoly = this, q = this.zero, r = this.zero;
    while (!f.isZero) {
      const [m,c] = first(f.terms);
      if (m.every((e,i) => e >= at(n,i))) {
        const t = this.make([[m.map((e,i) => e-at(n,i)), domainArith(this.K,'quo',c,d)]]);
        q = q.add(t); f = f.sub(t.mul(g));
      } else {
        const t = this.make([[m,c]]);
        r = r.add(t); f = f.sub(t);
      }
    }
    return [q,r];
  }
  exquo(g: FieldPoly): FieldPoly {
    const [q,r] = this.div(g);
    if (!r.isZero) throw new ExactQuotientFailed('inexact polynomial quotient');
    return q;
  }
  degree(i = 0): number { return this.isZero ? -Infinity : Math.max(...this.terms.map(([m]) => at(m,i))); }
  /** The coefficient of x_0**degree(f), embedded in the original ring. */
  private leading(): FieldPoly {
    const d = this.degree();
    return this.make(this.terms.filter(([m]) => first(m) === d).map(([m,c]) => [[0,...m.slice(1)],c]));
  }
  /** Pseudo-division with respect to x_0 over K[x_1,...]. */
  pseudoDiv(g: FieldPoly): [FieldPoly, FieldPoly] {
    this.compatible(g);
    if (g.isZero) throw new RangeError('polynomial pseudo-division by zero');
    const d = g.degree(), lc = g.leading();
    let remaining = Math.max(0,this.degree()-d+1), q = this.zero, r: FieldPoly = this;
    while (!r.isZero && r.degree() >= d) {
      const m = Array<number>(this.nvars).fill(0); m[0] = r.degree()-d;
      const t = r.leading().mul(this.make([[m,this.K.one]]));
      q = q.mul(lc).add(t); r = r.mul(lc).sub(t.mul(g)); remaining--;
    }
    const scale = lc.pow(remaining);
    return [q.mul(scale),r.mul(scale)];
  }
  /** Insert x_0 as a new first generator. */
  private inject(): FieldPoly { return new FieldPoly(this.K,this.nvars+1,this.terms.map(([m,c]) => [[0,...m],c])); }
  /** Content and primitive part with respect to x_0. */
  private primitive(): [FieldPoly, FieldPoly] {
    const coefficients = new Map<number, (readonly [readonly number[],unknown])[]>();
    for (const [m,c] of this.terms) {
      const i = first(m), terms = coefficients.get(i) ?? [];
      terms.push([m.slice(1),c]); coefficients.set(i,terms);
    }
    const zero = new FieldPoly(this.K,this.nvars-1,[]);
    const content = [...coefficients.values()].reduce((c,terms) => c.gcd(new FieldPoly(this.K,this.nvars-1,terms)),zero);
    return [content,this.exquo(content.inject())];
  }
  /** Primitive pseudo-remainder sequence, recursively removing polynomial contents. */
  gcd(g: FieldPoly): FieldPoly {
    this.compatible(g);
    if (this.isZero) return g.monic();
    if (g.isZero) return this.monic();
    if (this.nvars === 0) return this.one;
    let f: FieldPoly = this, h = g;
    if (this.nvars === 1) {
      while (!h.isZero) [f,h] = [h,f.div(h)[1]];
      return f.monic();
    }
    const [fc,F] = this.primitive(), [gc,G] = g.primitive();
    const c = fc.gcd(gc);
    [f,h] = [F,G];
    while (!h.isZero) {
      const r = f.pseudoDiv(h)[1];
      [f,h] = [h,r.isZero ? r : r.primitive()[1]];
    }
    return f.primitive()[1].mul(c.inject()).monic();
  }
  diff(i: number): FieldPoly {
    return this.make(this.terms.filter(([m]) => at(m,i)>0).map(([m,c]) => [m.map((e,j) => j===i ? e-1:e), domainArith(this.K,'mul',c,at(m,i))]));
  }
  /** Taylor translation f(x_0+a_0,...), without substituting inside coefficients. */
  shift(values:readonly unknown[]):FieldPoly {
    if(values.length!==this.nvars)throw new RangeError('wrong number of translation values');
    const variables=values.map((c,i)=>{
      const m=Array<number>(this.nvars).fill(0);m[i]=1;
      return this.make([[m,this.K.one]]).add(this.constant(c));
    });
    return this.terms.reduce((sum,[m,c])=>sum.add(m.reduce((term,n,i)=>term.mul(at(variables,i).pow(n)),this.constant(c))),this.zero);
  }
  /** Brown's subresultant PRS, with exact divisions in the coefficient polynomial ring. */
  subresultants(g: FieldPoly): FieldPoly[] {
    this.compatible(g);
    let f:FieldPoly=this,h=g,n=f.degree(),m=h.degree();
    if(n<m){[f,h]=[h,f];[n,m]=[m,n];}
    if(f.isZero)return [];
    if(h.isZero)return [f];
    const result=[f,h];
    let d=n-m,r=f.pseudoDiv(h)[1].scale(d%2===0?-1:1),lc=h.leading(),c=lc.pow(d).neg();
    while(!r.isZero){
      const k=r.degree();result.push(r);
      [f,h,d,m]=[h,r,m-k,k];
      const b=lc.mul(c.pow(d)).neg();
      r=f.pseudoDiv(h)[1].exquo(b);
      lc=h.leading();
      c=d>1?lc.neg().pow(d).exquo(c.pow(d-1)):lc.neg();
    }
    return result;
  }
  asExpr(gens: readonly Expr[]): Expr {
    if (gens.length !== this.nvars) throw new RangeError('wrong number of generators');
    return add(...this.terms.map(([m,c]) => mul(this.K.toSympy(c),...m.map((e,i) => pow(at(gens,i),e)))));
  }
}
