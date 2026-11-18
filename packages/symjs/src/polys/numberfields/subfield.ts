// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Based on SymPy 1.14 polys/numberfields/subfield.py, BSD-3-Clause; see LICENSE.
import type { Expr, ExprLike, Sym } from '../../core/nodes';
import { Dummy, ExtensionExpr, Pow, Rational, S } from '../../core/nodes';
import { at, defined, expectType } from '../../core/guard';
import { add, mul, pow, sympify } from '../../core/ops';
import { asCoefficientsDict } from '../../core/methods';
import { freeSymbols, mapBottomUp, xreplace } from '../../core/traverse';
import { NoMatch, isNoMatch, type NoMatchResult } from '../../core/truth';
import { NotImplementedError, DomainError } from '../../core/errors';
import { expand } from '../../simplify/expand';
import { Matrix } from '../../matrices/matrix';
import { rref } from '../../matrices/linalg';
import { AlgebraicNumber, minimalPolynomial } from '../numberfields';
import { Poly, resultant } from '../sympoly';
import { algebraicEnclosure, type AlgebraicBox } from './interval';

type AlgebraicInput = ExprLike | AlgebraicNumber;
const value = (a: AlgebraicInput): Expr => a instanceof AlgebraicNumber ? a.asExpr() : sympify(a);

/**
 * a in the power basis of b by exact rational linear algebra: expanded
 * radical monomials supply the equations, and consistency proves the
 * reconstruction. NoMatch when the expansions do not determine it.
 */
function powerBasisRepresentation(aIn: AlgebraicInput, bIn: AlgebraicInput): Rational[] | NoMatchResult {
  const a = value(aIn), b = value(bIn), t = new Dummy('t');
  if (freeSymbols(a).size || freeSymbols(b).size) throw new DomainError('Number fields must be algebraic over QQ');
  // Validate both inputs, including the rational target case.
  minimalPolynomial(a, t);
  const n = minimalPolynomial(b, t, { polys: true }).degree();
  const reduce = (e: Expr): Expr => expand(mapBottomUp(expand(e),(v) => {
    if (!(v instanceof Pow && v.exp instanceof Rational && v.exp.isInteger && v.exp.isPositive && v.base instanceof ExtensionExpr && v.base.name === 'CRootOf')) return v;
    const polynomial = at(v.base.args,0), gen = new Dummy('root');
    const symbols = [...freeSymbols(polynomial)];
    const f = Poly.from(xreplace(polynomial,symbols.map((x)=>[x,gen])),[gen]);
    return xreplace(Poly.from(pow(gen,v.exp),[gen]).rem(f).asExpr(),[[gen,v.base]]);
  }));
  const basis = Array.from({ length: n }, (_, i) => asCoefficientsDict(reduce(pow(b, i))));
  const target = asCoefficientsDict(reduce(a));
  const monomials = new Map([...target, ...basis.flatMap((d) => [...d])].map(([m]) => [m.key, m]));
  const rows = [...monomials.values()].map((m) => [...basis.map((d) => d.get(m) ?? S.Zero), target.get(m) ?? S.Zero]);
  const [reduced, pivots] = rref(Matrix.of(rows));
  if (pivots.includes(n) || pivots.length !== n) return NoMatch;
  const coeffs = pivots.map((_, i) => expectType(reduced.get(i, n), (c): c is Rational => c instanceof Rational, 'rational coefficient'));
  // Every expanded monomial is a row of the exact linear system. Consistency
  // already proves reconstruction; a second zero check cannot fail here.
  while (coeffs.length > 1 && at(coeffs, coeffs.length - 1).equals(0)) coeffs.pop();
  return coeffs.reverse();
}

/**
 * An isomorphism of Q(a) onto a subfield of Q(b): the coefficients, in
 * falling powers of b, of an element of Q(b) to which a may be mapped, or
 * NoMatch when Q(a) is not isomorphic to a subfield of Q(b). When the radical
 * expansions of a and b determine it, the element is a itself; otherwise it
 * is a root of the minimal polynomial of a in Q(b), found by factoring that
 * polynomial over Q(b) (Trager's square-free norm) and checked exactly.
 */
export function fieldIsomorphism(aIn: AlgebraicInput, bIn: AlgebraicInput): Rational[] | NoMatchResult {
  const direct = powerBasisRepresentation(aIn, bIn);
  return isNoMatch(direct) ? rootInField(value(aIn), value(bIn)) : direct;
}

/** Arithmetic in Q(b) = Q[y]/(g), on polynomials over it in falling powers of x. */
class FieldPolynomials {
  constructor(readonly g: Poly) {}
  reduce(c: Poly): Poly { return c.rem(this.g); }
  strip(f: readonly Poly[]): Poly[] {
    const i = f.findIndex((c) => !c.isZero);
    return i < 0 ? [] : f.slice(i);
  }
  /** The remainder of f by the nonzero g. */
  rem(fIn: readonly Poly[], h: readonly Poly[]): Poly[] {
    let f = this.strip(fIn);
    const inverse = at(h, 0).invert(this.g);
    while (f.length >= h.length) {
      const q = this.reduce(at(f, 0).mul(inverse));
      f = this.strip(f.map((c, i) => (i < h.length ? this.reduce(c.sub(q.mul(at(h, i)))) : c)));
    }
    return f;
  }
  gcd(fIn: readonly Poly[], hIn: readonly Poly[]): Poly[] {
    let [f, h] = [this.strip(fIn), this.strip(hIn)];
    while (h.length) [f, h] = [h, this.rem(f, h)];
    const inverse = at(f, 0).invert(this.g);
    return f.map((c) => this.reduce(c.mul(inverse)));
  }
}

/**
 * A root of the minimal polynomial f of a in Q(b), as coefficients in falling
 * powers of b: the linear factors of f over Q(b) are the gcds with f(x - k b)
 * of the degree-m irreducible factors of its square-free norm.
 */
function rootInField(a: Expr, b: Expr): Rational[] | NoMatchResult {
  const x = new Dummy('x'), y = new Dummy('y');
  const f = minimalPolynomial(a, x, { polys: true });
  const g = minimalPolynomial(b, y, { polys: true });
  const n = f.degree(), m = g.degree();
  if (m % n !== 0) return NoMatch;
  const K = new FieldPolynomials(g);
  for (let k = 1; ; k++) {
    const shifted = expand(xreplace(f.asExpr(), [[x, add(x, mul(-k, y))]]));
    const norm = Poly.from(resultant(g.asExpr(), shifted, y), [x]);
    if (!norm.isSqf) continue;
    const F = Poly.from(shifted, [x]).allCoeffs().map((c) => K.reduce(Poly.from(c, [y])));
    const candidates: Rational[][] = [];
    for (const [h] of norm.factorList()[1]) {
      if (h.degree() !== m) continue;
      // The linear factor x - c(b) of f(x - k b): c(b) - k b is a root of f.
      const [, c0] = K.gcd(F, h.allCoeffs().map((c) => Poly.from(c, [y])));
      const root = K.reduce(defined(c0).neg().sub(Poly.from(mul(k, y), [y])));
      candidates.push(root.allCoeffs().map((c) => expectType(c, (e): e is Rational => e instanceof Rational, 'rational coefficient')));
    }
    if (!candidates.length) return NoMatch;
    // A discriminant bound separates distinct roots of the primitive integer polynomial.
    const coeffs = f.clearDenoms(true)[1].allCoeffs().map((c)=>expectType(c,(v):v is Rational=>v instanceof Rational,'integer coefficient').p);
    const H = coeffs.reduce((h,c)=>{const a=c<0n?-c:c;return a>h?a:h;},1n);
    const separation = Rational.of(1n,H**BigInt(n-1)*(2n+2n*H)**BigInt(n*(n-1)/2));
    const cmp=(x:Rational,y:Rational):boolean=>x.p*y.q<y.p*x.q;
    const overlaps=(u:AlgebraicBox,v:AlgebraicBox):boolean=>u.every(([a,b],i)=>!cmp(b,at(v,i)[0])&&!cmp(at(v,i)[1],a));
    const width=(u:AlgebraicBox):Rational=>u.reduce((a,[lo,hi])=>Rational.of(a.p*lo.q*hi.q+(hi.p*lo.q-lo.p*hi.q)*a.q,a.q*lo.q*hi.q),Rational.of(0));
    for (let bits=32;;bits*=2) {
      try {
      const u=algebraicEnclosure(a,bits);
      let possible=false;
      for(const cs of candidates){
        const expression=add(...cs.map((c,i)=>mul(c,pow(b,cs.length-1-i))));
        const v=algebraicEnclosure(expression,bits);
        if(!overlaps(u,v))continue;
        possible=true;
        const w=width(u),z=width(v),total=Rational.of(w.p*z.q+z.p*w.q,w.q*z.q);
        if(cmp(total,separation))return cs;
      }
      if(!possible)return NoMatch;
      } catch (error) { if (!(error instanceof RangeError)) throw error; }
    }
  }
}

function representation(a: AlgebraicInput,b: AlgebraicInput): Rational[] | NoMatchResult {
  const direct=powerBasisRepresentation(a,b);
  return isNoMatch(direct)?rootInField(value(a),value(b)):direct;
}

export interface PrimitiveElementOptions { ex?: boolean; maxCandidates?: number; }
export function primitiveElement(extension: readonly AlgebraicInput[], x?: Sym, options?: PrimitiveElementOptions & { ex?: false }): [Expr, number[]];
export function primitiveElement(extension: readonly AlgebraicInput[], x: Sym | undefined, options: PrimitiveElementOptions & { ex: true }): [Expr, number[], Rational[][]];
export function primitiveElement(extension: readonly AlgebraicInput[], x: Sym | undefined, options: PrimitiveElementOptions): [Expr, number[]] | [Expr, number[], Rational[][]];
/** Primitive elements by an unbounded exact search, with certified generator embeddings. */
export function primitiveElement(extension: readonly AlgebraicInput[], x: Sym = new Dummy('x'), options: PrimitiveElementOptions = {}): [Expr, number[]] | [Expr, number[], Rational[][]] {
  if (!extension.length) throw new RangeError('At least one extension is required');
  const maxCandidates = options.maxCandidates ?? Infinity;
  if (options.maxCandidates !== undefined && (!Number.isInteger(maxCandidates) || maxCandidates < 1)) throw new RangeError('maxCandidates must be a positive integer');
  const generators = extension.map(value), coeffs = generators.map(() => 0);
  let theta: Expr = S.Zero;
  let representations: Rational[][] = [];
  for (const [i, generator] of generators.entries()) {
    const existing = representation(generator, theta);
    if (!isNoMatch(existing)) { representations.push(existing); continue; }
    let found = false;
    for (let k = 1; k <= maxCandidates; k++) {
      const candidate = add(theta, mul(k, generator));
      const reps = generators.slice(0, i + 1).map((g) => representation(g, candidate));
      if (reps.every((r): r is Rational[] => !isNoMatch(r))) {
        theta = candidate; coeffs[i] = k; representations = reps; found = true; break;
      }
    }
    if (!found) throw new NotImplementedError(`primitiveElement: no primitive element found within ${maxCandidates} candidates`);
  }
  const polynomial = minimalPolynomial(theta, x);
  if (!options.ex) return [polynomial, coeffs];
  return [polynomial, coeffs, representations];
}

/** Embed one or several algebraic values in an explicitly represented number field. */
export function toNumberField(extension: AlgebraicInput | readonly AlgebraicInput[], theta?: AlgebraicInput): AlgebraicNumber {
  const generators = Array.isArray(extension) ? extension : [extension];
  if (!generators.length) throw new RangeError('At least one extension is required');
  const values = generators.map(value);
  const [, coefficients] = primitiveElement(values);
  const root = values.length === 1 ? at(values, 0) : add(...values.map((v, i) => mul(at(coefficients, i), v)));
  if (theta === undefined) return new AlgebraicNumber(root);
  const target = value(theta), embedding = representation(root, target);
  if (isNoMatch(embedding)) throw new NotImplementedError('toNumberField: exact embedding was not found');
  return new AlgebraicNumber(target, embedding);
}
