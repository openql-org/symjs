// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14 polys/numberfields/galoisgroups.py, BSD-3-Clause; see LICENSE.

import { cast, defined, expectType } from '../../core/guard';
import { Dummy, Rational, Sym } from '../../core/nodes';
import type { ExprLike } from '../../core/nodes';
import { add, mul, pow, sub } from '../../core/ops';
import { xreplace } from '../../core/traverse';
import { isqrt } from '../../core/numberutils';
import { S1TransitiveSubgroups, S2TransitiveSubgroups, S3TransitiveSubgroups, S4TransitiveSubgroups, S5TransitiveSubgroups, S6TransitiveSubgroups } from '../../combinatorics/galois';
import type { TransitiveSubgroup } from '../../combinatorics/galois';
import type { PermutationGroupNode } from '../../combinatorics/permgroups';
import { numberFieldHooks } from '../domains/algebraicfield';
import { Poly, resultant } from '../sympoly';
import { getResolventByLookup } from './galoisresolvents';
import { coeffSearch } from './utilities';

export interface GaloisGroupOptions { byName?: boolean; maxTries?: number; randomize?: boolean }
export type GaloisGroupResult = [TransitiveSubgroup | PermutationGroupNode, boolean];
export class MaxTriesException extends RangeError {}

/** Whether the discriminant is a rational square. */
export function hasSquareDisc(polynomial: Poly): boolean {
  const d = expectType(polynomial.discriminant(), (e): e is Rational => e instanceof Rational, 'rational discriminant');
  return d.p >= 0n && isqrt(d.p) ** 2n === d.p && isqrt(d.q) ** 2n === d.q;
}
const squarefree = (p: Poly): boolean => p.gcd(p.diff(cast(p.gen, Sym))).degree() === 0;
const fromCoefficients = (c: readonly Rational[], x: Sym): Poly => Poly.from(add(...c.map((a, i) => mul(a, pow(x, c.length - i - 1)))), [x]);

/** A deterministic Tschirnhausen transformation avoiding previous defining polynomials. @internal */
export function tschirnhausenTransformation(T: Poly, maxTries = 30, history: Set<string> = new Set()): [Poly, Poly] {
  const x = cast(T.gen, Sym), y = new Dummy('X');
  history.add(T.asExpr().key);
  const coefficients = coeffSearch(T.degree() - 1, 1);
  for (let attempt = 0; attempt < maxTries; attempt++) {
    const c = coefficients.next().value;
    const A = Poly.from(add(pow(x, T.degree() - 1), ...c.map((a, i) => mul(a, pow(x, c.length - i - 1)))), [x]);
    const U = Poly.from(resultant(T.asExpr(), sub(y, A.asExpr()), x), [y]);
    const sameVariable = xreplace(U.asExpr(), [[y, x]]).key;
    if (!history.has(sameVariable) && squarefree(U)) return [A, Poly.from(xreplace(U.asExpr(), [[y, x]]), [x])];
  }
  throw new MaxTriesException('no separating Tschirnhausen transformation found');
}

function resolvent(T: Poly, number: number, maxTries: number): Poly {
  let polynomial = T;
  const history = new Set<string>();
  for (let attempt = 0; attempt < maxTries; attempt++) {
    const R = fromCoefficients(getResolventByLookup(polynomial, number), cast(polynomial.gen, Sym));
    if (squarefree(R)) return R;
    polynomial = tschirnhausenTransformation(polynomial, maxTries, history)[1];
  }
  throw new MaxTriesException('no square-free resolvent found');
}
const factors = (p: Poly): Poly[] => p.factorList()[1].flatMap(([f, m]) => Array.from({ length: m }, () => f));
const signature = (fs: readonly Poly[]): string => fs.map((f) => f.degree()).sort((a, b) => a - b).join(',');

function quinticCyclic(T: Poly, maxTries: number): boolean {
  const x = cast(T.gen, Sym), a = new Dummy('a');
  const modulus = xreplace(T.asExpr(), [[x, a]]);
  // Trager's square-free norm separates the factors over Q(a). The quintic
  // splits into five linear factors there precisely when the group is C5.
  for (let shift = 1; shift <= maxTries; shift++) {
    const shifted = xreplace(T.asExpr(), [[x, sub(x, mul(shift, a))]]);
    const norm = Poly.from(resultant(modulus, shifted, a), [x]);
    if (squarefree(norm)) return factors(norm).length === 5;
  }
  throw new MaxTriesException('no square-free quintic norm found');
}

function classify(T: Poly, maxTries: number): TransitiveSubgroup {
  const n = T.degree();
  if (n === 1) return S1TransitiveSubgroups.S1;
  if (n === 2) return S2TransitiveSubgroups.S2;
  const even = hasSquareDisc(T);
  if (n === 3) return even ? S3TransitiveSubgroups.A3 : S3TransitiveSubgroups.S3;
  if (n === 6 && T.isCyclotomic) return S6TransitiveSubgroups.C6;
  const fs = factors(resolvent(T, n === 4 ? 0 : 1, maxTries));
  const shape = signature(fs);
  if (n === 4) {
    const names: Record<string, TransitiveSubgroup> = { '6': even ? S4TransitiveSubgroups.A4 : S4TransitiveSubgroups.S4, '1,1,4': S4TransitiveSubgroups.C4, '2,2,2': S4TransitiveSubgroups.V, '2,4': S4TransitiveSubgroups.D4 };
    return defined(names[shape], 'quartic resolvent factorization');
  }
  if (n === 5) {
    if (shape === '6') return even ? S5TransitiveSubgroups.A5 : S5TransitiveSubgroups.S5;
    if (!even) return S5TransitiveSubgroups.M20;
    return quinticCyclic(T, maxTries) ? S5TransitiveSubgroups.C5 : S5TransitiveSubgroups.D5;
  }
  const G = S6TransitiveSubgroups;
  const named: Record<string, TransitiveSubgroup> = {
    '1,1,4': even ? G.A4 : G.S4m, '1,5': even ? G.PSL2F5 : G.PGL2F5, '1,1,1,3': G.S3,
  };
  if (named[shape] !== undefined) return named[shape];
  if (shape === '1,2,3') return hasSquareDisc(defined(fs.find((f) => f.degree() === 3))) ? G.C6 : G.D6;
  if (shape === '3,3') return fs.some(hasSquareDisc) ? G.G18 : G.G36m;
  if (shape === '2,4') return even ? G.S4p : hasSquareDisc(defined(fs.find((f) => f.degree() === 4))) ? G.A4xC2 : G.S4xC2;
  const second = resolvent(T, 2, maxTries);
  return factors(second).length === 1 ? (even ? G.A6 : G.S6) : (even ? G.G36p : G.G72);
}

/** Galois group of an irreducible rational polynomial of degree at most six. */
export function galoisGroup(f: Poly | ExprLike, x?: Sym | GaloisGroupOptions, options: GaloisGroupOptions = {}): GaloisGroupResult {
  const opts = x !== undefined && !(x instanceof Sym) ? x : options;
  const p = f instanceof Poly ? f : Poly.from(f, x instanceof Sym ? [x] : undefined);
  if (p.gens.length !== 1 || !['ZZ', 'QQ'].includes(p.domain) || !p.isIrreducible) throw new RangeError('an irreducible polynomial over QQ is required');
  if (p.degree() < 1 || p.degree() > 6) throw new RangeError('Galois groups require degree one through six');
  const maxTries = opts.maxTries ?? 30;
  const [T] = p.makeMonicOverIntegersByScalingRoots();
  const name = classify(T, maxTries);
  return [opts.byName === true ? name : name.getPermGroup(), hasSquareDisc(T)];
}

numberFieldHooks.galoisGroup = (K, options) => galoisGroup(K.ext.minpoly(), options);
