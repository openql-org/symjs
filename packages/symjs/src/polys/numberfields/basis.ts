// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0, polys/numberfields/basis.py, Copyright
// (c) 2006-2023 SymPy Development Team, BSD 3-Clause License (see LICENSE).

/**
 * @file Integral bases of number fields (SymPy
 * sympy.polys.numberfields.basis): the Round Two algorithm (`roundTwo`,
 * Cohen, A Course in Computational Algebraic Number Theory, Alg. 6.1.8)
 * computing the maximal order and the discriminant, and the nilradical of
 * an order modulo a prime (`nilradicalModP`).
 */

import { Rational } from '../../core/nodes';
import { first } from '../../core/guard';
import { asInt, fdiv, type IntLike } from '../../ntheory/intutil';
import { numberFieldHooks, type AlgebraicField } from '../domains/algebraicfield';
import { rat } from '../matrices/domainops';
import { Poly } from '../sympoly';
import type { ModuleElement, Submodule } from './modules';
import { ModuleEndomorphism, ModuleHomomorphism, PowerBasis, dmMul } from './modules';
import { extractFundamentalDiscriminant } from './utilities';

/** Poly f over GF(p). */
const modP = (f: Poly, p: bigint): Poly => Poly.from(f.asExpr(), f.gens, { modulus: p });
/** Poly f (over GF(p)) over ZZ, with the symmetric residues. */
const overZZ = (f: Poly): Poly => Poly.from(f.asExpr(), f.gens, { domain: 'ZZ' });

/**
 * Dedekind's criterion for the polynomial T at the prime p (Cohen,
 * Thm. 6.1.4): [U, m] where U = T/Z mod p for Z = gcd(f, g, h) mod p, and m
 * = deg Z; ZZ[theta] is p-maximal when m = 0.
 */
function applyDedekindCriterion(T: Poly, p: bigint): [Poly, number] {
  const Tbar = modP(T, p);
  const [, fl] = Tbar.factorList();
  let gbar = modP(Poly.from(1, T.gens), p);
  for (const [ti] of fl) gbar = gbar.mul(ti);
  const hbar = Tbar.quo(gbar);
  const g = overZZ(gbar), h = overZZ(hbar);
  const f = g.mul(h).sub(T).quoGround(Rational.of(p));
  let Zbar = modP(f, p);
  for (const b of [gbar, hbar]) Zbar = Zbar.gcd(b);
  return [Tbar.quo(Zbar), Zbar.degree()];
}

/** The smallest power q of p with q >= n. */
function powerAtLeast(p: bigint, n: number): bigint {
  let q = p;
  while (q < BigInt(n)) q *= p;
  return q;
}

/**
 * The nilradical modulo p of an order H (the elements some power of which
 * is in pH), as the kernel of x -> x**q over GF(p) for a power q of p at
 * least the degree (SymPy nilradical_mod_p; Cohen, Lemma 6.1.6).
 */
export function nilradicalModP(H: Submodule, pIn: IntLike, qIn?: IntLike): Submodule {
  const p = asInt(pIn, 'p');
  const q = qIn === undefined ? powerAtLeast(p, H.n) : asInt(qIn, 'q');
  const phi = new ModuleEndomorphism(H, (x) => x.pow(Number(q)));
  return phi.kernel(p);
}

/** The second enlargement of the order H at p (Cohen, Alg. 6.1.8, steps 5-7): [H1, the nilradical]. */
function secondEnlargement(H: Submodule, p: bigint, q: bigint): [Submodule, Submodule] {
  const Ip = nilradicalModP(H, p, q);
  const B = H.parent.submoduleFromMatrix(dmMul(H.matrix, Ip.matrix), H.denom);
  const C = B.add(H.mul(p));
  const E = C.endomorphismRing();
  const phi = new ModuleHomomorphism(H, E, (x: ModuleElement) => E.innerEndomorphism(x));
  const gamma = phi.kernel(p);
  const G = H.parent.submoduleFromMatrix(dmMul(H.matrix, gamma.matrix), H.denom * p);
  return [G.add(H), Ip];
}

/** Options of roundTwo. */
export interface RoundTwoOptions {
  /** A map that receives the nilradical modulo p of the maximal order for a prime p it was computed for (SymPy radicals). */
  radicals?: Map<bigint, Submodule>;
}

/**
 * The maximal order (ring of integers) ZK of the number field of an
 * irreducible polynomial T over ZZ or QQ, or of an algebraic field, and the
 * field's discriminant (SymPy round_two): [ZK, dK]. ZK is a submodule of the
 * power basis of T (made monic over ZZ by scaling its roots).
 *
 * SymPy stores in `radicals` the last nilradical computed under the last
 * prime of the loop, which may be another prime than the one it was
 * computed for (or computed before the order was enlarged at a later
 * prime); here a nilradical is recorded only under its own prime and only
 * when the order was not enlarged after it was computed.
 */
export function roundTwo(TIn: Poly | AlgebraicField, opts: RoundTwoOptions = {}): [Submodule, Rational] {
  const K = TIn instanceof Poly ? undefined : TIn;
  const T0 = TIn instanceof Poly ? TIn : TIn.ext.minpolyOfElement();
  // (a constant is not irreducible: SymPy goes on with it)
  if (T0.gens.length !== 1 || !['ZZ', 'QQ'].includes(T0.domain) || T0.degree() < 1 || !isIrreducible(T0)) {
    throw new RangeError('Round 2 requires an irreducible univariate polynomial over ZZ or QQ.');
  }
  const [T] = T0.makeMonicOverIntegersByScalingRoots();
  const n = T.degree();
  const D = rat(T.discriminant()).p;
  const DModulus = D < 0n ? -D : D;
  // D is 0 or 1 mod 4 (Cohen Sec. 4.4): D = D0*F**2 with D0 1 or a fundamental discriminant
  const [, F] = extractFundamentalDiscriminant(D);
  const Ztheta = new PowerBasis(K ?? T);
  let H = Ztheta.wholeSubmodule();
  let nilrad: [bigint, Submodule] | undefined;
  // SymPy pops the primes from the end of the dict
  for (const [p, e] of [...F].reverse()) {
    const [Ubar, m] = applyDedekindCriterion(T, p);
    if (m === 0) continue;
    // the first enlargement
    const U = Ztheta.elementFromPoly(overZZ(Ubar));
    // (it enlarges the order at p, Cohen Thm. 6.1.4: a nilradical computed before is no longer that of the order)
    H = H.add(H.mul(U.floordiv(p)), { hnfModulus: DModulus });
    nilrad = undefined;
    if (e <= m) continue;
    // second and further enlargements
    const q = powerAtLeast(p, n);
    let [H1, Ip] = secondEnlargement(H, p, q);
    while (!H1.equals(H)) {
      H = H1;
      [H1, Ip] = secondEnlargement(H, p, q);
    }
    nilrad = [p, Ip];
  }
  if (nilrad !== undefined) opts.radicals?.set(...nilrad);
  const ZK = H;
  // properties known to hold for the maximal order
  ZK.presetProperties(true, true);
  const det = rat(ZK.matrix.det()).p;
  const dK = Rational.of(fdiv(D * det ** 2n, ZK.denom ** BigInt(2 * n)));
  return [ZK, dK];
}

/** SymPy Poly.is_irreducible over ZZ or QQ: a single factor of multiplicity 1. */
function isIrreducible(T: Poly): boolean {
  const [, fl] = T.factorList();
  return fl.length === 1 && first(fl)[1] === 1;
}

numberFieldHooks.roundTwo = (K, radicals) => roundTwo(K, { radicals });
