// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (sympy/polys/agca/extensions.py), Copyright (c)
// 2006-2023 SymPy Development Team, BSD 3-Clause License.

/**
 * @file SymPy sympy.polys.agca.extensions: finite (monogenic) extensions
 * K[x]/(f) of a domain K by a polynomial f, and their elements.
 */

import { ExactQuotientFailed, NotImplementedError, NotInvertible } from '../../core/errors';
import { at, cast } from '../../core/guard';
import type { Expr, ExprLike } from '../../core/nodes';
import { Rational, Sym } from '../../core/nodes';
import { sympify } from '../../core/ops';
import { str } from '../../printing/str';
import type { Domain, GlobalPolynomialRing } from '../domains';
import { CoercionFailed } from '../domains';
import { GeneratorsError } from '../polyerrors';
import { freeSymbols } from '../../core/traverse';
import { preprocessDomain } from '../polyoptions';
import { Poly } from '../sympoly';

/** SymPy domain.is_unit of a coefficient: nonzero in a field, +-1 in a ring. */
function isGroundUnit(K: Domain, c: Expr): boolean {
  if (K.isField) return !(c instanceof Rational && c.isZero);
  return c instanceof Rational && c.q === 1n && (c.p === 1n || c.p === -1n);
}

/** SymPy ExtensionElement (ExtElem): an element of a finite extension, a polynomial reduced modulo the modulus. */
export class ExtensionElement {
  constructor(
    readonly rep: Poly,
    readonly ext: FiniteExtension,
  ) {}

  /** SymPy parent(): the extension. */
  parent(): FiniteExtension {
    return this.ext;
  }

  /** SymPy as_expr(). */
  asExpr(): Expr {
    return this.ext.toSympy(this);
  }

  /** SymPy bool(f): whether the element is nonzero. */
  get isZero(): boolean {
    return this.rep.isZero;
  }

  /** SymPy -f. */
  neg(): ExtensionElement {
    return new ExtensionElement(this.rep.neg(), this.ext);
  }

  #rep(g: ExtensionElement | ExprLike): Poly {
    if (g instanceof ExtensionElement) {
      if (!g.ext.equals(this.ext)) throw new CoercionFailed(`${String(g)} is not an element of ${String(this.ext)}`);
      return g.rep;
    }
    return this.ext.convert(g).rep;
  }

  /** SymPy f + g. */
  add(g: ExtensionElement | ExprLike): ExtensionElement {
    return new ExtensionElement(this.rep.add(this.#rep(g)), this.ext);
  }

  /** SymPy f - g. */
  sub(g: ExtensionElement | ExprLike): ExtensionElement {
    return new ExtensionElement(this.rep.sub(this.#rep(g)), this.ext);
  }

  /** SymPy f * g. */
  mul(g: ExtensionElement | ExprLike): ExtensionElement {
    return new ExtensionElement(this.rep.mul(this.#rep(g)).rem(this.ext.mod), this.ext);
  }

  /** SymPy _divcheck: whether the element can be inverted (division by zero raises NotInvertible). */
  #divcheck(): void {
    if (this.isZero) throw new NotInvertible('Zero divisor');
    if (this.ext.isField) return;
    if (!(this.isGround && isGroundUnit(this.ext.domain, this.rep.LC()))) {
      throw new NotImplementedError(`Can not invert ${String(this)} in ${String(this.ext)}. Only division by invertible constants is implemented.`);
    }
  }

  /** SymPy inverse(). */
  inverse(): ExtensionElement {
    this.#divcheck();
    const inv = this.ext.isField ? this.rep.invert(this.ext.mod) : this.ext.one.rep.exquo(this.rep);
    return new ExtensionElement(inv, this.ext);
  }

  /** SymPy f / g (and f // g). */
  div(g: ExtensionElement | ExprLike): ExtensionElement {
    const d = new ExtensionElement(this.#rep(g), this.ext);
    if (d.isZero) throw new RangeError(`${String(this)} / ${String(d)}`);
    return this.mul(d.inverse());
  }

  /** SymPy f % g: zero for an invertible g. */
  mod(g: ExtensionElement | ExprLike): ExtensionElement {
    const d = new ExtensionElement(this.#rep(g), this.ext);
    if (d.isZero) throw new RangeError(`${String(this)} % ${String(d)}`);
    d.#divcheck();
    return this.ext.zero;
  }

  /** SymPy f**n (a negative n through the inverse). */
  pow(nIn: number | bigint): ExtensionElement {
    let n = BigInt(nIn);
    let f: ExtensionElement = this;
    if (n < 0n) {
      try {
        f = this.inverse();
      } catch (e) {
        if (e instanceof NotImplementedError) throw new RangeError('negative powers are not defined');
        throw e;
      }
      n = -n;
    }
    let b = f.rep;
    let r = this.ext.one.rep;
    const m = this.ext.mod;
    while (n > 0n) {
      if (n % 2n) r = r.mul(b).rem(m);
      b = b.mul(b).rem(m);
      n /= 2n;
    }
    return new ExtensionElement(r, this.ext);
  }

  /** SymPy f == g. */
  equals(g: unknown): boolean {
    return g instanceof ExtensionElement && g.ext.equals(this.ext) && g.rep.equals(this.rep);
  }

  /** SymPy is_ground. */
  get isGround(): boolean {
    return this.rep.degree() <= 0;
  }

  /** SymPy to_ground(): the constant of a ground element. */
  toGround(): Expr {
    if (!this.isGround) throw new RangeError(`${String(this)} is not a constant`);
    return this.rep.LC();
  }

  toString(): string {
    return str(this.asExpr());
  }
}

/**
 * SymPy FiniteExtension(mod) (MonogenicFiniteExtension): the ring K[x]/(f)
 * of a univariate polynomial f over K (made monic over a field).
 *
 * @example
 * const R = new FiniteExtension(Poly.from(parse('x**2 - 2')));
 * String(R.new(parse('1 + x')).mul(parse('3 - 2*x'))) // 'x - 1'
 */
export class FiniteExtension {
  readonly isFiniteExtension = true;
  readonly isField: boolean;
  /** SymPy rank: the degree of the modulus. */
  readonly rank: number;
  /** SymPy modulus: the (monic) polynomial. */
  readonly modulus: Poly;
  /** SymPy mod: the modulus (its representation). */
  readonly mod: Poly;
  /** SymPy domain: the coefficient domain. */
  readonly domain: Domain;
  /** SymPy ring: K[x]. */
  readonly ring: GlobalPolynomialRing;
  /** SymPy symbol: the generator x. */
  readonly symbol: Sym;
  readonly zero: ExtensionElement;
  readonly one: ExtensionElement;
  readonly generator: ExtensionElement;
  readonly basis: readonly ExtensionElement[];

  constructor(modIn: Poly) {
    if (!(modIn instanceof Poly) || modIn.gens.length !== 1) throw new TypeError('modulus must be a univariate Poly');
    // SymPy mod.monic(auto=False): monic over a field, the polynomial itself over a ring when its leading coefficient is not 1
    const domain = preprocessDomain(modIn.domain);
    // SymPy mod.monic(auto=False): over a ring the leading coefficient must be a unit
    if (!isGroundUnit(domain, modIn.LC())) throw new ExactQuotientFailed(`${str(modIn.LC())} does not divide 1 in ${modIn.domain}`);
    const mod = modIn.monic();
    this.rank = mod.degree();
    this.modulus = mod;
    this.mod = mod;
    this.domain = domain;
    this.isField = domain.isField;
    this.symbol = cast(mod.gens[0], Sym, 'generator');
    this.ring = domain.oldPolyRing(this.symbol);
    this.zero = this.convert(0);
    this.one = this.convert(1);
    this.generator = this.convert(this.symbol);
    this.basis = Array.from({ length: this.rank }, (_, i) => this.convert(this.symbol.pow(i)));
  }

  #poly(e: Expr): Poly {
    return Poly.from(e, [this.symbol], { domain: this.modulus.domain });
  }

  /** SymPy K(arg) / new(arg): the element of a polynomial or an expression. */
  new(arg: ExtensionElement | Poly | ExprLike): ExtensionElement {
    return this.convert(arg);
  }

  /** SymPy convert(f): the element of f (an expression, a Poly or an element). */
  convert(f: ExtensionElement | Poly | ExprLike): ExtensionElement {
    if (f instanceof ExtensionElement) {
      if (!f.ext.equals(this)) throw new CoercionFailed(`${String(f)} is not an element of ${String(this)}`);
      return f;
    }
    const e = f instanceof Poly ? f.asExpr() : sympify(f);
    if ([...freeSymbols(e)].some((a) => a.key !== this.symbol.key && !this.domain.symbols.some((s) => s.key === a.key))) {
      throw new CoercionFailed(`cannot convert ${str(e)} to ${String(this)}`);
    }
    return new ExtensionElement(this.#poly(e).rem(this.mod), this);
  }

  equals(other: unknown): boolean {
    return other instanceof FiniteExtension && other.modulus.equals(this.modulus) && other.modulus.domain === this.modulus.domain;
  }

  toString(): string {
    return `${String(this.ring)}/(${str(this.modulus.asExpr())})`;
  }

  /** SymPy has_CharacteristicZero. */
  get hasCharacteristicZero(): boolean {
    return this.characteristic() === 0n;
  }

  /** SymPy characteristic(). */
  characteristic(): bigint {
    const m = /^GF\((\d+)\)$/.exec(this.modulus.domain);
    return m ? BigInt(at(m, 1)) : 0n;
  }

  /** SymPy to_sympy(f). */
  toSympy(f: unknown): Expr {
    return cast(f, ExtensionElement, 'extension element').rep.asExpr();
  }

  /** SymPy from_sympy(f). */
  fromSympy(f: ExprLike): Expr {
    return this.toSympy(this.convert(f));
  }

  /** SymPy set_domain(K): the extension by the modulus over another domain. */
  setDomain(K: Domain | string): FiniteExtension {
    return new FiniteExtension(Poly.from(this.modulus.asExpr(), [this.symbol], { domain: String(K) }));
  }

  /** SymPy drop(*symbols): the extension over the domain without the symbols. */
  drop(...symbols: Expr[]): FiniteExtension {
    if (symbols.some((s) => s.key === this.symbol.key)) throw new GeneratorsError('Can not drop generator from FiniteExtension');
    const rest = this.domain.symbols.filter((s) => !symbols.some((t) => t.key === s.key));
    const base = this.domain.dom;
    const K = rest.length === 0 ? base : this.domain.isField ? base.fracField(...rest) : base.polyRing(...rest);
    return this.setDomain(K);
  }

  /** SymPy quo(f, g) = exquo(f, g). */
  quo(f: ExtensionElement, g: ExtensionElement): ExtensionElement {
    return this.exquo(f, g);
  }

  /** SymPy exquo(f, g): the exact quotient of the representatives, reduced. */
  exquo(f: ExtensionElement, g: ExtensionElement): ExtensionElement {
    return new ExtensionElement(f.rep.exquo(g.rep).rem(this.mod), this);
  }

  /** SymPy is_negative(a): false. */
  isNegative(_a: ExtensionElement): boolean {
    return false;
  }

  /** SymPy is_unit(a): a nonzero element of a field, or an invertible constant ('unknown' for other elements of a ring). */
  isUnit(a: ExtensionElement): boolean | 'unknown' {
    if (this.isField) return !a.isZero;
    // SymPy returns None for a non-constant element (x + 1 is a unit of ZZ[x]/(x**2 - 2))
    return a.isGround ? isGroundUnit(this.domain, a.toGround()) : 'unknown';
  }
}
