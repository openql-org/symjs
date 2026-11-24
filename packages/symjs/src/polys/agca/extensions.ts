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
import type { ExprLike } from '../../core/nodes';
import { Expr, Rational, Sym, compareExpr } from '../../core/nodes';
import { str } from '../../printing/str';
import type { GlobalPolynomialRing } from '../domains';
import { CoercionFailed, Domain, groundToSympy } from '../domains';
import { GeneratorsError } from '../polyerrors';
import { freeSymbols } from '../../core/traverse';
import { Poly } from '../sympoly';

/** SymPy domain.is_unit of a coefficient: nonzero in a field, +-1 in a ring. */
function isGroundUnit(K: Domain, c: Expr): boolean {
  if (K.isField) return !(c instanceof Rational && c.isZero);
  return c instanceof Rational && c.q === 1n && (c.p === 1n || c.p === -1n);
}

/**
 * An element of a finite extension, a polynomial reduced modulo the modulus.
 *
 * @see SymPy `sympy.polys.agca.extensions.ExtensionElement`
 */
export class ExtensionElement {
  /**
   * Represents a residue class by a polynomial in the generating element.
   *
   * @param rep - Representation from which to construct the value.
   * @param ext - Algebraic extension defining the element.
   */
  constructor(
    /**
     * The polynomial representative of the residue class.
     *
     * @see SymPy `sympy.polys.agca.extensions.ExtensionElement.rep`
     */
    readonly rep: Poly,
    /**
     * The extension containing the element.
     *
     * @see SymPy `sympy.polys.agca.extensions.ExtensionElement.ext`
     */
    readonly ext: FiniteExtension,
  ) {}

  /**
   * The extension.
   *
   * @returns The algebra or domain containing this element.
   * @see SymPy `sympy.polys.agca.extensions.ExtensionElement.parent`
   */
  parent(): FiniteExtension {
    return this.ext;
  }

  /**
   * Substitutes the generator into the reduced polynomial representative.
   *
   * @returns The corresponding symbolic expression.
   * @see SymPy `sympy.polys.agca.extensions.ExtensionElement.as_expr`
   */
  asExpr(): Expr {
    return this.ext.toSympy(this);
  }

  /**
   * Tests for the additive identity.
   *
   * @returns Whether the value equals zero.
   */
  get isZero(): boolean {
    return this.rep.isZero;
  }

  /**
   * Reverses the sign of the value.
   *
   * @returns The additive inverse.
   * @see SymPy `sympy.polys.agca.extensions.ExtensionElement.__neg__`
   */
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

  /**
   * Adds the other operand to this value.
   *
   * @param g - Addend.
   * @returns The sum of the operands.
   * @see SymPy `sympy.polys.agca.extensions.ExtensionElement.__add__`
   */
  add(g: ExtensionElement | ExprLike): ExtensionElement {
    return new ExtensionElement(this.rep.add(this.#rep(g)), this.ext);
  }

  /**
   * Subtracts the other operand from this value.
   *
   * @param g - Value to subtract.
   * @returns The difference in operand order.
   * @see SymPy `sympy.polys.agca.extensions.ExtensionElement.__sub__`
   */
  sub(g: ExtensionElement | ExprLike): ExtensionElement {
    return new ExtensionElement(this.rep.sub(this.#rep(g)), this.ext);
  }

  /**
   * Multiplies this value by the factor on its right.
   *
   * @param g - Factor on the right.
   * @returns The product in operand order.
   * @see SymPy `sympy.polys.agca.extensions.ExtensionElement.__mul__`
   */
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

  /**
   * Finds an element whose product with the residue class is one.
   *
   * @returns The multiplicative inverse.
   * @throws NotImplementedError when inversion outside a field requires a nonconstant divisor or a
   *   nonunit.
   * @throws NotInvertible when the element is zero or has no inverse.
   * @see SymPy `sympy.polys.agca.extensions.ExtensionElement.inverse`
   */
  inverse(): ExtensionElement {
    this.#divcheck();
    const inv = this.ext.isField ? this.rep.invert(this.ext.mod) : this.ext.one.rep.exquo(this.rep);
    return new ExtensionElement(inv, this.ext);
  }

  /**
   * Divides by the supplied divisor.
   *
   * @param g - Divisor.
   * @returns The quotient.
   * @throws RangeError when division is not defined for the supplied divisor.
   * @throws NotImplementedError when inversion outside a field requires a nonconstant divisor or a
   *   nonunit.
   * @see SymPy `sympy.polys.agca.extensions.ExtensionElement.__truediv__`
   */
  div(g: ExtensionElement | ExprLike): ExtensionElement {
    const d = new ExtensionElement(this.#rep(g), this.ext);
    if (d.isZero) throw new RangeError(`${String(this)} / ${String(d)}`);
    return this.mul(d.inverse());
  }

  /**
   * Computes the quotient under the division rule of this domain.
   *
   * @param g - Divisor.
   * @returns The quotient under floor division.
   * @throws NotImplementedError when inversion outside a field requires a nonconstant divisor or a
   *   nonunit.
   * @see SymPy `sympy.polys.agca.extensions.ExtensionElement.__floordiv__`
   */
  floordiv(g: ExtensionElement | ExprLike): ExtensionElement {
    return this.div(g);
  }

  /**
   * Returns zero after verifying that division by the supplied element is defined.
   *
   * @param g - Divisor.
   * @returns The remainder after division.
   * @throws RangeError when division is not defined for the supplied divisor.
   * @throws NotImplementedError when inversion outside a field requires a nonconstant divisor or a
   *   nonunit.
   * @see SymPy `sympy.polys.agca.extensions.ExtensionElement.__mod__`
   */
  mod(g: ExtensionElement | ExprLike): ExtensionElement {
    const d = new ExtensionElement(this.#rep(g), this.ext);
    if (d.isZero) throw new RangeError(`${String(this)} % ${String(d)}`);
    d.#divcheck();
    return this.ext.zero;
  }

  /**
   * Raises the value to the specified power.
   *
   * @param nIn - Exponent to which to raise the value.
   * @returns The value raised to the given exponent.
   * @throws RangeError when a negative exponent requires an unavailable inverse.
   * @see SymPy `sympy.polys.agca.extensions.ExtensionElement.__pow__`
   */
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

  /**
   * Compares the two operands for equality.
   *
   * @param g - Value to compare against.
   * @returns Whether the operands are equal.
   * @see SymPy `sympy.polys.agca.extensions.ExtensionElement.__eq__`
   */
  equals(g: unknown): boolean {
    return g instanceof ExtensionElement && g.ext.equals(this.ext) && g.rep.equals(this.rep);
  }

  /**
   * Checks that no positive power of the generator occurs in the reduced representative.
   *
   * @returns Whether the element belongs to the coefficient domain.
   * @see SymPy `sympy.polys.agca.extensions.ExtensionElement.is_ground`
   */
  get isGround(): boolean {
    return this.rep.degree() <= 0;
  }

  /**
   * The constant of a ground element.
   *
   * @returns The constant coefficient.
   * @throws RangeError when the element is not constant.
   * @see SymPy `sympy.polys.agca.extensions.ExtensionElement.to_ground`
   */
  toGround(): Expr {
    if (!this.isGround) throw new RangeError(`${String(this)} is not a constant`);
    return this.rep.LC();
  }

  /**
   * Formats the value as text.
   *
   * @returns The printable representation.
   * @see SymPy `sympy.polys.agca.extensions.ExtensionElement.__str__`
   */
  toString(): string {
    return str(this.asExpr());
  }
}

/**
 * Represents the quotient of a univariate polynomial ring by a monic polynomial.
 *
 * @see SymPy `sympy.polys.agca.extensions.MonogenicFiniteExtension`
 * @example
 * ```ts
 * import { ex, FiniteExtension, Poly } from '@symjs/symjs';
 *
 * const R = new FiniteExtension(Poly.from(ex`x**2 - 2`));
 * String(R.new(ex`1 + x`).mul(ex`3 - 2*x`)); // => x - 1
 * ```
 */
export class FiniteExtension {
  /**
   * The flag identifying a finite ring extension.
   *
   * @see SymPy `sympy.polys.agca.extensions.MonogenicFiniteExtension.is_FiniteExtension`
   */
  readonly isFiniteExtension = true;
  /**
   * Indicates whether the base coefficient domain is a field.
   *
   * @see SymPy `sympy.polys.agca.extensions.MonogenicFiniteExtension.is_Field`
   */
  readonly isField: boolean;
  /**
   * The degree of the modulus.
   *
   * @see SymPy `sympy.polys.agca.extensions.MonogenicFiniteExtension.rank`
   */
  readonly rank: number;
  /**
   * The (monic) polynomial.
   *
   * @see SymPy `sympy.polys.agca.extensions.MonogenicFiniteExtension.modulus`
   */
  readonly modulus: Poly;
  /**
   * Computes the remainder on division by the supplied divisor.
   *
   * @see SymPy `sympy.polys.agca.extensions.MonogenicFiniteExtension.mod`
   */
  readonly mod: Poly;
  /**
   * The coefficient domain.
   *
   * @see SymPy `sympy.polys.agca.extensions.MonogenicFiniteExtension.domain`
   */
  readonly domain: Domain;
  /**
   * The polynomial ring in the generator over the base domain.
   *
   * @see SymPy `sympy.polys.agca.extensions.MonogenicFiniteExtension.ring`
   */
  readonly ring: GlobalPolynomialRing;
  /**
   * The generator x.
   *
   * @see SymPy `sympy.polys.agca.extensions.MonogenicFiniteExtension.symbol`
   */
  readonly symbol: Sym;
  /**
   * The additive identity.
   *
   * @see SymPy `sympy.polys.agca.extensions.MonogenicFiniteExtension.zero`
   */
  readonly zero: ExtensionElement;
  /**
   * The multiplicative identity.
   *
   * @see SymPy `sympy.polys.agca.extensions.MonogenicFiniteExtension.one`
   */
  readonly one: ExtensionElement;
  /**
   * The residue class of the polynomial variable.
   *
   * @see SymPy `sympy.polys.agca.extensions.MonogenicFiniteExtension.generator`
   */
  readonly generator: ExtensionElement;
  /**
   * Counts the independent generators of the Lie algebra.
   *
   * @see SymPy `sympy.polys.agca.extensions.MonogenicFiniteExtension.basis`
   */
  readonly basis: readonly ExtensionElement[];

  /**
   * Forms the quotient ring by reducing polynomials modulo the supplied polynomial.
   *
   * @param modIn - Univariate polynomial defining the quotient.
   * @throws TypeError when the modulus is not a univariate polynomial.
   * @throws ExactQuotientFailed when the leading coefficient cannot be divided out in the coefficient
   *   domain.
   */
  constructor(modIn: Poly) {
    if (!(modIn instanceof Poly) || modIn.gens.length !== 1) throw new TypeError('modulus must be a univariate Poly');
    // SymPy mod.monic(auto=False): monic over a field, the polynomial itself over a ring when its leading coefficient is not 1
    const domain = modIn.getDomain();
    // SymPy mod.monic(auto=False): over a ring the leading coefficient must be a unit
    if (!isGroundUnit(domain, modIn.LC())) throw new ExactQuotientFailed(`${str(modIn.LC())} does not divide 1 in ${modIn.domain}`);
    const mod = modIn.LC().equals(1) ? modIn : modIn.monic(false);
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
    return Poly.from(e, [this.symbol], { domain: this.domain });
  }

  /**
   * The element of a polynomial or an expression.
   *
   * @param arg - Value to represent.
   * @returns The newly constructed element.
   * @see SymPy `sympy.polys.agca.extensions.MonogenicFiniteExtension.new`
   */
  new(arg: ExtensionElement | Poly | ExprLike): ExtensionElement {
    return this.convert(arg);
  }

  /**
   * Coerces the input into the target domain.
   *
   * @param f - Element to convert or divide.
   * @param base - Source domain when converting an existing element.
   * @returns The value represented in the target domain.
   * @throws CoercionFailed when the value cannot be represented in the target domain.
   * @see SymPy `sympy.polys.agca.extensions.MonogenicFiniteExtension.convert`
   */
  convert(f: unknown, base?: Domain): ExtensionElement {
    if (f instanceof ExtensionElement) {
      if (!f.ext.equals(this)) throw new CoercionFailed(`${String(f)} is not an element of ${String(this)}`);
      return f;
    }
    const e = base !== undefined ? base.toSympy(f) : f instanceof Poly ? f.asExpr() : groundToSympy(f);
    if (!(e instanceof Expr)) throw new CoercionFailed(`cannot convert ${String(f)} to ${String(this)}`);
    if ([...freeSymbols(e)].some((a) => a.key !== this.symbol.key && !this.domain.symbols.some((s) => s.key === a.key))) {
      throw new CoercionFailed(`cannot convert ${str(e)} to ${String(this)}`);
    }
    return new ExtensionElement(this.#poly(e).rem(this.mod), this);
  }

  /**
   * Convert an element with an explicit coefficient domain.
   *
   * @param f - Element to convert or divide.
   * @param base - Source domain when converting an existing element.
   * @returns The value represented in the target domain.
   * @see SymPy `sympy.polys.agca.extensions.MonogenicFiniteExtension.convert_from`
   */
  convertFrom(f: unknown, base: Domain): ExtensionElement {
    return this.convert(f, base);
  }

  /**
   * Compares the two operands for equality.
   *
   * @param other - Value to compare against.
   * @returns Whether the operands are equal.
   * @see SymPy `sympy.polys.agca.extensions.MonogenicFiniteExtension.__eq__`
   */
  equals(other: unknown): boolean {
    return other instanceof FiniteExtension && other.modulus.equals(this.modulus) && other.modulus.domain === this.modulus.domain;
  }

  /**
   * Formats the value as text.
   *
   * @returns The printable representation.
   * @see SymPy `sympy.polys.agca.extensions.MonogenicFiniteExtension.__str__`
   */
  toString(): string {
    return `${String(this.ring)}/(${str(this.modulus.asExpr())})`;
  }

  /**
   * Checks the characteristic of the coefficient ring.
   *
   * @returns Whether the characteristic is zero.
   * @see SymPy `sympy.polys.agca.extensions.MonogenicFiniteExtension.has_CharacteristicZero`
   */
  get hasCharacteristicZero(): boolean {
    return this.characteristic() === 0n;
  }

  /**
   * Computes the characteristic inherited from the coefficient domain.
   *
   * @returns The characteristic of the coefficient domain.
   * @see SymPy `sympy.polys.agca.extensions.MonogenicFiniteExtension.characteristic`
   */
  characteristic(): bigint {
    const m = /^GF\((\d+)\)$/.exec(this.modulus.domain);
    return m ? BigInt(at(m, 1)) : 0n;
  }

  /**
   * Expresses the value using symbolic expression nodes.
   *
   * @param f - Element to convert or divide.
   * @returns The corresponding symbolic expression.
   * @see SymPy `sympy.polys.agca.extensions.MonogenicFiniteExtension.to_sympy`
   */
  toSympy(f: unknown): Expr {
    return cast(f, ExtensionElement, 'extension element').rep.asExpr();
  }

  /**
   * Interprets a symbolic expression in this domain.
   *
   * @param f - Element to convert or divide.
   * @returns The expression converted into the domain.
   * @see SymPy `sympy.polys.agca.extensions.MonogenicFiniteExtension.from_sympy`
   */
  fromSympy(f: ExprLike): Expr {
    return this.toSympy(this.convert(f));
  }

  /**
   * The same extension with canonical expression elements for DomainMatrix arithmetic.
   *
   * @returns The corresponding coefficient domain.
   */
  toDomain(): Domain {
    return new ExtensionDomain(this);
  }

  /**
   * The extension by the modulus over another domain.
   *
   * @param K - Coefficient domain for the values.
   * @returns The ring over the replacement domain.
   * @see SymPy `sympy.polys.agca.extensions.MonogenicFiniteExtension.set_domain`
   */
  setDomain(K: Domain | string): FiniteExtension {
    return new FiniteExtension(this.modulus.setDomain(K));
  }

  /**
   * The extension over the domain without the symbols.
   *
   * @param symbols - Polynomial generators.
   * @returns The extension with the specified symbols removed.
   * @throws GeneratorsError when a requested symbol is the extension generator.
   * @see SymPy `sympy.polys.agca.extensions.MonogenicFiniteExtension.drop`
   */
  drop(...symbols: Expr[]): FiniteExtension {
    if (symbols.some((s) => s.key === this.symbol.key)) throw new GeneratorsError('Can not drop generator from FiniteExtension');
    const rest = this.domain.symbols.filter((s) => !symbols.some((t) => t.key === s.key));
    const base = this.domain.dom;
    const K = rest.length === 0 ? base : this.domain.isField ? base.fracField(...rest) : base.polyRing(...rest);
    return this.setDomain(K);
  }

  /**
   * Order two extensions by their moduli for a deterministic tower, or unify the ground domain after
   * dropping the extension generator.
   *
   * @param K - Coefficient domain for the values.
   * @returns The unified extension.
   * @see SymPy `sympy.polys.agca.extensions.MonogenicFiniteExtension.unify`
   */
  unify(K: Domain | FiniteExtension): FiniteExtension {
    const other = K instanceof ExtensionDomain ? K.extension : K;
    if (other instanceof FiniteExtension) {
      if (other.equals(this)) return this;
      const [base, outer] = compareExpr(this.modulus.asExpr(), other.modulus.asExpr()) <= 0 ? [this, other] : [other, this];
      return outer.setDomain(base.toDomain());
    }
    return this.setDomain(this.domain.unify(other.drop(this.symbol)));
  }

  /**
   * Divides two elements in the coefficient domain.
   *
   * @param f - Dividend in the coefficient domain.
   * @param g - Divisor.
   * @returns The quotient.
   * @see SymPy `sympy.polys.agca.extensions.MonogenicFiniteExtension.quo`
   */
  quo(f: ExtensionElement, g: ExtensionElement): ExtensionElement {
    return this.exquo(f, g);
  }

  /**
   * Divides in the coefficient domain, requiring exact divisibility.
   *
   * @param f - Dividend in the coefficient domain.
   * @param g - Divisor.
   * @returns The exact quotient.
   * @see SymPy `sympy.polys.agca.extensions.MonogenicFiniteExtension.exquo`
   */
  exquo(f: ExtensionElement, g: ExtensionElement): ExtensionElement {
    return new ExtensionElement(f.rep.exquo(g.rep).rem(this.mod), this);
  }

  /**
   * Treats extension elements as unordered for sign tests.
   *
   * @param _a - Element on which to operate.
   * @returns Whether the value is negative in this domain.
   * @see SymPy `sympy.polys.agca.extensions.MonogenicFiniteExtension.is_negative`
   */
  isNegative(_a: ExtensionElement): boolean {
    return false;
  }

  /**
   * Tests invertibility in the extension, using the coefficient domain for constant elements.
   *
   * @param a - Element on which to operate.
   * @returns Whether the element is invertible, or `'unknown'` for a nonground element when the base
   *   is not a field.
   * @see SymPy `sympy.polys.agca.extensions.MonogenicFiniteExtension.is_unit`
   */
  isUnit(a: ExtensionElement): boolean | 'unknown' {
    if (this.isField) return !a.isZero;
    // SymPy returns None for a non-constant element (x + 1 is a unit of ZZ[x]/(x**2 - 2))
    return a.isGround ? isGroundUnit(this.domain, a.toGround()) : 'unknown';
  }
}

/** Expression representation of K[x]/(f), with division computed modulo f. */
class ExtensionDomain extends Domain {
  readonly ground = 'EX' as const;
  readonly isField: boolean;
  override readonly symbols: readonly Sym[];
  constructor(readonly extension: FiniteExtension) {
    super();
    this.isField = extension.isField;
    this.symbols = [...extension.domain.symbols, extension.symbol];
  }
  override get isFiniteExtension(): boolean { return true; }
  override get hasCharacteristicZero(): boolean { return this.extension.hasCharacteristicZero; }
  override characteristic(): bigint { return this.extension.characteristic(); }
  override unify(other: Domain): Domain { return this.extension.unify(other).toDomain(); }
  toString(): string { return this.extension.toString(); }
  canon(e: Expr): Expr { return this.extension.fromSympy(e); }
  fromSympy(e: ExprLike): Expr { return this.extension.fromSympy(e); }
  override quo(a: Expr, b: Expr): Expr {
    return this.extension.convert(a).div(this.extension.convert(b)).asExpr();
  }
  getField(): Domain {
    if (!this.isField) throw new NotImplementedError('The finite extension is not a field');
    return this;
  }
}
