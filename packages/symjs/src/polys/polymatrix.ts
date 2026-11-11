// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14 polys/polymatrix.py, BSD-3-Clause; see LICENSE.

import { at, expectType, first } from '../core/guard';
import { Sym } from '../core/nodes';
import type { ExprLike } from '../core/nodes';
import { pow, sympify } from '../core/ops';
import { Matrix } from '../matrices/matrix';
import { str } from '../printing/str';
import { constructDomain } from './constructor';
import type { Domain } from './domains';
import { preprocessDomain } from './polyoptions';
import { Poly } from './sympoly';

export type PolyMatrixEntry = ExprLike | Poly;
export interface PolyMatrixOptions { ring?: Domain | string }

/** A dense polynomial matrix, with arithmetic in a common coefficient ring. */
export class MutablePolyDenseMatrix {
  readonly ring: Domain;
  private matrix: Matrix;
  constructor(entries: readonly PolyMatrixEntry[] | readonly (readonly PolyMatrixEntry[])[] = [], ...generators: (Sym | PolyMatrixOptions)[]) {
    const last = generators.at(-1);
    const options = last !== undefined && !(last instanceof Sym) ? last : {};
    const gens = generators.filter((g): g is Sym => g instanceof Sym);
    const rows = entries.map((row) => Array.isArray(row) ? row : [row]);
    const items: PolyMatrixEntry[] = rows.flat();
    const allPoly = items.length > 0 && items.every((p) => p instanceof Poly);
    const expressions = items.map((p) => p instanceof Poly ? p.asExpr() : sympify(p));
    if ('ring' in options && options.ring !== undefined) this.ring = preprocessDomain(options.ring);
    else if (allPoly) {
      this.ring = items.map((item) => {
        const p = expectType(item, (value): value is Poly => value instanceof Poly, 'polynomial');
        return preprocessDomain(p.domain).polyRing(...p.gens.map((g) => { if (!(g instanceof Sym)) throw new TypeError('symbol generators required'); return g; }));
      }).reduce((a, b) => a.unify(b));
    } else {
      const domain = constructDomain(expressions)[0];
      const symbols = gens.length ? gens : domain.symbols;
      this.ring = domain.dom.getField().polyRing(...symbols);
    }
    const width = rows[0]?.length ?? 0;
    if (rows.some((row) => row.length !== width)) throw new RangeError('ragged polynomial matrix');
    this.matrix = Matrix.fromFunction(rows.length, width, (i, j) => this.ring.fromSympy(at(expressions, i * width + j)));
  }
  static fromMatrix(matrix: Matrix, options: PolyMatrixOptions): MutablePolyDenseMatrix {
    return new MutablePolyDenseMatrix(matrix.toArray(), options);
  }
  get rows(): number { return this.matrix.rows; }
  get cols(): number { return this.matrix.cols; }
  get shape(): [number, number] { return [this.rows, this.cols]; }
  get domain(): Domain { return this.ring.dom; }
  get gens(): readonly Sym[] { return this.ring.symbols; }
  toMatrix(): Matrix { return Matrix.of(this.matrix.toArray()); }
  get(i: number, j = 0): Poly { return Poly.from(this.matrix.get(i, j), this.gens, { domain: this.domain.toString() }); }
  set(i: number, j: number, value: PolyMatrixEntry): void {
    const data = [...this.matrix.data];
    this.matrix.get(i, j);
    data[i * this.cols + j] = this.ring.fromSympy(value instanceof Poly ? value.asExpr() : value);
    this.matrix = Matrix.fromFunction(this.rows, this.cols, (r, c) => at(data, r * this.cols + c));
  }
  private result(matrix: Matrix, ring = this.ring): MutablePolyDenseMatrix { return MutablePolyDenseMatrix.fromMatrix(matrix, { ring }); }
  add(other: MutablePolyDenseMatrix): MutablePolyDenseMatrix { return this.result(this.matrix.add(other.matrix), this.ring.unify(other.ring)); }
  sub(other: MutablePolyDenseMatrix): MutablePolyDenseMatrix { return this.result(this.matrix.sub(other.matrix), this.ring.unify(other.ring)); }
  neg(): MutablePolyDenseMatrix { return this.result(this.matrix.neg()); }
  mul(other: MutablePolyDenseMatrix | ExprLike): MutablePolyDenseMatrix {
    if (other instanceof MutablePolyDenseMatrix) return this.result(this.matrix.mul(other.matrix), this.ring.unify(other.ring));
    const scalar = sympify(other);
    const ring = this.ring.unify(constructDomain([scalar])[0]);
    return this.result(this.matrix.mul(scalar), ring);
  }
  div(other: ExprLike | Poly): MutablePolyDenseMatrix {
    const scalar = this.domain.fromSympy(other instanceof Poly ? other.asExpr() : other);
    return this.result(this.matrix.mul(this.domain.fromSympy(pow(scalar, -1))));
  }
  transpose(): MutablePolyDenseMatrix { return this.result(this.matrix.transpose()); }
  equals(other: MutablePolyDenseMatrix): boolean { return this.ring.equals(other.ring) && this.matrix.equals(other.matrix); }
  toString(): string {
    if (!this.rows || !this.cols) return `PolyMatrix(${this.rows}, ${this.cols}, [], ring=${this.ring.toString()})`;
    const rows = this.matrix.toArray().map((r) => r.map(str));
    const widths = first(rows).map((_, j) => Math.max(...rows.map((r) => at(r, j).length)));
    const body = this.rows === 1 ? `[${first(rows).join(', ')}]` : '\n' + rows.map((r) => `[${r.map((s, j) => s.padStart(at(widths, j))).join(', ')}]`).join(',\n');
    return `PolyMatrix([${body}], ring=${this.ring.toString()})`;
  }
}

export { MutablePolyDenseMatrix as PolyMatrix, MutablePolyDenseMatrix as MutablePolyMatrix };
