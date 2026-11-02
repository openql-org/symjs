// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file A minimal SymPy DomainMatrix: the entries of a matrix with the
 * ground domain they belong to (Matrix.to_DM).
 */

import { Float, Rational } from '../core/nodes';
import { freeSymbols } from '../core/traverse';
import { str } from '../printing/str';
import { inferDomain } from '../polys/sympoly';
import { Matrix } from './matrix';

/** A matrix over a domain (SymPy DomainMatrix), stored sparsely like SymPy's repr. */
export class DomainMatrix {
  constructor(
    readonly matrix: Matrix,
    /** The domain name: ZZ, QQ, RR, ZZ_I, QQ_I, ZZ[x], ZZ(x), EXRAW, ... */
    readonly domain: string,
  ) {}
  get shape(): [number, number] {
    return [this.matrix.rows, this.matrix.cols];
  }
  /** Back to a Matrix (SymPy to_Matrix). */
  toMatrix(): Matrix {
    return this.matrix;
  }
  /** SymPy repr: DomainMatrix({0: {0: 1, 1: 2}, ...}, (2, 2), ZZ). */
  toString(): string {
    const rows: string[] = [];
    for (let i = 0; i < this.matrix.rows; i++) {
      const cells: string[] = [];
      for (let j = 0; j < this.matrix.cols; j++) {
        const e = this.matrix.get(i, j);
        if (!(e instanceof Rational && e.isZero)) cells.push(`${j}: ${str(e)}`);
      }
      if (cells.length) rows.push(`${i}: {${cells.join(', ')}}`);
    }
    return `DomainMatrix({${rows.join(', ')}}, (${this.matrix.rows}, ${this.matrix.cols}), ${this.domain})`;
  }
}

/** The domain of matrix entries as SymPy's to_DM chooses it; `field` gives the fraction field. */
function matrixDomain(m: Matrix, field: boolean): string {
  const cs = m.data;
  const syms = new Set(cs.flatMap((c) => [...freeSymbols(c)].map((s) => s.key)));
  let d = inferDomain([...cs]);
  if (cs.some((c) => c instanceof Float) && syms.size && d === 'EX') {
    // floats with symbols: a polynomial ring over RR
    const rest = inferDomain(cs.map((c) => (c instanceof Float ? Rational.of(1n) : c)));
    d = rest.replace(/^(ZZ|QQ)/, 'RR');
  }
  if (d === 'EX') return 'EXRAW';
  if (!field) return d;
  if (d === 'ZZ') return 'QQ';
  if (d === 'ZZ_I') return 'QQ_I';
  const m2 = /^(ZZ|QQ|RR)\[(.*)\]$/.exec(d);
  return m2 ? `${m2[1]}(${m2[2]})` : d;
}

/** SymPy Matrix.to_DM(field): the matrix as a DomainMatrix over its ground domain. */
export function toDM(m: Matrix, opts: { field?: boolean; domain?: string } = {}): DomainMatrix {
  return new DomainMatrix(m, opts.domain ?? matrixDomain(m, Boolean(opts.field)));
}

