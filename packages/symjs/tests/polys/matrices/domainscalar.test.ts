// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/polys/matrices/domainscalar.ts. Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { Rational } from '../../../src/core';
import { QQ, ZZ } from '../../../src/polys/domains';
import { DomainScalar } from '../../../src/polys/matrices/domainscalar';

const z = (n: number) => new DomainScalar(Rational.of(BigInt(n)), ZZ);

describe('DomainScalar', () => {
  it('does arithmetic', () => {
    const [d, e] = [z(7), z(2)];
    expect([d.add(e), d.sub(e), d.mul(e), d.mul(3), d.floordiv(e), d.mod(e), d.pow(2), d.neg(), d.pos()].map(String)).toEqual(['9', '5', '14', '21', '3', '1', '49', '-7', '7']);
    expect(d.divmod(e).map(String)).toEqual(['3', '1']);
    expect([d.equals(e), d.equals(z(7)), d.equals(1), d.isZero(), d.isOne(), z(0).isZero(), z(1).isOne(), d.isNonzero]).toEqual([false, true, false, false, false, true, true, true]);
    expect(String(DomainScalar.fromSympy(Rational.of(1n, 2n)))).toBe('MPQ(1,2)');
    expect(String(DomainScalar.new(Rational.of(3n), ZZ))).toBe('3');
    expect(String(d.add(new DomainScalar(Rational.of(1n, 2n), QQ)))).toBe('MPQ(15,2)');
    expect(String(d.toDomain(QQ))).toBe('MPQ(7,1)');
    expect(String(d.convertTo(QQ).toSympy())).toBe('7');
    expect(String(new DomainScalar(Rational.of(2n), QQ).pow(-2))).toBe('MPQ(1,4)');
  });
});
