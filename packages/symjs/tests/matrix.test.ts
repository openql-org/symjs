import { describe, expect, it } from 'vitest';
import { I, Matrix, mul, symbols } from '../src';

const [a, b, c, d] = symbols('a b c d');

describe('Matrix', () => {
  it('basic algebra', () => {
    const m = Matrix.of([[a, b], [c, d]]);
    expect(m.det().toString()).toBe('a*d - b*c');
    expect(m.trace().toString()).toBe('a + d');
    expect(m.transpose().toString()).toBe('Matrix([[a, c], [b, d]])');
    expect(m.mul(Matrix.eye(2)).equals(m)).toBe(true);
    expect(m.inv().mul(m).simplify().equals(Matrix.eye(2))).toBe(true);
  });

  it('determinant of 3x3 via Berkowitz', () => {
    const m = Matrix.of([[2, 0, 1], [1, 3, 2], [1, 1, 2]]);
    expect(m.det().toString()).toBe('6');
    expect(Matrix.of([[a, b, 0], [c, d, 0], [0, 0, 1]]).det().toString()).toBe('a*d - b*c');
    expect(() => Matrix.of([[1, 2], [2, 4]]).inv()).toThrow(/singular/);
    expect(m.mul(m.inv()).equals(Matrix.eye(3))).toBe(true);
  });

  it('kronecker product', () => {
    const k = Matrix.kron(Matrix.of([[0, 1], [1, 0]]), Matrix.eye(2));
    expect(k.rows).toBe(4);
    expect(k.get(0, 2).toString()).toBe('1');
  });

  it('eigenvalues', () => {
    expect(Matrix.of([[0, 1], [1, 0]]).eigenvals().map(String)).toEqual(['-1', '1']);
    expect(Matrix.of([[0, mul(-1, I)], [I, 0]]).eigenvals().map(String)).toEqual(['-1', '1']);
    expect(Matrix.of([[2, 1], [1, 2]]).eigenvals().map(String)).toEqual(['1', '3']);
  });
});

