import { describe, expect, it } from 'vitest';
import { I, Sym, add, adjoint, conjugate, exp, latex, mul, pow, transpose } from '../src';

const x = new Sym('x');
const r = new Sym('r', { real: true });
const A = new Sym('A', { commutative: false });
const B = new Sym('B', { commutative: false });

describe('adjoint and transpose (SymPy semantics)', () => {
  it('adjoint', () => {
    expect(adjoint(x).toString()).toBe('conjugate(x)');
    expect(adjoint(r).toString()).toBe('r');
    expect(adjoint(add(2, mul(3, I))).toString()).toBe('2 - 3*I');
    expect(adjoint(mul(A, B)).toString()).toBe('adjoint(B)*adjoint(A)');
    expect(adjoint(mul(A, B, x)).toString()).toBe('conjugate(x)*adjoint(B)*adjoint(A)');
    expect(adjoint(add(A, B)).toString()).toBe('adjoint(A) + adjoint(B)');
    expect(adjoint(pow(A, 2)).toString()).toBe('adjoint(A)**2');
    expect(adjoint(adjoint(A)).toString()).toBe('A');
    expect(adjoint(mul(r, A)).toString()).toBe('r*adjoint(A)');
    expect(adjoint(conjugate(A)).toString()).toBe('transpose(A)');
    expect(adjoint(transpose(A)).toString()).toBe('conjugate(A)');
    expect(adjoint(exp(A)).toString()).toBe('exp(adjoint(A))');
  });
  it('transpose', () => {
    expect(transpose(x).toString()).toBe('x');
    expect(transpose(mul(A, B)).toString()).toBe('transpose(B)*transpose(A)');
    expect(transpose(mul(I, A)).toString()).toBe('I*transpose(A)');
    expect(conjugate(mul(A, B)).toString()).toBe('conjugate(A)*conjugate(B)');
  });
  it('latex', () => {
    expect(latex(adjoint(mul(A, B)))).toBe('B^{\\dagger} A^{\\dagger}');
    expect(latex(adjoint(pow(A, 2)))).toBe('\\left(A^{\\dagger}\\right)^{2}');
  });
});
