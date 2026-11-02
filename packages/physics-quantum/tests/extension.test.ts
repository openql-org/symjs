import { describe, expect, it } from 'vitest';
import { Expr, ExtensionExpr, Sym, adjoint, diff, latex, mul, subs, xreplace } from '@symjs/symjs';

/** A minimal Ket node defined outside the base module, using only its public API. */
class Ket extends ExtensionExpr {
  constructor(label: Expr) {
    super('Ket', [label]);
  }
  withArgs(args: readonly Expr[]): Expr {
    return new Ket(args[0]!);
  }
  override get isCommutative(): boolean {
    return false;
  }
  override printStr(print: (e: Expr) => string): string {
    return `|${print(this.args[0]!)}>`;
  }
  override printLatex(print: (e: Expr) => string): string {
    return `{\\left|${print(this.args[0]!)}\\right\\rangle}`;
  }
  override adjointSelf(): Expr {
    return new Bra(this.args[0]!);
  }
  override diffSelf(): Expr | undefined {
    return undefined;
  }
}

class Bra extends ExtensionExpr {
  constructor(label: Expr) {
    super('Bra', [label]);
  }
  withArgs(args: readonly Expr[]): Expr {
    return new Bra(args[0]!);
  }
  override get isCommutative(): boolean {
    return false;
  }
  override printStr(print: (e: Expr) => string): string {
    return `<${print(this.args[0]!)}|`;
  }
  override adjointSelf(): Expr {
    return new Ket(this.args[0]!);
  }
}

const x = new Sym('x');
const psi = new Sym('psi');

describe('extension nodes via ExtensionExpr', () => {
  it('print, substitute and rebuild', () => {
    const k = new Ket(psi);
    expect(String(mul(2, k))).toBe('2*|psi>');
    expect(latex(k)).toBe('{\\left|\\psi\\right\\rangle}');
    expect(String(subs(mul(x, k), [[psi, x]]))).toBe('x*|x>');
    expect(String(xreplace(k, [[psi, x]]))).toBe('|x>');
  });
  it('adjoint and product order', () => {
    const k = new Ket(psi);
    expect(String(adjoint(mul(x, k)))).toBe('conjugate(x)*<psi|');
    expect(String(mul(new Bra(psi), k))).toBe('<psi|*|psi>');
    expect(String(mul(k, new Bra(psi)))).toBe('|psi>*<psi|');
  });
  it('structural equality', () => {
    expect(new Ket(psi).equals(new Ket(psi))).toBe(true);
    expect(new Ket(psi).equals(new Bra(psi))).toBe(false);
  });
  it('derivative of a node without diffSelf fails loudly', () => {
    expect(() => diff(new Ket(x), x)).toThrow(/does not define a derivative/);
  });
});
