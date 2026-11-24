// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14 parsing/latex/lark/transformer.py (BSD-3-Clause).

import type { FnName, RelOp } from '../../../core/nodes';
import { Add, Derivative, Expr, ExtensionExpr, Float, Fn, Integral, Limit, Mul, Pow, Rational, Rel, S, Sym, UndefFn } from '../../../core/nodes';
import { at, cast } from '../../../core/guard';
import { add, mul, pow } from '../../../core/ops';
import { rel } from '../../../core/logic';
import { Concrete } from '../../../core/concrete';
import { globalParameters } from '../../../core/parameters';
import { subs } from '../../../core/traverse';
import { float } from '../../../numeric/floatctor';
import { fn, log } from '../../../functions/elementary/elementary';
import '../../../functions/special/special';
import { Matrix } from '../../../matrices/matrix';
import { Adjoint, ImmutableMatrixNode, MatAdd, MatMul, MatPow, MatrixExpr, Trace, Transpose } from '../../../matrices/expressions/matexpr';
import { LaTeXParsingError } from '../errors';
import { LatexTree } from '../tree';
import type { LatexResult } from '../tree';

// The core symbol constructor requires a nonempty name; mathit_text in LaTeX.g4
// also permits the empty identifier. It still behaves as an ordinary Sym.
class EmptyLatexSymbol extends Sym {
  override readonly name = '';
  constructor() { super(' '); }
}

const FUNCTION_NAMES: ReadonlyMap<string, FnName> = new Map<string, FnName>([
  ['sin', 'sin'], ['cos', 'cos'], ['tan', 'tan'], ['csc', 'csc'], ['sec', 'sec'], ['cot', 'cot'],
  ['arcsin', 'asin'], ['arccos', 'acos'], ['arctan', 'atan'], ['arccsc', 'acsc'], ['arcsec', 'asec'], ['arccot', 'acot'],
  ['sinh', 'sinh'], ['cosh', 'cosh'], ['tanh', 'tanh'], ['asinh', 'asinh'], ['acosh', 'acosh'], ['atanh', 'atanh'],
  ['abs', 'abs'], ['floor', 'floor'], ['ceil', 'ceiling'], ['factorial', 'factorial'], ['conjugate', 'conjugate'],
  ['binomial', 'binomial'], ['min', 'Min'], ['max', 'Max'],
]);
const INVERSES: ReadonlyMap<string, FnName> = new Map<string, FnName>([['sin', 'asin'], ['cos', 'acos'], ['tan', 'atan'], ['csc', 'acsc'], ['sec', 'asec'], ['cot', 'acot'], ['sinh', 'asinh'], ['cosh', 'acosh'], ['tanh', 'atanh']]);
const RELATIONS: ReadonlyMap<string, RelOp> = new Map([['eq', 'Eq'], ['ne', 'Ne'], ['lt', 'Lt'], ['lte', 'Le'], ['gt', 'Gt'], ['gte', 'Ge']]);

/** Dirac notation needs no dependency on the quantum simulation extension. */
class DiracExpr extends ExtensionExpr {
  withArgs(args: readonly Expr[]): Expr { return new DiracExpr(this.name, args); }
  protected override computeCommutative(): boolean { return this.name === 'InnerProduct'; }
  override printStr(print: (e: Expr) => string): string {
    if (this.name === 'Bra') return `<${this.args.map(print).join(',')}|`;
    if (this.name === 'Ket') return `|${this.args.map(print).join(',')}>`;
    if (this.name === 'InnerProduct') return `<${print(at(at(this.args, 0).args, 0))}|${print(at(at(this.args, 1).args, 0))}>`;
    return this.args.map(print).join('');
  }
  override printLatex(print: (e: Expr) => string): string {
    if (this.name === 'Bra') return `{\\left\\langle ${this.args.map(print).join(',')}\\right|}`;
    if (this.name === 'Ket') return `{\\left|${this.args.map(print).join(',')}\\right\\rangle }`;
    if (this.name === 'InnerProduct') return `\\left\\langle ${print(at(at(this.args, 0).args, 0))} | ${print(at(at(this.args, 1).args, 0))}\\right\\rangle `;
    return this.args.map(print).join('');
  }
}

/**
 * Traverses grammar trees to build expressions. Subclass number(), symbol(), or
 * transform() to customize conversion, and pass that class to LarkLaTeXParser.
 *
 * @see SymPy `sympy.parsing.latex.lark.transformer.TransformToSymPyExpr`
 */
export class TransformToSymPyExpr {
  /**
   * Creates a `TransformToSymPyExpr`.
   *
   * @param backend - The parser backend whose conventions to use.
   */
  constructor(private readonly backend: 'lark' | 'antlr' = 'lark') {}
  private get evaluating(): boolean { return this.backend === 'lark' && globalParameters.evaluate; }
  /**
   * Converts a numeric token into an expression.
   *
   * @param tokens - The tokens in source order.
   * @returns The numerical expression represented by the token.
   * @see SymPy `sympy.parsing.latex.lark.transformer.TransformToSymPyExpr.number`
   */
  number(tokens: readonly string[]): Expr {
    const value = at(tokens, 0);
    if (value === '\\imaginaryunit') return S.I;
    return value.includes('.') ? float(value.replaceAll(',', '')) : Rational.of(BigInt(value.replaceAll(',', '')));
  }
  /**
   * Converts a symbol token into an expression.
   *
   * @param value - The value to examine.
   * @returns The newly constructed symbol.
   * @see SymPy `sympy.parsing.latex.lark.transformer.TransformToSymPyExpr.SYMBOL`
   */
  symbol(value: string): Expr {
    if (this.backend === 'antlr') return new Sym(value);
    const name = value.replaceAll('\\', '').replace(/var(?=epsilon|theta|rho|phi)/g, '').replace(/_([^{}]+?)(?='*$)/, '_{$1}');
    return new Sym(name);
  }
  private text(tree: LatexTree, i: number): string {
    const value = at(tree.children, i);
    if (typeof value !== 'string') throw new LaTeXParsingError('Expected a grammar token');
    return value;
  }
  private child(tree: LatexTree, i: number): LatexTree { return cast(at(tree.children, i), LatexTree); }
  private expr(tree: LatexTree, i: number): Expr {
    const result = this.transform(this.child(tree, i));
    if (result instanceof LatexTree) throw new LaTeXParsingError('Expected an expression after the derivative operator');
    return result;
  }
  private args(tree: LatexTree): Expr[] { return tree.children.filter(c => c instanceof LatexTree).map(c => {
    const value = this.transform(c);
    if (value instanceof LatexTree) throw new LaTeXParsingError('Expected an expression');
    return value;
  }); }
  private add(a: Expr, b: Expr): Expr {
    if (a instanceof MatrixExpr || b instanceof MatrixExpr) return MatAdd(a, b);
    return this.evaluating ? add(a, b) : new Add([a, b]);
  }
  private mul(a: Expr, b: Expr): Expr {
    if (a instanceof MatrixExpr || b instanceof MatrixExpr) return MatMul(a, b);
    return this.evaluating ? mul(a, b) : new Mul([a, b]);
  }
  private power(a: Expr, b: Expr): Expr {
    if (a instanceof MatrixExpr) return this.evaluating ? MatPow(a, b) : new Pow(a, b);
    return this.evaluating ? pow(a, b) : new Pow(a, b);
  }
  private negative(a: Expr, unary = false): Expr {
    if (a instanceof MatrixExpr) return MatMul(S.NegOne, a);
    if (a instanceof Rational) return Rational.of(-a.p, a.q);
    if (a instanceof Float) return new Float({ ...a.mpf, man: -a.mpf.man }, a.prec);
    if (this.backend === 'antlr' && (unary || a.args.length === 0)) return mul(-1, a);
    return this.mul(S.NegOne, a);
  }
  private call(name: FnName, args: readonly Expr[]): Expr { return fn(name, args, { evaluate: this.evaluating }); }
  private division(numerator: Expr, denominator: Expr, fraction: boolean): Expr {
    if (denominator instanceof MatrixExpr) throw new LaTeXParsingError('Cannot divide by a matrix; multiply explicitly by its inverse');
    const inverse = this.power(denominator, S.NegOne);
    return fraction && this.backend === 'antlr' && numerator.key === '1' ? inverse : this.mul(numerator, inverse);
  }
  private unwrap(t: LatexTree): LatexTree {
    return t.data.startsWith('group_') ? this.unwrap(this.child(t, 1)) : t;
  }
  private differential(t: LatexTree): LatexTree | false {
    const node = this.unwrap(t);
    if (node.data === 'adjacent_expressions' && this.unwrap(this.child(node, 0)).children[0] === 'd') return this.child(node, 1);
    return false;
  }
  private fraction(tree: LatexTree): LatexResult {
    const numerator = this.child(tree, 0);
    const denominator = this.child(tree, 1);
    const variable = this.differential(denominator);
    if (variable !== false) {
      const v = this.transform(variable);
      if (v instanceof LatexTree) throw new LaTeXParsingError('Invalid differentiation variable');
      if (this.unwrap(numerator).children[0] === 'd') return new LatexTree('derivative_operator', [v]);
      const differentiated = this.differential(numerator);
      // SymPy's Lark transformer drops this numerator and returns a bare operator.
      // d f / d x denotes a derivative of f, so retain the differentiated expression.
      if (differentiated !== false) {
        const f = this.transform(differentiated);
        if (f instanceof LatexTree) throw new LaTeXParsingError('Invalid derivative numerator');
        return new Derivative([f, v, S.One]);
      }
    }
    // A numerator without a differential is an ordinary quotient, not an
    // unapplied derivative operator: a/(d*x) must retain a and its denominator.
    return this.division(this.expr(tree, 0), this.expr(tree, 1), true);
  }
  private superscript(tree: LatexTree): Expr {
    const base = this.expr(tree, 0);
    const exponent = at(tree.children, 2);
    if (typeof exponent === 'string') {
      if (!(base instanceof MatrixExpr)) throw new LaTeXParsingError('Prime and star superscripts require a matrix');
      const sup = exponent.replace(/[{}]/g, '');
      const stars = sup.includes('*') || sup.includes('\\ast');
      const count = sup.replaceAll('\\prime', "'").replaceAll('\\ast', '*').length;
      if (stars) return count % 2 ? Adjoint(base).doit() : base.doit();
      return count % 2 ? Transpose(base) : base;
    }
    const sup = this.expr(tree, 2);
    if (base instanceof MatrixExpr && sup instanceof Sym) {
      if (sup.name === 'T') return Transpose(base);
      if (sup.name === 'H') return Adjoint(base).doit();
    }
    return this.power(base, sup);
  }
  /**
   * Converts a LaTeX grammar tree into an expression or ambiguity tree.
   *
   * @param tree - The grammar tree to convert.
   * @returns The expression or an explicit ambiguity tree.
   * @throws LaTeXParsingError when the input cannot be parsed or transformed into a mathematical expression.
   * @see SymPy `sympy.parsing.latex.lark.transformer.TransformToSymPyExpr.transform`
   */
  transform(tree: LatexTree): LatexResult {
    const name = tree.data;
    const relation = RELATIONS.get(name);
    if (relation) return globalParameters.evaluate ? rel(relation, this.expr(tree, 0), this.expr(tree, 2)) : new Rel(relation, this.expr(tree, 0), this.expr(tree, 2));
    const normal = FUNCTION_NAMES.get(name);
    if (normal) {
      let args: Expr[];
      if (name === 'min' || name === 'max') args = this.args(this.child(tree, 1));
      else args = this.args(tree);
      // Conjugation of explicit matrices is entrywise, including evaluated matrix sums.
      if (name === 'conjugate' && this.evaluating && args[0] instanceof MatrixExpr) return new ImmutableMatrixNode(args[0].asExplicit().map(e => this.call('conjugate', [e])));
      if (name === 'abs' && args[0] instanceof Mul && args[0].args.every(e => e instanceof Fn && e.name === 'abs')) return fn('abs', args, { evaluate: false });
      return this.call(normal, args);
    }
    if (name.endsWith('_power')) {
      const baseName = name.slice(0, -6);
      const exponent = this.expr(tree, 2);
      const arg = this.expr(tree, 3);
      const inverse = INVERSES.get(baseName);
      const direct = FUNCTION_NAMES.get(baseName);
      if (!direct || !inverse) throw new LaTeXParsingError(`Unknown function ${baseName}`);
      return exponent.key === '-1' ? this.call(inverse, [arg]) : this.power(this.call(direct, [arg]), exponent);
    }
    switch (name) {
      case 'latex_string': return this.transform(this.child(tree, 0));
      case '_ambig': return new LatexTree('_ambig', tree.children.map(c => this.transform(cast(c, LatexTree))));
      case 'expression_value': return cast(at(tree.children, 0), Expr);
      case 'number': return this.number([this.text(tree, 0)]);
      case 'symbol': return this.symbol(this.text(tree, 0));
      case 'multi_letter_symbol': return this.text(tree, 0) === '' ? new EmptyLatexSymbol() : new Sym(this.text(tree, 0));
      case 'infinity': return S.Infinity;
      case 'group_round_parentheses': case 'group_square_brackets': case 'group_curly_parentheses': return this.transform(this.child(tree, 1));
      case 'add': return tree.children.length === 2 ? this.expr(tree, 1) : this.add(this.expr(tree, 0), this.expr(tree, 2));
      case 'sub': return tree.children.length === 2 ? this.negative(this.expr(tree, 1), true) : this.add(this.expr(tree, 0), this.negative(this.expr(tree, 2)));
      case 'mul': return this.mul(this.expr(tree, 0), this.expr(tree, 2));
      case 'div': return this.division(this.expr(tree, 0), this.expr(tree, 2), false);
      case 'adjacent_expressions': {
        const left = this.transform(this.child(tree, 0));
        const right = this.expr(tree, 1);
        if (left instanceof LatexTree) return new Derivative([right, cast(at(left.children, 0), Sym), S.One]);
        if (left instanceof DiracExpr && right instanceof DiracExpr && left.name === 'Ket' && right.name === 'Bra') return new DiracExpr('OuterProduct', [left, right]);
        return this.mul(left, right);
      }
      case 'fraction': return this.fraction(tree);
      case 'superscript': return this.superscript(tree);
      case 'symbol_prime': return new Sym(cast(this.expr(tree, 0), Sym).name + this.text(tree, 1));
      case 'matrix_prime': {
        const base = this.expr(tree, 0);
        if (!(base instanceof MatrixExpr)) throw new LaTeXParsingError('Postfix primes require a matrix');
        return this.text(tree, 1).length % 2 ? Transpose(base) : base;
      }
      case 'function_applied': return new UndefFn(cast(this.expr(tree, 0), Sym).name, this.args(this.child(tree, 1)));
      case 'exponential': return this.power(S.E, this.expr(tree, 1));
      case 'log': {
        const arg = this.expr(tree, tree.children.length - 1);
        const base = tree.children.length === 4 ? this.expr(tree, 2) : tree.children[0] === '\\lg' ? Rational.of(10) : S.E;
        if (this.evaluating) return log(arg, base);
        return this.call('log', this.backend === 'antlr' || base !== S.E ? [arg, base] : [arg]);
      }
      case 'square_root': {
        const arg = this.expr(tree, tree.children.length - 1);
        const root = tree.children.length === 3 ? this.expr(tree, 1) : Rational.of(2);
        const exponent = tree.children.length === 2 ? S.Half : this.backend === 'antlr' ? pow(root, -1) : this.power(root, S.NegOne);
        return this.power(arg, exponent);
      }
      case 'normal_integral': case 'integral_with_special_fraction': {
        const args = this.args(tree);
        if (this.backend === 'lark' && !this.evaluating) args[0] = new Mul([S.One, at(args, 0)]);
        return new Integral(args);
      }
      case 'summation': case 'product': {
        let f = this.expr(tree, 0);
        if (name === 'summation' && this.backend === 'lark' && !this.evaluating) f = new Mul([S.One, f]);
        const limits = this.args(this.child(tree, 1));
        const variable = at(limits, 0);
        if (!(variable instanceof Sym || variable instanceof UndefFn || variable instanceof Derivative)) throw new LaTeXParsingError('Invalid summation or product variable');
        return new Concrete(name === 'summation' ? 'Sum' : 'Product', [f, ...limits, this.expr(tree, 2)]);
      }
      case 'limit': {
        const dest = this.child(tree, 2);
        const point = this.expr(dest, 0);
        const dir = point === S.Infinity ? '-' : point === S.NegativeInfinity ? '+' : at(dest.children, 1);
        if (dir !== '+' && dir !== '-' && dir !== '+-') throw new LaTeXParsingError('Invalid limit direction');
        return new Limit([this.expr(tree, 0), this.expr(tree, 1), point], dir);
      }
      case 'derivative': return new Derivative([...this.args(tree), S.One]);
      case 'derivative_operator': return new LatexTree(name, this.args(tree));
      case 'bra': return new DiracExpr('Bra', this.args(tree));
      case 'ket': return new DiracExpr('Ket', this.args(tree));
      case 'inner_product': return new DiracExpr('InnerProduct', [new DiracExpr('Bra', [this.expr(tree, 0)]), new DiracExpr('Ket', [this.expr(tree, 1)])]);
      case 'matrix': case 'determinant_matrix': {
        const body = this.child(tree, 0);
        const matrix = Matrix.of(body.children.map(row => this.args(cast(row, LatexTree))));
        return name === 'matrix' ? new ImmutableMatrixNode(matrix) : matrix.det();
      }
      case 'determinant': case 'trace': case 'adjugate': {
        const arg = this.expr(tree, 1);
        if (!(arg instanceof MatrixExpr)) throw new LaTeXParsingError(`Cannot take ${name} of a non-matrix`);
        if (name === 'trace') return Trace(arg);
        return name === 'determinant' ? arg.asExplicit().det() : new ImmutableMatrixNode(arg.asExplicit().adjugate());
      }
      case 'eval_at': {
        const expr = this.expr(tree, 0);
        const values = tree.children.slice(1).map(c => {
          const bound = cast(c, LatexTree);
          const value = this.expr(bound, bound.children.length - 1);
          const variable = bound.children.length === 2 ? this.expr(bound, 0) : [...value.freeSymbols()][0];
          return variable ? subs(expr, [[variable, value]]) : expr;
        });
        return tree.children.length === 3 ? this.add(at(values, 0), this.negative(at(values, 1), true)) : at(values, 0);
      }
      default: throw new LaTeXParsingError(`Unknown LaTeX grammar rule: ${name}`);
    }
  }
}
