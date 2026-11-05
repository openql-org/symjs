// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * JavaScript translations of SymPy doctests whose setup is Python code that
 * the extractor cannot serialize: user-defined classes (Expr subclasses,
 * _sympy_, converter), Python lambdas and functions passed as arguments,
 * and SymPy-internal containers. Each entry is keyed by
 * "<module>:<doctest source>" and does with the symjs public API what the
 * doctest (with its preceding setup lines) does in Python; the result is
 * compared with SymPy's output like any other case.
 */

import * as sj from '../packages/symjs/src';
import { Expr } from '../packages/symjs/src';
import { JsDict, JsList, JsSet, JsTuple } from './harness';
import { DifferentialExtension } from '../packages/symjs/src/integrals/risch';
import { partition as unifyPartition } from '../packages/symjs/src/unify/core';

const sym = (names: string, assumptions?: sj.Assumptions) => sj.symbols(names, assumptions) as sj.Sym[];
const [x, y, z] = sym('x y z') as [sj.Sym, sj.Sym, sj.Sym];
const half = sj.Rational.of(1n, 2n);

// ---- sympy.core.expr: Expr._diff_wrt ------------------------------------------------

/** class MyScalar(Expr): _diff_wrt = True */
class MyScalar extends sj.ExtensionExpr {
  constructor() {
    super('MyScalar', []);
  }
  withArgs(): Expr {
    return new MyScalar();
  }
}
/** class MySymbol(Expr): _diff_wrt = True; is_scalar = False */
class MySymbol extends sj.ExtensionExpr {
  constructor() {
    super('MySymbol', []);
  }
  withArgs(): Expr {
    return new MySymbol();
  }
  override get isScalar(): boolean {
    return false;
  }
}

// ---- sympy.core.basic: Basic.rewrite ---------------------------------------------------

/**
 * class MySin(Expr):
 *     def _eval_rewrite(self, rule, args, **hints):
 *         if rule == cos: return cos(pi/2 - x, evaluate=False)
 *         if rule == sqrt: return sqrt(1 - cos(x)**2)
 */
class MySin extends sj.ExtensionExpr {
  constructor(arg: Expr) {
    super('MySin', [arg]);
  }
  withArgs(args: readonly Expr[]): Expr {
    return new MySin(args[0]!);
  }
  override rewriteSelf(target: string, [a]: readonly Expr[]): Expr | undefined {
    if (target === 'cos') return sj.fn('cos', [sj.sub(sj.mul(sj.pi, half), a!)], { evaluate: false });
    if (target === 'sqrt') return sj.sqrt(sj.sub(1, sj.pow(sj.cos(a!), 2)));
    return undefined;
  }
}
/** The second MySin of the doctest only defines _eval_rewrite_as_cos. */
class MySinCos extends sj.ExtensionExpr {
  constructor(arg: Expr) {
    super('MySin', [arg]);
  }
  withArgs(args: readonly Expr[]): Expr {
    return new MySinCos(args[0]!);
  }
  override rewriteSelf(target: string, [a]: readonly Expr[]): Expr | undefined {
    return target === 'cos' ? sj.fn('cos', [sj.sub(sj.mul(sj.pi, half), a!)], { evaluate: false }) : undefined;
  }
}

// ---- sympy.core.function: expand ----------------------------------------------------------

/**
 * class MyClass(Expr):
 *     def _eval_expand_double(self, *, force=False, **hints):
 *         if not force and len(self.args) > 4: return self
 *         return self.func(*(self.args + self.args))
 */
class MyClass extends sj.ExtensionExpr {
  constructor(...args: sj.ExprLike[]) {
    super('MyClass', args.map((a) => sj.sympify(a)));
  }
  withArgs(args: readonly Expr[]): Expr {
    return new MyClass(...args);
  }
  override expandSelf(hint: string, hints: Readonly<Record<string, unknown>>): Expr | undefined {
    if (hint !== 'double') return undefined;
    if (!hints['force'] && this.args.length > 4) return this;
    return new MyClass(...this.args, ...this.args);
  }
}
const myA = () => new MyClass(1, 2, new MyClass(3, 4));
const myB = () => new MyClass(1, 2, 3, 4, 5);

// ---- sympy.core.sympify ---------------------------------------------------------------------

/** mpmath bitcount: the number of bits of |n|. */
const bitcount = (n: Expr): number => ((n as sj.Rational).p < 0n ? -(n as sj.Rational).p : (n as sj.Rational).p).toString(2).length;
/** ns = {}; exec('from sympy.core.evalf import bitcount', ns) */
const ns: Record<string, sj.ExprLike | ((...args: Expr[]) => sj.ExprLike)> = { bitcount };

/** class MyList1: __iter__ yields 1, 2; _sympy_ returns Matrix(self) */
class MyList1 {
  *[Symbol.iterator](): Generator<number> {
    yield 1;
    yield 2;
  }
  [sj.sympifyMethod](): sj.Matrix {
    return sj.Matrix.of([...this].map((v) => [v]));
  }
}
/** class MyList2 with converter[MyList2] = lambda x: Matrix(x) */
class MyList2 {
  *[Symbol.iterator](): Generator<number> {
    yield 1;
    yield 2;
  }
}
sj.converter.set(MyList2, (l: MyList2) => sj.Matrix.of([...l].map((v) => [v])));

// ---- sympy.simplify.simplify -------------------------------------------------------------

/**
 * def my_measure(expr):
 *     count = count_ops(expr, visual=True).subs(POW, 10)
 *     count = count.replace(Symbol, type(S.One))
 */
function myMeasure(e: Expr): Expr {
  const count = sj.subs(sj.countOps(e, { visual: true }), [[new sj.Sym('POW'), 10]]);
  return sj.replace(count, (u) => u instanceof sj.Sym, () => sj.S.One) as Expr;
}

/** A port, or one port per occurrence of a doctest source that occurs after different setup lines. */
/** The simplify docstring example with a custom measure that penalizes powers. */
function simplifyWithMeasure(): unknown {
  const [a, b] = sym('a b', { positive: true });
  const g = sj.add(sj.log(a!), sj.log(b!), sj.mul(sj.log(a!), sj.log(sj.pow(b!, -1))));
  return sj.simplify(g, { measure: myMeasure });
}

// ---- sympy.tensor.tensor: dict updates and commutation groups ------------------------

/** Lorentz, i0, i1 and repl = {Lorentz: diag(1, -1, -1, -1)} of the TensorHead docstring. */
function lorentzRepl() {
  const Lorentz = sj.TensorIndexType('Lorentz', { dummyName: 'L' });
  const [i0, i1] = sj.tensorIndices('i0:2', Lorentz) as [sj.TensorIndex, sj.TensorIndex];
  const repl = new Map<Expr, sj.ArrayInput>([[Lorentz, sj.Matrix.diag(1, -1, -1, -1)]]);
  return { Lorentz, i0, i1, repl };
}
/** G and GH do not commute with themselves and commute with each other (the TensorManager.set_comm docstring). */
function commSetup() {
  const Lorentz = sj.TensorIndexType('Lorentz');
  const [i0, i1] = sj.tensorIndices('i0:5', Lorentz) as [sj.TensorIndex, sj.TensorIndex];
  const A = sj.TensorHead('A', [Lorentz]);
  const G = sj.TensorHead('G', [Lorentz], sj.TensorSymmetry.noSymmetry(1), 'Gcomm');
  const GH = sj.TensorHead('GH', [Lorentz], sj.TensorSymmetry.noSymmetry(1), 'GHcomm');
  sj.TensorManager.setComm('Gcomm', 'GHcomm', 0);
  return { i0, i1, A, G, GH };
}

// ---- sympy.printing.printer: ModOp and the three wrong ways of printing its arguments
const [px, pm] = sym('x m') as [sj.Sym, sj.Sym];
/** class ModOp(Mod): def _latex(self, printer): a, b = [<print>(i) for i in self.args]; ... */
class ModOpNode extends sj.ExtensionExpr {
  constructor(
    readonly how: 'ok' | 'doprint' | 'str' | 'fresh',
    args: readonly Expr[],
  ) {
    super({ ok: 'ModOp', doprint: 'ModOpModeWrong', str: 'ModOpNestedWrong', fresh: 'ModOpSettingsWrong' }[how], args);
  }
  withArgs(args: readonly Expr[]): Expr {
    return new ModOpNode(this.how, args);
  }
  override printLatex(print: (e: Expr) => string): string {
    // printer._print(i), printer.doprint(i) (the outer mode applied again), str(i), LatexPrinter()._print(i)
    const each = { ok: print, doprint: (e: Expr) => sj.latex(e, { mode: 'inline' }), str: (e: Expr) => sj.str(e), fresh: (e: Expr) => sj.latex(e, {}) }[this.how];
    const [a, b] = this.args.map(each);
    return `\\operatorname{Mod}{\\left(${a}, ${b}\\right)}`;
  }
}
const modOp = (how: ModOpNode['how'], a: sj.ExprLike, b: sj.ExprLike): Expr => new ModOpNode(how, [sj.sympify(a), sj.sympify(b)]);

// ---- sympy.utilities.memoization: the doctest's memoized factorial after factorial(4) and factorial(3)
function memoFactorial(): sj.RecurrenceMemo<number> {
  const factorial = sj.recurrenceMemo([1])((n, prev) => n * prev[prev.length - 1]!);
  factorial(4);
  factorial(3);
  return factorial;
}

export const PORTS: Record<string, (() => unknown) | readonly (() => unknown)[]> = {
  // ---- sympy.matrices.sparsetools: s = lambda d: (1 + d)**2, a function of the position on the diagonal
  'sympy.matrices.sparsetools:banded(5, {0: s, 2: s, -2: 2})': () => {
    const s = (d: number) => sj.pow(sj.add(1, d), 2);
    return sj.banded(5, new Map<number, sj.BandedValue>([[0, s], [2, s], [-2, 2]]));
  },
  // ---- sympy.printing.printer: custom LaTeX of a node (SymPy's _latex(self, printer)); the subcomponents printed with
  // the printer (ok), anew with the settings (doprint: the mode applied again), as str, or with a fresh printer (settings lost)
  'sympy.printing.printer:print_latex(ModOp(x, m))': () => sj.printLatex(modOp('ok', px, pm)),
  "sympy.printing.printer:print_latex(ModOp(x, m), mode='inline')  # ok": () => sj.printLatex(modOp('ok', px, pm), { mode: 'inline' }),
  "sympy.printing.printer:print_latex(ModOpModeWrong(x, m), mode='inline')  # bad": () => sj.printLatex(modOp('doprint', px, pm), { mode: 'inline' }),
  'sympy.printing.printer:print_latex(ModOp(ModOp(x, m), Integer(7)))  # ok': () => sj.printLatex(modOp('ok', modOp('ok', px, pm), 7)),
  'sympy.printing.printer:print_latex(ModOpNestedWrong(ModOpNestedWrong(x, m), Integer(7)))  # bad': () => sj.printLatex(modOp('str', modOp('str', px, pm), 7)),
  'sympy.printing.printer:print_latex(ModOp(Float(1) * x, m), full_prec=True)  # ok': () => sj.printLatex(modOp('ok', sj.mul(new sj.Float(1), px), pm), { fullPrec: true }),
  'sympy.printing.printer:print_latex(ModOpSettingsWrong(Float(1) * x, m), full_prec=True)  # bad': () => sj.printLatex(modOp('fresh', sj.mul(new sj.Float(1), px), pm), { fullPrec: true }),
  // ---- sympy.printing.tableform: a TableForm object (t = TableForm([[5, 7], [4, 2], [10, 3]]), headings='automatic' for as_matrix)
  'sympy.printing.tableform:print(t.as_latex())': () => new sj.TableForm([[5, 7], [4, 2], [10, 3]]).asLatex(),
  'sympy.printing.tableform:t.as_matrix()': () => new sj.TableForm([[5, 7], [4, 2], [10, 3]], { headings: 'automatic' }).asMatrix(),
  // Symbol('') has no counterpart (a symbol has a name); a blank prints the same
  "sympy.printing.tableform:TableForm([[Symbol('.'*(j if not i%2 else 1)) for i in range(3)]\n           for j in range(4)], alignments='rcl')": () =>
    new sj.TableForm([0, 1, 2, 3].map((j) => [0, 1, 2].map((i) => new sj.Sym('.'.repeat(i % 2 ? 1 : j) || ' '))), { alignments: 'rcl' }),
  // ---- sympy.utilities.memoization: @recurrence_memo([1]) def factorial(n, prev): return n * prev[-1]; factorial(4); factorial(3)
  'sympy.utilities.memoization:factorial.cache_length() # cache length can be obtained': () => memoFactorial().cacheLength(),
  'sympy.utilities.memoization:factorial.fetch_item(slice(2, 4))': () => memoFactorial().fetchItem(2, 4),
  // ---- sympy.utilities.iterables: capture(lambda: pprint(2/x)) prints through the print function capture hands over
  'sympy.utilities.iterables:capture(lambda: pprint(2/x))': () => sj.capture((print) => print(sj.pretty(sj.mul(2, sj.pow(x, -1))))),
  // ---- sympy.tensor.tensor: Python dict updates (they return None) and the commutation groups of TensorManager
  // F = TensorHead('F', [Lorentz, Lorentz], TensorSymmetry.fully_symmetric(-2)) with the field-strength components
  'sympy.tensor.tensor:repl.update({F(-i0, -i1): [\n[0, Ex/c, Ey/c, Ez/c],\n[-Ex/c, 0, -Bz, By],\n[-Ey/c, Bz, 0, -Bx],\n[-Ez/c, -By, Bx, 0]]})': () => {
    const { Lorentz, i0, i1, repl } = lorentzRepl();
    const [Ex, Ey, Ez, Bx, By, Bz] = sym('E_x E_y E_z B_x B_y B_z') as [sj.Sym, sj.Sym, sj.Sym, sj.Sym, sj.Sym, sj.Sym];
    const [c] = sym('c', { positive: true }) as [sj.Sym];
    const F = sj.TensorHead('F', [Lorentz, Lorentz], sj.TensorSymmetry.fullySymmetric(-2));
    const e = (v: Expr) => sj.mul(v, sj.pow(c, -1));
    const neg = (v: Expr) => sj.neg(v);
    repl.set(F.at(i0.neg(), i1.neg()), [
      [0, e(Ex), e(Ey), e(Ez)],
      [neg(e(Ex)), 0, neg(Bz), By],
      [neg(e(Ey)), Bz, 0, neg(Bx)],
      [neg(e(Ez)), neg(By), Bx, 0],
    ]);
    return null;
  },
  // P = TensorHead('P', [Lorentz], TensorSymmetry.no_symmetry(1)); E, px, py, pz positive
  'sympy.tensor.tensor:repl.update({P(i0): [E, px, py, pz]})': () => {
    const { Lorentz, i0, repl } = lorentzRepl();
    const P = sj.TensorHead('P', [Lorentz], sj.TensorSymmetry.noSymmetry(1));
    const [E, px, py, pz] = sym('E p_x p_y p_z', { positive: true }) as [sj.Sym, sj.Sym, sj.Sym, sj.Sym];
    repl.set(P.at(i0), [E, px, py, pz]);
    return null;
  },
  "sympy.tensor.tensor:TensorManager.set_comm('Gcomm', 'GHcomm', 0)": () => (sj.TensorManager.setComm('Gcomm', 'GHcomm', 0), null),
  'sympy.tensor.tensor:(GH(i1)*G(i0)).canon_bp()': () => {
    const { i0, i1, G, GH } = commSetup();
    return sj.canonBp(sj.mul(GH.at(i1), G.at(i0)));
  },
  'sympy.tensor.tensor:(G(i1)*G(i0)).canon_bp()': () => {
    const { i0, i1, G } = commSetup();
    return sj.canonBp(sj.mul(G.at(i1), G.at(i0)));
  },
  'sympy.tensor.tensor:(G(i1)*A(i0)).canon_bp()': () => {
    const { i0, i1, A, G } = commSetup();
    return sj.canonBp(sj.mul(G.at(i1), A.at(i0)));
  },
  'sympy.core.expr:MyScalar().diff(MyScalar())': () => sj.diff(new MyScalar(), new MyScalar()),

  // DE = DifferentialExtension(log(x) + exp(x), x, handle_first='exp')
  "sympy.integrals.risch:DE.indices('log')": () => new JsList(new DifferentialExtension(sj.add(sj.log(x), sj.exp(x)), x, { handleFirst: 'exp' }).indices('log').map((i) => sj.Rational.of(i))),
  "sympy.integrals.risch:DE.indices('exp')": () => new JsList(new DifferentialExtension(sj.add(sj.log(x), sj.exp(x)), x, { handleFirst: 'exp' }).indices('exp').map((i) => sj.Rational.of(i))),

  // the parameter objects of hyperexpand (SymPy-internal classes, ported as experimental ones)
  'sympy.simplify.hyperexpand:Hyper_Function(ap, bq).build_invariants()': () => {
    const [g, a, b] = new sj.Hyper_Function([half, sj.Rational.of(1n, 3n), sj.Rational.of(-1n, 2n), -2], [1, 2]).buildInvariants();
    const tr = (l: [Expr, number][]) => new JsTuple(l.map(([m, n]) => new JsTuple([m, sj.Rational.of(n)])));
    return new JsTuple([sj.Rational.of(g), tr(a), tr(b)]);
  },
  'sympy.simplify.hyperexpand:G_Function(a, b, [2], [y]).compute_buckets()': () => {
    const t = sj.Rational.of(3n, 2n);
    const bs = new sj.G_Function([1, 3, 2, t], [sj.add(1, y), y, 2, sj.add(y, 3)], [2], [y]).computeBuckets();
    return new JsTuple(bs.map((m) => new JsDict([...m].map(([k, v]) => [k, new JsList(v)] as const))));
  },
  // op = Operator(); op._poly = Poly(x**2 + z*x + y, x)
  'sympy.simplify.hyperexpand:op.apply(z**7, lambda f: f.diff(z))': () =>
    new sj.Operator(sj.add(sj.pow(x, 2), sj.mul(z, x), y), x).apply(sj.pow(z, 7), (f) => sj.diff(f, z)),
  // inc = lambda x: x + 1; dec = lambda x: x - 1
  // rl = minimize(inc, dec); rl(4) and rl = minimize(inc, dec, objective=lambda x: -x); rl(4)
  'sympy.strategies.core:rl(4)': [
    () => sj.minimize((v: Expr) => sj.add(v, 1), (v: Expr) => sj.sub(v, 1))(sj.Rational.of(4)),
    () => sj.minimize((v: Expr) => sj.add(v, 1), (v: Expr) => sj.sub(v, 1), { objective: (v: Expr) => sj.mul(-1, v) })(sj.Rational.of(4)),
  ],
  // key = lambda x: x.as_coeff_Mul()[1]; count = lambda x: x.as_coeff_Mul()[0]
  // combine = lambda cnt, arg: cnt * arg; rl = glom(key, count, combine)
  'sympy.strategies.rl:rl(Add(x, -x, 3*x, 2, 3, evaluate=False))': () =>
    sj.glom(
      (v) => sj.splitCoeff(v)[1],
      (v) => sj.splitCoeff(v)[0],
      (cnt, arg) => sj.mul(cnt, arg),
    )(new sj.Add([x, sj.mul(-1, x), sj.mul(3, x), sj.Rational.of(2), sj.Rational.of(3)])),
  // from sympy.unify.core import partition (an internal helper of the unification algorithm)
  'sympy.unify.core:partition((10, 20, 30, 40), [[0, 1, 2], [3]])': () =>
    new JsTuple(unifyPartition([10, 20, 30, 40].map((i) => sj.Rational.of(i)), [[0, 1, 2], [3]]).map((p) => new JsTuple(p))),
  'sympy.core.expr:MySymbol().diff(MySymbol())': () => sj.diff(new MySymbol(), new MySymbol()),

  // eye(1) is a mutable matrix, S(eye(1)) its immutable copy
  'sympy.core.basic:Basic.is_same(eye(1), S(eye(1)))': () => sj.isSame(sj.MutableDenseMatrix.eye(1), sj.sympify(sj.MutableDenseMatrix.eye(1))),
  'sympy.core.basic:Basic(a + x, x).matches(Basic(a + b + c, b + c))': () => {
    const [a, b, c] = sym('a b c');
    const w = new sj.Wild('x');
    const m = sj.match(sj.Basic(sj.add(a!, b!, c!), sj.add(b!, c!)), sj.Basic(sj.add(a!, w), w));
    return m instanceof Map ? new JsDict([...m]) : null;
  },
  'sympy.core.basic:(x*y).replace(Mul, lambda *args: sin(2*Mul(*args)))': () =>
    sj.replace(sj.mul(x, y), { type: 'Mul' }, (...args: Expr[]) => sj.sin(sj.mul(2, sj.mul(...args)))),
  'sympy.core.basic:(1 + x**(1 + y)).replace(\nlambda x: x.is_Pow and x.exp.is_Add and x.exp.args[0] == 1,\nlambda x: x.base**(1 - (x.exp - 1)))': () =>
    sj.replace(
      sj.add(1, sj.pow(x, sj.add(1, y))),
      (e) => e instanceof sj.Pow && e.exp instanceof sj.Add && e.exp.args[0]!.key === sj.S.One.key,
      (e) => sj.pow((e as sj.Pow).base, sj.sub(1, sj.sub((e as sj.Pow).exp, 1))),
    ),
  'sympy.core.basic:MySin(MySin(x)).rewrite(cos)': () => sj.rewrite(new MySin(new MySin(x)), 'cos'),
  'sympy.core.basic:MySin(x).rewrite(sqrt)': () => sj.rewrite(new MySin(x), 'sqrt'),
  'sympy.core.basic:MySin(x).rewrite(cos)': () => sj.rewrite(new MySinCos(x), 'cos'),

  'sympy.core.function:(1 + 42**f(x).diff(x)).replace(lambda arg: arg.is_Derivative,\n    lambda arg: arg.as_finite_difference())': () => {
    const f = sj.SymFunction('f');
    return sj.replace(
      sj.add(1, sj.pow(42, sj.diff(f(x), x))),
      (e) => e instanceof sj.Derivative,
      (e) => sj.asFiniteDifference(e as sj.Derivative),
    );
  },
  // the combined series objects of sympy.series.formal (FormalPowerSeriesProduct, ...Compose, ...Inverse)
  'sympy.series.formal:f1.product(f2, x).truncate(4)': () => sj.fps(sj.sin(x), x).product(sj.fps(sj.exp(x), x), x).truncate(4),
  'sympy.series.formal:f1.compose(f2, x).truncate()': () => sj.fps(sj.exp(x), x).compose(sj.fps(sj.sin(x), x), x).truncate(),
  'sympy.series.formal:f1.compose(f2, x).truncate(8)': () => sj.fps(sj.exp(x), x).compose(sj.fps(sj.sin(x), x), x).truncate(8),
  'sympy.series.formal:f1.inverse(x).truncate()': () => sj.fps(sj.exp(x), x).inverse().truncate(),
  'sympy.series.formal:f2.inverse(x).truncate(8)': () => sj.fps(sj.cos(x), x).inverse().truncate(8),
  // s = fourier_series(x**2, (x, -pi, pi)): a series with the argument shifted or scaled is not one of a function
  'sympy.series.fourier:s.shiftx(1).truncate()': () => sj.fourierSeries(sj.pow(x, 2), x).shiftx(1).truncate(),
  'sympy.series.fourier:s.scalex(2).truncate()': () => sj.fourierSeries(sj.pow(x, 2), x).scalex(2).truncate(),

  'sympy.core.function:a.expand(double=True)': () => sj.expand(myA(), { double: true }),
  'sympy.core.function:a.expand(double=True, deep=False)': () => sj.expand(myA(), { double: true, deep: false }),
  'sympy.core.function:b.expand(double=True)': () => sj.expand(myB(), { double: true }),
  'sympy.core.function:b.expand(double=True, force=True)': () => sj.expand(myB(), { double: true, force: true }),

  'sympy.core.exprtools:Factors((x*y**2).as_powers_dict()).as_expr()': () => new sj.Factors(sj.asPowersDict(sj.mul(x, sj.pow(y, 2)))).asExpr(),
  'sympy.core.exprtools:a.div(a)': () => {
    const a = new sj.Factors(sj.asPowersDict(sj.mul(x, sj.pow(y, 2))));
    return a.div(a);
  },
  'sympy.core.exprtools:a.div(x*z)': () => new sj.Factors(sj.asPowersDict(sj.mul(x, sj.pow(y, 2)))).div(sj.mul(x, z)),
  'sympy.core.exprtools:a.div(x/z)': () => new sj.Factors(sj.asPowersDict(sj.mul(x, sj.pow(y, 2)))).div(sj.mul(x, sj.pow(z, -1))),
  'sympy.core.exprtools:Factors(2**(2*x + 2)).div(S(8))': () => new sj.Factors(sj.pow(2, sj.add(sj.mul(2, x), 2))).div(8),

  // class Something(dict): pass
  'sympy.core.sympify:sympify(Something())': () => {
    class Something extends Map<unknown, unknown> {}
    return sj.sympify(new Something());
  },
  'sympy.core.sympify:sympify(s, locals=ns)': () => sj.parse('bitcount(42)', { locals: ns }),
  'sympy.core.sympify:ns.update(dict(O=Symbol("O")))  # method 3': () => {
    Object.assign(ns, { O: new sj.Sym('O') });
    return undefined;
  },
  'sympy.core.sympify:sympify("O + 1", locals=ns)': () => sj.parse('O + 1', { locals: { ...ns, O: new sj.Sym('O') } }),
  'sympy.core.sympify:sympify(MyList1())': () => sj.sympify(new MyList1()),
  'sympy.core.sympify:sympify(MyList2())': () => sj.sympify(new MyList2() as never),

  'sympy.functions.elementary.miscellaneous:(x + 1/sqrt(x)).find(lambda i: i.is_Pow and abs(i.exp) is S.Half)': () =>
    new JsSet(sj.find(sj.add(x, sj.pow(sj.sqrt(x), -1)), (e) => e instanceof sj.Pow && sj.abs(e.exp).key === half.key)),

  'sympy.simplify.simplify:simplify(g, measure=my_measure)': () => simplifyWithMeasure(),
  // the docstring of simplify, repeated in BasisDependent.simplify
  'sympy.vector.basisdependent:simplify(g, measure=my_measure)': () => simplifyWithMeasure(),

  // DMP([ZZ(1), ZZ(1)], ZZ) is the dense representation [1, 1]
  'sympy.polys.polytools:a.per(DMP([ZZ(1), ZZ(1)], ZZ), gens=[y])': () => sj.Poly.from(sj.add(sj.pow(x, 2), 1)).per([1, 1], { gens: [y] }),
  // def func(k, coeff): k = k[0]; return coeff//10**(2-k)
  'sympy.polys.polytools:Poly(x**2 + 20*x + 400).termwise(func)': () =>
    sj.Poly.from(sj.add(sj.pow(x, 2), sj.mul(20, x), 400)).termwise((k, coeff) => sj.floor(sj.mul(coeff, sj.pow(10, -(2 - k[0]!))))),
  // class SexyPrimePredicate(Predicate): name = "sexyprime"; registered for (Integer, Integer)
  'sympy.assumptions.assume:ask(Q.sexyprime(5, 11))': () => {
    const sexyprime = sj.Predicate('sexyprime', (_e, assumptions, [a, b]) =>
      a instanceof sj.Rational && b instanceof sj.Rational && a.q === 1n && b.q === 1n
        ? sj.ask(sj.Q.prime(a), assumptions) === true && sj.ask(sj.Q.prime(b), assumptions) === true && (b.p - a.p === 6n || a.p - b.p === 6n)
        : 'unknown',
    );
    return sj.ask(sexyprime(5, 11));
  },
  // Q.P = Predicate("P")
  'sympy.assumptions.assume:Q.P(1)': () => sj.Predicate('P')(1),
  // class MyOp(Basic): pass
  'sympy.utilities.iterables:flatten([MyOp(S(1), MyOp(S(2), S(3)))], cls=MyOp)': () => {
    class MyOp extends sj.BasicNode {
      constructor(args: readonly Expr[]) {
        super(args, 'MyOp');
      }
    }
    const one = sj.Rational.of(1n);
    return sj.flatten([new MyOp([one, new MyOp([sj.Rational.of(2n), sj.Rational.of(3n)])])], { cls: MyOp });
  },
  // sift(..., lambda x: x.as_base_exp()[0]); the dict is a defaultdict(list)
  'sympy.utilities.iterables:sift([sqrt(x), exp(x), (y**x)**2],\n     lambda x: x.as_base_exp()[0])': () =>
    sj.sift([sj.sqrt(x), sj.exp(x), sj.pow(sj.pow(y, x), 2)], (e: Expr) => sj.asBaseExp(e)[0]),
  // F = lambda x: (2048*pow(x, 2, n) + 32767) % n
  'sympy.ntheory.factor_:pollard_rho(n, F=F)': () => {
    const n = 16843009n;
    return sj.pollardRho(n, { F: (v: bigint) => (2048n * ((v * v) % n) + 32767n) % n });
  },
  // Permutation.from_sequence('SymPy', key=lambda x: x.lower())
  "sympy.combinatorics.permutations:Permutation.from_sequence('SymPy', key=lambda x: x.lower())": () =>
    sj.Permutation.fromSequence('SymPy', (c: string) => c.toLowerCase()),
  // G = PermutationGroup(Cycle(2, 3)(4, 5), Cycle(1, 2, 3, 4, 5)); p2 = Permutation(Cycle(1, 2, 3))
  'sympy.combinatorics.permutations:G.contains(p2,strict=False)': () => {
    const gens = [new sj.Permutation(new sj.Cycle(2, 3).call(4, 5) as sj.Cycle), new sj.Permutation(new sj.Cycle(1, 2, 3, 4, 5))];
    const degree = Math.max(...gens.map((g) => g.size));
    const key = (q: sj.Permutation) => new sj.Permutation(q, { size: degree }).arrayForm.join(',');
    const seen = new Map<string, sj.Permutation>([[key(new sj.Permutation([], { size: degree })), new sj.Permutation([], { size: degree })]]);
    const queue = [...seen.values()];
    while (queue.length) {
      const q = queue.pop()!;
      for (const g of gens) {
        const r = q.mul(g);
        if (!seen.has(key(r))) {
          seen.set(key(r), r);
          queue.push(r);
        }
      }
    }
    // strict=False: the permutation is resized to the degree of the group
    return seen.has(key(new sj.Permutation(new sj.Cycle(1, 2, 3))));
  },

  // ---- combinatorics: objects the extractor cannot serialize ----
  'sympy.combinatorics.partitions:IntegerPartition([1]*3 + [2] + [3]*4).as_dict()': () => new sj.IntegerPartition([1, 1, 1, 2, 3, 3, 3, 3]).asDict(),
  // superset = [1, 3, 2, 5, 4]
  'sympy.combinatorics.subsets:Subset.subset_indices([3, 2, 1], superset)': () => sj.Subset.subsetIndices([3, 2, 1], [1, 3, 2, 5, 4]),
  'sympy.combinatorics.subsets:Subset.subset_indices([1, 6], superset)': () => sj.Subset.subsetIndices([1, 6], [1, 3, 2, 5, 4]),
  'sympy.combinatorics.subsets:Subset.subset_indices([], superset)': () => sj.Subset.subsetIndices([], [1, 3, 2, 5, 4]),
  // a = Prufer([[0, 1], [0, 2], [0, 3]])
  'sympy.combinatorics.prufer:a.prufer_rank()': () =>
    new sj.Prufer([
      [0, 1],
      [0, 2],
      [0, 3],
    ]).pruferRank(),

  // ---- sympy.simplify.epathtools: EPath methods ----
  // path = EPath("/*/[0]/Symbol"); expr = [((x, 1), 2), ((3, y), z)]
  'sympy.simplify.epathtools:path.apply(expr, lambda expr: expr**2)': () =>
    sj.epath('/*/[0]/Symbol').apply(
      [
        [[x, 1], 2],
        [[3, y], z],
      ],
      (e: Expr) => sj.pow(e, 2),
    ),
  // path = EPath("/*/*/Symbol"); expr = t + sin(x + 1) + cos(x + y + E)
  'sympy.simplify.epathtools:path.apply(expr, lambda expr: 2*expr)': () =>
    sj.epath('/*/*/Symbol').apply(sj.add(new sj.Sym('t'), sj.sin(sj.add(x, 1)), sj.cos(sj.add(x, y, sj.E))), (e: Expr) => sj.mul(2, e)),
  // the two occurrences follow the two setups above
  'sympy.simplify.epathtools:path.select(expr)': [
    () =>
      sj.epath('/*/[0]/Symbol').select([
        [[x, 1], 2],
        [[3, y], z],
      ]),
    () => sj.epath('/*/*/Symbol').select(sj.add(new sj.Sym('t'), sj.sin(sj.add(x, 1)), sj.cos(sj.add(x, y, sj.E)))),
  ],

  // ---- sympy.polys.numberfields.minpoly: the domain QQ.algebraic_field(sqrt(2)) ----
  'sympy.polys.numberfields.minpoly:minimal_polynomial(sqrt(2), x, domain=QQ.algebraic_field(sqrt(2)))': () => sj.minimalPolynomial(sj.sqrt(2), x, { domain: 'QQ<sqrt(2)>' }),

  // ---- sympy.simplify.fu: a measure given as a lambda ----
  'sympy.simplify.fu:fu(sin(x)/cos(x), measure=lambda x: -x.count_ops()) # maximize op count': () =>
    sj.fu(sj.mul(sj.sin(x), sj.pow(sj.cos(x), -1)), { measure: (e: Expr) => -sj.countOps(e) }),

  // ---- sympy.sets: Range and DisjointUnion objects (the extractor does not serialize them) ----
  'sympy.sets.fancysets:Range(0, 10, 2).intersect(Interval(3, 7))': () => sj.Intersection(sj.Range.of(0, 10, 2), sj.Interval.of(3, 7)),
  'sympy.sets.fancysets:Range(3).intersect(Interval(4, oo))': () => sj.Intersection(sj.Range.of(0, 3), sj.Interval.of(4, sj.oo)),
  'sympy.sets.fancysets:Range(3).intersect(Range(4, oo))': () => sj.Intersection(sj.Range.of(0, 3), sj.Range.of(4, sj.oo)),
  // A = FiniteSet(1, 2, 3); B = Interval(0, 5); C = FiniteSet(x, y, z)
  'sympy.sets.sets:DisjointUnion(A, B).rewrite(Union)': () => sj.DisjointUnion(sj.FiniteSet.of(1, 2, 3), sj.Interval.of(0, 5)).rewriteAsUnion(),
  'sympy.sets.sets:DisjointUnion(C, C).rewrite(Union)': () => sj.DisjointUnion(sj.FiniteSet.of(x, y, z), sj.FiniteSet.of(x, y, z)).rewriteAsUnion(),

  // ---- sympy.core.containers: D = Dict({1: 'one', 2: 'two'}) (strings are sympified to symbols) ----
  "sympy.core.containers:D.has(Symbol('one')) # searches keys and values": () =>
    sj.Dict(new Map<sj.ExprLike, sj.ExprLike>([[1, sj.symbol('one')], [2, sj.symbol('two')]])).has(sj.symbol('one')),

  // ---- sympy.solvers.diophantine.diophantine: equation-type objects and DiophantineSolutionSet ----
  ...diophantinePorts(),
};

/** The doctests of the Diophantine equation classes, with the objects their setup lines create. */
function diophantinePorts(): Record<string, () => unknown> {
  const m = 'sympy.solvers.diophantine.diophantine:';
  const P = (s: string) => sj.parse(s);
  const [t, u] = sym('t u');
  const pq = (a: sj.ExprLike, b: sj.ExprLike) => [a, b];
  // s1 = DiophantineSolutionSet([x, y], [t, u]) and so on
  const dss = () => new sj.DiophantineSolutionSet([x, y], [t!, u!]);
  const s3 = () => {
    const s = dss();
    s.add([sj.pow(t!, 2), sj.add(t!, u!)]);
    return s;
  };
  return Object.fromEntries(
    Object.entries({
      'b1.matches()': () => new sj.BinaryQuadratic(P('x**3 + y**2 + 1')).matches(),
      'b2.matches()': () => new sj.BinaryQuadratic(P('x**2 + y**2 + 2*x + 2*y + 2')).matches(),
      'b2.solve()': () => new sj.BinaryQuadratic(P('x**2 + y**2 + 2*x + 2*y + 2')).solve(),
      'c1.matches()': () => new sj.CubicThue(P('x**3 + y**2 + 1')).matches(),
      's1.add((2, 3))': () => dss().add(pq(2, 3)),
      's1.add((-1, u))': () => dss().add(pq(-1, u!)),
      's2.add((3, 4))': () => dss().add(pq(3, 4)),
      's3.add((t**2, t + u))': () => s3().add([sj.pow(t!, 2), sj.add(t!, u!)]),
      's3.subs({t: 2, u: 3})': () => s3().subs(new Map([[t!, 2], [u!, 3]])),
      's3.subs(t, -1)': () => s3().subs(t!, -1),
      's3.subs(t, 3)': () => s3().subs(t!, 3),
      'GeneralPythagorean(a**2 + b**2 + c**2 - d**2).solve()': () => new sj.GeneralPythagorean(P('a**2 + b**2 + c**2 - d**2')).solve(),
      'GeneralPythagorean(9*a**2 - 4*b**2 + 16*c**2 + 25*d**2 + e**2).solve(parameters=[x, y, z, t])': () =>
        new sj.GeneralPythagorean(P('9*a**2 - 4*b**2 + 16*c**2 + 25*d**2 + e**2')).solve({ parameters: [x, y, z, t!] }),
      'GeneralSumOfEvenPowers(a**4 + b**4 - (2**4 + 3**4)).solve()': () => new sj.GeneralSumOfEvenPowers(P('a**4 + b**4 - (2**4 + 3**4)')).solve(),
      'GeneralSumOfSquares(a**2 + b**2 + c**2 + d**2 + e**2 - 2345).solve()': () => new sj.GeneralSumOfSquares(P('a**2 + b**2 + c**2 + d**2 + e**2 - 2345')).solve(),
      'HomogeneousTernaryQuadratic(x**2 + y**2 - 3*z**2 + x*y).solve()': () => new sj.HomogeneousTernaryQuadratic(P('x**2 + y**2 - 3*z**2 + x*y')).solve(),
      'HomogeneousTernaryQuadratic(3*x**2 + y**2 - 3*z**2 + 5*x*y + y*z).solve()': () => new sj.HomogeneousTernaryQuadratic(P('3*x**2 + y**2 - 3*z**2 + 5*x*y + y*z')).solve(),
      'HomogeneousTernaryQuadraticNormal(4*x**2 - 5*y**2 + z**2).solve()': () => new sj.HomogeneousTernaryQuadraticNormal(P('4*x**2 - 5*y**2 + z**2')).solve(),
      'l1.matches() # is this equation linear': () => new sj.Linear(P('2*x - 3*y - 5')).matches(),
      'l1.solve() # solves equation 2*x - 3*y - 5 == 0': () => new sj.Linear(P('2*x - 3*y - 5')).solve(),
      'Linear(2*x - 3*y - 4*z -3).solve()': () => new sj.Linear(P('2*x - 3*y - 4*z -3')).solve(),
      'Univariate((x - 2)*(x - 3)**2).solve() # solves equation (x - 2)*(x - 3)**2 == 0': () => new sj.Univariate(P('(x - 2)*(x - 3)**2')).solve(),
    }).map(([k, f]) => [m + k, f]),
  );
}

// ---- sympy.crypto.crypto: round_trip is a Python lambda of the doctest (decipher_bifid5 of encipher_bifid5)
PORTS['sympy.crypto.crypto:round_trip(msg.replace("J", j), key).replace(j, "J")'] = () => sj.decipherBifid5(sj.encipherBifid5('JOSIE'.replace('J', 'QIQ'), 'a'), 'a').replace('QIQ', 'J');
