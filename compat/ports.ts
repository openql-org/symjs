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
import { JsDict, JsSet } from './harness';

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

export const PORTS: Record<string, () => unknown> = {
  'sympy.core.expr:MyScalar().diff(MyScalar())': () => sj.diff(new MyScalar(), new MyScalar()),
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
    const f = sj.Function('f');
    return sj.replace(
      sj.add(1, sj.pow(42, sj.diff(f(x), x))),
      (e) => e instanceof sj.Derivative,
      (e) => sj.asFiniteDifference(e as sj.Derivative),
    );
  },
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

  'sympy.simplify.simplify:simplify(g, measure=my_measure)': () => {
    const [a, b] = sym('a b', { positive: true });
    const g = sj.add(sj.log(a!), sj.log(b!), sj.mul(sj.log(a!), sj.log(sj.pow(b!, -1))));
    return sj.simplify(g, { measure: myMeasure });
  },

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
};
