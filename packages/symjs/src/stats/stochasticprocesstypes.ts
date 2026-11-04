// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (sympy/stats/stochastic_process_types.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License.

/**
 * @file SymPy sympy.stats.stochastic_process_types: stochastic processes
 * (discrete and continuous Markov chains, the Bernoulli, Poisson, Wiener
 * and gamma processes), their random indexed symbols and the queries of
 * probabilities and expectations on them.
 *
 * A discrete-time process is indexed with `X.at(n)` (SymPy `X[n]`) and a
 * continuous-time one is applied with `X.call(t)` (SymPy `X(t)`). The
 * processes are expression nodes (`DiscreteMarkovChainNode`, ...) that can
 * be called like SymPy's constructors (`DiscreteMarkovChain('Y', [0, 1],
 * T)`). The Markov chains derive from MarkovProcess (SymPy also derives
 * them from DiscreteTimeStochasticProcess and
 * ContinuousTimeStochasticProcess). Sampling is not ported.
 */

import { BoolAtom, Dummy, Expr, ExtensionExpr, Float, Rational, Rel, S, Sym, UndefFn } from '../core/nodes';
import type { ExprLike, RelOp } from '../core/nodes';
import { add, exp, mul, pow, sqrt, sub, sympify } from '../core/ops';
import { Eq, Ge, Gt, Le, Lt, rel, piecewise } from '../core/logic';
import { BoolOp, and } from '../core/boolalg';
import { Lambda } from '../core/lambda';
import { Sum } from '../core/concrete';
import { Indexed } from '../core/indexed';
import { xreplace } from '../core/traverse';
import { doit } from '../calculus/doit';
import { TupleNode } from '../core/containers';
import { callableClass } from '../core/callable';
import { NonSquareMatrixError, NotImplementedError } from '../core/errors';
import { at, cast, defined, expectType, first } from '../core/guard';
import { igcd } from '../core/numberutils';
import { isIntegerQ, isNonNegative } from '../core/assumptions';
import {
  EmptySet,
  FiniteSet,
  Integers,
  Naturals0,
  Range,
  Reals,
  SetExpr,
  asRelational,
  complement,
  conditionSet,
  Contains,
  containsQ,
  finiteSet,
  inf,
  interval,
  intersection,
  isSubset,
  range,
  sup,
  union,
} from '../sets/sets';
import { asSet } from '../solvers/inequalities';
import { linsolve } from '../solvers/public';
import { abs } from '../functions/elementary/elementary';
import { ceiling, factorial, gamma as gammaFn } from '../functions/special/special';
import { stronglyConnectedComponents } from '../utilities/iterables';
import { Matrix } from '../matrices/matrix';
import { isDiagonalizable, diagonalize } from '../matrices/linalg';
import { ImmutableMatrixNode, MatrixExpr, MatrixSymbolNode } from '../matrices/expressions/matexpr';
import { Density, RandomIndexedSymbol, RandomSymbol, dependent, given, isRandom, pspace, randomSymbols, symbolConverter, valueCheck } from './rv';
import type { ComputeOptions, Distribution } from './rv';
import { ProbabilityNode, makeExpectation } from './symbolicprobability';
import { JointDistribution } from './jointrv';
import { JointDistributionHandmade } from './jointrvtypes';
import { Bernoulli, BernoulliDistribution } from './frvtypes';
import { Poisson, PoissonDistribution } from './drvtypes';
import { Gamma, GammaDistribution, Normal, NormalDistribution } from './crvtypes';
import { StochasticPSpace, UnspecifiedDistribution } from './stochasticprocess';

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/** A state space given as an array or a set (SymPy list, tuple, set or Set). */
export type StateSpaceInput = readonly (ExprLike | string)[] | SetExpr | TupleNode;

/** A transition or generator matrix (SymPy Matrix, ImmutableMatrix or MatrixSymbol). */
export type TransitionMatrixInput = Matrix | ImmutableMatrixNode | MatrixSymbolNode;

/** The JS integer of an integer expression. */
const toNumber = (e: Expr): number => Number(expectType(e, (x): x is Rational => x instanceof Rational, 'integer').p);

/** The elements of a finite set, a concrete Range or a Tuple (SymPy iteration). */
function elements(s: Expr): Expr[] {
  if (s === EmptySet) return [];
  if (s instanceof TupleNode || s instanceof FiniteSet) return [...s.args];
  const r = cast(s, Range, 'iterable set');
  const n = toNumber(r.size);
  return Array.from({ length: n }, (_, i) => r.at(i));
}

/** The number of elements (SymPy len). */
const size = (s: Expr): number => elements(s).length;

/** SymPy _set_converter: a list or tuple as a FiniteSet; a Set is kept. */
export function setConverter(itr: unknown): SetExpr {
  if (Array.isArray(itr)) return finiteSet(...itr.map(toExprArg));
  if (!(itr instanceof SetExpr)) throw new TypeError(`${String(itr)} is not an instance of list/tuple/set.`);
  return itr;
}

/** SymPy _sym_sympify: a string is a symbol. */
const symSympify = (arg: ExprLike | string): Expr => (typeof arg === 'string' ? new Sym(arg) : sympify(arg));

/** An element of a state space given as a JS value (a string is a symbol). */
function toExprArg(x: unknown): Expr {
  if (typeof x === 'string' || typeof x === 'number' || typeof x === 'bigint' || x instanceof Expr) return symSympify(x);
  throw new TypeError(`${String(x)} is not a state`);
}

/** SymPy _state_converter: the states as a Tuple (a symbolic Range is kept). */
function stateConverter(itr: unknown): TupleNode | Range {
  const conv = (xs: readonly unknown[]): TupleNode => new TupleNode(xs.map(toExprArg));
  if (itr instanceof TupleNode || itr instanceof FiniteSet) return conv(itr.args);
  if (Array.isArray(itr)) {
    if (new Set(itr.map((x) => (typeof x === 'string' ? `'${x}` : toExprArg(x).key))).size !== itr.length) throw new RangeError('The state space must have unique elements.');
    return conv(itr);
  }
  if (itr instanceof Range) {
    try {
      return conv(elements(itr));
    } catch {
      return itr;
    }
  }
  throw new TypeError(`${String(itr)} is not an instance of list/tuple/set/Range/Tuple/FiniteSet.`);
}

/** SymPy _matrix_checks: a square matrix (a Matrix becomes immutable). */
function matrixChecks(matrix: unknown): ImmutableMatrixNode | MatrixSymbolNode {
  const m = matrix instanceof Matrix ? new ImmutableMatrixNode(matrix) : matrix;
  if (!(m instanceof ImmutableMatrixNode || m instanceof MatrixSymbolNode)) throw new TypeError('Transition probabilities either should be a Matrix or a MatrixSymbol.');
  const [r, c] = m.shape;
  if (r.key !== c.key) throw new NonSquareMatrixError(`${m.toString()} is not a square matrix`);
  return m;
}

/** The number of elements of a state space (SymPy len, or ceiling((stop - start)/step) of a Range). */
const stateCount = (s: TupleNode | Range): Expr => (s instanceof Range ? ceiling(mul(sub(s.stop, s.start), pow(s.step, -1))) : Rational.of(s.args.length));

/** The value is exactly zero (SymPy x == 0 of a number). */
const isZeroNumber = (e: Expr): boolean => (e instanceof Rational || e instanceof Float) && e.isZero;

/** SymPy a < b for numbers (the relation evaluates to true). */
const lessThan = (a: Expr, b: Expr): boolean => Lt(a, b) === S.true;

/** SymPy expr.atoms(RandomIndexedSymbol), in the order they are found. */
function indexedSymbolsOf(e: Expr): RandomIndexedSymbol[] {
  const out = new Map<string, RandomIndexedSymbol>();
  const go = (x: Expr): void => {
    if (x instanceof RandomIndexedSymbol) out.set(x.key, x);
    else x.args.forEach(go);
  };
  go(e);
  return [...out.values()];
}

/** The time of a random indexed symbol (SymPy rv.key). */
const keyOf = (e: Expr): Expr => cast(e, RandomIndexedSymbol, 'random indexed symbol').indexKey;

/** The expression contains a Probability (SymPy expr.has(Probability)). */
const hasProbability = (e: Expr): boolean => e instanceof ProbabilityNode || e.args.some(hasProbability);

/** The relation with its sides in their order (SymPy type(condition)(lhs, rhs)). */
const relOf = (r: Rel, lhs: Expr, rhs: Expr): Expr => rel(r.op, lhs, rhs);

/** A boolean operation of the kind (SymPy isinstance(x, And), ...). */
const isOp = (e: Expr | undefined, op: 'And' | 'Or' | 'Not'): e is BoolOp => e instanceof BoolOp && e.op === op;

/** A relational or boolean (SymPy isinstance(x, (Relational, Boolean))). */
const isBooleanLike = (e: Expr): boolean => e instanceof Rel || e instanceof BoolOp || e instanceof BoolAtom || e instanceof Contains || e instanceof TransitionMatrixOfNode || e instanceof StochasticStateSpaceOfNode;

/** The process of a random indexed symbol (SymPy rv.pspace.process). */
const processOf = (rv: Expr): StochasticProcess => cast(cast(cast(rv, RandomIndexedSymbol).pspace, StochasticPSpace, 'stochastic space').process, StochasticProcess, 'process');

/** The process of a random indexed symbol that has simple random symbols. */
const simpleProcessOf = (rv: Expr): StochasticProcess & SimpleRv => expectType(processOf(rv), (p): p is StochasticProcess & SimpleRv => p instanceof StochasticProcess && 'simpleRv' in p, 'process');

/** The value at the time of a continuous-time process (SymPy process(time)). */
const callAt = (rv: Expr, time: Expr): RandomIndexedSymbol => processOf(rv).call(time);

// ---------------------------------------------------------------------------
// Stochastic processes
// ---------------------------------------------------------------------------

/**
 * SymPy StochasticProcess(sym, state_space=S.Reals): the base class of the
 * stochastic processes (`new StochasticProcess([sym, stateSpace])`).
 */
export class StochasticProcess extends ExtensionExpr {
  constructor(args: readonly Expr[], name = 'StochasticProcess') {
    super(name, [symbolConverter(at(args, 0)), ...args.slice(1)]);
  }
  withArgs(args: readonly Expr[]): Expr {
    return cast(Reflect.construct(this.constructor, [args]), Expr);
  }
  /** The set of the times (SymPy index_set). */
  get indexSet(): SetExpr {
    return Reals;
  }
  /** SymPy symbol. */
  get symbol(): Sym {
    return cast(at(this.args, 0), Sym);
  }
  /** The values the process takes (SymPy state_space). */
  get stateSpace(): SetExpr {
    const s = at(this.args, 1);
    if (s instanceof TupleNode) return finiteSet(...s.args);
    return cast(s, SetExpr, 'state space');
  }
  /** The distribution at a time (SymPy distribution(key)): unspecified here. */
  distribution(_key?: Expr): Distribution {
    return new UnspecifiedDistribution();
  }
  /** The density of a random indexed symbol (SymPy density(x)): unspecified here. */
  density(_x: Expr): Expr {
    return new Density([]);
  }
  /** SymPy X(t) of a continuous-time process. */
  call(_time: ExprLike): RandomIndexedSymbol {
    throw new NotImplementedError('Use [] for indexing discrete time stochastic process.');
  }
  /** SymPy X[n] of a discrete-time process. */
  at(_time: ExprLike): RandomIndexedSymbol {
    throw new NotImplementedError('Use () for indexing continuous time stochastic process.');
  }
  /** SymPy probability(condition, given_condition, evaluate). */
  probability(_condition: Expr, _givenCondition?: Expr, _opts?: ComputeOptions): Expr {
    throw new NotImplementedError('probability queries are not implemented for this process');
  }
  /** SymPy expectation(condition, given_condition). */
  expectation(_expr: Expr, _condition?: Expr, _opts?: ComputeOptions): Expr {
    throw new NotImplementedError('Abstract method for expectation queries.');
  }
  /**
   * The joint distribution of the process at several times (SymPy
   * joint_distribution): a time is replaced by the random indexed symbol at
   * that time.
   */
  jointDistribution(...argsIn: (ExprLike | Expr)[]): Distribution {
    const args = argsIn.map((a0) => {
      const a = sympify(a0);
      if (a.isNumber) return isSubset(this.indexSet, Integers) === true ? this.at(a) : this.call(a);
      if (!(a instanceof RandomIndexedSymbol)) throw new RangeError(`Expected a RandomIndexedSymbol or key not  ${a.toString()}`);
      return a;
    });
    const ps = cast(first(args).pspace, StochasticPSpace, 'stochastic space');
    if (ps.distribution instanceof UnspecifiedDistribution) return new UnspecifiedJointDistribution(args);
    const density = Lambda(args, mul(...args.map((a) => processOf(a).density(a))));
    return new JointDistributionHandmade([density]);
  }
}

/** SymPy JointDistribution(*args) of the random indexed symbols of a process without distribution. */
class UnspecifiedJointDistribution extends JointDistribution {
  constructor(args: readonly Expr[]) {
    super('JointDistribution', args);
  }
  pdf(): Expr {
    throw new TypeError('the distribution is not specified');
  }
  get set(): SetExpr {
    throw new TypeError('the distribution is not specified');
  }
}

/** SymPy X[time]: the random indexed symbol of a discrete-time process. */
function discreteAt(process: StochasticProcess, timeIn: ExprLike): RandomIndexedSymbol {
  const time = sympify(timeIn);
  if (!(time instanceof Sym)) {
    // SymPy time in Naturals0 decides an integer time by its assumptions
    const c = containsQ(process.indexSet, time) ?? (isIntegerQ(time) === true && isNonNegative(time) === true ? true : undefined);
    if (c === undefined) throw new TypeError(`did not evaluate to a bool: ${time.toString()} in ${process.indexSet.toString()}`);
    if (!c) throw new RangeError(`${time.toString()} is not in the index set of ${process.symbol.toString()}`);
  }
  const ps = new StochasticPSpace([process.symbol, process, process.distribution(time)]);
  return new RandomIndexedSymbol(new Indexed([process.symbol, time]), ps);
}

/** SymPy X(time): the random indexed symbol of a continuous-time process. */
function continuousCall(process: StochasticProcess, timeIn: ExprLike): RandomIndexedSymbol {
  const time = sympify(timeIn);
  if (!(time instanceof Sym) && containsQ(process.indexSet, time) !== true) throw new RangeError(`${time.toString()} is not in the index set of ${process.symbol.toString()}`);
  const ps = new StochasticPSpace([process.symbol, process, process.distribution(time)]);
  return new RandomIndexedSymbol(new UndefFn(process.symbol.name, [time]), ps);
}

/** SymPy DiscreteTimeStochasticProcess: a process indexed by discrete times, X.at(n). */
export class DiscreteTimeStochasticProcess extends StochasticProcess {
  constructor(args: readonly Expr[], name = 'DiscreteTimeStochasticProcess') {
    super(args, name);
  }
  override at(time: ExprLike): RandomIndexedSymbol {
    return discreteAt(this, time);
  }
}

/** SymPy ContinuousTimeStochasticProcess: a process indexed by continuous times, X.call(t). */
export class ContinuousTimeStochasticProcess extends StochasticProcess {
  constructor(args: readonly Expr[], name = 'ContinuousTimeStochasticProcess') {
    super(args, name);
  }
  override call(time: ExprLike): RandomIndexedSymbol {
    return continuousCall(this, time);
  }
}

// ---------------------------------------------------------------------------
// Conditions on Markov chains
// ---------------------------------------------------------------------------

/** SymPy TransitionMatrixOf(process, matrix): the transition matrix of a discrete Markov chain, as a condition. */
export class TransitionMatrixOfNode extends ExtensionExpr {
  constructor(args: readonly Expr[], name = 'TransitionMatrixOf') {
    const process = at(args, 0);
    if (name === 'TransitionMatrixOf' && !(process instanceof DiscreteMarkovChainNode)) throw new RangeError('Currently only DiscreteMarkovChain support TransitionMatrixOf.');
    if (name === 'GeneratorMatrixOf' && !(process instanceof ContinuousMarkovChainNode)) throw new RangeError('Currently only ContinuousMarkovChain support GeneratorMatrixOf.');
    super(name, [process, matrixChecks(at(args, 1))]);
  }
  withArgs(args: readonly Expr[]): Expr {
    return cast(Reflect.construct(this.constructor, [args]), Expr);
  }
  get process(): Expr {
    return at(this.args, 0);
  }
  get matrix(): ImmutableMatrixNode | MatrixSymbolNode {
    return matrixChecks(at(this.args, 1));
  }
}

/** SymPy TransitionMatrixOf(process, matrix). */
export const TransitionMatrixOf = /* @__PURE__ */ callableClass(
  TransitionMatrixOfNode,
  (process: Expr, matrix: TransitionMatrixInput): TransitionMatrixOfNode => new TransitionMatrixOfNode([process, matrixChecks(matrix)]),
);
export type TransitionMatrixOf = TransitionMatrixOfNode;

/** SymPy GeneratorMatrixOf(process, matrix): the generator matrix of a continuous Markov chain, as a condition. */
export class GeneratorMatrixOfNode extends TransitionMatrixOfNode {
  constructor(args: readonly Expr[]) {
    super(args, 'GeneratorMatrixOf');
  }
}

/** SymPy GeneratorMatrixOf(process, matrix). */
export const GeneratorMatrixOf = /* @__PURE__ */ callableClass(
  GeneratorMatrixOfNode,
  (process: Expr, matrix: TransitionMatrixInput): GeneratorMatrixOfNode => new GeneratorMatrixOfNode([process, matrixChecks(matrix)]),
);
export type GeneratorMatrixOf = GeneratorMatrixOfNode;

/** SymPy StochasticStateSpaceOf(process, state_space): the state space of a Markov chain as a condition (the Range of the state indices). */
export class StochasticStateSpaceOfNode extends ExtensionExpr {
  constructor(args: readonly Expr[]) {
    const process = at(args, 0);
    if (!(process instanceof MarkovProcess)) throw new RangeError('Currently only DiscreteMarkovChain and ContinuousMarkovChain support StochasticStateSpaceOf.');
    super('StochasticStateSpaceOf', [process, at(args, 1)]);
  }
  withArgs(args: readonly Expr[]): Expr {
    return new StochasticStateSpaceOfNode(args);
  }
  get process(): Expr {
    return at(this.args, 0);
  }
  /** SymPy state_index. */
  get stateIndex(): Range {
    return cast(at(this.args, 1), Range, 'state index');
  }
}

/** SymPy StochasticStateSpaceOf(process, state_space). */
export const StochasticStateSpaceOf = /* @__PURE__ */ callableClass(StochasticStateSpaceOfNode, (process: Expr, stateSpace: StateSpaceInput): StochasticStateSpaceOfNode => {
  const ss = stateConverter(stateSpace);
  return new StochasticStateSpaceOfNode([process, range(stateCount(ss))]);
});
export type StochasticStateSpaceOf = StochasticStateSpaceOfNode;

// ---------------------------------------------------------------------------
// Markov processes
// ---------------------------------------------------------------------------

/** The result of SymPy MarkovProcess._preprocess. */
interface Preprocessed {
  readonly insufficient: boolean;
  readonly mat: ImmutableMatrixNode | MatrixSymbolNode;
  readonly stateIndex: Expr;
  readonly given: Expr | undefined;
}

/** A Markov chain matrix of the arguments (the transition or generator matrix). */
const chainMatrix = (args: readonly Expr[]): ImmutableMatrixNode | MatrixSymbolNode => matrixChecks(at(args, 2));

/** SymPy MarkovProcess._sanity_checks: the state space and the matrix, completed from each other. */
function sanityChecks(stateSpaceIn: StateSpaceInput | undefined, transProbsIn: TransitionMatrixInput | undefined): [TupleNode | Range, ImmutableMatrixNode | MatrixSymbolNode] {
  if (stateSpaceIn === undefined && transProbsIn === undefined) {
    const n = new Dummy('n', { integer: true, nonnegative: true });
    return [stateConverter(range(n)), new MatrixSymbolNode('_T', n, n)];
  }
  if (stateSpaceIn === undefined) {
    const t = matrixChecks(transProbsIn);
    return [stateConverter(range(t.shape[0])), t];
  }
  const ss = stateConverter(stateSpaceIn);
  const n = stateCount(ss);
  if (transProbsIn === undefined) return [ss, new MatrixSymbolNode('_T', n, n)];
  const t = matrixChecks(transProbsIn);
  if (n.key !== t.shape[0].key) throw new RangeError('The size of the state space and the number of rows of the transition matrix must be the same.');
  return [ss, t];
}

/** SymPy MarkovProcess: the base class of the discrete and continuous Markov chains. */
export abstract class MarkovProcess extends StochasticProcess {
  /** The index of each state (SymPy index_of). */
  readonly indexOf: ReadonlyMap<string, Expr>;
  constructor(args: readonly Expr[], name: string) {
    super(args, name);
    const indices = new Map<string, Expr>();
    if (this.numberOfStates instanceof Rational) this.indexStates().forEach((s, i) => indices.set(s.key, Rational.of(i)));
    this.indexOf = indices;
  }
  /** The states in the order of their indices. */
  protected abstract indexStates(): Expr[];
  /** The matrix of the chain (transition or generator). */
  protected abstract get chainMatrix(): ImmutableMatrixNode | MatrixSymbolNode;
  /** The row sum of the matrix of the chain (1 or 0). */
  protected abstract get rowSum(): number;
  /** The matrix as a condition (TransitionMatrixOf or GeneratorMatrixOf). */
  protected abstract matrixOf(mat: Expr): Expr;
  /** The transition probabilities from the time difference (SymPy trans_probs**dt or trans_probs(dt)). */
  protected abstract transitionsAt(mat: ImmutableMatrixNode | MatrixSymbolNode, dt: Expr): MatrixExpr;
  /** SymPy number_of_states. */
  get numberOfStates(): Expr {
    return chainMatrix(this.args).shape[0];
  }
  /** SymPy _state_index. */
  get stateIndexArg(): Expr {
    return at(this.args, 1);
  }
  override get stateSpace(): SetExpr {
    const s = at(this.args, 1);
    return s instanceof Range ? s : finiteSet(...cast(s, TupleNode, 'state space').args);
  }
  /** The index of a state, or the value itself (SymPy index_of.get(x, x)). */
  private indexOrSelf(x: Expr): Expr {
    return this.indexOf.get(x.key) ?? x;
  }
  /** SymPy _extract_information: the matrix, state index and relational conditions of the given condition. */
  private extractInformation(givenIn: Expr | undefined): [ImmutableMatrixNode | MatrixSymbolNode, Expr, Expr | undefined] {
    let transProbs = this.chainMatrix;
    let stateIndex: Expr = at(this.args, 1);
    let given = givenIn;
    if (isOp(given, 'And')) {
      const gcs = given.args;
      given = S.true;
      for (const gc of gcs) {
        if (gc instanceof TransitionMatrixOfNode) transProbs = gc.matrix;
        if (gc instanceof StochasticStateSpaceOfNode) stateIndex = gc.stateIndex;
        if (gc instanceof Rel) given = and(given, gc);
      }
    }
    if (given instanceof TransitionMatrixOfNode) {
      transProbs = given.matrix;
      given = S.true;
    }
    if (given instanceof StochasticStateSpaceOfNode) {
      stateIndex = given.stateIndex;
      given = S.true;
    }
    return [transProbs, stateIndex, given];
  }
  /** SymPy _check_trans_probs: the rows sum to 1 (transition) or 0 (generator). */
  private checkTransProbs(transProbs: ImmutableMatrixNode | MatrixSymbolNode): void {
    if (!(transProbs instanceof ImmutableMatrixNode)) return;
    const m = transProbs.matrix;
    for (let i = 0; i < m.rows; i++) {
      if (!isZeroNumber(sub(add(...m.row(i).data), this.rowSum))) {
        throw new RangeError(`Values in a row must sum to ${this.rowSum}. If you are using Float or floats then please use Rational.`);
      }
    }
  }
  /** SymPy _work_out_state_index. */
  private workOutStateIndex(stateIndexIn: Expr, given: Expr, transProbs: ImmutableMatrixNode | MatrixSymbolNode): Expr {
    let stateIndex = stateIndexIn;
    const randVar = randomSymbols(given).filter((r) => !(r instanceof RandomIndexedSymbol));
    if (randVar.length === 1) stateIndex = first(randVar).pspace.domain.set;
    const symCond = !(this.numberOfStates instanceof Rational);
    const n = transProbs.shape[0];
    if (!symCond && Rational.of(size(stateIndex)).key !== n.key) throw new RangeError('state space is not compatible with the transition probabilities.');
    if (!(n instanceof Sym)) stateIndex = finiteSet(...Array.from({ length: toNumber(n) }, (_, i) => i));
    return stateIndex;
  }
  /** SymPy _preprocess. */
  private preprocess(givenIn: Expr | undefined, evaluate: boolean): Preprocessed {
    const [mat, stateIndex0, given] = this.extractInformation(givenIn);
    if (!evaluate || given === undefined) return { insufficient: true, mat, stateIndex: stateIndex0, given };
    this.checkTransProbs(mat);
    return { insufficient: false, mat, stateIndex: this.workOutStateIndex(stateIndex0, given, mat), given };
  }
  /** SymPy replace_with_index: the states of a relational replaced by their indices. */
  replaceWithIndex(condition: Expr): Expr {
    if (!(condition instanceof Rel)) return condition;
    let [lhs, rhs] = [condition.lhs, condition.rhs];
    if (!(lhs instanceof RandomIndexedSymbol)) [lhs, rhs] = [rhs, lhs];
    return relOf(condition, this.indexOrSelf(lhs), this.indexOrSelf(rhs));
  }
  override probability(conditionIn: Expr, givenConditionIn?: Expr, opts: ComputeOptions = {}): Expr {
    const evaluate = opts.evaluate ?? true;
    const pre = this.preprocess(givenConditionIn, evaluate);
    const rv = indexedSymbolsOf(conditionIn);
    const symbolic = rv.some((r) => r.indexKey instanceof Sym);
    if (pre.insufficient) return new ProbabilityNode(pre.given === undefined ? [conditionIn] : [conditionIn, pre.given]);
    const { mat, stateIndex } = pre;
    const condition = this.replaceWithIndex(conditionIn);
    const givenCondition = this.replaceWithIndex(defined(givenConditionIn, 'given condition'));
    const newGiven = this.replaceWithIndex(defined(pre.given, 'given condition'));
    if (condition instanceof Rel) {
      const gcs = isOp(newGiven, 'And') ? newGiven.args : [newGiven];
      const minKeys = indexedSymbolsOf(newGiven);
      if (!minKeys.length) return new ProbabilityNode([condition]);
      // SymPy takes any of them (the first of a set); the latest time is the one the Markov property conditions on
      const minKeyRv = minKeys.reduce((a, b) => (lessThan(a.indexKey, b.indexKey) ? b : a));
      for (const r of rv) {
        if (minKeyRv.indexKey instanceof Sym || r.indexKey instanceof Sym) continue;
        if (lessThan(r.indexKey, minKeyRv.indexKey)) return new ProbabilityNode([condition]);
      }
      if (symbolic) return this.symbolicProbability(condition, newGiven, first(rv), minKeyRv);
      if (rv.length > 1) return this.twoSymbolProbability(condition, newGiven);
      return this.singleProbability(condition, gcs, first(rv), minKeyRv, mat, stateIndex);
    }
    if (isOp(condition, 'Not')) return sub(1, this.probability(at(condition.args, 0), givenCondition, opts));
    if (isOp(condition, 'And')) return this.andProbability(condition, givenCondition, mat, stateIndex, opts);
    if (isOp(condition, 'Or')) return add(...condition.args.map((e) => this.probability(e, givenCondition, opts)));
    throw new NotImplementedError(`Mechanism for handling (${condition.toString()}, ${String(givenCondition)}) queries hasn't been implemented yet.`);
  }
  /** The probability of a relation between two random indexed symbols (SymPy probability, len(rv) > 1). */
  private twoSymbolProbability(conditionIn: Rel, newGiven: Expr): Expr {
    let [rv0, rv1] = [conditionIn.lhs, conditionIn.rhs];
    let op: RelOp = conditionIn.op;
    if (lessThan(keyOf(rv0), keyOf(rv1))) {
      [rv0, rv1] = [rv1, rv0];
      const flip: Record<RelOp, RelOp> = { Gt: 'Lt', Lt: 'Gt', Ge: 'Le', Le: 'Ge', Eq: 'Eq', Ne: 'Ne' };
      op = flip[op];
    }
    let s: Expr = S.Zero;
    const n = size(this.stateSpace);
    const term = (i: number, j: number): Expr => mul(this.probability(Eq(rv0, i), Eq(rv1, j)), this.probability(Eq(rv1, j), newGiven));
    if (op === 'Eq' || op === 'Ne') {
      for (let i = 0; i < n; i++) s = add(s, term(i, i));
      return op === 'Eq' ? s : sub(1, s);
    }
    const upper = op === 'Ge' || op === 'Lt' ? 1 : 0;
    const greater = op === 'Ge' || op === 'Gt';
    for (let i = 0; i < n; i++) {
      if (i <= Math.floor(n / 2)) {
        for (let j = 0; j < i + upper; j++) s = add(s, term(i, j));
      } else {
        s = add(s, this.probability(Eq(rv0, i), newGiven));
        for (let j = i + upper; j < n; j++) s = sub(s, term(i, j));
      }
    }
    return greater ? s : sub(1, s);
  }
  /** The probability of a relation on one random indexed symbol (SymPy probability, the last case of a Relational). */
  private singleProbability(condition: Rel, gcs: readonly Expr[], rv: RandomIndexedSymbol, minKeyRv: RandomIndexedSymbol, mat: ImmutableMatrixNode | MatrixSymbolNode, stateIndex: Expr): Expr {
    let states = asSet(condition);
    const prob = new Map<string, [SetExpr, Expr]>();
    let gstate: Expr | undefined;
    for (const gc of gcs) {
      if (!gc.has(minKeyRv)) continue;
      const r = cast(gc, Rel, 'given condition');
      if (hasProbability(gc)) {
        const [p, gp] = r.lhs instanceof ProbabilityNode ? [r.rhs, r.lhs] : [r.lhs, r.rhs];
        const gset = intersection(asSet(at(gp.args, 0)), cast(stateIndex, SetExpr));
        gstate = first(elements(gset));
        prob.set(gset.key, [gset, p]);
      } else {
        gstate = r.lhs instanceof RandomIndexedSymbol ? r.rhs : r.lhs;
      }
    }
    if (![rv.indexKey, minKeyRv.indexKey].every((k) => containsQ(this.indexSet, k) === true)) throw new RangeError("The timestamps of the process are not in it's index set.");
    if (!(this.numberOfStates instanceof Sym)) states = intersection(states, cast(stateIndex, SetExpr));
    for (const state of elements(union(states, finiteSet(defined(gstate, 'given state'))))) {
      if (!(state instanceof Rational && state.isInteger) || Ge(state, mat.shape[0]) === S.true) {
        throw new RangeError(`No information is available for (${String(gstate)}, ${state.toString()}) in transition probabilities of shape, (${mat.shape[0].toString()}, ${mat.shape[1].toString()}). State space is zero indexed.`);
      }
    }
    let gprob: Expr = S.One;
    if (prob.size) {
      const gstates = union(...[...prob.values()].map(([k]) => k));
      const all = cast(stateIndex, SetExpr);
      if (size(gstates) === 1) {
        gstate = first(elements(gstates));
        gprob = at([...prob.values()], 0)[1];
        prob.set(gstates.key, [gstates, gprob]);
      } else if (size(gstates) === size(all) - 1) {
        const rest = complement(all, gstates);
        gstate = first(elements(rest));
        gprob = sub(1, add(...[...prob.values()].map(([, p]) => p)));
        prob.set(rest.key, [rest, gprob]);
      } else {
        throw new RangeError('Conflicting information.');
      }
    }
    if (minKeyRv.key === rv.key) {
      return add(
        ...elements(states).map((state) => {
          const p = prob.get(finiteSet(state).key);
          if (p === undefined) throw new RangeError(`KeyError: {${state.toString()}}`);
          return p[1];
        }),
      );
    }
    const trans = this.transitionsAt(mat, sub(rv.indexKey, minKeyRv.indexKey));
    const g = defined(gstate, 'given state');
    return mul(gprob, add(...elements(states).map((state) => trans.at(g, state))));
  }
  /** The probability of a conjunction of conditions (SymPy probability, And). */
  private andProbability(condition: BoolOp, givenCondition: Expr | undefined, mat: ImmutableMatrixNode | MatrixSymbolNode, stateIndex: Expr, opts: ComputeOptions): Expr {
    const computeLater: Expr[] = [];
    const state2cond = new Map<string, [RandomIndexedSymbol, Expr]>();
    for (const e of condition.args) {
      if (e instanceof Rel) {
        const ris = first(indexedSymbolsOf(e));
        const prev = state2cond.get(ris.key)?.[1] ?? S.true;
        state2cond.set(ris.key, [ris, and(prev, e)]);
      } else {
        computeLater.push(e);
      }
    }
    for (const [k, [ri, c]] of state2cond) {
      const cset = intersection(asSet(c), cast(stateIndex, SetExpr));
      if (cset === EmptySet || size(cset) === 0) return S.Zero;
      state2cond.set(k, [ri, asRelational(cset, ri)]);
    }
    const sorted = [...state2cond.values()].sort(([a], [b]) => Number(lessThan(b.indexKey, a.indexKey)) - Number(lessThan(a.indexKey, b.indexKey)));
    let prod = this.probability(at(sorted, 0)[1], givenCondition, opts);
    for (let i = 1; i < sorted.length; i++) {
      const [ri, c] = at(sorted, i);
      const prevCond = at(sorted, i - 1)[1];
      if (!(c instanceof Rel && c.op === 'Eq')) throw new RangeError(`The process is in multiple states at ${ri.toString()}, unable to determine the probability.`);
      prod = mul(prod, this.probability(c, and(prevCond, this.matrixOf(mat), StochasticStateSpaceOf(this, cast(stateIndex, SetExpr))), opts));
    }
    for (const e of computeLater) prod = mul(prod, this.probability(e, givenCondition, opts));
    return prod;
  }
  /** SymPy _symbolic_probability: the probability for symbolic times. */
  private symbolicProbability(condition: Rel, newGiven: Expr, rv0: RandomIndexedSymbol, minKeyRv: RandomIndexedSymbol): Expr {
    // the relations have the random indexed symbol on the left (replaceWithIndex)
    const currState = cast(newGiven, Rel, 'given condition').rhs;
    const nextState = condition.rhs;
    const later = Gt(rv0.indexKey, minKeyRv.indexKey);
    if (condition.op === 'Eq' || condition.op === 'Ne') {
      const p = this.transitionsAt(this.chainMatrix, sub(rv0.indexKey, minKeyRv.indexKey));
      const e = p.at(currState, nextState);
      return piecewise([condition.op === 'Eq' ? e : sub(1, e), later], [new ProbabilityNode([condition]), true]);
    }
    const upper = condition.op === 'Ge' || condition.op === 'Lt' ? 0 : 1;
    const greater = condition.op === 'Ge' || condition.op === 'Gt';
    const k = new Dummy('k');
    const eqCond = Eq(condition.lhs, k);
    const total = Sum(this.probability(eqCond, newGiven), [k, add(nextState, upper), sup(this.stateSpace)]);
    return piecewise([greater ? total : sub(1, total), later], [new ProbabilityNode([eqCond]), true]);
  }
  override expectation(expr: Expr, conditionIn?: Expr, opts: ComputeOptions = {}): Expr {
    const pre = this.preprocess(conditionIn, opts.evaluate ?? true);
    if (pre.insufficient) return makeExpectation(expr, pre.given);
    const rvs = randomSymbols(expr);
    const cond0 = pre.given;
    if (cond0 instanceof Rel && cond0.op === 'Eq' && rvs.length === 1) {
      const condition = this.replaceWithIndex(cond0);
      const stateIndex = cast(pre.stateIndex, SetExpr);
      const rv = first(rvs);
      // the random indexed symbol is on the left (replaceWithIndex)
      const [lhsg, rhsg] = [cast(condition, Rel).lhs, cast(condition, Rel).rhs];
      if (containsQ(stateIndex, rhsg) !== true) throw new RangeError(`${rhsg.toString()} state is not in the state space.`);
      if (lessThan(keyOf(rv), keyOf(lhsg))) throw new RangeError(`Incorrect given condition is given, expectation time ${keyOf(rv).toString()} < time ${keyOf(rv).toString()}`);
      const cond = and(condition, this.matrixOf(pre.mat), StochasticStateSpaceOf(this, stateIndex));
      const states = this.stateIndexArg;
      return add(...elements(stateIndex).map((s) => mul(this.probability(Eq(rv, s), cond), expr.subs(rv, at(elements(states), toNumber(s))))));
    }
    throw new NotImplementedError(`Mechanism for handling (${expr.toString()}, ${String(conditionIn)}) queries hasn't been implemented yet.`);
  }
}

/** The stationary distributions of a symbolic matrix: Lambda or ConditionSet of wm*T = wm. */
function symbolicStationary(t: MatrixSymbolNode, n: Expr, conditionSetForm: boolean): Expr {
  const wm = new MatrixSymbolNode('wm', 1, n);
  const eq = new Rel('Eq', wm.mul(t), wm);
  return conditionSetForm ? conditionSet(wm, eq) : Lambda([wm, t], eq);
}

/** The single solution of a linear system with its free unknowns as parameters tau0, tau1, ... (SymPy linsolve). */
function linsolveTau(eqs: readonly Expr[], unknowns: readonly Sym[]): Expr[] {
  // the systems of the stationary and limiting distributions are consistent
  const sol = expectType(linsolve(eqs, unknowns), (x): x is Expr[] => Array.isArray(x), 'solution');
  const keys = new Set(unknowns.map((u) => u.key));
  const free = unknowns.filter((u) => sol.some((e) => [...e.freeSymbols()].some((s) => s.key === u.key && keys.has(s.key))));
  const taus = free.map((u, i) => [u, new Sym(`tau${i}`)] as const);
  return sol.map((e) => xreplace(e, taus));
}

/** SymPy DiscreteMarkovChain(sym, state_space, trans_probs): a discrete-time Markov chain. */
export class DiscreteMarkovChainNode extends MarkovProcess {
  constructor(args: readonly Expr[]) {
    super(args, 'DiscreteMarkovChain');
  }
  override get indexSet(): SetExpr {
    return Naturals0;
  }
  protected indexStates(): Expr[] {
    return elements(this.stateIndexArg);
  }
  protected get chainMatrix(): ImmutableMatrixNode | MatrixSymbolNode {
    return this.transitionProbabilities;
  }
  protected get rowSum(): number {
    return 1;
  }
  protected matrixOf(mat: Expr): Expr {
    return new TransitionMatrixOfNode([this, mat]);
  }
  protected transitionsAt(mat: ImmutableMatrixNode | MatrixSymbolNode, dt: Expr): MatrixExpr {
    return cast(mat.pow(dt), MatrixExpr, 'matrix power');
  }
  override at(time: ExprLike): RandomIndexedSymbol {
    return discreteAt(this, time);
  }
  /** SymPy transition_probabilities. */
  get transitionProbabilities(): ImmutableMatrixNode | MatrixSymbolNode {
    return chainMatrix(this.args);
  }
  /** The explicit transition matrix (a symbolic one raises NotImplementedError). */
  private explicit(): Matrix {
    const t = this.transitionProbabilities;
    if (!(t instanceof ImmutableMatrixNode)) throw new NotImplementedError('Cannot perform the operation with a symbolic matrix.');
    return t.matrix;
  }
  /**
   * The communication classes with their recurrence and period (SymPy
   * communication_classes): [states, is_recurrent, period] for each class.
   */
  communicationClasses(): [Expr[], Expr, Expr][] {
    const T = this.explicit();
    const n = T.rows;
    const V = Array.from({ length: n }, (_, i) => i);
    const nz = (i: number, j: number): boolean => !isZeroNumber(T.get(i, j));
    const E: [number, number][] = [];
    for (const i of V) for (const j of V) if (nz(i, j)) E.push([i, j]);
    const classes = stronglyConnectedComponents<number>([V, E]);
    const out: [Expr[], Expr, Expr][] = [];
    const states = this.indexStates();
    for (const cls of classes) {
      const sub2 = T.slice(cls, cls);
      let recurrent: Expr = S.true;
      for (let r = 0; r < sub2.rows; r++) if (!isZeroNumber(sub(add(...sub2.row(r).data), 1))) recurrent = S.false;
      let nonTree = new Set<number>();
      let visited = new Set([at(cls, 0)]);
      let newlyVisited = new Set([at(cls, 0)]);
      const level = new Map([[at(cls, 0), 0]]);
      let currentLevel = 0;
      let done = false;
      while (!done) {
        done = visited.size === cls.length;
        currentLevel += 1;
        for (const i of [...newlyVisited].sort((a, b) => a - b)) {
          newlyVisited = new Set(cls.filter((j) => nz(i, j)));
          const newTree = [...newlyVisited].filter((j) => !visited.has(j));
          for (const j of newTree) level.set(j, currentLevel);
          const newNonTree = [...newlyVisited].filter((j) => visited.has(j));
          nonTree = new Set([...nonTree, ...newNonTree.map((j) => defined(level.get(i)) - defined(level.get(j)) + 1)]);
          visited = new Set([...visited, ...newTree]);
        }
      }
      const positive = [...nonTree].filter((v) => v > 0);
      const period = positive.length === 0 ? cls.length : Number(igcd(...positive.map(BigInt)));
      out.push([cls.map((i) => at(states, i)), recurrent, Rational.of(period)]);
    }
    return out;
  }
  /** The fundamental matrix of the chain (SymPy fundamental_matrix). */
  fundamentalMatrix(): ImmutableMatrixNode {
    const [, , , Q] = this.decompose();
    const q = Q.matrix;
    if (q.rows > 0) {
      // I - Q is invertible: the states of Q are transient
      return new ImmutableMatrixNode(Matrix.eye(q.rows).sub(q).inv());
    }
    const P = this.explicit();
    const w = cast(this.fixedRowVector(), ImmutableMatrixNode).matrix;
    const W = Matrix.fromFunction(P.rows, P.cols, (_i, j) => w.get(0, j));
    const M = Matrix.eye(P.rows).sub(P).add(W);
    if (isZeroNumber(M.det())) throw new RangeError("The fundamental matrix doesn't exist.");
    return new ImmutableMatrixNode(M.inv());
  }
  /** The probabilities of absorption in each recurrent state from each transient state (SymPy absorbing_probabilities). */
  absorbingProbabilities(): ImmutableMatrixNode {
    const [, , R] = this.decompose();
    return new ImmutableMatrixNode(this.fundamentalMatrix().matrix.mul(R.matrix));
  }
  /** @deprecated SymPy absorbing_probabilites (a misspelling): use `absorbingProbabilities`. */
  absorbingProbabilites(): ImmutableMatrixNode {
    return this.absorbingProbabilities();
  }
  /** The chain is regular: one class of period 1 (SymPy is_regular). */
  isRegular(): Expr {
    const tuples = this.communicationClasses();
    if (!tuples.length) return S.false;
    return tuples.length === 1 && at(tuples, 0)[2].key === S.One.key ? S.true : S.false;
  }
  /** The chain is ergodic: one class (SymPy is_ergodic). */
  isErgodic(): Expr {
    return this.communicationClasses().length === 1 ? S.true : S.false;
  }
  /** The state is absorbing (SymPy is_absorbing_state); 'unknown' for a symbolic matrix or a state out of range. */
  isAbsorbingState(state: number): boolean | 'unknown' {
    const t = this.transitionProbabilities;
    if (t instanceof ImmutableMatrixNode && state < t.matrix.rows) return t.matrix.get(state, state).key === S.One.key;
    return 'unknown';
  }
  /** The chain is absorbing (SymPy is_absorbing_chain). */
  isAbsorbingChain(): Expr {
    const [, A] = this.decompose();
    const r = A.matrix.rows;
    return r > 0 && A.matrix.equals(Matrix.eye(r)) ? S.true : S.false;
  }
  /**
   * The stationary distribution (SymPy stationary_distribution): a row
   * vector; for a symbolic matrix, the Lambda (or with `conditionSet`, the
   * ConditionSet) of the equation wm*T = wm.
   */
  stationaryDistribution(opts: { readonly conditionSet?: boolean } = {}): Expr {
    const t = this.transitionProbabilities;
    const n = this.numberOfStates;
    if (n.key === S.Zero.key) return new ImmutableMatrixNode(Matrix.zeros(1, 0));
    if (t instanceof MatrixSymbolNode) return symbolicStationary(t, n, opts.conditionSet ?? false);
    const m = cast(t, ImmutableMatrixNode).matrix;
    const k = m.rows;
    const a0 = m.sub(Matrix.eye(k)).transpose();
    const a = Matrix.fromFunction(k, k, (i, j) => (i === 0 ? 1 : a0.get(i, j)));
    const xs = Array.from({ length: k }, (_, i) => new Dummy(`x${i}`));
    const eqs = Array.from({ length: k }, (_, i) => sub(add(...xs.map((x, j) => mul(a.get(i, j), x))), i === 0 ? 1 : 0));
    return new ImmutableMatrixNode(Matrix.of([linsolveTau(eqs, xs)]));
  }
  /** SymPy fixed_row_vector: the stationary distribution. */
  fixedRowVector(): Expr {
    return this.stationaryDistribution();
  }
  /** SymPy limiting_distribution: the stationary distribution. */
  get limitingDistribution(): Expr {
    return this.fixedRowVector();
  }
  /**
   * The states reordered recurrent first and the blocks of the transition
   * matrix: recurrent to recurrent, transient to recurrent and transient to
   * transient (SymPy decompose).
   */
  decompose(): [Expr[], ImmutableMatrixNode, ImmutableMatrixNode, ImmutableMatrixNode] {
    const T = this.explicit();
    const classes = this.communicationClasses();
    const rStates: Expr[] = [];
    const tStates: Expr[] = [];
    for (const [states, recurrent] of classes) (recurrent === S.true ? rStates : tStates).push(...states);
    const states = [...rStates, ...tStates];
    const idx = states.map((s) => toNumber(defined(this.indexOf.get(s.key), 'state index')));
    const r = rStates.length;
    const t = tStates.length;
    const A = Matrix.fromFunction(r, r, (i, j) => T.get(at(idx, i), at(idx, j)));
    const B = Matrix.fromFunction(t, r, (i, j) => T.get(at(idx, r + i), at(idx, j)));
    const C = Matrix.fromFunction(t, t, (i, j) => T.get(at(idx, r + i), at(idx, r + j)));
    return [states, new ImmutableMatrixNode(A), new ImmutableMatrixNode(B), new ImmutableMatrixNode(C)];
  }
  /** The states reordered and the transition matrix in canonical form [[A, 0], [B, C]] (SymPy canonical_form). */
  canonicalForm(): [Expr[], ImmutableMatrixNode] {
    const [states, A, B, C] = this.decompose();
    const r = A.matrix.rows;
    const n = r + C.matrix.rows;
    const m = Matrix.fromFunction(n, n, (i, j) => (i < r ? (j < r ? A.matrix.get(i, j) : 0) : j < r ? B.matrix.get(i - r, j) : C.matrix.get(i - r, j - r)));
    return [states, new ImmutableMatrixNode(m)];
  }
}

/** SymPy DiscreteMarkovChain(sym, state_space=None, trans_probs=None). */
export const DiscreteMarkovChain = /* @__PURE__ */ callableClass(
  DiscreteMarkovChainNode,
  (sym: string | Sym, stateSpace?: StateSpaceInput, transProbs?: TransitionMatrixInput): DiscreteMarkovChainNode => {
    const s = symbolConverter(typeof sym === 'string' ? sym : sympify(sym));
    const [ss, tp] = sanityChecks(stateSpace, transProbs);
    return new DiscreteMarkovChainNode([s, ss, tp]);
  },
);
export type DiscreteMarkovChain = DiscreteMarkovChainNode;

/** SymPy ContinuousMarkovChain(sym, state_space, gen_mat): a continuous-time Markov chain. */
export class ContinuousMarkovChainNode extends MarkovProcess {
  constructor(args: readonly Expr[]) {
    super(args, 'ContinuousMarkovChain');
  }
  protected indexStates(): Expr[] {
    return elements(this.stateSpace);
  }
  protected get chainMatrix(): ImmutableMatrixNode | MatrixSymbolNode {
    return this.generatorMatrix;
  }
  protected get rowSum(): number {
    return 0;
  }
  protected matrixOf(mat: Expr): Expr {
    return new GeneratorMatrixOfNode([this, mat]);
  }
  protected transitionsAt(mat: ImmutableMatrixNode | MatrixSymbolNode, dt: Expr): MatrixExpr {
    return cast(this.transitionProbabilities(mat).call(dt), MatrixExpr, 'transition matrix');
  }
  override call(time: ExprLike): RandomIndexedSymbol {
    return continuousCall(this, time);
  }
  /** SymPy generator_matrix. */
  get generatorMatrix(): ImmutableMatrixNode | MatrixSymbolNode {
    return chainMatrix(this.args);
  }
  /**
   * The transition probabilities as a function of the time (SymPy
   * transition_probabilities(gen_mat)): exp(t*G) for the generator matrix G
   * (by default the chain's), through its diagonalization when it has one.
   */
  transitionProbabilities(genMat: ImmutableMatrixNode | MatrixSymbolNode = this.generatorMatrix): ReturnType<typeof Lambda> {
    const t = new Dummy('t');
    if (genMat instanceof ImmutableMatrixNode && isDiagonalizable(genMat.matrix)) {
      const [Q, D] = diagonalize(genMat.matrix);
      const expD = Matrix.fromFunction(D.rows, D.cols, (i, j) => (i === j ? exp(mul(t, D.get(i, j))) : 0));
      return Lambda(t, new ImmutableMatrixNode(Q.mul(expD).mul(Q.inv())));
    }
    return Lambda(t, exp(genMat.rmul(t)));
  }
  /** The limiting distribution (SymPy limiting_distribution): a row vector, or for a symbolic matrix the Lambda of wm*G = wm. */
  limitingDistribution(): Expr {
    const g = this.generatorMatrix;
    if (g instanceof MatrixSymbolNode) return symbolicStationary(g, g.shape[0], false);
    const m = g.matrix;
    const w = Array.from({ length: m.rows }, (_, i) => new Dummy(`w${i}`));
    const wm = Matrix.of([w]).mul(m);
    const eqs = [...wm.data, sub(add(...w), 1)];
    return new ImmutableMatrixNode(Matrix.of([linsolveTau(eqs, w)]));
  }
}

/** SymPy ContinuousMarkovChain(sym, state_space=None, gen_mat=None). */
export const ContinuousMarkovChain = /* @__PURE__ */ callableClass(
  ContinuousMarkovChainNode,
  (sym: string | Sym, stateSpace?: StateSpaceInput, genMat?: TransitionMatrixInput): ContinuousMarkovChainNode => {
    const [ss, gm] = sanityChecks(stateSpace, genMat);
    return new ContinuousMarkovChainNode([symbolConverter(sym), ss, gm]);
  },
);
export type ContinuousMarkovChain = ContinuousMarkovChainNode;

// ---------------------------------------------------------------------------
// Bernoulli process
// ---------------------------------------------------------------------------

/** The random symbols of an expression whose random indexed symbols are replaced by simple random symbols (SymPy _SubstituteRV._rvindexed_subs). */
function rvindexedSubs(expr: Expr): Expr {
  const rvs = randomSymbols(expr).filter((rv): rv is RandomIndexedSymbol => rv instanceof RandomIndexedSymbol);
  if (!rvs.length) return expr;
  return expr.subs(rvs.map((rv) => [rv, simpleProcessOf(rv).simpleRv(rv)] as const));
}

/** SymPy _SubstituteRV._expectation: the expectation with simple random symbols in place of the random indexed symbols. */
export function substituteExpectation(expr: Expr, condition?: Expr, opts: ComputeOptions = {}): Expr {
  let newExpr = rvindexedSubs(expr);
  const newCondition = condition === undefined ? undefined : rvindexedSubs(condition);
  if (!isRandom(newExpr)) return newExpr;
  const ps = pspace(newExpr);
  if (newCondition !== undefined) newExpr = given(newExpr, newCondition);
  const evaluate = opts.evaluate ?? true;
  if (newExpr.kind === 'Add') return add(...newExpr.args.map((a) => ps.computeExpectation(a, undefined, { evaluate })));
  return ps.computeExpectation(newExpr, undefined, { evaluate });
}

/** SymPy _SubstituteRV._probability: the probability with simple random symbols in place of the random indexed symbols. */
export function substituteProbability(condition: Expr, givenCondition?: Expr, opts: ComputeOptions = {}): Expr {
  const newCondition = rvindexedSubs(condition);
  const newGiven = givenCondition === undefined ? undefined : rvindexedSubs(givenCondition);
  if (newGiven instanceof RandomSymbol) {
    const condrv = randomSymbols(newCondition);
    if (condrv.length === 1 && first(condrv).key === newGiven.key) return new BernoulliDistribution([substituteProbability(newCondition), S.Zero, S.One]);
    if (condrv.some((rv) => dependent(rv, newGiven))) return new ProbabilityNode([newCondition, newGiven]);
    return substituteProbability(newCondition);
  }
  if (newGiven !== undefined && !isBooleanLike(newGiven)) throw new RangeError(`${newGiven.toString()} is not a relational or combination of relationals`);
  if (newGiven === S.false || newCondition === S.false) return S.Zero;
  if (newCondition === S.true) return S.One;
  if (!isBooleanLike(newCondition)) throw new RangeError(`${newCondition.toString()} is not a relational or combination of relationals`);
  if (newGiven !== undefined) return substituteProbability(given(newCondition, newGiven, opts), undefined, opts);
  const result = pspace(newCondition).probability(newCondition, opts);
  return opts.evaluate ?? true ? doit(result) : result;
}

/** A process whose random indexed symbols can be replaced by simple random symbols (SymPy simple_rv). */
interface SimpleRv {
  simpleRv(rv: RandomIndexedSymbol): RandomSymbol;
}

/** SymPy BernoulliProcess(sym, p, success=1, failure=0): a sequence of independent Bernoulli trials. */
export class BernoulliProcessNode extends DiscreteTimeStochasticProcess implements SimpleRv {
  constructor(args: readonly Expr[]) {
    valueCheck([Ge(at(args, 1), 0), Le(at(args, 1), 1)], 'Value of p must be between 0 and 1.');
    super(args, 'BernoulliProcess');
  }
  override get indexSet(): SetExpr {
    return Naturals0;
  }
  /** SymPy p. */
  get p(): Expr {
    return at(this.args, 1);
  }
  /** SymPy success. */
  get success(): Expr {
    return at(this.args, 2);
  }
  /** SymPy failure. */
  get failure(): Expr {
    return at(this.args, 3);
  }
  override get stateSpace(): SetExpr {
    return setConverter([this.success, this.failure]);
  }
  /** The Bernoulli distribution of each trial (SymPy distribution(key)). */
  override distribution(_key?: Expr): Distribution {
    return new BernoulliDistribution([this.p, this.success, this.failure]);
  }
  /** SymPy simple_rv: the Bernoulli random symbol of the trial. */
  simpleRv(rv: RandomIndexedSymbol): RandomSymbol {
    return Bernoulli(rv.name, this.p, this.success, this.failure);
  }
  override expectation(expr: Expr, condition?: Expr, opts: ComputeOptions = {}): Expr {
    return substituteExpectation(expr, condition, opts);
  }
  override probability(condition: Expr, givenCondition?: Expr, opts: ComputeOptions = {}): Expr {
    return substituteProbability(condition, givenCondition, opts);
  }
  override density(x: Expr): Expr {
    return piecewise([this.p, Eq(x, this.success)], [sub(1, this.p), Eq(x, this.failure)], [S.Zero, true]);
  }
}

/** SymPy BernoulliProcess(sym, p, success=1, failure=0). */
export const BernoulliProcess = /* @__PURE__ */ callableClass(
  BernoulliProcessNode,
  (sym: string | Sym, p: ExprLike, success: ExprLike | string = 1, failure: ExprLike | string = 0): BernoulliProcessNode =>
    new BernoulliProcessNode([symbolConverter(sym), sympify(p), symSympify(success), symSympify(failure)]),
);
export type BernoulliProcess = BernoulliProcessNode;

// ---------------------------------------------------------------------------
// Counting processes
// ---------------------------------------------------------------------------

/**
 * SymPy get_timerv_swaps(expr, condition): the intervals of the symbolic
 * times of the random indexed symbols given by Contains conditions, and the
 * replacement of each such symbol by the symbol at the length of its
 * interval.
 */
export function getTimervSwaps(expr: Expr, condition: Expr): [SetExpr[], [RandomIndexedSymbol, Expr][]] {
  if (!isBooleanLike(condition)) throw new RangeError(`${condition.toString()} is not a relational or combination of relationals`);
  const exprSyms = indexedSymbolsOf(expr);
  const givenArgs = isOp(condition, 'And') || isOp(condition, 'Or') ? condition.args : [condition];
  const swap: [RandomIndexedSymbol, Expr][] = [];
  const intervals: SetExpr[] = [];
  for (const s of exprSyms) {
    for (const arg of givenArgs) {
      if (!(arg.has(s.indexKey) && s.indexKey instanceof Sym)) continue;
      const intv = setConverter(at(arg.args, 1));
      let diff = sub(sup(intv), inf(intv));
      if (diff === S.Infinity) throw new RangeError(`${s.name} should have finite bounds`);
      if (diff.key === S.Zero.key) diff = sup(intv);
      swap.push([s, s.subs(s.indexKey, diff)]);
      intervals.push(intv);
    }
  }
  return [intervals, swap];
}

/** The intervals are pairwise disjoint (or there is only one). */
const disjoint = (intervals: readonly SetExpr[]): boolean =>
  intervals.length === 1 || intervals.every((a, i) => intervals.slice(i + 1).every((b) => intersection(a, b) === EmptySet));

/** SymPy CountingProcess: a continuous-time process on [0, oo) whose increments are independent. */
export abstract class CountingProcess extends ContinuousTimeStochasticProcess implements SimpleRv {
  override get indexSet(): SetExpr {
    return interval(0, S.Infinity);
  }
  abstract simpleRv(rv: RandomIndexedSymbol): RandomSymbol;
  override expectation(exprIn: Expr, condition?: Expr, opts: ComputeOptions = {}): Expr {
    let expr = exprIn;
    if (condition !== undefined) {
      const [intervals, swap] = getTimervSwaps(expr, condition);
      if (!disjoint(intervals)) return makeExpectation(expr, condition);
      if (expr.kind === 'Add') return add(...expr.args.map((a) => this.expectation(a, condition)));
      expr = expr.subs(swap);
    }
    return substituteExpectation(expr, undefined, opts);
  }
  /** SymPy _solve_argwith_tworvs: a relation of two random indexed symbols as one of their difference. */
  private solveArgWithTwoRvs(arg: Rel): Expr {
    const [k0, k1] = [keyOf(arg.lhs), keyOf(arg.rhs)];
    if (Ge(k0, k1) === S.true || arg.op === 'Eq') return relOf(arg, callAt(arg.lhs, abs(sub(k0, k1))), S.Zero);
    return relOf(arg, callAt(arg.rhs, sub(k1, k0)), S.Zero);
  }
  /** SymPy _solve_numerical: the probability of conditions at numeric times, from the independent increments. */
  private solveNumerical(condition: Expr, givenCondition?: Expr): Expr {
    const condArgs = isOp(condition, 'And') ? [...condition.args] : [condition];
    const argsList = [...condArgs];
    if (givenCondition !== undefined) argsList.push(...(isOp(givenCondition, 'And') ? givenCondition.args : [givenCondition]));
    const rels = argsList.map((a) => cast(a, Rel, 'condition')).sort((a, b) => Number(lessThan(keyOf(b.lhs), keyOf(a.lhs))) - Number(lessThan(keyOf(a.lhs), keyOf(b.lhs))));
    const result: Expr[] = [];
    const first0 = at(rels, 0);
    const twoRvs = isRandom(first0.lhs) && isRandom(first0.rhs);
    if (condArgs.some((c) => c.key === first0.key) && !twoRvs) result.push(substituteProbability(first0));
    if (twoRvs) result.push(substituteProbability(this.solveArgWithTwoRvs(first0)));
    for (let i = 0; i < rels.length - 1; i++) {
      const [curr, nex] = [at(rels, i), at(rels, i + 1)];
      const diff = sub(keyOf(nex.lhs), keyOf(curr.lhs));
      const proc = (): RandomIndexedSymbol => callAt(curr.lhs, diff);
      if (Gt(curr.rhs, nex.rhs) === S.true) {
        result.push(S.Zero);
        break;
      }
      let ws: SetExpr = processOf(curr.lhs).stateSpace;
      ws = intersection(ws, curr.op === 'Eq' ? interval(curr.rhs, S.Infinity, true) : asSet(curr));
      ws = intersection(ws, nex.op === 'Eq' ? interval(S.NegativeInfinity, nex.rhs) : asSet(nex));
      if (ws === EmptySet) {
        result.push(substituteProbability(Eq(proc(), 0)));
      } else if (ws instanceof FiniteSet || ws instanceof Range) {
        const n = size(ws);
        const eqs = [curr.op === 'Eq', nex.op === 'Eq'];
        if (eqs[0] && eqs[1]) result.push(substituteProbability(Eq(proc(), n)));
        else if (eqs[0] !== eqs[1]) result.push(add(...Array.from({ length: n }, (_, x) => substituteProbability(Eq(proc(), x)))));
        else result.push(add(...Array.from({ length: n }, (_, x) => mul(n - x, substituteProbability(Eq(proc(), x))))));
      } else {
        result.push(substituteProbability(Le(proc(), sub(sup(ws), inf(ws)))));
      }
    }
    return mul(...result);
  }
  override probability(conditionIn: Expr, givenCondition?: Expr, opts: ComputeOptions = {}): Expr {
    let condition = conditionIn;
    const condArgs = isOp(condition, 'And') || isOp(condition, 'Or') ? condition.args : [condition];
    const numeric = condArgs.every((a) => keyOf(at(a.args, 0)).freeSymbols().size === 0);
    if (givenCondition !== undefined) {
      const givenArgs = isOp(givenCondition, 'And') || isOp(givenCondition, 'Or') ? givenCondition.args : [givenCondition];
      const givenNumeric = !hasContains(givenCondition);
      if (numeric && givenNumeric) {
        const res: Expr[] = [];
        if (isOp(condition, 'Or')) res.push(add(...condition.args.map((a) => this.solveNumerical(a, givenCondition))));
        if (isOp(givenCondition, 'Or')) res.push(add(...givenCondition.args.map((a) => this.solveNumerical(condition, a))));
        if (res.length) return add(...res);
        return this.solveNumerical(condition, givenCondition);
      }
      if (!givenArgs.every(hasContains)) {
        throw new RangeError(
          'If given condition is passed with `Contains`, then please pass the evaluated condition with its corresponding information in terms of intervals of each time stamp to be passed in given condition.',
        );
      }
      const [intervals, swap] = getTimervSwaps(condition, givenCondition);
      if (!disjoint(intervals)) return new ProbabilityNode([condition, givenCondition]);
      if (isOp(condition, 'And')) return mul(...condition.args.map((a) => this.probability(a, givenCondition)));
      if (isOp(condition, 'Or')) return add(...condition.args.map((a) => this.probability(a, givenCondition)));
      condition = condition.subs(swap);
    }
    if (numeric) return this.solveNumerical(condition);
    return substituteProbability(condition, undefined, opts);
  }
}

/** The expression contains a Contains (SymPy expr.has(Contains)). */
const hasContains = (e: Expr): boolean => e instanceof Contains || e.args.some(hasContains);

/** SymPy PoissonProcess(sym, lamda): a counting process with independent Poisson increments of rate lamda. */
export class PoissonProcessNode extends CountingProcess {
  constructor(args: readonly Expr[]) {
    valueCheck(Gt(at(args, 1), 0), 'lamda should be a positive number.');
    super(args, 'PoissonProcess');
  }
  /** SymPy lamda. */
  get lamda(): Expr {
    return at(this.args, 1);
  }
  override get stateSpace(): SetExpr {
    return Naturals0;
  }
  /** The Poisson distribution at a time (SymPy distribution(key)). */
  override distribution(key: Expr): Distribution {
    const t = key instanceof RandomIndexedSymbol ? key.indexKey : key;
    return new PoissonDistribution([mul(this.lamda, t)]);
  }
  override density(x: Expr): Expr {
    const lt = mul(this.lamda, keyOf(x));
    return mul(pow(lt, x), pow(factorial(x), -1), exp(mul(-1, lt)));
  }
  simpleRv(rv: RandomIndexedSymbol): RandomSymbol {
    return Poisson(rv.name, mul(this.lamda, rv.indexKey));
  }
  /** The merged process, of rate the sum of the rates (SymPy X + Y). */
  override add(other: ExprLike): PoissonProcessNode {
    if (!(other instanceof PoissonProcessNode)) throw new RangeError('Only instances of Poisson Process can be merged');
    return new PoissonProcessNode([new Dummy(this.symbol.name + other.symbol.name), add(this.lamda, other.lamda)]);
  }
  /** The process split into two of rates l1 and l2 (SymPy split). */
  split(l1: ExprLike, l2: ExprLike): [PoissonProcessNode, PoissonProcessNode] {
    if (add(l1, l2).key !== this.lamda.key) throw new RangeError(`Sum of l1 and l2 should be ${this.lamda.toString()}`);
    return [new PoissonProcessNode([new Dummy('l1'), sympify(l1)]), new PoissonProcessNode([new Dummy('l2'), sympify(l2)])];
  }
}

/** SymPy PoissonProcess(sym, lamda). */
export const PoissonProcess = /* @__PURE__ */ callableClass(
  PoissonProcessNode,
  (sym: string | Sym, lamda: ExprLike): PoissonProcessNode => new PoissonProcessNode([symbolConverter(sym), sympify(lamda)]),
);
export type PoissonProcess = PoissonProcessNode;

/** SymPy WienerProcess(sym): the Brownian motion, with independent normal increments. */
export class WienerProcessNode extends CountingProcess {
  constructor(args: readonly Expr[]) {
    super(args, 'WienerProcess');
  }
  override get stateSpace(): SetExpr {
    return Reals;
  }
  /** The normal distribution at a time (SymPy distribution(key)). */
  override distribution(key: Expr): Distribution {
    const t = key instanceof RandomIndexedSymbol ? key.indexKey : key;
    return new NormalDistribution([S.Zero, sqrt(t)]);
  }
  override density(x: Expr): Expr {
    const t = keyOf(x);
    return mul(exp(mul(-1, pow(x, 2), pow(mul(2, t), -1))), pow(mul(sqrt(mul(2, S.Pi)), sqrt(t)), -1));
  }
  simpleRv(rv: RandomIndexedSymbol): RandomSymbol {
    return Normal(rv.name, 0, sqrt(rv.indexKey));
  }
}

/** SymPy WienerProcess(sym). */
export const WienerProcess = /* @__PURE__ */ callableClass(WienerProcessNode, (sym: string | Sym): WienerProcessNode => new WienerProcessNode([symbolConverter(sym)]));
export type WienerProcess = WienerProcessNode;

/** SymPy GammaProcess(sym, lamda, gamma): a process with independent gamma increments. */
export class GammaProcessNode extends CountingProcess {
  constructor(args: readonly Expr[]) {
    valueCheck(Gt(at(args, 1), 0), 'lamda should be a positive number');
    valueCheck(Gt(at(args, 2), 0), 'gamma should be a positive number');
    super(args, 'GammaProcess');
  }
  /** SymPy lamda. */
  get lamda(): Expr {
    return at(this.args, 1);
  }
  /** SymPy gamma. */
  get gamma(): Expr {
    return at(this.args, 2);
  }
  override get stateSpace(): SetExpr {
    return setConverter(interval(0, S.Infinity));
  }
  /** The gamma distribution at a time (SymPy distribution(key)). */
  override distribution(key: Expr): Distribution {
    const t = key instanceof RandomIndexedSymbol ? key.indexKey : key;
    return new GammaDistribution([mul(this.gamma, t), pow(this.lamda, -1)]);
  }
  override density(x: Expr): Expr {
    const k = mul(this.gamma, keyOf(x));
    const theta = pow(this.lamda, -1);
    return mul(pow(x, sub(k, 1)), exp(mul(-1, x, pow(theta, -1))), pow(mul(gammaFn(k), pow(theta, k)), -1));
  }
  simpleRv(rv: RandomIndexedSymbol): RandomSymbol {
    return Gamma(rv.name, mul(this.gamma, rv.indexKey), pow(this.lamda, -1));
  }
}

/** SymPy GammaProcess(sym, lamda, gamma). */
export const GammaProcess = /* @__PURE__ */ callableClass(
  GammaProcessNode,
  (sym: string | Sym, lamda: ExprLike, gamma: ExprLike): GammaProcessNode => new GammaProcessNode([symbolConverter(sym), sympify(lamda), sympify(gamma)]),
);
export type GammaProcess = GammaProcessNode;
