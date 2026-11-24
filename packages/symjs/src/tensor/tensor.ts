// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Based on SymPy 1.14 tensor/tensor.py, BSD-3-Clause; see LICENSE.

/**
 * @file SymPy sympy.tensor.tensor: abstract tensors with index types,
 * contravariant and covariant indices, slot symmetries, Einstein
 * contraction, Butler–Portugal canonicalization (`canonBp`), metric
 * contraction and component arrays (`replaceWithArrays`).
 *
 * SymPy's `name` attributes are `typeName`, `indexName` and `tensorName`
 * (`name` is the class name of every node), and calling a head,
 * `A(i, -j)`, is `A.at(i, j.neg())`.
 */

import type { ExprLike } from '../core/nodes';
import type { Expr } from '../core/nodes';
import { Add, BoolAtom, ExtensionExpr, Mul, Rational, S, Sym, Wild, registerArithmetic } from '../core/nodes';
import { callableClass } from '../core/callable';
import { at, cast, defined, expectType, first, last } from '../core/guard';
import { DictNode, Tuple, TupleNode } from '../core/containers';
import { add, couldExtractMinusSign, mul, pow, sympify } from '../core/ops';
import { match } from '../core/match';
import { IndexedBase } from '../core/indexed';
import { Concrete } from '../core/concrete';
import { ExprMap } from '../core/exprmap';
import { NotImplementedError } from '../core/errors';
import { expandSymbolNames } from '../core/numberutils';
import { NoMatch, isNoMatch } from '../core/truth';
import type { NoMatchResult } from '../core/truth';
import { expand as expandExpr } from '../simplify/expand';
import { PREC, precedence } from '../printing/str';
import type { Key } from '../printing/sortkey';
import { compareKeys, sortKey } from '../printing/sortkey';
import { Permutation } from '../combinatorics/permutations';
import { Matrix } from '../matrices/matrix';
import { ImmutableDenseNDimArray, NDimArray, Slice } from './ndimarray';
import type { ArrayInput } from './ndimarray';
import { permutedims, tensorcontraction, tensorproduct } from './arrayop';
import type { Af } from './tensorcan';
import { bsgsDirectProductAf, canonicalize, getSymmetricGroupSgsAf, riemannBsgs } from './tensorcan';

const asRational = (x: unknown): Rational => expectType(x, (v): v is Rational => v instanceof Rational, 'an integer');
const range = (n: number): number[] => Array.from({ length: n }, (_, i) => i);
/** A strict order from a less-than predicate, for stable sorts that mirror Python's. */
const byLt =
  <T>(lt: (a: T, b: T) => boolean) =>
  (a: T, b: T): number =>
    lt(a, b) ? -1 : lt(b, a) ? 1 : 0;

// ---------------------------------------------------------------------------
// Commutation of tensor heads
// ---------------------------------------------------------------------------

/** A commutation group: 0 commuting, 1 anticommuting, 2 neither, or a name. */
export type CommGroup = ExprLike | string;

/** Commutation of two tensors: 0 commuting, 1 anticommuting, 'none' neither. */
export type Commutation = 0 | 1 | 'none';

/**
 * The commutation group of each tensor head (0 commuting, 1 anticommuting, 2 neither, or a named
 * group) and the commutation of the groups with each other.
 *
 * @see SymPy `sympy.tensor.tensor._TensorManager`
 */
export class TensorManagerClass {
  #comm: Map<number, Commutation>[] = [];
  #symbols = new Map<string, number>();
  /** Constructs an instance of `TensorManagerClass`. */
  constructor() {
    this.clear();
  }
  /**
   * Back to the groups 0, 1 and 2.
   *
   * @see SymPy `sympy.tensor.tensor._TensorManager.clear`
   */
  clear(): void {
    this.#comm = [0, 1, 2].map(() => new Map());
    for (const i of [0, 1, 2]) {
      at(this.#comm, 0).set(i, 0);
      at(this.#comm, i).set(0, 0);
    }
    at(this.#comm, 1).set(1, 1);
    at(this.#comm, 2).set(1, 'none');
    at(this.#comm, 1).set(2, 'none');
    this.#symbols = new Map([0, 1, 2].map((i) => [sympify(i).key, i]));
  }
  /**
   * Looks up a commutation group by name, allocating a number for a new group.
   *
   * @param i - First commutation group.
   * @returns The group number.
   * @see SymPy `sympy.tensor.tensor._TensorManager.comm_symbols2i`
   */
  commSymbols2i(i: CommGroup): number {
    const key = commExpr(i).key;
    const known = this.#symbols.get(key);
    if (known !== undefined) return known;
    const n = this.#comm.length;
    this.#comm.push(new Map([[0, 0]]));
    at(this.#comm, 0).set(n, 0);
    this.#symbols.set(key, n);
    return n;
  }
  /**
   * Groups i and j commute (0), anticommute (1) or neither (null).
   *
   * @param i - First commutation group.
   * @param j - Second commutation group.
   * @param c - 0 for commuting, 1 for anticommuting, or null for no relation.
   * @see SymPy `sympy.tensor.tensor._TensorManager.set_comm`
   */
  setComm(i: CommGroup, j: CommGroup, c: 0 | 1 | null): void {
    const ni = this.commSymbols2i(i);
    const nj = this.commSymbols2i(j);
    const v: Commutation = c ?? 'none';
    at(this.#comm, ni).set(nj, v);
    at(this.#comm, nj).set(ni, v);
  }
  /**
   * Registers a sequence of pairwise commutation rules.
   *
   * @param args - Triples of two group identifiers and their commutation relation.
   * @see SymPy `sympy.tensor.tensor._TensorManager.set_comms`
   */
  setComms(...args: [CommGroup, CommGroup, 0 | 1 | null][]): void {
    for (const [i, j, c] of args) this.setComm(i, j, c);
  }
  /**
   * Looks up the commutation rule for two commutation groups.
   *
   * @param i - First commutation group.
   * @param j - Second commutation group.
   * @returns 0 for commuting, 1 for anticommuting, or `'none'` for an unspecified relation.
   * @see SymPy `sympy.tensor.tensor._TensorManager.get_comm`
   */
  getComm(i: number, j: number): Commutation {
    return this.#comm[i]?.get(j) ?? (i === 0 || j === 0 ? 0 : 'none');
  }
}
/** The commutation group name as an expression (a string is a symbol). */
const commExpr = (c: CommGroup): Expr => (typeof c === 'string' ? new Sym(c) : sympify(c));

/**
 * The shared registry of tensor commutation groups and their pairwise relations.
 *
 * @see SymPy `sympy.tensor.tensor.TensorManager`
 */
export const TensorManager = new TensorManagerClass();

// ---------------------------------------------------------------------------
// Index types, indices, symmetries and heads
// ---------------------------------------------------------------------------

/** Options of TensorIndexType. */
export interface TensorIndexTypeOptions {
  /** Prefix of the dummy indices (default: the first letter of the name). */
  dummyName?: string;
  /** Dimension (default: the symbol dim_<dummyName>). */
  dim?: ExprLike;
  /** Dimension of the epsilon tensor (default: dim). */
  epsDim?: ExprLike;
  /** Metric symmetry: 1 symmetric, -1 antisymmetric, 0 none, null no metric. */
  metricSymmetry?: 1 | 0 | -1 | null;
  /** Name of the metric tensor. */
  metricName?: string;
}

/**
 * A family of tensor indices sharing a dimension and an optional metric.
 *
 * @see SymPy `sympy.tensor.tensor.TensorIndexType`
 */
export class TensorIndexTypeNode extends ExtensionExpr {
  #metric: TensorHeadNode | undefined;
  /**
   * Constructs an instance of `TensorIndexTypeNode`.
   *
   * @param name - Symbolic name.
   * @param options - Settings described by {@link TensorIndexTypeOptions}.
   */
  constructor(name: string, options: TensorIndexTypeOptions = {}) {
    const dummyName = options.dummyName ?? name.charAt(0);
    const dim = options.dim === undefined ? new Sym('dim_' + dummyName) : sympify(options.dim);
    const msym = options.metricSymmetry === undefined ? 1 : options.metricSymmetry;
    super('TensorIndexType', [new Sym(name), new Sym(dummyName), dim, options.epsDim === undefined ? dim : sympify(options.epsDim), msym === null ? Tuple() : sympify(msym), new Sym(options.metricName ?? 'metric')]);
  }
  /**
   * Identifies the type to which tensor indices belong by name.
   *
   * @returns The index type name.
   * @see SymPy `sympy.tensor.tensor.TensorIndexType.name`
   */
  get typeName(): string {
    return cast(first(this.args), Sym).name;
  }
  /**
   * Supplies the naming prefix for automatically generated dummy indices.
   *
   * @returns The formatted text.
   * @see SymPy `sympy.tensor.tensor.TensorIndexType.dummy_name`
   */
  get dummyName(): string {
    return cast(at(this.args, 1), Sym).name;
  }
  /**
   * Specifies the dimension of the tensor index space.
   *
   * @returns The index dimension.
   * @see SymPy `sympy.tensor.tensor.TensorIndexType.dim`
   */
  get dim(): Expr {
    return at(this.args, 2);
  }
  /**
   * Specifies the dimension of the alternating tensor for this index type.
   *
   * @returns The Levi-Civita dimension.
   * @see SymPy `sympy.tensor.tensor.TensorIndexType.eps_dim`
   */
  get epsDim(): Expr {
    return at(this.args, 3);
  }
  /**
   * Describes the symmetry of the metric tensor when the index type has one.
   *
   * @returns 1 for symmetric, −1 for antisymmetric, 0 for no symmetry, or `null` for no metric.
   */
  get metricSymmetry(): 1 | 0 | -1 | null {
    const m = at(this.args, 4);
    return m.equals(1) ? 1 : m.equals(-1) ? -1 : m.equals(0) ? 0 : null;
  }
  /**
   * Identifies the metric tensor by its symbolic name.
   *
   * @returns The metric name.
   */
  get metricName(): string {
    return cast(at(this.args, 5), Sym).name;
  }
  /**
   * Obtains the tensor head for this index type's metric, raising an error if no metric exists.
   *
   * @returns The metric tensor head.
   * @throws TypeError when the index type has no metric.
   * @see SymPy `sympy.tensor.tensor.TensorIndexType.metric`
   */
  get metric(): TensorHeadNode {
    const msym = this.metricSymmetry;
    if (msym === null) throw new TypeError(`${this.typeName} has no metric`);
    this.#metric ??= new TensorHeadNode(this.metricName, [this, this], msym === 0 ? TensorSymmetry.noSymmetry(2) : TensorSymmetry.fullySymmetric(2 * msym));
    return this.#metric;
  }
  /**
   * Constructs the identity tensor on this index type.
   *
   * @returns The Kronecker delta head.
   * @see SymPy `sympy.tensor.tensor.TensorIndexType.delta`
   */
  get delta(): TensorHeadNode {
    return new TensorHeadNode('KD', [this, this], TensorSymmetry.fullySymmetric(2));
  }
  /**
   * Obtains the alternating tensor for an integer Levi-Civita dimension.
   *
   * @returns The Levi-Civita tensor head.
   * @throws TypeError when the dimension of the alternating tensor is not an integer.
   * @see SymPy `sympy.tensor.tensor.TensorIndexType.epsilon`
   */
  get epsilon(): TensorHeadNode {
    const n = this.epsDim;
    if (!(n instanceof Rational && n.isInteger)) throw new TypeError(`${this.typeName} has no epsilon tensor: eps_dim ${n.toString()} is not an integer`);
    const k = Number(n.p);
    return new TensorHeadNode('Eps', Array.from({ length: k }, () => this), TensorSymmetry.fullySymmetric(-k));
  }
  /**
   * Rebuilds the expression with replacement arguments in their original order.
   *
   * @param args - Replacement arguments in the same order as `args` on the original expression.
   * @returns The rebuilt expression.
   */
  withArgs(args: readonly Expr[]): Expr {
    const msym = at(args, 4);
    return new TensorIndexTypeNode(cast(first(args), Sym).name, {
      dummyName: cast(at(args, 1), Sym).name,
      dim: at(args, 2),
      epsDim: at(args, 3),
      metricSymmetry: msym instanceof TupleNode ? null : msym.equals(-1) ? -1 : msym.equals(0) ? 0 : 1,
      metricName: cast(at(args, 5), Sym).name,
    });
  }
  /**
   * Formats the expression in plain text.
   *
   * @returns The formatted expression.
   */
  override printStr(): string {
    return this.typeName;
  }
}
/**
 * Constructs an index type for tensors.
 *
 * @param name - Symbolic name.
 * @param options - Settings described by {@link TensorIndexTypeOptions}.
 * @returns The resulting `TensorIndexType` expression.
 * @see SymPy `sympy.tensor.tensor.TensorIndexType`
 * @example
 * ```ts
 * import { TensorIndexType } from '@symjs/symjs';
 *
 * const L = TensorIndexType('Lorentz', { dummyName: 'L' });
 * L.metric; // => metric(Lorentz,Lorentz)
 * ```
 */
export const TensorIndexType = /* @__PURE__ */ callableClass(TensorIndexTypeNode, (name: string, options?: TensorIndexTypeOptions): TensorIndexTypeNode => new TensorIndexTypeNode(name, options));
export type TensorIndexType = TensorIndexTypeNode;

const autogenerated = new Map<string, number>();

/**
 * A named covariant or contravariant index of a specified tensor index type.
 *
 * @see SymPy `sympy.tensor.tensor.TensorIndex`
 */
export class TensorIndexNode extends ExtensionExpr {
  /**
   * An index of a type, contravariant (up) unless `isUp` is false; the name `true` generates a new
   * name `_i0`, `_i1`, ... for the type.
   *
   * @param name - Symbolic name.
   * @param tensorIndexType - Index type specifying the dimension and metric.
   * @param isUp - Use contravariant variance when true and covariant variance when false.
   * @param className - Name of the wrapped geometric entity type.
   * @param extra - Additional defining arguments of the subclass.
   */
  constructor(name: string | true, tensorIndexType: TensorIndexTypeNode, isUp = true, className = 'TensorIndex', extra: readonly Expr[] = []) {
    let n: string;
    if (name === true) {
      const k = autogenerated.get(tensorIndexType.key) ?? 0;
      autogenerated.set(tensorIndexType.key, k + 1);
      n = `_i${k}`;
    } else n = name;
    super(className, [new Sym(n), tensorIndexType, isUp ? S.true : S.false, ...extra]);
  }
  /**
   * Gives the name of the index independently of its variance.
   *
   * @returns The unsigned index name.
   * @see SymPy `sympy.tensor.tensor.TensorIndex.name`
   */
  get indexName(): string {
    return cast(first(this.args), Sym).name;
  }
  /**
   * Identifies the type supplying the dimension and metric for the index.
   *
   * @returns The tensor index type.
   * @see SymPy `sympy.tensor.tensor.TensorIndex.tensor_index_type`
   */
  get tensorIndexType(): TensorIndexTypeNode {
    return cast(at(this.args, 1), TensorIndexTypeNode);
  }
  /**
   * Indicates whether the tensor index is raised.
   *
   * @returns True for a contravariant index.
   * @see SymPy `sympy.tensor.tensor.TensorIndex.is_up`
   */
  get isUp(): boolean {
    return at(this.args, 2) === S.true;
  }
  /**
   * Reverses the variance of the tensor index.
   *
   * @returns The raised or lowered index.
   * @see SymPy `sympy.tensor.tensor.TensorIndex.__neg__`
   */
  override neg(): TensorIndexNode {
    return this.withName(this.indexName, !this.isUp);
  }
  /**
   * Creates an index with the new label and the original type and variance.
   *
   * @param name - New index label.
   * @param isUp - Use contravariant variance when true and covariant variance when false.
   * @returns The renamed index.
   * @internal
   */
  withName(name: string, isUp = this.isUp): TensorIndexNode {
    return new TensorIndexNode(name, this.tensorIndexType, isUp);
  }
  /**
   * Rebuilds the expression with replacement arguments in their original order.
   *
   * @param args - Replacement arguments in the same order as `args` on the original expression.
   * @returns The rebuilt expression.
   */
  withArgs(args: readonly Expr[]): Expr {
    return new TensorIndexNode(cast(first(args), Sym).name, cast(at(args, 1), TensorIndexTypeNode), at(args, 2) === S.true);
  }
  /**
   * Formats the expression in plain text.
   *
   * @returns The formatted expression.
   */
  override printStr(): string {
    return `${this.isUp ? '' : '-'}${this.indexName}`;
  }
  /**
   * Formats the index as a LaTeX superscript or subscript according to its variance.
   *
   * @param print - Formatter for a child expression.
   * @returns The formatted LaTeX.
   */
  override printLatex(print: (e: Expr) => string): string {
    return `{}${this.isUp ? '^' : '_'}{${print(first(this.args))}}`;
  }
  /**
   * Identifies the index label independently of its variance.
   *
   * @returns The formatted text.
   * @internal
   */
  get labelKey(): string {
    return `${this.tensorIndexType.key}:${this.indexName}`;
  }
  /**
   * Tests for an exact match to a plain tensor index.
   *
   * @param expr - Symbolic expression on which to operate.
   * @returns Bindings for the wildcard matches, or `NoMatch` if the pattern fails.
   * @see SymPy `sympy.tensor.tensor.TensorIndex.matches`
   */
  matches(expr: Expr): ExprMap<Expr> | NoMatchResult {
    return expr.equals(this) ? new ExprMap() : NoMatch;
  }
}
/**
 * Constructs a covariant or contravariant index of the supplied type.
 *
 * @param name - Symbolic name.
 * @param type - Type of the tensor indices.
 * @param isUp - Use contravariant variance when true and covariant variance when false.
 * @returns The resulting `TensorIndex` expression.
 * @see SymPy `sympy.tensor.tensor.TensorIndex`
 * @example
 * ```ts
 * import { TensorHead, TensorIndex, TensorIndexType } from '@symjs/symjs';
 *
 * const L = TensorIndexType('Lorentz', { dummyName: 'L' });
 * const mu = TensorIndex('mu', L, false);
 * TensorHead('A', [L, L]).at(mu, mu.neg()); // => A(-L_0, L_0)
 * ```
 */
export const TensorIndex = /* @__PURE__ */ callableClass(TensorIndexNode, (name: string | true, type: TensorIndexTypeNode, isUp = true): TensorIndexNode => new TensorIndexNode(name, type, isUp));
export type TensorIndex = TensorIndexNode;

/**
 * Creates tensor indices of one type from a sequence of names or a symbol range.
 *
 * @param names - Names of the symbols to construct.
 * @param type - Type of the tensor indices.
 * @returns The indices in name order.
 * @see SymPy `sympy.tensor.tensor.tensor_indices`
 * @example
 * ```ts
 * import { TensorIndexType, tensorIndices } from '@symjs/symjs';
 *
 * const L = TensorIndexType('Lorentz', { dummyName: 'L' });
 * tensorIndices('a,b,c,d', L); // => [a, b, c, d]
 * ```
 */
export function tensorIndices(names: string, type: TensorIndexTypeNode): TensorIndexNode[] {
  // the names as SymPy symbols() parses them, ranges such as 'i0:5' included
  return expandSymbolNames(names).map((n) => new TensorIndexNode(n, type));
}

/** SymPy TensorIndex.__lt__: by index type name, then index name. */
function indexLt(a: TensorIndexNode, b: TensorIndexNode): boolean {
  const ta = a.tensorIndexType;
  const tb = b.tensorIndexType;
  if (!ta.equals(tb)) return ta.typeName < tb.typeName;
  return a.indexName < b.indexName;
}
const compareIndices = byLt(indexLt);

const toPermutation = (af: Af): Permutation => new Permutation(af);
const isBsgsPair = (x: readonly number[] | readonly [readonly number[], readonly Permutation[]]): x is readonly [readonly number[], readonly Permutation[]] => Array.isArray(x[0]);

/**
 * The slot symmetry group of a tensor given by a base and strong generating set (permutations of
 * size rank + 2 whose last two points carry the sign). `new TensorSymmetry(rank, sign)` is no
 * symmetry (sign 0) or the fully (anti)symmetric group.
 *
 * @see SymPy `sympy.tensor.tensor.TensorSymmetry`
 * @example
 * ```ts
 * import { TensorSymmetry, getSymmetricGroupSgs } from '@symjs/symjs';
 *
 * new TensorSymmetry(getSymmetricGroupSgs(2)).equals(TensorSymmetry.fullySymmetric(2)); // => True
 * ```
 */
export class TensorSymmetry extends ExtensionExpr {
  /**
   * Constructs an instance of `TensorSymmetry`.
   *
   * @param rank - Number of tensor slots.
   * @param sign - Slot symmetry sign, positive for symmetric and negative for antisymmetric.
   * @param base - Base points of the permutation group.
   * @param generators - Strong generating permutations of the slot symmetry group.
   * @param bsgs - Base and strong generating set of the slot symmetry group.
   * @throws RangeError when the rank is not a nonnegative integer.
   */
  constructor(rank: number, sign?: -1 | 0 | 1);
  constructor(base: readonly number[], generators: readonly Permutation[]);
  constructor(bsgs: readonly [readonly number[], readonly Permutation[]]);
  constructor(a: number | readonly number[] | readonly [readonly number[], readonly Permutation[]], b?: -1 | 0 | 1 | readonly Permutation[]) {
    let bsgs: readonly [readonly number[], readonly Permutation[]];
    if (typeof a === 'number') {
      if (!Number.isInteger(a) || a < 0) throw new RangeError('Tensor rank must be a nonnegative integer');
      bsgs = typeof b === 'number' && b !== 0 ? symmetryBsgs.full(b * a) : symmetryBsgs.none(a);
    } else if (isBsgsPair(a)) bsgs = a;
    else bsgs = [a, expectType(b, (x): x is readonly Permutation[] => Array.isArray(x), 'generators')];
    super('TensorSymmetry', [Tuple(...bsgs[0].map((x) => sympify(x))), Tuple(...bsgs[1])]);
  }
  /**
   * Lists the points in the permutation group's base.
   *
   * @returns The base point array.
   * @see SymPy `sympy.tensor.tensor.TensorSymmetry.base`
   */
  get base(): number[] {
    return first(this.args).args.map((x) => Number(asRational(x).p));
  }
  /**
   * Lists permutations that strongly generate the slot symmetry group.
   *
   * @returns The strong generators.
   * @see SymPy `sympy.tensor.tensor.TensorSymmetry.generators`
   */
  get generators(): Permutation[] {
    return at(this.args, 1).args.map((g) => cast(g, Permutation));
  }
  /**
   * Counts the unbound index slots.
   *
   * @returns The tensor rank.
   * @see SymPy `sympy.tensor.tensor.TensorSymmetry.rank`
   */
  get rank(): number {
    return first(this.generators).size - 2;
  }
  /**
   * Constructs full slot symmetry for a nonnegative rank or antisymmetry for a negative rank.
   *
   * @param rank - Number of tensor slots.
   * @returns The tensor symmetry.
   * @see SymPy `sympy.tensor.tensor.TensorSymmetry.fully_symmetric`
   */
  static fullySymmetric(rank: number): TensorSymmetry {
    return new TensorSymmetry(...symmetryBsgs.full(rank));
  }
  /**
   * Constructs independent symmetric or antisymmetric groups on consecutive slots.
   *
   * @param ranks - Signed ranks of the symmetric or antisymmetric slot groups.
   * @returns The symmetry of the concatenated slot groups.
   * @see SymPy `sympy.tensor.tensor.TensorSymmetry.direct_product`
   */
  static directProduct(...ranks: number[]): TensorSymmetry {
    let base: number[] = [];
    let gens: Af[] = [[0, 1]];
    for (const r of ranks) {
      if (r === 0) continue;
      const [b2, g2] = getSymmetricGroupSgsAf(Math.abs(r), r < 0);
      [base, gens] = bsgsDirectProductAf(base, gens, b2, g2);
    }
    return new TensorSymmetry(base, gens.map(toPermutation));
  }
  /**
   * Constructs the monoterm slot symmetries of a Riemann tensor.
   *
   * @returns The Riemann tensor symmetry.
   * @see SymPy `sympy.tensor.tensor.TensorSymmetry.riemann`
   */
  static riemann(): TensorSymmetry {
    const [base, gens] = riemannBsgs();
    return new TensorSymmetry(base, gens.map(toPermutation));
  }
  /**
   * Constructs the trivial slot symmetry for the specified rank.
   *
   * @param rank - Number of tensor slots.
   * @returns The trivial slot symmetry for the specified rank.
   * @see SymPy `sympy.tensor.tensor.TensorSymmetry.no_symmetry`
   */
  static noSymmetry(rank: number): TensorSymmetry {
    return new TensorSymmetry(...symmetryBsgs.none(rank));
  }
  /**
   * Rebuilds the expression with replacement arguments in their original order.
   *
   * @param args - Replacement arguments in the same order as `args` on the original expression.
   * @returns The rebuilt expression.
   */
  withArgs(args: readonly Expr[]): Expr {
    return new TensorSymmetry(
      first(args).args.map((x) => Number(asRational(x).p)),
      at(args, 1).args.map((g) => cast(g, Permutation)),
    );
  }
}
const symmetryBsgs = {
  full(rank: number): [number[], Permutation[]] {
    if (rank === 0) return [[], [toPermutation([0, 1])]];
    const [base, gens] = getSymmetricGroupSgsAf(Math.abs(rank), rank < 0);
    return [base, gens.map(toPermutation)];
  },
  none: (rank: number): [number[], Permutation[]] => [[], [toPermutation(range(rank + 2))]],
};

/**
 * A tensor symbol with an ordered list of index types, slot symmetry and commutation group.
 *
 * @see SymPy `sympy.tensor.tensor.TensorHead`
 */
export class TensorHeadNode extends ExtensionExpr {
  /**
   * A tensor head with the index types of its slots, their symmetry and its commutation group (0
   * commuting, 1 anticommuting, or a group name).
   *
   * @param name - Symbolic name.
   * @param indexTypes - Index type for each tensor slot.
   * @param symmetry - Permutation symmetries of the tensor slots.
   * @param comm - Tensor commutation group.
   * @param className - Name of the wrapped geometric entity type.
   * @param extra - Additional defining arguments of the subclass.
   * @throws RangeError when the slot symmetry rank differs from the number of slots.
   */
  constructor(name: string, indexTypes: readonly TensorIndexTypeNode[], symmetry?: TensorSymmetry, comm: CommGroup = 0, className = 'TensorHead', extra: readonly Expr[] = []) {
    const sym = symmetry ?? TensorSymmetry.noSymmetry(indexTypes.length);
    if (sym.rank !== indexTypes.length) throw new RangeError('Tensor rank and symmetry rank differ');
    super(className, [new Sym(name), Tuple(...indexTypes), sym, commExpr(comm), ...extra]);
  }
  /**
   * Identifies the tensor head by its symbolic name.
   *
   * @returns The tensor name.
   * @see SymPy `sympy.tensor.tensor.TensorHead.name`
   */
  get tensorName(): string {
    return cast(first(this.args), Sym).name;
  }
  /**
   * Lists the index types required by successive tensor slots.
   *
   * @returns The ordered index types.
   * @see SymPy `sympy.tensor.tensor.TensorHead.index_types`
   */
  get indexTypes(): TensorIndexTypeNode[] {
    return at(this.args, 1).args.map((t) => cast(t, TensorIndexTypeNode));
  }
  /**
   * Describes the allowed permutations of the tensor slots.
   *
   * @returns The slot symmetry object.
   * @see SymPy `sympy.tensor.tensor.TensorHead.symmetry`
   */
  get symmetry(): TensorSymmetry {
    return cast(at(this.args, 2), TensorSymmetry);
  }
  /**
   * Identifies the commutation group of the tensor.
   *
   * @returns The group number.
   * @see SymPy `sympy.tensor.tensor.TensorHead.comm`
   */
  get comm(): number {
    return TensorManager.commSymbols2i(at(this.args, 3));
  }
  /**
   * Counts the unbound index slots.
   *
   * @returns The tensor rank.
   * @see SymPy `sympy.tensor.tensor.TensorHead.rank`
   */
  get rank(): number {
    return this.indexTypes.length;
  }
  /**
   * Raises the metric norm to the given power when explicit components are supplied.
   *
   * @param exponent - Power to which the operand is raised.
   * @param replacements - Tensor or index replacements.
   * @returns The symbolic power, or the power computed from the component contraction when replacements are given.
   * @see SymPy `sympy.tensor.tensor.TensorHead.__pow__`
   */
  override pow(exponent: ExprLike, replacements?: ArrayReplacements): Expr {
    if (!replacements) return super.pow(exponent);
    return this.at(...this.indexTypes.map((_, i) => `component_${i}`)).pow(exponent, replacements);
  }
  /**
   * Looks up the commutation rule for the groups of the two tensor heads.
   *
   * @param other - Tensor or tensor head whose commutation rule is requested.
   * @returns The commutation rule for the two tensor factors.
   * @see SymPy `sympy.tensor.tensor.TensorHead.commutes_with`
   */
  commutesWith(other: TensorHeadNode): Commutation {
    return TensorManager.getComm(this.comm, other.comm);
  }
  /**
   * Applies the tensor head to the supplied indices, interpreting a leading minus sign as a covariant
   * index.
   *
   * @param indices - Indices in slot order.
   * @returns The tensor with the given indices.
   * @throws RangeError when the number of indices does not match the rank.
   * @see SymPy `sympy.tensor.tensor.TensorHead.__call__`
   */
  at(...indices: (TensorIndexNode | string | Expr)[]): Tensor {
    if (indices.length !== this.rank) throw new RangeError('wrong number of indices');
    return cast(new Tensor(this, indices.map((idx, n) => parseIndexString(idx, at(this.indexTypes, n)))).doitShallow(), Tensor);
  }
  /**
   * Rebuilds the expression with replacement arguments in their original order.
   *
   * @param args - Replacement arguments in the same order as `args` on the original expression.
   * @returns The rebuilt expression.
   */
  withArgs(args: readonly Expr[]): Expr {
    return new TensorHeadNode(
      cast(first(args), Sym).name,
      at(args, 1).args.map((t) => cast(t, TensorIndexTypeNode)),
      cast(at(args, 2), TensorSymmetry),
      at(args, 3),
    );
  }
  /**
   * Formats the expression in plain text.
   *
   * @returns The formatted expression.
   */
  override printStr(): string {
    return `${this.tensorName}(${this.indexTypes.map((t) => t.typeName).join(',')})`;
  }
}
/**
 * Constructs a tensor symbol with an ordered list of index types, slot symmetry and commutation group.
 *
 * @param name - Symbolic name.
 * @param types - Index types in tensor slot order.
 * @param symmetry - Permutation symmetries of the tensor slots.
 * @param comm - Tensor commutation group.
 * @returns The resulting `TensorHead` expression.
 * @throws RangeError when the slot symmetry rank differs from the number of slots.
 * @throws RangeError when the symmetry rank differs from the number of index slots.
 * @see SymPy `sympy.tensor.tensor.TensorHead`
 * @example
 * ```ts
 * import { TensorHead, TensorIndexType, TensorSymmetry } from '@symjs/symjs';
 *
 * const L = TensorIndexType('Lorentz', { dummyName: 'L' });
 * const A = TensorHead('A', [L, L], TensorSymmetry.fullySymmetric(-2));
 * A.rank; // => 2
 * ```
 */
export const TensorHead = /* @__PURE__ */ callableClass(
  TensorHeadNode,
  (name: string, types: readonly TensorIndexTypeNode[], symmetry?: TensorSymmetry, comm?: CommGroup): TensorHeadNode => new TensorHeadNode(name, types, symmetry, comm),
);
export type TensorHead = TensorHeadNode;

/**
 * Creates tensor heads sharing index types, slot symmetry and commutation group.
 *
 * @param names - Names of the symbols to construct.
 * @param types - Index types in tensor slot order.
 * @param symmetry - Permutation symmetries of the tensor slots.
 * @param comm - Tensor commutation group.
 * @returns The tensor heads in name order.
 * @throws RangeError when the symmetry rank differs from the number of index slots.
 * @see SymPy `sympy.tensor.tensor.tensor_heads`
 */
export function tensorHeads(names: string, types: readonly TensorIndexTypeNode[], symmetry?: TensorSymmetry, comm?: CommGroup): TensorHeadNode[] {
  return names
    .split(/[\s,]+/)
    .filter(Boolean)
    .map((n) => new TensorHeadNode(n, types, symmetry, comm));
}

/** Python list comparison a < b with an element order. */
function listLt<T extends Expr>(a: readonly T[], b: readonly T[], lt: (x: T, y: T) => boolean): boolean {
  for (let i = 0; i < Math.min(a.length, b.length); i++) if (!at(a, i).equals(at(b, i))) return lt(at(a, i), at(b, i));
  return a.length < b.length;
}

function parseIndexString(idx: TensorIndexNode | string | Expr, type: TensorIndexTypeNode): TensorIndexNode | Expr {
  if (typeof idx !== 'string') return idx;
  const s = idx.trim().replace(/ /g, '');
  return s.startsWith('-') ? new TensorIndexNode(s.slice(1), type, false) : new TensorIndexNode(s, type);
}

// ---------------------------------------------------------------------------
// Index structure
// ---------------------------------------------------------------------------

type Free = [TensorIndexNode, number];
type Dum = [number, number];

/** SymPy _get_generator_for_dummy_indices: dummy names after those already used by the given indices. */
function dummyNameGenerator(used: readonly TensorIndexNode[]): (type: TensorIndexTypeNode) => string {
  const cdt = new Map<string, number>();
  for (const indx of used) {
    const [prefix, num] = indx.indexName.split('_');
    const n = Number(num);
    if (prefix === indx.tensorIndexType.dummyName && Number.isInteger(n)) cdt.set(indx.tensorIndexType.key, Math.max(cdt.get(indx.tensorIndexType.key) ?? 0, n + 1));
  }
  return (type) => {
    const nd = cdt.get(type.key) ?? 0;
    cdt.set(type.key, nd + 1);
    return `${type.dummyName}_${nd}`;
  };
}

/** SymPy _IndexStructure: free indices with positions, dummy position pairs (up, down), index types and indices. */
class IndexStructure {
  readonly dum: Dum[];
  constructor(
    readonly free: Free[],
    dum: Dum[],
    readonly indexTypes: TensorIndexTypeNode[],
    readonly indices: TensorIndexNode[],
  ) {
    this.dum = [...dum].sort((a, b) => a[0] - b[0]);
  }
  get extRank(): number {
    return this.free.length + 2 * this.dum.length;
  }
  static fromIndices(indices: readonly TensorIndexNode[]): IndexStructure {
    const [free, dum] = freeDumFromIndices(indices);
    return new IndexStructure(
      free,
      dum,
      indices.map((i) => i.tensorIndexType),
      replaceDummyNames(indices, free, dum),
    );
  }
  static fromComponentsFreeDum(components: readonly TensorHeadNode[], free: Free[], dum: Dum[]): IndexStructure {
    const indexTypes = components.flatMap((c) => c.indexTypes);
    const indices: TensorIndexNode[] = [];
    for (const [idx, pos] of free) indices[pos] = idx;
    const gen = dummyNameGenerator(free.map(([i]) => i));
    for (const [p1, p2] of dum) {
      const typ = at(indexTypes, p1);
      const name = gen(typ);
      indices[p1] = new TensorIndexNode(name, typ, true);
      indices[p2] = new TensorIndexNode(name, typ, false);
    }
    return new IndexStructure(free, dum, indexTypes, replaceDummyNames(indices, free, dum));
  }
  getIndices(): TensorIndexNode[] {
    return [...this.indices];
  }
  getFreeIndices(): TensorIndexNode[] {
    return [...this.free].sort((a, b) => a[1] - b[1]).map(([i]) => i);
  }
  sortedFree(): Free[] {
    return [...this.free].sort((a, b) => compareIndices(a[0], b[0]));
  }
  /**
   * Computes the permutation that orders the tensor indices, together with the dummy slots and
   * metric symmetry for each index type.
   */
  indicesCanonArgs(): [Af, number[][], (0 | 1 | null)[]] {
    const n = this.extRank;
    const g: Af = [...range(n), n, n + 1];
    this.sortedFree().forEach(([, ipos], i) => {
      g[ipos] = i;
    });
    let pos = this.free.length;
    let j = this.free.length;
    const dummies: number[][] = [];
    const msym: (0 | 1 | null)[] = [];
    let prev: TensorIndexTypeNode | undefined;
    let a: number[] = [];
    for (const [ipos1, ipos2] of this.dum) {
      g[ipos1] = j;
      g[ipos2] = j + 1;
      j += 2;
      const typ = at(this.indexTypes, ipos1);
      if (!prev?.equals(typ)) {
        if (a.length) dummies.push(a);
        a = [pos, pos + 1];
        prev = typ;
        const s = typ.metricSymmetry;
        msym.push(s === 1 ? 0 : s === -1 ? 1 : null);
      } else a.push(pos, pos + 1);
      pos += 2;
    }
    if (a.length) dummies.push(a);
    return [g, dummies, msym];
  }
  /** Builds the index structure obtained by applying the slot permutation `g` to the ordered indices. */
  perm2tensor(g: Af): IndexStructure {
    const sortedFree = this.sortedFree().map(([i]) => i);
    const [perm] = this.indicesCanonArgs();
    const lexTypes: TensorIndexTypeNode[] = [];
    const lexIndices: TensorIndexNode[] = [];
    this.indexTypes.forEach((t, i) => {
      lexTypes[at(perm, i)] = t;
      lexIndices[at(perm, i)] = at(this.indices, i);
    });
    const nfree = sortedFree.length;
    const rank = this.extRank;
    const dum: Dum[] = range((rank - nfree) / 2).map(() => [0, 0]);
    const free: Free[] = [];
    const indexTypes: TensorIndexTypeNode[] = [];
    const indices: TensorIndexNode[] = [];
    for (let i = 0; i < rank; i++) {
      const gi = at(g, i);
      indexTypes.push(at(lexTypes, gi));
      indices.push(at(lexIndices, gi));
      if (gi < nfree) free.push([at(sortedFree, gi), i]);
      else at(dum, Math.floor((gi - nfree) / 2))[(gi - nfree) % 2] = i;
    }
    return new IndexStructure(free, dum, indexTypes, indices);
  }
}

/** SymPy _free_dum_from_indices: the free indices (sorted) and the dummy pairs (up, down) of one tensor. */
function freeDumFromIndices(indices: readonly TensorIndexNode[]): [Free[], Dum[]] {
  if (indices.length === 1) return [[[first(indices), 0]], []];
  const free = indices.map(() => true);
  const seen = new Map<string, [boolean, number]>();
  const dum: Dum[] = [];
  indices.forEach((index, i) => {
    const prev = seen.get(index.labelKey);
    if (prev === undefined) {
      seen.set(index.labelKey, [index.isUp, i]);
      return;
    }
    const [isContr, pos] = prev;
    if (isContr === index.isUp) throw new RangeError(`two equal ${index.isUp ? 'contravariant' : 'covariant'} indices in slots ${pos} and ${i}`);
    free[pos] = false;
    free[i] = false;
    dum.push(index.isUp ? [i, pos] : [pos, i]);
  });
  const fr = indices.flatMap((index, i): Free[] => (free[i] ? [[index, i]] : []));
  fr.sort((a, b) => compareIndices(a[0], b[0]) || a[1] - b[1]);
  return [fr, dum];
}

/** SymPy _replace_dummy_names: dummies renamed L_0, L_1, ... in the order of their up positions. */
function replaceDummyNames(indices: readonly TensorIndexNode[], free: readonly Free[], dumIn: readonly Dum[]): TensorIndexNode[] {
  const dum = [...dumIn].sort((a, b) => a[0] - b[0]);
  const out = [...indices];
  const gen = dummyNameGenerator(free.map(([i]) => i));
  for (const [p1, p2] of dum) {
    const typ = at(out, p1).tensorIndexType;
    const name = gen(typ);
    out[p1] = new TensorIndexNode(name, typ, true);
    out[p2] = new TensorIndexNode(name, typ, false);
  }
  return out;
}

// ---------------------------------------------------------------------------
// Tensor expressions
// ---------------------------------------------------------------------------

type IndexRepl = ReadonlyMap<string, TensorIndexNode>;
/** A replacement dictionary of replaceWithArrays: tensors and index types (metrics) to arrays. */
export type ArrayReplacements = ReadonlyMap<Expr, ArrayInput>;

/**
 * The base class of tensor expressions.
 *
 * @see SymPy `sympy.tensor.tensor.TensExpr`
 */
export abstract class TensExpr extends ExtensionExpr {
  /**
   * Lists all indices in slot order, including contracted indices.
   *
   * @returns The ordered tensor indices.
   * @see SymPy `sympy.tensor.tensor.TensExpr.get_indices`
   */
  abstract getIndices(): TensorIndexNode[];
  /**
   * Lists the uncontracted indices in slot order.
   *
   * @returns The uncontracted indices.
   * @see SymPy `sympy.tensor.tensor.TensExpr.get_free_indices`
   */
  abstract getFreeIndices(): TensorIndexNode[];
  /**
   * Extracts the scalar factor multiplying the tensor part.
   *
   * @returns The scalar coefficient.
   * @see SymPy `sympy.tensor.tensor.TensExpr.coeff`
   */
  abstract get coEff(): Expr;
  /**
   * Removes the overall coefficient from the tensor expression.
   *
   * @returns The coefficient-free expression.
   * @see SymPy `sympy.tensor.tensor.TensExpr.nocoeff`
   */
  abstract get nocoeff(): Expr;
  /**
   * Replaces tensor indices using a map keyed by their structural keys.
   *
   * @param repl - Existing replacement map.
   * @returns The transformed tensor expression.
   * @internal
   */
  abstract replaceIndices(repl: IndexRepl): Expr;
  /**
   * Builds the component array from tensor replacements and tracks its remaining indices.
   *
   * @param repl - Existing replacement map.
   * @returns The remaining indices and their component array.
   * @internal
   */
  abstract extractData(repl: ExprMap<NDimArray>): [TensorIndexNode[], Expr];
  /**
   * Evaluates the outer tensor operation with the current operands.
   *
   * @returns The resulting expression.
   * @internal
   */
  abstract doitShallow(): Expr;
  /**
   * Canonicalizes the tensor under slot permutations, dummy renaming, and commutation rules.
   *
   * @returns The canonical expression.
   */
  abstract canonBp(): Expr;
  /**
   * Metrics g contracted with the other factors.
   *
   * @param g - Metric tensor head to contract.
   * @returns The transformed tensor expression.
   */
  abstract contractMetric(g: TensorHeadNode): Expr;
  /**
   * Substitutes index pairs while respecting index variance.
   *
   * @param indexTuples - Pairs of old and replacement indices.
   * @returns The transformed tensor expression.
   */
  abstract substituteIndices(...indexTuples: [TensorIndexNode, TensorIndexNode][]): Expr;
  /**
   * Evaluate at new free indices in canonical index order.
   *
   * @param indices - Indices in slot order.
   * @returns The tensor expression with its free slots assigned the supplied indices.
   * @throws RangeError when the replacement indices have incompatible types or arity.
   */
  call(...indices: TensorIndexNode[]): Expr {
    const free = this.getFreeIndices().sort(compareIndices);
    if (indices.length !== free.length || !free.every((idx, i) => idx.tensorIndexType.equals(at(indices, i).tensorIndexType))) throw new RangeError('incompatible index types');
    return this.substituteIndices(...free.map((idx, i): [TensorIndexNode, TensorIndexNode] => [idx, at(indices, i)]));
  }
  /**
   * Contract the components with a second copy with all free index variances reversed.
   *
   * @param exponent - Power to which the operand is raised.
   * @param replacements - Tensor or index replacements.
   * @returns The symbolic power, or the powered norm computed from the supplied components.
   * @see SymPy `sympy.tensor.tensor.TensExpr.__pow__`
   */
  override pow(exponent: ExprLike, replacements?: ArrayReplacements): Expr {
    if (!replacements) return super.pow(exponent);
    const free = this.getFreeIndices();
    const dual = this.substituteIndices(...free.map((i): [TensorIndexNode, TensorIndexNode] => [i, i.neg()]));
    const contracted = cast(tensMul(this, dual), TensExpr).replaceWithArrays(replacements);
    return pow(contracted, mul(S.Half, exponent));
  }
  /**
   * Rewrites the tensor expression in the requested representation.
   *
   * @param target - Name of the desired representation.
   * @param args - Operands in their defining order.
   * @returns The specialized result when the hook handles the operands.
   */
  override rewriteSelf(target: string, args: readonly Expr[]): Expr | undefined {
    if (target !== 'Indexed') return undefined;
    if (this instanceof TensAdd) return add(...args);
    if (!(this instanceof Tensor || this instanceof TensMul)) return undefined;
    const entry = (t: Tensor) => new IndexedBase(t.head.tensorName).at(...t.getIndices().map((i) => first(i.args)));
    const body = this instanceof Tensor ? entry(this) : mul(...this.args.map((f, i) => f instanceof Tensor ? entry(f) : at(args, i)));
    const indices = this.getIndices();
    const limits = this.dum.map(([up]) => at(indices, up)).sort(compareIndices).flatMap((i) => [first(i.args), S.Zero, i.tensorIndexType.dim.sub(1)]);
    return limits.length ? new Concrete('Sum', [body, ...limits]) : body;
  }
  /**
   * Substitutes tensor indices using the supplied old and new index pairs.
   *
   * @param indexTuples - Pairs of old and replacement indices.
   * @returns The expression with substituted indices.
   * @see SymPy `sympy.tensor.tensor.TensExpr.fun_eval`
   */
  funEval(...indexTuples: [TensorIndexNode, TensorIndexNode][]): Expr {
    return this.substituteIndices(...indexTuples);
  }
  /**
   * Builds a matrix of components from replacements, using a single column for a rank-one tensor.
   *
   * @param replacements - Tensor or index replacements.
   * @returns The components as a Matrix (a column for rank 1), for an expression of rank 1 or 2.
   * @throws NotImplementedError when the multidimensional expression has no implemented matrix reduction.
   * @see SymPy `sympy.tensor.tensor.TensExpr.get_matrix`
   */
  getMatrix(replacements: ArrayReplacements): Matrix {
    const array = this.replaceWithArrays(replacements);
    if (!(array instanceof NDimArray) || array.rank() < 1 || array.rank() > 2) throw new NotImplementedError('missing multidimensional reduction to matrix.');
    return array.rank() === 2 ? array.tomatrix() : Matrix.of(array.flatElements().map((e) => [e]));
  }
  protected override computeCommutative(): boolean {
    return false;
  }
  /**
   * Evaluates this node when expression evaluation reaches it.
   *
   * @returns The evaluated expression.
   */
  override doitSelf(): Expr {
    return this.doitShallow();
  }
  /**
   * Contracts indices joined by the specified Kronecker delta.
   *
   * @param delta - Kronecker delta tensor to contract.
   * @returns The transformed tensor expression.
   */
  contractDelta(delta: TensorHeadNode): Expr {
    return this.contractMetric(delta);
  }
  /**
   * Products distributed over sums of tensors.
   *
   * @returns The tensor expression with products distributed over sums.
   * @see SymPy `sympy.tensor.tensor.TensExpr.expand`
   */
  override expand(): Expr {
    return expandTens(this);
  }
  /**
   * Builds the expression's component array from tensor and metric arrays, ordering the output axes by
   * the supplied indices.
   *
   * @param replacements - Tensor or index replacements.
   * @param indices - Indices in slot order.
   * @returns The component array in the requested free-index order, or a scalar if all indices are contracted.
   * @throws RangeError when the replacement array dimensions do not match the tensor slots.
   * @see SymPy `sympy.tensor.tensor.TensExpr.replace_with_arrays`
   * @example
   * ```ts
   * import { TensorHead, TensorIndex, TensorIndexType } from '@symjs/symjs';
   *
   * const L = TensorIndexType('L', { dim: 2 });
   * const i = TensorIndex('i', L), v = TensorHead('v', [L]).at(i);
   * v.replaceWithArrays(new Map([[v, [3, 4]]]), [i]); // => [3, 4]
   * ```
   */
  replaceWithArrays(replacements: ArrayReplacements, indices: readonly (TensorIndexNode | Expr)[] = []): Expr {
    const free = this.getFreeIndices();
    const remap = new ExprMap<TensorIndexNode>(free.map((k): [Expr, TensorIndexNode] => [k.isUp ? first(k.args) : mul(-1, first(k.args)), k]));
    const idx = indices.map((index) => (index instanceof TensorIndexNode ? index : (remap.get(index) ?? defined(remap.get(mul(-1, index)), `index ${index.toString()}`).neg())));
    const repl = new ExprMap<NDimArray>();
    for (const [tensor, array] of replacements) {
      const arr = new ImmutableDenseNDimArray(array);
      const expected = tensor instanceof TensorIndexTypeNode ? [tensor.dim, tensor.dim] : cast(tensor, Tensor).component.indexTypes.map((t) => t.dim);
      if (expected.length !== arr.rank() || !expected.every((d, k) => !d.isNumber || d.equals(at(arr.shape, k)))) {
        throw new RangeError(`shapes for tensor ${tensor.toString()} expected to be ${expected.join(', ')}, replacement array shape is ${arr.shape.join(', ')}`);
      }
      repl.set(tensor, arr);
    }
    const [retIndices, array] = this.extractData(repl);
    return matchIndicesWithOtherTensor(array, idx, retIndices, repl)[1];
  }
  /**
   * Matches the tensor pattern against an expression for pattern-based operations.
   *
   * @param expr - Symbolic expression on which to operate.
   * @returns The bindings or `false` on mismatch.
   */
  override matchesSelf(expr: Expr): ReadonlyMap<Expr, Expr> | false {
    const m = this.matches(expr);
    return isNoMatch(m) ? false : m;
  }
  /**
   * Matches the tensor pattern to the expression.
   *
   * @param expr - Symbolic expression on which to operate.
   * @param replDict - Bindings already fixed in the match.
   * @returns The replacement map or `NoMatch`.
   * @see SymPy `sympy.tensor.tensor.TensExpr.matches`
   */
  matches(expr: ExprLike, replDict?: ReadonlyMap<Expr, Expr>): ExprMap<Expr> | NoMatchResult {
    return this.matchInternal(sympify(expr), new ExprMap(replDict));
  }
  /**
   * Matches a tensor pattern against an expression using the existing bindings.
   *
   * @param expr - Symbolic expression on which to operate.
   * @param repl - Existing replacement map.
   * @returns The extended bindings, or `NoMatch` if matching fails.
   * @throws NotImplementedError when the pattern contains unsupported wildcard tensor factors.
   * @internal
   */
  matchInternal(expr: Expr, repl: ExprMap<Expr>): ExprMap<Expr> | NoMatchResult {
    if (wildsOf(this).length) throw new NotImplementedError(`matching ${this.name} patterns with wild tensors`);
    return matchesSimple(this, expr, repl);
  }
}

const isTens = (e: unknown): e is TensExpr => e instanceof TensExpr;
const getIndicesOf = (t: Expr): TensorIndexNode[] => (isTens(t) ? t.getIndices() : []);
const getFreeIndicesOf = (t: Expr): TensorIndexNode[] => (isTens(t) ? t.getFreeIndices() : []);
function getDummyIndicesOf(t: Expr): TensorIndexNode[] {
  const free = new Set(getFreeIndicesOf(t).map((i) => i.key));
  return getIndicesOf(t).filter((i) => !free.has(i.key));
}
const keySet = (xs: readonly Expr[]): Set<string> => new Set(xs.map((x) => x.key));
const sameKeySet = (a: Set<string>, b: Set<string>): boolean => a.size === b.size && [...a].every((k) => b.has(k));

/** SymPy _matches_simple: equal free indices and canon_bp(self - expr) == 0. */
function matchesSimple(self: TensExpr, expr: Expr, repl: ExprMap<Expr>): ExprMap<Expr> | NoMatchResult {
  if (!isTens(expr)) {
    if (self.getFreeIndices().length) return NoMatch;
  } else if (!sameKeySet(keySet(self.getFreeIndices()), keySet(expr.getFreeIndices()))) return NoMatch;
  return canonBp(tensAdd(self, neg(expr))).equals(0) ? repl : NoMatch;
}

/** The wild symbols and wild tensor objects in an expression (SymPy _get_wilds). */
function wildsOf(e: Expr): Expr[] {
  if (e instanceof Wild || e instanceof WildTensor || e instanceof WildTensorIndexNode || e instanceof WildTensorHeadNode) return [e];
  return e.args.flatMap(wildsOf);
}

/**
 * An indexed tensor formed by applying a tensor head to its indices.
 *
 * @see SymPy `sympy.tensor.tensor.Tensor`
 * @example
 * ```ts
 * import { Tensor, TensorHead, TensorIndex, TensorIndexType } from '@symjs/symjs';
 *
 * const L = TensorIndexType('Lorentz', { dummyName: 'L' });
 * const mu = TensorIndex('mu', L), A = TensorHead('A', [L, L]);
 * new Tensor(A, [mu, mu.neg()]); // => A(mu, -mu)
 * ```
 */
export class Tensor extends TensExpr {
  /**
   * The index types, free indices and dummy contractions of the expression.
   *
   * @internal
   */
  readonly indexStructure: IndexStructure;
  /** Whether the indices have already been put in Butler–Portugal canonical form. */
  readonly isCanonBp: boolean;
  /**
   * A symbol or -symbol is a contravariant or covariant index of the slot type.
   *
   * @param head - Tensor head defining the slots of this tensor.
   * @param indices - Indices in slot order.
   * @param isCanonBp - Whether the input is already in canonical index order.
   * @throws RangeError when the number of indices does not match the rank.
   * @throws TypeError when an index cannot be interpreted for its slot.
   */
  constructor(head: TensorHeadNode, indices: readonly (TensorIndexNode | Expr)[], isCanonBp = false) {
    const types = head.indexTypes;
    if (head.rank !== indices.length) throw new RangeError('wrong number of indices');
    const parsed = indices.map((index, i): TensorIndexNode => {
      if (index instanceof TensorIndexNode) return index;
      if (index instanceof Sym) return new TensorIndexNode(index.name, at(types, i), true);
      if (index instanceof Mul && index.args.length === 2 && first(index.args).equals(-1) && at(index.args, 1) instanceof Sym) {
        return new TensorIndexNode(cast(at(index.args, 1), Sym).name, at(types, i), false);
      }
      throw new TypeError(`index not understood: ${index.toString()}`);
    });
    const structure = IndexStructure.fromIndices(parsed);
    super(head instanceof WildTensorHeadNode ? 'WildTensor' : 'Tensor', [head, Tuple(...parsed)]);
    this.indexStructure = structure;
    this.isCanonBp = isCanonBp;
  }
  /**
   * Identifies the tensor head applied in this factor.
   *
   * @returns The tensor head.
   * @see SymPy `sympy.tensor.tensor.Tensor.head`
   */
  get head(): TensorHeadNode {
    return cast(first(this.args), TensorHeadNode);
  }
  /**
   * Identifies the tensor head applied in this factor.
   *
   * @returns The tensor head.
   * @see SymPy `sympy.tensor.tensor.Tensor.component`
   */
  get component(): TensorHeadNode {
    return this.head;
  }
  /**
   * Lists tensor heads in the order of their factors.
   *
   * @returns The tensor heads in factor order.
   * @see SymPy `sympy.tensor.tensor.Tensor.components`
   */
  get components(): TensorHeadNode[] {
    return [this.head];
  }
  /**
   * Lists the index types required by successive tensor slots.
   *
   * @returns The ordered index types.
   * @see SymPy `sympy.tensor.tensor.Tensor.index_types`
   */
  get indexTypes(): TensorIndexTypeNode[] { return this.head.indexTypes; }
  /**
   * Lists indices in the order of the tensor or array slots.
   *
   * @returns The ordered indices.
   * @see SymPy `sympy.tensor.tensor.Tensor.indices`
   */
  get indices(): TensorIndexNode[] {
    return at(this.args, 1).args.map((i) => cast(i, TensorIndexNode));
  }
  /**
   * Locates each uncontracted index in the expression's slots.
   *
   * @returns The free index–position pairs.
   * @see SymPy `sympy.tensor.tensor.Tensor.free`
   */
  get free(): Free[] {
    return [...this.indexStructure.free];
  }
  /**
   * Identifies the slots linked by each dummy contraction.
   *
   * @returns The contracted slot pairs.
   * @see SymPy `sympy.tensor.tensor.Tensor.dum`
   */
  get dum(): Dum[] {
    return [...this.indexStructure.dum];
  }
  /**
   * Counts index slots before dummy indices are contracted.
   *
   * @returns The external rank.
   * @see SymPy `sympy.tensor.tensor.Tensor.ext_rank`
   */
  get extRank(): number {
    return this.indexStructure.extRank;
  }
  /**
   * Extracts the numerical or symbolic scalar factor of the tensor expression.
   *
   * @returns The scalar coefficient.
   * @see SymPy `sympy.tensor.tensor.Tensor.coeff`
   */
  get coEff(): Expr {
    return S.One;
  }
  /**
   * Factors out the scalar multiplier of the tensor expression.
   *
   * @returns The coefficient-free tensor expression.
   * @see SymPy `sympy.tensor.tensor.Tensor.nocoeff`
   */
  get nocoeff(): Expr {
    return this;
  }
  /**
   * Counts the indices left uncontracted.
   *
   * @returns The free rank.
   * @see SymPy `sympy.tensor.tensor.Tensor.rank`
   */
  get rank(): number {
    return this.indexStructure.free.length;
  }
  /**
   * Orders the free indices canonically.
   *
   * @returns The sorted free indices.
   * @see SymPy `sympy.tensor.tensor.Tensor.free_args`
   */
  get freeArgs(): TensorIndexNode[] {
    return this.indexStructure.free.map(([i]) => i).sort(compareIndices);
  }
  /**
   * Lists the tensor indices in slot order, including contracted indices.
   *
   * @returns The ordered tensor indices.
   * @see SymPy `sympy.tensor.tensor.Tensor.get_indices`
   */
  getIndices(): TensorIndexNode[] {
    return this.indices;
  }
  /**
   * Lists the uncontracted indices in slot order.
   *
   * @returns The uncontracted indices.
   * @see SymPy `sympy.tensor.tensor.Tensor.get_free_indices`
   */
  getFreeIndices(): TensorIndexNode[] {
    return this.indexStructure.getFreeIndices();
  }
  /**
   * Rebuilds the expression with replacement arguments in their original order.
   *
   * @param args - Replacement arguments in the same order as `args` on the original expression.
   * @returns The rebuilt expression.
   */
  withArgs(args: readonly Expr[]): Expr {
    return new Tensor(
      cast(first(args), TensorHeadNode),
      at(args, 1).args.map((i) => cast(i, TensorIndexNode)),
    );
  }
  /**
   * Replaces tensor indices using a map keyed by their structural keys.
   *
   * @param repl - Existing replacement map.
   * @returns The transformed tensor expression.
   */
  replaceIndices(repl: IndexRepl): Expr {
    return new Tensor(
      this.head,
      this.indices.map((i) => repl.get(i.key) ?? i),
    );
  }
  /**
   * Evaluates the outer tensor operation with the current operands.
   *
   * @returns The resulting expression.
   */
  doitShallow(): Expr {
    return first(contractIndices([this], true).args);
  }
  /**
   * Rebuilds the tensor with the supplied indices in slot order.
   *
   * @param indices - Indices in slot order.
   * @param isCanonBp - Whether the input is already in canonical index order.
   * @returns The tensor expression with the supplied index slots.
   * @see SymPy `sympy.tensor.tensor.Tensor._set_indices`
   * @internal
   */
  setIndices(indices: readonly TensorIndexNode[], isCanonBp = false): Expr {
    return new Tensor(this.head, indices, isCanonBp).doitShallow();
  }
  /**
   * Determines the commutation rule for this tensor and the other expression.
   *
   * @param other - Tensor or tensor head whose commutation rule is requested.
   * @returns The commutation rule for the two tensor factors.
   * @see SymPy `sympy.tensor.tensor.Tensor.commutes_with`
   */
  commutesWith(other: Expr): Commutation {
    return other instanceof Tensor ? this.component.commutesWith(other.component) : 0;
  }
  /**
   * Lists this single tensor as the sole factor.
   *
   * @returns A one-element array containing this tensor.
   * @see SymPy `sympy.tensor.tensor.Tensor.split`
   */
  split(): Expr[] {
    return [this];
  }
  /**
   * Preserves the component order of an individual tensor.
   *
   * @returns The tensor expression with components in canonical order.
   * @see SymPy `sympy.tensor.tensor.Tensor.sorted_components`
   */
  sortedComponents(): Tensor {
    return this;
  }
  /**
   * Canonicalizes tensor products under index symmetries using the Butler–Portugal algorithm.
   *
   * @returns The transformed tensor expression.
   * @see SymPy `sympy.tensor.tensor.Tensor.canon_bp`
   */
  canonBp(): Expr {
    return this.isCanonBp ? this : canonicalForm(this);
  }
  /**
   * Substitutes index pairs while respecting index variance.
   *
   * @param indexTuples - Pairs of old and replacement indices.
   * @returns The transformed tensor expression.
   * @see SymPy `sympy.tensor.tensor.Tensor.substitute_indices`
   */
  substituteIndices(...indexTuples: [TensorIndexNode, TensorIndexNode][]): Expr {
    const indices = this.indices.map((index) => {
      const hit = indexTuples.find(([old]) => old.labelKey === index.labelKey);
      if (!hit) return index;
      return hit[0].isUp === index.isUp ? hit[1] : hit[1].neg();
    });
    return this.head.at(...indices);
  }
  /**
   * Contracts pairs of indices using the given metric tensor.
   *
   * @param g - Metric tensor head to contract.
   * @returns The transformed tensor expression.
   * @see SymPy `sympy.tensor.tensor.Tensor.contract_metric`
   */
  contractMetric(g: TensorHeadNode): Expr {
    if (!this.component.equals(g) || this.indexStructure.free.length) return this;
    const antisym = metricAntisym(g);
    // g(i, -i) is the dimension, -dim for an antisymmetric metric with the up index first
    const dim = first(g.indexTypes).dim;
    return antisym === 1 && first(this.dum)[0] < first(this.dum)[1] ? mul(-1, dim) : dim;
  }
  /**
   * Builds the component array from tensor replacements and tracks its remaining indices.
   *
   * @param repl - Existing replacement map.
   * @returns The remaining indices and their component array.
   * @throws NotImplementedError when the tensor to match contains contractions.
   * @throws RangeError when the replacement map has no entry for the requested tensor.
   * @see SymPy `sympy.tensor.tensor.Tensor._extract_data`
   */
  extractData(repl: ExprMap<NDimArray>): [TensorIndexNode[], Expr] {
    const found = [...repl].find(([k]) => k instanceof Tensor && k.head.equals(this.head));
    if (!found) throw new RangeError(`${this.toString()} not found in the replacement dictionary`);
    let other = cast(found[0], Tensor);
    let array: Expr = found[1];
    const dum2 = other.dum;
    const hasPair = (ds: readonly Dum[], p: Dum): boolean => ds.some((d) => d[0] === p[0] && d[1] === p[1]);
    if (dum2.some((p) => !hasPair(this.dum, p))) throw new NotImplementedError(`${other.toString()} with contractions is not implemented`);
    const dum1 = this.dum.filter((p) => !hasPair(dum2, p));
    if (dum1.length) {
      const indices1 = this.getIndices();
      const indices2 = other.getIndices();
      const r = new Map<string, TensorIndexNode>();
      for (const [p1, p2] of dum1) {
        r.set(at(indices2, p2).key, at(indices2, p1).neg());
        for (const pos of [p1, p2]) {
          const i1 = at(indices1, pos);
          if (i1.isUp !== at(indices2, pos).isUp) {
            const metric = metricArray(repl, i1.tensorIndexType);
            array = contractAndPermuteWithMetric(i1.isUp ? inverseArray(metric) : metric, array, pos, indices2.length);
          }
        }
      }
      other = cast(cast(other.replaceIndices(r), Tensor).doitShallow(), Tensor);
      array = dataContractDum([array], dum1);
    }
    return matchIndicesWithOtherTensor(array, this.getFreeIndices(), other.getFreeIndices(), repl);
  }
  /**
   * Enumerates the signed forms obtained from the tensor's slot symmetries.
   *
   * @returns The symmetry-related expressions.
   */
  symmetrizedForms(): Expr[] {
    const gens = this.component.symmetry.generators;
    const rank = this.component.rank;
    const forms = new ExprMap<Expr>([[this, this]]);
    for (let size = 0; size !== forms.size; ) {
      size = forms.size;
      for (const tens of [...forms.values()]) {
        for (const gen of gens) {
          const af = gen.arrayForm;
          const inds = getIndicesOf(tens);
          const indMap = new Map(inds.map((ind, k): [string, TensorIndexNode] => [ind.key, at(inds, at(af, k))]));
          const sign = at(af, rank) === rank ? 1 : -1;
          const t = cast(tens instanceof TensMul ? last(tens.args) : tens, Tensor);
          const f = tensMul(sign * (tens instanceof TensMul ? -1 : 1), t.replaceIndices(indMap));
          forms.set(f, f);
        }
      }
    }
    return [...forms.values()];
  }
  /**
   * Matches a tensor pattern against an expression using the existing bindings.
   *
   * @param expr - Symbolic expression on which to operate.
   * @param repl - Existing replacement map.
   * @returns The extended bindings, or `NoMatch` if matching fails.
   */
  override matchInternal(expr: Expr, repl: ExprMap<Expr>): ExprMap<Expr> | NoMatchResult {
    if (this.equals(expr)) return repl;
    if (!(expr instanceof Tensor) || !this.head.equals(expr.head)) return NoMatch;
    for (const form of expr.symmetrizedForms()) {
      const m = this.matchesForm(form, repl);
      if (m instanceof ExprMap) return m;
    }
    return NoMatch;
  }
  /**
   * Matches the tensor indices in corresponding slots.
   *
   * @param expr - Symbolic expression on which to operate.
   * @param replIn - Existing replacement map.
   * @returns A map of index bindings, or `NoMatch` if a slot fails to match.
   * @see SymPy `sympy.tensor.tensor.Tensor._matches`
   */
  matchesForm(expr: Expr, replIn: ExprMap<Expr>): ExprMap<Expr> | NoMatchResult {
    if (!(expr instanceof Tensor)) return NoMatch;
    const repl = new ExprMap(replIn);
    const eIndices = expr.getIndices();
    for (const [k, sInd] of this.getIndices().entries()) {
      const m = sInd.matches(at(eIndices, k));
      if (!(m instanceof ExprMap)) return NoMatch;
      const prev = repl.get(sInd.neg());
      if (prev !== undefined && !cast(prev, TensorIndexNode).neg().equals(defined(m.get(sInd)))) return NoMatch;
      for (const [a, b] of m) {
        const prior = repl.get(a);
        if (prior && !prior.equals(b)) return NoMatch;
        repl.set(a, b);
      }
    }
    return repl;
  }
  /**
   * Formats the expression in plain text.
   *
   * @param print - Formatter for a child expression.
   * @returns The formatted expression.
   */
  override printStr(print: (e: Expr) => string): string {
    return this.component.rank > 0 ? `${this.component.tensorName}(${this.indices.map(print).join(', ')})` : this.component.tensorName;
  }
  /**
   * Formats the tensor name followed by runs of upper and lower indices.
   *
   * @param print - Formatter for a child expression.
   * @returns The formatted LaTeX.
   */
  override printLatex(print: (e: Expr) => string): string {
    return tensorIndicesLatex(first(this.component.args), this.getIndices(), new ExprMap(), print);
  }
}

/** SymPy `_printer_tensor_indices`: the name and the indices grouped by variance, with their fixed values. */
function tensorIndicesLatex(name: Expr, indices: readonly TensorIndexNode[], indexMap: ExprMap<Expr>, print: (e: Expr) => string): string {
  let out = print(name);
  let lastUp: boolean | undefined;
  let prevMapped = false;
  for (const index of indices) {
    const value = indexMap.get(index);
    if ((value !== undefined || prevMapped) && lastUp === index.isUp) out += ',';
    if (lastUp !== index.isUp) {
      if (lastUp !== undefined) out += '}';
      out += index.isUp ? '{}^{' : '{}_{';
    }
    out += print(first(index.args));
    if (value !== undefined) out += `=${print(value)}`;
    prevMapped = value !== undefined;
    lastUp = index.isUp;
  }
  return lastUp === undefined ? out : `${out}}`;
}

/** The symmetry of a metric head: 1 antisymmetric, 0 symmetric, null none. */
function metricAntisym(g: TensorHeadNode): 0 | 1 | null {
  if (g.symmetry.equals(TensorSymmetry.fullySymmetric(-2))) return 1;
  if (g.symmetry.equals(TensorSymmetry.fullySymmetric(2))) return 0;
  if (g.symmetry.equals(TensorSymmetry.noSymmetry(2))) return null;
  throw new NotImplementedError('contraction with a metric of general symmetry');
}

// ---------------------------------------------------------------------------
// Products
// ---------------------------------------------------------------------------

type DummyData = [TensorIndexNode, number, number, number, number];

/** SymPy _indices_to_free_dum. */
function indicesToFreeDum(argsIndices: readonly TensorIndexNode[][]): { indices: TensorIndexNode[]; free: Free[]; freeNames: string[]; dummyData: DummyData[] } {
  const free = new Map<string, [TensorIndexNode, number, number]>();
  const dummyData: DummyData[] = [];
  const indices: TensorIndexNode[] = [];
  let pos2 = 0;
  argsIndices.forEach((argIndices, pos1) => {
    for (const index of argIndices) {
      const negKey = index.neg().key;
      const other = free.get(negKey);
      if (other) {
        free.delete(negKey);
        dummyData.push(index.isUp ? [index, pos1, other[1], pos2, other[2]] : [index.neg(), other[1], pos1, other[2], pos2]);
      } else if (free.has(index.key)) throw new RangeError(`Repeated index: ${index.toString()}`);
      else free.set(index.key, [index, pos1, pos2]);
      indices.push(index);
      pos2++;
    }
  });
  dummyData.sort((a, b) => a[3] - b[3]);
  const fr = [...free.values()].map(([i, , p]): Free => [i, p]);
  return { indices, free: fr, freeNames: fr.map(([i]) => i.indexName), dummyData };
}

/**
 * Finds free indices and contracted pairs across the tensor factors, assigning fresh names to
 * dummy indices when `replace` is true.
 */
export function contractIndices(argsIn: readonly Expr[], replace: boolean): { args: Expr[]; indices: TensorIndexNode[]; free: Free[]; dum: Dum[] } {
  let args = [...argsIn];
  let r = indicesToFreeDum(args.map(getIndicesOf));
  if (replace && r.dummyData.length) {
    const cdt = new Map<string, number>();
    const replacements = args.map(() => new Map<string, TensorIndexNode>());
    for (const [old, pos1cov, pos1contra] of r.dummyData) {
      const type = old.tensorIndexType;
      let name: string;
      do {
        const nd = cdt.get(type.key) ?? 0;
        cdt.set(type.key, nd + 1);
        name = `${type.dummyName}_${nd}`;
      } while (r.freeNames.includes(name));
      const dummy = old.withName(name);
      at(replacements, pos1cov).set(old.key, dummy);
      at(replacements, pos1contra).set(old.neg().key, dummy.neg());
    }
    args = args.map((a, k) => (isTens(a) ? a.replaceIndices(at(replacements, k)) : a));
    r = indicesToFreeDum(args.map(getIndicesOf));
  }
  return { args, indices: r.indices, free: r.free, dum: r.dummyData.map((d): Dum => [d[3], d[4]]) };
}

/** SymPy TensMul._dedupe_indices: the dummies of `e` that clash with `exclude` renamed. */
function dedupeIndices(e: Expr, excludeIn: readonly TensorIndexNode[]): Expr {
  const exclude = keySet(excludeIn);
  const dums = getDummyIndicesOf(e);
  const conflicts = dums.filter((d) => exclude.has(d.key));
  const gen = dummyNameGenerator([...excludeIn, ...dums, ...getFreeIndicesOf(e)]);
  const repl = new Map<string, TensorIndexNode>();
  for (const d of conflicts) {
    if (repl.has(d.neg().key)) continue;
    const nd = d.withName(gen(d.tensorIndexType));
    repl.set(d.key, nd);
    repl.set(d.neg().key, nd.neg());
  }
  return cast(e, TensExpr).replaceIndices(repl);
}

/**
 * An ordered product of tensor factors and scalar coefficients.
 *
 * @see SymPy `sympy.tensor.tensor.TensMul`
 */
export class TensMul extends TensExpr {
  /**
   * Build a product from slot positions for its free and dummy indices.
   *
   * @param coeff - Scalar coefficient of the product.
   * @param components - Coefficients indexed by basis elements.
   * @param free - The uncontracted indices paired with their slot positions.
   * @param dum - Pairs of slot positions joined by dummy-index contractions.
   * @returns The resulting expression.
   * @see SymPy `sympy.tensor.tensor.TensMul.from_data`
   */
  static fromData(coeff: ExprLike, components: TensorHeadNode[], free: Free[], dum: Dum[]): Expr {
    const indices = IndexStructure.fromComponentsFreeDum(components, free, dum).getIndices();
    let offset = 0;
    return tensMul(coeff, ...components.map((head) => {
      const start = offset;
      offset += head.rank;
      return new Tensor(head, indices.slice(start, offset));
    }));
  }
  /**
   * Lists the index types required by successive tensor slots.
   *
   * @returns The ordered index types.
   * @see SymPy `sympy.tensor.tensor.TensMul.index_types`
   */
  get indexTypes(): TensorIndexTypeNode[] { return [...this.indexStructure.indexTypes]; }
  /**
   * The index types, free indices and dummy contractions of the expression.
   *
   * @internal
   */
  readonly indexStructure: IndexStructure;
  /** Whether the indices have already been put in Butler–Portugal canonical form. */
  readonly isCanonBp: boolean;
  /**
   * Constructs a `TensMul` instance.
   *
   * @param argsIn - Operands in their defining order.
   * @param isCanonBp - Whether the input is already in canonical index order.
   */
  constructor(argsIn: readonly ExprLike[], isCanonBp = false) {
    const args0 = argsIn.map(sympify);
    // the dummies of one factor that clash with free indices of the others are renamed
    const freeAll = args0.flatMap(getFreeIndicesOf);
    const occupied = keySet(freeAll);
    const deduped: Expr[] = [];
    for (const arg of args0) {
      const clash = getDummyIndicesOf(arg).some((d) => occupied.has(d.key));
      const factor = clash ? dedupeIndices(arg, [...freeAll, ...deduped.flatMap(getDummyIndicesOf)]) : arg;
      deduped.push(factor);
      for (const d of getDummyIndicesOf(factor)) occupied.add(d.key);
    }
    const flat = deduped.flatMap((a) => (a instanceof TensMul || a instanceof Mul ? a.args : [a]));
    const { args, indices, free, dum } = contractIndices(flat, false);
    super('TensMul', args);
    this.indexStructure = new IndexStructure(
      free,
      dum,
      indices.map((i) => i.tensorIndexType),
      indices,
    );
    this.isCanonBp = isCanonBp;
  }
  /**
   * Extracts the numerical or symbolic scalar factor of the tensor expression.
   *
   * @returns The scalar coefficient.
   * @see SymPy `sympy.tensor.tensor.TensMul.coeff`
   */
  get coEff(): Expr {
    return mul(...this.args.filter((a) => !isTens(a)));
  }
  /**
   * Factors out the scalar multiplier of the tensor expression.
   *
   * @returns The coefficient-free tensor expression.
   * @see SymPy `sympy.tensor.tensor.TensMul.nocoeff`
   */
  get nocoeff(): Expr {
    return tensMul(...this.args, pow(this.coEff, -1));
  }
  /**
   * Collects tensor heads from the factors, excluding sums.
   *
   * @returns The tensor heads in factor order.
   * @see SymPy `sympy.tensor.tensor.TensMul.components`
   */
  get components(): TensorHeadNode[] {
    return this.args.flatMap((a) => (a instanceof Tensor ? [a.component] : []));
  }
  /**
   * Locates each uncontracted index in the expression's slots.
   *
   * @returns The free index–position pairs.
   * @see SymPy `sympy.tensor.tensor.TensMul.free`
   */
  get free(): Free[] {
    return [...this.indexStructure.free];
  }
  /**
   * Identifies the slots linked by each dummy contraction.
   *
   * @returns The contracted slot pairs.
   * @see SymPy `sympy.tensor.tensor.TensMul.dum`
   */
  get dum(): Dum[] {
    return [...this.indexStructure.dum];
  }
  /**
   * Counts index slots before dummy indices are contracted.
   *
   * @returns The external rank.
   * @see SymPy `sympy.tensor.tensor.TensMul.ext_rank`
   */
  get extRank(): number {
    return this.indexStructure.extRank;
  }
  /**
   * Counts the indices left uncontracted.
   *
   * @returns The free rank.
   * @see SymPy `sympy.tensor.tensor.TensMul.rank`
   */
  get rank(): number {
    return this.indexStructure.free.length;
  }
  /**
   * Orders the free indices canonically.
   *
   * @returns The sorted free indices.
   * @see SymPy `sympy.tensor.tensor.TensMul.free_args`
   */
  get freeArgs(): TensorIndexNode[] {
    return this.indexStructure.free.map(([i]) => i).sort(compareIndices);
  }
  /**
   * Lists the tensor indices in slot order, including contracted indices.
   *
   * @returns The ordered tensor indices.
   * @see SymPy `sympy.tensor.tensor.TensMul.get_indices`
   */
  getIndices(): TensorIndexNode[] {
    return this.indexStructure.getIndices();
  }
  /**
   * Lists the uncontracted indices in slot order.
   *
   * @returns The uncontracted indices.
   * @see SymPy `sympy.tensor.tensor.TensMul.get_free_indices`
   */
  getFreeIndices(): TensorIndexNode[] {
    return this.indexStructure.getFreeIndices();
  }
  /**
   * Rebuilds the expression with replacement arguments in their original order.
   *
   * @param args - Replacement arguments in the same order as `args` on the original expression.
   * @returns The rebuilt expression.
   */
  withArgs(args: readonly Expr[]): Expr {
    return new TensMul(args);
  }
  /**
   * Substitutes one expression for another inside this node.
   *
   * @param old - Expression to replace.
   * @param nw - Expression to substitute in its place.
   * @returns The specialized result when the hook handles the operands.
   * @see SymPy `sympy.tensor.tensor.TensMul._eval_subs`
   */
  override subsSelf(old: Expr, nw: Expr): Expr | undefined {
    if (!(old instanceof TensorIndexNode && nw instanceof TensorIndexNode) || !this.getFreeIndices().some((i) => i.equals(old))) return undefined;
    const fresh = cast(dedupeIndices(this, [nw, nw.neg()]), TensMul);
    return fresh.replaceIndices(new Map([[old.key, nw]]));
  }
  /**
   * Matches a tensor pattern against an expression using the existing bindings.
   *
   * @param expr - Symbolic expression on which to operate.
   * @param initial - Initial values or starting expression.
   * @returns The extended bindings, or `NoMatch` if matching fails.
   * @throws NotImplementedError when a wildcard product contains non-tensor factors or wildcard tensor factors do not commute.
   */
  override matchInternal(expr: Expr, initial: ExprMap<Expr>): ExprMap<Expr> | NoMatchResult {
    if (!wildsOf(this).length) return super.matchInternal(expr, initial);
    const args = expr instanceof TensMul ? expr.args : [expr];
    if (args.some((f) => f instanceof Tensor && f.head.comm !== 0)) throw new NotImplementedError('wild tensor products require commuting factors');
    const concrete = this.args.filter(isTens).filter((factor) => !(factor instanceof WildTensor));
    const wild = this.args.filter((a): a is WildTensor => a instanceof WildTensor);
    const coeff = mul(...args.filter((a) => !isTens(a)));
    const search = (n: number, remaining: TensExpr[], bindings: ExprMap<Expr>, sign: Expr): ExprMap<Expr> | NoMatchResult => {
      if (n < concrete.length) {
        const pattern = at(concrete, n);
        if (!(pattern instanceof Tensor)) throw new NotImplementedError('wild product matching requires tensor factors');
        for (const form of pattern.symmetrizedForms()) {
          const signed = form instanceof TensMul;
          const tensor = cast(signed ? last(form.args) : form, Tensor);
          for (const [j, factor] of remaining.entries()) {
            if (!(factor instanceof Tensor) || !factor.head.equals(tensor.head)) continue;
            const m = tensor.matchesForm(factor, bindings);
            if (isNoMatch(m)) continue;
            const result = search(n + 1, remaining.filter((_, i) => i !== j), m, signed ? neg(sign) : sign);
            if (!isNoMatch(result)) return result;
          }
        }
        return NoMatch;
      }
      let rest = remaining, matched = bindings;
      for (const w of wild) {
        const selected = rest.filter((t) => !w.rank || t.getFreeIndices().every((i) => w.indices.some((j) => !isNoMatch(j.matches(i)))));
        const m = w.matchInternal(tensMul(...selected), matched);
        if (isNoMatch(m)) return NoMatch;
        for (const [key, value] of m) {
          const previous = matched.get(key);
          if (previous && !previous.equals(value)) return NoMatch;
        }
        matched = m;
        rest = rest.filter((f) => !selected.includes(f));
      }
      if (rest.length) return NoMatch;
      const scalar = match(mul(sign, coeff), this.coEff);
      if (!scalar) return NoMatch;
      for (const [k, v] of scalar) matched.set(k, v);
      return matched;
    };
    return search(0, args.filter(isTens), new ExprMap(initial), S.One);
  }
  /**
   * Replaces tensor indices using a map keyed by their structural keys.
   *
   * @param repl - Existing replacement map.
   * @returns The transformed tensor expression.
   */
  replaceIndices(repl: IndexRepl): Expr {
    return new TensMul(this.args.map((a) => (isTens(a) ? a.replaceIndices(repl) : a)));
  }
  /**
   * Evaluates the outer tensor operation with the current operands.
   *
   * @returns The resulting expression.
   */
  doitShallow(): Expr {
    const args = this.args.filter((a) => !a.equals(1));
    const coeff = mul(...args.filter((a) => !isTens(a)));
    const tens = args.filter(isTens);
    if (!tens.length) return coeff;
    if (coeff.equals(0)) return S.Zero;
    const all = coeff.equals(1) ? tens : [coeff, ...tens];
    if (all.length === 1) return first(all);
    return new TensMul(contractIndices(all, true).args, this.isCanonBp);
  }
  /**
   * Lists the factors with the scalar coefficient on the first factor.
   *
   * @returns The tensor factors with the scalar coefficient attached to the first factor.
   * @see SymPy `sympy.tensor.tensor.TensMul.split`
   */
  split(): Expr[] {
    const out: Expr[] = [];
    let res: Expr = S.One;
    for (const arg of this.args) {
      if (arg instanceof Tensor) {
        out.push(tensMul(res, arg));
        res = S.One;
      } else res = mul(res, arg);
    }
    return out;
  }
  /**
   * Orders commuting or anticommuting tensor factors by index type and name.
   *
   * @returns The tensor expression with components in canonical order.
   * @see SymPy `sympy.tensor.tensor.TensMul.sorted_components`
   */
  sortedComponents(): Expr {
    const cv = this.args.filter(isTens);
    let sign = 1;
    const n = cv.length - 1;
    const typesOf = (t: TensExpr): TensorIndexTypeNode[] => [...new ExprMap(cast(t, Tensor).component.indexTypes.map((x): [Expr, TensorIndexTypeNode] => [x, x])).values()].sort(byLt((x, y) => x.typeName < y.typeName));
    for (let i = 0; i < n; i++) {
      for (let j = n; j > i; j--) {
        const a = cast(at(cv, j - 1), Tensor);
        const b = cast(at(cv, j), Tensor);
        const c = a.commutesWith(b);
        if (c === 'none') continue;
        const t1 = typesOf(a);
        const t2 = typesOf(b);
        const typeLt = (x: TensorIndexTypeNode, y: TensorIndexTypeNode): boolean => x.typeName < y.typeName;
        const greater = sameTypes(t1, t2) ? a.component.tensorName > b.component.tensorName : listLt(t2, t1, typeLt);
        if (greater) {
          [cv[j - 1], cv[j]] = [b, a];
          if (c === 1) sign = -sign;
        }
      }
    }
    const coeff = mul(sign, this.coEff);
    return tensMul(...(coeff.equals(1) ? cv : [coeff, ...cv]));
  }
  /**
   * Canonicalizes tensor products under index symmetries using the Butler–Portugal algorithm.
   *
   * @returns The transformed tensor expression.
   * @see SymPy `sympy.tensor.tensor.TensMul.canon_bp`
   */
  canonBp(): Expr {
    return this.isCanonBp ? this : canonicalForm(this);
  }
  /**
   * Substitutes index pairs while respecting index variance.
   *
   * @param indexTuples - Pairs of old and replacement indices.
   * @returns The transformed tensor expression.
   * @see SymPy `sympy.tensor.tensor.TensMul.substitute_indices`
   */
  substituteIndices(...indexTuples: [TensorIndexNode, TensorIndexNode][]): Expr {
    return tensMul(...this.args.map((a) => (isTens(a) ? a.substituteIndices(...indexTuples) : a)));
  }
  /**
   * Maps each tensor slot to the position of its factor in the product.
   *
   * @returns The argument positions in index-slot order.
   * @internal
   */
  indicesToArgsPos(): number[] {
    return this.args.flatMap((arg, k) => (isTens(arg) ? range(cast(arg, Tensor).extRank).map(() => k) : []));
  }
  /**
   * Rebuilds the tensor with the supplied indices in slot order.
   *
   * @param indices - Indices in slot order.
   * @param isCanonBp - Whether the input is already in canonical index order.
   * @returns The tensor expression with the supplied index slots.
   * @see SymPy `sympy.tensor.tensor.TensMul._set_indices`
   * @internal
   */
  setIndices(indices: readonly TensorIndexNode[], isCanonBp = false): Expr {
    let pos = 0;
    const args = this.args.map((arg) => {
      if (!isTens(arg)) return arg;
      const t = cast(arg, Tensor);
      const r = t.setIndices(indices.slice(pos, pos + t.extRank));
      pos += t.extRank;
      return r;
    });
    return new TensMul(args, isCanonBp).doitShallow();
  }
  /**
   * Contracts pairs of indices using the given metric tensor.
   *
   * @param g - Metric tensor head to contract.
   * @returns The transformed tensor expression.
   * @see SymPy `sympy.tensor.tensor.TensMul.contract_metric`
   */
  contractMetric(g: TensorHeadNode): Expr {
    if (this.args.some((arg) => arg instanceof TensAdd)) return contractMetric(expandTens(this), g);
    const posMap = this.indicesToArgsPos();
    const args: Expr[] = [...this.args];
    const antisym = metricAntisym(g);
    const gpos = this.args.flatMap((x, k) => (x instanceof Tensor && x.component.equals(g) ? [k] : []));
    if (!gpos.length) return this;
    let sign: Expr = S.One;
    let dum = this.dum;
    let free = this.free;
    const elim = new Set<number>();
    const argOf = (p: number): number => at(posMap, p);
    for (const gposx of gpos) {
      const free1 = free.filter((x) => argOf(x[1]) === gposx);
      const dum1 = dum.filter((x) => argOf(x[0]) === gposx || argOf(x[1]) === gposx);
      if (!dum1.length) continue;
      elim.add(gposx);
      // the metric is removed from the product
      args[gposx] = S.One;
      if (dum1.length === 2) {
        const [dum10, dum11] = [first(dum1), at(dum1, 1)];
        let p0: number;
        let p1: number;
        // bring the indices of an antisymmetric metric to contravariant form
        if (argOf(dum10[1]) === gposx) {
          p0 = dum10[0];
          if (antisym && dum10[1] === 1) sign = mul(-1, sign);
        } else {
          p0 = dum10[1];
          if (antisym && dum10[0] === 0) sign = mul(-1, sign);
        }
        if (argOf(dum11[1]) === gposx) {
          p1 = dum11[0];
          if (antisym) sign = mul(-1, sign);
        } else p1 = dum11[1];
        dum.push([p0, p1]);
      } else {
        const [dp0, dp1] = first(dum1);
        if (argOf(dp0) === argOf(dp1)) {
          // g(i, -i)
          sign = mul(sign, first(g.indexTypes).dim);
          if (antisym && dp0 < dp1) sign = mul(-1, sign);
        } else {
          // g(i0, i1)*p(-i1)
          let p1: number;
          if (argOf(dp0) === gposx) {
            p1 = dp1;
            if (antisym && dp0 === 0) sign = mul(-1, sign);
          } else p1 = dp0;
          free.push([at(free1, 0)[0], p1]);
        }
      }
      dum = dum.filter((x) => !dum1.includes(x));
      free = free.filter((x) => !free1.includes(x));
    }
    // shift positions
    let shift = 0;
    const shifts = args.map((_, i) => {
      if (elim.has(i)) {
        shift += 2;
        return 0;
      }
      return shift;
    });
    const sh = (p: number): number => p - at(shifts, argOf(p));
    const free2 = free.filter(([, p]) => !elim.has(argOf(p))).map(([ind, p]): Free => [ind, sh(p)]);
    const dum2 = dum.filter(([p0, p1]) => !elim.has(argOf(p0)) && !elim.has(argOf(p1))).map(([p0, p1]): Dum => [sh(p0), sh(p1)]);
    const res = tensMul(sign, new TensMul(args));
    if (!(res instanceof Tensor || res instanceof TensMul)) return res;
    return res.setIndices(IndexStructure.fromComponentsFreeDum(res.components, free2, dum2).getIndices());
  }
  /**
   * Builds the component array from tensor replacements and tracks its remaining indices.
   *
   * @param repl - Existing replacement map.
   * @returns The remaining indices and their component array.
   * @see SymPy `sympy.tensor.tensor.TensMul._extract_data`
   */
  extractData(repl: ExprMap<NDimArray>): [TensorIndexNode[], Expr] {
    const parts = this.args.filter(isTens).map((a) => a.extractData(repl));
    const coeff = mul(...this.args.filter((a) => !isTens(a)));
    const r = indicesToFreeDum(parts.map(([i]) => i));
    const free = [...r.free].sort((a, b) => a[1] - b[1]).map(([i]) => i);
    return [
      free,
      scaleArray(
        coeff,
        dataContractDum(
          parts.map(([, a]) => a),
          r.dummyData.map((d): Dum => [d[3], d[4]]),
        ),
      ),
    ];
  }
  /**
   * Formats the expression in plain text.
   *
   * @param print - Formatter for a child expression.
   * @returns The formatted expression.
   */
  override printStr(print: (e: Expr) => string): string {
    let args = [...this.args];
    let sign = '';
    if (couldExtractMinusSign(this.coEff)) {
      sign = '-';
      if (first(args).equals(-1)) args = args.slice(1);
      else args[0] = neg(first(args));
    }
    return sign + args.map((a) => (precedence(a) <= PREC.MUL ? `(${print(a)})` : print(a))).join('*');
  }
  /**
   * Formats the product's sign and factors side by side.
   *
   * @param print - Formatter for a child expression.
   * @returns The formatted LaTeX.
   */
  override printLatex(print: (e: Expr) => string): string {
    let args = [...this.args];
    let sign = '';
    if (couldExtractMinusSign(this.coEff)) {
      sign = '-';
      if (first(args).equals(-1)) args = args.slice(1);
      else args[0] = neg(first(args));
    }
    return sign + args.map((a) => (precedence(a) <= PREC.MUL ? `\\left(${print(a)}\\right)` : print(a))).join('');
  }
  /**
   * Uses multiplication precedence for the tensor product.
   *
   * @returns The text printer’s precedence for this node.
   */
  strPrecedence(): number {
    return PREC.MUL;
  }
}

const sameTypes = (a: readonly TensorIndexTypeNode[], b: readonly TensorIndexTypeNode[]): boolean => a.length === b.length && a.every((t, i) => t.equals(at(b, i)));

/** SymPy -expr for tensors and scalars. */
const neg = (e: Expr): Expr => (e instanceof TensMul ? new TensMul([S.NegOne, e], e.isCanonBp).doitShallow() : mul(-1, e));

/**
 * Multiplies tensor expressions and evaluates the product without recursively evaluating its
 * factors.
 *
 * @see SymPy `sympy.tensor.tensor.TensMul`
 */
export function tensMul(...args: ExprLike[]): Expr {
  return new TensMul(args).doitShallow();
}

/**
 * Multiplies the supplied tensor expressions.
 *
 * @param a - Tensor or scalar factors in multiplication order.
 * @returns The tensor product expression.
 * @see SymPy `sympy.tensor.tensor.tensor_mul`
 */
export function tensorMul(...a: ExprLike[]): Expr {
  return a.reduce<Expr>((t, x) => mul(t, x), S.One);
}

// ---------------------------------------------------------------------------
// Sums
// ---------------------------------------------------------------------------

/**
 * A sum of tensor expressions with matching free indices.
 *
 * @see SymPy `sympy.tensor.tensor.TensAdd`
 * @example
 * ```ts
 * import { TensAdd, TensorHead, TensorIndex, TensorIndexType } from '@symjs/symjs';
 *
 * const L = TensorIndexType('Lorentz', { dummyName: 'L' });
 * const a = TensorIndex('a', L);
 * const p = TensorHead('p', [L]), q = TensorHead('q', [L]);
 * new TensAdd([p.at(a), q.at(a)]); // => p(a) + q(a)
 * ```
 */
export class TensAdd extends TensExpr {
  /**
   * Constructs a `TensAdd` instance.
   *
   * @param args - Terms of the tensor sum.
   * @internal
   */
  constructor(args: readonly Expr[]) {
    super('TensAdd', args);
  }
  /**
   * Extracts the numerical or symbolic scalar factor of the tensor expression.
   *
   * @returns The scalar coefficient.
   * @see SymPy `sympy.tensor.tensor.TensAdd.coeff`
   */
  get coEff(): Expr {
    return S.One;
  }
  /**
   * Factors out the scalar multiplier of the tensor expression.
   *
   * @returns The coefficient-free tensor expression.
   * @see SymPy `sympy.tensor.tensor.TensAdd.nocoeff`
   */
  get nocoeff(): Expr {
    return this;
  }
  /**
   * Counts the indices left uncontracted.
   *
   * @returns The free rank.
   * @see SymPy `sympy.tensor.tensor.TensAdd.rank`
   */
  get rank(): number {
    const a = first(this.args);
    return isTens(a) ? a.getFreeIndices().length : 0;
  }
  /**
   * Lists the uncontracted indices in slot order.
   *
   * @returns The uncontracted indices.
   * @see SymPy `sympy.tensor.tensor.TensAdd.get_free_indices`
   */
  getFreeIndices(): TensorIndexNode[] {
    return getFreeIndicesOf(first(this.args));
  }
  /**
   * Lists the tensor indices in slot order, including contracted indices.
   *
   * @returns The ordered tensor indices.
   * @see SymPy `sympy.tensor.tensor.TensAdd.get_indices`
   */
  getIndices(): TensorIndexNode[] {
    const out: TensorIndexNode[] = [];
    for (const arg of this.args) for (const i of getIndicesOf(arg)) if (!out.some((j) => j.equals(i))) out.push(i);
    return out;
  }
  /**
   * Rebuilds the expression with replacement arguments in their original order.
   *
   * @param args - Replacement arguments in the same order as `args` on the original expression.
   * @returns The rebuilt expression.
   */
  withArgs(args: readonly Expr[]): Expr {
    return newTensAdd(args);
  }
  /**
   * Replaces tensor indices using a map keyed by their structural keys.
   *
   * @param repl - Existing replacement map.
   * @returns The transformed tensor expression.
   */
  replaceIndices(repl: IndexRepl): Expr {
    return newTensAdd(this.args.map((a) => (isTens(a) ? a.replaceIndices(repl) : a)));
  }
  /**
   * Evaluates the outer tensor operation with the current operands.
   *
   * @returns The resulting expression.
   * @throws RangeError when the summands have different free indices.
   */
  doitShallow(): Expr {
    // all terms have the same free indices
    const free0 = keySet(this.getFreeIndices());
    if (this.args.some((a) => !sameKeySet(keySet(getFreeIndicesOf(a)), free0))) throw new RangeError('all tensors must have the same indices');
    return newTensAdd(collectTerms(this.args));
  }
  /**
   * Matches a tensor pattern against an expression using the existing bindings.
   *
   * @param expr - Symbolic expression on which to operate.
   * @param repl - Existing replacement map.
   * @returns The extended bindings, or `NoMatch` if matching fails.
   */
  override matchInternal(expr: Expr, repl: ExprMap<Expr>): ExprMap<Expr> | NoMatchResult {
    return expr instanceof TensAdd ? super.matchInternal(expr, repl) : NoMatch;
  }
  /**
   * Specifies when the text printer must parenthesize the expression.
   *
   * @returns The text printer’s precedence for this node.
   */
  strPrecedence(): number {
    return PREC.ADD;
  }
  /**
   * Canonicalizes tensor products under index symmetries using the Butler–Portugal algorithm.
   *
   * @returns The transformed tensor expression.
   * @see SymPy `sympy.tensor.tensor.TensAdd.canon_bp`
   */
  canonBp(): Expr {
    return tensAdd(...cast(expandTens(this), TensAdd).args.map(canonBp));
  }
  /**
   * Contracts pairs of indices using the given metric tensor.
   *
   * @param g - Metric tensor head to contract.
   * @returns The transformed tensor expression.
   * @see SymPy `sympy.tensor.tensor.TensAdd.contract_metric`
   */
  contractMetric(g: TensorHeadNode): Expr {
    return canonBp(tensAdd(...this.args.map((x) => contractMetric(x, g))));
  }
  /**
   * Substitutes index pairs while respecting index variance.
   *
   * @param indexTuples - Pairs of old and replacement indices.
   * @returns The transformed tensor expression.
   * @see SymPy `sympy.tensor.tensor.TensAdd.substitute_indices`
   */
  substituteIndices(...indexTuples: [TensorIndexNode, TensorIndexNode][]): Expr {
    return tensAdd(...this.args.map((a) => (isTens(a) ? a.substituteIndices(...indexTuples) : a)));
  }
  /**
   * Builds the component array from tensor replacements and tracks its remaining indices.
   *
   * @param repl - Existing replacement map.
   * @returns The remaining indices and their component array.
   * @see SymPy `sympy.tensor.tensor.TensAdd._extract_data`
   */
  extractData(repl: ExprMap<NDimArray>): [TensorIndexNode[], Expr] {
    const parts = this.args.map((arg): [TensorIndexNode[], Expr] => (isTens(arg) ? arg.extractData(repl) : [[], arg]));
    const ref = at(parts, 0)[0];
    const arrays = parts.map(([indices, array]) => (indices.length ? permutedims(array, getIndicesPermutation(indices, ref)) : array));
    return [ref, arrays.reduce((s, a) => (s instanceof NDimArray ? s.add(a) : add(s, a)))];
  }
  /**
   * Formats the expression in plain text.
   *
   * @param print - Formatter for a child expression.
   * @returns The formatted expression.
   */
  override printStr(print: (e: Expr) => string): string {
    return this.args.map(print).join(' + ').replaceAll('+ -', '- ');
  }
  /**
   * Orders the terms by their LaTeX representation.
   *
   * @param print - Formatter for a child expression.
   * @returns The formatted LaTeX.
   */
  override printLatex(print: (e: Expr) => string): string {
    // the terms are tensors or products, which bind tighter than a sum
    return this.args.map(print).sort().join(' + ').replaceAll('+ -', '- ');
  }
}

/** SymPy TensAdd.__new__: flattened, sorted, without zero terms. */
function newTensAdd(argsIn: readonly ExprLike[]): Expr {
  const args = argsIn
    .map(sympify)
    .filter((x) => !x.equals(0))
    .flatMap((x) => (x instanceof Add || x instanceof TensAdd ? x.args : [x]))
    .filter((x) => !isTens(x) || !x.coEff.equals(0));
  args.sort((a, b) => compareKeys(defaultSortKey(a), defaultSortKey(b)));
  if (!args.length) return S.Zero;
  if (args.length === 1) return first(args);
  return new TensAdd(args);
}

/** SymPy _tensAdd_collect_terms: terms differing only in their coefficients collected. */
function collectTerms(args: readonly Expr[]): Expr[] {
  const terms = new Map<string, [Expr, Expr[]]>();
  let scalars: Expr = S.Zero;
  for (const arg of args) {
    if (!isTens(arg)) {
      scalars = add(scalars, arg);
      continue;
    }
    const t = arg.nocoeff;
    const entry = terms.get(t.key) ?? [t, []];
    entry[1].push(arg.coEff);
    terms.set(t.key, entry);
  }
  const out = [...terms.values()].flatMap(([t, cs]) => {
    const c = add(...cs);
    return c.equals(0) ? [] : [tensMul(c, t)];
  });
  return [...(scalars instanceof Add ? scalars.args : scalars.equals(0) ? [] : [scalars]), ...out];
}

/**
 * Adds tensor expressions and evaluates the sum without recursively evaluating its terms.
 *
 * @see SymPy `sympy.tensor.tensor.TensAdd`
 */
export function tensAdd(...args: ExprLike[]): Expr {
  const s = newTensAdd(args);
  return isTens(s) ? s.doitShallow() : s;
}

/** SymPy default_sort_key of tensor expressions (the order of the terms of a TensAdd). */
function defaultSortKey(e: Expr): Key {
  const one = sortKey(S.One);
  if (e instanceof Permutation) return [[2, 0, 'Permutation'], [1, [e.toString()]], one, 1];
  if (e instanceof BoolAtom) return [[2, 0, e.value ? 'BooleanTrue' : 'BooleanFalse'], [1, [e.value ? 'True' : 'False']], one, 1];
  if (e instanceof ExtensionExpr && (e instanceof TensExpr || e instanceof TupleNode || e instanceof TensorIndexNode || e instanceof TensorIndexTypeNode || e instanceof TensorHeadNode || e instanceof TensorSymmetry || e instanceof DictNode)) {
    return [[5, 0, e.name], [e.args.length, e.args.map(defaultSortKey)], one, 1];
  }
  return sortKey(e);
}

// ---------------------------------------------------------------------------
// Canonicalization, contraction, substitution
// ---------------------------------------------------------------------------

/** SymPy components_canon_args: (base, generators, count, commutation) of each run of equal heads. */
function componentsCanonArgs(components: readonly TensorHeadNode[]): [number[], Af[], number, 0 | 1 | null][] {
  const runs: [TensorHeadNode, number][] = [];
  for (const t of components) {
    const lastRun = runs[runs.length - 1];
    if (lastRun?.[0].equals(t)) lastRun[1]++;
    else runs.push([t, 1]);
  }
  return runs.map(([h, n]) => {
    const c = h.comm === 0 || h.comm === 1 ? h.comm : TensorManager.getComm(h.comm, h.comm);
    return [h.symmetry.base, h.symmetry.generators.map((g) => g.arrayForm), n, c === 'none' ? null : c];
  });
}

/** SymPy Tensor/TensMul.canon_bp. */
function canonicalForm(self: Tensor | TensMul): Expr {
  const expanded = expandTens(self);
  if (expanded instanceof TensAdd) return expanded.canonBp();
  if (!(expanded instanceof Tensor || expanded instanceof TensMul)) return expanded;
  const t = expectType(expanded instanceof TensMul ? expanded.sortedComponents() : expanded, (v): v is Tensor | TensMul => v instanceof Tensor || v instanceof TensMul);
  const [g, dummies, msym] = t.indexStructure.indicesCanonArgs();
  const can = canonicalize(g, dummies, msym, ...componentsCanonArgs(t.components));
  return can === 0 ? S.Zero : perm2tensor(t, can, true);
}

/**
 * Permutes the tensor indices by `g` and applies its sign.
 *
 * @param t - Tensor expression to transform.
 * @param g - Index permutation in array form, including its sign slots.
 * @param isCanonBp - Whether the input is already in canonical index order.
 * @returns The signed permuted tensor.
 * @see SymPy `sympy.tensor.tensor.perm2tensor`
 */
export function perm2tensor(t: Tensor | TensMul, g: Af, isCanonBp = false): Expr {
  const nim = t.indexStructure.perm2tensor(g);
  const res = t.setIndices(nim.getIndices(), isCanonBp);
  return last(g) !== g.length - 1 ? neg(res) : res;
}

/**
 * Canonicalizes tensor expressions while preserving other expression types.
 *
 * @param p - Tensor expression to canonicalize.
 * @returns The resulting expression.
 * @see SymPy `sympy.tensor.tensor.canon_bp`
 */
export function canonBp(p: Expr): Expr {
  return isTens(p) ? p.canonBp() : p;
}

/**
 * Contracts pairs of indices using the given metric tensor.
 *
 * @param t - Tensor expression to transform.
 * @param g - Metric tensor head to contract.
 * @returns The transformed tensor expression.
 * @see SymPy `sympy.tensor.tensor.contract_metric`
 */
export function contractMetric(t: Expr, g: TensorHeadNode): Expr {
  return isTens(t) ? t.contractMetric(g) : t;
}

/**
 * Substitutes index pairs while respecting index variance.
 *
 * @param t - Tensor expression to transform.
 * @param indexTuples - Pairs of old and replacement indices.
 * @returns The transformed tensor expression.
 * @see SymPy `sympy.tensor.tensor.substitute_indices`
 */
export function substituteIndices(t: Expr, ...indexTuples: [TensorIndexNode, TensorIndexNode][]): Expr {
  return isTens(t) ? t.substituteIndices(...indexTuples) : t;
}

/** SymPy TensMul expansion (distribution over sums), repeated until it stops changing. */
function expandTens(e: Expr): Expr {
  for (let cur = e; ; ) {
    const next = expandOnce(cur);
    if (next.equals(cur)) return next;
    cur = next;
  }
}
function expandOnce(e: Expr): Expr {
  if (e instanceof TensAdd) return newTensAdd(e.args.map(expandOnce));
  if (!(e instanceof TensMul)) return e;
  const m = new TensMul(
    e.args.map((a) => (isTens(a) ? expandOnce(a) : expandExpr(a))),
    e.isCanonBp,
  );
  const groups = m.args.map((a) => (a instanceof Add || a instanceof TensAdd ? a.args : [a]));
  let combos: Expr[][] = [[]];
  for (const g of groups) combos = combos.flatMap((c) => g.map((x) => [...c, x]));
  return newTensAdd(combos.map((c) => tensMul(...c)));
}

/**
 * Rewrites a Riemann tensor with four free indices using its cyclic identity.
 *
 * @param tR - Riemann tensor with four free indices.
 * @returns An equivalent linear combination of index permutations.
 * @see SymPy `sympy.tensor.tensor.riemann_cyclic_replace`
 */
export function riemannCyclicReplace(tR: Tensor | TensMul): Expr {
  const [m, n, p, q] = [...tR.free].sort((a, b) => a[1] - b[1]).map(([i]) => i);
  const [im, iN, ip, iq] = [defined(m), defined(n), defined(p), defined(q)];
  const t0 = mul(tR, Rational.of(2, 3));
  const t1 = mul(neg(tR.substituteIndices([im, im], [iN, iq], [ip, iN], [iq, ip])), Rational.of(1, 3));
  const t2 = mul(tR.substituteIndices([im, im], [iN, ip], [ip, iN], [iq, iq]), Rational.of(1, 3));
  return add(t0, t1, t2);
}

/**
 * Replaces Riemann tensors by their cyclic-identity form and canonicalizes the result.
 *
 * @param t2 - Tensor expression containing Riemann factors.
 * @returns The canonical tensor expression after applying the cyclic identity.
 * @see SymPy `sympy.tensor.tensor.riemann_cyclic`
 * @example
 * ```ts
 * import { TensorHead, TensorIndex, TensorIndexType, TensorSymmetry, riemannCyclic, tensorIndices } from '@symjs/symjs';
 *
 * const L = TensorIndexType('Lorentz', { dummyName: 'L' });
 * const [i, j, k, l] = tensorIndices('i,j,k,l', L) as [TensorIndex, TensorIndex, TensorIndex, TensorIndex];
 * const R = TensorHead('R', [L, L, L, L], TensorSymmetry.riemann());
 * const a = R.at(i.neg(), j.neg(), k.neg(), l.neg()), b = R.at(i.neg(), k.neg(), j.neg(), l.neg());
 * riemannCyclic(R.at(i, j, k, l).mul(a.sub(b.mul(2)))); // => 0
 * ```
 */
export function riemannCyclic(t2: Expr): Expr {
  const t = expandTens(t2);
  const args = t instanceof TensAdd ? t.args : [t];
  const a3 = args.map((x) => tensorMul(...asProduct(x).split().map((tx) => riemannCyclicReplace(asProduct(tx)))));
  const t3 = tensAdd(...a3);
  return canonBp(t3);
}
const asProduct = (x: unknown): Tensor | TensMul => expectType(x, (v): v is Tensor | TensMul => v instanceof Tensor || v instanceof TensMul, 'a product of tensors');

// ---------------------------------------------------------------------------
// Component arrays
// ---------------------------------------------------------------------------

const asArray = (a: Expr): NDimArray => (a instanceof NDimArray ? a : new ImmutableDenseNDimArray([a], []));
const scaleArray = (c: Expr, a: Expr): Expr => (a instanceof NDimArray ? a.rmul(c) : mul(c, a));
const getIndicesPermutation = (indices1: readonly TensorIndexNode[], indices2: readonly TensorIndexNode[]): number[] => indices2.map((i) => indices1.findIndex((j) => j.equals(i)));

function metricArray(repl: ExprMap<NDimArray>, type: TensorIndexTypeNode): NDimArray {
  return defined(repl.get(type), 'No metric provided to lower index');
}

/** SymPy _TensorDataLazyEvaluator.inverse_matrix. */
const inverseArray = (a: NDimArray): NDimArray => new ImmutableDenseNDimArray(a.tomatrix().inv());

/** SymPy _contract_and_permute_with_metric. */
function contractAndPermuteWithMetric(metric: NDimArray, array: Expr, pos: number, dim: number): Expr {
  const contracted = tensorcontraction(tensorproduct(metric, asArray(array)), [1, 2 + pos]);
  const permu = range(dim);
  [permu[0], permu[pos]] = [pos, 0];
  return permutedims(contracted, permu);
}

/** SymPy data_contract_dum: the tensor product of the arrays contracted over the dummy pairs. */
function dataContractDum(arrays: readonly Expr[], dum: readonly Dum[]): Expr {
  const prod = tensorproduct(...arrays.map(asArray));
  return dum.length ? tensorcontraction(prod, ...dum) : prod;
}

/** SymPy _match_indices_with_other_tensor: the array with the variances and axis order of free_ind1. */
function matchIndicesWithOtherTensor(arrayIn: Expr, freeInd1: readonly TensorIndexNode[], freeInd2In: readonly TensorIndexNode[], repl: ExprMap<NDimArray>): [TensorIndexNode[], Expr] {
  let array = arrayIn;
  const freeInd2 = [...freeInd2In];
  const remaining: (TensorIndexNode | undefined)[] = [...freeInd2In];
  const pos2up: number[] = [];
  const pos2down: number[] = [];
  const posOf = (x: TensorIndexNode): number => remaining.findIndex((r) => r?.equals(x));
  freeInd1.forEach((index1, pos1) => {
    let pos2 = posOf(index1);
    if (pos2 >= 0) {
      remaining[pos2] = undefined;
      return;
    }
    pos2 = posOf(index1.neg());
    if (pos2 >= 0) {
      remaining[pos2] = undefined;
      freeInd2[pos2] = index1;
      (index1.isUp ? pos2up : pos2down).push(pos2);
      return;
    }
    const index2 = remaining[pos1];
    if (index2 === undefined) throw new RangeError(`incompatible indices: ${freeInd1.join(', ')} and ${freeInd2In.join(', ')}`);
    remaining[pos1] = undefined;
    freeInd2[pos1] = index1;
    if (index1.isUp !== index2.isUp) (index1.isUp ? pos2up : pos2down).push(pos1);
  });
  const set2 = keySet(freeInd2);
  if (keySet(freeInd1.filter((i) => set2.has(i.key))).size < freeInd1.length) throw new RangeError(`incompatible indices: ${freeInd1.join(', ')} and ${freeInd2In.join(', ')}`);
  for (const pos of pos2up) array = contractAndPermuteWithMetric(inverseArray(metricArray(repl, at(freeInd1, pos).tensorIndexType)), array, pos, freeInd1.length);
  for (const pos of pos2down) array = contractAndPermuteWithMetric(metricArray(repl, at(freeInd1, pos).tensorIndexType), array, pos, freeInd1.length);
  if (freeInd1.length) array = permutedims(array, getIndicesPermutation(freeInd2, freeInd1));
  if (array instanceof NDimArray && array.rank() === 0) array = array.get([]);
  return [freeInd2, array];
}

// ---------------------------------------------------------------------------
// TensorElement
// ---------------------------------------------------------------------------

/**
 * A tensor with specified index values fixed and its remaining indices free.
 *
 * @see SymPy `sympy.tensor.tensor.TensorElement`
 */
export class TensorElementNode extends TensExpr {
  /**
   * Constructs a `TensorElement` instance.
   *
   * @param expr - Symbolic expression on which to operate.
   * @param indexMap - Component values keyed by the indices to fix.
   * @param freeIndices - The indices whose values remain free.
   * @internal
   */
  constructor(
    expr: Tensor,
    indexMap: DictNode,
    /** The indices whose values remain free. */
    readonly freeIndices: readonly TensorIndexNode[],
  ) {
    super('TensorElement', [expr, indexMap]);
  }
  /**
   * Identifies the operand of this tensor operation.
   *
   * @returns The underlying expression.
   * @see SymPy `sympy.tensor.tensor.TensorElement.expr`
   */
  get expr(): Tensor {
    return cast(first(this.args), Tensor);
  }
  /**
   * Locates each uncontracted index in the expression's slots.
   *
   * @returns The free index–position pairs.
   * @see SymPy `sympy.tensor.tensor.TensorElement.free`
   */
  get free(): Free[] {
    return IndexStructure.fromIndices(this.freeIndices).free;
  }
  /**
   * Identifies the slots linked by each dummy contraction.
   *
   * @returns The contracted slot pairs.
   * @see SymPy `sympy.tensor.tensor.TensorElement.dum`
   */
  get dum(): Dum[] {
    return IndexStructure.fromIndices(this.freeIndices).dum;
  }
  /**
   * Associates fixed indices with their supplied component values.
   *
   * @returns The fixed component values keyed by index.
   * @see SymPy `sympy.tensor.tensor.TensorElement.index_map`
   */
  get indexMap(): DictNode {
    return cast(at(this.args, 1), DictNode);
  }
  /**
   * Extracts the numerical or symbolic scalar factor of the tensor expression.
   *
   * @returns The scalar coefficient.
   * @see SymPy `sympy.tensor.tensor.TensorElement.coeff`
   */
  get coEff(): Expr {
    return S.One;
  }
  /**
   * Factors out the scalar multiplier of the tensor expression.
   *
   * @returns The coefficient-free tensor expression.
   * @see SymPy `sympy.tensor.tensor.TensorElement.nocoeff`
   */
  get nocoeff(): Expr {
    return this;
  }
  /**
   * Lists the uncontracted indices in slot order.
   *
   * @returns The uncontracted indices.
   * @see SymPy `sympy.tensor.tensor.TensorElement.get_free_indices`
   */
  getFreeIndices(): TensorIndexNode[] {
    return [...this.freeIndices];
  }
  /**
   * Lists the tensor indices in slot order, including contracted indices.
   *
   * @returns The ordered tensor indices.
   * @see SymPy `sympy.tensor.tensor.TensorElement.get_indices`
   */
  getIndices(): TensorIndexNode[] {
    return this.getFreeIndices();
  }
  /**
   * Rebuilds the expression with replacement arguments in their original order.
   *
   * @param args - Replacement arguments in the same order as `args` on the original expression.
   * @returns The rebuilt expression.
   */
  withArgs(args: readonly Expr[]): Expr {
    return makeTensorElement(at(args, 0), cast(at(args, 1), DictNode).items());
  }
  /**
   * Replaces tensor indices using a map keyed by their structural keys.
   *
   * @param repl - Existing replacement map.
   * @returns The transformed tensor expression.
   */
  replaceIndices(repl: IndexRepl): Expr {
    return makeTensorElement(
      this.expr.replaceIndices(repl),
      this.indexMap.items().map(([k, v]): [Expr, Expr] => [repl.get(k.key) ?? k, v]),
    );
  }
  /**
   * Evaluates the outer tensor operation with the current operands.
   *
   * @returns The resulting expression.
   */
  doitShallow(): Expr {
    return this;
  }
  /**
   * Canonicalizes tensor products under index symmetries using the Butler–Portugal algorithm.
   *
   * @returns The transformed tensor expression.
   */
  canonBp(): Expr {
    return this;
  }
  /**
   * Contracts pairs of indices using the given metric tensor.
   *
   * @returns The transformed tensor expression.
   */
  contractMetric(): Expr {
    return this;
  }
  /**
   * Substitutes index pairs while respecting index variance.
   *
   * @returns The transformed tensor expression.
   */
  substituteIndices(): Expr {
    return this;
  }
  /**
   * Formats the tensor indices together with their fixed values.
   *
   * @param print - Formatter for a child expression.
   * @returns The formatted LaTeX.
   */
  override printLatex(print: (e: Expr) => string): string {
    return tensorIndicesLatex(first(this.expr.component.args), this.expr.getIndices(), new ExprMap(this.indexMap.items()), print);
  }
  /**
   * Builds the component array from tensor replacements and tracks its remaining indices.
   *
   * @param repl - Existing replacement map.
   * @returns The remaining indices and their component array.
   * @see SymPy `sympy.tensor.tensor.TensorElement._extract_data`
   */
  extractData(repl: ExprMap<NDimArray>): [TensorIndexNode[], Expr] {
    const [retIndices, array] = this.expr.extractData(repl);
    const map = new ExprMap(this.indexMap.items());
    const item = retIndices.map((i) => {
      const v = map.get(i);
      return v === undefined ? new Slice() : Number(asRational(v).p);
    });
    return [retIndices.filter((i) => !map.has(i)), cast(array, NDimArray).get(item)];
  }
}

function makeTensorElement(expr: Expr, items: readonly (readonly [Expr, Expr])[]): Expr {
  if (!(expr instanceof Tensor)) {
    if (!isTens(expr)) throw new TypeError(`${expr.toString()} is not a tensor expression`);
    return expr.withArgs(expr.args.map((a) => makeTensorElement(a, items)));
  }
  const free = expr.getFreeIndices();
  const byName = new ExprMap(free.map((i): [Expr, TensorIndexNode] => [first(i.args), i]));
  const freeKeys = keySet(free);
  const kept = items.map(([k, v]): [Expr, Expr] => [byName.get(k) ?? k, v]).filter(([k]) => freeKeys.has(k.key));
  if (!kept.length) return expr;
  const mapped = keySet(kept.map(([k]) => k));
  return new TensorElementNode(
    expr,
    new DictNode(kept.map(([k, v]) => Tuple(k, v))),
    free.filter((i) => !mapped.has(i.key)),
  );
}

/**
 * Fixes selected free indices of the tensor to specified values.
 *
 * @param expr - Symbolic expression on which to operate.
 * @param indexMap - Component values keyed by the indices to fix.
 * @returns The partially indexed tensor or the original expression when no indices are fixed.
 * @see SymPy `sympy.tensor.tensor.TensorElement`
 * @example
 * ```ts
 * import { TensorElement, TensorHead, TensorIndex, TensorIndexType, TensorSymmetry } from '@symjs/symjs';
 *
 * const L = TensorIndexType('Lorentz', { dummyName: 'L' });
 * const i = TensorIndex('i', L), j = TensorIndex('j', L);
 * const A = TensorHead('A', [L, L], TensorSymmetry.fullySymmetric(2));
 * TensorElement(A.at(i, j), new Map([[i, 2]])); // => TensorElement(A(i, j), {i: 2})
 * ```
 */
export const TensorElement = /* @__PURE__ */ callableClass(TensorElementNode, (expr: Expr, indexMap: ReadonlyMap<Expr, ExprLike>): Expr => makeTensorElement(expr, [...indexMap].map(([k, v]): [Expr, Expr] => [k, sympify(v)])));
export type TensorElement = TensorElementNode;

// ---------------------------------------------------------------------------
// Wild tensors
// ---------------------------------------------------------------------------

/**
 * A tensor head for patterns with wildcard tensor factors.
 *
 * @see SymPy `sympy.tensor.tensor.WildTensorHead`
 */
export class WildTensorHeadNode extends TensorHeadNode {
  /**
   * A tensor head matching any tensor (its index types follow the indices it is called with).
   *
   * @param name - Symbolic name.
   * @param indexTypes - Index type for each tensor slot.
   * @param symmetry - Permutation symmetries of the tensor slots.
   * @param comm - Tensor commutation group.
   * @param unorderedIndices - Allow the wildcard to match indices in a different order.
   * @throws NotImplementedError when the wildcard specifies nontrivial slot symmetries.
   */
  constructor(name: string, indexTypes: readonly TensorIndexTypeNode[] = [], symmetry?: TensorSymmetry, comm: CommGroup = 0, unorderedIndices = false) {
    const sym = symmetry ?? TensorSymmetry.noSymmetry(indexTypes.length);
    if (!sym.equals(TensorSymmetry.noSymmetry(indexTypes.length))) throw new NotImplementedError('Wild matching based on symmetry is not implemented.');
    super(name, indexTypes, sym, comm, 'WildTensorHead', [unorderedIndices ? S.true : S.false]);
  }
  /**
   * Indicates whether a wildcard can match permuted index slots.
   *
   * @returns The unordered-index flag.
   * @see SymPy `sympy.tensor.tensor.WildTensorHead.unordered_indices`
   */
  get unorderedIndices(): boolean {
    return at(this.args, 4) === S.true;
  }
  /**
   * Applies the tensor head to indices in slot order.
   *
   * @param indices - Indices in slot order.
   * @returns The tensor with the given indices.
   * @see SymPy `sympy.tensor.tensor.WildTensorHead.__call__`
   */
  override at(...indices: (TensorIndexNode | string | Expr)[]): WildTensor {
    return cast(new WildTensor(this, indices.map((i) => cast(i, TensorIndexNode))).doitShallow(), WildTensor);
  }
  /**
   * Rebuilds the expression with replacement arguments in their original order.
   *
   * @param args - Replacement arguments in the same order as `args` on the original expression.
   * @returns The rebuilt expression.
   */
  override withArgs(args: readonly Expr[]): Expr {
    return new WildTensorHeadNode(
      cast(first(args), Sym).name,
      at(args, 1).args.map((t) => cast(t, TensorIndexTypeNode)),
      cast(at(args, 2), TensorSymmetry),
      at(args, 3),
      at(args, 4) === S.true,
    );
  }
}
/**
 * Constructs a tensor head for patterns with wildcard tensor factors.
 *
 * @param name - Symbolic name.
 * @param options - `indexTypes` specifies the slots, `symmetry` their symmetry, `comm` the commutation group, and `unorderedIndices` permits reordered matches.
 * @returns The resulting `WildTensorHead` expression.
 * @throws NotImplementedError when the wildcard specifies nontrivial slot symmetries.
 * @see SymPy `sympy.tensor.tensor.WildTensorHead`
 * @example
 * ```ts
 * import { TensorIndex, TensorIndexType, WildTensor, WildTensorHead } from '@symjs/symjs';
 *
 * const L = TensorIndexType('Lorentz', { dummyName: 'L' });
 * const p = TensorIndex('p', L);
 * WildTensorHead('W').at(p) instanceof WildTensor; // => True
 * ```
 */
export const WildTensorHead = /* @__PURE__ */ callableClass(
  WildTensorHeadNode,
  (name: string, options: { indexTypes?: readonly TensorIndexTypeNode[]; symmetry?: TensorSymmetry; comm?: CommGroup; unorderedIndices?: boolean } = {}): WildTensorHeadNode =>
    new WildTensorHeadNode(name, options.indexTypes, options.symmetry, options.comm, options.unorderedIndices),
);
export type WildTensorHead = WildTensorHeadNode;

/**
 * A wild tensor W(p, q), or W() matching any tensor expression.
 *
 * @see SymPy `sympy.tensor.tensor.WildTensor`
 * @example
 * ```ts
 * import { TensorHead, TensorIndex, TensorIndexType, WildTensor, WildTensorHead, isNoMatch } from '@symjs/symjs';
 *
 * const L = TensorIndexType('Lorentz', { dummyName: 'L' });
 * const p = TensorIndex('p', L);
 * const pattern = new WildTensor(WildTensorHead('W'), [p]);
 * isNoMatch(pattern.matches(TensorHead('K', [L]).at(p))); // => False
 * ```
 */
export class WildTensor extends Tensor {
  /**
   * Constructs an instance of `WildTensor`.
   *
   * @param head - Tensor head defining the slots of this tensor.
   * @param indices - Indices in slot order.
   */
  constructor(head: WildTensorHeadNode, indices: readonly TensorIndexNode[]) {
    super(
      new WildTensorHeadNode(
        head.tensorName,
        indices.map((i) => i.tensorIndexType),
        undefined,
        at(head.args, 3),
        head.unorderedIndices,
      ),
      indices,
    );
  }
  /**
   * Identifies the tensor head applied in this factor.
   *
   * @returns The tensor head.
   * @see SymPy `sympy.tensor.tensor.WildTensor.head`
   */
  override get head(): WildTensorHeadNode {
    return cast(first(this.args), WildTensorHeadNode);
  }
  /**
   * Rebuilds the expression with replacement arguments in their original order.
   *
   * @param args - Replacement arguments in the same order as `args` on the original expression.
   * @returns The rebuilt expression.
   */
  override withArgs(args: readonly Expr[]): Expr {
    return new WildTensor(
      cast(first(args), WildTensorHeadNode),
      at(args, 1).args.map((i) => cast(i, TensorIndexNode)),
    );
  }
  /**
   * Applies a matched wildcard tensor expression to this tensor's indices.
   *
   * @param old - Expression to replace.
   * @param nw - Expression to substitute in its place.
   * @returns The specialized result when the hook handles the operands.
   * @see SymPy `sympy.tensor.tensor.WildTensor._eval_subs`
   */
  override subsSelf(old: Expr, nw: Expr): Expr | undefined {
    if (nw instanceof WildTensExpr && old.key === this.head.key) return nw.call(...this.indices);
    return undefined;
  }
  /**
   * Replaces tensor indices using a map keyed by their structural keys.
   *
   * @param repl - Existing replacement map.
   * @returns The transformed tensor expression.
   */
  override replaceIndices(repl: IndexRepl): Expr {
    return new WildTensor(
      this.head,
      this.indices.map((i) => repl.get(i.key) ?? i),
    );
  }
  /**
   * Matches a tensor pattern against an expression using the existing bindings.
   *
   * @param expr - Symbolic expression on which to operate.
   * @param replIn - Existing replacement map.
   * @returns The extended bindings, or `NoMatch` if matching fails.
   */
  override matchInternal(expr: Expr, replIn: ExprMap<Expr>): ExprMap<Expr> | NoMatchResult {
    if (!isTens(expr) && !expr.equals(1)) return NoMatch;
    const repl = new ExprMap(replIn);
    const indices = this.indices;
    if (!indices.length) {
      // without indices a wild tensor matches tensors with any number of indices
      repl.set(this, expr);
      return repl;
    }
    if (!isTens(expr)) return NoMatch;
    const exprIndices = expr.getFreeIndices();
    if (exprIndices.length !== indices.length) return NoMatch;
    if (this.head.unorderedIndices) {
      const m = this.matchIndicesIgnoringOrder(expr);
      if (!(m instanceof ExprMap)) return NoMatch;
      for (const [a, b] of m) repl.set(a, b);
    } else {
      for (const [k, ind] of indices.entries()) {
        const m = ind.matches(at(exprIndices, k));
        if (!(m instanceof ExprMap)) return NoMatch;
        for (const [a, b] of m) repl.set(a, b);
      }
    }
    repl.set(this.component, new WildTensExpr(expr));
    return repl;
  }
  /**
   * Matches wildcard indices under permutations of the candidate slots.
   *
   * @param expr - Symbolic expression on which to operate.
   * @returns The match or computed value, or `NoMatch` when no match exists.
   * @see SymPy `sympy.tensor.tensor.WildTensor._match_indices_ignoring_order`
   */
  matchIndicesIgnoringOrder(expr: TensExpr): ExprMap<Expr> | NoMatchResult {
    const repl = new ExprMap<Expr>();
    const kind = (ind: TensorIndexNode): number => (ind instanceof WildTensorIndexNode ? (ind.ignoreUpdown ? 2 : 1) : 0);
    const matched: TensorIndexNode[] = [];
    const isMatched = (e: TensorIndexNode): boolean => matched.some((m) => m.equals(e));
    for (const k of [0, 1, 2]) {
      for (const ind of this.indices.filter((i) => kind(i) === k)) {
        const hit = expr
          .getIndices()
          .filter((e) => !isMatched(e))
          .map((e): [TensorIndexNode, ExprMap<Expr> | NoMatchResult] => [e, ind.matches(e)])
          .find(([, m]) => m instanceof ExprMap);
        if (!hit) return NoMatch;
        const m = cast(hit[1], ExprMap<Expr>);
        const prev = repl.get(ind.neg());
        if (k > 0 && prev !== undefined && !cast(prev, TensorIndexNode).neg().equals(defined(m.get(ind)))) return NoMatch;
        for (const [a, b] of m) repl.set(a, b);
        matched.push(hit[0]);
      }
    }
    return repl;
  }
}

/**
 * A pattern index that binds a tensor index of the same type.
 *
 * @see SymPy `sympy.tensor.tensor.WildTensorIndex`
 */
export class WildTensorIndexNode extends TensorIndexNode {
  /**
   * An index matching any index of its type (and variance, unless ignoreUpdown).
   *
   * @param name - Symbolic name.
   * @param tensorIndexType - Index type specifying the dimension and metric.
   * @param isUp - Use contravariant variance when true and covariant variance when false.
   * @param ignoreUpdown - Allow matches of either index variance.
   */
  constructor(name: string | true, tensorIndexType: TensorIndexTypeNode, isUp = true, ignoreUpdown = false) {
    super(name, tensorIndexType, isUp, 'WildTensorIndex', [ignoreUpdown ? S.true : S.false]);
  }
  /**
   * Indicates whether the wildcard disregards raised and lowered index positions.
   *
   * @returns The variance-matching flag.
   * @see SymPy `sympy.tensor.tensor.WildTensorIndex.ignore_updown`
   */
  get ignoreUpdown(): boolean {
    return at(this.args, 3) === S.true;
  }
  /**
   * Creates an index with the new label and the original type and variance.
   *
   * @param name - New index label.
   * @param isUp - Use contravariant variance when true and covariant variance when false.
   * @returns The renamed index.
   */
  override withName(name: string, isUp = this.isUp): WildTensorIndexNode {
    return new WildTensorIndexNode(name, this.tensorIndexType, isUp, this.ignoreUpdown);
  }
  /**
   * Reverses variance while preserving the wildcard matching options.
   *
   * @returns The index with opposite variance.
   * @see SymPy `sympy.tensor.tensor.WildTensorIndex.__neg__`
   */
  override neg(): WildTensorIndexNode {
    return this.withName(this.indexName, !this.isUp);
  }
  /**
   * Rebuilds the expression with replacement arguments in their original order.
   *
   * @param args - Replacement arguments in the same order as `args` on the original expression.
   * @returns The rebuilt expression.
   */
  override withArgs(args: readonly Expr[]): Expr {
    return new WildTensorIndexNode(cast(first(args), Sym).name, cast(at(args, 1), TensorIndexTypeNode), at(args, 2) === S.true, at(args, 3) === S.true);
  }
  /**
   * Matches a tensor index of the same type, taking the pattern’s variance rule into account.
   *
   * @param expr - Symbolic expression on which to operate.
   * @returns Bindings for the wildcard matches, or `NoMatch` if the pattern fails.
   * @see SymPy `sympy.tensor.tensor.WildTensorIndex.matches`
   */
  override matches(expr: Expr): ExprMap<Expr> | NoMatchResult {
    if (!(expr instanceof TensorIndexNode) || !this.tensorIndexType.equals(expr.tensorIndexType)) return NoMatch;
    if (!this.ignoreUpdown && this.isUp !== expr.isUp) return NoMatch;
    return new ExprMap([[this, expr]]);
  }
}
/**
 * Constructs a pattern index that matches an index of the same type.
 *
 * @param name - Symbolic name.
 * @param type - Type of the tensor indices.
 * @param isUp - Use contravariant variance when true and covariant variance when false.
 * @param ignoreUpdown - Allow matches of either index variance.
 * @returns The resulting `WildTensorIndex` expression.
 * @see SymPy `sympy.tensor.tensor.WildTensorIndex`
 * @example
 * ```ts
 * import { TensorIndex, TensorIndexType, WildTensorIndex, isNoMatch } from '@symjs/symjs';
 *
 * const L = TensorIndexType('Lorentz', { dummyName: 'L' });
 * const q = WildTensorIndex('q', L), p = TensorIndex('p', L);
 * isNoMatch(q.matches(p)); // => False
 * ```
 */
export const WildTensorIndex = /* @__PURE__ */ callableClass(
  WildTensorIndexNode,
  (name: string | true, type: TensorIndexTypeNode, isUp = true, ignoreUpdown = false): WildTensorIndexNode => new WildTensorIndexNode(name, type, isUp, ignoreUpdown),
);
export type WildTensorIndex = WildTensorIndexNode;

/**
 * The expression a wild tensor head matched, called with new indices.
 *
 * @see SymPy `sympy.tensor.tensor._WildTensExpr`
 * @example
 * ```ts
 * import { TensorHead, TensorIndex, TensorIndexType, WildTensExpr } from '@symjs/symjs';
 *
 * const L = TensorIndexType('L'), p = TensorIndex('p', L), q = TensorIndex('q', L);
 * const K = TensorHead('K', [L]);
 * new WildTensExpr(K.at(p)).call(q); // => K(q)
 * ```
 */
export class WildTensExpr extends ExtensionExpr {
  /**
   * Constructs an instance of `WildTensExpr`.
   *
   * @param expr - Symbolic expression on which to operate.
   */
  constructor(
    /** The underlying expression on which this operation acts. */
    readonly expr: TensExpr) {
    super('_WildTensExpr', [expr]);
  }
  /**
   * Replaces the free indices of the matched expression with the supplied indices.
   *
   * @param indices - Indices in slot order.
   * @returns The relabeled expression.
   * @see SymPy `sympy.tensor.tensor._WildTensExpr.__call__`
   */
  call(...indices: TensorIndexNode[]): Expr {
    const free = this.expr.getFreeIndices();
    return this.expr.replaceIndices(new Map(free.map((f, k): [string, TensorIndexNode] => [f.key, at(indices, k)])));
  }
  /**
   * Rebuilds the expression with replacement arguments in their original order.
   *
   * @param args - Replacement arguments in the same order as `args` on the original expression.
   * @returns The rebuilt expression.
   */
  withArgs(args: readonly Expr[]): Expr {
    return new WildTensExpr(cast(first(args), TensExpr));
  }
}

// ---------------------------------------------------------------------------
// Arithmetic
// ---------------------------------------------------------------------------

registerArithmetic((op, args) => {
  if (!args.some(isTens)) return undefined;
  switch (op) {
    case 'mul':
      return tensMul(...args);
    case 'add':
      return tensAdd(...args);
    case 'sub':
      return tensAdd(first(args), neg(at(args, 1)));
    case 'pow':
      throw new RangeError(isTens(first(args)) ? 'No power on abstract tensors (and no division by a tensor)' : 'a tensor cannot be an exponent');
  }
});
