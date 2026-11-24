// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/** Differential geometry on coordinate patches (SymPy 1.14 diffgeom.py). */
import { splitSuperSub } from '../printing/conventions';
import { Add, Mul, Pow, Expr, ExtensionExpr, Sym, Dummy, S } from '../core/nodes';
import type { ExprLike } from '../core/nodes';
import { Matrix } from '../matrices/matrix';
import { ImmutableDenseNDimArray, NDimArray } from '../tensor/ndimarray';
import { LambdaNode as Lambda } from '../core/lambda';
import { Tuple } from '../core/containers';
import { NotImplementedError } from '../core/errors';
import { add, mul, sub, sympify } from '../core/ops';
import { diff } from '../calculus/diff';
import { xreplace } from '../core/traverse';
import { simplify } from '../simplify/simplify';
import { expand } from '../simplify/expand';
import { solve } from '../solvers/solve';
import { factorial } from '../functions/special/special';
import { SymFunction } from '../core/undef';
import { coeff, rcall } from '../core/methods';

function at<T>(xs: readonly T[], i: number): T {
  const v = xs[i];
  if (v === undefined) throw new RangeError(`Index ${i} out of range`);
  return v;
}
function instance<T>(value: unknown, cls: abstract new (...args: never[]) => T): T {
  if (!(value instanceof cls)) throw new TypeError(`Expected ${cls.name}`);
  return value;
}
function indexValue(value: Expr): number {
  const n = Number(String(value));
  if (!Number.isSafeInteger(n)) throw new RangeError('Expected an integer index');
  return n;
}
function column(values: readonly ExprLike[]): Matrix {
  return Matrix.of(values.map((v) => [v]));
}
function coordinates(values: readonly ExprLike[] | Matrix): Expr[] {
  return values instanceof Matrix ? [...values.data] : values.map(sympify);
}
function replacements(from: readonly Expr[], to: readonly Expr[]): [Expr, Expr][] {
  if (from.length !== to.length) throw new RangeError('Coordinate dimensions do not agree');
  return from.map((v, i) => [v, at(to, i)]);
}
function atoms<T extends Expr>(e: Expr, cls: abstract new (...args: never[]) => T): T[] {
  const out = new Map<string, T>();
  function visit(v: Expr): void {
    if (v instanceof cls) out.set(v.key, v);
    else if (!(v instanceof CoordSystem)) v.args.forEach(visit);
  }
  visit(e);
  return [...out.values()];
}
function systems(e: Expr): CoordSystem[] {
  return [
    ...new Map(
      [...atoms(e, BaseScalarField), ...atoms(e, BaseVectorField)].map((v) => [v.coordSys.key, v.coordSys]),
    ).values(),
  ];
}
function singleSystem(e: Expr): CoordSystem {
  const cs = systems(e);
  if (cs.length !== 1) throw new RangeError('The field must concern exactly one coordinate system');
  return at(cs, 0);
}

/**
 * A named manifold of a specified dimension.
 *
 * @see SymPy `sympy.diffgeom.diffgeom.Manifold`
 * @example
 * ```ts
 * import { Manifold } from '@symjs/symjs/diffgeom';
 *
 * const m = new Manifold('M', 2);
 * m.dim; // => 2
 * ```
 */
export class Manifold extends ExtensionExpr {
  /** The patches registered on the manifold. */
  readonly patches: Patch[] = [];
  /**
   * Constructs an instance of `Manifold`.
   *
   * @param name - Symbolic name.
   * @param dim - Dimension of the space.
   * @throws RangeError when the manifold dimension is invalid.
   */
  constructor(
    name: string,
    /**
     * Dimension of the manifold.
     *
     * @see SymPy `sympy.diffgeom.diffgeom.Manifold.dim`
     */
    readonly dim: number,
  ) {
    super(name, [sympify(dim)]);
    if (!Number.isSafeInteger(dim) || dim < 0) throw new RangeError('Invalid manifold dimension');
  }
  protected override computeKey(): string {
    return `Manifold:${this.name}:${this.dim}`;
  }
  /**
   * Rebuilds the expression with replacement arguments in their original order.
   *
   * @param args - Replacement arguments in the same order as `args` on the original expression.
   * @returns The rebuilt expression.
   */
  withArgs(args: readonly Expr[]): Expr {
    return new Manifold(this.name, indexValue(at(args, 0)));
  }
  /**
   * Formats the expression in plain text.
   *
   * @returns The formatted expression.
   */
  override printStr(): string {
    return this.name;
  }
  /**
   * Formats the expression as LaTeX.
   *
   * @returns The formatted LaTeX.
   */
  override printLatex(): string {
    const [name, supers, subs] = splitSuperSub(this.name);
    return `\\text{${name}}` + (supers.length ? `^{${supers.join(' ')}}` : '') + (subs.length ? `_{${subs.join(' ')}}` : '');
  }
}

/**
 * A coordinate neighborhood on a manifold.
 *
 * @see SymPy `sympy.diffgeom.diffgeom.Patch`
 * @example
 * ```ts
 * import { Manifold, Patch } from '@symjs/symjs/diffgeom';
 *
 * const p = new Patch('P', new Manifold('M', 2));
 * p.dim; // => 2
 * ```
 */
export class Patch extends ExtensionExpr {
  /** The coordinate systems registered on the patch. */
  readonly coordSystems: CoordSystem[] = [];
  /**
   * Constructs an instance of `Patch`.
   *
   * @param name - Symbolic name.
   * @param manifold - The manifold containing the patch.
   */
  constructor(
    name: string,
    /**
     * The manifold containing the patch.
     *
     * @see SymPy `sympy.diffgeom.diffgeom.Patch.manifold`
     */
    readonly manifold: Manifold,
  ) {
    super(name, [manifold]);
    manifold.patches.push(this);
  }
  /**
   * Counts the independent coordinates on the manifold.
   *
   * @returns The manifold dimension.
   * @see SymPy `sympy.diffgeom.diffgeom.Patch.dim`
   */
  get dim(): number {
    return this.manifold.dim;
  }
  protected override computeKey(): string {
    return `Patch:${this.name}:${this.manifold.key}`;
  }
  /**
   * Rebuilds the expression with replacement arguments in their original order.
   *
   * @param args - Replacement arguments in the same order as `args` on the original expression.
   * @returns The rebuilt expression.
   */
  withArgs(args: readonly Expr[]): Expr {
    return new Patch(this.name, instance(at(args, 0), Manifold));
  }
  /**
   * Formats the expression in plain text.
   *
   * @returns The formatted expression.
   */
  override printStr(): string {
    return this.name;
  }
  /**
   * Formats the expression as LaTeX.
   *
   * @param print - Formatter for a child expression.
   * @returns The formatted LaTeX.
   */
  override printLatex(print: (e: Expr) => string): string {
    return `\\text{${print(new Sym(this.name))}}_{${print(this.manifold)}}`;
  }
}

/** A transformation given by source symbols and target coordinate expressions, or by a lambda. */
export type CoordinateRelation = readonly [readonly Sym[], readonly ExprLike[]] | Lambda;
/** Transformations indexed by pairs of source and target chart names. */
export type CoordinateRelations = ReadonlyMap<readonly [string, string], CoordinateRelation>;

/** A coordinate transformation with a Matrix-valued body. */
class Transformation {
  constructor(
    readonly signature: readonly Sym[],
    readonly expr: Matrix,
  ) {}
  call(...values: ExprLike[]): Matrix {
    const pairs = replacements(this.signature, values.map(sympify));
    return this.expr.map((e) => xreplace(e, pairs));
  }
  toString(): string {
    const signature = this.signature.length === 1 ? String(at(this.signature, 0)) : `(${this.signature.join(', ')})`;
    return `Lambda(${signature}, ${String(this.expr)})`;
  }
}

/**
 * A coordinate chart with named coordinates and transformations to other charts on its patch.
 *
 * @see SymPy `sympy.diffgeom.diffgeom.CoordSystem`
 * @remarks SymPy prints the coordinate symbols as `(x, y)`.
 * @example
 * ```ts
 * import { CoordSystem, Manifold, Patch } from '@symjs/symjs/diffgeom';
 *
 * const p = new Patch('P', new Manifold('M', 2));
 * const chart = new CoordSystem('Car2D', p, ['x', 'y']);
 * chart.symbols; // => [x, y]
 * ```
 */
export class CoordSystem extends ExtensionExpr {
  /** The symbols used to name the coordinates. */
  readonly coordinateNames: readonly Sym[];
  /**
   * The coordinate transformations keyed by source and target chart names.
   *
   * @see SymPy `sympy.diffgeom.diffgeom.CoordSystem.relations`
   */
  readonly relations: Map<readonly [string, string], readonly [readonly Sym[], readonly Expr[]]>;
  /**
   * Explicitly registered transformations to other coordinate systems.
   *
   * @see SymPy `sympy.diffgeom.diffgeom.CoordSystem.transforms`
   */
  readonly transforms = new Map<CoordSystem, readonly [readonly Sym[], readonly Expr[]]>();
  /**
   * Constructs an instance of `CoordSystem`.
   *
   * @param name - Symbolic name.
   * @param patch - The coordinate patch containing this object.
   * @param symbols - Coordinate names or symbols in axis order.
   * @param relations - Coordinate changes keyed by the names of the source and target charts.
   */
  constructor(
    name: string,
    /**
     * The coordinate patch containing this object.
     *
     * @see SymPy `sympy.diffgeom.diffgeom.CoordSystem.patch`
     */
    readonly patch: Patch,
    symbols?: readonly (Sym | string)[],
    relations: CoordinateRelations = new Map(),
  ) {
    const names =
      symbols?.map((s) => (typeof s === 'string' ? new Sym(s, { real: true }) : new Sym(s.name, s.assumptions))) ??
      Array.from({ length: patch.dim }, (_, i) => new Sym(`${name}_${i}`, { real: true }));
    const rel = new Map<readonly [string, string], readonly [readonly Sym[], readonly Expr[]]>();
    for (const [key, value] of [...relations].sort(([a], [b]) => a.join('\0').localeCompare(b.join('\0')))) {
      const [signature, expr] =
        value instanceof Lambda
          ? [value.variables.map((v) => instance(v, Sym)), instance(value.expr, Tuple).args]
          : value;
      rel.set(key, [signature, expr.map(sympify)]);
    }
    super(name, [
      patch,
      ...names,
      ...[...rel].flatMap(([[a, b], [s, e]]) => [new Sym(a), new Sym(b), new Tuple(s), new Tuple(e)]),
    ]);
    this.coordinateNames = names;
    this.relations = rel;
    patch.coordSystems.push(this);
  }
  /**
   * Identifies the manifold to which the patch belongs.
   *
   * @returns The parent manifold.
   * @see SymPy `sympy.diffgeom.diffgeom.CoordSystem.manifold`
   */
  get manifold(): Manifold {
    return this.patch.manifold;
  }
  /**
   * Counts the independent coordinates on the manifold.
   *
   * @returns The manifold dimension.
   * @see SymPy `sympy.diffgeom.diffgeom.CoordSystem.dim`
   */
  get dim(): number {
    return this.patch.dim;
  }
  /**
   * Lists the chart coordinates in axis order.
   *
   * @returns The coordinate symbols.
   * @see SymPy `sympy.diffgeom.diffgeom.CoordSystem.symbols`
   */
  get symbols(): CoordinateSymbol[] {
    return this.coordinateNames.map((_, i) => new CoordinateSymbol(this, i));
  }
  protected override computeKey(): string {
    return `CoordSystem:${this.name}(${this.args.map((a) => a.key).join(',')})`;
  }
  /**
   * Rebuilds the expression with replacement arguments in their original order.
   *
   * @param args - Replacement arguments in the same order as `args` on the original expression.
   * @returns The rebuilt expression.
   */
  withArgs(args: readonly Expr[]): Expr {
    const end = 1 + this.coordinateNames.length;
    const relations = new Map<readonly [string, string], CoordinateRelation>();
    for (let i = end; i < args.length; i += 4) {
      relations.set(
        [instance(at(args, i), Sym).name, instance(at(args, i + 1), Sym).name],
        [instance(at(args, i + 2), Tuple).args.map((s) => instance(s, Sym)), instance(at(args, i + 3), Tuple).args],
      );
    }
    return new CoordSystem(
      this.name,
      instance(at(args, 0), Patch),
      args.slice(1, end).map((a) => instance(a, Sym)),
      relations,
    );
  }
  /**
   * Formats the expression in plain text.
   *
   * @returns The formatted expression.
   */
  override printStr(): string {
    return this.name;
  }
  /**
   * Formats the expression as LaTeX.
   *
   * @param print - Formatter for a child expression.
   * @returns The formatted LaTeX.
   */
  override printLatex(print: (e: Expr) => string): string {
    return `\\text{${print(new Sym(this.name))}}^{\\text{${print(new Sym(this.patch.name))}}}_{${print(this.manifold)}}`;
  }
  /**
   * Builds the coordinate transformation from this chart to the target chart.
   *
   * @param to - Target coordinate system.
   * @returns The resulting transformation.
   * @see SymPy `sympy.diffgeom.diffgeom.CoordSystem.transformation`
   */
  transformation(to: CoordSystem): Transformation {
    return new Transformation(this.coordinateNames, this.transform(to, this.coordinateNames));
  }
  /**
   * Expresses coordinates from this chart in a target chart.
   *
   * @param to - Target coordinate system.
   * @param values - Coordinate values in chart order.
   * @returns The target coordinate values as a column matrix.
   * @throws RangeError when the coordinate count disagrees with the chart dimension or the coordinate systems are disconnected.
   * @see SymPy `sympy.diffgeom.diffgeom.CoordSystem.transform`
   * @example
   * ```ts
   * import { R2P, R2R } from '@symjs/symjs/diffgeom';
   *
   * const polar = R2R.transform(R2P, [0, 1]);
   * polar.get(0, 0); // => 1
   * polar.get(1, 0); // => pi/2
   * ```
   */
  transform(to: CoordSystem, values: readonly ExprLike[] | Matrix = this.symbols): Matrix {
    const input = coordinates(values);
    if (input.length !== this.coordinateNames.length) throw new RangeError('Incorrect number of coordinates');
    if (this.equals(to)) return column(input);
    const relations = [...this.relations, ...to.relations];
    for (const cs of this.patch.coordSystems) {
      for (const [target, relation] of cs.transforms) relations.push([[cs.name, target.name], relation]);
    }
    const queue: { name: string; values: Expr[] }[] = [{ name: this.name, values: input }];
    const seen = new Set([this.name]);
    for (let pos = 0; pos < queue.length; pos++) {
      const current = at(queue, pos);
      const edges = relations
        .filter(([[a]]) => a === current.name)
        .concat(
          relations.filter(([[a, b]]) => b === current.name && !relations.some(([[c, d]]) => c === b && d === a)),
        );
      for (const [[a, b], [xs, ys]] of edges) {
        const next = a === current.name ? b : a;
        if (seen.has(next)) continue;
        const result =
          a === current.name
            ? ys.map((y) => xreplace(y, replacements(xs, current.values)))
            : inverse(xs, ys, current.values);
        if (next === to.name) return column(result);
        seen.add(next);
        queue.push({ name: next, values: result });
      }
    }
    throw new RangeError('Two coordinate systems are not connected');
  }
  /**
   * Registers a coordinate transformation from this chart to another.
   *
   * @param to - Target coordinate system.
   * @param from - Symbols used for the source coordinates.
   * @param expressions - Target coordinates expressed in terms of the source symbols.
   * @param options - `inverse` registers the reverse transformation by default. Intermediate charts can be traversed on demand with `fillInGaps`.
   * @see SymPy `sympy.diffgeom.diffgeom.CoordSystem.connect_to`
   */
  connectTo(
    to: CoordSystem,
    from: readonly Sym[],
    expressions: readonly ExprLike[],
    options: { inverse?: boolean; fillInGaps?: boolean } = {},
  ): void {
    const exprs = expressions.map(sympify);
    replacements(from, exprs);
    const back = options.inverse === false ? [] : inverse(from, exprs, to.coordinateNames);
    this.transforms.set(to, [from, exprs]);
    if (options.inverse !== false) to.transforms.set(this, [to.coordinateNames, back]);
    // Connected paths are composed on demand, including when fillInGaps is requested.
  }
  /**
   * Transforms a coordinate tuple from this chart to the target chart.
   *
   * @param to - Target coordinate system.
   * @param values - Coordinate values in chart order.
   * @returns The target coordinates in a column matrix.
   * @see SymPy `sympy.diffgeom.diffgeom.CoordSystem.coord_tuple_transform_to`
   */
  coordTupleTransformTo(to: CoordSystem, values: readonly ExprLike[] | Matrix): Matrix {
    return this.transform(to, values);
  }
  /**
   * Computes the matrix of partial derivatives of the target coordinates with respect to the source
   * coordinates.
   *
   * @param to - Target coordinate system.
   * @param values - Coordinate values in chart order.
   * @returns The Jacobian with target coordinates indexing rows and source coordinates indexing columns.
   * @see SymPy `sympy.diffgeom.diffgeom.CoordSystem.jacobian`
   */
  jacobian(to: CoordSystem, values: readonly ExprLike[] | Matrix = this.symbols): Matrix {
    const xs = this.symbols;
    const transformed = this.transform(to);
    const pairs = replacements(xs, coordinates(values));
    return Matrix.fromFunction(transformed.rows, xs.length, (i, j) =>
      xreplace(diff(transformed.get(i, 0), at(xs, j)), pairs),
    );
  }
  /**
   * Computes the Jacobian matrix of the change from this chart to the target chart.
   *
   * @param to - Target coordinate system.
   * @param values - Coordinate values in chart order.
   * @returns The matrix of target-coordinate derivatives with respect to the source coordinates.
   * @see SymPy `sympy.diffgeom.diffgeom.CoordSystem.jacobian_matrix`
   */
  jacobianMatrix(to: CoordSystem, values?: readonly ExprLike[] | Matrix): Matrix {
    return this.jacobian(to, values);
  }
  /**
   * Computes the determinant of the Jacobian of the change from this chart to the target chart.
   *
   * @param to - Target coordinate system.
   * @param values - Coordinate values in chart order.
   * @returns The signed local scale factor for the coordinate transformation.
   * @see SymPy `sympy.diffgeom.diffgeom.CoordSystem.jacobian_determinant`
   */
  jacobianDeterminant(to: CoordSystem, values?: readonly ExprLike[] | Matrix): Expr {
    return this.jacobian(to, values).det();
  }
  /**
   * Creates a point with the supplied coordinates in this chart.
   *
   * @param values - Coordinate values in chart order.
   * @returns A point in this coordinate system.
   * @see SymPy `sympy.diffgeom.diffgeom.CoordSystem.point`
   */
  point(values: readonly ExprLike[] | Matrix): Point {
    return new Point(this, values);
  }
  /**
   * Expresses the coordinates of a point in this chart.
   *
   * @param point - Point at which to evaluate the operation.
   * @returns The coordinate column in this chart.
   * @see SymPy `sympy.diffgeom.diffgeom.CoordSystem.point_to_coords`
   */
  pointToCoords(point: Point): Matrix {
    return point.coords(this);
  }
  /**
   * Selects the scalar field that reads one coordinate of a point.
   *
   * @param index - Zero-based index or indices selecting the desired component.
   * @returns The resulting base scalar field.
   * @see SymPy `sympy.diffgeom.diffgeom.CoordSystem.base_scalar`
   */
  baseScalar(index: number): BaseScalarField {
    return new BaseScalarField(this, index);
  }
  /**
   * Selects the scalar field for one coordinate direction.
   *
   * @param index - Zero-based index or indices selecting the desired component.
   * @returns The resulting base scalar field.
   * @see SymPy `sympy.diffgeom.diffgeom.CoordSystem.coord_function`
   */
  coordFunction(index: number): BaseScalarField {
    return this.baseScalar(index);
  }
  /**
   * Lists the basis scalar fields in chart order.
   *
   * @returns The coordinate fields.
   * @see SymPy `sympy.diffgeom.diffgeom.CoordSystem.base_scalars`
   */
  baseScalars(): BaseScalarField[] {
    return this.coordinateNames.map((_, i) => this.baseScalar(i));
  }
  /**
   * Lists the coordinate scalar fields in chart order.
   *
   * @returns The resulting list in axis order.
   * @see SymPy `sympy.diffgeom.diffgeom.CoordSystem.coord_functions`
   */
  coordFunctions(): BaseScalarField[] {
    return this.baseScalars();
  }
  /**
   * Selects the vector field that differentiates along one coordinate.
   *
   * @param index - Zero-based index or indices selecting the desired component.
   * @returns The resulting base vector field.
   * @see SymPy `sympy.diffgeom.diffgeom.CoordSystem.base_vector`
   */
  baseVector(index: number): BaseVectorField {
    return new BaseVectorField(this, index);
  }
  /**
   * Lists the coordinate basis vectors in axis order.
   *
   * @returns The vector fields.
   * @see SymPy `sympy.diffgeom.diffgeom.CoordSystem.base_vectors`
   */
  baseVectors(): BaseVectorField[] {
    return this.coordinateNames.map((_, i) => this.baseVector(i));
  }
  /**
   * Selects the basis one-form dual to the indexed coordinate vector.
   *
   * @param index - Zero-based index or indices selecting the desired component.
   * @returns The one-form dual to the selected basis vector.
   * @see SymPy `sympy.diffgeom.diffgeom.CoordSystem.base_oneform`
   */
  baseOneform(index: number): Expr {
    return Differential(this.baseScalar(index));
  }
  /**
   * Constructs the dual basis of the coordinate vector fields.
   *
   * @returns The coordinate one-forms.
   * @see SymPy `sympy.diffgeom.diffgeom.CoordSystem.base_oneforms`
   */
  baseOneforms(): Expr[] {
    return this.coordinateNames.map((_, i) => this.baseOneform(i));
  }
}

/** Eliminate one source coordinate at a time, retaining every inverse branch. */
function inverse(xs: readonly Sym[], expressions: readonly Expr[], targets: readonly Expr[]): Expr[] {
  const variables = xs.map((x) => new Dummy(x.name, x.assumptions));
  const renamed = replacements(xs, variables);
  let branches: { equations: Expr[]; values: Expr[] }[] = [
    { equations: expressions.map((e, i) => sub(xreplace(e, renamed), at(targets, i))), values: [] },
  ];
  for (const x of variables) {
    const next: typeof branches = [];
    for (const branch of branches) {
      const equation = branch.equations.find((e) => e.has(x));
      if (equation === undefined) throw new NotImplementedError('Inverse relation is underdetermined');
      for (const solution of solve(equation, x)) {
        const pair: [Expr, Expr][] = [[x, solution]];
        const values = [...branch.values.map((v) => xreplace(v, pair)), solution];
        next.push({
          equations: branch.equations.filter((e) => e !== equation).map((e) => simplify(xreplace(e, pair))),
          values,
        });
      }
    }
    branches = next;
  }
  branches = branches.filter((b) => b.equations.every((e) => simplify(e).equals(0)));
  if (branches.length === 0) throw new NotImplementedError('Cannot solve inverse relation');
  if (branches.length > 1) throw new RangeError('Obtained multiple inverse relations');
  return at(branches, 0).values;
}

/**
 * A symbol representing one of a chart’s coordinates and carrying its assumptions.
 *
 * @see SymPy `sympy.diffgeom.diffgeom.CoordinateSymbol`
 * @example
 * ```ts
 * import { CoordinateSymbol, R2R } from '@symjs/symjs/diffgeom';
 *
 * const x = new CoordinateSymbol(R2R, 0);
 * x.name; // => x
 * x.index; // => 0
 * ```
 */
export class CoordinateSymbol extends Sym {
  /**
   * Constructs an instance of `CoordinateSymbol`.
   *
   * @param coordSys - Coordinate system defining the basis.
   * @param index - Zero-based index or indices selecting the desired component.
   */
  constructor(
    /** The coordinate system in which this object is defined. */
    readonly coordSys: CoordSystem,
    /** Zero-based coordinate direction in the chart. */
    readonly index: number,
  ) {
    const symbol = at(coordSys.coordinateNames, index);
    super(symbol.name, symbol.assumptions);
  }
  protected override computeKey(): string {
    return `CoordinateSymbol:${this.coordSys.key}:${this.index}`;
  }
  /**
   * Identifies the class used to sort this expression.
   *
   * @returns The ordering class name.
   */
  override get sortClass(): string {
    return 'CoordinateSymbol';
  }
  /**
   * Expresses this coordinate in another chart.
   *
   * @param to - Target coordinate system or representation.
   * @returns The coordinate expressed in the requested chart when a transformation exists.
   * @see SymPy `sympy.diffgeom.diffgeom.CoordinateSymbol.rewrite`
   */
  override rewrite(to: string | CoordSystem): Expr {
    return to instanceof CoordSystem ? to.transform(this.coordSys).get(this.index, 0) : super.rewrite(to);
  }
}

/**
 * A point on a manifold specified by a chart and its coordinates.
 *
 * @see SymPy `sympy.diffgeom.diffgeom.Point`
 * @remarks SymPy prints this coordinate column as `Matrix([[-sqrt(2)], [sqrt(2)]])`.
 * @example
 * ```ts
 * import { ex } from '@symjs/symjs';
 * import { Point, R2P, R2R } from '@symjs/symjs/diffgeom';
 *
 * const p = new Point(R2P, [2, ex`3*pi/4`]);
 * p.coords(R2R); // => Matrix([
 * //   [-sqrt(2)],
 * //   [ sqrt(2)]])
 * ```
 */
export class Point extends ExtensionExpr {
  /** The coordinates of the point as a column matrix. */
  readonly coordinates: readonly Expr[];
  /**
   * Constructs an instance of `Point`.
   *
   * @param coordSys - Coordinate system defining the basis.
   * @param values - Coordinate values in chart order.
   */
  constructor(
    /** The coordinate system in which this object is defined. */
    readonly coordSys: CoordSystem,
    values: readonly ExprLike[] | Matrix,
  ) {
    const coords = coordinates(values);
    replacements(coordSys.coordinateNames, coords);
    super('Point', [coordSys, ...coords]);
    this.coordinates = coords;
  }
  /**
   * Identifies the patch on which this object is defined.
   *
   * @returns The coordinate patch.
   * @see SymPy `sympy.diffgeom.diffgeom.Point.patch`
   */
  get patch(): Patch {
    return this.coordSys.patch;
  }
  /**
   * Identifies the manifold to which the patch belongs.
   *
   * @returns The parent manifold.
   * @see SymPy `sympy.diffgeom.diffgeom.Point.manifold`
   */
  get manifold(): Manifold {
    return this.coordSys.manifold;
  }
  /**
   * Counts the independent coordinates on the manifold.
   *
   * @returns The manifold dimension.
   * @see SymPy `sympy.diffgeom.diffgeom.Point.dim`
   */
  get dim(): number {
    return this.manifold.dim;
  }
  /**
   * Coordinates of the point in given coordinate system. If coordinate system is not passed, it
   * returns the coordinates in the coordinate system in which the point was defined.
   *
   * @param to - Target coordinate system.
   * @returns The coordinate column in the selected chart.
   * @see SymPy `sympy.diffgeom.diffgeom.Point.coords`
   */
  coords(to: CoordSystem = this.coordSys): Matrix {
    return this.coordSys.transform(to, this.coordinates);
  }
  /**
   * Rebuilds the expression with replacement arguments in their original order.
   *
   * @param args - Replacement arguments in the same order as `args` on the original expression.
   * @returns The rebuilt expression.
   */
  withArgs(args: readonly Expr[]): Expr {
    return new Point(instance(at(args, 0), CoordSystem), args.slice(1));
  }
  /**
   * Collects the free symbols of this expression.
   *
   * @returns The set of free symbols.
   * @see SymPy `sympy.diffgeom.diffgeom.Point.free_symbols`
   */
  override freeSymbolsSelf(): ReadonlySet<Expr> {
    return column(this.coordinates).freeSymbols();
  }
  /**
   * Formats the expression in plain text.
   *
   * @returns The formatted expression.
   */
  override printStr(): string {
    return `Point(${String(this.coordSys)}, ${String(column(this.coordinates))})`;
  }
}

/**
 * Base scalar field over a manifold for a given coordinate system.
 *
 * @see SymPy `sympy.diffgeom.diffgeom.BaseScalarField`
 * @example
 * ```ts
 * import { BaseScalarField, R2R } from '@symjs/symjs/diffgeom';
 *
 * new BaseScalarField(R2R, 1).call(R2R.point([2, 3])); // => 3
 * ```
 */
export class BaseScalarField extends ExtensionExpr {
  /**
   * Constructs an instance of `BaseScalarField`.
   *
   * @param coordSys - Coordinate system defining the basis.
   * @param index - Zero-based index or indices selecting the desired component.
   */
  constructor(
    /**
     * The coordinate system in which this object is defined.
     *
     * @see SymPy `sympy.diffgeom.diffgeom.BaseScalarField.coord_sys`
     */
    readonly coordSys: CoordSystem,
    /**
     * Zero-based coordinate direction in the chart.
     *
     * @see SymPy `sympy.diffgeom.diffgeom.BaseScalarField.index`
     */
    readonly index: number,
  ) {
    super('BaseScalarField', [coordSys, sympify(index)]);
    at(coordSys.coordinateNames, index);
  }
  /**
   * Identifies the patch on which this object is defined.
   *
   * @returns The coordinate patch.
   * @see SymPy `sympy.diffgeom.diffgeom.BaseScalarField.patch`
   */
  get patch(): Patch {
    return this.coordSys.patch;
  }
  /**
   * Identifies the manifold to which the patch belongs.
   *
   * @returns The parent manifold.
   * @see SymPy `sympy.diffgeom.diffgeom.BaseScalarField.manifold`
   */
  get manifold(): Manifold {
    return this.coordSys.manifold;
  }
  /**
   * Counts the independent coordinates on the manifold.
   *
   * @returns The manifold dimension.
   * @see SymPy `sympy.diffgeom.diffgeom.BaseScalarField.dim`
   */
  get dim(): number {
    return this.manifold.dim;
  }
  /**
   * Rebuilds the expression with replacement arguments in their original order.
   *
   * @param args - Replacement arguments in the same order as `args` on the original expression.
   * @returns The rebuilt expression.
   */
  withArgs(args: readonly Expr[]): Expr {
    return new BaseScalarField(instance(at(args, 0), CoordSystem), indexValue(at(args, 1)));
  }
  /**
   * Formats the expression in plain text.
   *
   * @param print - Formatter for a child expression.
   * @returns The formatted expression.
   */
  override printStr(print: (e: Expr) => string): string {
    return print(at(this.coordSys.coordinateNames, this.index));
  }
  /**
   * Formats the expression as LaTeX.
   *
   * @param print - Formatter for a child expression.
   * @returns The formatted LaTeX.
   */
  override printLatex(print: (e: Expr) => string): string {
    return `\\mathbf{${print(at(this.coordSys.coordinateNames, this.index))}}`;
  }
  /**
   * Collects the free symbols of this expression.
   *
   * @returns The set of free symbols.
   * @see SymPy `sympy.diffgeom.diffgeom.BaseScalarField.free_symbols`
   */
  override freeSymbolsSelf(): ReadonlySet<Expr> {
    return new Set();
  }
  /**
   * Computes the derivative of this expression.
   *
   * @returns Zero for ordinary symbolic differentiation of the coordinate field.
   */
  override diffSelf(): Expr {
    return S.Zero;
  }
  /**
   * Evaluates the coordinate scalar at the given point.
   *
   * @param args - Point on which to evaluate the coordinate field.
   * @returns The coordinate value at the point, or the scalar field when no point is supplied.
   * @see SymPy `sympy.diffgeom.diffgeom.BaseScalarField.__call__`
   */
  call(...args: (ExprLike | null)[]): Expr {
    const point = args[0];
    return args.length === 1 && point instanceof Point
      ? simplify(point.coords(this.coordSys).get(this.index, 0))
      : this;
  }
}

/**
 * Base vector field over a manifold for a given coordinate system.
 *
 * @see SymPy `sympy.diffgeom.diffgeom.BaseVectorField`
 * @example
 * ```ts
 * import { BaseVectorField, R2R } from '@symjs/symjs/diffgeom';
 *
 * new BaseVectorField(R2R, 1).call(R2R.y.pow(2)); // => 2*y
 * ```
 */
export class BaseVectorField extends ExtensionExpr {
  /**
   * Constructs an instance of `BaseVectorField`.
   *
   * @param coordSys - Coordinate system defining the basis.
   * @param index - Zero-based index or indices selecting the desired component.
   */
  constructor(
    /**
     * The coordinate system in which this object is defined.
     *
     * @see SymPy `sympy.diffgeom.diffgeom.BaseVectorField.coord_sys`
     */
    readonly coordSys: CoordSystem,
    /**
     * Zero-based coordinate direction in the chart.
     *
     * @see SymPy `sympy.diffgeom.diffgeom.BaseVectorField.index`
     */
    readonly index: number,
  ) {
    super('BaseVectorField', [coordSys, sympify(index)]);
    at(coordSys.coordinateNames, index);
  }
  /**
   * Identifies the patch on which this object is defined.
   *
   * @returns The coordinate patch.
   * @see SymPy `sympy.diffgeom.diffgeom.BaseVectorField.patch`
   */
  get patch(): Patch {
    return this.coordSys.patch;
  }
  /**
   * Identifies the manifold to which the patch belongs.
   *
   * @returns The parent manifold.
   * @see SymPy `sympy.diffgeom.diffgeom.BaseVectorField.manifold`
   */
  get manifold(): Manifold {
    return this.coordSys.manifold;
  }
  /**
   * Counts the independent coordinates on the manifold.
   *
   * @returns The manifold dimension.
   * @see SymPy `sympy.diffgeom.diffgeom.BaseVectorField.dim`
   */
  get dim(): number {
    return this.manifold.dim;
  }
  /**
   * Indicates whether the field commutes under multiplication.
   *
   * @returns Its commutativity flag.
   * @see SymPy `sympy.diffgeom.diffgeom.BaseVectorField.is_commutative`
   */
  override get isCommutative(): boolean {
    return false;
  }
  /**
   * Rebuilds the expression with replacement arguments in their original order.
   *
   * @param args - Replacement arguments in the same order as `args` on the original expression.
   * @returns The rebuilt expression.
   */
  withArgs(args: readonly Expr[]): Expr {
    return new BaseVectorField(instance(at(args, 0), CoordSystem), indexValue(at(args, 1)));
  }
  /**
   * Formats the expression in plain text.
   *
   * @param print - Formatter for a child expression.
   * @returns The formatted expression.
   */
  override printStr(print: (e: Expr) => string): string {
    return `e_${print(at(this.coordSys.coordinateNames, this.index))}`;
  }
  /**
   * Formats the expression as LaTeX.
   *
   * @param print - Formatter for a child expression.
   * @returns The formatted LaTeX.
   */
  override printLatex(print: (e: Expr) => string): string {
    return `\\partial_{${print(at(this.coordSys.coordinateNames, this.index))}}`;
  }
  /**
   * Differentiates the scalar field along this coordinate direction.
   *
   * @param field - Field to evaluate or differentiate.
   * @returns The directional derivative of the scalar field.
   * @throws RangeError when the argument of the vector field is not scalar.
   * @see SymPy `sympy.diffgeom.diffgeom.BaseVectorField.__call__`
   */
  call(field: ExprLike | null = null): Expr {
    if (field === null) return this;
    const f = sympify(field);
    if (covariantOrder(f) || contravariantOrder(f))
      throw new RangeError('Only scalar fields can be supplied to vector fields');
    const scalars = atoms(f, BaseScalarField);
    const dummies = scalars.map((_, i) => new Dummy(`xi${i}`));
    const body = xreplace(f, replacements(scalars, dummies));
    const result = add(
      ...scalars.map((scalar, i) => {
        const jacobian = this.coordSys.jacobian(scalar.coordSys, this.coordSys.baseScalars());
        return mul(
          xreplace(diff(body, at(dummies, i)), replacements(dummies, scalars)),
          jacobian.get(scalar.index, this.index),
        );
      }),
    );
    return result;
  }
}

function order(e: Expr, contra: boolean, strict: boolean): number {
  if (e instanceof Add || e instanceof Mul) {
    const orders = e.args.map((a) => order(a, contra, false));
    if (e instanceof Add) {
      if (new Set(orders).size !== 1) throw new RangeError('Fields of varying order');
      return at(orders, 0);
    }
    const nonzero = orders.filter((o) => o !== 0);
    if (nonzero.length > 1) throw new RangeError('Multiplication of tensor fields requires TensorProduct');
    return nonzero[0] ?? 0;
  }
  if (e instanceof Pow) {
    // SymPy 1.14 checks covariant_order twice and misses powers of vectors.
    if ([e.base, e.exp].some((a) => covariantOrder(a) !== 0 || contravariantOrder(a) !== 0))
      throw new RangeError('A tensor field cannot be raised to a power');
    return 0;
  }
  if (e instanceof TensorProductNode) return e.args.reduce((sum, a) => sum + order(a, contra, false), 0);
  if (e instanceof DifferentialNode) return contra ? 0 : covariantOrder(e.formField) + 1;
  if (e instanceof BaseVectorField || e instanceof CommutatorNode) return contra ? 1 : 0;
  if (e instanceof LieDerivativeNode) return order(e.expr, contra, false);
  return !strict || atoms(e, BaseScalarField).length > 0 ? 0 : -1;
}
/**
 * Counts the contravariant slots of a tensor field.
 *
 * @param expr - Symbolic expression on which to operate.
 * @param strict - Return -1 for a scalar expression without a coordinate field.
 * @returns The computed contravariant order.
 * @throws RangeError when terms have incompatible tensor orders or the expression contains an ambiguous tensor product.
 * @see SymPy `sympy.diffgeom.diffgeom.contravariant_order`
 * @example
 * ```ts
 * import { ex } from '@symjs/symjs';
 * import { R2, contravariantOrder } from '@symjs/symjs/diffgeom';
 *
 * contravariantOrder(ex`a`); // => 0
 * contravariantOrder(R2.eX); // => 1
 * ```
 */
export function contravariantOrder(expr: ExprLike, strict = false): number {
  return order(sympify(expr), true, strict);
}
/**
 * Counts the covariant slots of a tensor field.
 *
 * @param expr - Symbolic expression on which to operate.
 * @param strict - Return -1 for a scalar expression without a coordinate field.
 * @returns The computed covariant order.
 * @throws RangeError when terms have incompatible tensor orders or the expression contains an ambiguous tensor product.
 * @see SymPy `sympy.diffgeom.diffgeom.covariant_order`
 * @example
 * ```ts
 * import { ex } from '@symjs/symjs';
 * import { R2, covariantOrder } from '@symjs/symjs/diffgeom';
 *
 * covariantOrder(ex`a`); // => 0
 * covariantOrder(R2.dx); // => 1
 * ```
 */
export function covariantOrder(expr: ExprLike, strict = false): number {
  return order(sympify(expr), false, strict);
}
function vector(e: Expr): void {
  if (contravariantOrder(e) !== 1 || covariantOrder(e) !== 0) throw new RangeError('Expected a vector field');
}
function apply(e: Expr, args: readonly (ExprLike | null)[]): Expr {
  return rcall(e, ...args);
}

class CommutatorNode extends ExtensionExpr {
  constructor(
    readonly v1: Expr,
    readonly v2: Expr,
  ) {
    super('Commutator', [v1, v2]);
  }
  override get isCommutative(): boolean {
    return false;
  }
  withArgs(args: readonly Expr[]): Expr {
    return Commutator(at(args, 0), at(args, 1));
  }
  call(field: ExprLike): Expr {
    return sub(apply(this.v1, [apply(this.v2, [field])]), apply(this.v2, [apply(this.v1, [field])]));
  }
}
/**
 * Computes the commutator of two vector fields by subtracting the two orders of differentiation.
 *
 * @param v1 - First vector field in the commutator.
 * @param v2 - Second vector field in the commutator.
 * @returns The vector-field commutator, or zero for commuting fields.
 * @throws RangeError when either input is not a vector field.
 * @see SymPy `sympy.diffgeom.diffgeom.Commutator`
 * @example
 * ```ts
 * import { Commutator, R2R } from '@symjs/symjs/diffgeom';
 *
 * Commutator(R2R.eX, R2R.eY); // => 0
 * ```
 */
export function Commutator(v1: ExprLike, v2: ExprLike): Expr {
  const a = sympify(v1),
    b = sympify(v2);
  vector(a);
  vector(b);
  if (a.equals(b)) return S.Zero;
  if (systems(add(a, b)).length !== 1) return new CommutatorNode(a, b);
  return expand(
    add(
      ...atoms(a, BaseVectorField).flatMap((x) =>
        atoms(b, BaseVectorField).map((y) => {
          const c = coeff(expand(a), x),
            d = coeff(expand(b), y);
          return sub(mul(c, x.call(d), y), mul(d, y.call(c), x));
        }),
      ),
    ),
  );
}

class DifferentialNode extends ExtensionExpr {
  constructor(readonly formField: Expr) {
    super('Differential', [formField]);
  }
  override get isCommutative(): boolean {
    return false;
  }
  withArgs(args: readonly Expr[]): Expr {
    return Differential(at(args, 0));
  }
  override printStr(print: (e: Expr) => string): string {
    return this.formField instanceof BaseScalarField ? `d${print(this.formField)}` : `d(${print(this.formField)})`;
  }
  override printLatex(print: (e: Expr) => string): string {
    return this.formField instanceof BaseScalarField
      ? `\\operatorname{d}${print(at(this.formField.coordSys.coordinateNames, this.formField.index))}`
      : `\\operatorname{d}\\left(${print(this.formField)}\\right)`;
  }
  call(...fields: (ExprLike | null)[]): Expr {
    const degree = covariantOrder(this);
    if (fields.length > degree) throw new RangeError('Too many arguments to Differential');
    const vs = fields.map((f) => (f === null ? null : sympify(f)));
    vs.forEach((v) => {
      if (v !== null) vector(v);
    });
    if (vs.length === 0 || vs.every((v) => v === null)) return this;
    if (degree === 1) return apply(instance(at(vs, 0), Expr), [this.formField]);
    if (vs.length !== degree || vs.some((v) => v === null))
      throw new NotImplementedError('Partial contraction of an exterior derivative of higher degree');
    const vectors = vs.map((v) => instance(v, Expr));
    return add(
      ...vectors.flatMap((v, i) => {
        const terms = [
          mul(
            (-1) ** i,
            apply(v, [
              apply(
                this.formField,
                vectors.filter((_, k) => k !== i),
              ),
            ]),
          ),
        ];
        for (let j = i + 1; j < vectors.length; j++) {
          const bracket = Commutator(v, at(vectors, j));
          if (!bracket.equals(0))
            terms.push(
              mul((-1) ** (i + j), apply(this.formField, [bracket, ...vectors.filter((_, k) => k !== i && k !== j)])),
            );
        }
        return terms;
      }),
    );
  }
}
/**
 * Return the differential (exterior derivative) of a form field.
 *
 * @param form - Scalar field or differential form to differentiate.
 * @returns The exterior derivative, or zero for a repeated exterior derivative.
 * @throws RangeError when the operand has contravariant slots.
 * @see SymPy `sympy.diffgeom.diffgeom.Differential`
 * @example
 * ```ts
 * import { rcall } from '@symjs/symjs';
 * import { Differential, R2R } from '@symjs/symjs/diffgeom';
 *
 * const dx = Differential(R2R.x);
 * rcall(dx, R2R.eX); // => 1
 * Differential(dx); // => 0
 * ```
 */
export function Differential(form: ExprLike): Expr {
  const f = sympify(form);
  if (contravariantOrder(f)) throw new RangeError('Differential requires a form field');
  return f instanceof DifferentialNode ? S.Zero : new DifferentialNode(f);
}

class TensorProductNode extends ExtensionExpr {
  constructor(
    args: readonly Expr[],
    readonly alternating = false,
  ) {
    super(alternating ? 'WedgeProduct' : 'TensorProduct', args);
  }
  override get isCommutative(): boolean {
    return false;
  }
  withArgs(args: readonly Expr[]): Expr {
    return product(args, this.alternating);
  }
  call(...fields: (ExprLike | null)[]): Expr {
    const orders = this.args.map((a) => covariantOrder(a) + contravariantOrder(a));
    const total = orders.reduce((a, b) => a + b, 0);
    if (fields.length > total) throw new RangeError('Too many arguments to tensor');
    const padded = [...fields, ...Array.from({ length: total - fields.length }, () => null)];
    const contract = (values: readonly (ExprLike | null)[]): Expr => {
      let start = 0;
      return TensorProduct(
        ...this.args.map((a, i) => {
          const end = start + at(orders, i),
            result = apply(a, values.slice(start, end));
          start = end;
          return result;
        }),
      );
    };
    if (!this.alternating) return contract(padded);
    const denominator = mul(...orders.map((n) => factorial(n)));
    function permute(indices: number[]): Expr {
      if (indices.length === total) {
        let inversions = 0;
        indices.forEach((v, i) =>
          indices.slice(i + 1).forEach((w) => {
            if (v > w) inversions++;
          }),
        );
        return mul((-1) ** inversions, contract(indices.map((i) => at(padded, i))));
      }
      return add(...padded.flatMap((_, i) => (indices.includes(i) ? [] : [permute([...indices, i])])));
    }
    return expand(permute([]).div(denominator));
  }
}
function product(args: readonly ExprLike[], alternating: boolean): Expr {
  const scalar: Expr[] = [],
    tensors: Expr[] = [];
  args.map(sympify).forEach((a) => (covariantOrder(a) + contravariantOrder(a) === 0 ? scalar : tensors).push(a));
  return mul(...scalar, ...(tensors.length < 2 ? tensors : [new TensorProductNode(tensors, alternating)]));
}
/**
 * Forms the ordered tensor product of vector fields and differential forms.
 *
 * @param args - Factors in tensor-product order.
 * @returns The tensor product of the factors.
 * @see SymPy `sympy.diffgeom.diffgeom.TensorProduct`
 * @example
 * ```ts
 * import { rcall } from '@symjs/symjs';
 * import { R2, TensorProduct } from '@symjs/symjs/diffgeom';
 *
 * const form = TensorProduct(R2.dx, R2.dy);
 * rcall(form, R2.eX, R2.eY); // => 1
 * rcall(form, R2.eY, R2.eX); // => 0
 * ```
 */
export function TensorProduct(...args: ExprLike[]): Expr {
  return product(args, false);
}
/**
 * Forms the alternating tensor product of the supplied fields.
 *
 * @param args - Factors in alternating-product order.
 * @returns The alternating product of the factors.
 * @see SymPy `sympy.diffgeom.diffgeom.WedgeProduct`
 * @example
 * ```ts
 * import { rcall } from '@symjs/symjs';
 * import { R2, WedgeProduct } from '@symjs/symjs/diffgeom';
 *
 * const form = WedgeProduct(R2.dx, R2.dy);
 * rcall(form, R2.eX, R2.eY); // => 1
 * rcall(form, R2.eY, R2.eX); // => -1
 * ```
 */
export function WedgeProduct(...args: ExprLike[]): Expr {
  return product(args, true);
}

class LieDerivativeNode extends ExtensionExpr {
  constructor(
    readonly vField: Expr,
    readonly expr: Expr,
  ) {
    super('LieDerivative', [vField, expr]);
  }
  override get isCommutative(): boolean {
    return false;
  }
  withArgs(args: readonly Expr[]): Expr {
    return LieDerivative(at(args, 0), at(args, 1));
  }
  call(...fields: ExprLike[]): Expr {
    const vs = fields.map(sympify);
    vs.forEach(vector);
    // SymPy 1.14 multiplies the argument vectors in the correction term;
    // the tensor must instead be evaluated on the replaced argument list.
    return sub(
      apply(this.vField, [apply(this.expr, vs)]),
      add(
        ...vs.map((v, i) => {
          const bracket = Commutator(this.vField, v);
          return bracket.equals(0)
            ? S.Zero
            : apply(
                this.expr,
                vs.map((w, j) => (i === j ? bracket : w)),
              );
        }),
      ),
    );
  }
}
/**
 * Computes the Lie derivative along the specified vector field.
 *
 * @param v - Vector field giving the direction of differentiation or flow.
 * @param expr - Symbolic expression on which to operate.
 * @returns The derivative of the field or tensor along the vector field.
 * @throws RangeError when the differentiation direction is not a vector field.
 * @see SymPy `sympy.diffgeom.diffgeom.LieDerivative`
 * @example
 * ```ts
 * import { LieDerivative, R2R } from '@symjs/symjs/diffgeom';
 *
 * LieDerivative(R2R.eX, R2R.y); // => 0
 * LieDerivative(R2R.eX, R2R.x); // => 1
 * ```
 */
export function LieDerivative(v: ExprLike, expr: ExprLike): Expr {
  const field = sympify(v),
    e = sympify(expr);
  vector(field);
  if (covariantOrder(e) > 0) return new LieDerivativeNode(field, e);
  return contravariantOrder(e) > 0 ? Commutator(field, e) : apply(field, [e]);
}

/**
 * Rewrites the basis vectors in the target chart while keeping scalar coefficients in their
 * original coordinates.
 *
 * @param expr - Symbolic expression on which to operate.
 * @param to - Target coordinate system.
 * @returns The same field in the requested vector basis, with its scalar coefficients preserved.
 * @see SymPy `sympy.diffgeom.diffgeom.vectors_in_basis`
 * @example
 * ```ts
 * import { R2P, R2R, vectorsInBasis } from '@symjs/symjs/diffgeom';
 *
 * vectorsInBasis(R2P.eR, R2R); // => sin(theta)*e_y + cos(theta)*e_x
 * ```
 */
export function vectorsInBasis(expr: ExprLike, to: CoordSystem): Expr {
  const e = sympify(expr);
  return xreplace(
    e,
    atoms(e, BaseVectorField).map((v): [Expr, Expr] => {
      const jac = v.coordSys.jacobian(to, v.coordSys.baseScalars());
      return [v, add(...to.baseVectors().map((b, j) => mul(jac.get(j, v.index), b)))];
    }),
  );
}

/**
 * Covariant differentiation along one coordinate basis vector using the supplied connection
 * coefficients.
 *
 * @see SymPy `sympy.diffgeom.diffgeom.BaseCovarDerivativeOp`
 * @example
 * ```ts
 * import { BaseCovarDerivativeOp, R2, R2R, TensorProduct, metricToChristoffel2nd } from '@symjs/symjs/diffgeom';
 *
 * const metric = TensorProduct(R2.dx, R2.dx).add(TensorProduct(R2.dy, R2.dy));
 * const deriv = new BaseCovarDerivativeOp(R2R, 0, metricToChristoffel2nd(metric));
 * deriv.call(R2.x); // => 1
 * ```
 */
export class BaseCovarDerivativeOp extends ExtensionExpr {
  /**
   * The connection coefficients indexed by the output and two input directions.
   *
   * @see SymPy `sympy.diffgeom.diffgeom.BaseCovarDerivativeOp.christoffel`
   */
  readonly christoffel: NDimArray;
  /**
   * Constructs an instance of `BaseCovarDerivativeOp`.
   *
   * @param coordSys - Coordinate system defining the basis.
   * @param index - Zero-based index or indices selecting the desired component.
   * @param christoffel - Christoffel symbols of the second kind, indexed by three coordinate directions.
   */
  constructor(
    /**
     * The coordinate system in which this object is defined.
     *
     * @see SymPy `sympy.diffgeom.diffgeom.BaseCovarDerivativeOp.coord_sys`
     */
    readonly coordSys: CoordSystem,
    /**
     * Zero-based coordinate direction in the chart.
     *
     * @see SymPy `sympy.diffgeom.diffgeom.BaseCovarDerivativeOp.index`
     */
    readonly index: number,
    christoffel: NDimArray | readonly (readonly (readonly ExprLike[])[])[],
  ) {
    const ch = christoffel instanceof NDimArray ? christoffel : new ImmutableDenseNDimArray(christoffel);
    super('BaseCovarDerivativeOp', [coordSys, sympify(index), ch]);
    at(coordSys.coordinateNames, index);
    this.christoffel = ch;
  }
  /**
   * Rebuilds the expression with replacement arguments in their original order.
   *
   * @param args - Replacement arguments in the same order as `args` on the original expression.
   * @returns The rebuilt expression.
   */
  withArgs(args: readonly Expr[]): Expr {
    return new BaseCovarDerivativeOp(
      instance(at(args, 0), CoordSystem),
      indexValue(at(args, 1)),
      instance(at(args, 2), NDimArray),
    );
  }
  /**
   * Computes the covariant derivative in the chosen basis direction.
   *
   * @param field - Field to evaluate or differentiate.
   * @returns The differentiated field.
   * @throws NotImplementedError when the operand is a differential form of positive degree.
   * @see SymPy `sympy.diffgeom.diffgeom.BaseCovarDerivativeOp.__call__`
   */
  call(field: ExprLike): Expr {
    const f = vectorsInBasis(field, this.coordSys),
      basis = this.coordSys.baseVector(this.index);
    const derive = (e: Expr): Expr => {
      if (e instanceof Add) return add(...e.args.map(derive));
      if (e instanceof Mul)
        return add(...e.args.map((a, i) => mul(...e.args.map((b, j) => (i === j ? derive(a) : b)))));
      if (e instanceof TensorProductNode)
        return add(
          ...e.args.map((a, i) =>
            product(
              e.args.map((b, j) => (i === j ? derive(a) : b)),
              e.alternating,
            ),
          ),
        );
      if (e instanceof BaseVectorField)
        return add(...this.coordSys.baseVectors().map((b, k) => mul(this.christoffel.get(k, this.index, e.index), b)));
      if (covariantOrder(e)) throw new NotImplementedError('Covariant derivatives of forms');
      return basis.call(e);
    };
    return expand(derive(f));
  }
}
/**
 * Covariant differentiation along a vector field using the supplied connection coefficients.
 *
 * @see SymPy `sympy.diffgeom.diffgeom.CovarDerivativeOp`
 * @example
 * ```ts
 * import { CovarDerivativeOp, R2, TensorProduct, metricToChristoffel2nd } from '@symjs/symjs/diffgeom';
 *
 * const metric = TensorProduct(R2.dx, R2.dx).add(TensorProduct(R2.dy, R2.dy));
 * const deriv = new CovarDerivativeOp(R2.x.mul(R2.eX), metricToChristoffel2nd(metric));
 * deriv.call(R2.x); // => x
 * ```
 */
export class CovarDerivativeOp extends ExtensionExpr {
  /**
   * The vector field giving the differentiation direction.
   *
   * @see SymPy `sympy.diffgeom.diffgeom.CovarDerivativeOp.wrt`
   */
  readonly wrt: Expr;
  /**
   * The connection coefficients indexed by the output and two input directions.
   *
   * @see SymPy `sympy.diffgeom.diffgeom.CovarDerivativeOp.christoffel`
   */
  readonly christoffel: NDimArray;
  /**
   * Constructs an instance of `CovarDerivativeOp`.
   *
   * @param wrt - The vector field giving the differentiation direction.
   * @param christoffel - Christoffel symbols of the second kind, indexed by three coordinate directions.
   * @throws NotImplementedError when the direction uses more than one coordinate system.
   */
  constructor(wrt: ExprLike, christoffel: NDimArray | readonly (readonly (readonly ExprLike[])[])[]) {
    const v = sympify(wrt);
    vector(v);
    if (systems(v).length > 1) throw new NotImplementedError('Covariant derivative with mixed coordinate systems');
    const ch = christoffel instanceof NDimArray ? christoffel : new ImmutableDenseNDimArray(christoffel);
    super('CovarDerivativeOp', [v, ch]);
    this.wrt = v;
    this.christoffel = ch;
  }
  /**
   * Rebuilds the expression with replacement arguments in their original order.
   *
   * @param args - Replacement arguments in the same order as `args` on the original expression.
   * @returns The rebuilt expression.
   */
  withArgs(args: readonly Expr[]): Expr {
    return new CovarDerivativeOp(at(args, 0), instance(at(args, 1), NDimArray));
  }
  /**
   * Computes the covariant derivative of a field along the defining vector.
   *
   * @param field - Field to evaluate or differentiate.
   * @returns The differentiated field.
   * @see SymPy `sympy.diffgeom.diffgeom.CovarDerivativeOp.__call__`
   */
  call(field: ExprLike): Expr {
    return add(
      ...atoms(this.wrt, BaseVectorField).map((v) =>
        mul(coeff(expand(this.wrt), v), new BaseCovarDerivativeOp(v.coordSys, v.index, this.christoffel).call(field)),
      ),
    );
  }
}

/**
 * Expands the coordinates of an integral curve in powers of its parameter about the starting
 * point.
 *
 * @param v - Vector field giving the direction of differentiation or flow.
 * @param param - Parameter along the integral curve.
 * @param start - Point on the curve at parameter zero.
 * @param n - Number of series terms.
 * @param options - `coordSys` selects the chart and `coeffs` requests the separate Taylor terms.
 * @returns The coordinate Taylor polynomial, or the individual Taylor terms when `coeffs` is true.
 * @throws RangeError when the number of terms is not a nonnegative safe integer.
 * @see SymPy `sympy.diffgeom.diffgeom.intcurve_series`
 * @remarks SymPy prints the series column as `Matrix([[t + x], [y]])`.
 * @example
 * ```ts
 * import { ex } from '@symjs/symjs';
 * import { R2R, intcurveSeries } from '@symjs/symjs/diffgeom';
 *
 * const p = R2R.point([ex`x`, ex`y`]);
 * intcurveSeries(R2R.eX, ex`t`, p, 3); // => Matrix([
 * //   [t + x],
 * //   [    y]])
 * ```
 */
export function intcurveSeries(
  v: ExprLike,
  param: ExprLike,
  start: Point,
  n?: number,
  options?: { coordSys?: CoordSystem; coeffs?: false },
): Matrix;
export function intcurveSeries(
  v: ExprLike,
  param: ExprLike,
  start: Point,
  n: number,
  options: { coordSys?: CoordSystem; coeffs: true },
): Matrix[];
export function intcurveSeries(
  v: ExprLike,
  param: ExprLike,
  start: Point,
  n = 6,
  options: { coordSys?: CoordSystem; coeffs?: boolean } = {},
): Matrix | Matrix[] {
  const field = sympify(v),
    t = sympify(param);
  vector(field);
  if (!Number.isSafeInteger(n) || n < 0) throw new RangeError('Invalid series length');
  const cs = options.coordSys ?? start.coordSys;
  let terms: Expr[] = cs.baseScalars();
  const coefficients: Matrix[] = [];
  for (let i = 0; i < n; i++) {
    coefficients.push(column(terms.map((e) => mul(t.pow(i), apply(e, [start])).div(factorial(i)))));
    terms = terms.map((e) => apply(field, [e]));
  }
  return options.coeffs === true
    ? coefficients
    : column(cs.baseScalars().map((_, j) => add(...coefficients.map((c) => c.get(j, 0)))));
}
/**
 * Builds the coordinate differential equations and initial conditions for an integral curve.
 *
 * @param v - Vector field giving the direction of differentiation or flow.
 * @param param - Parameter along the integral curve.
 * @param start - Point on the curve at parameter zero.
 * @param coordSys - Coordinate system defining the basis.
 * @returns The differential equations and initial conditions, each expressed with zero right-hand side.
 * @see SymPy `sympy.diffgeom.diffgeom.intcurve_diffequ`
 * @remarks The second result contains the initial conditions, each expressed as a quantity that vanishes at parameter zero.
 * @example
 * ```ts
 * import { symbols } from '@symjs/symjs';
 * import { R2, R2R, intcurveDiffequ } from '@symjs/symjs/diffgeom';
 *
 * const [t] = symbols('t');
 * const rotation = R2.x.mul(R2.eY).sub(R2.y.mul(R2.eX));
 * const [equations, initial] = intcurveDiffequ(rotation, t, R2R.point([0, 1]));
 * initial; // => [f_0(0), f_1(0) - 1]
 * ```
 */
export function intcurveDiffequ(
  v: ExprLike,
  param: Sym,
  start: Point,
  coordSys: CoordSystem = start.coordSys,
): [Expr[], Expr[]] {
  const field = sympify(v);
  vector(field);
  const functions = coordSys.baseScalars().map((_, i) => SymFunction(`f_${i}`)(param));
  const point = new Point(coordSys, functions);
  return [
    coordSys
      .baseScalars()
      .map((f, i) => simplify(sub(diff(at(functions, i), param), apply(apply(field, [f]), [point])))),
    coordSys.baseScalars().map((f, i) => sub(at(functions, i).subs(param, 0), f.call(start))),
  ];
}

/**
 * Evaluates a covariant two-tensor on pairs of coordinate basis vectors to obtain its matrix.
 *
 * @param expr - Symbolic expression on which to operate.
 * @returns The matrix of the tensor in the coordinate basis.
 * @throws RangeError when the operand is not a covariant two-tensor.
 * @see SymPy `sympy.diffgeom.diffgeom.twoform_to_matrix`
 * @remarks SymPy prints the matrix as `Matrix([[1, 0], [0, 1]])`.
 * @example
 * ```ts
 * import { R2, TensorProduct, twoformToMatrix } from '@symjs/symjs/diffgeom';
 *
 * const metric = TensorProduct(R2.dx, R2.dx).add(TensorProduct(R2.dy, R2.dy));
 * twoformToMatrix(metric); // => Matrix([
 * //   [1, 0],
 * //   [0, 1]])
 * ```
 */
export function twoformToMatrix(expr: ExprLike): Matrix {
  const e = sympify(expr);
  if (covariantOrder(e) !== 2 || contravariantOrder(e) !== 0) throw new RangeError('Expected a two-form');
  const vs = singleSystem(e).baseVectors();
  return Matrix.fromFunction(vs.length, vs.length, (i, j) => expand(apply(e, [at(vs, j), at(vs, i)])));
}
/**
 * Computes the Christoffel symbols of the first kind for the given metric.
 *
 * @param expr - Symbolic expression on which to operate.
 * @returns The array of components in the coordinate basis of the metric.
 * @throws RangeError when the metric is not symmetric.
 * @see SymPy `sympy.diffgeom.diffgeom.metric_to_Christoffel_1st`
 * @example
 * ```ts
 * import { R2, TensorProduct, metricToChristoffel1st } from '@symjs/symjs/diffgeom';
 *
 * const metric = TensorProduct(R2.dx, R2.dx).add(TensorProduct(R2.dy, R2.dy));
 * metricToChristoffel1st(metric).get(0, 0, 0); // => 0
 * ```
 */
export function metricToChristoffel1st(expr: ExprLike): ImmutableDenseNDimArray {
  const e = sympify(expr),
    matrix = twoformToMatrix(e),
    vs = singleSystem(e).baseVectors();
  for (let i = 0; i < vs.length; i++)
    for (let j = i + 1; j < vs.length; j++) {
      if (!simplify(sub(matrix.get(i, j), matrix.get(j, i))).equals(0))
        throw new RangeError('The metric is not symmetric');
    }
  return new ImmutableDenseNDimArray(
    vs.map((vi, i) =>
      vs.map((vj, j) =>
        vs.map((vk, k) =>
          simplify(add(vk.call(matrix.get(i, j)), vj.call(matrix.get(i, k)), vi.call(matrix.get(j, k)).neg()).div(2)),
        ),
      ),
    ),
  );
}
/**
 * Computes the Christoffel symbols of the second kind of the Levi-Civita connection.
 *
 * @param expr - Symbolic expression on which to operate.
 * @returns The array of components in the coordinate basis of the metric.
 * @see SymPy `sympy.diffgeom.diffgeom.metric_to_Christoffel_2nd`
 * @example
 * ```ts
 * import { R2, TensorProduct, metricToChristoffel2nd } from '@symjs/symjs/diffgeom';
 *
 * const metric = TensorProduct(R2.dx, R2.dx).add(TensorProduct(R2.dy, R2.dy));
 * metricToChristoffel2nd(metric).get(0, 0, 0); // => 0
 * ```
 */
export function metricToChristoffel2nd(expr: ExprLike): ImmutableDenseNDimArray {
  const e = sympify(expr),
    ch = metricToChristoffel1st(e),
    matrix = twoformToMatrix(e).inv(),
    vs = singleSystem(e).baseVectors();
  return new ImmutableDenseNDimArray(
    vs.map((_, i) =>
      vs.map((_, j) => vs.map((_, k) => simplify(add(...vs.map((_, l) => mul(matrix.get(i, l), ch.get(l, j, k))))))),
    ),
  );
}
/**
 * Computes the Riemann curvature components of a metric in its coordinate basis.
 *
 * @param expr - Symbolic expression on which to operate.
 * @returns The array of components in the coordinate basis of the metric.
 * @see SymPy `sympy.diffgeom.diffgeom.metric_to_Riemann_components`
 * @example
 * ```ts
 * import { R2, TensorProduct, metricToRiemannComponents } from '@symjs/symjs/diffgeom';
 *
 * const metric = TensorProduct(R2.dx, R2.dx).add(TensorProduct(R2.dy, R2.dy));
 * metricToRiemannComponents(metric).get(0, 0, 0, 0); // => 0
 * ```
 */
export function metricToRiemannComponents(expr: ExprLike): ImmutableDenseNDimArray {
  const e = sympify(expr),
    ch = metricToChristoffel2nd(e),
    vs = singleSystem(e).baseVectors();
  return new ImmutableDenseNDimArray(
    vs.map((_, r) =>
      vs.map((_, s) =>
        vs.map((vm, m) =>
          vs.map((vn, n) =>
            simplify(
              add(
                vm.call(ch.get(r, s, n)),
                vn.call(ch.get(r, s, m)).neg(),
                ...vs.map((_, l) => sub(mul(ch.get(r, l, m), ch.get(l, s, n)), mul(ch.get(r, l, n), ch.get(l, s, m)))),
              ),
            ),
          ),
        ),
      ),
    ),
  );
}
/**
 * Contracts the curvature of a metric to obtain its Ricci tensor components.
 *
 * @param expr - Symbolic expression on which to operate.
 * @returns The array of components in the coordinate basis of the metric.
 * @see SymPy `sympy.diffgeom.diffgeom.metric_to_Ricci_components`
 * @example
 * ```ts
 * import { R2, TensorProduct, metricToRicciComponents } from '@symjs/symjs/diffgeom';
 *
 * const metric = TensorProduct(R2.dx, R2.dx).add(TensorProduct(R2.dy, R2.dy));
 * metricToRicciComponents(metric).get(0, 0); // => 0
 * ```
 */
export function metricToRicciComponents(expr: ExprLike): ImmutableDenseNDimArray {
  const e = sympify(expr),
    riemann = metricToRiemannComponents(e),
    vs = singleSystem(e).baseVectors();
  return new ImmutableDenseNDimArray(
    vs.map((_, i) => vs.map((_, j) => simplify(add(...vs.map((_, k) => riemann.get(k, i, k, j)))))),
  );
}
