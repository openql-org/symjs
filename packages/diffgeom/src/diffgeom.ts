// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/** Differential geometry on coordinate patches (SymPy 1.14 diffgeom.py). */
import {
  Add, Mul, Pow, Expr, ExtensionExpr, Sym, Dummy, S, Matrix,
  ImmutableDenseNDimArray, NDimArray, Lambda, Tuple, NotImplementedError,
  add, mul, sub, diff, sympify, xreplace, simplify, expand, solve,
  factorial, SymFunction, coeff, rcall,
} from '@symjs/symjs';
import type { ExprLike } from '@symjs/symjs';

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
function column(values: readonly ExprLike[]): Matrix { return Matrix.of(values.map(v => [v])); }
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
  return [...new Map([...atoms(e, BaseScalarField), ...atoms(e, BaseVectorField)].map(v => [v.coordSys.key, v.coordSys])).values()];
}
function singleSystem(e: Expr): CoordSystem {
  const cs = systems(e);
  if (cs.length !== 1) throw new RangeError('The field must concern exactly one coordinate system');
  return at(cs, 0);
}

export class Manifold extends ExtensionExpr {
  readonly patches: Patch[] = [];
  constructor(name: string, readonly dim: number) {
    super(name, [sympify(dim)]);
    if (!Number.isSafeInteger(dim) || dim < 0) throw new RangeError('Invalid manifold dimension');
  }
  protected override computeKey(): string { return `Manifold:${this.name}:${this.dim}`; }
  withArgs(args: readonly Expr[]): Expr { return new Manifold(this.name, indexValue(at(args, 0))); }
  override printStr(): string { return this.name; }
  override printLatex(): string { return this.name; }
}

export class Patch extends ExtensionExpr {
  readonly coordSystems: CoordSystem[] = [];
  constructor(name: string, readonly manifold: Manifold) {
    super(name, [manifold]);
    manifold.patches.push(this);
  }
  get dim(): number { return this.manifold.dim; }
  protected override computeKey(): string { return `Patch:${this.name}:${this.manifold.key}`; }
  withArgs(args: readonly Expr[]): Expr { return new Patch(this.name, instance(at(args, 0), Manifold)); }
  override printStr(): string { return this.name; }
  override printLatex(): string { return this.name; }
}

export type CoordinateRelation = readonly [readonly Sym[], readonly ExprLike[]] | Lambda;
export type CoordinateRelations = ReadonlyMap<readonly [string, string], CoordinateRelation>;

/** A coordinate transformation with a Matrix-valued body. */
class Transformation {
  constructor(readonly signature: readonly Sym[], readonly expr: Matrix) {}
  call(...values: ExprLike[]): Matrix {
    const pairs = replacements(this.signature, values.map(sympify));
    return this.expr.map(e => xreplace(e, pairs));
  }
  toString(): string {
    const signature = this.signature.length === 1 ? String(at(this.signature, 0)) : `(${this.signature.join(', ')})`;
    return `Lambda(${signature}, ${String(this.expr)})`;
  }
}

export class CoordSystem extends ExtensionExpr {
  readonly coordinateNames: readonly Sym[];
  readonly relations: Map<readonly [string, string], readonly [readonly Sym[], readonly Expr[]]>;
  readonly transforms = new Map<CoordSystem, readonly [readonly Sym[], readonly Expr[]]>();
  constructor(name: string, readonly patch: Patch, symbols?: readonly (Sym | string)[], relations: CoordinateRelations = new Map()) {
    const names = symbols?.map(s => typeof s === 'string' ? new Sym(s, { real: true }) : new Sym(s.name, s.assumptions))
      ?? Array.from({ length: patch.dim }, (_, i) => new Sym(`${name}_${i}`, { real: true }));
    const rel = new Map<readonly [string, string], readonly [readonly Sym[], readonly Expr[]]>();
    for (const [key, value] of [...relations].sort(([a], [b]) => a.join('\0').localeCompare(b.join('\0')))) {
      const [signature, expr] = value instanceof Lambda
        ? [value.variables.map(v => instance(v, Sym)), instance(value.expr, Tuple).args] : value;
      rel.set(key, [signature, expr.map(sympify)]);
    }
    super(name, [patch, ...names, ...[...rel].flatMap(([[a, b], [s, e]]) => [new Sym(a), new Sym(b), new Tuple(s), new Tuple(e)])]);
    this.coordinateNames = names;
    this.relations = rel;
    patch.coordSystems.push(this);
  }
  get manifold(): Manifold { return this.patch.manifold; }
  get dim(): number { return this.patch.dim; }
  get symbols(): CoordinateSymbol[] { return this.coordinateNames.map((_, i) => new CoordinateSymbol(this, i)); }
  protected override computeKey(): string { return `CoordSystem:${this.name}(${this.args.map(a => a.key).join(',')})`; }
  withArgs(args: readonly Expr[]): Expr {
    const end = 1 + this.coordinateNames.length;
    const relations = new Map<readonly [string, string], CoordinateRelation>();
    for (let i = end; i < args.length; i += 4) {
      relations.set([instance(at(args, i), Sym).name, instance(at(args, i + 1), Sym).name],
        [instance(at(args, i + 2), Tuple).args.map(s => instance(s, Sym)), instance(at(args, i + 3), Tuple).args]);
    }
    return new CoordSystem(this.name, instance(at(args, 0), Patch), args.slice(1, end).map(a => instance(a, Sym)), relations);
  }
  override printStr(): string { return this.name; }
  override printLatex(): string { return this.name; }
  transformation(to: CoordSystem): Transformation {
    return new Transformation(this.coordinateNames, this.transform(to, this.coordinateNames));
  }
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
      const edges = relations.filter(([[a]]) => a === current.name)
        .concat(relations.filter(([[a, b]]) => b === current.name && !relations.some(([[c, d]]) => c === b && d === a)));
      for (const [[a, b], [xs, ys]] of edges) {
        const next = a === current.name ? b : a;
        if (seen.has(next)) continue;
        const result = a === current.name
          ? ys.map(y => xreplace(y, replacements(xs, current.values)))
          : inverse(xs, ys, current.values);
        if (next === to.name) return column(result);
        seen.add(next);
        queue.push({ name: next, values: result });
      }
    }
    throw new RangeError('Two coordinate systems are not connected');
  }
  connectTo(to: CoordSystem, from: readonly Sym[], expressions: readonly ExprLike[], options: { inverse?: boolean; fillInGaps?: boolean } = {}): void {
    const exprs = expressions.map(sympify);
    replacements(from, exprs);
    const back = options.inverse === false ? [] : inverse(from, exprs, to.coordinateNames);
    this.transforms.set(to, [from, exprs]);
    if (options.inverse !== false) to.transforms.set(this, [to.coordinateNames, back]);
    // Connected paths are composed on demand, including when fillInGaps is requested.
  }
  coordTupleTransformTo(to: CoordSystem, values: readonly ExprLike[] | Matrix): Matrix { return this.transform(to, values); }
  jacobian(to: CoordSystem, values: readonly ExprLike[] | Matrix = this.symbols): Matrix {
    const xs = this.symbols;
    const transformed = this.transform(to);
    const pairs = replacements(xs, coordinates(values));
    return Matrix.fromFunction(transformed.rows, xs.length, (i, j) => xreplace(diff(transformed.get(i, 0), at(xs, j)), pairs));
  }
  jacobianMatrix(to: CoordSystem, values?: readonly ExprLike[] | Matrix): Matrix { return this.jacobian(to, values); }
  jacobianDeterminant(to: CoordSystem, values?: readonly ExprLike[] | Matrix): Expr { return this.jacobian(to, values).det(); }
  point(values: readonly ExprLike[] | Matrix): Point { return new Point(this, values); }
  pointToCoords(point: Point): Matrix { return point.coords(this); }
  baseScalar(index: number): BaseScalarField { return new BaseScalarField(this, index); }
  coordFunction(index: number): BaseScalarField { return this.baseScalar(index); }
  baseScalars(): BaseScalarField[] { return this.coordinateNames.map((_, i) => this.baseScalar(i)); }
  coordFunctions(): BaseScalarField[] { return this.baseScalars(); }
  baseVector(index: number): BaseVectorField { return new BaseVectorField(this, index); }
  baseVectors(): BaseVectorField[] { return this.coordinateNames.map((_, i) => this.baseVector(i)); }
  baseOneform(index: number): Expr { return Differential(this.baseScalar(index)); }
  baseOneforms(): Expr[] { return this.coordinateNames.map((_, i) => this.baseOneform(i)); }
}

/** Eliminate one source coordinate at a time, retaining every inverse branch. */
function inverse(xs: readonly Sym[], expressions: readonly Expr[], targets: readonly Expr[]): Expr[] {
  const variables = xs.map(x => new Dummy(x.name, x.assumptions));
  const renamed = replacements(xs, variables);
  let branches: { equations: Expr[]; values: Expr[] }[] = [{ equations: expressions.map((e, i) => sub(xreplace(e, renamed), at(targets, i))), values: [] }];
  for (const x of variables) {
    const next: typeof branches = [];
    for (const branch of branches) {
      const equation = branch.equations.find(e => e.has(x));
      if (equation === undefined) throw new NotImplementedError('Inverse relation is underdetermined');
      for (const solution of solve(equation, x)) {
        const pair: [Expr, Expr][] = [[x, solution]];
        const values = [...branch.values.map(v => xreplace(v, pair)), solution];
        next.push({ equations: branch.equations.filter(e => e !== equation).map(e => simplify(xreplace(e, pair))), values });
      }
    }
    branches = next;
  }
  branches = branches.filter(b => b.equations.every(e => simplify(e).equals(0)));
  if (branches.length === 0) throw new NotImplementedError('Cannot solve inverse relation');
  if (branches.length > 1) throw new RangeError('Obtained multiple inverse relations');
  return at(branches, 0).values;
}

export class CoordinateSymbol extends Sym {
  constructor(readonly coordSys: CoordSystem, readonly index: number) {
    const symbol = at(coordSys.coordinateNames, index);
    super(symbol.name, symbol.assumptions);
  }
  protected override computeKey(): string { return `CoordinateSymbol:${this.coordSys.key}:${this.index}`; }
  override get sortClass(): string { return 'CoordinateSymbol'; }
  override rewrite(to: string | CoordSystem): Expr {
    return to instanceof CoordSystem ? to.transform(this.coordSys).get(this.index, 0) : super.rewrite(to);
  }
}

export class Point extends ExtensionExpr {
  readonly coordinates: readonly Expr[];
  constructor(readonly coordSys: CoordSystem, values: readonly ExprLike[] | Matrix) {
    const coords = coordinates(values);
    replacements(coordSys.coordinateNames, coords);
    super('Point', [coordSys, ...coords]);
    this.coordinates = coords;
  }
  get patch(): Patch { return this.coordSys.patch; }
  get manifold(): Manifold { return this.coordSys.manifold; }
  get dim(): number { return this.manifold.dim; }
  coords(to: CoordSystem = this.coordSys): Matrix { return this.coordSys.transform(to, this.coordinates); }
  withArgs(args: readonly Expr[]): Expr { return new Point(instance(at(args, 0), CoordSystem), args.slice(1)); }
  override freeSymbolsSelf(): ReadonlySet<Expr> { return column(this.coordinates).freeSymbols(); }
  override printStr(): string { return `Point(${String(this.coordSys)}, ${String(column(this.coordinates))})`; }
}

export class BaseScalarField extends ExtensionExpr {
  constructor(readonly coordSys: CoordSystem, readonly index: number) {
    super('BaseScalarField', [coordSys, sympify(index)]);
    at(coordSys.coordinateNames, index);
  }
  get patch(): Patch { return this.coordSys.patch; }
  get manifold(): Manifold { return this.coordSys.manifold; }
  get dim(): number { return this.manifold.dim; }
  withArgs(args: readonly Expr[]): Expr { return new BaseScalarField(instance(at(args, 0), CoordSystem), indexValue(at(args, 1))); }
  override printStr(print: (e: Expr) => string): string { return print(at(this.coordSys.coordinateNames, this.index)); }
  override printLatex(print: (e: Expr) => string): string { return `\\mathbf{${print(at(this.coordSys.coordinateNames, this.index))}}`; }
  override freeSymbolsSelf(): ReadonlySet<Expr> { return new Set(); }
  override diffSelf(): Expr { return S.Zero; }
  call(...args: (ExprLike | null)[]): Expr {
    const point = args[0];
    return args.length === 1 && point instanceof Point ? simplify(point.coords(this.coordSys).get(this.index, 0)) : this;
  }
}

export class BaseVectorField extends ExtensionExpr {
  constructor(readonly coordSys: CoordSystem, readonly index: number) {
    super('BaseVectorField', [coordSys, sympify(index)]);
    at(coordSys.coordinateNames, index);
  }
  get patch(): Patch { return this.coordSys.patch; }
  get manifold(): Manifold { return this.coordSys.manifold; }
  get dim(): number { return this.manifold.dim; }
  override get isCommutative(): boolean { return false; }
  withArgs(args: readonly Expr[]): Expr { return new BaseVectorField(instance(at(args, 0), CoordSystem), indexValue(at(args, 1))); }
  override printStr(print: (e: Expr) => string): string { return `e_${print(at(this.coordSys.coordinateNames, this.index))}`; }
  override printLatex(print: (e: Expr) => string): string { return `\\partial_{${print(at(this.coordSys.coordinateNames, this.index))}}`; }
  call(field: ExprLike | null = null): Expr {
    if (field === null) return this;
    const f = sympify(field);
    if (covariantOrder(f) || contravariantOrder(f)) throw new RangeError('Only scalar fields can be supplied to vector fields');
    const scalars = atoms(f, BaseScalarField);
    const dummies = scalars.map((_, i) => new Dummy(`xi${i}`));
    const body = xreplace(f, replacements(scalars, dummies));
    const result = add(...scalars.map((scalar, i) => {
      const jacobian = this.coordSys.jacobian(scalar.coordSys, this.coordSys.baseScalars());
      return mul(xreplace(diff(body, at(dummies, i)), replacements(dummies, scalars)), jacobian.get(scalar.index, this.index));
    }));
    return result;
  }
}

function order(e: Expr, contra: boolean, strict: boolean): number {
  if (e instanceof Add || e instanceof Mul) {
    const orders = e.args.map(a => order(a, contra, false));
    if (e instanceof Add) {
      if (new Set(orders).size !== 1) throw new RangeError('Fields of varying order');
      return at(orders, 0);
    }
    const nonzero = orders.filter(o => o !== 0);
    if (nonzero.length > 1) throw new RangeError('Multiplication of tensor fields requires TensorProduct');
    return nonzero[0] ?? 0;
  }
  if (e instanceof Pow) {
    // SymPy 1.14 checks covariant_order twice and misses powers of vectors.
    if ([e.base, e.exp].some(a => covariantOrder(a) !== 0 || contravariantOrder(a) !== 0)) throw new RangeError('A tensor field cannot be raised to a power');
    return 0;
  }
  if (e instanceof TensorProductNode) return e.args.reduce((sum, a) => sum + order(a, contra, false), 0);
  if (e instanceof DifferentialNode) return contra ? 0 : covariantOrder(e.formField) + 1;
  if (e instanceof BaseVectorField || e instanceof CommutatorNode) return contra ? 1 : 0;
  if (e instanceof LieDerivativeNode) return order(e.expr, contra, false);
  return !strict || atoms(e, BaseScalarField).length > 0 ? 0 : -1;
}
export function contravariantOrder(expr: ExprLike, strict = false): number { return order(sympify(expr), true, strict); }
export function covariantOrder(expr: ExprLike, strict = false): number { return order(sympify(expr), false, strict); }
function vector(e: Expr): void {
  if (contravariantOrder(e) !== 1 || covariantOrder(e) !== 0) throw new RangeError('Expected a vector field');
}
function apply(e: Expr, args: readonly (ExprLike | null)[]): Expr { return rcall(e, ...args); }

class CommutatorNode extends ExtensionExpr {
  constructor(readonly v1: Expr, readonly v2: Expr) { super('Commutator', [v1, v2]); }
  override get isCommutative(): boolean { return false; }
  withArgs(args: readonly Expr[]): Expr { return Commutator(at(args, 0), at(args, 1)); }
  call(field: ExprLike): Expr { return sub(apply(this.v1, [apply(this.v2, [field])]), apply(this.v2, [apply(this.v1, [field])])); }
}
export function Commutator(v1: ExprLike, v2: ExprLike): Expr {
  const a = sympify(v1), b = sympify(v2);
  vector(a); vector(b);
  if (a.equals(b)) return S.Zero;
  if (systems(add(a, b)).length !== 1) return new CommutatorNode(a, b);
  return expand(add(...atoms(a, BaseVectorField).flatMap(x => atoms(b, BaseVectorField).map(y => {
    const c = coeff(expand(a), x), d = coeff(expand(b), y);
    return sub(mul(c, x.call(d), y), mul(d, y.call(c), x));
  }))));
}

class DifferentialNode extends ExtensionExpr {
  constructor(readonly formField: Expr) { super('Differential', [formField]); }
  override get isCommutative(): boolean { return false; }
  withArgs(args: readonly Expr[]): Expr { return Differential(at(args, 0)); }
  override printStr(print: (e: Expr) => string): string {
    return this.formField instanceof BaseScalarField ? `d${print(this.formField)}` : `d(${print(this.formField)})`;
  }
  override printLatex(print: (e: Expr) => string): string {
    return this.formField instanceof BaseScalarField ? `\\operatorname{d}${print(this.formField)}` : `\\operatorname{d}\\left(${print(this.formField)}\\right)`;
  }
  call(...fields: (ExprLike | null)[]): Expr {
    const degree = covariantOrder(this);
    if (fields.length > degree) throw new RangeError('Too many arguments to Differential');
    const vs = fields.map(f => f === null ? null : sympify(f));
    vs.forEach(v => { if (v !== null) vector(v); });
    if (vs.length === 0 || vs.every(v => v === null)) return this;
    if (degree === 1) return apply(instance(at(vs, 0), Expr), [this.formField]);
    if (vs.length !== degree || vs.some(v => v === null)) throw new NotImplementedError('Partial contraction of an exterior derivative of higher degree');
    const vectors = vs.map(v => instance(v, Expr));
    return add(...vectors.flatMap((v, i) => {
      const terms = [mul((-1) ** i, apply(v, [apply(this.formField, vectors.filter((_, k) => k !== i))]))];
      for (let j = i + 1; j < vectors.length; j++) {
        const bracket = Commutator(v, at(vectors, j));
        if (!bracket.equals(0)) terms.push(mul((-1) ** (i + j), apply(this.formField, [bracket, ...vectors.filter((_, k) => k !== i && k !== j)])));
      }
      return terms;
    }));
  }
}
export function Differential(form: ExprLike): Expr {
  const f = sympify(form);
  if (contravariantOrder(f)) throw new RangeError('Differential requires a form field');
  return f instanceof DifferentialNode ? S.Zero : new DifferentialNode(f);
}

class TensorProductNode extends ExtensionExpr {
  constructor(args: readonly Expr[], readonly alternating = false) { super(alternating ? 'WedgeProduct' : 'TensorProduct', args); }
  override get isCommutative(): boolean { return false; }
  withArgs(args: readonly Expr[]): Expr { return product(args, this.alternating); }
  call(...fields: (ExprLike | null)[]): Expr {
    const orders = this.args.map(a => covariantOrder(a) + contravariantOrder(a));
    const total = orders.reduce((a, b) => a + b, 0);
    if (fields.length > total) throw new RangeError('Too many arguments to tensor');
    const padded = [...fields, ...Array.from({ length: total - fields.length }, () => null)];
    const contract = (values: readonly (ExprLike | null)[]): Expr => {
      let start = 0;
      return TensorProduct(...this.args.map((a, i) => {
        const end = start + at(orders, i), result = apply(a, values.slice(start, end));
        start = end;
        return result;
      }));
    };
    if (!this.alternating) return contract(padded);
    const denominator = mul(...orders.map(n => factorial(n)));
    function permute(indices: number[]): Expr {
      if (indices.length === total) {
        let inversions = 0;
        indices.forEach((v, i) => indices.slice(i + 1).forEach(w => { if (v > w) inversions++; }));
        return mul((-1) ** inversions, contract(indices.map(i => at(padded, i))));
      }
      return add(...padded.flatMap((_, i) => indices.includes(i) ? [] : [permute([...indices, i])]));
    }
    return expand(permute([]).div(denominator));
  }
}
function product(args: readonly ExprLike[], alternating: boolean): Expr {
  const scalar: Expr[] = [], tensors: Expr[] = [];
  args.map(sympify).forEach(a => (covariantOrder(a) + contravariantOrder(a) === 0 ? scalar : tensors).push(a));
  return mul(...scalar, ...(tensors.length < 2 ? tensors : [new TensorProductNode(tensors, alternating)]));
}
export function TensorProduct(...args: ExprLike[]): Expr { return product(args, false); }
export function WedgeProduct(...args: ExprLike[]): Expr { return product(args, true); }

class LieDerivativeNode extends ExtensionExpr {
  constructor(readonly vField: Expr, readonly expr: Expr) { super('LieDerivative', [vField, expr]); }
  override get isCommutative(): boolean { return false; }
  withArgs(args: readonly Expr[]): Expr { return LieDerivative(at(args, 0), at(args, 1)); }
  call(...fields: ExprLike[]): Expr {
    const vs = fields.map(sympify);
    vs.forEach(vector);
    // SymPy 1.14 multiplies the argument vectors in the correction term;
    // the tensor must instead be evaluated on the replaced argument list.
    return sub(apply(this.vField, [apply(this.expr, vs)]), add(...vs.map((v, i) => {
      const bracket = Commutator(this.vField, v);
      return bracket.equals(0) ? S.Zero : apply(this.expr, vs.map((w, j) => i === j ? bracket : w));
    })));
  }
}
export function LieDerivative(v: ExprLike, expr: ExprLike): Expr {
  const field = sympify(v), e = sympify(expr);
  vector(field);
  if (covariantOrder(e) > 0) return new LieDerivativeNode(field, e);
  return contravariantOrder(e) > 0 ? Commutator(field, e) : apply(field, [e]);
}

export function vectorsInBasis(expr: ExprLike, to: CoordSystem): Expr {
  const e = sympify(expr);
  return xreplace(e, atoms(e, BaseVectorField).map((v): [Expr, Expr] => {
    const jac = v.coordSys.jacobian(to, v.coordSys.baseScalars());
    return [v, add(...to.baseVectors().map((b, j) => mul(jac.get(j, v.index), b)))];
  }));
}

export class BaseCovarDerivativeOp extends ExtensionExpr {
  readonly christoffel: NDimArray;
  constructor(readonly coordSys: CoordSystem, readonly index: number, christoffel: NDimArray | readonly (readonly (readonly ExprLike[])[])[]) {
    const ch = christoffel instanceof NDimArray ? christoffel : new ImmutableDenseNDimArray(christoffel);
    super('BaseCovarDerivativeOp', [coordSys, sympify(index), ch]);
    at(coordSys.coordinateNames, index);
    this.christoffel = ch;
  }
  withArgs(args: readonly Expr[]): Expr { return new BaseCovarDerivativeOp(instance(at(args, 0), CoordSystem), indexValue(at(args, 1)), instance(at(args, 2), NDimArray)); }
  call(field: ExprLike): Expr {
    const f = vectorsInBasis(field, this.coordSys), basis = this.coordSys.baseVector(this.index);
    const derive = (e: Expr): Expr => {
      if (e instanceof Add) return add(...e.args.map(derive));
      if (e instanceof Mul) return add(...e.args.map((a, i) => mul(...e.args.map((b, j) => i === j ? derive(a) : b))));
      if (e instanceof TensorProductNode) return add(...e.args.map((a, i) => product(e.args.map((b, j) => i === j ? derive(a) : b), e.alternating)));
      if (e instanceof BaseVectorField) return add(...this.coordSys.baseVectors().map((b, k) => mul(this.christoffel.get(k, this.index, e.index), b)));
      if (covariantOrder(e)) throw new NotImplementedError('Covariant derivatives of forms');
      return basis.call(e);
    };
    return expand(derive(f));
  }
}
export class CovarDerivativeOp extends ExtensionExpr {
  readonly wrt: Expr;
  readonly christoffel: NDimArray;
  constructor(wrt: ExprLike, christoffel: NDimArray | readonly (readonly (readonly ExprLike[])[])[]) {
    const v = sympify(wrt);
    vector(v);
    if (systems(v).length > 1) throw new NotImplementedError('Covariant derivative with mixed coordinate systems');
    const ch = christoffel instanceof NDimArray ? christoffel : new ImmutableDenseNDimArray(christoffel);
    super('CovarDerivativeOp', [v, ch]);
    this.wrt = v; this.christoffel = ch;
  }
  withArgs(args: readonly Expr[]): Expr { return new CovarDerivativeOp(at(args, 0), instance(at(args, 1), NDimArray)); }
  call(field: ExprLike): Expr {
    return add(...atoms(this.wrt, BaseVectorField).map(v => mul(coeff(expand(this.wrt), v), new BaseCovarDerivativeOp(v.coordSys, v.index, this.christoffel).call(field))));
  }
}

export function intcurveSeries(v: ExprLike, param: ExprLike, start: Point, n?: number, options?: { coordSys?: CoordSystem; coeffs?: false }): Matrix;
export function intcurveSeries(v: ExprLike, param: ExprLike, start: Point, n: number, options: { coordSys?: CoordSystem; coeffs: true }): Matrix[];
export function intcurveSeries(v: ExprLike, param: ExprLike, start: Point, n = 6, options: { coordSys?: CoordSystem; coeffs?: boolean } = {}): Matrix | Matrix[] {
  const field = sympify(v), t = sympify(param);
  vector(field);
  if (!Number.isSafeInteger(n) || n < 0) throw new RangeError('Invalid series length');
  const cs = options.coordSys ?? start.coordSys;
  let terms: Expr[] = cs.baseScalars();
  const coefficients: Matrix[] = [];
  for (let i = 0; i < n; i++) {
    coefficients.push(column(terms.map(e => mul(t.pow(i), apply(e, [start])).div(factorial(i)))));
    terms = terms.map(e => apply(field, [e]));
  }
  return options.coeffs === true ? coefficients : column(cs.baseScalars().map((_, j) => add(...coefficients.map(c => c.get(j, 0)))));
}
export function intcurveDiffequ(v: ExprLike, param: Sym, start: Point, coordSys: CoordSystem = start.coordSys): [Expr[], Expr[]] {
  const field = sympify(v);
  vector(field);
  const functions = coordSys.baseScalars().map((_, i) => SymFunction(`f_${i}`)(param));
  const point = new Point(coordSys, functions);
  return [coordSys.baseScalars().map((f, i) => simplify(sub(diff(at(functions, i), param), apply(apply(field, [f]), [point])))),
    coordSys.baseScalars().map((f, i) => sub(at(functions, i).subs(param, 0), f.call(start)))];
}

export function twoformToMatrix(expr: ExprLike): Matrix {
  const e = sympify(expr);
  if (covariantOrder(e) !== 2 || contravariantOrder(e) !== 0) throw new RangeError('Expected a two-form');
  const vs = singleSystem(e).baseVectors();
  return Matrix.fromFunction(vs.length, vs.length, (i, j) => expand(apply(e, [at(vs, j), at(vs, i)])));
}
export function metricToChristoffel1st(expr: ExprLike): ImmutableDenseNDimArray {
  const e = sympify(expr), matrix = twoformToMatrix(e), vs = singleSystem(e).baseVectors();
  for (let i = 0; i < vs.length; i++) for (let j = i + 1; j < vs.length; j++) {
    if (!simplify(sub(matrix.get(i, j), matrix.get(j, i))).equals(0)) throw new RangeError('The metric is not symmetric');
  }
  return new ImmutableDenseNDimArray(vs.map((vi, i) => vs.map((vj, j) => vs.map((vk, k) => simplify(add(vk.call(matrix.get(i, j)), vj.call(matrix.get(i, k)), vi.call(matrix.get(j, k)).neg()).div(2))))));
}
export function metricToChristoffel2nd(expr: ExprLike): ImmutableDenseNDimArray {
  const e = sympify(expr), ch = metricToChristoffel1st(e), matrix = twoformToMatrix(e).inv(), vs = singleSystem(e).baseVectors();
  return new ImmutableDenseNDimArray(vs.map((_, i) => vs.map((_, j) => vs.map((_, k) => simplify(add(...vs.map((_, l) => mul(matrix.get(i, l), ch.get(l, j, k)))))))));
}
export function metricToRiemannComponents(expr: ExprLike): ImmutableDenseNDimArray {
  const e = sympify(expr), ch = metricToChristoffel2nd(e), vs = singleSystem(e).baseVectors();
  return new ImmutableDenseNDimArray(vs.map((_, r) => vs.map((_, s) => vs.map((vm, m) => vs.map((vn, n) => simplify(add(
    vm.call(ch.get(r, s, n)), vn.call(ch.get(r, s, m)).neg(),
    ...vs.map((_, l) => sub(mul(ch.get(r, l, m), ch.get(l, s, n)), mul(ch.get(r, l, n), ch.get(l, s, m)))),
  )))))));
}
export function metricToRicciComponents(expr: ExprLike): ImmutableDenseNDimArray {
  const e = sympify(expr), riemann = metricToRiemannComponents(e), vs = singleSystem(e).baseVectors();
  return new ImmutableDenseNDimArray(vs.map((_, i) => vs.map((_, j) => simplify(add(...vs.map((_, k) => riemann.get(k, i, k, j)))))));
}
