// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Algorithms from SymPy 1.14 combinatorics/perm_groups.py (Schreier lemma), BSD-3-Clause.
import type { Expr } from '../core/nodes';
import { ExtensionExpr } from '../core/nodes';
import { at, cast, getOrThrow } from '../core/guard';
import { callableClass } from '../core/callable';
import { Permutation } from './permutations';

interface Chain { point: number; transversal: Map<number, Permutation>; stabilizer: readonly Permutation[]; next: Chain | undefined; }
const identity = (degree: number): Permutation => new Permutation(Array.from({ length: degree }, (_, i) => i));
const distinct = (generators: readonly Permutation[]): Permutation[] => [...new Map(generators.filter((g) => !g.isIdentity).map((g) => [g.key, g])).values()];

function orbitTransversal(generators: readonly Permutation[], degree: number, point: number): Map<number, Permutation> {
  const trans = new Map([[point, identity(degree)]]);
  const queue = [point];
  for (let i = 0; i < queue.length; i++) {
    const beta = at(queue, i);
    for (const g of generators) {
      const gamma = at(g.arrayForm, beta);
      if (!trans.has(gamma)) { trans.set(gamma, getOrThrow(trans, beta).mul(g)); queue.push(gamma); }
    }
  }
  return trans;
}
function schreier(generators: readonly Permutation[], trans: ReadonlyMap<number, Permutation>): Permutation[] {
  const out: Permutation[] = [];
  for (const [beta, t] of trans) for (const g of generators) {
    const gamma = at(g.arrayForm, beta);
    out.push(t.mul(g).mul(getOrThrow(trans, gamma).inverse()));
  }
  return distinct(out);
}
function buildChain(generators: readonly Permutation[], degree: number): Chain | undefined {
  const point = Array.from({ length: degree }, (_, i) => i).find((i) => generators.some((g) => at(g.arrayForm, i) !== i));
  if (point === undefined) return undefined;
  const transversal = orbitTransversal(generators, degree, point);
  const stabilizer = schreier(generators, transversal);
  return { point, transversal, stabilizer, next: buildChain(stabilizer, degree) };
}
function sift(p: Permutation, chain: Chain | undefined): boolean {
  if (!chain) return p.isIdentity;
  const t = chain.transversal.get(at(p.arrayForm, chain.point));
  return t !== undefined && sift(p.mul(t.inverse()), chain.next);
}
function* enumerate(chain: Chain | undefined, degree: number): Generator<Permutation> {
  if (!chain) { yield identity(degree); return; }
  for (const h of enumerate(chain.next, degree)) for (const t of chain.transversal.values()) yield h.mul(t);
}
const isPermutationList = (x: Permutation | readonly Permutation[] | undefined): x is readonly Permutation[] => Array.isArray(x);

/** Finite permutation group with a deterministic stabilizer chain. */
export class PermutationGroupNode extends ExtensionExpr {
  readonly degree: number;
  readonly generators: readonly Permutation[];
  private chain: Chain | undefined;
  private initialized = false;
  constructor(...input: Permutation[] | [readonly Permutation[]]) {
    const raw = isPermutationList(input[0]) ? input[0] : input.map((p) => cast(p, Permutation));
    const degree = Math.max(0, ...raw.map((p) => p.size));
    const gs = [...new Map(raw.map((p) => { const g = p.resize(degree); return [g.key, g] as const; })).values()];
    super('PermutationGroup', gs);
    this.generators = gs.length ? gs : [identity(degree)]; this.degree = degree;
  }
  withArgs(args: readonly Expr[]): Expr { return new PermutationGroupNode(args.map((a) => cast(a, Permutation))); }
  private getChain(): Chain | undefined {
    if (!this.initialized) { this.chain = buildChain(distinct(this.generators), this.degree); this.initialized = true; }
    return this.chain;
  }
  /** Exact order: the product of orbit sizes along the stabilizer chain. */
  order(): bigint {
    let order = 1n;
    for (let c = this.getChain(); c; c = c.next) order *= BigInt(c.transversal.size);
    return order;
  }
  contains(permutation: Permutation, strict = true): boolean {
    if (permutation.size > this.degree || (strict && permutation.size !== this.degree)) return false;
    return sift(permutation.resize(this.degree), this.getChain());
  }
  get isTrivial(): boolean { return this.generators.every((g) => g.isIdentity); }
  get isAbelian(): boolean { return this.generators.every((g) => this.generators.every((h) => g.mul(h).equals(h.mul(g)))); }
  get isSymmetric(): boolean {
    let factorial = 1n; for (let i = 2; i <= this.degree; i++) factorial *= BigInt(i);
    return this.order() === factorial;
  }
  get isAlternating(): boolean {
    if (this.degree < 3) return this.isTrivial;
    let factorial = 1n; for (let i = 2; i <= this.degree; i++) factorial *= BigInt(i);
    return this.generators.every((g) => g.signature() === 1) && this.order() * 2n === factorial;
  }
  private checkPoint(point: number): void {
    if (!Number.isInteger(point) || point < 0 || point >= this.degree) throw new RangeError('point outside the permutation domain');
  }
  orbit(point: number): Set<number> { this.checkPoint(point); return new Set(orbitTransversal(this.generators, this.degree, point).keys()); }
  orbits(): Set<number>[] {
    const remaining = new Set(Array.from({ length: this.degree }, (_, i) => i)); const out: Set<number>[] = [];
    for (const p of remaining) { const orbit = this.orbit(p); out.push(orbit); for (const q of orbit) remaining.delete(q); }
    return out;
  }
  isTransitive(strict = true): boolean {
    if (strict) return this.degree === 0 || this.orbit(0).size === this.degree;
    return this.orbits().filter((o) => o.size > 1).length <= 1;
  }
  stabilizer(point: number): PermutationGroupNode {
    this.checkPoint(point);
    const gs = schreier(this.generators, orbitTransversal(this.generators, this.degree, point));
    return new PermutationGroupNode(gs.length ? gs : [identity(this.degree)]);
  }
  pointwiseStabilizer(points: readonly number[]): PermutationGroupNode {
    let group: PermutationGroupNode = this;
    for (const p of points) group = group.stabilizer(p);
    return group;
  }
  isSubgroup(group: PermutationGroupNode, strict = true): boolean {
    return (!strict || this.degree === group.degree) && this.generators.every((g) => group.contains(g, strict));
  }
  /** Enumerate lazily; order and membership never enumerate the group. */
  *generateSchreierSims(): Generator<Permutation> { yield* enumerate(this.getChain(), this.degree); }
  /** Orbit representatives t with point^t = beta. */
  orbitTransversal(point: number): Permutation[] { this.checkPoint(point); return [...orbitTransversal(this.generators, this.degree, point).values()]; }
  get base(): number[] { const out: number[] = []; for (let c = this.getChain(); c; c = c.next) out.push(c.point); return out; }
  get basicOrbits(): number[][] { const out: number[][] = []; for (let c = this.getChain(); c; c = c.next) out.push([...c.transversal.keys()].sort((a, b) => a - b)); return out; }
}
export const PermutationGroup = /* @__PURE__ */ callableClass(PermutationGroupNode, (...generators: Permutation[] | [readonly Permutation[]]): PermutationGroupNode => new PermutationGroupNode(...generators));
export type PermutationGroup = PermutationGroupNode;
