// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14 combinatorics/polyhedron.py, BSD-3-Clause; see LICENSE.

/**
 * @file SymPy sympy.combinatorics.polyhedron: Polyhedron, the corners and
 * faces of a polyhedron moved by the permutations of a group.
 */

import { TupleNode } from '../core/containers';
import { at, cast } from '../core/guard';
import type { Expr, ExprLike } from '../core/nodes';
import { ExtensionExpr, Rational, Sym, asRational } from '../core/nodes';
import { sympify } from '../core/ops';
import type { SetExpr } from '../sets/sets';
import { finiteSet } from '../sets/sets';
import { minlex } from '../utilities/iterables';
import { Permutation } from './permutations';
import { PermutationGroupNode } from './permgroups';

const faceTuple = (f: readonly number[]): TupleNode => new TupleNode(f.map((i) => Rational.of(BigInt(i))));
const faceIndices = (t: Expr): number[] => cast(t, TupleNode).args.map((e) => Number(asRational(e).p));

/**
 * SymPy Polyhedron(corners, faces, pgroup): corners (any expressions; a
 * string is a Symbol) whose positions the permutations of pgroup move.
 * Faces are lists of corner indices, stored in their minimal rotation.
 */
export class Polyhedron extends ExtensionExpr {
  #corners: Expr[];
  readonly pgroup: PermutationGroupNode;
  constructor(corners: readonly (ExprLike | string)[], faces: readonly (readonly number[])[] = [], pgroup: readonly Permutation[] = []) {
    // a string corner is a Symbol (SymPy sympifies the corners)
    const c = new TupleNode(corners.map((x) => (typeof x === 'string' ? new Sym(x) : sympify(x))));
    const f = new TupleNode(faces.map((face) => faceTuple(minlex(face, { directed: false }))));
    const g = new TupleNode(pgroup);
    if (pgroup.length && at(pgroup, 0).size !== corners.length) throw new RangeError('Permutation size unequal to number of corners.');
    super('Polyhedron', [c, f, g]);
    this.#corners = [...c.args];
    this.pgroup = new PermutationGroupNode(pgroup.length ? [...pgroup] : [new Permutation(Array.from({ length: corners.length }, (_, i) => i))]);
  }

  withArgs(args: readonly Expr[]): Expr {
    const [c, f, g] = args;
    return new Polyhedron(cast(c, TupleNode).args, cast(f, TupleNode).args.map(faceIndices), cast(g, TupleNode).args.map((p) => cast(p, Permutation)));
  }

  /** SymPy corners (vertices): the corners in their current positions. */
  get corners(): Expr[] {
    return [...this.#corners];
  }

  /** SymPy vertices: the same as corners. */
  get vertices(): Expr[] {
    return this.corners;
  }

  /** SymPy array_form: the original index of the corner now at each position. */
  get arrayForm(): number[] {
    const original = cast(at(this.args, 0), TupleNode).args;
    return this.#corners.map((c) => original.findIndex((o) => o.key === c.key));
  }

  /** SymPy cyclic_form: the cycles of the array form. */
  get cyclicForm(): number[][] {
    return new Permutation(this.arrayForm).cyclicForm;
  }

  /** SymPy size: the number of corners. */
  get size(): number {
    return this.#corners.length;
  }

  /** SymPy faces: the set of faces, each a tuple of corner indices in its minimal rotation. */
  get faces(): SetExpr {
    return finiteSet(...cast(at(this.args, 1), TupleNode).args);
  }

  /** SymPy edges: the set of sorted index pairs of consecutive corners of the faces. */
  get edges(): SetExpr {
    const out = new Map<string, number[]>();
    for (const face of cast(at(this.args, 1), TupleNode).args.map(faceIndices)) {
      face.forEach((v, i) => {
        const edge = [v, at(face, (i - 1 + face.length) % face.length)].sort((a, b) => a - b);
        out.set(edge.join(','), edge);
      });
    }
    return finiteSet(...[...out.values()].map(faceTuple));
  }

  /**
   * SymPy rotate(perm): move the corners by a permutation of the size, or by
   * the generator of pgroup with that index (in place, as in SymPy).
   */
  rotate(perm: Permutation | number): void {
    const p = typeof perm === 'number' ? this.pgroup.getItem(perm) : perm;
    if (p.size !== this.size) throw new RangeError('Polyhedron and Permutation sizes differ.');
    const a = p.arrayForm;
    const corners = this.#corners;
    this.#corners = corners.map((_, i) => at(corners, at(a, i)));
  }

  /** SymPy reset(): return the corners to their original positions. */
  reset(): void {
    this.#corners = [...cast(at(this.args, 0), TupleNode).args];
  }
}

/** A polyhedron with the corners 0, ..., n - 1, its faces and the cycles of the permutations of its group. */
const solid = (n: number, faces: number[][], pgroup: number[][][]): Polyhedron =>
  new Polyhedron(
    Array.from({ length: n }, (_, i) => i),
    faces,
    pgroup.map((cycles) => new Permutation(cycles, { size: n })),
  );

/**
 * SymPy polyhedron.tetrahedron: the tetrahedron: 4 corners, 4 faces and 7 rotations. Like SymPy's module-level object
 * it is one mutable Polyhedron: `rotate` moves its corners, `reset` restores them.
 */
export const tetrahedron: Polyhedron = /* @__PURE__ */ solid(4, [[0,1,2],[0,2,3],[0,1,3],[1,2,3]], [[[1,2,3]],[[0,1,2]],[[0,3,2]],[[0,3,1]],[[0,1],[2,3]],[[0,2],[1,3]],[[0,3],[1,2]]]);

/**
 * SymPy polyhedron.cube: the cube: 8 corners, 6 faces and 13 rotations. Like SymPy's module-level object
 * it is one mutable Polyhedron: `rotate` moves its corners, `reset` restores them.
 */
export const cube: Polyhedron = /* @__PURE__ */ solid(8, [[0,1,2,3],[0,1,5,4],[1,2,6,5],[2,3,7,6],[0,3,7,4],[4,5,6,7]], [[[0,1,2,3],[4,5,6,7]],[[0,4,5,1],[2,3,7,6]],[[0,4,7,3],[1,5,6,2]],[[0,1],[2,4],[3,5],[6,7]],[[0,6],[1,2],[3,5],[4,7]],[[0,6],[1,7],[2,3],[4,5]],[[0,3],[1,7],[2,4],[5,6]],[[0,4],[1,7],[2,6],[3,5]],[[0,6],[1,5],[2,4],[3,7]],[[1,3,4],[2,7,5]],[[0,5,2],[3,4,6]],[[0,5,7],[1,6,3]],[[0,7,2],[1,4,6]]]);

/**
 * SymPy polyhedron.octahedron: the octahedron (the double of the cube): 6 corners, 8 faces and 13 rotations. Like SymPy's module-level object
 * it is one mutable Polyhedron: `rotate` moves its corners, `reset` restores them.
 */
export const octahedron: Polyhedron = /* @__PURE__ */ solid(6, [[0,1,2],[0,2,3],[0,3,4],[0,1,4],[1,2,5],[2,3,5],[3,4,5],[1,4,5]], [[[1,2,3,4]],[[0,4,5,2]],[[0,1,5,3]],[[0,1],[2,4],[3,5]],[[0,2],[1,3],[4,5]],[[0,3],[1,5],[2,4]],[[0,4],[1,3],[2,5]],[[0,5],[1,4],[2,3]],[[0,5],[1,2],[3,4]],[[0,4,1],[2,3,5]],[[0,1,2],[3,4,5]],[[0,2,3],[1,5,4]],[[0,4,3],[1,5,2]]]);

/**
 * SymPy polyhedron.dodecahedron: the dodecahedron: 20 corners, 12 faces and 31 rotations. Like SymPy's module-level object
 * it is one mutable Polyhedron: `rotate` moves its corners, `reset` restores them.
 */
export const dodecahedron: Polyhedron = /* @__PURE__ */ solid(20, [[0,1,2,3,4],[0,1,6,10,5],[1,2,7,11,6],[2,3,8,12,7],[3,4,9,13,8],[0,4,9,14,5],[5,10,16,15,14],[6,10,16,17,11],[7,11,17,18,12],[8,12,18,19,13],[9,13,19,15,14],[15,16,17,18,19]], [[[0,1,2,3,4],[5,6,7,8,9],[10,11,12,13,14],[15,16,17,18,19]],[[0,5,10,6,1],[2,4,14,16,11],[3,9,15,17,7],[8,13,19,18,12]],[[0,10,17,12,3],[1,6,11,7,2],[4,5,16,18,8],[9,14,15,19,13]],[[0,6,17,19,9],[1,11,18,13,4],[2,7,12,8,3],[5,10,16,15,14]],[[0,2,12,19,14],[1,7,18,15,5],[3,8,13,9,4],[6,11,17,16,10]],[[0,4,9,14,5],[1,3,13,15,10],[2,8,19,16,6],[7,12,18,17,11]],[[0,1],[2,5],[3,10],[4,6],[7,14],[8,16],[9,11],[12,15],[13,17],[18,19]],[[0,7],[1,2],[3,6],[4,11],[5,12],[8,10],[9,17],[13,16],[14,18],[15,19]],[[0,12],[1,8],[2,3],[4,7],[5,18],[6,13],[9,11],[10,19],[14,17],[15,16]],[[0,8],[1,13],[2,9],[3,4],[5,12],[6,19],[7,14],[10,18],[11,15],[16,17]],[[0,4],[1,9],[2,14],[3,5],[6,13],[7,15],[8,10],[11,19],[12,16],[17,18]],[[0,5],[1,14],[2,15],[3,16],[4,10],[6,9],[7,19],[8,17],[11,13],[12,18]],[[0,11],[1,6],[2,10],[3,16],[4,17],[5,7],[8,15],[9,18],[12,14],[13,19]],[[0,18],[1,12],[2,7],[3,11],[4,17],[5,19],[6,8],[9,16],[10,13],[14,15]],[[0,18],[1,19],[2,13],[3,8],[4,12],[5,17],[6,15],[7,9],[10,16],[11,14]],[[0,13],[1,19],[2,15],[3,14],[4,9],[5,8],[6,18],[7,16],[10,12],[11,17]],[[0,16],[1,15],[2,19],[3,18],[4,17],[5,10],[6,14],[7,13],[8,12],[9,11]],[[0,18],[1,17],[2,16],[3,15],[4,19],[5,12],[6,11],[7,10],[8,14],[9,13]],[[0,15],[1,19],[2,18],[3,17],[4,16],[5,14],[6,13],[7,12],[8,11],[9,10]],[[0,17],[1,16],[2,15],[3,19],[4,18],[5,11],[6,10],[7,14],[8,13],[9,12]],[[0,19],[1,18],[2,17],[3,16],[4,15],[5,13],[6,12],[7,11],[8,10],[9,14]],[[1,4,5],[2,9,10],[3,14,6],[7,13,16],[8,15,11],[12,19,17]],[[0,6,2],[3,5,11],[4,10,7],[8,14,17],[9,16,12],[13,15,18]],[[0,11,8],[1,7,3],[4,6,12],[5,17,13],[9,10,18],[14,16,19]],[[0,7,13],[1,12,9],[2,8,4],[5,11,19],[6,18,14],[10,17,15]],[[0,3,9],[1,8,14],[2,13,5],[6,12,15],[7,19,10],[11,18,16]],[[0,14,10],[1,9,16],[2,13,17],[3,19,11],[4,15,6],[7,8,18]],[[0,16,7],[1,10,11],[2,5,17],[3,14,18],[4,15,12],[8,9,19]],[[0,16,13],[1,17,8],[2,11,12],[3,6,18],[4,10,19],[5,15,9]],[[0,11,15],[1,17,14],[2,18,9],[3,12,13],[4,7,19],[5,6,16]],[[0,8,15],[1,12,16],[2,18,10],[3,19,5],[4,13,14],[6,7,17]]]);

/**
 * SymPy polyhedron.icosahedron: the icosahedron (the double of the dodecahedron): 12 corners, 20 faces and 31 rotations. Like SymPy's module-level object
 * it is one mutable Polyhedron: `rotate` moves its corners, `reset` restores them.
 */
export const icosahedron: Polyhedron = /* @__PURE__ */ solid(12, [[0,1,2],[0,2,3],[0,3,4],[0,4,5],[0,1,5],[1,6,7],[1,2,7],[2,7,8],[2,3,8],[3,8,9],[3,4,9],[4,9,10],[4,5,10],[5,6,10],[1,5,6],[6,7,11],[7,8,11],[8,9,11],[9,10,11],[6,10,11]], [[[1,2,3,4,5],[6,7,8,9,10]],[[0,5,6,7,2],[3,4,10,11,8]],[[0,1,7,8,3],[4,5,6,11,9]],[[0,2,8,9,4],[1,7,11,10,5]],[[0,3,9,10,5],[1,2,8,11,6]],[[0,4,10,6,1],[2,3,9,11,7]],[[0,1],[2,5],[3,6],[4,7],[8,10],[9,11]],[[0,2],[1,3],[4,7],[5,8],[6,9],[10,11]],[[0,3],[1,9],[2,4],[5,8],[6,11],[7,10]],[[0,4],[1,9],[2,10],[3,5],[6,8],[7,11]],[[0,5],[1,4],[2,10],[3,6],[7,9],[8,11]],[[0,6],[1,5],[2,10],[3,11],[4,7],[8,9]],[[0,7],[1,2],[3,6],[4,11],[5,8],[9,10]],[[0,8],[1,9],[2,3],[4,7],[5,11],[6,10]],[[0,9],[1,11],[2,10],[3,4],[5,8],[6,7]],[[0,10],[1,9],[2,11],[3,6],[4,5],[7,8]],[[0,11],[1,6],[2,10],[3,9],[4,8],[5,7]],[[0,11],[1,8],[2,7],[3,6],[4,10],[5,9]],[[0,11],[1,10],[2,9],[3,8],[4,7],[5,6]],[[0,11],[1,7],[2,6],[3,10],[4,9],[5,8]],[[0,11],[1,9],[2,8],[3,7],[4,6],[5,10]],[[0,5,1],[2,4,6],[3,10,7],[8,9,11]],[[0,1,2],[3,5,7],[4,6,8],[9,10,11]],[[0,2,3],[1,8,4],[5,7,9],[6,11,10]],[[0,3,4],[1,8,10],[2,9,5],[6,7,11]],[[0,4,5],[1,3,10],[2,9,6],[7,8,11]],[[0,10,7],[1,5,6],[2,4,11],[3,9,8]],[[0,6,8],[1,7,2],[3,5,11],[4,10,9]],[[0,7,9],[1,11,4],[2,8,3],[5,6,10]],[[0,8,10],[1,7,6],[2,11,5],[3,9,4]],[[0,9,6],[1,3,11],[2,8,7],[4,10,5]]]);
