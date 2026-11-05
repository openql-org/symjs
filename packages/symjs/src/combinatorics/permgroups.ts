// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14 combinatorics/perm_groups.py, BSD-3-Clause; see LICENSE.

/**
 * @file SymPy sympy.combinatorics.perm_groups: PermutationGroup (Schreier-Sims
 * bases and strong generating sets, orbits, stabilizers, cosets, blocks,
 * derived and central series, subgroup search), SymmetricPermutationGroup and
 * Coset. Randomized algorithms draw from SymPy's shared generator
 * (ntheory/random.ts), so that a seeded run gives SymPy's results.
 */

import { NotImplementedError } from '../core/errors';
import { at, cast, defined, expectType, getOrThrow } from '../core/guard';
import { callableClass } from '../core/callable';
import type { Expr, ExprLike } from '../core/nodes';
import { ExtensionExpr, Rational, Sym, asRational } from '../core/nodes';
import type { NoMatchResult } from '../core/truth';
import { NoMatch } from '../core/truth';
import { factorint, multiplicity, primefactors } from '../ntheory/factor';
import { rng } from '../ntheory/random';
import { Cycle, Permutation, afCommutesWith, afInvert, afNew, afPow, afRmul, afRmuln, permutationStr } from './permutations';
import type { SlpEntry, Transversal } from './util';
import { baseOrdering, checkCyclesAltSym, distributeGensByBase, handlePrecomputedBsgs, includesPerm, orbitList, orbitTransversalPairs, orbitsTransversalsFromBsgs, strip, stripAf, strongGensFromDistr } from './util';

const range = (n: number): number[] => Array.from({ length: n }, (_, i) => i);
const sameArray = (a: readonly number[], b: readonly number[]): boolean => a.length === b.length && a.every((x, i) => x === b[i]);
const factorial = (n: number): bigint => {
  let f = 1n;
  for (let i = 2; i <= n; i++) f *= BigInt(i);
  return f;
};
/** The first point an array form moves (the array form is not the identity). */
const firstMoved = (af: readonly number[]): number => {
  let m = 0;
  while (af[m] === m) m++;
  return m;
};
/** Permutations without repeats, in order (SymPy uniq). */
const uniqPerms = (ps: readonly Permutation[]): Permutation[] => [...new Map(ps.map((p) => [p.key, p] as const)).values()];
/** A set of permutations, compared structurally (a Python set of Permutations). */
const permSet = (ps: Iterable<Permutation>): Set<Permutation> => new Set(uniqPerms([...ps]));

/** The action of SymPy orbit(alpha, action): on tuples, on sets, or the union of the orbits of the points. */
export type OrbitAction = 'tuples' | 'sets' | 'union';

/** SymPy _orbit(degree, generators, alpha, action). */
function orbitOf(degree: number, generators: readonly Permutation[], alpha: number | readonly number[], action: OrbitAction): Set<number> | Set<number[]> {
  const points = typeof alpha === 'number' ? [alpha] : [...alpha];
  if (points.length === 1 || action === 'union') {
    const gens = generators.map((g) => g.arrayForm);
    const orb = [...points];
    const used = new Array<boolean>(degree).fill(false);
    for (const el of points) used[el] = true;
    for (let k = 0; k < orb.length; k++) {
      for (const gen of gens) {
        const temp = at(gen, at(orb, k));
        if (!used[temp]) {
          orb.push(temp);
          used[temp] = true;
        }
      }
    }
    return new Set(orb);
  }
  const gens = generators.map((g) => g.arrayForm);
  const norm = action === 'sets' ? (t: number[]): number[] => [...new Set(t)].sort((a, b) => a - b) : (t: number[]): number[] => t;
  const start = norm(points);
  const orb = [start];
  const used = new Set([start.join(',')]);
  for (let k = 0; k < orb.length; k++) {
    for (const gen of gens) {
      const temp = norm(at(orb, k).map((x) => at(gen, x)));
      if (!used.has(temp.join(','))) {
        orb.push(temp);
        used.add(temp.join(','));
      }
    }
  }
  return new Set(orb);
}

/** SymPy _orbits(degree, generators): the orbits, each found from its smallest point. */
function orbitsOf(degree: number, generators: readonly Permutation[]): Set<number>[] {
  const orbs: Set<number>[] = [];
  let sortedI = range(degree);
  while (sortedI.length) {
    const orb = new Set(orbitList(degree, generators, at(sortedI, 0)));
    orbs.push(orb);
    sortedI = sortedI.filter((i) => !orb.has(i));
  }
  return orbs;
}

/** SymPy _stabilizer(degree, generators, alpha): Schreier generators of the point stabilizer. */
function stabilizerGens(degree: number, generators: readonly Permutation[], alpha: number): Permutation[] {
  const orb = [alpha];
  const table = new Map([[alpha, range(degree)]]);
  const tableInv = new Map([[alpha, range(degree)]]);
  const used = new Array<boolean>(degree).fill(false);
  used[alpha] = true;
  const gens = generators.map((x) => x.arrayForm);
  const stabGens: number[][] = [];
  for (let k = 0; k < orb.length; k++) {
    const b = at(orb, k);
    for (const gen of gens) {
      const temp = at(gen, b);
      if (!used[temp]) {
        const genTemp = afRmul(gen, getOrThrow(table, b));
        orb.push(temp);
        table.set(temp, genTemp);
        tableInv.set(temp, afInvert(genTemp));
        used[temp] = true;
      } else {
        const schreierGen = afRmuln(getOrThrow(tableInv, temp), gen, getOrThrow(table, b));
        if (!stabGens.some((s) => sameArray(s, schreierGen))) stabGens.push(schreierGen);
      }
    }
  }
  return stabGens.map(afNew);
}

const isNumber = (x: unknown): x is number => typeof x === 'number';
const isNumberArray = (x: unknown): x is number[] => Array.isArray(x);
const isPermutationList = (x: unknown): x is readonly (Permutation | Cycle)[] => Array.isArray(x);
const rmul = (...ps: Permutation[]): Permutation => Permutation.rmulWithAf(...ps);

/** Options of the PermutationGroup constructor. */
export interface PermutationGroupOptions {
  /** Remove repeated generators (SymPy dups=True, the default). */
  dups?: boolean;
  /** The degree the generators are resized to when their sizes differ (default: the largest size). */
  degree?: number;
}
const isGroupOptions = (x: unknown): x is PermutationGroupOptions => typeof x === 'object' && x !== null && !(x instanceof Permutation) && !(x instanceof Cycle) && !Array.isArray(x);

/** The Schreier-Sims data of a group (SymPy _base, _strong_gens, _transversals, ...). */
interface Bsgs {
  base: number[];
  strongGens: Permutation[];
  strongGensSlp: Map<string, Permutation[]>;
  basicOrbits: number[][];
  transversals: Transversal[];
  transversalSlp: Map<number, number[]>[];
}

/** SymPy PermutationGroup: the group generated by a list of permutations of the same size. */
export class PermutationGroupNode extends ExtensionExpr {
  readonly generators: readonly Permutation[];
  /** @internal SymPy _degree (the named groups set it). */
  degreeValue: number;
  /** @internal Properties known in advance (SymPy _order, _is_abelian, ...; the named groups set them). */
  known: { order?: bigint; isAbelian?: boolean; isSym?: boolean; isAlt?: boolean; isNilpotent?: boolean; isSolvable?: boolean; isTransitive?: boolean; isDihedral?: boolean; isCyclic?: boolean; isPrimitive?: boolean; isPerfect?: boolean; transitivityDegree?: number; center?: PermutationGroupNode } = {};
  #bsgs: Bsgs | undefined;
  #elements: Permutation[] | undefined;
  #randomGens: number[][] = [];

  /** SymPy PermutationGroup(*gens) or PermutationGroup(gens), with optional { dups, degree }. */
  constructor(...input: (Permutation | Cycle | readonly (Permutation | Cycle)[] | PermutationGroupOptions)[]) {
    const tail = input[input.length - 1];
    const opts: PermutationGroupOptions = isGroupOptions(tail) ? tail : {};
    const items = isGroupOptions(tail) ? input.slice(0, -1) : input;
    const head = items[0];
    const raw: unknown[] = isPermutationList(head) ? [...head] : items;
    let args = raw.length ? raw.map((a) => (a instanceof Cycle ? new Permutation(a) : cast(a, Permutation))) : [new Permutation()];
    if (new Set(args.map((a) => a.size)).size > 1) {
      const degree = opts.degree ?? Math.max(...args.map((a) => a.size));
      args = args.map((a) => (a.size === degree ? a : new Permutation(a, { size: degree })));
    }
    if (opts.dups ?? true) args = uniqPerms(args);
    if (args.length > 1) args = args.filter((g) => !g.isIdentity);
    super('PermutationGroup', args);
    this.generators = args;
    this.degreeValue = at(args, 0).size;
  }

  withArgs(args: readonly Expr[]): Expr {
    return new PermutationGroupNode(args.map((a) => cast(a, Permutation)));
  }

  /** SymPy str: PermutationGroup([ followed by one generator per line. */
  override printStr(_print: (e: Expr) => string): string {
    return `PermutationGroup([\n${this.generators.map((g) => `    ${permutationStr(g)}`).join(',\n')}])`;
  }

  /** SymPy degree: the size of the permutations. */
  get degree(): number {
    return this.degreeValue;
  }

  /** SymPy identity: the identity permutation of the group's degree. */
  get identity(): Permutation {
    return afNew(range(this.degree));
  }

  /** SymPy len(G): the number of generators. */
  get length(): number {
    return this.generators.length;
  }

  /** SymPy G[i]: the ith generator. */
  getItem(i: number): Permutation {
    return at(this.generators, i);
  }

  /** SymPy copy(). */
  copy(): PermutationGroupNode {
    return new PermutationGroupNode([...this.generators]);
  }

  /**
   * SymPy equals(other): whether both generate the same group (unlike the
   * structural `==`). A non-group is never equal.
   */
  override equals(other: ExprLike): boolean {
    if (!(other instanceof PermutationGroupNode)) return false;
    const a = uniqPerms(this.generators);
    const b = uniqPerms(other.generators);
    if (a.length === b.length && a.every((g) => includesPerm(b, g))) return true;
    return a.every((g) => other.contains(g)) && b.every((g) => this.contains(g));
  }

  /** SymPy G*H: the direct product acting on n1 + n2 points; G*p is the right coset Coset(p, G). */
  override mul(other: ExprLike): PermutationGroupNode | Coset {
    if (other instanceof Permutation) return new Coset(other, this, undefined, '+');
    const o = cast(other, PermutationGroupNode);
    const n1 = this.degree;
    const n2 = o.degree;
    const gens1 = this.generators.map((p) => [...p.arrayForm, ...range(n2).map((i) => i + n1)]);
    const gens2 = o.generators.map((p) => [...range(n1), ...p.arrayForm.map((x) => x + n1)]);
    return new PermutationGroupNode([...gens1, ...gens2].map(afNew));
  }

  // ---- Schreier-Sims ---------------------------------------------------------

  #ensureBsgs(): Bsgs {
    if (this.#bsgs === undefined) this.#schreierSims();
    return defined(this.#bsgs);
  }

  /** SymPy schreier_sims(): compute (once) a base and strong generating set with the incremental algorithm. */
  schreierSims(): void {
    this.#ensureBsgs();
  }

  /** SymPy _schreier_sims(base): recompute the base and strong generating set, starting from `base`. */
  #schreierSims(baseIn?: readonly number[]): void {
    const { base, strongGens, slp } = this.#incremental(baseIn ? [...baseIn] : [], undefined);
    const strongGensSlp = new Map<string, Permutation[]>(slp);
    if (!base.length) {
      this.#bsgs = { base, strongGens, strongGensSlp, basicOrbits: [], transversals: [], transversalSlp: [] };
      return;
    }
    const distr = distributeGensByBase(base, strongGens);
    const { basicOrbits, transversals, slps } = orbitsTransversalsFromBsgs(base, distr);
    const transversalSlp = slps.map((s, i) => new Map([...s].map(([k, v]) => [k, v.map((j) => strongGens.findIndex((g) => g.key === at(at(distr, i), j).key))])));
    this.#bsgs = { base, strongGens, strongGensSlp, transversals, basicOrbits: basicOrbits.map((o) => [...o].sort((a, b) => a - b)), transversalSlp };
  }

  /**
   * SymPy schreier_sims_incremental(base, gens): extend `base` to a base and
   * `gens` to a strong generating set of the group, as [base, strong_gens].
   */
  schreierSimsIncremental(base: readonly number[] = [], gens?: readonly Permutation[]): [number[], Permutation[]] {
    const r = this.#incremental([...base], gens);
    return [r.base, r.strongGens];
  }

  #incremental(baseIn: number[], gensIn: readonly Permutation[] | undefined): { base: number[]; strongGens: Permutation[]; slp: [string, Permutation[]][] } {
    const gens0 = gensIn ? [...gensIn] : [...this.generators];
    const degree = this.degree;
    if (gens0.length === 1 && at(gens0, 0).isIdentity) return { base: baseIn, strongGens: gens0, slp: [[at(gens0, 0).key, [at(gens0, 0)]]] };
    const base = [...baseIn];
    const gens = gens0.filter((x) => !x.isIdentity);
    for (const gen of gens) {
      const af = gen.arrayForm;
      if (base.every((x) => af[x] === x)) base.push(firstMoved(af));
    }
    const distr = distributeGensByBase(base, gens);
    const strongGensSlp: [Permutation, SlpEntry[]][] = [];
    const transversals: Map<number, number[]>[] = [];
    const slps: Map<number, number[]>[] = [];
    const orbs: number[][] = [];
    const setLevel = (l: number): void => {
      const { tr, slp } = orbitTransversalPairs(degree, at(distr, l), at(base, l));
      transversals[l] = new Map(tr);
      slps[l] = slp;
      orbs[l] = tr.map(([x]) => x);
    };
    for (let i = 0; i < base.length; i++) setLevel(i);
    let i = base.length - 1;
    while (i >= 0) {
      let continueI = false;
      const db = new Map<number, number[]>();
      const ti = at(transversals, i);
      outer: for (const [beta, uBeta] of [...ti]) {
        const level = at(distr, i);
        for (let j = 0; j < level.length; j++) {
          const gen = at(level, j).arrayForm;
          const gb = at(gen, beta);
          const u1 = getOrThrow(ti, gb);
          const g1 = afRmul(gen, uBeta);
          if (sameArray(g1, u1)) continue;
          let u1Inv = db.get(gb);
          if (u1Inv === undefined) {
            u1Inv = afInvert(u1);
            db.set(gb, u1Inv);
          }
          const schreierGen = afRmul(u1Inv, g1);
          const u1InvSlp = [...getOrThrow(at(slps, i), gb)].reverse().map((g): SlpEntry => [i, [g]]);
          const slp0: SlpEntry[] = [...u1InvSlp, [i, j], ...getOrThrow(at(slps, i), beta).map((g): SlpEntry => [i, g])];
          const [h, jj, slp] = stripAf(schreierGen, base, orbs, transversals, i, slp0, slps);
          let y = true;
          if (jj <= base.length) y = false;
          else if (h !== false) {
            y = false;
            base.push(firstMoved(h));
            distr.push([]);
          }
          if (!y) {
            const hp = afNew(expectType(h, isNumberArray));
            strongGensSlp.push([hp, slp]);
            for (let l = i + 1; l < jj; l++) {
              at(distr, l).push(hp);
              setLevel(l);
            }
            i = jj - 1;
            continueI = true;
            break outer;
          }
        }
      }
      if (continueI) continue;
      i--;
    }
    const strongGens = [...gens, ...strongGensSlp.map(([k]) => k)];
    const slp: [string, Permutation[]][] = strongGensSlp.map(([k, s]) => [k.key, s.map(([lev, g]) => (typeof g === 'number' ? at(at(distr, lev), g) : at(at(distr, lev), at(g, 0)).inverse()))]);
    for (const g of gens) slp.push([g.key, [g]]);
    return { base, strongGens, slp };
  }

  /**
   * SymPy schreier_sims_random(base, gens, consec_succ): a probable base and
   * strong generating set from random elements, as [base, strong_gens].
   */
  schreierSimsRandom(baseIn: readonly number[] = [], gens: readonly Permutation[] = this.generators, consecSucc = 10): [number[], Permutation[]] {
    const base = [...baseIn];
    const n = this.degree;
    for (const gen of gens) {
      const af = gen.arrayForm;
      if (base.every((x) => af[x] === x)) base.push(firstMoved(af));
    }
    const distr = distributeGensByBase(base, gens);
    const transversals: Transversal[] = [];
    const orbs: number[][] = [];
    const setLevel = (l: number): void => {
      const { tr } = orbitTransversalPairs(n, at(distr, l), at(base, l));
      transversals[l] = new Map(tr.map(([x, y]) => [x, afNew(y)]));
      orbs[l] = tr.map(([x]) => x);
    };
    for (let i = 0; i < base.length; i++) setLevel(i);
    let c = 0;
    while (c < consecSucc) {
      const g = this.randomPr();
      const [h, j] = strip(g, base, orbs, transversals);
      let y = true;
      if (j <= base.length) y = false;
      else if (!h.isIdentity) {
        y = false;
        base.push(firstMoved(h.arrayForm));
        distr.push([]);
      }
      if (!y) {
        for (let l = 1; l < j; l++) {
          at(distr, l).push(h);
          setLevel(l);
        }
        c = 0;
      } else c++;
    }
    return [base, strongGensFromDistr(distr)];
  }

  /** SymPy base: the base of the group's stabilizer chain. */
  get base(): number[] {
    return [...this.#ensureBsgs().base];
  }

  /** SymPy strong_gens: a strong generating set relative to the base. */
  get strongGens(): Permutation[] {
    return [...this.#ensureBsgs().strongGens];
  }

  /** SymPy basic_orbits: the orbit of each base point under its basic stabilizer, sorted. */
  get basicOrbits(): number[][] {
    return this.#ensureBsgs().basicOrbits.map((o) => [...o]);
  }

  /** SymPy basic_transversals: for each base point, a Map from orbit point to coset representative. */
  get basicTransversals(): Map<number, Permutation>[] {
    return this.#ensureBsgs().transversals.map((t) => new Map(t));
  }

  /** SymPy basic_stabilizers: the groups generated by the strong generators fixing the first base points. */
  get basicStabilizers(): PermutationGroupNode[] {
    const { base, strongGens } = this.#ensureBsgs();
    if (!base.length) return [];
    return distributeGensByBase(base, strongGens).map((gens) => new PermutationGroupNode(gens));
  }

  /**
   * SymPy baseswap(base, strong_gens, pos, randomized): a base and strong
   * generating set with the base points at pos and pos + 1 interchanged.
   */
  baseswap(base: readonly number[], strongGens: readonly Permutation[], pos: number, randomized = false): [number[], Permutation[]] {
    const { transversals, basicOrbits, strongGensDistr } = handlePrecomputedBsgs(base, strongGens);
    const degree = this.degree;
    const orbitSize = (gens: readonly Permutation[], p: number): number => orbitList(degree, gens, p).length;
    const size = (at(basicOrbits, pos).length * at(basicOrbits, pos + 1).length) / orbitSize(at(strongGensDistr, pos), at(base, pos + 1));
    const T = pos + 2 > base.length - 1 ? [] : [...at(strongGensDistr, pos + 2)];
    if (randomized) {
      const stabPos = new PermutationGroupNode(at(strongGensDistr, pos));
      const v = stabPos.schreierVector(at(base, pos + 1));
      while (orbitSize(T, at(base, pos)) !== size) T.push(stabPos.randomStab(at(base, pos + 1), v));
    } else {
      let gamma0 = new Set(at(basicOrbits, pos));
      gamma0.delete(at(base, pos));
      gamma0.delete(at(base, pos + 1));
      while (orbitSize(T, at(base, pos)) !== size) {
        const gamma = at([...gamma0], 0);
        const x = getOrThrow(at(transversals, pos), gamma);
        const temp = x.arrayForm.indexOf(at(base, pos + 1));
        if (!at(basicOrbits, pos + 1).includes(temp)) {
          const orb = new Set(orbitList(degree, T, gamma));
          gamma0 = new Set([...gamma0].filter((q) => !orb.has(q)));
        } else {
          const el = rmul(x, getOrThrow(at(transversals, pos + 1), temp));
          // SymPy appends el when it moves base[pos] out of the orbit of T; were it inside, the same gamma
          // would be chosen again without end, so a run that terminates always appends it
          T.push(el);
          const orb = new Set(orbitList(degree, T, at(base, pos)));
          gamma0 = new Set([...gamma0].filter((q) => !orb.has(q)));
        }
      }
    }
    const newDistr = [...strongGensDistr];
    newDistr[pos + 1] = T;
    const baseNew = [...base];
    [baseNew[pos], baseNew[pos + 1]] = [at(baseNew, pos + 1), at(baseNew, pos)];
    const strongGensNew = strongGensFromDistr(newDistr);
    for (const gen of T) if (!includesPerm(strongGensNew, gen)) strongGensNew.push(gen);
    return [baseNew, strongGensNew];
  }

  // ---- membership, order and elements ----------------------------------------------

  /**
   * SymPy coset_factor(g, factor_index): the transversal elements u_i with
   * g = u_n*...*u_1 (or, with factorIndex, the orbit points), [] when g is
   * not in the group.
   */
  cosetFactor(g: Permutation | Cycle | readonly number[], factorIndex: true): number[];
  cosetFactor(g: Permutation | Cycle | readonly number[], factorIndex?: false): Permutation[];
  cosetFactor(g: Permutation | Cycle | readonly number[], factorIndex = false): Permutation[] | number[] {
    const gl = g instanceof Permutation ? g.list() : g instanceof Cycle ? g.list() : [...g];
    if (gl.length !== this.degree) throw new RangeError('g should be the same size as permutations of G');
    const { base, basicOrbits, transversals } = this.#ensureBsgs();
    const factors: number[] = [];
    let h = gl;
    for (let i = 0; i < base.length; i++) {
      const beta = at(h, at(base, i));
      if (beta === base[i]) {
        factors.push(beta);
        continue;
      }
      if (!at(basicOrbits, i).includes(beta)) return [];
      h = afRmul(afInvert(getOrThrow(at(transversals, i), beta).arrayForm), h);
      factors.push(beta);
    }
    if (!sameArray(h, range(this.degree))) return [];
    if (factorIndex) return factors;
    return factors.map((f, i) => getOrThrow(at(transversals, i), f));
  }

  /** SymPy contains(g, strict): whether g is an element (strict=false resizes g to the degree). */
  contains(g: unknown, strict = true): boolean {
    if (!(g instanceof Permutation)) return false;
    let p = g;
    if (p.size !== this.degree) {
      if (strict) return false;
      p = new Permutation(p, { size: this.degree });
    }
    if (includesPerm(this.generators, p)) return true;
    return this.cosetFactor(p.arrayForm, true).length > 0;
  }

  /**
   * SymPy generator_product(g, original): g as a product of strong
   * generators (or, with original, of the group's generators).
   */
  generatorProduct(g: Permutation, original = false): Permutation[] {
    if (g.isIdentity) return [];
    const bsgs = this.#ensureBsgs();
    const expand = (ps: readonly Permutation[]): Permutation[] => ps.flatMap((s) => this.generatorProduct(s, true));
    if (includesPerm(bsgs.strongGens, g)) {
      if (!original || includesPerm(this.generators, g)) return [g];
      return expand(getOrThrow(bsgs.strongGensSlp, g.key));
    }
    const gi = g.inverse();
    if (includesPerm(bsgs.strongGens, gi)) {
      if (!original || includesPerm(this.generators, gi)) return [g];
      return expand(getOrThrow(bsgs.strongGensSlp, gi.key)).reverse().map((p) => p.inverse());
    }
    const f = this.cosetFactor(g, true);
    const product: Permutation[] = [];
    f.forEach((j, i) => {
      for (const s of getOrThrow(at(bsgs.transversalSlp, i), j)) {
        const sg = at(bsgs.strongGens, s);
        if (!original) product.push(sg);
        else product.push(...this.generatorProduct(sg, true));
      }
    });
    return product;
  }

  /** SymPy coset_rank(g): the rank of g in the Schreier-Sims ordering of the elements (NoMatch when g is not an element). */
  cosetRank(g: Permutation): bigint | NoMatchResult {
    const factors = this.cosetFactor(g, true);
    if (!factors.length) return NoMatch;
    const { transversals, basicOrbits } = this.#ensureBsgs();
    let rank = 0n;
    let b = 1n;
    factors.forEach((k, i) => {
      rank += b * BigInt(at(basicOrbits, i).indexOf(k));
      b *= BigInt(at(transversals, i).size);
    });
    return rank;
  }

  /** SymPy coset_unrank(rank): the element of that rank (NoMatch for a rank outside 0 .. order - 1). */
  cosetUnrank(rankIn: bigint | number): Permutation | NoMatchResult {
    let rank = BigInt(rankIn);
    if (rank < 0n || rank >= this.order()) return NoMatch;
    const { transversals, basicOrbits } = this.#ensureBsgs();
    const a = transversals.map((t, i) => {
      const n = BigInt(t.size);
      const c = Number(rank % n);
      rank /= n;
      return getOrThrow(t, at(at(basicOrbits, i), c)).arrayForm;
    });
    return afNew(afRmuln(...a));
  }

  /** SymPy order(): the number of elements, the product of the basic orbit lengths. */
  order(): bigint {
    if (this.known.order !== undefined) return this.known.order;
    if (this.known.isSym) return (this.known.order = factorial(this.degree));
    if (this.known.isAlt) return (this.known.order = factorial(this.degree) / 2n);
    return (this.known.order = this.#ensureBsgs().transversals.reduce((p, t) => p * BigInt(t.size), 1n));
  }

  /** SymPy index(H): [G : H] (NoMatch when H is not a subgroup). */
  index(H: PermutationGroupNode): bigint | NoMatchResult {
    return H.isSubgroup(this) ? this.order() / H.order() : NoMatch;
  }

  /** SymPy generate(method, af): the elements, by Schreier-Sims ('coset', the default) or Dimino's method. */
  *generate(method: 'coset' | 'dimino' = 'coset'): Generator<Permutation> {
    if (method === 'dimino') yield* this.generateDimino();
    else yield* this.generateSchreierSims();
  }

  /** SymPy generate_dimino(): the elements in the order of Dimino's method. */
  *generateDimino(): Generator<Permutation> {
    const idn = range(this.degree);
    const elementList = [idn];
    const seen = new Set([idn.join(',')]);
    yield afNew(idn);
    const gens = this.generators.map((p) => p.arrayForm);
    for (let i = 0; i < gens.length; i++) {
      const D = [...elementList];
      let N = [idn];
      while (N.length) {
        const A = N;
        N = [];
        for (const a of A) {
          for (const g of gens.slice(0, i + 1)) {
            const ag = afRmul(a, g);
            if (seen.has(ag.join(','))) continue;
            for (const d of D) {
              const ap = afRmul(d, ag);
              yield afNew(ap);
              elementList.push(ap);
              seen.add(ap.join(','));
              N.push(ap);
            }
          }
        }
      }
    }
    this.known.order = BigInt(elementList.length);
  }

  /** SymPy generate_schreier_sims(): the elements from the basic transversals, without repeats. */
  *generateSchreierSims(): Generator<Permutation> {
    const n = this.degree;
    const { transversals, basicOrbits } = this.#ensureBsgs();
    if (transversals.length === 0) {
      yield* this.generators;
      return;
    }
    if (transversals.length === 1) {
      for (const i of at(basicOrbits, 0)) yield getOrThrow(at(transversals, 0), i);
      return;
    }
    const u = [...transversals].reverse();
    const orbits = [...basicOrbits].reverse();
    const stg = [range(n)];
    const posmax = u.map((x) => x.size);
    const n1 = posmax.length - 1;
    const pos = new Array<number>(n1).fill(0);
    let h = 0;
    for (;;) {
      if (at(pos, h) >= at(posmax, h)) {
        if (h === 0) return;
        pos[h] = 0;
        h--;
        stg.pop();
        continue;
      }
      const p = afRmul(getOrThrow(at(u, h), at(at(orbits, h), at(pos, h))).arrayForm, at(stg, stg.length - 1));
      pos[h] = at(pos, h) + 1;
      stg.push(p);
      h++;
      if (h === n1) {
        for (const i of at(orbits, orbits.length - 1)) yield afNew(afRmul(getOrThrow(at(u, u.length - 1), i).arrayForm, at(stg, stg.length - 1)));
        stg.pop();
        h--;
      }
    }
  }

  /** SymPy elements: the list of all elements (computed once). */
  get elements(): Permutation[] {
    this.#elements ??= [...this.generate()];
    return [...this.#elements];
  }

  // ---- random elements -----------------------------------------------------------

  /** SymPy _random_pr_init(r, n): the product replacement state, randomized by n steps. */
  #randomPrInit(r: number, n: number): void {
    const randomGens = this.generators.map((x) => x.arrayForm);
    const k = randomGens.length;
    for (let i = k; i < r; i++) randomGens.push([...at(randomGens, i - k)]);
    randomGens.push(range(this.degree));
    this.#randomGens = randomGens;
    for (let i = 0; i < n; i++) this.randomPr();
  }

  /** SymPy random_pr(gen_count, iterations): a random element by the product replacement algorithm. */
  randomPr(genCount = 11, iterations = 50): Permutation {
    if (this.#randomGens.length === 0) this.#randomPrInit(genCount, iterations);
    const g = this.#randomGens;
    const r = g.length - 1;
    const s = Number(rng.randrange(0n, BigInt(r)));
    let t = Number(rng.randrange(0n, BigInt(r - 1)));
    if (t === s) t = r - 1;
    const x = rng.randbelow(2n) === 0n ? 1 : 2;
    const e = rng.randbelow(2n) === 0n ? -1 : 1;
    if (x === 1) {
      g[s] = afRmul(at(g, s), afPow(at(g, t), e));
      g[r] = afRmul(at(g, r), at(g, s));
    } else {
      g[s] = afRmul(afPow(at(g, t), e), at(g, s));
      g[r] = afRmul(at(g, s), at(g, r));
    }
    return afNew([...at(g, r)]);
  }

  /** SymPy random_stab(alpha, schreier_vector): a random element of the stabilizer of alpha. */
  randomStab(alpha: number, schreierVector?: readonly (number | NoMatchResult)[]): Permutation {
    const v = schreierVector ?? this.schreierVector(alpha);
    const rand = this.randomPr();
    const beta = at(rand.arrayForm, alpha);
    const h = cast(this.orbitRep(alpha, beta, v), Permutation);
    return rmul(h.inverse(), rand);
  }

  /** SymPy random(): a uniformly random element (coset_unrank of a random rank). */
  random(): Permutation {
    return cast(this.cosetUnrank(rng.randrange(0n, this.order())), Permutation);
  }

  /**
   * SymPy make_perm(n, seed): the product of n generators chosen at random
   * (or by the indices in seed; a sequence for n is the seed itself).
   */
  makePerm(nIn: number | readonly number[], seedIn?: number | readonly number[]): Permutation {
    let n: number;
    let seed = seedIn;
    if (typeof nIn !== 'number') {
      if (seed !== undefined) throw new RangeError('If n is a sequence, seed should be None');
      n = nIn.length;
      seed = nIn;
    } else n = nIn;
    if (typeof seed === 'number') rng.seed(seed);
    const queue = typeof seed === 'object' ? [...seed] : undefined;
    const m = this.length;
    const next = (): number => {
      if (queue === undefined) return Number(rng.randrange(0n, BigInt(m)));
      for (;;) {
        const x = queue.shift();
        if (x === undefined) throw new RangeError('_randrange sequence was too short');
        if (x >= 0 && x < m) return x;
      }
    };
    let result = afNew(range(this.degree));
    for (let i = 0; i < n; i++) result = rmul(result, at(this.generators, next()));
    return result;
  }

  // ---- orbits and stabilizers --------------------------------------------------------

  #checkPoint(point: number): void {
    if (!Number.isInteger(point) || point < 0 || point >= this.degree) throw new RangeError('point outside the permutation domain');
  }

  /**
   * SymPy orbit(alpha, action): the orbit of a point (a Set of points), or
   * of a sequence of points acting on tuples, on sets or by union.
   */
  orbit(alpha: number): Set<number>;
  orbit(alpha: readonly number[], action: 'union'): Set<number>;
  orbit(alpha: readonly number[], action?: 'tuples' | 'sets'): Set<number[]> | Set<number>;
  orbit(alpha: number | readonly number[], action: OrbitAction = 'tuples'): Set<number> | Set<number[]> {
    for (const p of typeof alpha === 'number' ? [alpha] : alpha) this.#checkPoint(p);
    return orbitOf(this.degree, this.generators, alpha, action);
  }

  /** SymPy orbits(): the orbits of the group on its points. */
  orbits(): Set<number>[] {
    return orbitsOf(this.degree, this.generators);
  }

  /**
   * SymPy orbit_transversal(alpha, pairs): a representative t with
   * alpha^t = beta for each orbit point beta (with pairs, as [beta, t]).
   */
  orbitTransversal(alpha: number, pairs: true): [number, Permutation][];
  orbitTransversal(alpha: number, pairs?: false): Permutation[];
  orbitTransversal(alpha: number, pairs = false): Permutation[] | [number, Permutation][] {
    this.#checkPoint(alpha);
    const tr = orbitTransversalPairs(this.degree, this.generators, alpha).tr.map(([x, y]): [number, Permutation] => [x, afNew(y)]);
    return pairs ? tr : tr.map(([, y]) => y);
  }

  /**
   * SymPy schreier_vector(alpha): for each point of the orbit of alpha the
   * index of the generator that reaches it (-1 for alpha), NoMatch (SymPy
   * None) for the points outside the orbit.
   */
  schreierVector(alpha: number): (number | NoMatchResult)[] {
    this.#checkPoint(alpha);
    const n = this.degree;
    const v: (number | NoMatchResult)[] = new Array<number | NoMatchResult>(n).fill(NoMatch);
    v[alpha] = -1;
    const orb = [alpha];
    const used = new Array<boolean>(n).fill(false);
    used[alpha] = true;
    const gens = this.generators.map((g) => g.arrayForm);
    for (let k = 0; k < orb.length; k++) {
      gens.forEach((g, i) => {
        const temp = at(g, at(orb, k));
        if (!used[temp]) {
          orb.push(temp);
          used[temp] = true;
          v[temp] = i;
        }
      });
    }
    return v;
  }

  /** SymPy orbit_rep(alpha, beta, schreier_vector): an element mapping alpha to beta, false when beta is not in the orbit. */
  orbitRep(alpha: number, betaIn: number, schreierVector?: readonly (number | NoMatchResult)[]): Permutation | false {
    const v = schreierVector ?? this.schreierVector(alpha);
    let beta = betaIn;
    let k = v[beta];
    if (typeof k !== 'number') return false;
    const gens = this.generators.map((x) => x.arrayForm);
    const a: number[][] = [];
    while (k !== -1) {
      const g = at(gens, k);
      a.push(g);
      beta = g.indexOf(beta);
      k = expectType(v[beta], isNumber);
    }
    return a.length ? afNew(afRmuln(...a)) : afNew(range(this.degree));
  }

  /** SymPy stabilizer(alpha): the stabilizer of a point, from Schreier generators. */
  stabilizer(alpha: number): PermutationGroupNode {
    this.#checkPoint(alpha);
    return new PermutationGroupNode(stabilizerGens(this.degree, this.generators, alpha));
  }

  /** SymPy pointwise_stabilizer(points, incremental): the elements fixing every point of the list. */
  pointwiseStabilizer(points: readonly number[], incremental = true): PermutationGroupNode {
    for (const p of points) this.#checkPoint(p);
    if (incremental) {
      const [, strongGens] = this.schreierSimsIncremental(points);
      const stabGens = strongGens.filter((gen) => points.every((p) => gen.arrayForm[p] === p));
      return new PermutationGroupNode(stabGens.length ? stabGens : [this.identity]);
    }
    let gens = this.generators;
    for (const x of points) gens = stabilizerGens(this.degree, gens, x);
    return new PermutationGroupNode([...gens]);
  }

  /** SymPy is_transitive(strict): one orbit (strict=false: at most one orbit of length > 1). */
  isTransitive(strict = true): boolean {
    if (this.known.isTransitive) return true;
    if (strict) {
      if (this.known.isTransitive !== undefined) return this.known.isTransitive;
      return (this.known.isTransitive = this.degree === 0 || this.orbit(0).size === this.degree);
    }
    return this.orbits().filter((x) => x.size > 1).length === 1;
  }

  /** SymPy transitivity_degree: the largest k for which the group is k-fold transitive. */
  get transitivityDegree(): number {
    if (this.known.transitivityDegree !== undefined) return this.known.transitivityDegree;
    const n = this.degree;
    let G: PermutationGroupNode = this;
    for (let i = 0; i < n; i++) {
      if (G.orbit(i).size !== n - i) return (this.known.transitivityDegree = i);
      G = G.stabilizer(i);
    }
    return (this.known.transitivityDegree = n);
  }

  // ---- blocks ---------------------------------------------------------------------------

  /** SymPy max_div: the largest proper divisor of the degree (the maximum block size). */
  get maxDiv(): number {
    const n = this.degree;
    if (n === 1) return 1;
    let x = 2;
    while (n % x !== 0) x++;
    return n / x;
  }

  /**
   * SymPy minimal_block(points): the block system of the smallest block
   * containing the points, as the block number of each point (false when
   * the group is not transitive).
   */
  minimalBlock(points: readonly number[]): number[] | false {
    if (!this.isTransitive()) return false;
    const n = this.degree;
    const gens = this.generators;
    const parents = range(n);
    const ranks = new Array<number>(n).fill(1);
    const notRep: number[] = [];
    const k = points.length;
    if (k > this.maxDiv) return new Array<number>(n).fill(0);
    for (let i = 0; i < k - 1; i++) {
      parents[at(points, i + 1)] = at(points, 0);
      notRep.push(at(points, i + 1));
    }
    ranks[at(points, 0)] = k;
    let lenNotRep = k - 1;
    const rep = (num: number): number => {
      let r = num;
      while (at(parents, r) !== r) r = at(parents, r);
      let temp = num;
      while (at(parents, temp) !== r) {
        const next = at(parents, temp);
        parents[temp] = r;
        temp = next;
      }
      return r;
    };
    const merge = (first: number, second: number): number => {
      const r1 = rep(first);
      const r2 = rep(second);
      if (r1 === r2) return 0;
      const [n1, n2] = at(ranks, r1) >= at(ranks, r2) ? [r1, r2] : [r2, r1];
      const total = at(ranks, n1) + at(ranks, n2);
      if (total > this.maxDiv) return -1;
      parents[n2] = n1;
      ranks[n1] = total;
      notRep.push(n2);
      return 1;
    };
    for (let i = 0; i < lenNotRep; i++) {
      const gamma = at(notRep, i);
      for (const gen of gens) {
        const delta = rep(gamma);
        const temp = merge(at(gen.arrayForm, gamma), at(gen.arrayForm, delta));
        if (temp === -1) return new Array<number>(n).fill(0);
        lenNotRep += temp;
      }
    }
    for (let i = 0; i < n; i++) rep(i);
    const newReps = new Map<number, number>();
    return parents.map((r, i) => {
      if (!newReps.has(r)) newReps.set(r, i);
      return getOrThrow(newReps, r);
    });
  }

  /** The stabilizer of 0 used by is_primitive and minimal_blocks: random elements, or the Schreier generators. */
  #stabilizerOfZero(randomized: boolean): PermutationGroupNode {
    if (!randomized) return this.stabilizer(0);
    const v = this.schreierVector(0);
    return new PermutationGroupNode(this.generators.map(() => this.randomStab(0, v)));
  }

  /** SymPy is_primitive(randomized): whether the group has only the trivial block systems. */
  isPrimitive(randomized = true): boolean {
    if (this.known.isPrimitive !== undefined) return this.known.isPrimitive;
    if (!this.isTransitive()) return false;
    for (const orb of this.#stabilizerOfZero(randomized).orbits()) {
      const x = Math.min(...orb);
      if (x !== 0 && expectType(this.minimalBlock([0, x]), isNumberArray).some((e) => e !== 0)) return (this.known.isPrimitive = false);
    }
    return (this.known.isPrimitive = true);
  }

  /** SymPy minimal_blocks(randomized): the minimal block systems (false when the group is not transitive). */
  minimalBlocks(randomized = true): number[][] | false {
    if (!this.isTransitive()) return false;
    const blocks: number[][] = [];
    const numBlocks: string[] = [];
    const repBlocks: Set<number>[] = [];
    for (const orb of this.#stabilizerOfZero(randomized).orbits()) {
      const x = Math.min(...orb);
      if (x === 0) continue;
      const block = expectType(this.minimalBlock([0, x]), isNumberArray);
      const appeared = new Map<number, number>();
      const numBlock = block.map((b) => {
        if (!appeared.has(b)) appeared.set(b, appeared.size);
        return getOrThrow(appeared, b);
      });
      const rep = new Set(range(this.degree).filter((j) => numBlock[j] === 0));
      let minimal = true;
      const remove = new Array<boolean>(blocks.length).fill(false);
      for (let i = 0; i < repBlocks.length; i++) {
        const r = at(repBlocks, i);
        if (r.size > rep.size && [...rep].every((q) => r.has(q))) remove[i] = true;
        else if (r.size < rep.size && [...r].every((q) => rep.has(q))) {
          minimal = false;
          break;
        }
      }
      for (let i = remove.length - 1; i >= 0; i--) {
        if (!remove[i]) continue;
        blocks.splice(i, 1);
        numBlocks.splice(i, 1);
        repBlocks.splice(i, 1);
      }
      if (minimal && !numBlocks.includes(numBlock.join(','))) {
        blocks.push(block);
        numBlocks.push(numBlock.join(','));
        repBlocks.push(rep);
      }
    }
    return blocks;
  }

  // ---- properties -------------------------------------------------------------------------

  /** SymPy is_trivial: the group has only the identity. */
  get isTrivial(): boolean {
    return this.length === 1 && at(this.generators, 0).isIdentity;
  }

  /** SymPy is_abelian: the generators commute. */
  get isAbelian(): boolean {
    if (this.known.isAbelian !== undefined) return this.known.isAbelian;
    const gens = this.generators.map((p) => p.arrayForm);
    this.known.isAbelian = gens.every((x, i) => gens.every((y, j) => j <= i || afCommutesWith(x, y)));
    return this.known.isAbelian;
  }

  /** SymPy is_elementary(p): abelian, with every generator of order p. */
  isElementary(p: number | bigint): boolean {
    return this.isAbelian && this.generators.every((g) => g.order().p === BigInt(p));
  }

  /** SymPy abelian_invariants(): the orders of the cyclic factors of the abelianization, sorted. */
  abelianInvariants(): bigint[] {
    if (this.isTrivial) return [];
    let gns = [...this.generators];
    const inv: bigint[] = [];
    let G: PermutationGroupNode = this;
    const H = G.derivedSubgroup();
    const hgens = H.generators;
    for (const p of primefactors(G.order())) {
      const ranks: number[] = [];
      for (;;) {
        const pows = gns.map((g) => g.pow(p)).filter((elm) => !H.contains(elm));
        const K = pows.length ? new PermutationGroupNode([...hgens, ...pows]) : H;
        const r = G.order() / K.order();
        G = K;
        gns = pows;
        if (r === 1n) break;
        ranks.push(Number(multiplicity(p, r)));
      }
      if (ranks.length) {
        const pows = new Array<bigint>(at(ranks, 0)).fill(1n);
        for (const i of ranks) for (let j = 0; j < i; j++) pows[j] = at(pows, j) * p;
        inv.push(...pows);
      }
    }
    return inv.sort((a, b) => (a < b ? -1 : a > b ? 1 : 0));
  }

  #isAltSymNaive(onlySym = false, onlyAlt = false): boolean {
    const symOrder = factorial(this.degree);
    const order = this.order();
    if (order === symOrder) {
      this.known.isSym = true;
      this.known.isAlt = false;
      return !onlyAlt;
    }
    if (2n * order === symOrder) {
      this.known.isSym = false;
      this.known.isAlt = true;
      return !onlySym;
    }
    return false;
  }

  #isAltSymMonteCarlo(eps = 0.05): boolean {
    const n = this.degree;
    const cN = n < 17 ? 0.34 : 0.57;
    const dN = (cN * Math.log(2)) / Math.log(n);
    const nEps = Math.trunc(-Math.log(eps) / dN);
    for (let i = 0; i < nEps; i++) if (checkCyclesAltSym(this.randomPr())) return true;
    return false;
  }

  /**
   * SymPy is_alt_sym(eps): whether the group is the symmetric or alternating
   * group of its degree (Monte Carlo for degree 8 and more: a false answer
   * may be wrong with probability eps).
   */
  isAltSym(eps = 0.05): boolean {
    if (this.known.isSym || this.known.isAlt) return true;
    if (this.known.isSym === false && this.known.isAlt === false) return false;
    if (this.degree < 8) return this.#isAltSymNaive();
    if (this.isTransitive()) return this.#isAltSymMonteCarlo(eps);
    this.known.isSym = false;
    this.known.isAlt = false;
    return false;
  }

  /** SymPy is_symmetric: whether the group is the symmetric group of its degree. */
  get isSymmetric(): boolean {
    if (this.known.isSym !== undefined) return this.known.isSym;
    return this.#isAltSymWith(true);
  }

  /** SymPy is_alternating: whether the group is the alternating group of its degree. */
  get isAlternating(): boolean {
    if (this.known.isAlt !== undefined) return this.known.isAlt;
    return this.#isAltSymWith(false);
  }

  #isAltSymWith(sym: boolean): boolean {
    if (this.degree >= 8) {
      if (this.isTransitive()) {
        if (this.#isAltSymMonteCarlo()) {
          const odd = this.generators.some((g) => g.isOdd);
          this.known.isSym = odd;
          this.known.isAlt = !odd;
          return sym ? odd : !odd;
        }
        return this.#isAltSymNaive(sym, !sym);
      }
      this.known.isSym = false;
      this.known.isAlt = false;
      return false;
    }
    return this.#isAltSymNaive(sym, !sym);
  }

  /** SymPy is_cyclic: whether one element generates the group. */
  get isCyclic(): boolean {
    if (this.known.isCyclic !== undefined) return this.known.isCyclic;
    if (this.length === 1) {
      this.known.isAbelian = true;
      return (this.known.isCyclic = true);
    }
    if (this.known.isAbelian === false) return (this.known.isCyclic = false);
    const order = this.order();
    if (order < 6n) {
      this.known.isAbelian = true;
      if (order !== 4n) return (this.known.isCyclic = true);
    }
    const factors = factorint(order);
    if ([...factors.values()].every((v) => v === 1n)) {
      if (this.known.isAbelian) return (this.known.isCyclic = true);
      const primes = [...factors.keys()].sort((a, b) => Number(a - b));
      if (primes.every((p, i) => primes.every((q, j) => j <= i || q % p !== 1n))) {
        this.known.isAbelian = true;
        return (this.known.isCyclic = true);
      }
    }
    if (!this.isAbelian) return (this.known.isCyclic = false);
    const identity = this.identity;
    return (this.known.isCyclic = [...factors].filter(([, e]) => e > 1n).every(([p]) => this.generators.some((g) => !g.pow(order / p).equals(identity))));
  }

  /** SymPy is_dihedral: whether the group is a dihedral group. */
  get isDihedral(): boolean {
    if (this.known.isDihedral !== undefined) return this.known.isDihedral;
    const order = this.order();
    if (order % 2n === 1n) return (this.known.isDihedral = false);
    if (order === 2n) return (this.known.isDihedral = true);
    if (order === 4n) return (this.known.isDihedral = !this.isCyclic);
    if (this.isAbelian) return (this.known.isDihedral = false);
    const n = order / 2n;
    if (this.length === 2) {
      let [x, y] = [at(this.generators, 0), at(this.generators, 1)];
      let [a, b] = [x.order().p, y.order().p];
      if (a < b) [x, y, a, b] = [y, x, b, a];
      if (a === 2n && b === 2n) return (this.known.isDihedral = true);
      if (a === n && b === 2n && y.mul(x).mul(y).equals(x.inverse())) return (this.known.isDihedral = true);
    }
    const order2: Permutation[] = [];
    const orderN: Permutation[] = [];
    for (const p of this.elements) {
      const k = p.order().p;
      if (k === 2n) order2.push(p);
      else if (k === n) orderN.push(p);
    }
    if (BigInt(order2.length) !== n + 1n - (n % 2n)) return (this.known.isDihedral = false);
    if (!orderN.length) return (this.known.isDihedral = false);
    const x = at(orderN, 0);
    let y = at(order2, 0);
    if (n % 2n === 0n && y.equals(x.pow(n / 2n))) y = at(order2, 1);
    return (this.known.isDihedral = y.mul(x).mul(y).equals(x.inverse()));
  }

  /** SymPy is_subgroup(G, strict): whether every generator is an element of G (strict=false allows a smaller degree). */
  isSubgroup(G: PermutationGroupNode | SymmetricPermutationGroupNode, strict = true): boolean {
    if (G instanceof SymmetricPermutationGroupNode) return this.degree === G.degree;
    if (this.equals0(G) || at(this.generators, 0).size === 0) return true;
    if (G.order() % this.order() !== 0n) return false;
    if (!(this.degree === G.degree || (this.degree < G.degree && !strict))) return false;
    return this.generators.every((g) => G.contains(g, strict));
  }

  /** Structural equality (SymPy ==). */
  private equals0(G: PermutationGroupNode): boolean {
    return this.key === G.key;
  }

  /** SymPy is_normal(gr, strict): whether the group is a normal subgroup of gr. */
  isNormal(gr: PermutationGroupNode, strict = true): boolean {
    if (!this.isSubgroup(gr, strict)) return false;
    const dSelf = this.degree;
    const dGr = gr.degree;
    if (this.isTrivial && (dSelf === dGr || !strict)) return true;
    if (this.known.isAbelian) return true;
    let newSelf = this.copy();
    if (!strict && dSelf !== dGr) {
      // is_subgroup(gr, strict=False) admits only a smaller degree, so SymPy's branch for a larger one is not reached
      newSelf = new PermutationGroupNode([...newSelf.generators, new Permutation(dGr - 1)]);
    }
    const gens2 = newSelf.generators.map((p) => p.arrayForm);
    for (const g1 of gr.generators.map((p) => p.arrayForm)) {
      for (const g2 of gens2) if (!newSelf.cosetFactor(afRmuln(g1, g2, afInvert(g1)), true).length) return false;
    }
    return true;
  }

  // ---- subgroups and series ---------------------------------------------------------------

  /** SymPy subgroup(gens): the subgroup generated by elements of the group. */
  subgroup(gens: readonly Permutation[]): PermutationGroupNode {
    if (!gens.every((g) => this.contains(g))) throw new RangeError('The group does not contain the supplied generators');
    return new PermutationGroupNode([...gens]);
  }

  /**
   * SymPy normal_closure(other, k): the smallest normal subgroup containing
   * other (a group, a list of elements or an element), by the randomized
   * algorithm of SymPy.
   */
  normalClosure(other: PermutationGroupNode | readonly Permutation[] | Permutation, k = 10): PermutationGroupNode {
    if (other instanceof Permutation) return this.normalClosure(new PermutationGroupNode([other]), k);
    if (!(other instanceof PermutationGroupNode)) return this.normalClosure(new PermutationGroupNode([...other]), k);
    const identity = this.identity;
    if (other.generators.every((g) => g.equals(identity))) return other;
    let Z = new PermutationGroupNode([...other.generators]);
    let [base, strongGens] = Z.schreierSimsIncremental();
    let { basicOrbits, transversals } = orbitsTransversalsFromBsgs(base, distributeGensByBase(base, strongGens));
    this.#randomPrInit(10, 20);
    const sifts = (conj: Permutation): boolean => {
      const [h, j] = strip(conj, base, basicOrbits, transversals);
      return h.equals(identity) && j === base.length + 1;
    };
    let loop = true;
    while (loop) {
      Z.#randomPrInit(10, 10);
      for (let i = 0; i < k; i++) {
        const g = this.randomPr();
        const h = Z.randomPr();
        const conj = h.xor(g);
        if (!sifts(conj)) {
          Z = new PermutationGroupNode([...Z.generators, conj]);
          strongGens.push(conj);
          [base, strongGens] = Z.schreierSimsIncremental(base, strongGens);
          ({ basicOrbits, transversals } = orbitsTransversalsFromBsgs(base, distributeGensByBase(base, strongGens)));
        }
      }
      loop = this.generators.some((g) => Z.generators.some((h) => !sifts(h.xor(g))));
    }
    return Z;
  }

  /** SymPy commutator(G, H): the commutator subgroup [G, H], as a normal closure in this group. */
  commutator(G: PermutationGroupNode, H: PermutationGroupNode): PermutationGroupNode {
    const commutators: Permutation[] = [];
    for (const ggen of G.generators) {
      for (const hgen of H.generators) {
        const c = rmul(hgen, ggen, hgen.inverse(), ggen.inverse());
        if (!includesPerm(commutators, c)) commutators.push(c);
      }
    }
    return this.normalClosure(commutators);
  }

  /** SymPy derived_subgroup(): the commutator subgroup [G, G]. */
  derivedSubgroup(): PermutationGroupNode {
    const gens = this.generators.map((p) => p.arrayForm);
    const degree = this.degree;
    const set = new Map<string, number[]>();
    for (const p1 of gens) {
      for (const p2 of gens) {
        const c = range(degree);
        for (let k = 0; k < degree; k++) c[at(p2, at(p1, k))] = at(p1, at(p2, k));
        set.set(c.join(','), c);
      }
    }
    return this.normalClosure([...set.values()].map(afNew));
  }

  /** SymPy derived_series(): G, [G, G], ... until the series stabilizes. */
  derivedSeries(): PermutationGroupNode[] {
    const res: PermutationGroupNode[] = [this];
    let current: PermutationGroupNode = this;
    let nxt = this.derivedSubgroup();
    while (!current.isSubgroup(nxt)) {
      res.push(nxt);
      current = nxt;
      nxt = nxt.derivedSubgroup();
    }
    return res;
  }

  /** SymPy lower_central_series(): G, [G, G], [G, [G, G]], ... until the series stabilizes. */
  lowerCentralSeries(): PermutationGroupNode[] {
    const res: PermutationGroupNode[] = [this];
    let current: PermutationGroupNode = this;
    let nxt = this.commutator(this, current);
    while (!current.isSubgroup(nxt)) {
      res.push(nxt);
      current = nxt;
      nxt = this.commutator(this, current);
    }
    return res;
  }

  /** SymPy is_perfect: whether the group equals its derived subgroup. */
  get isPerfect(): boolean {
    return (this.known.isPerfect ??= this.equals(this.derivedSubgroup()));
  }

  /** SymPy is_solvable: whether the derived series ends in the trivial group. */
  get isSolvable(): boolean {
    if (this.known.isSolvable !== undefined) return this.known.isSolvable;
    if (this.order() % 2n !== 0n) return true;
    const ds = this.derivedSeries();
    return (this.known.isSolvable = at(ds, ds.length - 1).generators.every((g) => g.isIdentity));
  }

  /** SymPy is_polycyclic: a finite group is polycyclic exactly when it is solvable. */
  get isPolycyclic(): boolean {
    return this.isSolvable;
  }

  /** SymPy is_nilpotent: whether the lower central series ends in the trivial group. */
  get isNilpotent(): boolean {
    if (this.known.isNilpotent !== undefined) return this.known.isNilpotent;
    const lcs = this.lowerCentralSeries();
    const nil = at(lcs, lcs.length - 1).generators.every((g) => g.isIdentity);
    if (nil) this.known.isSolvable = true;
    return (this.known.isNilpotent = nil);
  }

  /** SymPy composition_series(): a composition series of a solvable group, from the derived series. */
  compositionSeries(): PermutationGroupNode[] {
    const der = this.derivedSeries();
    if (!at(der, der.length - 1).generators.every((g) => g.isIdentity)) throw new NotImplementedError('Group should be solvable');
    const series: PermutationGroupNode[] = [];
    for (let i = 0; i < der.length - 1; i++) {
      let H = at(der, i + 1);
      let upSeg: PermutationGroupNode[] = [];
      for (const g0 of at(der, i).generators) {
        let g = g0;
        const K = new PermutationGroupNode([g, ...H.generators]);
        const downSeg: PermutationGroupNode[] = [];
        for (const [p, e] of factorint(K.order() / H.order())) {
          for (let k = 0n; k < e; k++) {
            downSeg.push(new PermutationGroupNode([g, ...H.generators]));
            g = g.pow(p);
          }
        }
        upSeg = [...downSeg, ...upSeg];
        H = K;
      }
      upSeg[0] = at(der, i);
      series.push(...upSeg);
    }
    series.push(at(der, der.length - 1));
    return series;
  }

  /**
   * SymPy subgroup_search(prop, base, strong_gens, tests, init_subgroup): the
   * subgroup of the elements satisfying prop, by backtracking over a base
   * (prop must define a subgroup; tests prune partial base images).
   */
  subgroupSearch(prop: (g: Permutation) => boolean, baseIn?: readonly number[], strongGensIn?: readonly Permutation[], testsIn?: readonly ((computedWords: readonly Permutation[]) => boolean)[], initSubgroup?: PermutationGroupNode): PermutationGroupNode {
    const [base, strongGens] = baseIn === undefined ? this.schreierSimsIncremental() : [[...baseIn], [...(strongGensIn ?? this.strongGens)]];
    const baseLen = base.length;
    const degree = this.degree;
    const identity = this.identity;
    const ordering = [...baseOrdering(base, degree), degree, -1];
    const ord = (p: number): number => at(ordering, p);
    const distr = distributeGensByBase(base, strongGens);
    const { basicOrbits, transversals } = orbitsTransversalsFromBsgs(base, distr);
    const res = initSubgroup ?? new PermutationGroupNode([identity]);
    const tests = testsIn ?? base.map(() => () => true);
    let f = baseLen - 1;
    let l = baseLen - 1;
    const resBase0 = [...base];
    const [resBase1, resStrongGens] = res.schreierSimsIncremental(resBase0);
    let resBase = resBase1;
    let resDistr = distributeGensByBase(resBase, resStrongGens);
    const resGenerators = [...res.generators];
    let resBasicOrbitsInitBase = range(baseLen).map((i) => orbitList(degree, at(resDistr, i), at(resBase, i)));
    const getReps = (orbits: readonly Set<number>[]): number[] => orbits.map((orbit) => [...orbit].reduce((m, x) => (ord(x) < ord(m) ? x : m)));
    const orbitReps: number[][] = new Array<number[]>(baseLen).fill([]);
    let orbits = orbitsOf(degree, at(resDistr, f));
    orbitReps[f] = getReps(orbits).filter((x) => x !== base[f]);
    const c = new Array<number>(baseLen).fill(0);
    const u = new Array<Permutation>(baseLen).fill(identity);
    const sortedOrbits = basicOrbits.map((o) => [...o].sort((a, b) => ord(a) - ord(b)));
    const mu = new Array<number>(baseLen).fill(0);
    const nu = new Array<number>(baseLen).fill(0);
    const updateNu = (lv: number): void => {
      const tempIndex = at(basicOrbits, lv).length + 1 - at(resBasicOrbitsInitBase, lv).length;
      nu[lv] = tempIndex >= at(sortedOrbits, lv).length ? at(ordering, degree) : at(at(sortedOrbits, lv), tempIndex);
    };
    mu[l] = degree + 1;
    updateNu(l);
    const computedWords = new Array<Permutation>(baseLen).fill(identity);
    const img = (w: Permutation, p: number): number => at(w.arrayForm, p);
    for (;;) {
      while (l < baseLen - 1 && at(orbitReps, l).includes(img(at(computedWords, l), at(base, l))) && ord(at(mu, l)) < ord(img(at(computedWords, l), at(base, l))) && ord(img(at(computedWords, l), at(base, l))) < ord(at(nu, l)) && at(tests, l)(computedWords)) {
        const newPoint = img(at(computedWords, l), at(base, l));
        resBase[l] = newPoint;
        const newStabGens = stabilizerGens(degree, at(resDistr, l), newPoint);
        resDistr[l + 1] = newStabGens;
        orbits = orbitsOf(degree, newStabGens);
        orbitReps[l + 1] = getReps(orbits);
        l++;
        sortedOrbits[l] = at(basicOrbits, l).map((point) => img(at(computedWords, l - 1), point)).sort((a, b) => ord(a) - ord(b));
        // the candidate latest in the base ordering (degree + 1 has the ordering -1)
        const candidates = range(l).filter((i) => at(resBasicOrbitsInitBase, i).includes(at(base, l))).map((i) => img(at(computedWords, i), at(base, i)));
        mu[l] = at([degree + 1, ...candidates].sort((a, b) => ord(b) - ord(a)), 0);
        updateNu(l);
        c[l] = 0;
        const gamma = at(computedWords, l - 1).arrayForm.indexOf(at(at(sortedOrbits, l), 0));
        u[l] = getOrThrow(at(transversals, l), gamma);
        computedWords[l] = rmul(at(computedWords, l - 1), at(u, l));
      }
      const g = at(computedWords, l);
      const tempPoint = img(g, at(base, l));
      if (l === baseLen - 1 && ord(at(mu, l)) < ord(tempPoint) && ord(tempPoint) < ord(at(nu, l)) && at(orbitReps, l).includes(tempPoint) && at(tests, l)(computedWords) && prop(g)) {
        resGenerators.push(g);
        resBase = [...base];
        resStrongGens.push(g);
        resDistr = distributeGensByBase(resBase, resStrongGens);
        resBasicOrbitsInitBase = range(baseLen).map((i) => orbitList(degree, at(resDistr, i), at(resBase, i)));
        orbitReps[f] = getReps(orbits);
        l = f;
      }
      while (l >= 0 && at(c, l) === at(basicOrbits, l).length - 1) l--;
      if (l === -1) return new PermutationGroupNode(resGenerators);
      if (l < f) {
        f = l;
        c[l] = 0;
        orbitReps[f] = getReps(orbitsOf(degree, at(resDistr, f)));
        mu[l] = degree + 1;
        updateNu(l);
      }
      c[l] = at(c, l) + 1;
      const gamma = l === 0 ? at(at(sortedOrbits, l), at(c, l)) : at(computedWords, l - 1).arrayForm.indexOf(at(at(sortedOrbits, l), at(c, l)));
      u[l] = getOrThrow(at(transversals, l), gamma);
      computedWords[l] = l === 0 ? at(u, l) : rmul(at(computedWords, l - 1), at(u, l));
    }
  }

  /** SymPy centralizer(other): the elements commuting with every element of other (a group, a list or an element). */
  centralizer(other: PermutationGroupNode | readonly Permutation[] | Permutation): PermutationGroupNode {
    if (other instanceof Permutation) return this.centralizer(new PermutationGroupNode([other]));
    if (!(other instanceof PermutationGroupNode)) return this.centralizer(new PermutationGroupNode([...other]));
    if (other.isTrivial || this.isTrivial) return this;
    const degree = this.degree;
    const identity = this.identity;
    const orbits = other.orbits().sort((a, b) => b.size - a.size);
    const orbitReps: number[] = [];
    const orbitDescr = new Array<number>(degree).fill(0);
    let longBase: number[] = [];
    orbits.forEach((orbit, i) => {
      const o = [...orbit];
      orbitReps.push(at(o, 0));
      for (const point of o) orbitDescr[point] = i;
      longBase = [...longBase, ...o];
    });
    const [fullBase, strongGens] = this.schreierSimsIncremental(longBase);
    const distr = distributeGensByBase(fullBase, strongGens);
    let i = 0;
    for (i = 0; i < fullBase.length; i++) if (at(distr, i).length === 1 && at(at(distr, i), 0).equals(identity)) break;
    const base = fullBase.slice(0, i);
    const baseLen = i;
    let j = 0;
    for (j = 0; j < orbits.length; j++) if (at(orbits, j).has(at(base, baseLen - 1))) break;
    const transversals = orbits.slice(0, j + 1).map((_, k) => new Map(other.orbitTransversal(at(orbitReps, k), true)));
    const tests = base.map((b, l) => {
      if (orbitReps.includes(b)) return () => true;
      return (computedWords: readonly Permutation[]): boolean => {
        const g = at(computedWords, l).arrayForm;
        const repOrbIndex = at(orbitDescr, b);
        const rep = at(orbitReps, repOrbIndex);
        return at(g, b) === at(getOrThrow(at(transversals, repOrbIndex), b).arrayForm, at(g, rep));
      };
    });
    const prop = (g: Permutation): boolean => other.generators.every((gen) => rmul(g, gen).equals(rmul(gen, g)));
    return this.subgroupSearch(prop, base, strongGens, tests);
  }

  /** SymPy center(): the elements commuting with every element of the group. */
  center(): PermutationGroupNode {
    return (this.known.center ??= this.centralizer(this));
  }

  // ---- cosets and conjugacy ---------------------------------------------------------

  /** SymPy coset_transversal(H): a transversal of the right cosets of the subgroup H. */
  cosetTransversal(H: PermutationGroupNode): Permutation[] {
    if (!H.isSubgroup(this)) throw new RangeError('The argument must be a subgroup');
    if (H.order() === 1n) return this.elements;
    this.#schreierSims(H.base);
    const base = this.base;
    const ordering = baseOrdering(base, this.degree);
    const identity = new Permutation(this.degree - 1);
    const transversals = this.basicTransversals.map((t, l) => [...t.values()].sort((x, y) => at(ordering, at(x.arrayForm, at(base, l))) - at(ordering, at(y.arrayForm, at(base, l)))));
    const orbits = H.basicOrbits;
    const hStabs = H.basicStabilizers;
    const gStabs = this.basicStabilizers;
    const indices = hStabs.map((y, k) => at(gStabs, k).order() / y.order());
    const T = gStabs.length > hStabs.length ? at(gStabs, hStabs.length).elements : [identity];
    let tLen = T.length;
    for (let l = hStabs.length - 1; l > -1; l--) {
      const tNext: Permutation[] = [];
      outer: for (const u of at(transversals, l)) {
        if (u.equals(identity)) continue;
        const b = at(ordering, at(u.arrayForm, at(base, l)));
        for (const t of T) {
          const p = t.mul(u);
          if (at(orbits, l).every((h) => at(ordering, at(p.arrayForm, h)) >= b)) tNext.push(p);
          if (BigInt(tLen + tNext.length) === at(indices, l)) break outer;
        }
      }
      T.push(...tNext);
      tLen += tNext.length;
    }
    return [identity, ...T.filter((t) => !t.equals(identity))];
  }

  /** SymPy _coset_representative(g, H): the representative in coset_transversal(H) of the coset H*g. */
  #cosetRepresentative(g: Permutation, H: PermutationGroupNode): Permutation {
    if (H.order() === 1n) return g;
    // cosetTable has run coset_transversal, which recomputed the base starting with H's base
    const orbits = H.basicOrbits;
    const hTransversals = H.basicTransversals.map((t) => [...t.values()]);
    const transversals = this.basicTransversals.map((t) => [...t.values()]);
    const base = this.base;
    const ordering = baseOrdering(base, this.degree);
    const step = (l: number, xIn: Permutation): Permutation => {
      let x = xIn;
      const xa = x.arrayForm;
      const gamma = at(orbits, l).reduce((m, y) => (at(ordering, at(xa, y)) < at(ordering, at(xa, m)) ? y : m));
      const i = at(hTransversals, l).findIndex((h) => at(h.arrayForm, at(base, l)) === gamma);
      x = at(at(hTransversals, l), i).mul(x);
      if (l < orbits.length - 1) {
        const u = cast(at(transversals, l).find((v) => at(v.arrayForm, at(base, l)) === at(x.arrayForm, at(base, l))), Permutation);
        x = step(l + 1, x.mul(u.inverse())).mul(u);
      }
      return x;
    };
    return step(0, g);
  }

  /** SymPy coset_table(H): the standardized coset table of the subgroup H. */
  cosetTable(H: PermutationGroupNode): number[][] {
    if (!H.isSubgroup(this)) throw new RangeError('The argument must be a subgroup');
    const T = this.cosetTransversal(H);
    const n = T.length;
    const A = this.generators.flatMap((gen) => [gen, gen.inverse()]);
    const table = T.map((t) => A.map((x) => {
      const r = this.#cosetRepresentative(t.mul(x), H);
      return T.findIndex((q) => q.equals(r));
    }));
    let gamma = 1;
    // SymPy loops over product(range(n), A) and returns once gamma >= n - 1, which always happens
    // before the pairs run out (gamma grows with each new coset)
    for (let idx = 0; ; idx++) {
      {
        const alpha = Math.floor(idx / A.length);
        const a = idx % A.length;
        const beta = at(at(table, alpha), a);
        if (beta >= gamma) {
          if (beta > gamma) {
            for (let x = 0; x < A.length; x++) {
              const z = at(at(table, gamma), x);
              at(table, gamma)[x] = at(at(table, beta), x);
              at(table, beta)[x] = z;
              for (const row of table) {
                if (row[x] === beta) row[x] = gamma;
                else if (row[x] === gamma) row[x] = beta;
              }
            }
          }
          gamma++;
        }
        if (gamma >= n - 1) return table;
      }
    }
  }

  /** SymPy conjugacy_class(x): the set of the conjugates s*x*~s. */
  conjugacyClass(x: Permutation): Set<Permutation> {
    const newClass = new Map([[x.key, x]]);
    let last = [x];
    while (last.length) {
      const these = new Map<string, Permutation>();
      for (const y of last) {
        for (const s of this.generators) {
          const conjugated = s.mul(y).mul(s.inverse());
          if (!newClass.has(conjugated.key)) these.set(conjugated.key, conjugated);
        }
      }
      for (const y of last) newClass.set(y.key, y);
      last = [...these.values()];
    }
    return new Set(newClass.values());
  }

  /** SymPy conjugacy_classes(): the conjugacy classes, the identity's first. */
  conjugacyClasses(): Set<Permutation>[] {
    const identity = this.identity;
    const known = new Set([identity.key]);
    const classes = [permSet([identity])];
    for (const x of this.generate()) {
      if (known.has(x.key)) continue;
      const cls = this.conjugacyClass(x);
      classes.push(cls);
      for (const y of cls) known.add(y.key);
    }
    return classes;
  }
}

/** SymPy PermutationGroup(*gens): the group generated by the permutations (a list, or several arguments). */
export const PermutationGroup = /* @__PURE__ */ callableClass(PermutationGroupNode, (...input: ConstructorParameters<typeof PermutationGroupNode>): PermutationGroupNode => new PermutationGroupNode(...input));
export type PermutationGroup = PermutationGroupNode;

/** SymPy SymmetricPermutationGroup(deg): the symmetric group of degree deg without generators. */
export class SymmetricPermutationGroupNode extends ExtensionExpr {
  readonly degree: number;
  constructor(deg: number | bigint | Rational) {
    const d = deg instanceof Rational ? deg : Rational.of(BigInt(deg));
    super('SymmetricPermutationGroup', [d]);
    this.degree = Number(d.p);
  }

  withArgs(args: readonly Expr[]): Expr {
    return new SymmetricPermutationGroupNode(asRational(at(args, 0)));
  }

  /** SymPy order(): deg!. */
  order(): bigint {
    return factorial(this.degree);
  }

  /** SymPy identity: the identity permutation of the degree. */
  get identity(): Permutation {
    return afNew(range(this.degree));
  }

  /** SymPy i in G: a permutation of the same size. */
  contains(i: unknown): boolean {
    if (!(i instanceof Permutation)) throw new TypeError(`A SymmetricPermutationGroup contains only Permutations as elements, not elements of type ${typeof i}`);
    return i.size === this.degree;
  }
}
/** SymPy SymmetricPermutationGroup(deg). */
export const SymmetricPermutationGroup = /* @__PURE__ */ callableClass(SymmetricPermutationGroupNode, (deg: number | bigint | Rational): SymmetricPermutationGroupNode => new SymmetricPermutationGroupNode(deg));
export type SymmetricPermutationGroup = SymmetricPermutationGroupNode;

/** SymPy Coset(g, H, G, dir): the right (dir '+') or left (dir '-') coset of the subgroup H by g. */
export class Coset extends ExtensionExpr {
  constructor(g: Permutation, H: PermutationGroupNode, G?: PermutationGroupNode | SymmetricPermutationGroupNode, dir: '+' | '-' | Sym = '+') {
    let group = G;
    if (group !== undefined) {
      if (!H.isSubgroup(group)) throw new RangeError(`${H.toString()} must be a subgroup of ${group.toString()}.`);
      if (!group.contains(g)) throw new RangeError(`${g.toString()} must be an element of ${group.toString()}.`);
    } else {
      if (g.size !== H.degree) throw new RangeError(`The size of the permutation ${g.toString()} and the degree of the permutation group ${H.toString()} should be matching `);
      group = new SymmetricPermutationGroupNode(g.size);
    }
    const d = dir instanceof Sym ? dir : new Sym(dir);
    if (d.name !== '+' && d.name !== '-') throw new RangeError(`dir must be one of '+' or '-' not ${d.name}`);
    super('Coset', [g, H, group, d]);
  }

  withArgs(args: readonly Expr[]): Expr {
    const [g, H, G, d] = args;
    return new Coset(cast(g, Permutation), cast(H, PermutationGroupNode), G instanceof PermutationGroupNode ? G : cast(G, SymmetricPermutationGroupNode), cast(d, Sym));
  }

  get #dir(): string {
    return cast(at(this.args, 3), Sym).name;
  }

  /** SymPy is_left_coset: dir is '-'. */
  get isLeftCoset(): boolean {
    return this.#dir === '-';
  }

  /** SymPy is_right_coset: dir is '+'. */
  get isRightCoset(): boolean {
    return this.#dir === '+';
  }

  /** SymPy as_list(): the elements h*g (right coset) or g*h (left coset). */
  asList(): Permutation[] {
    const g = cast(at(this.args, 0), Permutation);
    const H = cast(at(this.args, 1), PermutationGroupNode);
    return H.elements.map((h) => (this.isRightCoset ? h.mul(g) : g.mul(h)));
  }
}
