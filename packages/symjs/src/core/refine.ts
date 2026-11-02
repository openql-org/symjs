// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file SymPy's assumption system (sympy.assumptions): the predicates Q,
 * ask, refine, user handlers and the global assumptions.
 *
 * An applied predicate such as Q.positive(x) is an expression, so it
 * combines with And, Or and Not. The assumptions are brought into
 * disjunctive normal form; in every branch the facts are closed under the
 * implications between predicates (Q.prime implies Q.integer and
 * Q.positive, ...). The predicates the symbols carry (real, positive,
 * integer, ...) are then applied by rebuilding the expression with symbols
 * carrying those assumptions, and the other predicates (rational, even,
 * prime, algebraic, ...) by handlers on the structure of the expression.
 */

import type { Assumptions, ExprLike } from './nodes';
import { Add, BoolAtom, Constant, Expr, ExtensionExpr, Fn, Float, Mul, Pow, Rational, Rel, S, Special, Sym } from './nodes';
import { add, mul, pow, sympify } from './ops';
import { mapBottomUp, xreplace } from './traverse';
import { isIntegerQ, isNegative, isNonNegative, isNonZero, isPositive, isReal, isZero } from './assumptions';
import { BoolOp, and, not, or } from './boolalg';
import type { Truth } from './truth';
import { at, getOrThrow } from './guard';
import { SympifyError } from './errors';

/** Predicate names of Q (SymPy Q.<name>). */
export type PredicateName =
  | 'real'
  | 'extended_real'
  | 'positive'
  | 'negative'
  | 'nonnegative'
  | 'nonpositive'
  | 'zero'
  | 'nonzero'
  | 'extended_positive'
  | 'extended_negative'
  | 'extended_nonnegative'
  | 'extended_nonpositive'
  | 'extended_nonzero'
  | 'positive_infinite'
  | 'negative_infinite'
  | 'integer'
  | 'noninteger'
  | 'rational'
  | 'irrational'
  | 'algebraic'
  | 'transcendental'
  | 'even'
  | 'odd'
  | 'prime'
  | 'composite'
  | 'complex'
  | 'imaginary'
  | 'hermitian'
  | 'antihermitian'
  | 'finite'
  | 'infinite'
  | 'commutative'
  | 'is_true'
  | 'eq'
  | 'ne'
  | 'gt'
  | 'ge'
  | 'lt'
  | 'le'
  | 'square'
  | 'symmetric'
  | 'invertible'
  | 'singular'
  | 'orthogonal'
  | 'unitary'
  | 'positive_definite'
  | 'upper_triangular'
  | 'lower_triangular'
  | 'triangular'
  | 'unit_triangular'
  | 'diagonal'
  | 'fullrank'
  | 'normal'
  | 'integer_elements'
  | 'real_elements'
  | 'complex_elements';

/** A predicate applied to arguments, such as Q.positive(x) (SymPy AppliedPredicate). */
export class AppliedPredicate extends ExtensionExpr {
  constructor(
    /** The predicate name (positive for Q.positive). */
    readonly predicate: string,
    args: readonly Expr[],
  ) {
    super(`Q.${predicate}`, args);
  }
  withArgs(args: readonly Expr[]): Expr {
    return new AppliedPredicate(this.predicate, args);
  }
  /** The (first) argument. */
  get arg(): Expr {
    return at(this.args, 0);
  }
  override printLatex(print: (e: Expr) => string): string {
    return `Q_{\\text{${this.predicate.replace(/_/g, '\\_')}}}\\left(${this.args.map(print).join(', ')}\\right)`;
  }
  /** Conjunction (SymPy &). */
  and(...others: (Expr | readonly Expr[])[]): Expr {
    return and(this, ...others.flat());
  }
  /** Disjunction (SymPy |). */
  or(...others: Expr[]): Expr {
    return or(this, ...others);
  }
  /** Negation (SymPy ~). */
  not(): Expr {
    return not(this);
  }
}

/**
 * A handler deciding a predicate: true, false or 'unknown' (SymPy
 * register_handler); expr is the first argument, args all of them.
 */
export type PredicateHandler = (expr: Expr, assumptions: Expr, args: readonly Expr[]) => Truth;

/** A predicate such as Q.positive; calling it applies it (SymPy Predicate). */
export interface Predicate {
  (...args: ExprLike[]): AppliedPredicate;
  /** The name (positive for Q.positive). */
  readonly predicateName: string;
}

const handlers = new Map<string, PredicateHandler[]>();

/**
 * A predicate with the given name (SymPy Predicate); handlers added with
 * registerHandler decide it in ask.
 */
export function Predicate(name: string, handler?: PredicateHandler): Predicate {
  const f = (...args: ExprLike[]): AppliedPredicate => new AppliedPredicate(name, args.map((a) => sympify(a)));
  Object.defineProperty(f, 'predicateName', { value: name });
  Object.defineProperty(f, 'toString', { value: () => `Q.${name}` });
  if (handler) registerHandler(name, handler);
  // oxlint-disable-next-line typescript/no-unsafe-type-assertion -- predicateName was added above with Object.defineProperty (non-enumerable, read-only)
  return f as Predicate;
}

const BUILTIN = [
  'real', 'extended_real', 'positive', 'negative', 'nonnegative', 'nonpositive', 'zero', 'nonzero',
  'extended_positive', 'extended_negative', 'extended_nonnegative', 'extended_nonpositive', 'extended_nonzero',
  'positive_infinite', 'negative_infinite', 'integer', 'noninteger', 'rational', 'irrational', 'algebraic',
  'transcendental', 'even', 'odd', 'prime', 'composite', 'complex', 'imaginary', 'hermitian', 'antihermitian',
  'finite', 'infinite', 'commutative', 'is_true', 'eq', 'ne', 'gt', 'ge', 'lt', 'le', 'square', 'symmetric',
  'invertible', 'singular', 'orthogonal', 'unitary', 'positive_definite', 'upper_triangular', 'lower_triangular',
  'triangular', 'unit_triangular', 'diagonal', 'fullrank', 'normal', 'integer_elements', 'real_elements',
  'complex_elements',
] as const satisfies readonly PredicateName[];

const predicates: Record<string, Predicate> = Object.fromEntries(BUILTIN.map((n) => [n, Predicate(n)]));

/** SymPy Q: the assumption predicates (Q.positive(x), Q.even(n), Q.gt(x, y), ...). */
// oxlint-disable-next-line typescript/no-unsafe-type-assertion -- predicates holds an entry for every name in BUILTIN, which covers PredicateName (checked by satisfies above)
export const Q = predicates as { readonly [K in PredicateName]: Predicate } & { readonly [name: string]: Predicate | undefined };

/**
 * Adds a handler for a predicate (SymPy register_handler); a predicate not
 * in Q is added to it. The handler is tried before the built-in rules.
 */
export function registerHandler(key: string | Predicate, handler: PredicateHandler): void {
  const name = typeof key === 'string' ? key : key.predicateName;
  handlers.set(name, [...(handlers.get(name) ?? []), handler]);
  if (!(name in predicates)) predicates[name] = Predicate(name);
}

/** Removes a handler added by registerHandler (SymPy remove_handler). */
export function removeHandler(key: string | Predicate, handler: PredicateHandler): void {
  const name = typeof key === 'string' ? key : key.predicateName;
  handlers.set(name, (handlers.get(name) ?? []).filter((h) => h !== handler));
}

/** Assumptions: a boolean expression of predicates, a list of them (a conjunction), or true. */
export type Assumption = Expr | readonly Expr[] | boolean;

/** A set of assumptions in force for ask and refine (SymPy AssumptionsContext). */
export class AssumptionsContext {
  private readonly items = new Map<string, Expr>();
  /** Adds assumptions. */
  add(...assumptions: Expr[]): void {
    for (const a of assumptions) this.items.set(a.key, a);
  }
  /** Removes assumptions. */
  remove(...assumptions: Expr[]): void {
    for (const a of assumptions) this.items.delete(a.key);
  }
  /** Removes every assumption. */
  clear(): void {
    this.items.clear();
  }
  /** The assumption is present. */
  has(assumption: Expr): boolean {
    return this.items.has(assumption.key);
  }
  get size(): number {
    return this.items.size;
  }
  [Symbol.iterator](): IterableIterator<Expr> {
    return this.items.values();
  }
  /** The conjunction of the assumptions. */
  toExpr(): Expr {
    return and(...this.items.values());
  }
  toString(): string {
    return `AssumptionsContext({${[...this.items.values()].map((e) => e.toString()).join(', ')}})`;
  }
}

/** The assumptions used by every ask and refine (SymPy global_assumptions). */
export const globalAssumptions: AssumptionsContext = new AssumptionsContext();

/**
 * Runs body with the assumptions added to the global assumptions (SymPy
 * `with assuming(...)`), and returns its result.
 */
export function assuming<T>(assumptions: Assumption, body: () => T): T {
  const added = asList(assumptions).filter((a) => !globalAssumptions.has(a));
  globalAssumptions.add(...added);
  try {
    return body();
  } finally {
    globalAssumptions.remove(...added);
  }
}

// ---- facts -------------------------------------------------------------------------------

type Literal = readonly [name: string, value: boolean];

/** Implications between predicates on the same argument. */
const IMPLIES: Readonly<Record<string, readonly Literal[]>> = {
  positive: [['real', true], ['nonzero', true], ['nonnegative', true], ['extended_positive', true], ['negative', false], ['nonpositive', false], ['zero', false]],
  negative: [['real', true], ['nonzero', true], ['nonpositive', true], ['extended_negative', true], ['positive', false], ['nonnegative', false], ['zero', false]],
  zero: [['real', true], ['even', true], ['nonnegative', true], ['nonpositive', true], ['positive', false], ['negative', false], ['nonzero', false]],
  nonzero: [['real', true], ['extended_nonzero', true], ['zero', false]],
  nonnegative: [['real', true], ['extended_nonnegative', true], ['negative', false]],
  nonpositive: [['real', true], ['extended_nonpositive', true], ['positive', false]],
  even: [['integer', true], ['odd', false]],
  odd: [['integer', true], ['nonzero', true], ['even', false]],
  prime: [['integer', true], ['positive', true], ['composite', false]],
  composite: [['integer', true], ['positive', true], ['prime', false]],
  integer: [['rational', true], ['noninteger', false]],
  noninteger: [['real', true], ['integer', false]],
  rational: [['real', true], ['algebraic', true], ['irrational', false]],
  irrational: [['real', true], ['rational', false]],
  algebraic: [['complex', true], ['transcendental', false]],
  transcendental: [['complex', true], ['algebraic', false]],
  real: [['complex', true], ['extended_real', true], ['hermitian', true], ['imaginary', false]],
  imaginary: [['complex', true], ['antihermitian', true], ['real', false]],
  complex: [['finite', true], ['commutative', true]],
  finite: [['infinite', false]],
  infinite: [['finite', false]],
  extended_real: [['commutative', true]],
  extended_positive: [['extended_real', true], ['extended_nonzero', true], ['extended_nonnegative', true], ['extended_negative', false], ['extended_nonpositive', false]],
  extended_negative: [['extended_real', true], ['extended_nonzero', true], ['extended_nonpositive', true], ['extended_positive', false], ['extended_nonnegative', false]],
  extended_nonzero: [['extended_real', true]],
  extended_nonnegative: [['extended_real', true], ['extended_negative', false]],
  extended_nonpositive: [['extended_real', true], ['extended_positive', false]],
  positive_infinite: [['infinite', true], ['extended_positive', true]],
  negative_infinite: [['infinite', true], ['extended_negative', true]],
  orthogonal: [['invertible', true], ['square', true], ['unitary', true]],
  unitary: [['invertible', true], ['square', true], ['normal', true]],
  positive_definite: [['invertible', true], ['square', true]],
  invertible: [['square', true], ['fullrank', true], ['singular', false]],
  singular: [['square', true], ['invertible', false]],
  diagonal: [['upper_triangular', true], ['lower_triangular', true], ['symmetric', true], ['normal', true]],
  upper_triangular: [['triangular', true]],
  lower_triangular: [['triangular', true]],
  unit_triangular: [['triangular', true]],
  symmetric: [['square', true]],
  integer_elements: [['real_elements', true]],
  real_elements: [['complex_elements', true]],
};

/** The literals implied by one literal (with the contrapositives of IMPLIES). */
const consequences = (() => {
  const out = new Map<string, Literal[]>();
  const push = (from: string, l: Literal) => out.set(from, [...(out.get(from) ?? []), l]);
  for (const [a, ls] of Object.entries(IMPLIES)) {
    for (const [b, v] of ls) {
      push(`${a}:true`, [b, v]);
      push(`${b}:${String(!v)}`, [a, false]);
    }
  }
  return out;
})();

/** The facts known about one argument: predicate name -> value. */
type Facts = Map<string, boolean>;
/** The facts of one branch of the assumptions, by argument key. */
interface Branch {
  readonly facts: Map<string, { expr: Expr; facts: Facts }>;
  readonly forward: Map<string, Sym>;
}

class Inconsistent extends RangeError {}

function addFact(facts: Facts, name: string, value: boolean): void {
  const todo: Literal[] = [[name, value]];
  for (let lit = todo.pop(); lit !== undefined; lit = todo.pop()) {
    const [n, v] = lit;
    const cur = facts.get(n);
    if (cur === v) continue;
    if (cur !== undefined) throw new Inconsistent('inconsistent assumptions');
    facts.set(n, v);
    todo.push(...(consequences.get(`${n}:${String(v)}`) ?? []));
  }
}

const asList = (a: Assumption): Expr[] => (typeof a === 'boolean' ? (a ? [] : [S.false]) : a instanceof Expr ? [a] : [...a]);

/** The assumptions in disjunctive normal form: a list of conjunctions of literals. */
function dnf(e: Expr, negated = false): (readonly [AppliedPredicate, boolean])[][] {
  if (e instanceof BoolAtom) return e.value !== negated ? [[]] : [];
  if (e instanceof BoolOp) {
    if (e.op === 'Not') return dnf(at(e.args, 0), !negated);
    const isAnd = (e.op === 'And') !== negated;
    if (e.op !== 'And' && e.op !== 'Or') return [[]];
    const parts = e.args.map((a) => dnf(a, negated));
    if (!isAnd) return parts.flat();
    let acc: (readonly [AppliedPredicate, boolean])[][] = [[]];
    for (const p of parts) {
      acc = acc.flatMap((c) => p.map((d) => [...c, ...d]));
      if (acc.length > 256) return [[]];
    }
    return acc;
  }
  if (e instanceof AppliedPredicate) return [[[e, !negated]]];
  // a relation as an assumption is not used (SymPy ask(Q.positive(x), x > 0) is None)
  return [[]];
}

/** The branches of the assumptions with their facts closed under the implications. */
function branches(assumptions: Assumption): Branch[] {
  const all = and(...asList(assumptions), ...globalAssumptions);
  const out: Branch[] = [];
  for (const conj of dnf(all)) {
    const facts = new Map<string, { expr: Expr; facts: Facts }>();
    try {
      for (const [ap, v] of conj) {
        const rel = relationFact(ap, v);
        if (rel) {
          const entry = facts.get(rel[0].key) ?? { expr: rel[0], facts: new Map<string, boolean>() };
          addFact(entry.facts, rel[1], rel[2]);
          facts.set(rel[0].key, entry);
          continue;
        }
        if (ap.args.length !== 1) continue;
        const entry = facts.get(ap.arg.key) ?? { expr: ap.arg, facts: new Map<string, boolean>() };
        addFact(entry.facts, ap.predicate, v);
        facts.set(ap.arg.key, entry);
      }
    } catch (err) {
      if (err instanceof Inconsistent) continue;
      throw err;
    }
    out.push({ facts, forward: symbolsWithFacts(facts) });
  }
  if (!out.length) throw new RangeError('inconsistent assumptions');
  return out;
}

/** Q.gt(a, b) as a fact about a - b (Q.positive(a - b)). */
function relationFact(p: AppliedPredicate, v: boolean): [Expr, string, boolean] | undefined {
  if (p.args.length !== 2) return undefined;
  const d = add(at(p.args, 0), mul(-1, at(p.args, 1)));
  switch (p.predicate) {
    case 'gt':
      return [d, 'positive', v];
    case 'lt':
      return [d, 'negative', v];
    case 'ge':
      return [d, 'nonnegative', v];
    case 'le':
      return [d, 'nonpositive', v];
    case 'eq':
      return [d, 'zero', v];
    case 'ne':
      return [d, 'zero', !v];
    default:
      return undefined;
  }
}

/** Symbols rebuilt with the assumptions their facts imply. */
function symbolsWithFacts(facts: Branch['facts']): Map<string, Sym> {
  const forward = new Map<string, Sym>();
  for (const [k, { expr, facts: f }] of facts) {
    if (!(expr instanceof Sym)) continue;
    const a: { -readonly [K in keyof Assumptions]: Assumptions[K] } = {};
    if (f.get('real') === true) a.real = true;
    if (f.get('positive') === true) a.positive = true;
    if (f.get('negative') === true) a.negative = true;
    if (f.get('nonnegative') === true) a.nonnegative = true;
    if (f.get('nonpositive') === true) a.nonpositive = true;
    if (f.get('integer') === true) a.integer = true;
    if (f.get('zero') === false || f.get('nonzero') === true) a.zero = false;
    if (f.get('commutative') === true) a.commutative = true;
    if (!Object.keys(a).length) continue;
    const s = new Sym(expr.name, { ...expr.assumptions, ...a });
    if (s.key !== expr.key) forward.set(k, s);
  }
  return forward;
}

/** Rebuild every node so that the assumptions take effect. */
function reevaluate(e: Expr, forward: Map<string, Sym>): Expr {
  if (!forward.size) return e;
  const pairs = [...forward].flatMap(([k, s]) => {
    const a = findByKey(e, k);
    return a ? [[a, s] as const] : [];
  });
  return pairs.length ? xreplace(e, pairs) : e;
}

function findByKey(e: Expr, key: string): Expr | undefined {
  if (e.key === key) return e;
  for (const a of e.args) {
    const r = findByKey(a, key);
    if (r) return r;
  }
  return undefined;
}

// ---- deciding a predicate ----------------------------------------------------------------

type Tri = boolean | undefined;
const tri = (v: boolean | undefined | null): Tri => (v === null ? undefined : v);
const notTri = (v: Tri): Tri => (v === undefined ? undefined : !v);
const allTri = (xs: readonly Expr[], f: (e: Expr) => Tri): Tri => {
  let unknown = false;
  for (const x of xs) {
    const r = f(x);
    if (r === false) return false;
    if (r === undefined) unknown = true;
  }
  return unknown ? undefined : true;
};
const isInt = (e: Expr): e is Rational => e instanceof Rational && e.q === 1n;
const isConst = (e: Expr, ...names: string[]): boolean => e instanceof Constant && names.includes(e.name);

/** n is prime (deterministic Miller-Rabin for n < 3.3e24, strong probable prime above). */
function isPrimeBig(n: bigint): boolean {
  if (n < 2n) return false;
  const small = [2n, 3n, 5n, 7n, 11n, 13n, 17n, 19n, 23n, 29n, 31n, 37n, 41n];
  for (const p of small) if (n % p === 0n) return n === p;
  let d = n - 1n;
  let s = 0;
  while (d % 2n === 0n) {
    d /= 2n;
    s++;
  }
  const powmod = (b0: bigint, e0: bigint): bigint => {
    let r = 1n;
    let b = b0 % n;
    let e = e0;
    while (e > 0n) {
      if (e & 1n) r = (r * b) % n;
      b = (b * b) % n;
      e >>= 1n;
    }
    return r;
  };
  outer: for (const a of small) {
    let x = powmod(a, d);
    if (x === 1n || x === n - 1n) continue;
    for (let i = 1; i < s; i++) {
      x = (x * x) % n;
      if (x === n - 1n) continue outer;
    }
    return false;
  }
  return true;
}

class Decider {
  constructor(
    readonly branch: Branch,
    readonly assumptions: Expr,
  ) {}

  /** The predicate on e: true, false or undefined (unknown). */
  q(name: string, e: Expr): Tri {
    const known = this.branch.facts.get(e.key)?.facts.get(name);
    if (known !== undefined) return known;
    for (const h of handlers.get(name) ?? []) {
      const r = h(e, this.assumptions, [e]);
      if (r !== 'unknown') return r;
    }
    // predicates refer to each other (integer <-> rational, real <-> imaginary): a query in progress is unknown
    const k = `${name}|${e.key}`;
    if (this.memo.has(k)) return this.memo.get(k) ?? undefined;
    this.memo.set(k, null);
    const r = this.builtin(name, e);
    this.memo.set(k, r);
    return r;
  }
  private readonly memo = new Map<string, Tri | null>();

  /** e with the symbol facts applied. */
  private re(e: Expr): Expr {
    return reevaluate(e, this.branch.forward);
  }

  private builtin(name: string, e: Expr): Tri {
    switch (name) {
      case 'real':
        if (e instanceof Special) return false;
        if (isConst(e, 'I')) return false;
        if (this.q('imaginary', e) === true) return false;
        return tri(isReal(this.re(e))) ?? (this.q('rational', e) === true ? true : undefined);
      case 'extended_real':
        if (e instanceof Special) return e.name === 'oo' || e.name === '-oo';
        return this.q('real', e) === true ? true : undefined;
      case 'positive':
        if (e instanceof Special) return false;
        return this.ext(tri(isPositive(this.re(e))), e) ?? this.trichotomy(e, 'negative');
      case 'negative':
        if (e instanceof Special) return false;
        return this.ext(tri(isNegative(this.re(e))), e) ?? this.trichotomy(e, 'positive');
      case 'nonnegative':
        if (e instanceof Special) return false;
        return this.ext(tri(isNonNegative(this.re(e))), e);
      case 'nonpositive': {
        if (e instanceof Special) return false;
        const p = this.q('positive', e);
        if (p === true) return false;
        if (p === false && this.q('real', e) === true) return true;
        return this.q('real', e) === false ? false : undefined;
      }
      case 'zero':
        if (e instanceof Special) return false;
        return tri(isZero(this.re(e))) ?? (this.q('nonzero', e) === true || this.q('real', e) === false ? false : undefined);
      case 'nonzero': {
        if (e instanceof Special) return false;
        if (this.q('real', e) === false) return false;
        const z = tri(isNonZero(this.re(e)));
        return z !== undefined ? z && this.q('real', e) === true ? true : z ? undefined : false : this.q('positive', e) === true || this.q('negative', e) === true || this.q('odd', e) === true ? true : undefined;
      }
      case 'extended_positive':
        return isConst(e) || !(e instanceof Special) ? this.q('positive', e) === true ? true : this.q('extended_real', e) === true && this.q('extended_nonpositive', e) === true ? false : undefined : e.name === 'oo';
      case 'extended_negative':
        return e instanceof Special ? e.name === '-oo' : this.q('negative', e) === true ? true : undefined;
      case 'extended_nonnegative':
        return e instanceof Special ? e.name === 'oo' : this.q('nonnegative', e) === true ? true : undefined;
      case 'extended_nonpositive':
        return e instanceof Special ? e.name === '-oo' : this.q('nonpositive', e) === true ? true : undefined;
      case 'extended_nonzero':
        return e instanceof Special ? e.name === 'oo' || e.name === '-oo' : this.q('nonzero', e) === true ? true : undefined;
      case 'positive_infinite':
        return e instanceof Special ? e.name === 'oo' : this.q('finite', e) === true ? false : undefined;
      case 'negative_infinite':
        return e instanceof Special ? e.name === '-oo' : this.q('finite', e) === true ? false : undefined;
      case 'integer':
        if (e instanceof Special || isConst(e, 'pi', 'E', 'I', 'GoldenRatio', 'TribonacciConstant')) return false;
        if (e instanceof Rational) return e.q === 1n;
        return tri(isIntegerQ(this.re(e))) ?? (this.q('rational', e) === false ? false : undefined);
      case 'noninteger': {
        const i = this.q('integer', e);
        return i === true ? false : i === false && this.q('real', e) === true ? true : undefined;
      }
      case 'rational':
        return this.rational(e);
      case 'irrational': {
        const r = this.q('rational', e);
        if (r === true) return false;
        const real = this.q('real', e);
        if (real === false) return false;
        return r === false && real === true ? true : undefined;
      }
      case 'algebraic':
        return this.algebraic(e);
      case 'transcendental': {
        const a = this.q('algebraic', e);
        return a === true ? false : a === false && this.q('complex', e) === true ? true : undefined;
      }
      case 'even':
        return this.parity(e, 0n);
      case 'odd':
        return this.parity(e, 1n);
      case 'prime':
        return this.prime(e);
      case 'composite': {
        if (isInt(e)) return e.p > 1n && !isPrimeBig(e.p);
        if (this.q('integer', e) === false || this.q('positive', e) === false) return false;
        if (this.q('prime', e) === true) return false;
        return undefined;
      }
      case 'complex':
        return this.complex(e);
      case 'imaginary':
        return this.imaginary(e);
      case 'hermitian':
        if (this.q('real', e) === true) return true;
        return this.q('imaginary', e) === true && this.q('nonzero', mul(-1, S.I, e)) === true ? false : undefined;
      case 'antihermitian':
        if (this.q('imaginary', e) === true) return true;
        if (this.q('zero', e) === true) return true;
        return this.q('real', e) === true && this.q('zero', e) === false ? false : undefined;
      case 'finite':
        return this.finite(e);
      case 'infinite':
        return notTri(this.q('finite', e));
      case 'commutative':
        return this.re(e).isCommutative ? true : undefined;
      case 'is_true':
        return e instanceof BoolAtom ? e.value : undefined;
      default:
        return undefined;
    }
  }

  /** A real number that is neither zero nor of the other sign has this sign. */
  private trichotomy(e: Expr, other: 'positive' | 'negative'): Tri {
    return this.q('real', e) === true && this.q('zero', e) === false && this.q(other, e) === false ? true : undefined;
  }

  /** A real-valued predicate: false for a non-real argument. */
  private ext(v: Tri, e: Expr): Tri {
    if (v !== undefined) return v;
    return this.q('real', e) === false ? false : undefined;
  }

  private rational(e: Expr): Tri {
    if (e instanceof Rational) return true;
    if (e instanceof Float) return undefined;
    if (e instanceof Special) return false;
    if (e instanceof Constant) return e.name === 'EulerGamma' || e.name === 'Catalan' ? undefined : false;
    if (e instanceof Sym) {
      if (this.q('integer', e) === true) return true;
      return this.q('real', e) === false ? false : undefined;
    }
    if (e instanceof Add || e instanceof Mul) {
      const rs = e.args.map((a) => this.q('rational', a));
      if (rs.every((r) => r === true)) return true;
      const irr = rs.filter((r) => r === false).length;
      if (irr === 1 && rs.filter((r) => r === undefined).length === 0) {
        const bad = at(e.args, rs.indexOf(false));
        if (this.q('irrational', bad) !== true && this.q('real', bad) !== true) return undefined;
        if (e instanceof Add) return false;
        return e.args.every((a, i) => i === rs.indexOf(false) || this.q('nonzero', a) === true) ? false : undefined;
      }
      if (this.q('real', e) === false) return false;
      return undefined;
    }
    if (e instanceof Pow) {
      const [b, x] = e.args;
      if (isConst(b, 'E')) return this.q('rational', x) === true && this.q('nonzero', x) === true ? false : undefined;
      if (this.q('integer', x) === true && this.q('rational', b) === true) return this.q('nonzero', b) === true || this.q('nonnegative', x) === true ? true : undefined;
      if (b instanceof Rational && x instanceof Rational) return b.isNegative ? false : false; // an unevaluated rational power of a rational is irrational
      if (this.q('rational', x) === true && this.q('algebraic', b) === true && this.q('rational', b) === false && this.q('positive', b) === true) {
        return undefined;
      }
      return undefined;
    }
    if (e instanceof Fn) {
      const a = e.args[0];
      if (!a) return undefined;
      const transcendentalAtNonzeroRational = ['exp', 'sin', 'cos', 'tan', 'cot', 'asin', 'atan', 'acot', 'sinh', 'cosh', 'tanh', 'asinh', 'atanh'];
      if (transcendentalAtNonzeroRational.includes(e.name) && this.q('rational', a) === true && this.q('nonzero', a) === true) return false;
      if (e.name === 'log' && this.q('rational', a) === true && this.q('positive', a) === true) return false;
      if (e.name === 'acos' && this.q('rational', a) === true) return false;
      return undefined;
    }
    return undefined;
  }

  private algebraic(e: Expr): Tri {
    if (e instanceof Rational) return true;
    if (e instanceof Float || e instanceof Special) return e instanceof Special ? false : undefined;
    if (e instanceof Constant) return e.name === 'I' || e.name === 'GoldenRatio' || e.name === 'TribonacciConstant' ? true : e.name === 'pi' || e.name === 'E' ? false : undefined;
    if (e instanceof Sym) return this.q('rational', e) === true ? true : undefined;
    if (e instanceof Add || e instanceof Mul) {
      const rs = e.args.map((a) => this.q('algebraic', a));
      if (rs.every((r) => r === true)) return true;
      if (rs.filter((r) => r === false).length === 1 && !rs.includes(undefined)) {
        if (e instanceof Add) return false;
        const k = rs.indexOf(false);
        return e.args.every((a, i) => i === k || this.q('nonzero', a) === true) ? false : undefined;
      }
      return undefined;
    }
    if (e instanceof Pow) {
      const [b, x] = e.args;
      if (isConst(b, 'E')) return this.q('algebraic', x) === true && this.q('nonzero', x) === true ? false : undefined;
      if (this.q('rational', x) === true) return this.q('algebraic', b);
      return undefined;
    }
    if (e instanceof Fn) {
      const a = e.args[0];
      if (!a) return undefined;
      if (['exp', 'sin', 'cos', 'tan', 'cot', 'asin', 'acos', 'atan', 'acot'].includes(e.name) && this.q('algebraic', a) === true && this.q('nonzero', a) === true) return false;
      if (e.name === 'log' && this.q('algebraic', a) === true && this.q('nonzero', add(a, -1)) === true) return false;
      return undefined;
    }
    return undefined;
  }

  /** even (r = 0) or odd (r = 1). */
  private parity(e: Expr, r: bigint): Tri {
    if (e instanceof Rational) return e.q === 1n ? ((e.p % 2n) + 2n) % 2n === r : false;
    const integer = this.q('integer', e);
    if (integer === false) return false;
    const other = r === 0n ? 'odd' : 'even';
    if (e instanceof Sym) {
      const o = this.branch.facts.get(e.key)?.facts.get(other);
      return o === true ? false : undefined;
    }
    const par = (a: Expr): bigint | undefined => (this.q('even', a) === true ? 0n : this.q('odd', a) === true ? 1n : undefined);
    if (e instanceof Mul) {
      if (!e.args.every((a) => this.q('integer', a) === true)) return undefined;
      const ps = e.args.map(par);
      if (ps.includes(0n)) return r === 0n;
      if (ps.every((p) => p === 1n)) return r === 1n;
      return undefined;
    }
    if (e instanceof Add) {
      if (!e.args.every((a) => this.q('integer', a) === true)) return undefined;
      let sum = 0n;
      for (const a of e.args) {
        const p = par(a);
        if (p === undefined) return undefined;
        sum += p;
      }
      return sum % 2n === r;
    }
    if (e instanceof Pow) {
      const [b, x] = e.args;
      if (this.q('integer', b) === true && this.q('positive', x) === true && this.q('integer', x) === true) {
        const p = par(b);
        return p === undefined ? undefined : p === r;
      }
      return undefined;
    }
    if (e instanceof Fn && e.name === 'abs') {
      const p = par(at(e.args, 0));
      return p === undefined ? undefined : p === r;
    }
    if (integer === true) {
      const o = this.branch.facts.get(e.key)?.facts.get(other);
      if (o !== undefined) return !o;
    }
    return undefined;
  }

  private prime(e: Expr): Tri {
    if (e instanceof Rational) return e.q === 1n && isPrimeBig(e.p);
    if (this.q('integer', e) === false) return false;
    if (this.q('positive', e) === false) return false;
    if (e instanceof Mul) {
      // SymPy PrimePredicate for Mul: a composite number factor of an integer product
      if (!e.args.every((a) => this.q('integer', a) === true)) return undefined;
      return e.args.some((a) => isInt(a) && a.p > 1n && !isPrimeBig(a.p)) ? false : undefined;
    }
    if (e instanceof Pow) {
      const [b, x] = e.args;
      if (this.q('integer', b) === true && this.q('integer', x) === true && isInt(x) && x.p > 1n) return false;
      return undefined;
    }
    if (this.q('even', e) === true) {
      return this.q('zero', add(e, -2)) === true ? true : this.q('zero', add(e, -2)) === false ? false : undefined;
    }
    return undefined;
  }

  private complex(e: Expr): Tri {
    if (e instanceof Rational || e instanceof Float || e instanceof Constant) return true;
    if (e instanceof Special) return false;
    if (this.q('real', e) === true || this.q('imaginary', e) === true) return true;
    if (e instanceof Add || e instanceof Mul) return allTri(e.args, (a) => this.q('complex', a)) === true ? true : this.q('infinite', e) === true ? false : undefined;
    if (e instanceof Pow) {
      const [b, x] = e.args;
      if (this.q('complex', b) === true && this.q('complex', x) === true && (this.q('nonzero', b) === true || this.q('nonnegative', x) === true || isConst(b, 'E'))) return true;
      return undefined;
    }
    if (e instanceof Fn) {
      if (['exp', 'sin', 'cos', 'sinh', 'cosh', 're', 'im', 'abs', 'arg', 'conjugate', 'atan'].includes(e.name)) return allTri(e.args, (a) => this.q('complex', a)) === true ? true : undefined;
      return undefined;
    }
    return undefined;
  }

  private imaginary(e: Expr): Tri {
    if (isConst(e, 'I')) return true;
    if (e instanceof Rational || e instanceof Float || e instanceof Special) return false;
    if (e instanceof Constant) return false;
    if (this.q('real', e) === true) return false;
    if (e instanceof Mul) {
      const im = e.args.filter((a) => this.q('imaginary', a) === true);
      const re = e.args.filter((a) => this.q('real', a) === true && this.q('nonzero', a) === true);
      if (im.length + re.length === e.args.length) return im.length % 2 === 1;
      return undefined;
    }
    if (e instanceof Add) return allTri(e.args, (a) => this.q('imaginary', a)) === true && this.q('nonzero', mul(-1, S.I, e)) === true ? true : undefined;
    if (e instanceof Pow) {
      const [b, x] = e.args;
      if (isConst(b, 'E') && this.q('rational', mul(x, pow(mul(S.I, S.Pi), -1))) === true) return undefined;
      if (this.q('negative', b) === true && x instanceof Rational && x.equals(Rational.of(1n, 2n))) return true;
      return undefined;
    }
    return undefined;
  }

  private finite(e: Expr): Tri {
    if (e instanceof Rational || e instanceof Float || e instanceof Constant) return true;
    if (e instanceof Special) return false;
    if (e instanceof Sym) return this.q('real', e) === true || this.q('complex', e) === true ? true : undefined;
    if (e instanceof Add || e instanceof Mul) return allTri(e.args, (a) => this.q('finite', a)) === true ? true : undefined;
    if (e instanceof Pow) {
      const [b, x] = e.args;
      if (this.q('finite', b) === true && this.q('finite', x) === true && (this.q('nonzero', b) === true || this.q('nonnegative', x) === true || isConst(b, 'E'))) return true;
      return undefined;
    }
    if (e instanceof Fn) {
      const a = e.args[0];
      if (a && ['sin', 'cos', 'atan', 'tanh'].includes(e.name) && this.q('real', a) === true) return true;
      if (a && ['exp', 'sinh', 'cosh', 'abs', 're', 'im', 'conjugate'].includes(e.name) && this.q('finite', a) === true) return true;
      return undefined;
    }
    return undefined;
  }
}

/** The value of a proposition in one branch. */
function decide(prop: Expr, d: Decider): Tri {
  if (prop instanceof BoolAtom) return prop.value;
  if (prop instanceof BoolOp) {
    const vs = prop.args.map((a) => decide(a, d));
    switch (prop.op) {
      case 'Not':
        return notTri(vs[0]);
      case 'And':
        return vs.includes(false) ? false : vs.includes(undefined) ? undefined : true;
      case 'Or':
        return vs.includes(true) ? true : vs.includes(undefined) ? undefined : false;
      case 'Xor':
        return vs.includes(undefined) ? undefined : vs.filter(Boolean).length % 2 === 1;
      case 'ITE':
        return vs[0] === undefined ? undefined : vs[0] ? vs[1] : vs[2];
    }
  }
  if (prop instanceof Rel) {
    const names = { Gt: 'gt', Lt: 'lt', Ge: 'ge', Le: 'le', Eq: 'eq', Ne: 'ne' } as const;
    return decide(new AppliedPredicate(names[prop.op], [prop.lhs, prop.rhs]), d);
  }
  if (prop instanceof AppliedPredicate) {
    const rel = relationFact(prop, true);
    if (rel) {
      const v = d.q(rel[1], rel[0]);
      return rel[2] ? v : notTri(v);
    }
    if (prop.args.length !== 1) {
      for (const h of handlers.get(prop.predicate) ?? []) {
        const r = h(prop.arg, d.assumptions, prop.args);
        if (r !== 'unknown') return r;
      }
      return undefined;
    }
    return d.q(prop.predicate, prop.arg);
  }
  throw new TypeError(`ask: ${prop.toString()} is not a proposition`);
}

/**
 * SymPy ask(proposition, assumptions): true, false, or 'unknown' when it
 * cannot be decided. The proposition is a predicate (Q.even(x)), a
 * relation, or a boolean combination of them; inconsistent assumptions
 * throw a RangeError.
 */
export function ask(proposition: ExprLike | boolean, assumptions: Assumption = true): Truth {
  const prop = typeof proposition === 'boolean' ? (proposition ? S.true : S.false) : sympify(proposition);
  const assumed = and(...asList(assumptions), ...globalAssumptions);
  const vs = branches(assumed).map((b) => decide(prop, new Decider(b, assumed)));
  if (vs.every((v) => v === true)) return true;
  if (vs.every((v) => v === false)) return false;
  return 'unknown';
}

/** (-1)**(a + b + ...) with the even terms dropped and the odd ones replaced by 1 (SymPy refine_Pow). */
function refineSignPowers(e: Expr, d: Decider): Expr {
  return mapBottomUp(e, (r) => {
    if (!(r instanceof Pow && r.base instanceof Rational && r.base.equals(S.NegOne) && r.exp instanceof Add)) return r;
    let changed = false as boolean;
    const terms = r.exp.args.flatMap((t): Expr[] => {
      if (d.q('even', t) === true) {
        changed = true;
        return [];
      }
      if (d.q('odd', t) === true && !t.equals(S.One)) {
        changed = true;
        return [S.One];
      }
      return [t];
    });
    return changed ? pow(-1, add(...terms)) : r;
  });
}

/**
 * SymPy refine(expr, assumptions): expr simplified under the assumptions,
 * e.g. refine(sqrt(x**2), Q.real(x)) = Abs(x),
 * refine(Abs(x), Q.positive(x)) = x; a predicate becomes true or false
 * when the assumptions decide it (refine(Q.real(x), Q.positive(x)) = true).
 */
export function refine(expr: ExprLike, assumptions?: Assumption): Expr;
/** A matrix (any object with map) refined entry by entry (SymPy Matrix.refine). */
export function refine<M extends { map(f: (e: Expr) => ExprLike): M }>(expr: M, assumptions?: Assumption): M;
export function refine(expr: unknown, assumptions: Assumption = true): unknown {
  if (!(expr instanceof Expr) && typeof expr === 'object' && expr !== null && 'map' in expr && typeof expr.map === 'function') {
    return expr.map((x: Expr) => refine(x, assumptions));
  }
  if (!(expr instanceof Expr) && typeof expr !== 'number' && typeof expr !== 'bigint') throw new SympifyError(`Cannot convert ${String(expr)} to an expression`, expr);
  const e = sympify(expr);
  if (e instanceof AppliedPredicate || (e instanceof BoolOp && (e.op === 'And' || e.op === 'Or' || e.op === 'Not'))) {
    const v = ask(e, assumptions);
    if (v !== 'unknown') return v ? S.true : S.false;
    if (e instanceof BoolOp) {
      const args = e.args.map((a) => refine(a, assumptions));
      return e.op === 'And' ? and(...args) : e.op === 'Or' ? or(...args) : not(at(args, 0));
    }
    return e;
  }
  if (e instanceof Rel) {
    const v = ask(e, assumptions);
    if (v !== 'unknown') return v ? S.true : S.false;
  }
  const assumed = and(...asList(assumptions), ...globalAssumptions);
  const bs = branches(assumed);
  const results = bs.map((b) => {
    const d = new Decider(b, assumed);
    const back = [...b.forward].map(([k, s]): [Expr, Expr] => [s, getOrThrow(b.facts, k).expr]);
    const r = reevaluate(e, b.forward);
    const restored = back.length ? xreplace(r, back) : r;
    return refineSignPowers(restored, d);
  });
  const first = at(results, 0);
  return results.every((r) => r.key === first.key) ? first : e;
}
