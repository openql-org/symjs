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
import { Add, BoolAtom, Constant, Expr, ExtensionExpr, Fn, Float, Mul, Piecewise, Pow, Rational, Rel, S, Special, Sym, functionFactHandlers, impl } from './nodes';
import { add, couldExtractMinusSign, mul, pow, sympify } from './ops';
import { mapBottomUp, some, xreplace } from './traverse';
import { asRealImag } from './methods';
import { isIntegerQ, isMinMax, isNegative, isNonNegative, isNonZero, isPositive, isReal, isZero, torf } from './assumptions';
import { BoolOp, and, not, or, xor } from './boolalg';
import type { Truth } from './truth';
import { at, getOrThrow, pair } from './guard';
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
  /** The arguments of this applied predicate (SymPy AppliedPredicate.arguments). */
  get arguments(): readonly Expr[] { return this.args; }
  /** The predicate applied by this expression (SymPy AppliedPredicate.function). */
  get function(): Predicate { return Q[this.predicate] ?? Predicate(this.predicate); }
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
    return `\\operatorname{Q}_{\\text{${this.predicate.replace(/_/g, '\\_')}}}(${this.args.map(print).join(', ')})`;
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
  (...args: (ExprLike | boolean)[]): AppliedPredicate;
  /** The name (positive for Q.positive). */
  readonly predicateName: string;
}

const handlers = new Map<string, PredicateHandler[]>();

/** Register an optional decision procedure for propositions. */
export function registerPropositionHandler(handler: (proposition: Expr, assumptions: Expr) => Truth): void {
  propositionHandlers.push(handler);
}
const propositionHandlers: ((proposition: Expr, assumptions: Expr) => Truth)[] = [];

/** Register structural assumption refinements supplied by feature modules. */
export function registerRefineHandler(handler: (expr: Expr, assumptions: Assumption) => Expr): void {
  refineHandlers.push(handler);
}
const refineHandlers: ((expr: Expr, assumptions: Assumption) => Expr)[] = [];

/**
 * A predicate with the given name (SymPy Predicate); handlers added with
 * registerHandler decide it in ask.
 */
const REL_PREDICATES = { Gt: 'gt', Lt: 'lt', Ge: 'ge', Le: 'le', Eq: 'eq', Ne: 'ne' } as const;

export function Predicate(name: string, handler?: PredicateHandler): Predicate {
  const f = (...argsIn: (ExprLike | boolean)[]): AppliedPredicate => {
    const args = argsIn.map((a) => (typeof a === 'boolean' ? (a ? S.true : S.false) : sympify(a)));
    // SymPy IsTruePredicate: Q.is_true of a predicate is the predicate, of a relation its predicate (Q.eq, Q.gt, ...)
    const a0 = args[0];
    if (name === 'is_true' && a0 instanceof AppliedPredicate) return a0;
    if (name === 'is_true' && a0 instanceof Rel) return new AppliedPredicate(REL_PREDICATES[a0.op], [a0.lhs, a0.rhs]);
    return new AppliedPredicate(name, args);
  };
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

/** Adds a fact and its consequences; false when it contradicts the known facts. */
function addFact(facts: Facts, name: string, value: boolean): boolean {
  const todo: Literal[] = [[name, value]];
  for (let lit = todo.pop(); lit !== undefined; lit = todo.pop()) {
    const [n, v] = lit;
    const cur = facts.get(n);
    if (cur === v) continue;
    if (cur !== undefined) return false;
    facts.set(n, v);
    todo.push(...(consequences.get(`${n}:${String(v)}`) ?? []));
  }
  return true;
}

const asList = (a: Assumption): Expr[] => (typeof a === 'boolean' ? (a ? [] : [S.false]) : a instanceof Expr ? [a] : [...a]);

/**
 * Xor, ITE, Implies, Equivalent, Nand, Nor and Xnor (the core nodes and the
 * gates of the logic module, told apart by name) in terms of And, Or and Not.
 */
function expandBool(e: Expr): Expr | undefined {
  const name = e instanceof BoolOp ? e.className : e instanceof ExtensionExpr && !(e instanceof AppliedPredicate) ? e.name : '';
  const a = e.args;
  switch (name) {
    case 'Xor': {
      const h = at(a, 0);
      const r = xor(...a.slice(1));
      return or(and(h, not(r)), and(not(h), r));
    }
    case 'ITE':
      return or(and(at(a, 0), at(a, 1)), and(not(at(a, 0)), at(a, 2)));
    case 'Implies':
      return or(not(at(a, 0)), at(a, 1));
    case 'Equivalent':
      return or(and(...a), and(...a.map((x) => not(x))));
    case 'Nand':
      return not(and(...a));
    case 'Nor':
      return not(or(...a));
    case 'Xnor':
      return not(xor(...a));
    default:
      return undefined;
  }
}

/** The assumptions in disjunctive normal form: a list of conjunctions of literals. */
function dnf(e: Expr, negated = false): (readonly [AppliedPredicate, boolean])[][] {
  if (e instanceof BoolAtom) return e.value !== negated ? [[]] : [];
  const expanded = expandBool(e);
  if (expanded) return dnf(expanded, negated);
  if (e instanceof BoolOp) {
    if (e.op === 'Not') return dnf(at(e.args, 0), !negated);
    // only And and Or are left
    const isAnd = (e.op === 'And') !== negated;
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
  return [[]];
}

/** The branches of the assumptions with their facts closed under the implications (none when inconsistent). */
function consistentBranches(all: Expr): Branch[] {
  const out: Branch[] = [];
  for (const conj of dnf(all)) {
    const facts = new Map<string, { expr: Expr; facts: Facts }>();
    const consistent = conj.every(([ap, v]) => {
      // Q.gt(a, b) is a fact about a - b; other predicates of several arguments are not used
      const fact = relationFact(ap, v) ?? (ap.args.length === 1 ? ([ap.arg, ap.predicate, v] as const) : undefined);
      if (!fact) return true;
      const [arg, name, value] = fact;
      const entry = facts.get(arg.key) ?? { expr: arg, facts: new Map<string, boolean>() };
      facts.set(arg.key, entry);
      return addFact(entry.facts, name, value);
    });
    if (consistent) out.push({ facts, forward: symbolsWithFacts(facts) });
  }
  return out;
}

/** The branches of the assumptions together with the global assumptions; throws when they are inconsistent. */
function branches(assumptions: Assumption): Branch[] {
  const out = consistentBranches(and(...asList(assumptions), ...globalAssumptions));
  if (!out.length) throw new RangeError('inconsistent assumptions');
  return out;
}

/** Q.gt(a, b) as a fact about a - b (Q.positive(a - b)). */
function relationFact(p: AppliedPredicate, v: boolean): [Expr, string, boolean] | undefined {
  if (p.args.length !== 2) return undefined;
  let d = add(at(p.args, 0), mul(-1, at(p.args, 1)));
  if ((p.predicate === 'eq' || p.predicate === 'ne') && couldExtractMinusSign(d)) d = mul(-1, d);
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
    if (f.get('zero') === true) a.zero = true;
    if (f.get('zero') === false || f.get('nonzero') === true) a.zero = false;
    if (f.has('commutative')) a.commutative = f.get('commutative');
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

/** The predicates Max and Min have when all their arguments have them (SymPy MinMaxBase._eval_is_*). */
const MIN_MAX_PREDICATES = new Set([
  'algebraic', 'antihermitian', 'commutative', 'complex', 'composite', 'even', 'finite', 'hermitian', 'imaginary', 'infinite', 'integer',
  'irrational', 'negative', 'noninteger', 'nonnegative', 'nonpositive', 'nonzero', 'odd', 'positive', 'prime', 'rational', 'real',
  'extended_real', 'transcendental', 'zero',
]);

/** The predicates of a Piecewise that all its expressions share (SymPy Piecewise._eval_is_*). */
/** Functions that are extended real for an extended real argument. */
const EXTENDED_REAL_FNS = new Set(['sin', 'cos', 'tan', 'cot', 'sec', 'csc', 'sinh', 'cosh', 'tanh', 'coth', 'sech', 'csch', 'asinh', 'acsch', 'atan', 'acot', 'exp']);

const PIECEWISE_PREDICATES = new Set([
  'complex', 'even', 'finite', 'imaginary', 'integer', 'irrational', 'negative', 'nonnegative', 'nonpositive', 'nonzero', 'odd', 'positive',
  'real', 'extended_real', 'zero',
]);

class Decider {
  constructor(
    readonly branch: Branch,
    readonly assumptions: Expr,
  ) {}

  /** The predicate on e: true, false or undefined (unknown). */
  q(name: string, e: Expr): Tri {
    const known = this.branch.facts.get(e.key)?.facts.get(name);
    if (known !== undefined) return known;
    const symbolFact = e instanceof Sym ? e.assumptions0.get(name) : undefined;
    if (symbolFact !== undefined) return symbolFact;
    // nan has no handler in SymPy: every predicate but commutative is undecided on it
    if (e === S.NaN && name !== 'commutative') return undefined;
    for (const h of handlers.get(name) ?? []) {
      const r = h(e, this.assumptions, [e]);
      if (r !== 'unknown') return r;
    }
    // predicates refer to each other (integer <-> rational, real <-> imaginary): a query in progress is unknown
    const k = `${name}|${e.key}`;
    if (this.memo.has(k)) return this.memo.get(k) ?? undefined;
    this.memo.set(k, null);
    const r = (isMinMax(e) && MIN_MAX_PREDICATES.has(name) ? torf(e.args, (a) => this.q(name, a)) : undefined)
      ?? (e instanceof Piecewise && PIECEWISE_PREDICATES.has(name) ? torf(e.pairs.map(([x]) => x), (a) => this.q(name, a)) : undefined)
      ?? this.exponentialDomain(name, e)
      ?? (e instanceof Fn ? functionFactHandlers[e.name]?.(name, e.args, (fact, arg) => this.q(fact, arg)) : undefined)
      ?? this.numericDomain(name, e)
      ?? this.builtin(name, e);
    this.memo.set(k, r);
    return r;
  }
  private readonly memo = new Map<string, Tri | null>();

  /** e with the symbol facts applied. */
  private re(e: Expr): Expr {
    return reevaluate(e, this.branch.forward);
  }

  /** SymPy's numeric real and imaginary handlers inspect the corresponding coordinate. */
  private numericDomain(name: string, e: Expr): Tri {
    if ((name !== 'real' && name !== 'imaginary') || !(e instanceof Add || e instanceof Mul || e instanceof Pow) || !e.isNumber) return undefined;
    const [re, im] = asRealImag(e.evalf());
    const imaginaryZero = isZero(im);
    if (name === 'real') return imaginaryZero;
    const realZero = isZero(re);
    return realZero === false || imaginaryZero === true ? false : realZero === true && imaginaryZero === false ? true : undefined;
  }

  private exponentialDomain(name: string, e: Expr): Tri {
    if (e instanceof Pow && isConst(e.base, 'E') && ['real', 'imaginary', 'positive', 'negative'].includes(name)) {
      if (this.q('real', e.exp) === true) return name === 'real' || name === 'positive';
      const phase = mul(-1, S.I, e.exp, pow(S.Pi, -1));
      const integral = this.q('integer', phase);
      if (name === 'real' && integral === true) return true;
      if (name === 'positive' && integral === true) return this.q('even', phase);
      if (name === 'negative' && integral === true) return this.q('odd', phase);
      if (name === 'imaginary') {
        const halfIntegral = this.q('integer', mul(2, phase));
        if (integral === true || halfIntegral === false) return false;
        if (integral === false && halfIntegral === true) return true;
      }
    }
    return undefined;
  }

  private builtin(name: string, e: Expr): Tri {
    switch (name) {
      case 'real':
        if (e instanceof Fn && e.name === 'log') return this.q('positive', at(e.args, 0));
        if (e instanceof Special) return false;
        // isReal counts oo and -oo as real (extended reals); Q.real does not
        if (this.q('finite', e) === false) return false;
        if (isConst(e, 'I')) return false;
        if (e instanceof Add) {
          const rs = e.args.map((a) => this.q('real', a));
          if (rs.every((r) => r === true)) return true;
          if (rs.filter((r) => r === false).length === 1 && !rs.includes(undefined)) return false;
        }
        if (e instanceof Mul) {
          const real = e.args.map((a) => this.q('real', a));
          if (real.filter((r) => r === false).length === 1 && !real.includes(undefined)
            && e.args.every((a, i) => real[i] === false || this.q('nonzero', a) === true)) return false;
          const im = e.args.filter((a) => this.q('imaginary', a) === true);
          if (im.length && e.args.every((a) => im.includes(a) || this.q('real', a) === true)) {
            if (im.length % 2 === 0) return true;
            if (e.args.every((a) => im.includes(a) || this.q('zero', a) === false)) return false;
          }
        }
        if (this.q('imaginary', e) === true) return false;
        if (e instanceof Pow) {
          const { base, exp } = e;
          if (base instanceof Pow && isConst(base.base, 'E') && this.q('integer', exp) === true) {
            const inner = base.exp;
            return this.q('real', new Pow(S.E, mul(inner, exp)));
          }
          if (base instanceof Pow && isConst(base.base, 'E') && this.q('imaginary', exp) === true) {
            const inner = base.exp;
            if (this.q('imaginary', inner) === true) return true;
          }
          if (this.q('imaginary', base) === true && this.q('integer', exp) === true) {
            const odd = this.q('odd', exp);
            if (odd !== undefined) return !odd;
          }
          if ((isConst(base, 'I') || isConst(mul(-1, base), 'I') || isInt(base) && base.p === -1n) && this.q('imaginary', exp) === true) return true;
          if (this.q('positive', base) === true && this.q('real', exp) === true) return true;
          if (this.q('real', base) === true && this.q('real', exp) === true) {
            // A zero base is real only for a nonnegative exponent; a negative base needs an odd denominator.
            if (this.q('zero', base) === true) return this.q('nonnegative', exp) === true ? true : undefined;
            if (exp instanceof Rational && exp.q % 2n === 0n) return this.q('nonnegative', base) === true ? true : this.q('negative', base) === true ? false : undefined;
            if (this.q('integer', exp) === true) return this.q('zero', base) === false || this.q('nonnegative', exp) === true ? true : undefined;
            if (this.q('nonnegative', base) === true && this.q('positive', exp) === true) return true;
          }
        }
        return isReal(this.re(e)) ?? (this.q('rational', e) === true ? true : undefined);
      case 'extended_real': {
        if (e instanceof Special) return e.name === 'oo' || e.name === '-oo';
        if (e instanceof Fn && (e.name === 'asin' || e.name === 'acos')) return this.q('real', e);
        if (e instanceof Add && e.args.length === 2 && e.args.some((a) => a instanceof Special && (a.name === 'oo' || a.name === '-oo')) && e.args.some((a) => this.q('real', a) === true)) return true;
        // SymPy _eval_is_extended_real of functions real on the extended real line
        if (e instanceof Fn && e.args.length === 1 && EXTENDED_REAL_FNS.has(e.name) && this.q('extended_real', at(e.args, 0)) === true) return true;
        const r = this.q('real', e);
        if (r === true) return true;
        // a finite number that is not real (I) is not an extended real
        return r === false && this.q('finite', e) === true ? false : undefined;
      }
      case 'positive':
        if (e instanceof Pow && this.q('positive', e.base) === true && this.q('real', e.exp) === true) return true;
        if (e instanceof Fn && e.name === 'acot' && this.q('imaginary', at(e.args, 0)) === true) return false;
        if (e instanceof Fn && e.name === 'asin') {
          const arg = at(e.args, 0);
          if (this.q('positive', arg) === true && this.q('nonpositive', add(arg, -1)) === true) return true;
          if (this.q('negative', arg) === true && this.q('nonnegative', add(arg, 1)) === true) return false;
        }
        if (e instanceof Fn && e.name === 'factorial' && this.q('integer', at(e.args, 0)) === true && this.q('positive', at(e.args, 0)) === true) return true;
        if (e instanceof Special) return false;
        if (e instanceof Add && e.args.every((a) => this.q('nonnegative', a) === true) && e.args.some((a) => this.q('positive', a) === true)) return true;
        if (e instanceof Pow && this.q('negative', e.base) === true && this.q('integer', e.exp) === true) return this.q('even', e.exp);
        return this.ext(isPositive(this.re(e)), e) ?? (this.q('negative', e) === true ? false : this.trichotomy(e, 'negative'));
      case 'negative':
        if (e instanceof Special) return false;
        if (e instanceof Fn && e.name === 'abs') return false;
        if (e instanceof Add && e.args.every((a) => this.q('nonpositive', a) === true) && e.args.some((a) => this.q('negative', a) === true)) return true;
        if (e instanceof Pow && this.q('negative', e.base) === true && this.q('integer', e.exp) === true) return this.q('odd', e.exp);
        return this.ext(isNegative(this.re(e)), e) ?? (this.q('positive', e) === true ? false : this.trichotomy(e, 'positive'));
      case 'nonnegative':
        if (e instanceof Pow && this.q('real', e.base) === true && this.q('even', e.exp) === true && this.q('positive', e.exp) === true) return true;
        if (e instanceof Special) return false;
        return this.ext(isNonNegative(this.re(e)), e);
      case 'nonpositive': {
        if (e instanceof Special) return false;
        const p = this.q('positive', e);
        if (p === true) return false;
        if (p === false && this.q('real', e) === true) return true;
        return this.q('real', e) === false ? false : undefined;
      }
      case 'zero':
        if (e instanceof Special) return false;
        // a product with a zero factor (and no infinite one)
        if (e instanceof Mul && e.args.some((a) => this.q('zero', a) === true) && e.args.every((a) => this.q('infinite', a) !== true)) return true;
        return isZero(this.re(e)) ?? (this.q('nonzero', e) === true || this.q('real', e) === false ? false : undefined);
      case 'nonzero': {
        if (e instanceof Special) return false;
        if (this.q('real', e) === false) return false;
        const z = isNonZero(this.re(e));
        return z !== undefined ? z && this.q('real', e) === true ? true : z ? undefined : false : this.q('positive', e) === true || this.q('negative', e) === true || this.q('odd', e) === true ? true : undefined;
      }
      case 'extended_positive':
        if (e instanceof Special) return e.name === 'oo';
        if (e instanceof Fn && e.name === 'log') {
          const argument = at(e.args, 0);
          if (this.q('infinite', argument) === true && this.q('extended_positive', argument) === true) return true;
        }
        if (this.q('positive', e) === true) return true;
        if (this.q('extended_real', e) === false) return false;
        return this.q('extended_real', e) === true && this.q('extended_nonpositive', e) === true ? false : undefined;
      case 'extended_negative':
        return e instanceof Special ? e.name === '-oo' : this.extended(e, 'negative', 'nonnegative');
      case 'extended_nonnegative':
        return e instanceof Special ? e.name === 'oo' : this.extended(e, 'nonnegative', 'negative');
      case 'extended_nonpositive':
        return e instanceof Special ? e.name === '-oo' : this.extended(e, 'nonpositive', 'positive');
      case 'extended_nonzero':
        return e instanceof Special ? e.name === 'oo' || e.name === '-oo' : this.extended(e, 'nonzero', 'zero');
      case 'positive_infinite':
        return e instanceof Special ? e.name === 'oo' : this.q('finite', e) === true ? false : undefined;
      case 'negative_infinite':
        return e instanceof Special ? e.name === '-oo' : this.q('finite', e) === true ? false : undefined;
      case 'integer':
        if (e instanceof Float) return e.mpf.exp < 0n ? false : undefined;
        if (e instanceof Special || isConst(e, 'pi', 'E', 'I', 'GoldenRatio', 'TribonacciConstant')) return false;
        if (e instanceof Rational) return e.q === 1n;
        if (e instanceof Pow && this.q('zero', e.exp) === true && this.q('zero', e.base) === false) return true;
        if (e instanceof Mul) {
          const half = e.args.find((a) => a instanceof Rational && a.q === 2n);
          if (half instanceof Rational) return this.q('even', mul(half.p, ...e.args.filter((a) => a !== half)));
        }
        if (e instanceof Fn && e.name === 'abs' && this.q('real', at(e.args, 0)) === true) return this.q('integer', at(e.args, 0));
        return isIntegerQ(this.re(e)) ?? (this.q('rational', e) === false ? false : undefined);
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
        return this.adjoint(e, false);
      case 'antihermitian':
        return this.adjoint(e, true);
      case 'finite':
        return this.finite(e);
      case 'infinite':
        return notTri(this.q('finite', e));
      case 'commutative':
        return this.re(e).isCommutative;
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

  private hasRationalElementaryValue(e: Fn): boolean {
    if (e.args.length !== 1) return false;
    const argument = at(e.args, 0);
    if (['sin', 'cos', 'tan', 'asin', 'atan'].includes(e.name)) return this.q('zero', argument) === true;
    if (e.name === 'log' || e.name === 'acos') return this.q('zero', add(argument, -1)) === true;
    return false;
  }

  private rational(e: Expr): Tri {
    if (e instanceof Rational) return true;
    if (e instanceof Fn && e.name === 'exp_polar' && this.q('zero', at(e.args, 0)) === true) return true;
    if (e instanceof Fn && this.hasRationalElementaryValue(e)) return true;
    if (e instanceof Fn && this.q('zero', e) === true) return true;
    // SymPy Abs._eval_is_rational and _eval_is_integer: |a| of a rational (integer) real a
    if (e instanceof Fn && e.name === 'abs' && this.q('real', at(e.args, 0)) === true) return this.q('rational', at(e.args, 0));
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
        // a rational number plus (or a nonzero rational number times) a number that is not rational is not rational
        if (e instanceof Add) return false;
        return e.args.every((a, i) => i === rs.indexOf(false) || this.q('nonzero', a) === true) ? false : undefined;
      }
      if (this.q('real', e) === false) return false;
      // a transcendental number is not rational
      return this.q('algebraic', e) === false ? false : undefined;
    }
    if (e instanceof Pow) {
      const [b, x] = e.args;
      if (isConst(b, 'E') && x instanceof Fn && x.name === 'log' && x.args.length === 1) {
        return this.q('rational', at(x.args, 0));
      }
      if (this.q('algebraic', e) === false) return false;
      if (isConst(b, 'E')) return this.q('zero', x) === true ? true : undefined;
      if (isInt(x) && x.p === -1n && this.q('rational', b) === false && this.q('finite', b) === true) return false;
      if (this.q('integer', x) === true && this.q('rational', b) === true) return this.q('nonzero', b) === true || this.q('nonnegative', x) === true ? true : undefined;
      // an unevaluated rational power of a rational number is irrational or not real
      if (b instanceof Rational && x instanceof Rational) return false;
      return undefined;
    }
    if (e instanceof Fn) {
      // the functions named below take one argument
      const a = (): Expr => at(e.args, 0);
      if (['cot', 'acot'].includes(e.name) && this.q('rational', a()) === true) return false;
      const transcendentalAtNonzeroRational = ['exp', 'sin', 'cos', 'tan', 'cot', 'asin', 'atan', 'acot', 'sinh', 'cosh', 'tanh', 'asinh', 'atanh'];
      if (transcendentalAtNonzeroRational.includes(e.name) && this.q('rational', a()) === true && this.q('nonzero', a()) === true) return false;
      // log(1) = acos(1) = 0
      if (e.name === 'log' && this.q('rational', a()) === true && this.q('nonzero', add(a(), -1)) === true) return false;
      if (e.name === 'acos' && this.q('rational', a()) === true && this.q('nonzero', add(a(), -1)) === true) return false;
      return undefined;
    }
    return undefined;
  }

  private algebraic(e: Expr): Tri {
    // a float is a finite binary fraction
    if (e instanceof Rational || e instanceof Float) return true;
    if (e instanceof Special) return false;
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
      if (isConst(b, 'E')) {
        // exp(pi*I*r) is a root of unity when r is rational.
        if (this.q('rational', mul(x, pow(mul(S.Pi, S.I), -1))) === true) return true;
        // e**(pi*r) for a nonzero rational r is transcendental (Gelfond)
        if (this.q('nonzero', x) === true && this.q('rational', mul(x, pow(S.Pi, -1))) === true) return false;
        return this.q('algebraic', x) === true && this.q('nonzero', x) === true ? false : undefined;
      }
      if (this.q('zero', x) === true) return true;
      if (this.q('rational', x) === true) {
        const algebraic = this.q('algebraic', b);
        return algebraic === true || this.q('zero', x) === false ? algebraic : undefined;
      }
      return undefined;
    }
    if (e instanceof Fn) {
      if (this.hasRationalElementaryValue(e)) return true;
      // the functions named below take one argument
      const a = (): Expr => at(e.args, 0);
      if (['cot', 'acot'].includes(e.name) && this.q('algebraic', a()) === true) return false;
      // trigonometric functions at rational multiples of pi are algebraic (SymPy sin._eval_is_algebraic)
      if (['sin', 'cos', 'tan', 'cot', 'sec', 'csc'].includes(e.name) && this.q('rational', mul(a(), pow(S.Pi, -1))) === true) return e.name === 'sin' || e.name === 'cos' ? true : undefined;
      if (['exp', 'sin', 'cos', 'tan', 'cot', 'sec', 'csc', 'asin', 'atan', 'acot'].includes(e.name) && this.q('algebraic', a()) === true && this.q('nonzero', a()) === true) return false;
      // re, im and conjugate of an algebraic number; W(a) for a nonzero algebraic a is transcendental
      if (['re', 'im', 'conjugate'].includes(e.name) && this.q('algebraic', a()) === true) return true;
      if (e.name === 'LambertW' && e.args.length === 1 && this.q('algebraic', a()) === true && this.q('nonzero', a()) === true) return false;
      // log(1) = acos(1) = 0
      if ((e.name === 'log' || e.name === 'acos') && this.q('algebraic', a()) === true && this.q('nonzero', add(a(), -1)) === true) return false;
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
    const par = (a: Expr): bigint | undefined => (this.q('even', a) === true ? 0n : this.q('odd', a) === true ? 1n : undefined);
    if (e instanceof Mul) {
      if (!e.args.every((a) => this.q('integer', a) === true)) return undefined;
      for (const a of e.args) {
        if (e.args.some((b) => b !== a && this.q('odd', add(b, mul(-1, a))) === true)) return r === 0n;
      }
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
      if (isInt(b) && b.p === -1n && this.q('integer', x) === true) return r === 1n;
      if (this.q('odd', b) === true && this.q('integer', x) === true && this.q('negative', x) === false) return r === 1n;
      if (this.q('integer', b) === true && this.q('positive', x) === true && this.q('integer', x) === true) {
        const p = par(b);
        return p === undefined ? undefined : p === r;
      }
      return undefined;
    }
    if (e instanceof Fn && (e.name === 're' || e.name === 'im') && this.q('real', at(e.args, 0)) === true) return e.name === 'im' ? r === 0n : this.q(r === 0n ? 'even' : 'odd', at(e.args, 0));
    if (e instanceof Fn && e.name === 'abs') {
      // SymPy Abs._eval_is_even and _eval_is_odd: those of a real argument
      const a = at(e.args, 0);
      return this.q('real', a) === true ? this.q(r === 0n ? 'even' : 'odd', a) : undefined;
    }
    if (integer === true) {
      const o = this.branch.facts.get(e.key)?.facts.get(other);
      if (o !== undefined) return !o;
    }
    return undefined;
  }

  /**
   * SymPy _PrimePredicate_number: an exact number that is numerically an integer is tested as that integer
   * (12345678901234567890 + cos(1)**2 + sin(1)**2); 'symbolic' for anything else.
   */
  private primeNumber(e: Expr): Tri | 'symbolic' {
    if (!(e instanceof Add) || e.freeSymbols().size > 0) return 'symbolic';
    const float = some(e, (t) => t instanceof Float);
    const value = impl.evalf(e, 60);
    if (!(value instanceof Float)) return 'symbolic';
    const { man, exp } = value.mpf;
    // the nearest integer of man * 2**exp
    const nearest = exp >= 0n ? man << exp : (man + (1n << (-exp - 1n))) >> -exp;
    const difference = impl.evalf(add(e, Rational.of(-nearest)), 30);
    if (difference instanceof Float && Math.abs(difference.value) > 1e-25) return false;
    return float ? undefined : isPrimeBig(nearest);
  }

  private prime(e: Expr): Tri {
    if (e instanceof Rational) return e.q === 1n && isPrimeBig(e.p);
    if (this.q('integer', e) === false) return false;
    if (this.q('positive', e) === false) return false;
    const number = this.primeNumber(e);
    if (number !== 'symbolic') return number;
    if (e instanceof Mul) {
      // SymPy PrimePredicate for Mul: a composite number factor of an integer product
      if (!e.args.every((a) => this.q('integer', a) === true)) return undefined;
      return e.args.some((a) => isInt(a) && a.p > 1n && !isPrimeBig(a.p)) ? false : undefined;
    }
    if (e instanceof Pow) {
      const [b, x] = e.args;
      if (isInt(x) && x.p === 1n) return this.q('prime', b);
      if (this.q('integer', x) === true && (this.q('composite', b) === true || this.q('prime', b) === true && this.q('zero', add(x, -1)) === false)) return false;
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
      // SymPy ComplexPredicate: exp is complex for every argument
      if (!expressionFacts && isConst(b, 'E')) return true;
      if (this.q('complex', b) === true && this.q('complex', x) === true && (this.q('nonzero', b) === true || this.q('nonnegative', x) === true || isConst(b, 'E'))) return true;
      return undefined;
    }
    if (e instanceof Fn) {
      // SymPy ComplexPredicate: sin and cos are complex for every argument
      if (!expressionFacts && (e.name === 'sin' || e.name === 'cos')) return true;
      if (['sin', 'cos', 'exp', 'sinh', 'cosh', 're', 'im', 'abs', 'arg', 'conjugate', 'atan'].includes(e.name)) return allTri(e.args, (a) => this.q('complex', a)) === true ? true : undefined;
      return undefined;
    }
    return undefined;
  }

  /**
   * An extended predicate of a finite expression: true when `finite` holds,
   * false when the opposite holds or the expression is not an extended real.
   */
  private extended(e: Expr, finite: string, opposite: string): Tri {
    if (this.q(finite, e) === true) return true;
    if (this.q(opposite, e) === true || this.q('extended_real', e) === false) return false;
    return undefined;
  }

  private imaginary(e: Expr): Tri {
    if (isConst(e, 'I')) return true;
    // SymPy sign._eval_is_imaginary
    if (e instanceof Fn && e.name === 'sign') return this.q('imaginary', at(e.args, 0));
    if (e instanceof Rational || e instanceof Float || e instanceof Special) return false;
    if (e instanceof Constant) return false;
    if (this.q('real', e) === true) return false;
    if (e instanceof Mul) {
      const im = e.args.filter((a) => this.q('imaginary', a) === true);
      const re = e.args.filter((a) => this.q('real', a) === true && this.q('nonzero', a) === true);
      if (im.length + re.length === e.args.length) return im.length % 2 === 1;
      return undefined;
    }
    if (e instanceof Add) {
      if (allTri(e.args, (a) => this.q('imaginary', a)) === true && this.q('nonzero', mul(-1, S.I, e)) === true) return true;
      // a nonzero real part and imaginary terms (2 + 3*I)
      const reals = e.args.filter((a) => this.q('real', a) === true);
      if (reals.length && e.args.every((a) => reals.includes(a) || this.q('imaginary', a) === true) && this.q('nonzero', add(...reals)) === true) return false;
      return undefined;
    }
    if (e instanceof Pow) {
      const [b, x] = e.args;
      if (b instanceof Pow && isConst(b.base, 'E') && this.q('integer', x) === true) {
        const inner = b.exp;
        return this.q('imaginary', new Pow(S.E, mul(inner, x)));
      }
      if (b instanceof Pow && isConst(b.base, 'E') && this.q('imaginary', x) === true) {
        const inner = b.exp;
        if (this.q('imaginary', inner) === true) return false;
      }
      if (this.q('imaginary', b) === true && this.q('integer', x) === true) return this.q('odd', x);
      if (this.q('real', b) === true && this.q('integer', x) === true) return false;
      if (this.q('real', b) === true && this.q('real', x) === true) {
        if (this.q('rational', x) === false) return false;
        const halfIntegral = this.q('integer', mul(2, x));
        if (halfIntegral === false) return false;
        if (halfIntegral === true && this.q('integer', x) === false && this.q('negative', b) === true) return true;
      }
      return undefined;
    }
    return undefined;
  }

  /** Adjoint parity for sums and products with at most one noncommutative factor. */
  private adjoint(e: Expr, anti: boolean): Tri {
    const name = anti ? 'antihermitian' : 'hermitian';
    if (e.isNumber && e.isCommutative) {
      if (!anti) return this.q('real', e);
      if (this.q('real', e) === false && this.q('imaginary', e) === false) return false;
    }
    if (e instanceof Add) {
      const values = e.args.map((a) => this.q(name, a));
      if (values.every((v) => v === true)) return true;
      if (!values.includes(undefined) && values.filter((v) => v === false).length === 1) return false;
    }
    if (e instanceof Mul && e.args.filter((a) => !a.isCommutative).length <= 1) {
      let parity = false;
      for (const a of e.args) {
        if (this.q('hermitian', a) === true) continue;
        if (this.q('antihermitian', a) !== true) return undefined;
        parity = !parity;
      }
      if (parity === anti) return true;
      return this.q('zero', e) === false ? false : undefined;
    }
    if (anti) {
      if (this.q('imaginary', e) === true || this.q('zero', e) === true) return true;
      return this.q('imaginary', e) === false && this.q('zero', e) === false ? false : undefined;
    }
    return e.isCommutative ? this.q('real', e) : undefined;
  }

  private finite(e: Expr): Tri {
    if (e instanceof Rational || e instanceof Float || e instanceof Constant) return true;
    if (e instanceof Special) return false;
    // a real symbol is complex
    if (e instanceof Sym) return this.q('complex', e) === true ? true : undefined;
    if (e instanceof Add && !expressionFacts) {
      // SymPy FinitePredicate handler of Add: the terms that are not known finite must agree in
      // extended_positive (true, or false for all of them), and an infinite one makes the sum infinite
      let sign: Tri | 'none' = 'none';
      let result: Tri = true;
      for (const a of e.args) {
        const bounded = this.q('finite', a);
        if (bounded === true) continue;
        const positive = this.q('extended_positive', a);
        if ((sign !== 'none' && positive !== sign) || (positive === undefined && (bounded === undefined || sign === undefined))) return undefined;
        sign = positive;
        if (result !== false) result = bounded;
      }
      return result;
    }
    if (e instanceof Add) {
      const unbounded = e.args.filter((a) => this.q('finite', a) !== true);
      if (!unbounded.length) return true;
      if (unbounded.length === 1) return this.q('finite', at(unbounded, 0));
      // Infinite terms cannot cancel when every remaining term has the same sign.
      if (['extended_positive', 'extended_negative'].some((p) => unbounded.every((a) => this.q(p, a) === true))) {
        return unbounded.some((a) => this.q('finite', a) === false) ? false : undefined;
      }
      return undefined;
    }
    if (e instanceof Mul) {
      const fs = e.args.map((a) => this.q('finite', a));
      if (fs.every((f) => f === true)) return true;
      if (!fs.includes(false) || fs.filter((f) => f === undefined).length > 1) return undefined;
      // A finite zero or an unsigned unknown factor can make an infinite product indeterminate.
      return e.args.every((a, i) => at(fs, i) === false || this.q('zero', a) === false || this.q('extended_nonzero', a) === true) ? false : undefined;
    }
    if (e instanceof Pow) {
      const [b, x] = e.args;
      if (isConst(b, 'E')) return this.q('finite', x);
      const bf = this.q('finite', b), xf = this.q('finite', x);
      if (bf === true && xf === true) {
        const bz = this.q('zero', b), xn = this.q('negative', x);
        if (bz === true && xn === true) return false;
        if (bz === false || xn === false) return true;
      }
      if (bf === false && this.q('extended_positive', x) === true) return false;
      if (bf === false && this.q('extended_negative', x) === true) return true;
      if (b instanceof Rational) {
        const magnitude = b.p < 0n ? -b.p : b.p;
        if (magnitude <= b.q && this.q('extended_positive', x) === true) return true;
        if (magnitude >= b.q && this.q('extended_negative', x) === true) return true;
        if (magnitude > b.q && xf === false && this.q('extended_positive', x) === true) return false;
        // SymPy: a base of modulus at least 1 to an infinite power is not finite
        if (!expressionFacts && magnitude >= b.q && xf === false) return false;
      }
      return undefined;
    }
    if (e instanceof Fn) {
      // the functions named below take one argument
      const a = (): Expr => at(e.args, 0);
      // SymPy FinitePredicate: sin and cos are bounded
      if (!expressionFacts && (e.name === 'sin' || e.name === 'cos')) return true;
      if (['sin', 'cos', 'atan', 'tanh'].includes(e.name) && this.q('real', a()) === true) return true;
      // SymPy frac._eval_is_finite and RoundFunction._eval_is_finite; sign is -1, 0, 1 or on the unit circle
      if (e.name === 'frac' || e.name === 'sign') return true;
      // SymPy inverse hyperbolic _eval_is_finite
      if (e.name === 'asinh' || e.name === 'acosh') return this.q('finite', a()) === true ? true : undefined;
      if ((e.name === 'atanh' || e.name === 'acoth') && this.q('nonzero', add(a(), -1)) === true && this.q('nonzero', add(a(), 1)) === true) return true;
      if ((e.name === 'asech' || e.name === 'acsch') && this.q('nonzero', a()) === true) return true;
      if (e.name === 'floor' || e.name === 'ceiling') return this.q('finite', a());
      if (['exp', 'sinh', 'cosh', 'abs', 're', 'im', 'conjugate'].includes(e.name) && this.q('finite', a()) === true) return true;
      if (e.name === 'log') {
        // SymPy FinitePredicate handler of log: infinite at an infinite argument and at 0 only
        if (this.q('zero', a()) === true || this.q('finite', a()) === false || this.q('infinite', a()) === true) return false;
        if (this.q('zero', a()) === false && (!expressionFacts || this.q('finite', a()) === true)) return true;
      }
      return undefined;
    }
    return undefined;
  }
}

/** The value of a proposition in one branch. */
function decide(prop: Expr, d: Decider): Tri {
  if (prop instanceof BoolAtom) return prop.value;
  const expanded = expandBool(prop);
  if (expanded) return decide(expanded, d);
  if (prop instanceof BoolOp) {
    // only And, Or and Not are left
    const vs = prop.args.map((a) => decide(a, d));
    if (prop.op === 'Not') return notTri(at(vs, 0));
    if (prop.op === 'And') return vs.includes(false) ? false : vs.includes(undefined) ? undefined : true;
    return vs.includes(true) ? true : vs.includes(undefined) ? undefined : false;
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
/**
 * The facts of an expression (SymPy expr.is_<fact>, the old assumptions) are asked without the rules that only
 * the handlers of SymPy's ask have: sin(x).is_finite is None, while ask(Q.finite(sin(x))) is True.
 */
let expressionFacts = false;

/** ask for a fact of an expression itself (SymPy expr.is_<fact>). */
export function askExpressionFact(proposition: Expr): Truth {
  const outer = expressionFacts;
  expressionFacts = true;
  try {
    return ask(proposition);
  } finally {
    expressionFacts = outer;
  }
}

export function ask(proposition: ExprLike | boolean, assumptions: Assumption = true): Truth {
  const prop = typeof proposition === 'boolean' ? (proposition ? S.true : S.false) : sympify(proposition);
  const assumed = and(...asList(assumptions), ...globalAssumptions);
  // Implies(a, b) holds when b follows from the assumptions and a (or a contradicts them)
  if (prop instanceof BoolOp && prop.className === 'Implies') {
    const [a, b] = pair(prop.args);
    const withA = and(assumed, a);
    if (!consistentBranches(withA).length || ask(b, withA) === true) return true;
  }
  for (const handler of propositionHandlers) {
    const value = handler(prop, assumed);
    if (value !== 'unknown') return value;
  }
  if (prop instanceof BoolOp && consistentBranches(assumed).length) {
    if (!consistentBranches(and(assumed, not(prop))).length) return true;
    if (!consistentBranches(and(assumed, prop)).length) return false;
    // SymPy sathandlers: a product is zero exactly when one of its factors is
    const factored = mapBottomUp(assumed, (node) => (node instanceof AppliedPredicate && node.predicate === 'zero' && node.arg instanceof Mul
      ? or(...node.arg.args.map((factor) => new AppliedPredicate('zero', [factor]))) : node));
    if (factored.key !== assumed.key && !consistentBranches(and(factored, not(prop))).length) return true;
  }
  const relationAssumed = prop instanceof Rel ? mapBottomUp(assumed, (node) => node instanceof Rel ? new AppliedPredicate(REL_PREDICATES[node.op], [node.lhs, node.rhs]) : node) : assumed;
  const vs = branches(relationAssumed).map((b) => decide(prop, new Decider(b, relationAssumed)));
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
  let e = sympify(expr);
  if (e instanceof Pow && e.exp.equals(S.Half) && e.base instanceof Pow && e.base.exp.equals(S.NegOne) && ask(Q.positive(e.base.base), assumptions) !== true) return e;
  for (const handler of refineHandlers) e = mapBottomUp(e, (node) => handler(node, assumptions));
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
  const refineIn = (b: Branch): Expr => {
    const d = new Decider(b, assumed);
    const back = [...b.forward].map(([k, s]): [Expr, Expr] => [s, getOrThrow(b.facts, k).expr]);
    const r = reevaluate(e, b.forward);
    const restored = back.length ? xreplace(r, back) : r;
    return refineSignPowers(restored, d);
  };
  const results = bs.map(refineIn);
  const first = at(results, 0);
  if (results.every((r) => r.key === first.key)) return first;
  // the branches disagree: refine with the facts common to all of them
  // (refine(sqrt(x**2), Q.positive(x) | Q.negative(x)) uses Q.real(x) and gives Abs(x))
  return refineIn(commonBranch(bs));
}

/** The facts that hold in every branch. */
function commonBranch(bs: readonly Branch[]): Branch {
  const rest = bs.slice(1);
  const facts: Branch['facts'] = new Map();
  for (const [k, { expr, facts: f0 }] of at(bs, 0).facts) {
    const f = new Map([...f0].filter(([n, v]) => rest.every((b) => b.facts.get(k)?.facts.get(n) === v)));
    if (f.size) facts.set(k, { expr, facts: f });
  }
  return { facts, forward: symbolsWithFacts(facts) };
}
