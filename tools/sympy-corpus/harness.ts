// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Harness that replays SymPy doctest cases (tools/sympy-corpus/corpus.json) against symjs.
 *
 * Each case is a call `f(args, **kwargs)` or `obj.m(args, **kwargs)` with
 * serialized arguments and SymPy's `str()` of the result. An adapter maps the
 * SymPy API name to symjs; the result is formatted like Python's `str()` and
 * compared with the expected string.
 */

import { readFileSync } from 'node:fs';
import * as sj from '../../packages/symjs/src';
import * as dg from '@symjs/symjs/diffgeom';
import * as categories from '../../packages/symjs/src/categories';
import * as plotting from '../../packages/symjs/src/plotting';
import * as parsing from '../../packages/symjs/src/parsing';
// Category dispatch selects diffgeom.Point; the root geometry Point keeps its name.
const publicApi = { ...dg, ...sj, ...parsing };
import { equivalent } from '../../packages/symjs/tests/sympy-equivalent';
import { GrowableGrid } from '../../packages/symjs/src/categories/diagram_drawing';
import { PORTS } from './ports';
import { constantCount, solvesOdeSystem } from './ode-checks';
import { Expr, ExprLike, Integral, Matrix, S, Sym } from '../../packages/symjs/src';
import { Fn } from '../../packages/symjs/src/core/nodes';

// ---------------------------------------------------------------------------
// Python-like containers for formatting results
// ---------------------------------------------------------------------------

export class JsIterator {
  constructor(readonly items: readonly unknown[]) {}
}
export class JsList {
  constructor(readonly items: readonly unknown[]) {}
}
export class JsTuple {
  constructor(
    readonly items: readonly unknown[],
    /** the Python value was a list */
    readonly isList = false,
  ) {}
}
export class JsDict {
  constructor(readonly entries: readonly (readonly [unknown, unknown])[]) {}
}
export class JsDefaultDict {
  constructor(readonly entries: readonly (readonly [unknown, unknown])[]) {}
}
export class JsFrozenSet {
  constructor(readonly items: readonly unknown[]) {}
}
export class JsSet {
  constructor(readonly items: readonly unknown[]) {}
}

export class Unsupported extends Error {}
/** An element of GF(p) (SymPy ModularInteger, the terms of the LFSR sequences of sympy.crypto). */
export class JsFFElement {
  constructor(readonly v: bigint, readonly mod: bigint, readonly symmetric: boolean) {}
  toString(): string {
    const v = this.symmetric && this.v > this.mod / 2n ? this.v - this.mod : this.v;
    return `${this.symmetric ? 'Symmetric' : ''}ModularIntegerMod${this.mod}(${v})`;
  }
}

/** A Python float (printed as 2.0, 0.5, ...). */
export class JsFloat {
  constructor(readonly v: number) {}
}

/** An undefined function class (SymPy `Function('f')` itself, not applied). */
/** A polynomial domain by its SymPy name (ZZ, QQ, GF(5), QQ<sqrt(2)>, ZZ[x], ...) and its symjs domain when one exists. */
export class JsDomain {
  constructor(
    readonly name: string,
    readonly domain?: unknown,
    readonly definition?: Tree,
  ) {}
}

/**
 * A Python callback that is not an expression of its parameters (lambda i, j: [x, y][j]),
 * recorded as the table of the calls the reference computation made.
 */
export class JsTable {
  constructor(readonly entries: readonly (readonly [readonly unknown[], unknown])[]) {}
  call(...xs: unknown[]): unknown {
    const key = xs.map((x) => fmt(typeof x === 'number' ? sj.Rational.of(BigInt(x)) : x)).join(', ');
    const entry = this.entries.find(([args]) => args.map((a) => fmt(a)).join(', ') === key);
    if (entry === undefined) throw new Unsupported(`callback called with (${key}), outside the recorded calls`);
    return entry[1];
  }
}

/** A predicate lambda testing a SymPy is_* attribute (lambda e: e.is_Mul). */
export class JsPred {
  constructor(readonly attr: string) {}
  test(e: Expr): boolean {
    switch (this.attr) {
      case 'is_Number':
        return e instanceof sj.Rational || e instanceof sj.Float;
      case 'is_Integer':
        return e instanceof sj.Rational && e.isInteger;
      case 'is_Rational':
        return e instanceof sj.Rational;
      case 'is_rational':
        return sj.ask(sj.Q.rational(e)) === true;
      case 'is_commutative':
        return e.isCommutative;
      case 'is_Mul':
        return e instanceof sj.Mul;
      case 'is_Add':
        return e instanceof sj.Add;
      case 'is_Pow':
        return e instanceof sj.Pow;
      case 'is_Symbol':
        return e instanceof Sym;
      case 'is_Derivative':
        return e instanceof sj.Derivative;
      case 'is_Function':
        return e instanceof sj.Fn || e instanceof sj.UndefFn;
      default:
        throw new Unsupported(`predicate ${this.attr}`);
    }
  }
}

/** SymPy Lambda(variables, expr). */
export class JsLambda {
  constructor(
    readonly vars: Expr[],
    readonly body: Expr,
  ) {}
  call(...xs: Expr[]): Expr {
    return sj.xreplace(this.body, this.vars.map((v, i) => [v, xs[i]!] as [Expr, Expr]));
  }
  /** Python arithmetic on primitive callback arguments (not symbolic sympification). */
  callStrings(...xs: unknown[]): unknown {
    const env = new Map(this.vars.map((v, i) => [v.key, xs[i]]));
    const visit = (e: Expr): unknown => {
      if (env.has(e.key)) return env.get(e.key);
      if (e instanceof sj.Rational || e instanceof sj.Float) return e.value;
      const values = e.args.map(visit);
      if (e instanceof sj.Add && values.every((v) => typeof v === 'string')) return values.join('');
      if (e instanceof sj.Mul) {
        const strings = values.filter((v): v is string => typeof v === 'string');
        const numbers = values.filter((v): v is number => typeof v === 'number');
        const count = numbers.reduce((a, b) => a * b, 1);
        if (strings.length === 1 && numbers.length + 1 === values.length && Number.isSafeInteger(count)) return strings[0]!.repeat(Math.max(0, count));
      }
      throw new Unsupported('Python callback arithmetic on these primitive values');
    };
    return visit(this.body);
  }
}

/** A Lambda inside an expression is a Lambda node (a JsLambda is the form passed as an argument). */
const lambdaAsNode = (v: unknown): unknown => v instanceof sj.AlgebraicNumber ? (v.alias ?? v.asExpr()) : v instanceof JsLambda ? sj.Lambda(v.vars, expressionContainer(v.body)) : v;

/** A library function passed as an argument (equal_valued, factor, math.isclose, ...). */
export class JsFunc {
  constructor(readonly name: string) {}
}

export class UFnClass {
  constructor(readonly name: string, readonly nargs?: number[]) {}
}

/** A built-in SymPy function class such as `sin`. */
export class FnClass {
  constructor(readonly name: string) {}
}

/** The SymPy classes of the public constructors that are heads (SymPy expr.func), by their printed path. */
const HEAD_CLASSES = new Map<unknown, string>([
  [sj.Add, 'core.add.Add'], [sj.Mul, 'core.mul.Mul'], [sj.Pow, 'core.power.Pow'], [sj.Sym, 'core.symbol.Symbol'], [sj.Dummy, 'core.symbol.Dummy'],
  [sj.Sum, 'concrete.summations.Sum'], [sj.Product, 'concrete.products.Product'],
  [sj.Eq, 'core.relational.Equality'], [sj.Ne, 'core.relational.Unequality'], [sj.Lt, 'core.relational.StrictLessThan'],
  [sj.Le, 'core.relational.LessThan'], [sj.Gt, 'core.relational.StrictGreaterThan'], [sj.Ge, 'core.relational.GreaterThan'],
]);

/** A SymPy class object such as `Mul` or `Symbol`. */
export class TypeRef {
  constructor(readonly name: string) {}
}

/** An item of a Python list, tuple, set or dict prints as its repr: Permutation(0, 1, 2) for a Permutation. */
const fmtItem = (v: unknown): string => {
  if (v instanceof sj.Permutation) return sj.permutationRepr(v);
  // members of the S<n>TransitiveSubgroups enumerations print their Enum repr inside containers
  if (v instanceof sj.TransitiveSubgroup) return v.repr();
  // a prime ideal of a number field prints its repr inside containers
  if (v instanceof sj.PrimeIdeal) return v.repr();
  // domain elements (PythonMPQ, Gaussian elements, ModularInteger, ANP) print their repr inside containers
  if (v instanceof sj.PythonMPQ || v instanceof sj.GaussianElement || v instanceof sj.ModularInteger || v instanceof sj.ANP) return v.repr();
  // DDM and SDM print their repr inside containers
  if (v instanceof sj.DDM || v instanceof sj.SDM) return v.repr();
  return fmt(v);
};

export function fmt(v: unknown): string {
  if (v instanceof sj.PolyElement && v.ring.domain instanceof sj.AlgebraicField) {
    // SymPy prints sparse algebraic coefficients in their ANP representation.
    const K = v.ring.domain;
    const terms = v.terms().map(([m, c], i) => {
      const negative = K.isNegative(K.convert(c));
      const monomial = m.flatMap((n, j) => n === 0 ? [] : [sj.str(v.ring.symbols[j]!) + (n === 1 ? '' : `**${n}`)]).join('*');
      const coeff = K.convert(negative && monomial ? sj.neg(c) : c);
      const factor = monomial && coeff.equals(K.one) ? '' : coeff.repr();
      return (i === 0 ? negative ? '-' : '' : negative ? ' - ' : ' + ') + factor + (factor && monomial ? '*' : '') + monomial;
    });
    return terms.join('') || K.convert(0).repr();
  }
  if (v instanceof Expr) return sj.str(v);
  if (v instanceof Matrix) return v.toString();
  if (v instanceof sj.Poly) return v.toString();
  if (v instanceof sj.AlgebraicNumber) return sj.str(v.asExpr());
  if (v instanceof sj.GroebnerBasis) return v.toString();
  if (v instanceof sj.Monomial || v instanceof sj.Factors || v instanceof sj.DomainMatrix) return v.toString();
  if (v instanceof JsFloat) return Number.isInteger(v.v) ? v.v.toFixed(1) : String(v.v);
  if (v instanceof Error) return v.message;
  if (v instanceof Map) return fmt(new JsDict([...v]));
  if (Array.isArray(v)) return fmt(new JsTuple(v));
  if (v instanceof Set) return fmt(new JsSet([...v]));
  if (v === -Infinity) return '-oo';
  if (typeof v === 'boolean') return v ? 'True' : 'False';
  if (v === null || v === undefined) return 'None';
  if (typeof v === 'number' || typeof v === 'bigint') return String(v);
  if (v === 'EmptySet') return 'EmptySet';
  if (typeof v === 'string') return v.includes("'") && !v.includes('"') ? `"${v}"` : `'${v}'`;
  if (v instanceof JsList || (v instanceof JsTuple && v.isList)) return `[${v.items.map(fmtItem).join(', ')}]`;
  if (v instanceof JsTuple) return v.items.length === 1 ? `(${fmtItem(v.items[0])},)` : `(${v.items.map(fmtItem).join(', ')})`;
  if (v instanceof JsDefaultDict) return `defaultdict(<class 'int'>, ${fmt(new JsDict(v.entries))})`;
  if (v instanceof JsDict) return `{${v.entries.map(([k, x]) => `${fmtItem(k)}: ${fmtItem(x)}`).join(', ')}}`;
  if (v instanceof JsFrozenSet) return `frozenset(${fmt(new JsSet(v.items))})`;
  if (v instanceof JsSet) return v.items.length === 0 ? 'set()' : `{${v.items.map(fmtItem).join(', ')}}`;
  if (v instanceof UFnClass || v instanceof FnClass) return v.name;
  // a function class (expm1, isnan): its name
  if (typeof v === 'function' && 'functionName' in v && typeof v.functionName === 'string') return v.functionName;
  // an unapplied predicate (Q.even)
  if (typeof v === 'function' && typeof (v as { predicateName?: unknown }).predicateName === 'string') return String(v);
  if (v instanceof TypeRef) return `<class 'sympy.${v.name}'>`;
  // library objects with their own SymPy-like str (Cycle, PropKB, ...)
  if (typeof v === 'object' && (v as { toString: unknown }).toString !== Object.prototype.toString) return String(v);
  throw new Unsupported(`cannot format ${String(v)}`);
}

/** Split the top level of "{a, b: c, ...}" into items (bracket aware). */
function topLevelItems(s: string): string[] {
  const inner = s.slice(1, -1);
  const out: string[] = [];
  let depth = 0;
  let cur = '';
  for (const ch of inner) {
    if ('([{'.includes(ch)) depth++;
    if (')]}'.includes(ch)) depth--;
    if (ch === ',' && depth === 0) {
      out.push(cur.trim());
      cur = '';
    } else cur += ch;
  }
  if (cur.trim()) out.push(cur.trim());
  return out;
}

/**
 * Python set and dict literals at any depth with their items sorted: sets
 * print in hash order, and SymPy fills its result dicts while iterating
 * sets, so neither order carries meaning (top-level dicts and sets are
 * already compared without order).
 */
function normalizeSets(s: string): string {
  let out = '';
  let i = 0;
  while (i < s.length) {
    const ch = s[i]!;
    if (ch !== '{') {
      out += ch;
      i++;
      continue;
    }
    // find the matching brace
    let depth = 0;
    let j = i;
    for (; j < s.length; j++) {
      if ('([{'.includes(s[j]!)) depth++;
      if (')]}'.includes(s[j]!)) depth--;
      if (depth === 0) break;
    }
    const inner = s.slice(i, j + 1);
    const items = topLevelItems(inner).map(normalizeSets);
    out += `{${[...items].sort().join(', ')}}`;
    i = j + 1;
  }
  return out;
}

/** Compare with Python's str(); dict and set item order is ignored. */
/** SymPy results printed in a non-canonical form that symjs prints canonically (the same object). */
const PRINT_ALIASES: Readonly<Record<string, string>> = { 'Interval(-oo, oo)': 'Reals' };
/** QQ elements of SymPy's pure Python ground types print as MPQ(p,q): the rational p/q. */
const MPQ_RE = /MPQ\((-?\d+),(\d+)\)/g;
const unMPQ = (s: string): string => s.replace(MPQ_RE, (_m, p: string, q: string) => (q === '1' ? p : `${p}/${q}`));
// Matrix reprs nested inside other objects use multiline layout in SymPy.
// Ignore spacing at delimiters, preserving quoted strings and symbol names.
const normalizeLayout = (s: string): string => s.replace(/'(?:\\.|[^'\\])*'|"(?:\\.|[^"\\])*"|[^'"]+/g,
  (part) => /^["']/.test(part) ? part : part.replace(/\s*([()[\]{},])\s*/g, '$1'));
export function matches(v: unknown, expectedIn: string): boolean {
  const got = fmt(v);
  if (expectedIn.includes('MPQ(') && got !== expectedIn) return matches0(v, unMPQ(expectedIn), unMPQ(got));
  return matches0(v, expectedIn, got);
}
function matches0(v: unknown, expected: string, got: string): boolean {
  if (got === expected || PRINT_ALIASES[expected] === got) return true;
  if (normalizeLayout(got) === normalizeLayout(expected)) return true;
  if (v instanceof sj.GroebnerBasis && expected.startsWith('[')) return matches(new JsList(v.exprs), expected);
  if (v instanceof sj.SDM && expected.startsWith('{')) {
    // The corpus stores dense rows, which cannot preserve explicitly empty
    // sparse rows. Their presence does not change any matrix entry.
    const rows = (s: string) => topLevelItems(s).filter((row) => {
      const empty = /^(\d+):\s*\{\}$/.exec(row);
      return !empty || Number(empty[1]) >= v.rows;
    }).sort().join(',');
    if (rows(got) === rows(expected)) return true;
  }
  // JavaScript has one -Infinity for SymPy's -oo and Python's float -inf (dmp_degree of the zero polynomial)
  if (v === -Infinity && expected === '-inf') return true;
  if (got.includes('{') && normalizeSets(got) === normalizeSets(expected)) return true;
  const listPrefix = "defaultdict(<class 'list'>, ";
  if (expected.startsWith(listPrefix)) return matches(v, expected.slice(listPrefix.length, -1));
  const setPrefix = "defaultdict(<class 'set'>, ";
  if (expected.startsWith(setPrefix) && v instanceof JsDict) return matches(v, expected.slice(setPrefix.length, -1));
  const ddPrefix = "defaultdict(<class 'int'>, ";
  // a dict result is a Map, which prints as a dict (count_digits returns a defaultdict(int))
  if (expected.startsWith(ddPrefix) && (v instanceof JsDefaultDict || v instanceof JsDict)) return matches(new JsDict(v.entries), expected.slice(ddPrefix.length, -1));
  if ((v instanceof JsDict || v instanceof JsSet) && expected.startsWith('{')) {
    const a = topLevelItems(got).sort();
    const b = topLevelItems(expected).sort();
    return a.length === b.length && a.every((x, i) => x === b[i]);
  }
  if (v instanceof JsList || v instanceof JsTuple) {
    // JavaScript has only arrays: a Python tuple and list of the same items agree
    const brackets = (t: string) => t.replace(/,\)/g, ')').replace(/\(/g, '[').replace(/\)/g, ']');
    if (brackets(got) === brackets(expected)) return true;
    if (normalizeSets(brackets(got)) === normalizeSets(brackets(expected))) return true;
  }
  return false;
}

// ---------------------------------------------------------------------------
// Deserialization of SymPy objects
// ---------------------------------------------------------------------------

export type Tree = { t: string; [k: string]: unknown };

const diffgeomNamespace: Record<string, unknown> = dg;
function isDiffgeomTree(tree: Tree | undefined): boolean {
  return tree?.t === 'Diffgeom';
}

function diffgeomPlain(value: unknown): unknown {
  if (value instanceof JsList || value instanceof JsTuple) return value.items.map(diffgeomPlain);
  if (value instanceof JsDict) return new Map(value.entries.map(([k, v]) => [diffgeomPlain(k), diffgeomPlain(v)]));
  if (value instanceof JsLambda) {
    const body = diffgeomPlain(value.body);
    return sj.Lambda(value.vars, Array.isArray(body) ? new sj.Tuple(body) : (body as sj.Expr));
  }
  return value;
}
const diffgeomInteger = (v: unknown): number => Number(String(v));
function constructDiffgeom(name: string, args: unknown[], kwargs: Record<string, unknown> = {}): unknown {
  const fn = diffgeomNamespace[camel(name)];
  if (typeof fn !== 'function') throw new Unsupported(`diffgeom export ${name}`);
  const a = args.map(diffgeomPlain);
  if (['Manifold', 'CoordinateSymbol', 'BaseScalarField', 'BaseVectorField', 'BaseCovarDerivativeOp'].includes(name))
    a[1] = diffgeomInteger(a[1]);
  if (name === 'CoordSystem' && Object.keys(kwargs).length) {
    a[2] = a[2] ?? diffgeomPlain(kwargs['symbols'] ?? kwargs['names']);
    a[3] = a[3] ?? diffgeomPlain(kwargs['relations']);
  }
  if (name === 'intcurve_series') {
    a[3] = diffgeomInteger(a[3] ?? kwargs['n'] ?? 6);
    a[4] = { coordSys: a[4] ?? kwargs['coord_sys'], coeffs: a[5] ?? kwargs['coeffs'] ?? false };
    a.length = 5;
  }
  if (name === 'intcurve_diffequ') a[3] = a[3] ?? kwargs['coord_sys'];
  const result = /^class[\s{]/.test(Function.prototype.toString.call(fn)) ? Reflect.construct(fn, a) : fn(...a);
  return name === 'intcurve_diffequ' ? new JsTuple((result as unknown[][]).map((xs) => new JsList(xs))) : result;
}

export function diffgeomAdapter(c: Case): Adapter | undefined {
  if (c.category !== 'diffgeom') return undefined;
  if (!c.fn.startsWith('.') && camel(c.fn) in diffgeomNamespace) return (args, kw) => constructDiffgeom(c.fn, args, kw);
  if ((c.fn.startsWith('.__') && c.fn !== '.__call__') || c.fn.startsWith('.is_')) return undefined;
  if (c.fn === '.rcall' || c.fn === '.__call__')
    return (args, _kw, self) => {
      if (!(self instanceof sj.Expr)) throw new Unsupported('not a callable field');
      return sj.rcall(self, ...(args.map(diffgeomPlain) as (sj.ExprLike | null)[]));
    };
  if (c.fn === '.rewrite' && isDiffgeomTree(c.self) && c.self?.['cls'] === 'CoordinateSymbol')
    return (args, _kw, self) => (self as dg.CoordinateSymbol).rewrite(args[0] as dg.CoordSystem);
  if (!isDiffgeomTree(c.self)) return undefined;
  const method = camel(c.fn.slice(1));
  return (args, kw, self) => {
    if (self === undefined || self === null) throw new Unsupported('missing receiver');
    const member: unknown = Reflect.get(self, method);
    const a = args.map(diffgeomPlain);
    if (['baseScalar', 'baseVector', 'baseOneform', 'coordFunction'].includes(method)) a[0] = diffgeomInteger(a[0]);
    if (method === 'connectTo') a[3] = { inverse: kw['inverse'], fillInGaps: kw['fill_in_gaps'] };
    if (member === undefined) throw new Unsupported(`diffgeom method ${method}`);
    const result =
      typeof member === 'function'
        ? Reflect.apply(member, self, a)
        : member instanceof sj.Expr && 'call' in member
          ? sj.rcall(member, ...(a as (sj.ExprLike | null)[]))
          : member;
    return method === 'symbols' ? new JsTuple(result as unknown[]) : result;
  };
}

const REL_OPS: Record<string, sj.RelOp> = {
  Equality: 'Eq',
  Unequality: 'Ne',
  StrictLessThan: 'Lt',
  LessThan: 'Le',
  StrictGreaterThan: 'Gt',
  GreaterThan: 'Ge',
};

const SPECIAL_NAMES = ['bernoulli', 'euler', 'genocchi', 'bell', 'fibonacci', 'lucas', 'tribonacci', 'partition', 'totient', 'reduced_totient', 'mobius', 'divisor_sigma', 'primenu', 'primeomega', 'primepi', 'multigamma', 'factorial', 'factorial2', 'binomial', 'ff', 'rf', 'subfactorial', 'harmonic', 'catalan', 'gamma', 'loggamma', 'polygamma', 'lowergamma', 'uppergamma', 'beta', 'zeta', 'erf', 'erfc', 'erfi', 'erf2', 'erfinv', 'erfcinv', 'erf2inv', 'Ei', 'li', 'Li', 'Si', 'Ci', 'Shi', 'Chi', 'expint', 'fresnels', 'fresnelc', 'sign', 'floor', 'ceiling', 'atan2', 'Min', 'Max'] as const;
/** Functions of the zeta, beta, elliptic and Appell families (functions/special/zetafunctions.ts, special.ts, ellipticintegrals.ts, hyper.ts). */
const ZETA_FAMILY_NAMES = ['polylog', 'lerchphi', 'dirichlet_eta', 'riemann_xi', 'stieltjes', 'betainc', 'betainc_regularized', 'elliptic_k', 'elliptic_e', 'elliptic_f', 'elliptic_pi', 'appellf1'] as const;
const definedOr = <T>(v: T | undefined, what: string): T => {
  if (v === undefined) throw new Unsupported(what);
  return v;
};

/** A serialized SymPy domain as the symjs domain (undefined when symjs has no counterpart). */
function deserializeDomain(tree: Tree): sj.Domain | undefined {
  if (tree['t'] === 'FiniteExtension') return new sj.FiniteExtension(deserialize(tree['modulus'] as Tree) as sj.Poly).toDomain();
  const name = tree['name'] as string;
  const known: Record<string, sj.Domain> = { ZZ: sj.ZZ, QQ: sj.QQ, RR: sj.RR, CC: sj.CC, EX: sj.EX, EXRAW: sj.EXRAW, ZZ_I: sj.ZZ_I, QQ_I: sj.QQ_I };
  if (tree['mod'] !== undefined) return sj.GF(tree['mod'] as number, tree['symmetric'] as boolean);
  if (tree['prec'] !== undefined) return (tree['prec'] as number) === 53 ? known[name] : undefined;
  if (tree['base'] === undefined) return known[name];
  const base = deserializeDomain(tree['base'] as Tree);
  if (base === undefined) return undefined;
  if (tree['minpoly'] !== undefined) {
    // a primitive element given by its minimal polynomial: a symbol root, or an alias (zeta, theta)
    const alias = tree['alias'] as string | null;
    const root = alias === null ? (deserialize(tree['ext'] as Tree) as Expr) : new Sym(alias);
    return new sj.AlgebraicField(base, new sj.AlgebraicNumber(root, [1, 0], { minpoly: deserialize(tree['minpoly'] as Tree) as sj.Poly, ...(alias === null ? {} : { alias }) }));
  }
  if (tree['ext'] !== undefined) return base.algebraicField(...(tree['gens'] as Tree[]).map((t) => deserialize(t) as Expr));
  const symbols = (tree['symbols'] as Tree[]).map((t) => deserialize(t) as Sym);
  if (tree['oldPolyRing'] === true) return new sj.PolynomialRingBase(base, symbols, tree['order'] as string);
  return name.endsWith(']') ? base.polyRing(...symbols) : base.fracField(...symbols);
}

/**
 * The ring of a polynomial matrix: SymPy's PolynomialRing domain K[gens] is a
 * coefficient domain K (itself possibly a polynomial ring, as in QQ[x][y])
 * and generators; a string names the ring.
 */
function polyMatrixRing(v: unknown): sj.PolyMatrixRing | string {
  if (typeof v === 'string') return v;
  const tree = v instanceof JsDomain ? v.definition : undefined;
  if (tree === undefined || tree['base'] === undefined || tree['symbols'] === undefined || !(tree['name'] as string).endsWith(']')) throw new Unsupported('polynomial matrix ring');
  const base = deserializeDomain(tree['base'] as Tree);
  if (base === undefined) throw new Unsupported('polynomial matrix coefficient domain');
  return new sj.PolyMatrixRing(base, (tree['symbols'] as Tree[]).map((t) => deserialize(t) as Expr));
}

/** SymPy PolyMatrix arguments: lists as arrays, a generator tuple as an array, an entry lambda as a function of (i, j). */
function polyMatrixArgs(args: unknown[], kw: Record<string, unknown>): unknown[] {
  const converted = args.map((a) => a instanceof JsLambda ? (i: number, j: number) => a.call(sj.Rational.of(BigInt(i)), sj.Rational.of(BigInt(j))) : toJs(a, true));
  return kw['ring'] === undefined ? converted : [...converted, { ring: polyMatrixRing(kw['ring']) }];
}

/** The parameter tuples of a serialized hyper or meijerg. */
const tupleItems = (t: unknown): Expr[] => (t as JsTuple).items.map((x) => x as Expr);

const FUNCTIONS: Record<string, (args: Expr[]) => Expr> = {
  LaplaceTransform: ([f, t, s]) => new sj.LaplaceTransform(f!, t as Sym, s as Sym),
  InverseLaplaceTransform: ([F, s, t, plane]) => new sj.InverseLaplaceTransform(F!, s as Sym, t as Sym, plane instanceof sj.Dummy && plane.name === 'None' ? undefined : plane),
  DiracDelta: ([x, k]) => sj.DiracDelta(x!, k),
  Heaviside: ([x, h0]) => sj.Heaviside(x!, h0),
  SingularityFunction: ([x, a, n]) => sj.SingularityFunction(x!, a!, n!),
  Mod: ([a, b]) => sj.Mod(a!, b!),
  // the C99 math functions of sympy.codegen.cfunctions
  ...Object.fromEntries(([sj.expm1, sj.log1p, sj.exp2, sj.log2, sj.fma, sj.log10, sj.Sqrt, sj.Cbrt, sj.hypot, sj.isnan, sj.isinf] as const).map((f) => [f.functionName, (args: Expr[]) => f(...args)])),
  SchurNumber: ([k]) => sj.SchurNumber(k!),
  ...Object.fromEntries(SPECIAL_NAMES.map((n) => [n, (args: Expr[]) => sj.fn(n, args)])),
  RisingFactorial: (args) => sj.fn('rf', args),
  Rem: ([p, q]) => sj.Rem(p!, q!),
  KroneckerDelta: ([i, j]) => sj.KroneckerDelta(i!, j!),
  ...Object.fromEntries(ZETA_FAMILY_NAMES.map((n) => [n, (args: Expr[]) => sj.fn(n, args)])),
  hyper: ([ap, bq, z]) => sj.hyper(tupleItems(ap), tupleItems(bq), z!),
  meijerg: ([a, b, z]) => {
    const [an, ap] = (a as unknown as JsTuple).items;
    const [bm, bq] = (b as unknown as JsTuple).items;
    return sj.meijerg(tupleItems(an), tupleItems(ap), tupleItems(bm), tupleItems(bq), z!);
  },
  jn: ([n, z]) => sj.jn(n!, z!),
  yn: ([n, z]) => sj.yn(n!, z!),
  Lambda: ([vs, body]) => new JsLambda((vs as unknown as JsTuple).items as Expr[], body!) as unknown as Expr,
  FallingFactorial: (args) => sj.fn('ff', args),
  exp: ([a]) => sj.exp(a!),
  Abs: ([a]) => sj.abs(a!),
  log: (args) => sj.log(args[0]!, args[1]),
  LambertW: (args) => sj.LambertW(args[0]!, args[1]),
  ...Object.fromEntries((['besselj', 'bessely', 'besseli', 'besselk', 'airyai', 'airybi', 'airyaiprime', 'airybiprime'] as const).map((n) => [n, (args: Expr[]) => sj.fn(n, args)])),
  ...Object.fromEntries((['hankel1', 'hankel2', 'hn1', 'hn2', 'marcumq', 'Ynm', 'Znm', 'mathieus', 'mathieuc', 'mathieusprime', 'mathieucprime'] as const).map((n) => [n, (args: Expr[]) => sj.fn(n, args)])),
  ...Object.fromEntries((['jacobi', 'gegenbauer', 'chebyshevt', 'chebyshevu', 'legendre', 'assoc_legendre', 'hermite', 'hermite_prob', 'laguerre', 'assoc_laguerre'] as const).map((n) => [n, (args: Expr[]) => sj.fn(n, args)])),
  frac: ([a]) => sj.frac(a!),
  ...Object.fromEntries(
    (['sin', 'cos', 'tan', 'asin', 'acos', 'atan', 'sinh', 'cosh', 'tanh', 're', 'im', 'arg', 'conjugate', 'adjoint', 'transpose', 'cot', 'sec', 'csc', 'acot', 'asec', 'acsc', 'coth', 'sech', 'csch', 'asinh', 'acosh', 'atanh', 'acoth', 'asech', 'acsch', 'sinc', 'exp_polar', 'polar_lift', 'periodic_argument', 'principal_branch'] as const).map(
      (n) => [n, (args: Expr[]) => sj.fn(n, args)],
    ),
  ),
  Piecewise: (args) =>
    sj.piecewise(
      ...(args as unknown as JsTuple[]).map((t) => {
        const [e, c] = t.items;
        return [asExpr(e), typeof c === 'boolean' ? c : asExpr(c)] as const;
      }),
    ),
  Integral: (args) => integralNode(args),
  NonElementaryIntegral: (args) => new sj.NonElementaryIntegral(integralNode(args).args),
  Sum: (args) => concreteNode('Sum', args),
  Product: (args) => concreteNode('Product', args),
  Limit: (args) => new sj.Limit(args as Expr[]),
  Order: ([e, ...rest]) => orderNode(e!, rest),
};

const OP_STR: Record<string, sj.RelOp> = { '<': 'Lt', '>': 'Gt', '<=': 'Le', '>=': 'Ge', '==': 'Eq', '!=': 'Ne' };
function reduceAbs(e: Expr, op: string, x: Sym): Expr {
  const r = OP_STR[op];
  if (!r) throw new Unsupported(`relation ${op}`);
  return sj.solveUnivariateInequality(sj.rel(r, e, S.Zero), x);
}

function integralNode(args: unknown[]): Expr {
  // several limits: nested integrals, innermost first
  if (args.length > 2) return args.slice(2).reduce<Expr>((acc, l) => integralNode([acc, l]), integralNode(args.slice(0, 2)));
  const [f, lim] = args;
  if (lim === undefined) {
    const fs = [...sj.freeSymbols(f as Expr)];
    if (fs.length === 1) return new Integral([f as Expr, fs[0]!]);
  }
  if (lim instanceof Sym) return new Integral([f as Expr, lim]);
  if (lim instanceof JsTuple && lim.items.length === 3) return new Integral([f as Expr, ...(lim.items as Expr[])]);
  if (lim instanceof JsTuple && lim.items.length === 1) return new Integral([f as Expr, lim.items[0] as Expr]);
  if (lim instanceof JsTuple && lim.items.length === 2 && args.length === 2) return new Integral([f as Expr, ...(lim.items as Expr[])]);
  throw new Unsupported('Integral limits');
}

const concreteDoit = (e: Expr): Expr => (e instanceof sj.Concrete ? sj.doitConcrete(e) : e);

function concreteNode(kind: 'Sum' | 'Product', args: unknown[]): Expr {
  const [f, ...lims] = args;
  const ls = lims.map((l) => {
    if (!(l instanceof JsTuple) || l.items.length !== 3) throw new Unsupported('limits');
    return l.items as [Sym, Expr, Expr];
  });
  return kind === 'Sum' ? sj.Sum(f as Expr, ...ls) : sj.Product(f as Expr, ...ls);
}

function orderNode(e: unknown, rest: unknown[]): Expr {
  const r = rest[0];
  if (r === undefined) return sj.O(e as Expr);
  if (rest.length > 1) {
    // O(e, x, y) or O(e, (x, p), (y, p))
    if (rest.every((t) => t instanceof Sym)) return sj.O(e as Expr, rest as Sym[]);
    if (rest.every((t) => t instanceof JsTuple && t.items.length === 2)) {
      const ts = rest as JsTuple[];
      const p = ts[0]!.items[1] as Expr;
      if (ts.some((t) => (t.items[1] as Expr).key !== p.key)) throw new Unsupported('Order points');
      return sj.O(e as Expr, ts.map((t) => t.items[0] as Sym), p);
    }
    throw new Unsupported('Order arguments');
  }
  if (r instanceof JsTuple && r.items.length === 2) return sj.O(e as Expr, r.items[0] as Sym, r.items[1] as Expr);
  if (r instanceof Sym) return sj.O(e as Expr, r);
  throw new Unsupported('Order arguments');
}

export function deserialize(tree: Tree): unknown {
  switch (tree.t) {
    case 'Diffgeom': {
      if ('ref' in tree) {
        const name = camel(String(tree['ref']));
        if (!(name in diffgeomNamespace)) throw new Unsupported(`diffgeom reference ${name}`);
        return diffgeomNamespace[name];
      }
      return constructDiffgeom(String(tree['cls']), (tree['args'] as Tree[]).map(deserialize));
    }
    case 'PublicObject': {
      const name = String(tree['cls']);
      const cls = (sj as unknown as Record<string, unknown>)[name];
      if (typeof cls !== 'function') throw new Unsupported(`class ${name}`);
      // Container conversion only: the public constructor owns all computation.
      const args = (tree['args'] as Tree[]).map((a) => name === 'Factors' ? plain(deserialize(a)) : toJs(deserialize(a), true));
      return /^class[\s{]/.test(Function.prototype.toString.call(cls))
        ? Reflect.construct(cls, args) : cls(...args);
    }
    case 'PolyMatrix': {
      const ring = polyMatrixRing(deserialize(tree['ring'] as Tree));
      const rows = toJs(deserialize(tree['entries'] as Tree), true) as sj.PolyMatrixEntry[][];
      const shape = tree['rows'] === undefined ? [rows.length, rows[0]?.length ?? 0] : [tree['rows'] as number, tree['cols'] as number];
      return sj.PolyMatrix.fromList(shape[0]!, shape[1]!, rows.flat(), [], ring);
    }
    case 'TransitiveSubgroup': {
      const groups = [sj.S1TransitiveSubgroups, sj.S2TransitiveSubgroups, sj.S3TransitiveSubgroups, sj.S4TransitiveSubgroups, sj.S5TransitiveSubgroups, sj.S6TransitiveSubgroups];
      const group = groups[Number(tree['degree']) - 1];
      const name = group && [...group].find((g) => g.name === String(tree['name']));
      if (name === undefined) throw new Unsupported('transitive subgroup name');
      return name;
    }
    case 'SATSolver': return sj.SATSolver.fromState({
      clauses: tree['clauses'] as number[][], variables: Number(tree['variables']),
      settings: tree['settings'] as number[], variableSet: tree['variableSet'] as boolean[],
      sentinels: tree['sentinels'] as [number, number[]][], scores: tree['scores'] as [number, number][],
      heap: tree['heap'] as [number, number][], learned: Number(tree['learned']),
      levels: (tree['levels'] as Tree[]).map((entry) => ({ decision: Number(entry['decision']), flipped: Boolean(entry['flipped']), settings: entry['settings'] as number[] })),
      queue: tree['queue'] as number[], unsatisfied: Boolean(tree['unsatisfied']),
    });
    case 'SATLevel': {
      const level = new sj.Level(Number(tree['decision']), Boolean(tree['flipped']));
      for (const lit of tree['settings'] as number[]) level.varSettings.add(lit);
      return level;
    }
    case 'GrayCode': return new sj.GrayCode(Number(tree['n']), { start: String(tree['current']) });
    case 'PartComponent': {
      const part = new sj.PartComponent();
      part.c = Number(tree['c']); part.u = Number(tree['u']); part.v = Number(tree['v']);
      return part;
    }
    case 'Predicate': return sj.Q[String(tree['name'])] ?? sj.Predicate(String(tree['name']));
    case 'Kind': {
      const kind = (sj as unknown as Record<string, unknown>)[String(tree['name'])];
      if (!(kind instanceof sj.Kind)) throw new Unsupported(`kind ${String(tree['name'])}`);
      return kind;
    }
    case 'GlobalParameters':
      if (tree['evaluate'] !== sj.globalParameters.evaluate) throw new Unsupported('non-default global parameters');
      return sj.globalParameters;
    case 'Slice': {
      const part = (name: string): number | undefined => {
        const value = deserialize(tree[name] as Tree);
        return value === null ? undefined : Number(value);
      };
      return sj.slice(part('start'), part('stop'), part('step'));
    }
    case 'Transform': {
      const variable = deserialize(tree['var'] as Tree) as Expr;
      const body = asExpr(deserialize(tree['body'] as Tree));
      const condition = asExpr(deserialize(tree['condition'] as Tree));
      return new sj.Transform((key: sj.ExprLike) => sj.subs(body, [[variable, key]]),
        (key: sj.ExprLike) => sj.subs(condition, [[variable, key]]).equals(S.true));
    }
    case 'ECMPoint': {
      const [x, z, a24, mod] = (tree['coords'] as string[]).map(BigInt);
      return new sj.ECMPoint(x!, z!, a24!, mod!);
    }
    case 'ExtensionElement':
      return new sj.FiniteExtension(deserialize(tree['modulus'] as Tree) as sj.Poly).convert(deserialize(tree['expr'] as Tree) as Expr);
    case 'DMP': {
      if (tree['level'] !== 0) throw new Unsupported('multivariate DMP');
      const domain = deserializeDomain(tree['domain'] as Tree);
      if (!domain) throw new Unsupported('DMP domain');
      const ring = domain.oldPolyRing(new Sym('_x'));
      return new sj.DMP((deserialize(tree['coeffs'] as Tree) as JsTuple).items.map((c) => c instanceof sj.PythonMPQ ? sj.Rational.of(c.numerator, c.denominator) : asExpr(c)), ring);
    }
    case 'CartanType':
      return sj.CartanType(`${String(tree['series'])}${String(tree['n'])}`);
    case 'RootSystem':
      return new sj.RootSystem(deserialize(tree['cartanType'] as Tree) as sj.StandardCartan);
    case 'WeylGroup':
      return new sj.WeylGroup(deserialize(tree['cartanType'] as Tree) as sj.StandardCartan);
    case 'FFElement':
      return new JsFFElement(BigInt(tree['v'] as number), BigInt(tree['mod'] as number), tree['symmetric'] as boolean);
    case 'Js':
      return tree['v'];
    case 'Quaternion': {
      const [a, b, c, d] = (tree['args'] as Tree[]).map((t) => deserialize(t) as Expr);
      const norm = tree['norm'] === null ? undefined : (deserialize(tree['norm'] as Tree) as Expr);
      return sj.Quaternion(a, b, c, d, { realField: tree['realField'] as boolean, norm });
    }
    case 'Basic':
      return sj.Basic(...(tree['args'] as Tree[]).map((t) => deserialize(t) as Expr));
    case 'Str':
      return tree['v'];
    case 'Rational':
      if (tree['mpq']) return new sj.PythonMPQ(BigInt(tree['p'] as string), BigInt(tree['q'] as string));
      return sj.Rational.of(BigInt(tree['p'] as string), BigInt(tree['q'] as string));
    case 'GaussianElement': {
      // an element x + y*I of ZZ_I or QQ_I
      const dom = tree['domain'] === 'ZZ_I' ? sj.ZZ_I : sj.QQ_I;
      return dom.new(deserialize(tree['x'] as Tree), deserialize(tree['y'] as Tree));
    }
    case 'EXElement':
      return new sj.Expression(deserialize(tree['ex'] as Tree) as Expr);
    case 'ANP':
      // an element of an algebraic number field (coefficients in the primitive element, its minimal polynomial)
      return new sj.ANP((tree['rep'] as Tree[]).map(deserialize), (tree['mod'] as Tree[]).map(deserialize), deserializeDomain(tree['dom'] as Tree));
    case 'Float': {
      if (tree['man'] !== undefined) {
        return new sj.Float({ man: BigInt(tree['man'] as string), exp: BigInt(tree['exp'] as number) }, tree['prec'] as number);
      }
      const value = tree['v'];
      // JSON cannot encode IEEE non-finite numbers as numeric literals.
      if (value === 'Infinity') return sj.S.Infinity;
      if (value === '-Infinity') return sj.S.NegativeInfinity;
      if (value === 'NaN') return sj.S.NaN;
      if (typeof value !== 'number') throw new Unsupported('Float value');
      return new sj.Float(value);
    }
    case 'Symbol': {
      const a = tree['assume'] as Record<string, boolean>;
      return new Sym(tree['name'] as string, Object.fromEntries(Object.entries(a).map(([k,v]) => [camel(k),v])));
    }
    case 'DiagramGrid': {
      const entries = (deserialize(tree['morphisms'] as Tree) as JsDict).entries;
      const d = sj.Diagram(new Map(entries.map(([m, p]) => [m as sj.Morphism, p as sj.SetExpr])));
      const grid = new categories.DiagramGrid(d);
      // the serialized grid lists its morphisms; rebuilding the diagram from them would compose them again
      grid.morphisms.clear();
      for (const [m, p] of entries) grid.morphisms.set(m as sj.Morphism, p as sj.SetExpr);
      const cells = (tree['cells'] as Tree[][]).map((row) => row.map(deserialize));
      const storage = new GrowableGrid<Expr>(cells[0]?.length ?? 0, cells.length);
      cells.forEach((row, i) => row.forEach((cell, j) => storage.set(i, j, cell instanceof Expr ? cell : sj.NoMatch)));
      Object.defineProperty(grid, 'grid', { value: storage });
      return grid;
    }
    case 'XypicDiagramDrawer': {
      const drawer = new categories.XypicDiagramDrawer();
      drawer.unit = String(tree['unit']); drawer.defaultCurvingAmount = Number(tree['amount']); drawer.defaultCurvingStep = Number(tree['step']);
      const formatter = (state: Record<string, unknown>) => (arrow: categories.ArrowStringDescription) => {
        for (const [key, v] of Object.entries(state)) Reflect.set(arrow, camel(key), typeof v === 'string' ? v.replace(/@([a-z_]+)@/g, (_, name: string) => String(Reflect.get(arrow, camel(name)))) : v);
      };
      if (tree['defaultFormatter']) drawer.defaultArrowFormatter = formatter(tree['defaultFormatter'] as Record<string, unknown>);
      for (const [name, f] of Object.entries(tree['formatters'] as Record<string, Record<string, unknown>>)) drawer.arrowFormatters.set(name, formatter(f));
      return drawer;
    }
    case 'CategoryObject': return new sj.SymObject(String(tree['name']));
    case 'CategoryClass': return new sj.CategoryClass(deserialize(tree['objects'] as Tree) as sj.SetExpr);
    case 'Category': return sj.Category(String(tree['name']), deserialize(tree['objects'] as Tree) as sj.SetExpr, (tree['diagrams'] as Tree[]).map((d) => deserialize(d) as sj.Diagram));
    case 'Morphism': {
      const args = (tree['args'] as Tree[]).map(deserialize);
      if (tree['cls'] === 'IdentityMorphism') return sj.IdentityMorphism(asExpr(args[0]));
      if (tree['cls'] === 'NamedMorphism') return sj.NamedMorphism(asExpr(args[0]), asExpr(args[1]), String(args[2]));
      return sj.CompositeMorphism((args[0] as JsTuple).items as sj.Morphism[]);
    }
    case 'Diagram': {
      const input = (t: Tree): sj.Dict => sj.Dict((deserialize(t) as JsDict).entries.map(([k, v]) => [asExpr(k), asExpr(v)]));
      return sj.Diagram(input(tree['premises'] as Tree), input(tree['conclusions'] as Tree));
    }
    case 'Const': {
      const m: Record<string, Expr> = {
        pi: S.Pi,
        E: S.E,
        I: S.I,
        oo: S.Infinity,
        '-oo': S.NegativeInfinity,
        zoo: S.ComplexInfinity,
        nan: S.NaN,
        EulerGamma: S.EulerGamma,
        Catalan: S.Catalan,
        GoldenRatio: S.GoldenRatio,
        TribonacciConstant: S.TribonacciConstant,
      };
      return m[tree['name'] as string];
    }
    case 'Add': {
      const args = (tree['args'] as Tree[]).map((a) => lambdaAsNode(deserialize(a)) as Expr);
      if (tree['evaluate'] === false) return new sj.Add(args);
      // A numeric term after a symbolic one records an unevaluated argument order.
      if (args.slice(1).some((a) => a instanceof sj.Rational || a instanceof sj.Float)) return new sj.Add(args);
      return sj.add(...args);
    }
    case 'Mul':
    case 'MatMul': {
      const args = (tree['args'] as Tree[]).map((a) => lambdaAsNode(deserialize(a)) as Expr);
      if (tree['t'] === 'Mul' && tree['evaluate'] === false) return new sj.Mul(args);
      // SymPy distributes a number over a sum (2*(x + 1) -> 2*x + 2): a Mul(number, Add) was built with evaluate=False
      if (tree['t'] === 'Mul' && args.length === 2 && args[0] instanceof sj.Rational && args[1] instanceof sj.Add) return new sj.Mul(args);
      // a product of numbers and powers of numbers that SymPy kept as a Mul was built with evaluate=False
      // (factorint(n, visual=True))
      const numeric = (a: Expr): boolean => a instanceof sj.Rational || (a instanceof sj.Pow && a.base instanceof sj.Rational && a.exp instanceof sj.Rational && a.exp.isInteger);
      if (tree['t'] === 'Mul' && args.length > 1 && args.every(numeric) && args.some((a) => a instanceof sj.Pow)) return new sj.Mul(args);
      // Canceled reciprocal factors in a serialized Mul prove it was unevaluated.
      // Preserve its domain restrictions (e.g. x * 1/x at x = 0).
      if (tree['t'] === 'Mul' && args.some((a) => a instanceof sj.Pow && a.exp instanceof sj.Rational && a.exp.isNegative && args.some((b) => b.equals(a.base)))) return new sj.Mul(args);
      if (tree['t'] === 'Mul' && args.length > 1 && args.some((a) => a.equals(S.One))) return new sj.Mul(args);
      const result = sj.mul(...args);
      // A retained product of numeric roots can have been built unevaluated;
      // retain it only when canonicalization would remove the Mul itself.
      if (tree['t'] === 'Mul' && !(result instanceof sj.Mul) && args.every((a) => a instanceof sj.Rational || (a instanceof sj.Pow && a.base instanceof sj.Rational && a.exp instanceof sj.Rational))) return new sj.Mul(args);
      return result;
    }
    case 'AccumBounds':
      return sj.AccumBounds(deserialize(tree['min'] as Tree) as Expr, deserialize(tree['max'] as Tree) as Expr);
    case 'Geom': {
      // a geometric entity rebuilt by its class constructor from its arguments (Tuples as arrays)
      const cls = tree['cls'] as string;
      const args = (tree['args'] as Tree[]).map((a) => {
        const v = deserialize(a);
        return v instanceof JsTuple ? v.items : v;
      });
      const lib = sj as unknown as Record<string, (...a: unknown[]) => unknown>;
      if (cls === 'Plane') return sj.Plane(args[0] as Expr, { normalVector: args[1] as Expr[] });
      if (/^Point/.test(cls)) return lib[cls]!(...args, { evaluate: false });
      return lib[cls]!(...args);
    }
    case 'Vec':
      return deserializeVector(tree);
    case 'Stats':
      return deserializeStats(tree);
    case 'Indexed': {
      const base = deserialize(tree['base'] as Tree);
      const indices = (tree['indices'] as Tree[]).map((t) => asExpr(deserialize(t)));
      if (base instanceof sj.IndexedBase) return base.at(...indices);
      // an array indexed by symbols (a[i, j]) is SymPy's Indexed with the array as its base
      return base instanceof sj.NDimArray ? base.get(...indices) : new sj.Indexed([asExpr(base), ...indices]);
    }
    case 'IndexedBase':
      return new sj.IndexedBase(deserialize(tree['label'] as Tree) as Sym, tree['shape'] === undefined ? {} : { shape: (tree['shape'] as Tree[]).map((t) => asExpr(deserialize(t))) });
    case 'StrategySubs': {
      const mapping = deserialize(tree['mapping'] as Tree) as JsDict;
      return sj.tools.subs(new Map(mapping.entries.map(([k, v]) => [asExpr(k), asExpr(v)])));
    }
    case 'DirectionalDerivative': {
      const vector = asExpr(deserialize(tree['vector'] as Tree));
      return (field: Expr) => sj.directionalDerivative(field, vector);
    }
    case 'PureKeyDict': {
      const entries = new Map((tree['items'] as [Tree, Tree][]).map(([k, v]) => [deserialize(k) as sj.Poly, deserialize(v)]));
      const key = (value: Expr | sj.Poly): sj.Poly | undefined => {
        if (!(value instanceof sj.Poly) && value.freeSymbols().size !== 1) return undefined;
        const poly = value instanceof sj.Poly ? value : sj.PurePoly(value);
        return [...entries.keys()].find((p) => p.equals(poly));
      };
      return {
        contains: (value: Expr | sj.Poly) => key(value) !== undefined,
        getitem: (value: Expr | sj.Poly) => {
          const k = key(value);
          if (k === undefined) throw new RangeError('KeyError: the key is not in the dict');
          return entries.get(k);
        },
      };
    }
    case 'CRootOf':
      return new sj.CRootOf(deserialize(tree['poly'] as Tree) as Expr, tree['index'] as number);
    case 'Pow': {
      const [b, e] = (tree['args'] as Tree[]).map((a) => deserialize(a) as Expr);
      if (tree['evaluate'] === false && b !== undefined && e !== undefined) return new sj.Pow(b, e);
      // a power of rationals that SymPy kept as a Pow was built with evaluate=False
      // (an integer power too large to compute, Pow(2, 10**16, evaluate=False), is kept as it is)
      if (b instanceof sj.Rational && e instanceof sj.Rational && e.isInteger && e.p > 100000n) return new sj.Pow(b, e);
      if (b instanceof sj.Rational && e instanceof sj.Rational && e.isInteger && sj.pow(b, e) instanceof sj.Rational) return new sj.Pow(b, e);
      // a power of a power that SymPy did not combine ((1/x)**-1) was built unevaluated too
      if (b instanceof sj.Pow) {
        const v = sj.pow(b, e!);
        if (!(v instanceof sj.Pow && v.base.key === b.key)) return new sj.Pow(b, e!);
      }
      return sj.pow(b!, e!);
    }
    case 'Rel': {
      const op = REL_OPS[tree['op'] as string];
      if (!op) throw new Unsupported(`relation ${tree['op']}`);
      const [a, b] = (tree['args'] as Tree[]).map((x) => deserialize(x) as Expr);
      return sj.rel(op, a!, b!);
    }
    case 'Fn': {
      // a factorial too large to evaluate was built with evaluate=False in SymPy
      if (tree['name'] === 'factorial') {
        const a = deserialize((tree['args'] as Tree[])[0]!);
        if (a instanceof sj.Rational && a.q === 1n && a.p > 100000n) return new Fn('factorial', [a]);
      }
      const f = FUNCTIONS[tree['name'] as string];
      if (!f) throw new Unsupported(`function ${tree['name']}`);
      return f((tree['args'] as Tree[]).map((a) => deserialize(a)) as Expr[]);
    }
    case 'AlgebraicNumber':
      return new sj.AlgebraicNumber(deserialize(tree['root'] as Tree) as Expr, (tree['coeffs'] as Tree[]).map((t) => deserialize(t) as Expr), tree['alias'] === undefined ? {} : { alias: deserialize(tree['alias'] as Tree) as Sym });
    case 'Domain':
      // the domain object rebuilt from its parameters; ZZ/QQ also stay recognizable as JsDomain where an adapter compares the name
      return new JsDomain(tree['name'] as string, deserializeDomain(tree), tree);
    case 'ArraySymbol':
      return new sj.ArraySymbol(tree['name'] as string, (tree['shape'] as Tree[]).map((d) => deserialize(d) as Expr));
    case 'ArrayElement':
      return new sj.ArrayElement(deserialize(tree['parent'] as Tree) as Expr, (tree['indices'] as Tree[]).map((d) => deserialize(d) as Expr));
    case 'ArrayExpression': {
      const cls = ({ ArrayTensorProduct: sj.ArrayTensorProduct, ArrayAdd: sj.ArrayAdd, ZeroArray: sj.ZeroArray })[tree['cls'] as 'ArrayTensorProduct' | 'ArrayAdd' | 'ZeroArray'];
      return new cls(...(tree['args'] as Tree[]).map((d) => deserialize(d) as Expr));
    }
    case 'ArrayAxes': {
      const cls = tree['cls'] === 'ArrayContraction' ? sj.ArrayContraction : sj.ArrayDiagonal;
      return new cls(deserialize(tree['expr'] as Tree) as Expr, ...(tree['axes'] as number[][]));
    }
    case 'PermuteDims':
      return new sj.PermuteDims(deserialize(tree['expr'] as Tree) as Expr, tree['permutation'] as number[]);
    case 'Reshape':
      return new sj.Reshape(deserialize(tree['expr'] as Tree) as Expr, (tree['shape'] as Tree[]).map((d) => deserialize(d) as Expr));
    case 'AGCAQuotientRing':
      return new sj.QuotientRing(toJs(deserialize(tree['ring'] as Tree), false) as sj.Domain, deserialize(tree['ideal'] as Tree) as sj.ModuleImplementedIdeal);
    case 'AGCAIdeal':
      return (toJs(deserialize(tree['ring'] as Tree), false) as sj.Domain).ideal(...(tree['gens'] as Tree[]).map((g) => deserialize(g) as Expr));
    case 'AGCAFreeModule':
      return (toJs(deserialize(tree['ring'] as Tree), false) as sj.Domain).freeModule(tree['rank'] as number);
    case 'AGCAQuotientModule':
      return new sj.QuotientModule(deserialize(tree['base'] as Tree) as sj.FreeModule, deserialize(tree['killed'] as Tree) as sj.SubModule);
    case 'AGCASubModule':
      return (deserialize(tree['container'] as Tree) as sj.Module).submodule(...(tree['gens'] as Tree[]).map((g) => deserialize(g) as sj.ModuleElement));
    case 'AGCAElement':
      return (deserialize(tree['module'] as Tree) as sj.Module).convert((tree['data'] as Tree[]).map((g) => deserialize(g) as Expr));
    case 'AGCAHomomorphism':
      return sj.homomorphism(deserialize(tree['domain'] as Tree) as sj.Module, deserialize(tree['codomain'] as Tree) as sj.Module, (tree['matrix'] as Tree[]).map((g) => deserialize(g) as sj.ModuleElement));
    case 'MonomialOrder':
      return (sj as Record<string, unknown>)[tree['name'] as string];
    case 'PolyRing':
    case 'FracField': {
      // a polynomial ring or field of fractions: generators, domain (or its name) and order
      const d = deserialize(tree['domain'] as Tree);
      const K = d instanceof JsDomain ? (d.domain ?? d.name) : d;
      const cls = tree.t === 'PolyRing' ? sj.PolyRing : (sj as Record<string, unknown>)['FracField'];
      if (typeof cls !== 'function') throw new Unsupported(`argument type ${tree.t}`);
      return new (cls as new (...a: unknown[]) => unknown)((tree['symbols'] as Tree[]).map((s) => deserialize(s)), K, tree['order'] as string);
    }
    case 'PolyElement': {
      // SymPy 1.14 rs_series can still store fractional exponents in its
      // legacy PolyElement. Preserve them in the explicit Puiseux type.
      const ring = deserialize(tree['ring'] as Tree) as sj.PolyRing;
      const expression = deserialize(tree['expr'] as Tree) as Expr;
      try { return ring.fromExpr(expression); }
      catch (error) {
        if (!(error instanceof RangeError)) throw error;
        return new sj.PuiseuxRing(ring.symbols, ring.domain).fromExpr(expression);
      }
    }
    case 'PuiseuxRing': {
      const d = deserialize(tree['domain'] as Tree);
      return new sj.PuiseuxRing((tree['symbols'] as Tree[]).map((s) => deserialize(s) as Expr), (d instanceof JsDomain ? (d.domain ?? d.name) : d) as sj.Domain | string);
    }
    case 'PuiseuxPoly':
      return (deserialize(tree['ring'] as Tree) as sj.PuiseuxRing).fromDict((tree['terms'] as [Tree[], Tree][]).map(([m, c]) => [m.map((e) => deserialize(e) as Expr), deserialize(c) as Expr]));
    case 'FracElement': {
      const field = deserialize(tree['field'] as Tree) as sj.FracField;
      return field.new(field.ring.fromExpr(deserialize(tree['numer'] as Tree) as Expr), field.ring.fromExpr(deserialize(tree['denom'] as Tree) as Expr));
    }
    case 'DomainMatrix': {
      // DomainMatrix, DDM or SDM of rows of elements (as expressions) over a domain
      const K = definedOr(deserializeDomain(tree['domain'] as Tree), 'domain');
      const shape = tree['shape'] as [number, number];
      const rows = (tree['rows'] as Tree[][]).map((r) => r.map((e) => K.fromSympy(deserialize(e) as Expr)));
      if (tree['cls'] === 'DDM') return new sj.DDM(rows, shape, K);
      if (tree['cls'] === 'SDM') return sj.SDM.fromList(rows, shape, K);
      return new sj.DomainMatrix(rows, shape, K, { fmt: tree['fmt'] as 'dense' | 'sparse' });
    }
    case 'DomainScalar': {
      const K = definedOr(deserializeDomain(tree['domain'] as Tree), 'domain');
      return new sj.DomainScalar(K.fromSympy(deserialize(tree['element'] as Tree) as Expr), K);
    }
    case 'JsPred':
      return new JsPred(tree['attr'] as string);
    case 'RootSum': {
      const fun = deserialize(tree['fun'] as Tree);
      const lam = fun instanceof JsLambda ? sj.Lambda(fun.vars, fun.body) : (fun as sj.Lambda);
      return new sj.RootSumNode([deserialize(tree['poly'] as Tree) as Expr, lam, deserialize(tree['var'] as Tree) as Expr]);
    }
    case 'JsFunc':
      return new JsFunc(tree['name'] as string);
    case 'JsTable':
      return new JsTable((tree['entries'] as [Tree[], Tree][]).map(([args, value]) => [args.map(deserialize), deserialize(value)] as const));
    case 'JsLambda':
      return new JsLambda((tree['params'] as Tree[]).map((t) => deserialize(t) as Expr), deserialize(tree['body'] as Tree) as Expr);
    case 'Tuple':
      return new JsTuple((tree['items'] as Tree[]).map(deserialize), Boolean(tree['list']));
    case 'Poly':
      return sj.Poly.from(
        deserialize(tree['expr'] as Tree) as Expr,
        (tree['gens'] as Tree[]).map((g) => deserialize(g) as Expr),
        { domain: tree['domain'] as string, pure: Boolean(tree['pure']) },
      );
    case 'UFnClass':
      return new UFnClass(tree['name'] as string, tree['nargs'] as number[] | undefined);
    case 'FnClass':
      return new FnClass(tree['name'] as string);
    case 'Interval':
      return sj.interval(deserialize(tree['a'] as Tree) as Expr, deserialize(tree['b'] as Tree) as Expr, tree['lo'] as boolean, tree['ro'] as boolean);
    case 'FiniteSet':
      return sj.finiteSet(...(tree['items'] as Tree[]).map((x) => expressionContainer(deserialize(x))));
    case 'Range':
      return sj.Range.of(deserialize(tree['start'] as Tree) as Expr, deserialize(tree['stop'] as Tree) as Expr, deserialize(tree['step'] as Tree) as Expr);
    case 'Contains':
      return new sj.Contains(deserialize(tree['x'] as Tree) as Expr, deserialize(tree['set'] as Tree) as sj.SetExpr);
    case 'NamedSet': {
      const named = (sj as unknown as Record<string, unknown>)[tree['name'] as string];
      if (!(named instanceof sj.SetExpr)) throw new Unsupported(`set ${String(tree['name'])}`);
      return named;
    }
    case 'ImageSet': {
      const lam = deserialize(tree['lamda'] as Tree);
      const sets = (tree['sets'] as Tree[]).map((x) => deserialize(x) as sj.SetExpr);
      if (!(lam instanceof JsLambda) || lam.vars.length !== 1 || sets.length !== 1) throw new Unsupported('ImageSet over several sets');
      // A serialized ImageSet already has its chosen representatives. The
      // evaluating imageset factory can shift them modulo the integer period.
      return new sj.ImageSet(lam.vars[0]!, lam.body, sets[0]!);
    }
    case 'ConditionSet':
      return new sj.ConditionSet(deserialize(tree['sym'] as Tree) as Expr, asExpr(deserialize(tree['condition'] as Tree)), deserialize(tree['base'] as Tree) as sj.SetExpr);
    case 'FourierSeries': {
      const [f, x, a, b] = (['f', 'x', 'a', 'b'] as const).map((k) => deserialize(tree[k] as Tree) as Expr);
      return sj.fourierSeries(f!, x as Sym, [a!, b!]);
    }
    case 'FormalPowerSeries':
      return sj.fps(deserialize(tree['f'] as Tree) as Expr, deserialize(tree['x'] as Tree) as Sym, deserialize(tree['x0'] as Tree) as Expr, tree['dir'] as '+' | '-');
    case 'EmptySequence':
      return sj.EmptySequence;
    case 'SeqExpr': {
      const gen = deserialize(tree['gen'] as Tree);
      const lim = deserialize(tree['limits'] as Tree) as JsTuple;
      return sj.SeqExpr(gen instanceof JsTuple ? sj.Tuple(...gen.items.map(asExpr)) : asExpr(gen), [asSym(lim.items[0]), asExpr(lim.items[1]), asExpr(lim.items[2])]);
    }
    case 'SeqExprOp':
      return sj.SeqExprOp(...(tree['args'] as Tree[]).map((t) => deserialize(t) as sj.SeqBase));
    case 'SeqFormula':
    case 'SeqPer': {
      // sympy.series.sequences: (items, (x, start, stop))
      const items = (tree['items'] as Tree[]).map((t) => deserialize(t) as Expr);
      const lim = [deserialize(tree['x'] as Tree) as Sym, deserialize(tree['start'] as Tree) as Expr, deserialize(tree['stop'] as Tree) as Expr] as const;
      return tree['t'] === 'SeqPer' ? sj.SeqPer(items, lim) : sj.SeqFormula(items[0]!, lim);
    }
    case 'SeqOp': {
      const seqs = (tree['args'] as Tree[]).map((t) => deserialize(t) as sj.SeqBase);
      return tree['op'] === 'SeqAdd' ? sj.SeqAdd(...seqs) : sj.SeqMul(...seqs);
    }
    case 'RecursiveSeq':
      return sj.RecursiveSeq(
        deserialize(tree['recurrence'] as Tree) as Expr,
        deserialize(tree['yn'] as Tree) as Expr,
        deserialize(tree['n'] as Tree) as Expr,
        (tree['initial'] as Tree[]).map((t) => deserialize(t) as Expr),
        deserialize(tree['start'] as Tree) as Expr,
      );
    case 'New': {
      // a helper object constructed without arguments (MultisetPartitionTraverser)
      const cls = (sj as unknown as Record<string, unknown>)[tree['cls'] as string];
      if (typeof cls !== 'function') throw new Unsupported(`class ${String(tree['cls'])}`);
      return new (cls as new () => unknown)();
    }
    case 'SetOp': {
      const xs = (tree['args'] as Tree[]).map((x) => deserialize(x) as sj.SetExpr);
      if (tree['op'] === 'Union') return sj.union(...xs);
      if (tree['op'] === 'Intersection') return sj.intersection(...xs);
      return sj.complement(xs[0]!, xs[1]!);
    }
    case 'Groebner':
      return new sj.GroebnerBasis(
        (tree['exprs'] as Tree[]).map((e) => deserialize(e) as Expr),
        (tree['gens'] as Tree[]).map((g) => deserialize(g) as Sym),
        'ZZ',
        tree['order'] as sj.MonomialOrder,
      );
    case 'JsSet':
      return new JsSet((tree['items'] as Tree[]).map(deserialize));
    case 'BoolOp': {
      const xs = (tree['args'] as Tree[]).map((x) => deserialize(x) as Expr);
      return tree['op'] === 'And' ? sj.and(...xs) : tree['op'] === 'Not' ? sj.not(xs[0]!) : sj.or(...xs);
    }
    case 'AssumptionsContext': {
      const ctx = new sj.AssumptionsContext();
      ctx.add(...(tree['items'] as Tree[]).map((x) => deserialize(x) as Expr));
      return ctx;
    }
    case 'QKeys':
      return sj.Q;
    case 'Subs':
      return sj.Subs(
        deserialize(tree['expr'] as Tree) as Expr,
        (tree['vars'] as Tree[]).map((x) => deserialize(x) as Expr) as never,
        (tree['point'] as Tree[]).map((x) => deserialize(x) as Expr) as never,
      );
    case 'MatExpr': {
      const cls = tree['cls'] as string;
      const args = (tree['args'] as Tree[]).map((x) => deserialize(x));
      const lib = sj as unknown as Record<string, (...a: unknown[]) => unknown>;
      if (cls === 'MatrixSlice') {
        const sl = (t: Tree[]) => t.map((x) => deserialize(x) as Expr);
        const [r, c] = tree['slices'] as Tree[][];
        return sj.MatrixSlice(args[0] as Expr, sl(r!) as never, sl(c!) as never);
      }
      const f = lib[cls];
      if (typeof f !== 'function') throw new Unsupported(`matrix expression ${cls}`);
      return f(...args.map(lambdaAsNode));
    }
    case 'EllipticCurve': {
      const [a4, a6, a1, a2, a3] = (tree['coeffs'] as Tree[]).map((t) => deserialize(t) as sj.Rational);
      return new sj.EllipticCurve(a4!, a6!, a1, a2, a3, Number(tree['modulus']));
    }
    case 'EllipticCurvePoint': {
      const [x, y, z] = (tree['coords'] as Tree[]).map((t) => deserialize(t) as sj.Rational);
      return new sj.EllipticCurvePoint(x!, y!, z!, deserialize(tree['curve'] as Tree) as sj.EllipticCurve);
    }
    case 'Ordinal':
      return sj.Ordinal(...(tree['terms'] as Tree[]).map((t) => deserialize(t) as sj.OmegaPowerNode));
    case 'OmegaPower':
      return sj.OmegaPower(deserialize(tree['exp'] as Tree) as sj.OrdinalNode, BigInt(String(tree['mult'])));
    case 'PowerSet':
      return sj.PowerSet(deserialize(tree['set'] as Tree) as sj.SetExpr);
    case 'Sieve':
      return new sj.Sieve();
    case 'SingleODEProblem':
      return new sj.SingleODEProblem(deserialize(tree['eq'] as Tree) as Expr, deserialize(tree['func'] as Tree) as sj.UndefFn, deserialize(tree['sym'] as Tree) as Sym);
    case 'SingleODESolver': {
      const problem = deserialize(tree['problem'] as Tree) as sj.SingleODEProblem;
      if (tree['cls'] === 'NthAlgebraic') return new sj.NthAlgebraic(problem);
      throw new Unsupported(`ODE solver ${String(tree['cls'])}`);
    }
    case 'CNFLiteral':
      return new sj.Literal(deserialize(tree['lit'] as Tree) as Expr, tree['isNot'] as boolean);
    case 'CNF':
      return new sj.CNF((tree['clauses'] as Tree[][]).map((c) => c.map((l) => deserialize(l) as InstanceType<typeof sj.Literal>)));
    case 'EncodedCNF':
      return new sj.EncodedCNF(tree['data'] as number[][], (tree['encoding'] as [Tree, number][]).map(([k, v]) => [deserialize(k) as Expr, v] as const));
    case 'ArrayComprehension':
    case 'ArrayComprehensionMap': {
      const limits = (tree['limits'] as Tree[]).map((l) => (deserialize(l) as JsTuple).items as [Expr, Expr, Expr]);
      if (tree.t === 'ArrayComprehension') return sj.ArrayComprehension(deserialize(tree['function'] as Tree) as Expr, ...limits);
      const lam = deserialize(tree['function'] as Tree) as JsLambda;
      return sj.ArrayComprehensionMap(lam.vars.length === 0 ? () => lam.body : (x: number) => lam.call(sj.sympify(x)), ...limits);
    }
    case 'IntegerPartition': return new sj.IntegerPartition(tree['parts'] as number[]);
    case 'Partition': return new sj.Partition(...(tree['blocks'] as Tree[][]).map((b) => b.map((e) => deserialize(e) as Expr)));
    case 'FiniteExtension': return new sj.FiniteExtension(deserialize(tree['modulus'] as Tree) as sj.Poly);
    case 'FiniteDensity': return new sj.FiniteDensity((tree['items'] as [Tree, Tree][]).map(([k, v]) => [deserialize(k) as Expr, deserialize(v) as Expr]));
    case 'StrPrinter': return new sj.StrPrinter(Object.fromEntries((deserialize(tree['settings'] as Tree) as JsDict).entries as [string,unknown][]));
    case 'Permutation':
      return new sj.Permutation(tree['array'] as number[]);
    case 'PermutationGroup':
      return sj.PermutationGroup((tree['generators'] as Tree[]).map((g) => deserialize(g) as sj.Permutation));
    case 'TensorIndexType': return sj.TensorIndexType(String(tree['name']), { dim: deserialize(tree['dim'] as Tree) as Expr, dummyName: String(tree['dummyName']) });
    case 'TensorIndex': return sj.TensorIndex(String(tree['name']), deserialize(tree['type'] as Tree) as sj.TensorIndexType, Boolean(tree['up']));
    case 'TensorSymmetry':
      // a general slot symmetry by its base and strong generating set
      if (tree['base'] !== undefined) return new sj.TensorSymmetry(tree['base'] as number[], (tree['generators'] as Tree[]).map((g) => deserialize(g) as sj.Permutation));
      return new sj.TensorSymmetry(Number(tree['rank']), Number(tree['sign']) as -1 | 0 | 1);
    case 'WildTensorIndex': return sj.WildTensorIndex(String(tree['name']), deserialize(tree['type'] as Tree) as sj.TensorIndexType, Boolean(tree['up']), Boolean(tree['ignoreUpdown']));
    case 'WildTensorHead': return sj.WildTensorHead(String(tree['name']), { indexTypes: (tree['types'] as Tree[]).map((t) => deserialize(t) as sj.TensorIndexType), unorderedIndices: Boolean(tree['unordered']) });
    case 'WildTensor': return (deserialize(tree['head'] as Tree) as sj.WildTensorHead).at(...(tree['indices'] as Tree[]).map((t) => deserialize(t) as sj.TensorIndex));
    case 'TensAdd': return sj.add(...(tree['args'] as Tree[]).map((t) => deserialize(t) as Expr));
    case 'TensorElement': return sj.TensorElement(deserialize(tree['expr'] as Tree) as Expr, new Map((deserialize(tree['indexMap'] as Tree) as JsDict).entries as [Expr, Expr][]));
    case 'SymmetricPermutationGroup': return sj.SymmetricPermutationGroup(Number(tree['deg']));
    case 'DifferentialOperatorAlgebra':
    case 'RecurrenceOperatorAlgebra': {
      // the operator algebra over the univariate polynomial ring of its base domain
      const base = (deserialize(tree['base'] as Tree) as JsDomain).domain as sj.Domain;
      const R = base.oldPolyRing(deserialize(tree['x'] as Tree) as Sym);
      return tree['t'] === 'DifferentialOperatorAlgebra' ? new sj.DifferentialOperatorAlgebra(R, String(tree['gen'])) : new sj.RecurrenceOperatorAlgebra(R, String(tree['gen']));
    }
    case 'DifferentialOperator':
    case 'RecurrenceOperator': {
      const parent = deserialize(tree['parent'] as Tree);
      const coeffs = (tree['coeffs'] as Tree[]).map((t) => deserialize(t) as Expr);
      return parent instanceof sj.DifferentialOperatorAlgebra ? new sj.DifferentialOperator(coeffs, parent) : new sj.RecurrenceOperator(coeffs, parent as sj.RecurrenceOperatorAlgebra);
    }
    case 'HolonomicFunction': {
      const y0 = deserialize(tree['y0'] as Tree);
      // Python lists of initial values arrive as JsTuple/JsList containers
      const values = (v: unknown): Expr[] => (v instanceof JsTuple || v instanceof JsList ? [...v.items] : (v as Expr[])) as Expr[];
      const ics = y0 === null ? undefined : y0 instanceof JsDict ? new Map(y0.entries.map(([k, v]) => [k as Expr, values(v)])) : values(y0);
      return new sj.HolonomicFunction(deserialize(tree['op'] as Tree) as sj.DifferentialOperator, deserialize(tree['x'] as Tree) as Sym, deserialize(tree['x0'] as Tree) as Expr, ics);
    }
    case 'HolonomicSequence':
      return new sj.HolonomicSequence(deserialize(tree['op'] as Tree) as sj.RecurrenceOperator, ((u0) => (u0 instanceof JsTuple || u0 instanceof JsList ? [...u0.items] : u0) as Expr[])(deserialize(tree['u0'] as Tree)));
    case 'ComplexInterval': {
      const q = (ts: Tree[]): sj.Rational[] => ts.map((t) => deserialize(t) as sj.Rational);
      const [ax, ay] = q(tree['a'] as Tree[]);
      const [bx, by] = q(tree['b'] as Tree[]);
      return sj.ComplexInterval.fromRectangle(q(tree['coeffs'] as Tree[]), [ax!, ay!], [bx!, by!], Boolean(tree['conj']));
    }
    case 'FreeGroup': return new sj.FreeGroup((tree['symbols'] as Tree[]).map((t) => deserialize(t) as Expr));
    case 'FreeGroupElement': return (deserialize(tree['group'] as Tree) as sj.FreeGroup).dtype((tree['array'] as [Tree, number][]).map(([s, e]) => [deserialize(s) as Expr, e]));
    case 'FpGroup': return new sj.FpGroup(deserialize(tree['free'] as Tree) as sj.FreeGroup, (tree['relators'] as Tree[]).map((t) => deserialize(t) as sj.FreeGroupElement));
    case 'FpSubgroup': return new sj.FpSubgroup(deserialize(tree['parent'] as Tree) as sj.FpGroup, (tree['generators'] as Tree[]).map((t) => deserialize(t) as sj.FreeGroupElement), Boolean(tree['normal']));
    case 'CosetTable': {
      // the state of a coset table, set through its public fields
      const C = new sj.CosetTable(deserialize(tree['group'] as Tree) as sj.FpGroup, (tree['subgroup'] as Tree[]).map((t) => deserialize(t) as sj.FreeGroupElement), Number(tree['maxCosets']));
      C.table = (tree['table'] as (number | null)[][]).map((r) => [...r]);
      C.p = [...(tree['p'] as number[])];
      C.deductionStack = (tree['deductions'] as [number, Tree][]).map(([a, x]) => [a, C.A.findIndex((l) => l.equals(deserialize(x)))]);
      const sch = tree['schreier'] as { free: Tree; generators: Tree[]; relators: Tree[]; hasRelators: boolean; P: (Tree | null)[][] } | undefined;
      if (sch) {
        C.schreier = { freeGroup: deserialize(sch.free) as sj.FreeGroup, generators: sch.generators.map((t) => deserialize(t) as sj.FreeGroupElement), ...(sch.hasRelators ? { relators: sch.relators.map((t) => deserialize(t) as sj.FreeGroupElement) } : {}) };
        C.P = sch.P.map((row) => row.map((t) => (t === null ? null : (deserialize(t) as sj.FreeGroupElement))));
      }
      return C;
    }
    case 'PowerBasis': {
      const K = tree['field'] === null ? undefined : (deserialize(tree['field'] as Tree) as JsDomain).domain;
      return new sj.PowerBasis(K instanceof sj.AlgebraicField ? K : (deserialize(tree['T'] as Tree) as sj.Poly));
    }
    case 'Submodule': return new sj.Submodule(deserialize(tree['parent'] as Tree) as sj.NumberFieldModule, deserialize(tree['matrix'] as Tree) as sj.DomainMatrix, BigInt(tree['denom'] as string));
    case 'ModuleElement': return sj.makeModElt(deserialize(tree['module'] as Tree) as sj.NumberFieldModule, sj.toCol((tree['col'] as string[]).map(BigInt)), BigInt(tree['denom'] as string));
    case 'PrimeIdeal':
      return new sj.PrimeIdeal(deserialize(tree['ZK'] as Tree) as sj.Submodule, BigInt(tree['p'] as string), deserialize(tree['alpha'] as Tree) as sj.PowerBasisElement, Number(tree['f']), Number(tree['e']));
    case 'Collector': return new sj.Collector((tree['pcgs'] as Tree[]).map((t) => deserialize(t) as sj.Permutation), (tree['series'] as Tree[]).map((t) => deserialize(t) as sj.PermutationGroup), tree['relativeOrder'] as number[]);
    case 'PolycyclicGroup': return new sj.PolycyclicGroup((tree['pcgs'] as Tree[]).map((t) => deserialize(t) as sj.Permutation), (tree['series'] as Tree[]).map((t) => deserialize(t) as sj.PermutationGroup), tree['relativeOrder'] as number[]);
    case 'GroupHomomorphism': return new sj.GroupHomomorphism(deserialize(tree['domain'] as Tree) as sj.HomomorphismGroup, deserialize(tree['codomain'] as Tree) as sj.HomomorphismGroup, (tree['images'] as [Tree, Tree][]).map(([k, v]) => [deserialize(k) as sj.GroupElement, deserialize(v) as sj.GroupElement] as const));
    case 'Polyhedron': {
      const polyhedron = new sj.Polyhedron(
        (tree['corners'] as Tree[]).map((c) => deserialize(c) as Expr),
        tree['faces'] as number[][],
        (tree['pgroup'] as Tree[]).map((g) => deserialize(g) as sj.Permutation),
      );
      if (tree['rotation'] !== undefined) polyhedron.rotate(new sj.Permutation(tree['rotation'] as number[]));
      return polyhedron;
    }
    case 'TensorHead': return sj.TensorHead(String(tree['name']), (tree['types'] as Tree[]).map((t) => deserialize(t) as sj.TensorIndexType), deserialize(tree['symmetry'] as Tree) as sj.TensorSymmetry);
    case 'Tensor': return new sj.Tensor(deserialize(tree['head'] as Tree) as sj.TensorHead, (tree['indices'] as Tree[]).map((t) => deserialize(t) as sj.TensorIndex));
    case 'TensMul': return sj.mul(...(tree['args'] as Tree[]).map((t) => deserialize(t) as Expr));
    case 'Cycle': {
      let c = new sj.Cycle();
      for (const cyc of tree['cycles'] as number[][]) c = c.call(...cyc) as sj.Cycle;
      const size = tree['size'] as number;
      if (size > c.size) c = c.call(size - 1) as sj.Cycle;
      return c;
    }
    case 'NDimArray': {
      const cls = (sj as unknown as Record<string, (flat: unknown, shape: number[]) => unknown>)[tree['cls'] as string];
      if (!cls) throw new Unsupported(`array class ${tree['cls']}`);
      return cls((tree['flat'] as Tree[]).map((x) => deserialize(x)), tree['shape'] as number[]);
    }
    case 'Idx': {
      const label = deserialize(tree['label'] as Tree) as Expr;
      const lo = tree['lower'] as Tree | null;
      const hi = tree['upper'] as Tree | null;
      return lo === null || hi === null ? sj.Idx(label) : sj.Idx(label, [deserialize(lo) as Expr, deserialize(hi) as Expr]);
    }
    case 'PropKB': {
      const kb = new sj.PropKB();
      for (const c of tree['clauses'] as Tree[]) kb.tell(deserialize(c) as Expr);
      return kb;
    }
    case 'Logic': {
      const xs = (tree['args'] as Tree[]).map((x) => deserialize(x) as Expr);
      switch (tree['op']) {
        case 'Not':
          return sj.not(xs[0]!);
        case 'Xor':
          return sj.Xor(...xs);
        case 'Implies':
          return sj.Implies(...xs);
        case 'Equivalent':
          return sj.Equivalent(...xs);
        case 'Nand':
          return sj.Nand(...xs, { evaluate: false });
        case 'Nor':
          return sj.Nor(...xs, { evaluate: false });
        case 'Xnor':
          return sj.Xnor(...xs, { evaluate: false });
        case 'ITE':
          return sj.ITE(xs[0]!, xs[1]!, xs[2]!, { evaluate: false });
        default:
          throw new Unsupported(`logic ${tree['op']}`);
      }
    }
    case 'Pred': {
      const p = sj.Q[tree['name'] as string];
      if (!p) throw new Unsupported(`predicate ${tree['name']}`);
      return p(...(tree['args'] as Tree[]).map((x) => deserialize(x) as Expr));
    }
    case 'Iterator':
      return new JsIterator((tree['items'] as Tree[]).map(deserialize));
    case 'Type':
      return new TypeRef(tree['name'] as string);
    case 'Wild': {
      const a = Object.fromEntries(Object.entries(tree['assume'] as Record<string, boolean>).map(([k, v]) => [camel(k), v]));
      const props = ((tree['props'] as string[] | undefined) ?? []).map((attr) => (e: Expr) => new JsPred(attr).test(e));
      return new sj.Wild(tree['name'] as string, { exclude: (tree['exclude'] as Tree[]).map((x) => deserialize(x) as Expr), ...a, ...(props.length ? { properties: props } : {}) });
    }
    case 'WildFunction':
      return new sj.WildFunction(tree['name'] as string, (tree['nargs'] as number[] | null) ?? undefined);
    case 'Dummy': {
      const a = Object.fromEntries(Object.entries(tree['assume'] as Record<string, boolean>).map(([k, v]) => [camel(k), v]));
      return new sj.Dummy(tree['name'] as string, a, 1_000_000 + (tree['index'] as number));
    }
    case 'UFn':
      return sj.SymFunction(tree['name'] as string)(...(tree['args'] as Tree[]).map((a) => deserialize(a) as Expr));
    case 'Derivative': {
      const expr = deserialize(tree['expr'] as Tree) as Expr | Matrix;
      const variables = (tree['vc'] as [Tree, number][]).map(([v, n]): [Expr | Matrix, number] => [deserialize(v) as Expr | Matrix, n]);
      const shaped = (value: Expr | Matrix) => value instanceof Matrix || value instanceof sj.MatrixExpr || value instanceof sj.NDimArray || value instanceof sj.ArrayExpr;
      // The original corpus serialized ArrayDerivative using its Derivative base tag.
      if (shaped(expr) || variables.some(([v]) => shaped(v))) return sj.ArrayDerivative(expr, ...variables);
      return sj.derivative(expr as Expr, variables as [Expr, number][]);
    }
    case 'Dict':
      return new JsDict((tree['items'] as [Tree, Tree][]).map(([k, v]) => [deserialize(k), deserialize(v)] as const));
    case 'MatrixSymbol':
      return new sj.MatrixSymbol(tree['name'] as string, deserialize(tree['rows'] as Tree) as Expr, deserialize(tree['cols'] as Tree) as Expr);
    case 'Matrix':
      if (tree['sparse'] === true) return new sj.SparseMatrix(...(tree['shape'] as [number, number]), (tree['rows'] as Tree[][]).map((r) => r.map((e) => asExpr(deserialize(e)))));
      // empty matrices keep their shape (e.g. 0x2)
      if (!(tree['rows'] as Tree[][]).length && tree['shape']) return Matrix.zeros(...(tree['shape'] as [number, number]));
      return Matrix.of((tree['rows'] as Tree[][]).map((r) => r.map((x) => {
        const v = deserialize(x);
        return v instanceof Matrix ? sj.sympifyMatrix(v) : asExpr(v);
      })));
    default:
      throw new Unsupported(`type ${tree.t}`);
  }
}

// ---------------------------------------------------------------------------
// Adapters: SymPy API name -> symjs
// ---------------------------------------------------------------------------

/** A sympy.vector object rebuilt by its class constructor from its arguments. */
function deserializeVector(tree: Tree): unknown {
  const cls = tree['cls'] as string;
  if (cls === 'CoordSys3D') {
    const tr = tree['transformation'] as Tree;
    const parent = tree['parent'] === null ? undefined : (deserialize(tree['parent'] as Tree) as sj.CoordSys3D);
    const names = { vectorNames: tree['vectorNames'] as string[], variableNames: tree['variableNames'] as string[], parent };
    if (tr.t === 'Str') return sj.CoordSys3D(tree['name'] as string, { ...names, transformation: tr['v'] as string });
    const t = deserialize(tr);
    if (t instanceof JsTuple && t.items[0] instanceof Matrix) {
      return sj.CoordSys3D(tree['name'] as string, { ...names, rotationMatrix: t.items[0], location: parent ? (t.items[1] as Expr) : undefined });
    }
    const transformation = lambdaAsNode(t);
    if (!(transformation instanceof sj.Lambda)) throw new Unsupported('coordinate transformation');
    return sj.CoordSys3D(tree['name'] as string, { ...names, transformation });
  }
  const args = (tree['args'] as Tree[]).map((a) => deserialize(a));
  const items = (v: unknown): unknown[] => (v instanceof JsTuple ? [...v.items] : [v]);
  const e = (i: number): Expr => args[i] as Expr;
  switch (cls) {
    case 'BaseVector':
      return (args[1] as sj.CoordSys3D).baseVectors()[Number((args[0] as sj.Rational).p)];
    case 'BaseScalar':
      return (args[1] as sj.CoordSys3D).baseScalars()[Number((args[0] as sj.Rational).p)];
    case 'VectorZero':
      return sj.Vector.zero;
    case 'DyadicZero':
      return sj.Dyadic.zero;
    case 'Point':
      return sj.VectorPoint(args[0] as string, e(1), args[2] as sj.VectorPoint | undefined);
    case 'BodyOrienter':
    case 'SpaceOrienter':
      return (sj[cls] as (a: Expr, b: Expr, c: Expr, o: string) => Expr)(e(0), e(1), e(2), args[3] as string);
    case 'ImplicitRegion':
      return sj.ImplicitRegion(items(args[0]) as Expr[], e(1));
    case 'ParametricRegion':
      return sj.ParametricRegion(items(args[0]) as Expr[], ...args.slice(1).map((b) => (b instanceof JsTuple ? (b.items as [Expr, Expr, Expr]) : (b as Expr))));
    case 'Cross':
    case 'Dot':
    case 'ParametricIntegral':
      // the stored (canonical) form, unevaluated
      return new (sj[cls] as unknown as new (a: Expr, b: Expr) => Expr)(e(0), e(1));
    default:
      return (sj as unknown as Record<string, (...a: unknown[]) => unknown>)[cls]!(...args);
  }
}

/** A sympy.stats object rebuilt by its class constructor from its arguments. */
function deserializeStats(tree: Tree): unknown {
  const cls = tree['cls'] as string;
  const toArg = (v: unknown): Expr => {
    if (typeof v === 'boolean') return v ? S.true : S.false;
    if (v instanceof JsDict) return sj.Dict(v.entries.map(([k, x]) => [toArg(k), toArg(x)] as const));
    if (v instanceof JsSet) return sj.FiniteSet.of(...v.items.map(toArg)) as Expr;
    if (v instanceof JsLambda) return sj.Lambda(v.vars, v.body);
    // a sympy Tuple (the state space of a Markov chain) and an explicit matrix argument
    if (v instanceof JsTuple) return new sj.TupleNode(v.items.map(toArg));
    if (v instanceof Matrix) return sj.ImmutableMatrix(v);
    return v as Expr;
  };
  const args = (tree['args'] as Tree[]).map((a) => toArg(deserialize(a)));
  const lib = sj as unknown as Record<string, new (...a: unknown[]) => unknown>;
  if (cls === 'RandomSymbol') return new sj.RandomSymbol(args[0] as Sym, args[1] as sj.PSpace);
  if (cls === 'JointRandomSymbol') return new sj.JointRandomSymbol(args[0] as Sym, args[1] as sj.PSpace);
  if (cls === 'RandomIndexedSymbol') return new sj.RandomIndexedSymbol(args[0] as Expr, args[1] as sj.PSpace);
  if (cls === 'RandomMatrixSymbol') return new sj.RandomMatrixSymbol(args[0] as Sym, args[1] as Expr, args[2] as Expr, args[3] as sj.PSpace);
  // SymPy's Distribution() of a stochastic process without a distribution
  if (cls === 'Distribution') return new sj.UnspecifiedDistribution();
  // the symbolic probability nodes are classes ExpectationNode, ...; the spaces, domains and distributions take their arguments
  const C = lib[`${cls}Node`] ?? lib[cls];
  if (!C) throw new Unsupported(`stats class ${cls}`);
  return new C(args);
}

export type Adapter = (args: unknown[], kwargs: Record<string, unknown>, self?: unknown) => unknown;

const asExpr = (v: unknown): Expr => {
  if (v instanceof Expr) return v;
  if (typeof v === 'number') return sj.sympify(v);
  if (typeof v === 'boolean') return v ? S.true : S.false;
  throw new Unsupported(`expected an expression, got ${fmt(v)}`);
};
/** Tuples and dictionaries embedded in expressions need symbolic containers. */
function expressionContainer(v: unknown): Expr {
  if (v instanceof JsTuple) return sj.Tuple(...v.items.map(expressionContainer));
  if (v instanceof JsDict) return sj.Dict(v.entries.map(([k, x]) => [expressionContainer(k), expressionContainer(x)]));
  return asExpr(v);
}
const asExprList = (value: unknown): Expr[] => {
  if (value instanceof JsList || value instanceof JsTuple || value instanceof JsSet) return value.items.map(asExpr);
  throw new Unsupported('expression sequence');
};

const asExprOrPoly = (v: unknown): Expr => (v instanceof sj.Poly ? v.asExpr() : asExpr(v));
/** Translate Python coefficient-domain options; all arithmetic stays in the public API. */
const polynomialOptions = (kw: Record<string, unknown>): sj.PolynomialDomainOptions => ({
  ...(kw['extension'] === undefined ? {} : { extension: typeof kw['extension'] === 'boolean' ? kw['extension'] : kw['extension'] instanceof JsTuple ? kw['extension'].items.map(asExpr) : asExpr(kw['extension']) }),
  ...(kw['domain'] === undefined ? {} : { domain: kw['domain'] instanceof JsDomain ? kw['domain'].name : String(kw['domain']) }),
  ...(kw['modulus'] === undefined ? {} : { modulus: (kw['modulus'] as sj.Rational).p }),
});
const asPoly = (v: unknown): sj.Poly => {
  if (v instanceof sj.Poly) return v;
  throw new Unsupported('expected a Poly');
};
const polyOf = (args: unknown[]): sj.Poly =>
  args[0] instanceof sj.Poly ? args[0] : sj.Poly.from(asExpr(args[0]), args.slice(1).map(asExpr));
/** SymPy parallel_poly_from_expr: n leading arguments as Polys over common gens (rest are gens). */
const parallelPolys = (args: unknown[], n: number): { ps: sj.Poly[]; asPolys: boolean } => {
  const fs = args.slice(0, n);
  const asPolys = fs.some((f) => f instanceof sj.Poly);
  let gens = args.slice(n).flatMap((g) => g instanceof JsTuple ? g.items.map(asExpr) : [asExpr(g)]);
  if (!gens.length) {
    const g = new Map<string, Expr>();
    for (const f of fs) for (const x of f instanceof sj.Poly ? f.gens : sj.Poly.from(asExpr(f)).gens) g.set(x.key, x);
    gens = sj.sortGens([...g.values()]);
  }
  return { ps: fs.map((f) => sj.Poly.from(asExprOrPoly(f), gens)), asPolys };
};
const polyFn =
  (n: number, f: (ps: sj.Poly[], rest: unknown[]) => unknown, nExtra = 0): Adapter =>
  (args, kw) => {
    for (const k of Object.keys(kw)) if (k !== 'polys') throw new Unsupported(`kwargs ${k}`);
    const extra = args.slice(n, n + nExtra);
    const { ps, asPolys } = parallelPolys([...args.slice(0, n), ...args.slice(n + nExtra)], n);
    const outputPolys = kw['polys'] === undefined ? asPolys : Boolean(kw['polys']);
    const out = (v: unknown): unknown =>
      v instanceof sj.Poly ? (outputPolys ? v : v.asExpr()) : v instanceof JsTuple ? new JsTuple(v.items.map(out), v.isList) : v instanceof JsList ? new JsList(v.items.map(out)) : Array.isArray(v) ? new JsList(v.map(out)) : v;
    return out(f(ps, extra));
  };
/** SymPy solve_poly_system / solve_triangulated (Gröbner basis, solutions sorted by default_sort_key). */
function polySystemSolutions(args: unknown[], kw: Record<string, unknown>, rationalOnly = false): unknown {
  noKw(kw);
  const eqs = (args[0] as JsList | JsTuple).items.map(asExpr);
  const syms = args.slice(1).map(asSym);
  return new JsList(sj.solvePolySystem(eqs, syms, { rationalOnly }).map((t) => new JsTuple(t)));
}
/** ff/rf of a Poly: product of the polynomial shifted by -i (ff) or +i (rf). */
function polyFactorial(args: unknown[], kw: Record<string, unknown>, dir: 1 | -1): unknown {
  noKw(kw);
  const [p, k] = args;
  if (!(p instanceof sj.Poly)) return sj.fn(dir === 1 ? 'rf' : 'ff', args.map(asExpr));
  const g = p.gens[0]!;
  let acc: Expr = S.One;
  for (let i = 0; i < Number((k as sj.Rational).p); i++) acc = sj.mul(acc, sj.xreplace(p.asExpr(), [[g, sj.add(g, dir * i)]]));
  return sj.Poly.from(sj.expand(acc), p.gens);
}
/** Univariate division over ZZ (SymPy dup_rr_div): stops when the leading coefficient does not divide. */
function divOverZZ(f: Expr, g: Expr): [Expr, Expr] {
  const gens = sj.sortGens([...sj.freeSymbols(sj.add(f, g))]) as Sym[];
  if (gens.length !== 1) throw new Unsupported('div over ZZ');
  const x = gens[0]!;
  let r = sj.Poly.from(f, [x]);
  const G = sj.Poly.from(g, [x]);
  const lg = G.LC() as sj.Rational;
  let q: Expr = S.Zero;
  while (!r.isZero && r.degree() >= G.degree()) {
    const lr = r.LC() as sj.Rational;
    if (!lr.isInteger || !lg.isInteger || lr.p % lg.p !== 0n) break;
    const t = sj.mul(sj.Rational.of(lr.p / lg.p), sj.pow(x, r.degree() - G.degree()));
    q = sj.add(q, t);
    r = sj.Poly.from(sj.expand(sj.add(r.asExpr(), sj.mul(-1, t, G.asExpr()))), [x]);
  }
  return [q, r.asExpr()];
}
/** eps as an exact rational (SymPy QQ.convert of a float such as 1e-2). */
function epsArg(v: unknown): sj.Rational | undefined {
  if (v === undefined) return undefined;
  if (v instanceof sj.Rational) return v;
  const e = asExpr(v);
  return sj.nsimplify(e) as sj.Rational;
}
function intervalsAdapter(p: sj.Poly, kw: Record<string, unknown>): unknown {
  for (const k of Object.keys(kw)) if (k !== 'eps') throw new Unsupported(`kwargs ${k}`);
  return new JsList(p.intervals(epsArg(kw['eps'])).map(([[s, t], k]) => new JsTuple([new JsTuple([s, t]), sj.Rational.of(k)])));
}
function refineAdapter(p: sj.Poly, args: unknown[], kw: Record<string, unknown>): unknown {
  for (const k of Object.keys(kw)) if (k !== 'eps' && k !== 'steps') throw new Unsupported(`kwargs ${k}`);
  const [s, t] = p.refineRoot(asExpr(args[0]) as sj.Rational, asExpr(args[1]) as sj.Rational, epsArg(kw['eps']), kw['steps'] === undefined ? undefined : intArg(kw['steps']));
  return new JsTuple([s, t]);
}
const asSym = (v: unknown): Sym => {
  if (v instanceof Sym) return v;
  throw new Unsupported('expected a symbol');
};
const noKw = (kw: Record<string, unknown>) => {
  const keys = Object.keys(kw);
  if (keys.length) throw new Unsupported(`kwargs ${keys.join(',')}`);
};
const exprFn =
  (f: (e: Expr) => unknown): Adapter =>
  (args, kw) => {
    noKw(kw);
    if (args.length !== 1) throw new Unsupported('arity');
    return f(asExpr(args[0]));
  };
const exprMethod =
  (f: (e: Expr) => unknown): Adapter =>
  (args, kw, self) => {
    noKw(kw);
    if (args.length !== 0) throw new Unsupported('arity');
    return f(asExpr(self));
  };
const matrixMethod =
  (f: (m: Matrix, args: unknown[]) => unknown): Adapter =>
  (args, kw, self) => {
    noKw(kw);
    if (!(self instanceof Matrix)) throw new Unsupported('expected a Matrix');
    return f(self, args);
  };

/** Python str() of a list of roots with multiplicity -> SymPy dict {root: multiplicity}. */
function rootsDict(rs: Expr[]): JsDict {
  const m = new Map<string, [Expr, number]>();
  for (const r of rs) {
    const e = m.get(r.key);
    if (e) e[1]++;
    else m.set(r.key, [r, 1]);
  }
  return new JsDict([...m.values()].map(([r, k]) => [r, k] as const));
}

function diffArgs(e: Expr, rest: unknown[]): Expr {
  if (!rest.length) {
    const fs = [...sj.freeSymbols(e)].filter((s) => s instanceof Sym);
    if (fs.length !== 1) throw new Unsupported('diff variable');
    return sj.diff(e, fs[0]!);
  }
  let out = e;
  for (let i = 0; i < rest.length; i++) {
    const v = asExpr(rest[i]);
    const n = rest[i + 1];
    if (n instanceof sj.Rational && n.isInteger) {
      out = sj.diff(out, v, Number(n.p));
      i++;
    } else out = sj.diff(out, v);
  }
  return out;
}

function subsArgs(e: Expr, args: unknown[]): Expr {
  if (args.length === 2) return e.subs(asExpr(args[0]), asExpr(args[1]));
  const a = args[0];
  if (a instanceof JsDict) return sj.subs(e, new Map(a.entries.map(([k, v]) => [asExpr(k), asExpr(v)] as const)));
  if (a instanceof JsTuple || a instanceof JsIterator) {
    // sequential substitution like SymPy (an iterator of pairs too)
    let out = e;
    for (const p of a.items) {
      if (!(p instanceof JsTuple)) throw new Unsupported('subs pair');
      out = out.subs(asExpr(p.items[0]), asExpr(p.items[1]));
    }
    return out;
  }
  throw new Unsupported('subs arguments');
}

const HINTS = ['deep', 'mul', 'multinomial', 'power_exp', 'power_base', 'log', 'complex', 'trig', 'force', 'func', 'frac', 'numer', 'denom', 'diracdelta', 'wrt'];
function expandHints(kw: Record<string, unknown>): sj.ExpandHints {
  for (const k of Object.keys(kw)) if (!HINTS.includes(k)) throw new Unsupported(`expand hint ${k}`);
  // wrt (the variable of the diracdelta hint) is an expression
  return Object.fromEntries(Object.entries(kw).map(([k, v]) => [k, k === 'wrt' ? v : Boolean(v)])) as sj.ExpandHints;
}

function asOrdered(e: Expr): Expr[] {
  return sj.orderedTerms(e);
}

function allSymbols(eqs: Expr[]): Sym[] {
  const m = new Map<string, Sym>();
  for (const e of eqs) for (const s of [...sj.freeSymbols(e)].filter((s) => s instanceof Sym)) m.set(s.key, s);
  return [...m.values()].sort((a, b) => (a.name < b.name ? -1 : a.name > b.name ? 1 : 0));
}

function solveAug(aug: Matrix, syms: Sym[]): Expr[] | undefined {
  const result = sj.linsolveAugmented(aug, syms);
  return Array.isArray(result) ? result : undefined;
}

function idxList(v: unknown): (number | boolean)[] {
  if (!(v instanceof JsTuple)) throw new Unsupported('index list');
  return v.items.map((x) => (typeof x === 'boolean' ? x : Number((x as sj.Rational).p)));
}

function intArg(v: unknown): number {
  if (v instanceof sj.Rational && v.isInteger) return Number(v.p);
  if (typeof v === 'number' && Number.isInteger(v)) return v;
  throw new Unsupported('integer argument');
}

const asSet = (v: unknown): sj.SetExpr => {
  if (v instanceof sj.SetExpr) return v;
  throw new Unsupported('expected a set');
};
const typeMethod = (self: unknown, type: string, f: () => unknown, kw: Record<string, unknown>): unknown => {
  noKw(kw);
  if (!(self instanceof TypeRef && self.name === type)) throw new Unsupported(`classmethod of ${type}`);
  return f();
};
const monoAdapter =
  (f: (e: Expr, iv?: sj.SetExpr, x?: Sym) => sj.Truth): Adapter =>
  (args, kw) => {
    noKw(kw);
    return none(f(asExpr(args[0]), (args[1] as sj.SetExpr | undefined) ?? sj.Reals, args[2] === undefined ? undefined : asSym(args[2])));
  };
const autoKw = (kw: Record<string, unknown>): boolean => {
  for (const k of Object.keys(kw)) if (k !== 'auto') throw new Unsupported(`kwargs ${k}`);
  return kw['auto'] === undefined ? true : Boolean(kw['auto']);
};
const polyArg = (v: unknown): sj.Poly | Expr => (v instanceof sj.Poly ? v : asExpr(v));
const polyM =
  (f: (p: sj.Poly, args: unknown[]) => unknown): Adapter =>
  (args, kw, self) => {
    noKw(kw);
    return f(asPoly(self), args);
  };

function evalfAdapter(self: unknown, args: unknown[], kw: Record<string, unknown>): unknown {
  for (const k of Object.keys(kw)) if (!['subs', 'n', 'chop'].includes(k)) throw new Unsupported(`evalf kwarg ${k}`);
  const n = args.length ? intArg(args[0]) : kw['n'] !== undefined ? intArg(kw['n']) : 15;
  if (args.length > 1) throw new Unsupported('evalf args');
  const opts: sj.EvalfOptions = {};
  const subs = kw['subs'];
  if (subs !== undefined) {
    if (!(subs instanceof JsDict)) throw new Unsupported('evalf subs');
    opts.subs = new Map(subs.entries.map(([k, v]) => [asExpr(k), asExpr(v)] as const));
  }
  const chop = kw['chop'];
  if (chop !== undefined) opts.chop = typeof chop === "boolean" ? chop : asExpr(chop).toNumber();
  if (self instanceof Matrix) return self.evalf(n, opts);
  if (self instanceof sj.AlgebraicNumber) return self.asExpr().evalf(n, opts);
  return asExpr(self).evalf(n, opts);
}

function toQuery(v: unknown): sj.Query {
  if (v instanceof FnClass && ['Function', 'AppliedUndef'].includes(v.name)) return { type: v.name };
  if (v instanceof FnClass || v instanceof UFnClass) return { fn: v.name };
  if (v instanceof TypeRef) return { type: v.name };
  if (v instanceof Expr) return v;
  if (v instanceof JsPred) return (e: Expr) => v.test(e);
  throw new Unsupported('query');
}

function applyFn(name: string, args: Expr[]): Expr {
  const f = FUNCTIONS[name];
  if (f) return f(args);
  return sj.SymFunction(name)(...args);
}

function matchDict(m: ReadonlyMap<Expr, Expr> | sj.NoMatchResult | undefined): unknown {
  return m instanceof Map ? new JsDict([...m]) : null;
}

/** The first element of a solution pair, or None. */
const first0 = (r: [Expr, Sym[]] | sj.UnsolvedResult): unknown => (Array.isArray(r) ? r[0] : null);
/** The equations are linear in the symbols. */
const isLinearSystem = (eqs: Expr[], vars: Sym[]): boolean => {
  try {
    sj.linearEqToMatrix(eqs, vars);
    return true;
  } catch {
    return false;
  }
};

/** SymPy None for the public API's 'unknown', NoMatch and Unsolved. */
const none = (v: unknown): unknown => (v === undefined || v === null || v === 'unknown' || sj.isNoMatch(v) || sj.isUnsolved(v) ? null : v);

const FN_NAMES = ['sin', 'cos', 'tan', 'asin', 'acos', 'atan', 'sinh', 'cosh', 'tanh', 'log', 're', 'im', 'arg', 'conjugate', 'cot', 'sec', 'csc', 'acot', 'asec', 'acsc', 'coth', 'sech', 'csch', 'asinh', 'acosh', 'atanh', 'acoth', 'asech', 'acsch', 'sinc'] as const;

/** Python's Diophantine helpers return sets of solution tuples. */
function diophantineSet(result: unknown): unknown {
  return Array.isArray(result) ? new JsSet(result.map((t) => new JsTuple(t))) : none(result);
}

/** SymPy polynomial Options objects serialize as dictionaries. */
function polynomialGenerators(options: unknown): Sym[] {
  if (!(options instanceof JsDict)) throw new Unsupported('polynomial options');
  const gens = options.entries.find(([key]) => key === 'gens')?.[1];
  if (!(gens instanceof JsTuple)) throw new Unsupported('polynomial generators');
  return gens.items.map(asSym);
}

export const ADAPTERS: Record<string, Adapter> = {
  // SymPy returns (None, None) when the expression does not match
  match_real_imag: (args, kw) => {
    noKw(kw);
    const m = sj.matchRealImag(asExpr(args[0]));
    return new JsTuple(sj.isNoMatch(m) ? [null, null] : m);
  },
  invert_complex: (args, kw) => (noKw(kw), new JsTuple(sj.invertComplex(asExpr(args[0]), asExpr(args[1]), asSym(args[2])))),
  invert_real: (args, kw) => (noKw(kw), new JsTuple(sj.invertReal(asExpr(args[0]), asExpr(args[1]), asSym(args[2])))),
  solve_generic: (args, kw) => (noKw(kw), new JsList(sj.solveGeneric((args[0] as JsTuple).items as sj.Poly[], polynomialGenerators(args[1])).map((row) => new JsTuple(row)))),
  solve_biquadratic: (args, kw) => (noKw(kw), new JsList(sj.solveBiquadratic(args[0] as sj.Poly, args[1] as sj.Poly, polynomialGenerators(args[2])).map((row) => new JsTuple(row)))),
  finite_diff_weights: (args, kw) => (noKw(kw), fromJs(sj.finiteDiffWeights(intArg(args[0]), (args[1] as JsTuple).items.map(asExpr), args[2] === undefined ? 1 : asExpr(args[2])))),
  constantsimp: (args, kw) => (noKw(kw), sj.constantsimp(asExpr(args[0]), [...(args[1] as JsSet).items].map(asSym))),
  integer_powers: (args, kw) => (noKw(kw), new JsList(sj.integerPowers((args[0] as JsTuple).items.map(asExpr)).map(([base, powers]) => new JsTuple([base, new JsList(powers.map((p) => new JsTuple(p)))])))),
  cornacchia: (args, kw) => (noKw(kw), new JsSet(sj.cornacchia(asExpr(args[0]), asExpr(args[1]), asExpr(args[2])).map((t) => new JsTuple(t)))),
  diop_univariate: (args, kw) => (noKw(kw), diophantineSet(sj.diopUnivariate(asExpr(args[0])))),
  diop_quadratic: (args, kw) => (noKw(kw), diophantineSet(sj.diopQuadratic(asExpr(args[0]), args[1] === undefined ? undefined : asSym(args[1])))),
  diop_general_sum_of_squares: (args, kw) => (noKw(kw), diophantineSet(sj.diopGeneralSumOfSquares(asExpr(args[0]), args[1] === undefined ? undefined : intArg(args[1])))),
  diop_general_sum_of_even_powers: (args, kw) => (noKw(kw), diophantineSet(sj.diopGeneralSumOfEvenPowers(asExpr(args[0]), args[1] === undefined ? undefined : intArg(args[1])))),
  diop_solve: (args, kw) => {
    noKw(kw);
    const r = sj.diopSolve(asExpr(args[0]), args[1] === undefined ? undefined : asSym(args[1]));
    return Array.isArray(r) && !Array.isArray(r[0]) ? new JsTuple(r) : diophantineSet(r);
  },
  prime_as_sum_of_two_squares: (args, kw) => {
    noKw(kw);
    const r = sj.primeAsSumOfTwoSquares(asExpr(args[0]));
    return Array.isArray(r) ? new JsTuple(r) : null;
  },
  sdm_irref: (args, kw) => {
    noKw(kw);
    const input = args[0];
    if (!(input instanceof JsDict)) throw new Unsupported('sdm_irref rows');
    // SymPy infers the field from its ground elements; symjs takes it explicitly.
    const rows = new Map(input.entries.map(([i, row]) => {
      if (!(row instanceof JsDict)) throw new Unsupported('sdm_irref row');
      return [intArg(i), new Map(row.entries.map(([j, value]) => {
        const coefficient = value instanceof sj.PythonMPQ ? sj.Rational.of(value.numerator, value.denominator) : value;
        if (!(coefficient instanceof sj.Rational)) throw new Unsupported('sdm_irref coefficient field');
        return [intArg(j), coefficient] as const;
      }))] as const;
    }));
    return fromJs(sj.sdmIrref(rows, sj.QQ));
  },
  N: (args, kw) => evalfAdapter(args[0], args.slice(1), kw),
  // SymPy Ynm_c (camelCase YnmC)
  Ynm_c: (args) => sj.YnmC(args[0] as Expr, args[1] as Expr, args[2] as Expr, args[3] as Expr),
  Float: (args, kw) => {
    for (const k of Object.keys(kw)) if (!['dps', 'precision'].includes(k)) throw new Unsupported(`Float kwarg ${k}`);
    let num = args[0];
    if (num instanceof JsTuple) {
      // an mpf tuple (sign, mantissa, exponent[, bitcount]) at the given decimal precision
      const [sg, man, ex] = num.items.map((x) => (x as sj.Rational).p);
      const d = args[1] ?? kw['dps'];
      const prec = d === undefined ? 53 : sj.dpsToPrec(intArg(d));
      return new sj.Float({ man: sg ? -man! : man!, exp: ex! }, prec);
    }
    const d = args[1] ?? kw['dps'];
    const dps = d === undefined ? undefined : typeof d === 'string' ? (d as '') : intArg(d);
    const precision = kw['precision'] !== undefined ? intArg(kw['precision']) : undefined;
    if (typeof num === 'string' || num instanceof Expr) return sj.float(num, dps, precision);
    throw new Unsupported('Float argument');
  },
  // ---- core constructors
  Function: (args, kw) => {
    noKw(kw);
    return new UFnClass(String(args[0]));
  },
  Subs: (args, kw) => {
    noKw(kw);
    const many = (a: unknown) => (a instanceof JsTuple ? a.items.map(asExpr) : asExpr(a));
    return sj.Subs(asExpr(args[0]), many(args[1]), many(args[2]));
  },
  Derivative: (args, kw) => {
    for (const k of Object.keys(kw)) if (k !== 'evaluate') throw new Unsupported(`kwargs ${k}`);
    if (kw['evaluate'] === true) {
      let e = asExpr(args[0]);
      for (const a of args.slice(1)) {
        if (a instanceof JsTuple) e = sj.diff(e, asExpr(a.items[0]), Number((a.items[1] as sj.Rational).p));
        else e = sj.diff(e, asExpr(a));
      }
      return e;
    }
    const e = asExpr(args[0]);
    const vc: [Expr, number][] = [];
    for (const a of args.slice(1)) {
      if (a instanceof JsTuple) vc.push([asExpr(a.items[0]), Number((a.items[1] as sj.Rational).p)]);
      else vc.push([asExpr(a), 1]);
    }
    return sj.derivative(e, vc);
  },
  symbols: (args, kw) => {
    const a: Record<string, boolean> = {};
    let seq = false;
    for (const [k, v] of Object.entries(kw)) {
      if (k === 'seq') {
        seq = Boolean(v);
        continue;
      }
      if (k === 'cls' && v instanceof FnClass && v.name === 'Function') continue;
      if (k === 'commutative' && v === false) {
        a[k] = false;
        continue;
      }
      if (!['real', 'positive', 'nonnegative', 'integer', 'negative', 'nonpositive'].includes(k) || v !== true) throw new Unsupported(`symbols ${k}`);
      a[k] = true;
    }
    const asFunctions = kw['cls'] instanceof FnClass;
    const one = (spec: string): unknown => {
      const names = sj.expandSymbolNames(spec);
      const syms: unknown[] = names.map((n) => (asFunctions ? new UFnClass(n) : new Sym(n, a)));
      const isSeq = seq || spec.includes(',') || spec.trim().includes(' ') || spec.includes(':');
      return syms.length === 1 && !isSeq ? syms[0] : new JsTuple(syms);
    };
    const first = args[0];
    if (first instanceof JsSet) return new JsSet(first.items.map((s) => one(String(s))));
    if (first instanceof JsList || (first instanceof JsTuple && first.isList)) return new JsList((first as JsTuple).items.map((s) => one(String(s))));
    if (first instanceof JsTuple) return new JsTuple(first.items.map((s) => one(String(s))));
    return one(String(first));
  },
  Rel: (args, kw) => {
    noKw(kw);
    const op = args[2] === undefined || args[2] === null ? '==' : String(args[2]);
    const map: Record<string, sj.RelOp> = {
      '==': 'Eq', eq: 'Eq', '!=': 'Ne', ne: 'Ne', '<>': 'Ne', '<': 'Lt', lt: 'Lt', '<=': 'Le', le: 'Le', '>': 'Gt', gt: 'Gt', '>=': 'Ge', ge: 'Ge',
    };
    const o = map[op];
    if (!o) throw new Unsupported(`Rel op ${op}`);
    return sj.rel(o, asExpr(args[0]), asExpr(args[1]));
  },
  integer_log: (args, kw) => {
    noKw(kw);
    const [e, t] = sj.integerLog((asExpr(args[0]) as sj.Rational).p, (asExpr(args[1]) as sj.Rational).p);
    return new JsTuple([sj.Rational.of(e), t]);
  },
  Symbol: (args, kw) => {
    const a: Record<string, boolean> = {};
    for (const [k, v] of Object.entries(kw)) {
      if (!['real', 'positive', 'nonnegative', 'integer', 'negative', 'nonpositive', 'commutative'].includes(k) || v !== true) throw new Unsupported(`Symbol ${k}`);
      a[k] = true;
    }
    return new Sym(String(args[0]), a);
  },
  Dummy: (args, kw) => {
    const a: Record<string, boolean> = {};
    for (const [k, v] of Object.entries(kw)) {
      if (!['real', 'positive', 'nonnegative', 'integer', 'negative', 'nonpositive', 'commutative'].includes(k) || v !== true) throw new Unsupported(`Dummy ${k}`);
      a[k] = true;
    }
    return new sj.Dummy(args.length ? String(args[0]) : 'Dummy', a);
  },
  Wild: (args, kw) => {
    for (const k of Object.keys(kw)) if (k !== 'exclude') throw new Unsupported(`kwargs ${k}`);
    const ex = kw['exclude'] instanceof JsList || kw['exclude'] instanceof JsTuple ? (kw['exclude'] as JsList).items.map(asExpr) : [];
    return new sj.Wild(String(args[0]), { exclude: ex });
  },
  WildFunction: (args, kw) => (noKw(kw), new sj.WildFunction(String(args[0]))),
  Equality: (args, kw) => (noKw(kw), sj.Eq(asExpr(args[0]), asExpr(args[1]))),
  Unequality: (args, kw) => (noKw(kw), sj.Ne(asExpr(args[0]), asExpr(args[1]))),
  Lambda: (args, kw) => {
    noKw(kw);
    const vs = args[0] instanceof JsTuple ? args[0].items.map(asExpr) : [asExpr(args[0])];
    return sj.Lambda(vs, asExpr(args[1]));
  },
  ...Object.fromEntries(
    (['pi', 'E', 'I', 'oo', 'nan', 'zoo', 'Catalan', 'EulerGamma', 'GoldenRatio', 'TribonacciConstant'] as const).map((n) => [n, () => sj.parse(n)] as [string, Adapter]),
  ),
  // the values are Python tuples (implied, rejected) of predicate sets
  generate_known_facts_dict: (args, kw) => (
    noKw(kw),
    new JsDict(
      [...sj.generateKnownFactsDict((args[0] as JsList).items.map(asExpr), asExpr(args[1]))].map(
        ([k, [i, r]]) => [k, new JsTuple([new JsSet([...i]), new JsSet([...r])])] as const,
      ),
    )
  ),
  hypersimp: (args, kw) => (noKw(kw), none(sj.hypersimp(asExpr(args[0]), asExpr(args[1])))),
  hypersimilar: (args, kw) => (noKw(kw), sj.hypersimilar(asExpr(args[0]), asExpr(args[1]), asExpr(args[2]))),
  rcollect: (args, kw) => (noKw(kw), sj.rcollect(asExpr(args[0]), ...args.slice(1).map(asExpr))),
  Piecewise: (args, kw) => (noKw(kw), sj.Piecewise(...args.map((a) => (a as JsTuple).items.map((x) => (typeof x === 'boolean' ? x : asExpr(x))) as [Expr, Expr | boolean]))),
  '.matches': (args, kw, self) => {
    noKw(kw);
    // SymPy TensExpr.matches / TensorIndex.matches: the tensor pattern's own matcher
    if (self instanceof sj.TensExpr || self instanceof sj.TensorIndex) return matchDict(self.matches(asExpr(args[0])));
    return matchDict(sj.match(asExpr(args[0]), asExpr(self)));
  },
  legendre_symbol: (args, kw) => (noKw(kw), sj.Rational.of(sj.legendreSymbol((args[0] as sj.Rational).p, (args[1] as sj.Rational).p))),
  motzkin: (args, kw) => (noKw(kw), sj.Rational.of(sj.motzkin(Number((args[0] as sj.Rational).p)))),
  andre: (args, kw) => (noKw(kw), sj.Rational.of(sj.andre(Number((args[0] as sj.Rational).p)))),
  PurePoly: (args, kw) => {
    for (const k of Object.keys(kw)) if (k !== 'domain') throw new Unsupported(`kwargs ${k}`);
    return sj.Poly.from(asExpr(args[0]), args.slice(1).map(asExpr), { pure: true, ...(kw['domain'] ? { domain: String(kw['domain']) } : {}) });
  },
  GroebnerBasis: (args, kw) => ADAPTERS['groebner']!([new JsList(args[0] instanceof JsList || args[0] instanceof JsTuple ? args[0].items : [args[0]]), ...args.slice(1)], kw),
  nth_power_roots_poly: (args, kw) => (noKw(kw), polyOf([args[0]]).nthPowerRootsPoly(Number((args[1] as sj.Rational).p))),
  det_quick: (args, kw) => (noKw(kw), (args[0] as Matrix).det()),
  inv_quick: (args, kw) => (noKw(kw), (args[0] as Matrix).inv()),
  linear_eq_to_matrix: (args, kw) => {
    noKw(kw);
    const eqs = args[0] instanceof JsList || args[0] instanceof JsTuple ? args[0].items.map(asExpr) : [asExpr(args[0])];
    const syms = args[1] instanceof JsList || args[1] instanceof JsTuple ? args[1].items.map(asSym) : args.slice(1).map(asSym);
    return new JsTuple(sj.linearEqToMatrix(eqs, syms));
  },
  '.rref_rhs': matrixMethod((m, [b]) => new JsTuple(sj.rrefRhs(m, b as Matrix))),
  '.rank_decomposition': matrixMethod((m) => new JsTuple(sj.rankDecomposition(m))),
  '.inv_mod': matrixMethod((m, [k]) => sj.invMod(m, (k as sj.Rational).p)),
  '.permute_rows': matrixMethod((m, [p]) => sj.permuteRows(m, (p as JsList).items.map((i) => Number((i as sj.Rational).p)))),
  '.permute_cols': matrixMethod((m, [p]) => sj.permuteCols(m, (p as JsList).items.map((i) => Number((i as sj.Rational).p)))),
  '.rmultiply': matrixMethod((m, [b]) => (b as Matrix).mul(m)),
  '.jordan_form': matrixMethod((m) => new JsTuple(sj.jordanForm(m))),
  '.liupc': matrixMethod((m) => {
    const [R, parent] = sj.liupc(m);
    const ints = (xs: number[]) => new JsList(xs.map((i) => sj.Rational.of(i)));
    return new JsTuple([new JsList(R.map(ints)), ints(parent)]);
  }),
  '.row_structure_symbolic_cholesky': matrixMethod((m) => new JsList(sj.rowStructureSymbolicCholesky(m).map((xs) => new JsList(xs.map((i) => sj.Rational.of(i)))))),
  '.irregular': (args, kw) => (noKw(kw), sj.irregular(Number((args[0] as sj.Rational).p), ...(args.slice(1) as Matrix[]))),
  '.berkowitz_eigenvals': (args, kw, self) => ADAPTERS['.eigenvals']!(args, kw, self),
  '.is_hypergeometric': (args, kw, self) => (noKw(kw), sj.isHypergeometric(asExpr(self), asExpr(args[0]))),
  '.taylor_term': (args, kw, self) => (noKw(kw), sj.taylorTerm(asExpr(self), Number((args[0] as sj.Rational).p), asSym(args[1]))),
  '.as_immutable': (_a, kw, self) => (noKw(kw), self),
  '.as_mutable': (_a, kw, self) => (noKw(kw), self),
  '.orthogonalize': (args, kw) => {
    for (const k of Object.keys(kw)) if (k !== 'normalize') throw new Unsupported(`kwargs ${k}`);
    return new JsList(sj.GramSchmidt(args as Matrix[], Boolean(kw['normalize'])));
  },
  MutableDenseMatrix: (args, kw) => ADAPTERS['Matrix']!(args, kw),
  MutableMatrix: (args, kw) => ADAPTERS['Matrix']!(args, kw),
  parse_expr: (args, kw) => {
    for (const k of Object.keys(kw)) if (!['transformations', 'evaluate', 'local_dict'].includes(k)) throw new Unsupported(`kwargs ${k}`);
    const tr0 = kw['transformations'];
    // a tuple of SymPy transformations: the implicit ones (multiplication, application, splitting of symbols) and
    // convert_equals_signs map to the parser options
    const names = tr0 instanceof JsTuple ? tr0.items.map((f) => (f as JsFunc).name) : [];
    const equals = names.includes('convert_equals_signs');
    const each: Readonly<Record<string, readonly sj.ParseTransformation[]>> = {
      implicit_multiplication: ['implicitMultiplication'], implicit_application: ['implicitApplication'],
      function_exponentiation: ['functionExponentiation'], split_symbols: ['splitSymbols'],
      implicit_multiplication_application: ['implicitMultiplication', 'implicitApplication', 'functionExponentiation', 'splitSymbols'],
    };
    const chosen = [...new Set(names.flatMap((n) => each[n] ?? []))];
    const tr = tr0 instanceof JsTuple ? (chosen.length ? chosen : undefined) : tr0;
    if (tr !== undefined && tr !== 'all' && tr !== 'implicit' && !Array.isArray(tr)) throw new Unsupported('transformations');
    // a function class in local_dict is a function of the parser's locals, anything else an expression
    const locals = kw['local_dict'] instanceof JsDict ? Object.fromEntries(kw['local_dict'].entries.map(([k, v]) => [String(k), v instanceof UFnClass ? sj.SymFunction(v.name) : asExpr(v)])) : undefined;
    return sj.parse(String(args[0]), { ...(tr ? { transformations: tr as sj.ParseOptions['transformations'] } : {}), ...(equals ? { convertEqualsSigns: true } : {}), ...(kw['evaluate'] === false ? { evaluate: false } : {}), ...(locals ? { locals } : {}) });
  },
  sympify: (args, kw) => {
    for (const k of Object.keys(kw)) if (!['rational', 'evaluate', 'convert_xor', 'locals'].includes(k)) throw new Unsupported(`kwargs ${k}`);
    const v = args[0];
    const localsArg = args[1] instanceof JsDict ? args[1] : kw['locals'] instanceof JsDict ? kw['locals'] : undefined;
    if (typeof v === 'string' && (kw['evaluate'] === false || kw['convert_xor'] === false || localsArg)) {
      // a locals value that is not an expression (sympy.abc._clash entries) makes the name a plain symbol
      const symbols = localsArg ? Object.fromEntries(localsArg.entries.map(([k, x]) => [String(k), typeof x === 'string' || x === null ? new Sym(String(k)) : asExpr(x)])) : undefined;
      return sj.parse(v, { ...(kw['evaluate'] === false ? { evaluate: false } : {}), ...(kw['convert_xor'] === false ? { convertXor: false } : {}), ...(symbols ? { symbols } : {}) });
    }
    if (typeof v === 'string') {
      if (kw['rational'] === true) {
        // decimal literals become exact rationals
        return sj.parse(v.replace(/\d*\.\d+(?:[eE][+-]?\d+)?/g, (m) => `(${sj.str(sj.rationalFromString(m))})`));
      }
      const t = v.trim();
      if (t.startsWith('[') && t.endsWith(']')) {
        // a Python list literal: split on top-level commas
        const items: string[] = [];
        let depth = 0;
        let cur = '';
        for (const ch of t.slice(1, -1)) {
          if ('([{'.includes(ch)) depth++;
          if (')]}'.includes(ch)) depth--;
          if (ch === ',' && depth === 0) {
            items.push(cur);
            cur = '';
          } else cur += ch;
        }
        if (cur.trim()) items.push(cur);
        return new JsList(items.map((i) => sj.parse(i.trim())));
      }
      return sj.parse(v);
    }
    if (v instanceof JsTuple) return new JsList(v.items.map((i) => (typeof i === 'string' ? sj.parse(i) : asExpr(i))));
    return asExpr(v);
  },
  S: (args, kw) => ADAPTERS['sympify']!(args, kw),
  Rational: (args, kw) => {
    noKw(kw);
    const conv = (v: unknown): Expr =>
      typeof v === 'string' ? sj.rationalFromString(v) : v instanceof sj.Float ? sj.rationalFromFloat(v.value) : asExpr(v);
    const [p, q] = args.map(conv);
    return q ? sj.mul(p!, sj.pow(q, -1)) : p;
  },
  Integer: (args, kw) => {
    noKw(kw);
    const v = args[0];
    if (typeof v === 'string') return sj.Rational.of(BigInt(v));
    const e = asExpr(v);
    if (e instanceof sj.Float) return sj.Rational.of(BigInt(Math.trunc(e.value)));
    if (!(e instanceof sj.Rational && e.isInteger)) throw new Unsupported('Integer');
    return e;
  },
  Add: (args, kw) => {
    for (const k of Object.keys(kw)) if (k !== 'evaluate') throw new Unsupported(`kwargs ${k}`);
    if (kw['evaluate'] === false) return new sj.Add(args.map(asExpr));
    return sj.add(...args.map(asExpr));
  },
  Mul: (args, kw) => {
    for (const k of Object.keys(kw)) if (k !== 'evaluate') throw new Unsupported(`kwargs ${k}`);
    if (kw['evaluate'] === false) {
      return new sj.Mul(args.map(asExpr));
    }
    return sj.mul(...args.map(asExpr));
  },
  Interval: (args, kw) => (noKw(kw), sj.interval(asExpr(args[0]), asExpr(args[1]), Boolean(args[2]), Boolean(args[3]))),
  // a Python set as an element is a FiniteSet (SymPy sympify)
  // a Python set as an element is a FiniteSet and a tuple a Tuple (SymPy sympify)
  FiniteSet: (args, kw) => (noKw(kw), sj.finiteSet(...args.map((a) => (a instanceof JsSet ? sj.finiteSet(...a.items.map(asExpr)) : a instanceof JsTuple && !a.isList ? sj.Tuple(...a.items.map(asExpr)) : asExpr(a))))),
  Range: (args, kw) => (noKw(kw), args.length === 1 ? sj.Range.of(0, asExpr(args[0])) : sj.Range.of(asExpr(args[0]), asExpr(args[1]), args[2] === undefined ? 1 : asExpr(args[2]))),
  '.powerset': (_args, kw, self) => (noKw(kw), sj.powerset(asSet(self))),
  '.symmetric_difference': (args, kw, self) => (noKw(kw), sj.symmetricDifference(asSet(self), asSet(args[0]))),
  // squares.lamda(2): the Lambda of an ImageSet applied
  '.lamda': (args, kw, self) => (noKw(kw), (self as sj.ImageSet).lamda.call(...args.map(asExpr))),
  use: (args, kw, _self) => {
    for (const k of Object.keys(kw)) if (k !== 'level') throw new Unsupported(`kwargs ${k}`);
    const f = args[1];
    const g = f instanceof JsFunc ? (sj as unknown as Record<string, unknown>)[f.name] : undefined;
    if (typeof g !== 'function') throw new Unsupported('use function');
    return sj.use(asExpr(args[0]), (x) => (g as (e: Expr) => Expr)(x), kw['level'] === undefined ? 0 : intArg(kw['level']));
  },
  Union: (args, kw) => (noKw(kw), sj.union(...args.map(asSet))),
  Intersection: (args, kw) => (noKw(kw), sj.intersection(...args.map(asSet))),
  Complement: (args, kw) => (noKw(kw), sj.complement(asSet(args[0]), asSet(args[1]))),
  '.open': (args, kw, self) => typeMethod(self, 'Interval', () => sj.interval(asExpr(args[0]), asExpr(args[1]), true, true), kw),
  '.Lopen': (args, kw, self) => typeMethod(self, 'Interval', () => sj.interval(asExpr(args[0]), asExpr(args[1]), true, false), kw),
  '.Ropen': (args, kw, self) => typeMethod(self, 'Interval', () => sj.interval(asExpr(args[0]), asExpr(args[1]), false, true), kw),
  '.contains': (args, kw, self) => (noKw(kw), self instanceof sj.GroebnerBasis ? self.contains(asExpr(args[0])) : sj.contains(asSet(self), asExpr(args[0]))),
  '.intersect': (args, kw, self) => (noKw(kw), sj.intersection(asSet(self), asSet(args[0]))),
  '.union': (args, kw, self) => (noKw(kw), sj.union(asSet(self), asSet(args[0]))),
  '.is_subset': (args, kw, self) => (noKw(kw), none(sj.isSubset(asSet(self), asSet(args[0])))),
  // SymPy defines these by is_subset and intersect
  '.is_superset': (args, kw, self) => (noKw(kw), none(sj.isSubset(asSet(args[0]), asSet(self)))),
  '.is_proper_subset': (args, kw, self) => (noKw(kw), asSet(self).key === asSet(args[0]).key ? false : none(sj.isSubset(asSet(self), asSet(args[0])))),
  '.is_proper_superset': (args, kw, self) => (noKw(kw), asSet(self).key === asSet(args[0]).key ? false : none(sj.isSubset(asSet(args[0]), asSet(self)))),
  '.is_disjoint': (args, kw, self) => (noKw(kw), sj.intersection(asSet(self), asSet(args[0])) === sj.EmptySet),
  // A.complement(U) is Complement(U, A)
  '.complement': (args, kw, self) => (noKw(kw), sj.complement(asSet(args[0]), asSet(self))),
  imageset: (args, kw) => {
    noKw(kw);
    if (args.length === 3) return sj.imageset(asExpr(args[0]), asExpr(args[1]), asSet(args[2]));
    if (args.length !== 2) throw new Unsupported('imageset over several sets');
    const [f, base] = args;
    if (f instanceof FnClass) {
      const x = sj.symbol('x');
      return sj.imageset(x, applyFn(f.name, [x]), asSet(base));
    }
    if (!(f instanceof JsLambda) || f.vars.length !== 1) throw new Unsupported('imageset function');
    // a Python lambda's parameter is a symbol of the same name
    const v = f.vars[0]!;
    const x = v instanceof sj.Dummy ? sj.symbol(v.name) : v;
    return sj.imageset(x, f.call(x), asSet(base));
  },
  ConditionSet: (args, kw) => (noKw(kw), sj.ConditionSet.of(asExpr(args[0]), asExpr(args[1]), args[2] === undefined ? sj.UniversalSet : asSet(args[2]))),
  Contains: (args, kw) => {
    noKw(kw);
    // SymPy Contains evaluates to a truth value when membership is decided
    const v = sj.containsQ(asSet(args[1]), asExpr(args[0]));
    return typeof v === 'boolean' ? v : new sj.Contains(asExpr(args[0]), asSet(args[1]));
  },
  FunctionMatrix: (args, kw) => {
    noKw(kw);
    const f = args[2];
    return sj.FunctionMatrix(asExpr(args[0]), asExpr(args[1]), typeof f === 'string' ? f : (lambdaAsNode(f) as sj.Lambda));
  },
  '.as_relational': (args, kw, self) => (noKw(kw), sj.asRelational(asSet(self), asExpr(args[0]))),
  solveset: (args, kw) => {
    for (const k of Object.keys(kw)) if (k !== 'domain') throw new Unsupported(`kwargs ${k}`);
    const dom = (kw['domain'] ?? args[2]) as sj.SetExpr | undefined;
    const f = asExpr(args[0]);
    const x = args[1] ? asSym(args[1]) : (sj.freeSymbols(f).values().next().value as Sym);
    return sj.solveset(f, x, dom ?? sj.Complexes);
  },
  solve_univariate_inequality: (args, kw) => {
    for (const k of Object.keys(kw)) if (!['relational', 'domain'].includes(k)) throw new Unsupported(`kwargs ${k}`);
    const rel = kw['relational'] ?? args[2];
    const dom = (kw['domain'] ?? args[3]) as sj.SetExpr | undefined;
    return sj.solveUnivariateInequality(asExpr(args[0]), asSym(args[1]), { relational: rel === undefined ? true : Boolean(rel), domain: dom });
  },
  solve_poly_inequality: (args, kw) => (noKw(kw), new JsList(sj.solvePolyInequality(asPoly(args[0]), args[1] as string))),
  solve_rational_inequalities: (args, kw) => {
    noKw(kw);
    const groups = (args[0] as JsList).items.map((g) =>
      (g as JsList).items.map((it) => {
        const [nd, rel] = (it as JsTuple).items as [JsTuple, string];
        return [[asPoly(nd.items[0]), asPoly(nd.items[1])], rel] as [[sj.Poly, sj.Poly], string];
      }),
    );
    return sj.solveRationalInequalities(groups);
  },
  reduce_abs_inequality: (args, kw) => (noKw(kw), reduceAbs(asExpr(args[0]), args[1] as string, asSym(args[2]))),
  reduce_abs_inequalities: (args, kw) => {
    noKw(kw);
    const x = asSym(args[1]);
    return sj.and(...(args[0] as JsTuple).items.map((it) => reduceAbs(asExpr((it as JsTuple).items[0]), (it as JsTuple).items[1] as string, x)));
  },
  reduce_inequalities: (args, kw) => {
    noKw(kw);
    const a = args[0];
    const ineqs = a instanceof JsList || a instanceof JsTuple ? a.items.map(asExpr) : [asExpr(a)];
    const syms = args[1] instanceof JsList || args[1] instanceof JsTuple ? args[1].items.map(asSym) : [];
    return sj.reduceInequalities(ineqs, syms);
  },
  periodicity: (args, kw) => (noKw(kw), none(sj.periodicity(asExpr(args[0]), asSym(args[1])))),
  singularities: (args, kw) => (noKw(kw), sj.singularities(asExpr(args[0]), asSym(args[1]), args[2] as sj.SetExpr | undefined)),
  stationary_points: (args, kw) => (noKw(kw), sj.stationaryPoints(asExpr(args[0]), asSym(args[1]), (args[2] as sj.SetExpr | undefined) ?? sj.Reals)),
  maximum: (args, kw) => (noKw(kw), sj.maximum(asExpr(args[0]), asSym(args[1]), (args[2] as sj.SetExpr | undefined) ?? sj.Reals)),
  minimum: (args, kw) => (noKw(kw), sj.minimum(asExpr(args[0]), asSym(args[1]), (args[2] as sj.SetExpr | undefined) ?? sj.Reals)),
  is_increasing: monoAdapter(sj.isIncreasing),
  is_strictly_increasing: monoAdapter(sj.isStrictlyIncreasing),
  is_decreasing: monoAdapter(sj.isDecreasing),
  is_strictly_decreasing: monoAdapter(sj.isStrictlyDecreasing),
  is_monotonic: monoAdapter(sj.isMonotonic),
  is_convex: (args, kw) => {
    for (const k of Object.keys(kw)) if (k !== 'domain') throw new Unsupported(`kwargs ${k}`);
    if (args.length > 2) throw new Unsupported('multivariate convexity');
    return sj.isConvex(asExpr(args[0]), asSym(args[1]), (kw['domain'] as sj.SetExpr | undefined) ?? sj.Reals);
  },
  isprime: (args, kw) => (noKw(kw), sj.isprime(asExpr(args[0]))),
  jacobi_symbol: (args, kw) => (noKw(kw), sj.jacobiSymbol((args[0] as sj.Rational).p, (args[1] as sj.Rational).p)),
  kronecker_symbol: (args, kw) => (noKw(kw), sj.kroneckerSymbol((args[0] as sj.Rational).p, (args[1] as sj.Rational).p)),
  '.piecewise_integrate': (args, kw, self) => (noKw(kw), sj.piecewiseIntegrate(self as sj.Piecewise, asSym(args[0]))),
  '.as_expr_set_pairs': (args, kw, self) =>
    (noKw(kw), new JsList(sj.asExprSetPairs(asExpr(self), (args[0] as sj.SetExpr | undefined) ?? sj.Reals).map(([e, st]) => new JsTuple([e, st])))),
  piecewise_fold: (args, kw) => {
    noKw(kw);
    const e = asExpr(args[0]);
    const fold = (x: Expr): Expr => {
      const a = x.args.map(fold);
      const y = a.every((v, i) => v === x.args[i]) ? x : sj.rebuild(x, a);
      if ((y instanceof sj.Add || y instanceof sj.Mul) && y.args.filter((t) => t instanceof sj.Piecewise).length === 1) {
        const pw = y.args.find((t) => t instanceof sj.Piecewise) as sj.Piecewise;
        const others = y.args.filter((t) => t !== pw);
        const op = y instanceof sj.Add ? sj.add : sj.mul;
        return sj.piecewise(...pw.pairs.map(([v, c]) => [op(...others, v), c] as const));
      }
      return y;
    };
    return fold(e);
  },
  invert: (args, kw) => {
    for (const k of Object.keys(kw)) if (k !== 'integer_power') throw new Unsupported(`kwargs ${k}`);
    const syms = args.slice(1).filter((a) => a instanceof Sym) as Sym[];
    if (args.length === 2 && !(args[1] instanceof Sym)) {
      const f = asExpr(args[0]);
      const g = asExpr(args[1]);
      const gens = sj.sortGens([...sj.freeSymbols(sj.add(f, g))]);
      return sj.Poly.from(f, gens).invert(sj.Poly.from(g, gens)).asExpr();
    }
    return new JsTuple(sj.invertEquation(asExpr(args[0]), syms, { integerPower: Boolean(kw['integer_power']) }));
  },
  '.invert': (args, kw, self) => {
    noKw(kw);
    if (self instanceof sj.Rational && args[0] instanceof sj.Rational) return sj.modInverse(self, args[0]);
    if (self instanceof sj.Poly) return self.invert(args[0] as sj.Poly);
    throw new Unsupported('invert');
  },
  factor_system: (args, kw) => {
    noKw(kw);
    const eqs = (args[0] as JsList).items.map(asExpr);
    const gens = args[1] === undefined ? [] : (args[1] as JsList).items.map(asExpr);
    return new JsList(sj.factorSystem(eqs, gens).map((s) => new JsList(s)));
  },
  is_zero_dimensional: (args, kw) => {
    noKw(kw);
    const F = (args[0] as JsList).items.map(asExpr);
    const gens = args.slice(1).map(asSym);
    const vars = gens.length ? gens : (sj.sortGens([...sj.freeSymbols(sj.add(...F))]) as Sym[]);
    // zero-dimensional: every variable has a pure power as a leading monomial of the basis
    const G = sj.groebner(F, vars, 'grevlex');
    const lms = G.exprs.map((g) => sj.Poly.from(g, vars).monoms()[0]!);
    return vars.every((_, i) => lms.some((m) => m.every((k, j) => (j === i ? k > 0 : k === 0))));
  },
  '.keys': (_args, kw, self) => {
    noKw(kw);
    if (!(self instanceof JsDict)) throw new Unsupported('dictionary keys');
    return { toString: () => `dict_keys(${fmt(new JsList(self.entries.map(([key]) => key)))})` };
  },
  _linsolve: (args, kw) => {
    noKw(kw);
    const result = sj._linsolve(asExprList(args[0]), asExprList(args[1]));
    return result === sj.EmptySet ? null : fromJs(result);
  },
  _lin_eq2dict: (args, kw) => {
    noKw(kw);
    const result = sj._linEq2dict(asExpr(args[0]), new Set(asExprList(args[1])));
    return new JsTuple(result.map(fromJs));
  },
  _linear_eq_to_dict: (args, kw) => {
    noKw(kw);
    return new JsTuple(sj._linearEqToDict(asExprList(args[0]), asExprList(args[1])).map(fromJs));
  },
  dom_eigenvects: (args, kw) => {
    noKw(kw);
    const [rational, algebraic] = sj.domEigenvects(args[0] as sj.DomainMatrix, args[1] as Sym | undefined);
    const pack = (rows: unknown[][]) => new JsList(rows.map((row) => new JsTuple(row.map(fromJs))));
    return new JsTuple([pack(rational), pack(algebraic)]);
  },
  dom_eigenvects_to_sympy: (args, kw) => {
    for (const name of Object.keys(kw)) if (!['cubics', 'quartics', 'quintics'].includes(name)) throw new Unsupported(`kwargs ${name}`);
    const convert = (v: unknown) => (v as JsList).items.map((row) => (row as JsTuple).items.map((x, i) => i === 2 ? Number(x) : x instanceof JsDomain ? x.domain : x));
    const result = sj.domEigenvectsToSympy(convert(args[0]) as sj.RationalEigenvectors[], convert(args[1]) as sj.AlgebraicEigenvectors[], Matrix, kw);
    return new JsList(result.map(([value, mult, vectors]) => new JsTuple([value, mult, new JsList(vectors)])));
  },
  '.fglm': (args, kw, self) => {
    noKw(kw);
    return (self as sj.GroebnerBasis).fglm(String(args[0]) as sj.MonomialOrder);
  },
  groebner: (args, kw) => {
    for (const k of Object.keys(kw)) if (!['order', 'method'].includes(k)) throw new Unsupported(`kwargs ${k}`);
    const F = (args[0] as JsList).items.map(asExpr);
    const gens = args.slice(1).map(asSym);
    // a Python ordering object (order=lex) selects the ordering by its alias
    const o = kw['order'];
    const order = typeof o === 'object' && o !== null && 'alias' in o ? o.alias : o;
    return sj.groebner(F, gens.length ? gens : (sj.sortGens([...sj.freeSymbols(sj.add(...F))]) as Sym[]), (order as sj.MonomialOrder | undefined) ?? 'lex');
  },
  '.reduce': (args, kw, self) => {
    noKw(kw);
    if (!(self instanceof sj.GroebnerBasis)) throw new Unsupported('reduce');
    const isPoly = args[0] instanceof sj.Poly;
    const [qs, r] = self.reduce(isPoly ? (args[0] as sj.Poly).asExpr() : asExpr(args[0]));
    const wrap = (e: Expr) => (isPoly ? sj.Poly.from(e, self.gens, { domain: 'ZZ' }) : e);
    return new JsTuple([new JsList(qs.map(wrap)), wrap(r)]);
  },
  symmetrize: (args, kw) => {
    for (const k of Object.keys(kw)) if (k !== 'formal') throw new Unsupported(`kwargs ${k}`);
    const gens = args.slice(1).map(asSym);
    if (kw['formal']) {
      const [s, r, m] = sj.symmetrize(asExpr(args[0]), gens);
      return new JsTuple([s, r, new JsList(m.map(([a, b]) => new JsTuple([a, b])))]);
    }
    return new JsTuple(sj.symmetrizeExpr(asExpr(args[0]), gens));
  },
  separatevars: (args, kw) => {
    for (const k of Object.keys(kw)) if (!['symbols', 'dict', 'force'].includes(k)) throw new Unsupported(`kwargs ${k}`);
    const symsArg = kw['symbols'] ?? args[1];
    const symbols = symsArg instanceof JsTuple || symsArg instanceof JsList ? symsArg.items.map(asSym) : [];
    const r = kw['dict'] ? sj.separatevars(asExpr(args[0]), { symbols, dict: true, force: Boolean(kw['force']) }) : sj.separatevars(asExpr(args[0]), { symbols, force: Boolean(kw['force']) });
    if (sj.isNoMatch(r)) return null;
    if (r instanceof Map) return new JsDict([...r].map(([k, v]) => [k, v] as const));
    return r;
  },

  apart: (args, kw) => {
    for (const k of Object.keys(kw)) if (!['full', 'domain'].includes(k)) throw new Unsupported(`kwargs ${k}`);
    return sj.apart(asExpr(args[0]), args[1] === undefined ? undefined : asSym(args[1]), { full: Boolean(kw['full']), ...(kw['domain'] === undefined ? {} : { domain: kw['domain'] instanceof JsDomain ? kw['domain'].name : String(kw['domain']) }) });
  },
  apart_list: (args, kw) => {
    noKw(kw);
    const e = asExpr(args[0]);
    const x = args[1] === undefined ? ([...sj.freeSymbols(e)].filter((s) => s instanceof Sym)[0] as Sym) : asSym(args[1]);
    const [common, poly, terms, w] = sj.apartList(e, x);
    return new JsTuple([common, poly, new JsList(terms.map(([r, nf, df, ex]) => new JsTuple([Array.isArray(r) ? new JsList(r) : sj.Poly.from(r, [w]), nf, df, sj.Rational.of(ex)])))]);
  },
  assemble_partfrac_list: (args, kw) => {
    noKw(kw);
    const t = args[0] as JsTuple;
    const toLam = (f: unknown) => (f instanceof JsLambda ? sj.Lambda(f.vars, f.body) : (f as sj.Lambda));
    let w: Sym | undefined;
    const terms = ((t.items[2] as JsList).items as JsTuple[]).map((it) => {
      const [r, nf, df, ex] = it.items;
      let rr: Expr | Expr[];
      if (r instanceof sj.Poly) {
        w = r.gens[0] as Sym;
        rr = r.asExpr();
      } else rr = (r as JsList).items.map(asExpr);
      return [rr, toLam(nf), toLam(df), Number((ex as sj.Rational).p)] as sj.PartfracTerm;
    });
    const poly = t.items[1] instanceof sj.Poly ? t.items[1] : sj.Poly.from(asExpr(t.items[1]));
    return sj.assemblePartfracList([asExpr(t.items[0]), poly, terms, w ?? new sj.Dummy('w')]);
  },
  exp_polar: (args, kw) => (noKw(kw), sj.expPolar(asExpr(args[0]))),
  polar_lift: (args, kw) => (noKw(kw), sj.polarLift(asExpr(args[0]))),
  periodic_argument: (args, kw) => (noKw(kw), sj.periodicArgument(asExpr(args[0]), asExpr(args[1]))),
  principal_branch: (args, kw) => (noKw(kw), sj.principalBranch(asExpr(args[0]), asExpr(args[1]))),
  unbranched_argument: (args, kw) => (noKw(kw), sj.unbranchedArgument(asExpr(args[0]))),
  unpolarify: (args, kw) => (noKw(kw), sj.unpolarify(asExpr(args[0]))),
  '.extract_branch_factor': (_args, kw, self) => {
    for (const k of Object.keys(kw)) if (k !== 'allow_half') throw new Unsupported(`kwargs ${k}`);
    return new JsTuple(sj.extractBranchFactor(asExpr(self), Boolean(kw['allow_half'])));
  },
  frac: exprFn(sj.frac),
  nsimplify: (args, kw) => {
    for (const k of Object.keys(kw)) if (!['tolerance', 'rational', 'rational_conversion'].includes(k)) throw new Unsupported(`kwargs ${k}`);
    const constants = args[1] instanceof JsList || args[1] instanceof JsTuple ? args[1].items.map(asExpr) : undefined;
    return sj.nsimplify(asExpr(args[0]), {
      ...(constants ? { constants } : {}),
      tolerance: kw['tolerance'] === undefined ? undefined : asExpr(kw['tolerance']).toNumber(),
      rational: kw['rational'] as boolean | undefined,
      rationalConversion: kw['rational_conversion'] as 'base10' | 'exact' | undefined,
    });
  },
  sqrtdenest: exprFn(sj.sqrtdenest),
  '.extract_leading_order': (args, kw, self) =>
    (noKw(kw), new JsTuple(sj.extractLeadingOrder(asExpr(self), asSym(args[0])).map(([a, b]) => new JsTuple([a, b])))),
  '.as_finite_difference': (args, kw, self) => {
    for (const k of Object.keys(kw)) if (!['points', 'x0', 'wrt'].includes(k)) throw new Unsupported(`kwargs ${k}`);
    if (!(self instanceof sj.Derivative)) throw new Unsupported('as_finite_difference');
    const pts = kw['points'] ?? args[0];
    const points = pts === undefined ? 1 : pts instanceof JsList || pts instanceof JsTuple ? pts.items.map(asExpr) : asExpr(pts);
    const x0 = kw['x0'] ?? args[1];
    return sj.asFiniteDifference(self, points, x0 === undefined ? undefined : asExpr(x0), kw['wrt'] === undefined ? undefined : asSym(kw['wrt']));
  },
  '.pinv_solve': (args, kw, self) => {
    for (const k of Object.keys(kw)) if (k !== 'arbitrary_matrix') throw new Unsupported(`kwargs ${k}`);
    return sj.pinvSolve(self as Matrix, args[0] as Matrix, kw['arbitrary_matrix'] as Matrix | undefined);
  },
  '.is_meromorphic': (args, kw, self) => (noKw(kw), none(sj.isMeromorphic(asExpr(self), asExpr(args[0]), asExpr(args[1])))),
  ratsimp: exprFn(sj.ratsimp),
  primitive: (args, kw) => {
    for (const k of Object.keys(kw)) if (k !== 'expand') throw new Unsupported(`kwargs ${k}`);
    // expand=False: the expression as it is (SymPy treats it as a single term structure)
    if (kw['expand'] === false) return new JsTuple(sj.primitive(asExpr(args[0])));
    const p = polyOf(args);
    const [c, q] = p.primitive();
    return new JsTuple([c, q.asExpr()]);
  },
  content: (args, kw) => (noKw(kw), polyOf(args).content()),
  pdiv: polyFn(2, ([f, g]) => new JsTuple(f!.pdiv(g!))),
  prem: polyFn(2, ([f, g]) => f!.prem(g!)),
  pexquo: polyFn(2, ([f, g]) => f!.pexquo(g!)),
  gcdex: polyFn(2, ([f, g]) => new JsTuple(f!.gcdex(g!))),
  half_gcdex: polyFn(2, ([f, g]) => new JsTuple(f!.halfGcdex(g!))),
  sturm: polyFn(1, ([f]) => f!.sturm()),
  sqf_part: polyFn(1, ([f]) => f!.sqfPart()),
  subresultants: polyFn(2, ([f, g]) => f!.subresultants(g!)),
  reduced: (args, kw) => {
    noKw(kw);
    const G = (args[1] as JsTuple).items;
    const { ps, asPolys } = parallelPolys([args[0], ...G, ...args.slice(2)], G.length + 1);
    const gens = ps[0]!.gens as Sym[];
    const [qs, r] = sj.reduced(ps[0]!.asExpr(), ps.slice(1).map((p) => p.asExpr()), gens);
    const out = (e: Expr) => (asPolys ? sj.Poly.from(e, gens) : e);
    return new JsTuple([new JsList(qs.map(out)), out(r)]);
  },
  monic: polyFn(1, ([f]) => f!.monic()),
  trunc: polyFn(1, ([f], [p]) => f!.trunc(asExpr(p)), 1),
  sqf_list: polyFn(1, ([f]) => {
    const [c, fs] = f!.sqfListAll(false);
    return new JsTuple([c, new JsList(fs.map(([g, k]) => new JsTuple([g, k])))]);
  }),
  sqf: (args, kw) => {
    noKw(kw);
    const { ps, asPolys } = parallelPolys(args, 1);
    const [c, fs] = ps[0]!.sqfListAll(false);
    const e = sj.mul(c, ...fs.map(([g, k]) => sj.pow(g.asExpr(), k)));
    return asPolys ? sj.Poly.from(e, ps[0]!.gens) : e;
  },
  gcd_list: (args, kw) => {
    noKw(kw);
    const fs = (args[0] as JsTuple).items;
    const { ps, asPolys } = parallelPolys([...fs, ...args.slice(1)], fs.length);
    const r = ps.reduce((a, b) => a.gcd(b));
    return asPolys ? r : r.asExpr();
  },
  lcm_list: (args, kw) => {
    noKw(kw);
    const fs = (args[0] as JsTuple).items;
    const { ps, asPolys } = parallelPolys([...fs, ...args.slice(1)], fs.length);
    const r = ps.reduce((a, b) => a.lcm(b));
    return asPolys ? r : r.asExpr();
  },
  viete: (args, kw) => {
    noKw(kw);
    const f = asExprOrPoly(args[0]);
    const x = args[2] ? asSym(args[2]) : (sj.sortGens([...sj.freeSymbols(f)])[0] as Sym);
    const p = sj.Poly.from(f, [x]);
    const n = p.degree();
    const rs = args[1] ? (args[1] as JsTuple).items.map(asExpr) : Array.from({ length: n }, (_, i) => new Sym(`r${i + 1}`));
    const cs = p.allCoeffs();
    const lc = cs[0]!;
    const out: JsTuple[] = [];
    // elementary symmetric polynomials of the roots
    const choose = (k: number, start: number): Expr[][] => (k === 0 ? [[]] : rs.slice(start).flatMap((r, i) => choose(k - 1, start + i + 1).map((c) => [r, ...c])));
    for (let k = 1; k <= n; k++) {
      const sym = sj.add(...choose(k, 0).map((c) => sj.mul(...c)));
      out.push(new JsTuple([sym, sj.mul(k % 2 ? -1 : 1, cs[k]!, sj.pow(lc, -1))]));
    }
    return new JsList(out);
  },
  poly: (args, kw) => (noKw(kw), sj.Poly.from(asExprOrPoly(args[0]), args.slice(1).map(asExpr))),
  pquo: polyFn(2, ([f, g]) => asPoly(f).pquo(asPoly(g))),
  exquo: polyFn(2, ([f, g]) => asPoly(f).exquo(asPoly(g))),
  cofactors: polyFn(2, ([f, g]) => new JsTuple(asPoly(f).cofactors(asPoly(g)))),
  compose: polyFn(2, ([f, g]) => asPoly(f).compose(asPoly(g))),
  decompose: polyFn(1, ([f]) => asPoly(f).decompose()),
  '.decompose': polyM((p) => new JsList(p.decompose())),
  degree_list: (args, kw) => (noKw(kw), new JsTuple(polyOf(args).degreeList())),
  '.retract': (_args, kw, self) => {
    for (const k of Object.keys(kw)) if (k !== 'field') throw new Unsupported(`kwargs ${k}`);
    return asPoly(self).retract(Boolean(kw['field']));
  },
  nroots: (args, kw) => {
    for (const k of Object.keys(kw)) if (k !== 'n') throw new Unsupported(`kwargs ${k}`);
    const n = kw['n'] ?? args[1];
    return new JsList(sj.nroots(args[0] instanceof sj.Poly ? args[0] : asExpr(args[0]), n === undefined ? 15 : intArg(n)));
  },
  '.nroots': (args, kw, self) => {
    for (const k of Object.keys(kw)) if (k !== 'n') throw new Unsupported(`kwargs ${k}`);
    const n = kw['n'] ?? args[0];
    return new JsList(sj.nroots(asPoly(self), n === undefined ? 15 : intArg(n)));
  },
  '.is_convergent': (_args, kw, self) => {
    noKw(kw);
    if (!(self instanceof sj.Concrete)) throw new Unsupported('is_convergent');
    return none(sj.isConvergent(self));
  },
  '.is_absolutely_convergent': (_args, kw, self) => {
    noKw(kw);
    if (!(self instanceof sj.Concrete)) throw new Unsupported('is_absolutely_convergent');
    return none(sj.isAbsolutelyConvergent(self));
  },
  '.as_sum': (args, kw, self) => {
    for (const k of Object.keys(kw)) if (k !== 'method' && k !== 'evaluate') throw new Unsupported(`kwargs ${k}`);
    if (!(self instanceof Integral) || !self.limits) throw new Unsupported('as_sum');
    const method = (kw['method'] ?? args[1] ?? 'midpoint') as 'midpoint';
    return sj.asSum(self, asExpr(args[0]), method, { evaluate: kw['evaluate'] !== false });
  },
  '.euler_maclaurin': (args, kw, self) => {
    for (const k of Object.keys(kw)) if (k !== 'm' && k !== 'n') throw new Unsupported(`kwargs ${k}`);
    const m = Number(((kw['m'] ?? args[0] ?? sj.Rational.of(0)) as sj.Rational).p);
    const n = Number(((kw['n'] ?? args[1] ?? sj.Rational.of(0)) as sj.Rational).p);
    return new JsTuple(sj.eulerMaclaurin(self as sj.Concrete, m, n));
  },
  igcd: (args, kw) => (noKw(kw), sj.Rational.of(sj.igcd(...args.map((a) => (a as sj.Rational).p)))),
  igcdex: (args, kw) => (noKw(kw), sj.igcdex((args[0] as sj.Rational).p, (args[1] as sj.Rational).p)),
  isqrt: (args, kw) => (noKw(kw), sj.isqrt((args[0] as sj.Rational).p)),
  ilcm: (args, kw) => (noKw(kw), sj.Rational.of(sj.ilcm(...args.map((a) => (a as sj.Rational).p)))),
  integer_nthroot: (args, kw) => {
    noKw(kw);
    const [r, ok] = sj.integerNthroot((args[0] as sj.Rational).p, intArg(args[1]));
    return new JsTuple([sj.Rational.of(r), ok]);
  },
  trailing: (args, kw) => (noKw(kw), sj.trailing((args[0] as sj.Rational).p)),
  num_digits: (args, kw) => (noKw(kw), sj.numDigits((args[0] as sj.Rational).p, args[1] === undefined ? 10 : intArg(args[1]))),
  mod_inverse: (args, kw) => (noKw(kw), sj.modInverse(args[0] as sj.Rational, args[1] as sj.Rational)),
  prod: (args, kw) => {
    noKw(kw);
    const xs = args[0] instanceof JsList || args[0] instanceof JsTuple || args[0] instanceof JsIterator ? args[0].items.map(asExpr) : [];
    return sj.mul(args[1] === undefined ? 1 : asExpr(args[1]), ...xs);
  },
  nfloat: (args, kw) => {
    for (const k of Object.keys(kw)) if (!['n', 'exponent'].includes(k)) throw new Unsupported(`kwargs ${k}`);
    return sj.nfloat(asExpr(args[0]), kw['n'] === undefined ? 15 : intArg(kw['n']), Boolean(kw['exponent']));
  },
  comp: (args, kw) => {
    noKw(kw);
    const tol = args[2] === undefined ? undefined : args[2] === '' ? ('' as const) : asExpr(args[2]).toNumber();
    return sj.comp(asExpr(args[0]), asExpr(args[1]), tol);
  },
  var: (args, kw) => ADAPTERS['symbols']!(args, kw),
  '.limit_denominator': (args, kw, self) => (noKw(kw), sj.limitDenominator(self as sj.Rational, (args[0] as sj.Rational).p)),
  '.as_two_terms': exprMethod((e) => new JsTuple(sj.asTwoTerms(e))),
  '.has_xfree': (args, kw, self) => (noKw(kw), sj.hasXfree(asExpr(self), (args[0] as JsSet).items.filter((i) => !(i instanceof UFnClass)).map(asExpr))),
  '.is_algebraic_expr': (args, kw, self) => (noKw(kw), sj.isAlgebraicExpr(asExpr(self), args.map(asExpr))),
  '.dummy_eq': (args, kw, self) => (noKw(kw), sj.dummyEq(asExpr(lambdaAsNode(self)), asExpr(lambdaAsNode(args[0])), args[1] === undefined ? undefined : asExpr(args[1]))),
  '.compare': (args, kw, self) => (noKw(kw), Math.sign(sj.compareKeys(sj.sortKey(asExpr(self)), sj.sortKey(asExpr(args[0]))))),
  '.could_extract_minus_sign': exprMethod((e) => sj.couldExtractMinusSign(e)),
  '.as_ordered_factors': exprMethod((e) => new JsList(sj.orderedFactors ? sj.orderedFactors(e) : [e])),
  '.leadterm': (args, kw, self) => (noKw(kw), new JsTuple(sj.leadterm(asExpr(self), asSym(args[0])))),
  '.as_leading_term': (args, kw, self) => (noKw(kw), sj.asLeadingTerm(asExpr(self), asSym(args[0]))),
  '.getn': exprMethod((e) => none(sj.getn(e))),
  '.nseries': (args, kw, self) => {
    for (const k of Object.keys(kw)) if (k !== 'logx') throw new Unsupported(`kwargs ${k}`);
    const x = asSym(args[0]);
    const x0 = args[1] === undefined ? 0 : asExpr(args[1]);
    const n = args[2] === undefined ? 6 : intArg(args[2]);
    return sj.series(asExpr(self), x, x0, n, '+', kw['logx'] === undefined ? {} : { logx: asExpr(kw['logx']) });
  },
  root: (args, kw) => (noKw(kw), sj.root(asExpr(args[0]), asExpr(args[1]), args[2] === undefined ? 0 : asExpr(args[2]))),
  cbrt: exprFn(sj.cbrt),
  real_root: (args, kw) => (noKw(kw), sj.realRoot(asExpr(args[0]), asExpr(args[1]))),
  '.has_free': (args, kw, self) => {
    noKw(kw);
    return sj.hasFree(asExpr(self), ...args.map((a) => (a instanceof UFnClass ? { fn: a.name } : asExpr(a))));
  },
  '.as_coefficients_dict': (args, kw, self) => {
    noKw(kw);
    return new JsDefaultDict([...sj.asCoefficientsDict(asExpr(self), args.map(asExpr))]);
  },
  Pow: (args, kw) => (noKw(kw), sj.pow(asExpr(args[0]), asExpr(args[1]))),
  sqrt: exprFn(sj.sqrt),
  ...Object.fromEntries(
    SPECIAL_NAMES.map((n) => [
      n,
      ((args, kw) => {
        noKw(kw);
        return sj.fn(n, args.flatMap((a) => (a instanceof JsTuple ? a.items.map(asExpr) : [asExpr(a)])));
      }) as Adapter,
    ]),
  ),
  ff: (args, kw) => polyFactorial(args, kw, -1),
  rf: (args, kw) => polyFactorial(args, kw, 1),
  digamma: (args, kw) => {
    for (const k of Object.keys(kw)) if (k !== 'evaluate') throw new Unsupported(`kwargs ${k}`);
    return sj.digamma(asExpr(args[0]), { evaluate: kw['evaluate'] !== false });
  },
  trigamma: (args, kw) => {
    for (const k of Object.keys(kw)) if (k !== 'evaluate') throw new Unsupported(`kwargs ${k}`);
    return sj.trigamma(asExpr(args[0]), { evaluate: kw['evaluate'] !== false });
  },
  E1: exprFn(sj.E1),
  RisingFactorial: (args, kw) => (noKw(kw), sj.rf(asExpr(args[0]), asExpr(args[1]))),
  FallingFactorial: (args, kw) => (noKw(kw), sj.ff(asExpr(args[0]), asExpr(args[1]))),
  expand_func: exprFn(sj.expandFunc),
  conjugate: exprFn(sj.conjugate),
  exp: (args,kw) => (noKw(kw), args[0] instanceof Matrix ? sj.matrixExp(args[0]) : sj.exp(asExpr(args[0]))),
  Abs: exprFn(sj.abs),
  ...Object.fromEntries(FN_NAMES.map((n) => [n, exprFn((e) => sj.fn(n, [e]))])),
  log: (args, kw) => {
    noKw(kw);
    if (args.length < 1 || args.length > 2) throw new Unsupported('arity');
    return sj.log(asExpr(args[0]), args[1] === undefined ? undefined : asExpr(args[1]));
  },
  Eq: (args, kw) => {
    for (const k of Object.keys(kw)) if (k !== 'evaluate') throw new Unsupported(`kwargs ${k}`);
    if (kw['evaluate'] === false) return new sj.Rel('Eq', asExpr(args[0]), asExpr(args[1] ?? 0));
    return sj.Eq(asExpr(args[0]), asExpr(args[1] ?? 0));
  },
  StrictGreaterThan: (args, kw) => (noKw(kw), sj.Gt(asExpr(args[0]), asExpr(args[1]))),
  GreaterThan: (args, kw) => (noKw(kw), sj.Ge(asExpr(args[0]), asExpr(args[1]))),
  StrictLessThan: (args, kw) => (noKw(kw), sj.Lt(asExpr(args[0]), asExpr(args[1]))),
  LessThan: (args, kw) => (noKw(kw), sj.Le(asExpr(args[0]), asExpr(args[1]))),
  Ne: (args, kw) => (noKw(kw), sj.Ne(asExpr(args[0]), asExpr(args[1]))),
  Lt: (args, kw) => (noKw(kw), sj.Lt(asExpr(args[0]), asExpr(args[1]))),
  Le: (args, kw) => (noKw(kw), sj.Le(asExpr(args[0]), asExpr(args[1]))),
  Gt: (args, kw) => (noKw(kw), sj.Gt(asExpr(args[0]), asExpr(args[1]))),
  Ge: (args, kw) => (noKw(kw), sj.Ge(asExpr(args[0]), asExpr(args[1]))),

  // ---- manipulation
  expand: (args, kw) => {
    if (args.length !== 1) throw new Unsupported('arity');
    const { modulus, ...rest } = kw;
    const r = sj.expand(asExpr(args[0]), expandHints(rest));
    if (modulus === undefined) return r;
    // coefficients reduced modulo m (SymPy modulus hint, symmetric=False)
    const m = (modulus as sj.Rational).p;
    const gens = sj.sortGens([...sj.freeSymbols(r)]);
    const P = sj.Poly.from(r, gens);
    return sj.add(...P.terms().map(([mon, c]) => {
      const q = c as sj.Rational;
      if (!q.isInteger) throw new Unsupported('modulus with rational coefficients');
      return sj.mul(sj.Rational.of(((q.p % m) + m) % m), ...mon.map((k, i) => sj.pow(gens[i]!, k)));
    }));
  },
  expand_mul: exprFn(sj.expand_mul),
  expand_multinomial: exprFn(sj.expand_multinomial),
  expand_log: (args, kw) => sj.expand_log(asExpr(args[0]), Boolean(kw['force'])),
  expand_power_exp: exprFn((e) => sj.expand_power_exp(e)),
  expand_power_base: (args, kw) => {
    for (const k of Object.keys(kw)) if (k !== 'force' && k !== 'deep') throw new Unsupported(`kwargs ${k}`);
    return sj.expand_power_base(asExpr(args[0]), kw as { force?: boolean; deep?: boolean });
  },
  expand_trig: exprFn(sj.expand_trig),
  expand_complex: exprFn(sj.expand_complex),
  simplify: exprFn(sj.simplify),
  factor: (args, kw) => {
    for (const k of Object.keys(kw)) if (!['deep', 'gaussian', 'extension', 'modulus', 'domain', 'fraction'].includes(k)) throw new Unsupported(`kwargs ${k}`);
    if (args.length !== 1) throw new Unsupported('arity');
    const ext = kw['extension'];
    const extension = ext === undefined ? undefined : ext instanceof JsTuple || ext instanceof JsList ? ext.items.map(asExpr) : [asExpr(ext)];
    return sj.factor(asExpr(args[0]), { ...polynomialOptions(kw), deep: Boolean(kw['deep']), gaussian: Boolean(kw['gaussian']), extension, ...(kw['fraction'] === false ? { fraction: false } : {}) });
  },
  together: (args, kw) => {
    for (const k of Object.keys(kw)) if (k !== 'deep') throw new Unsupported(`kwargs ${k}`);
    return sj.together(asExpr(args[0]), { deep: Boolean(kw['deep']) });
  },
  cancel: (args, kw) => {
    for (const k of Object.keys(kw)) if (!['domain','modulus','extension'].includes(k)) throw new Unsupported(`kwargs ${k}`);
    if (args.length !== 1) throw new Unsupported('arity');
    return sj.cancel(asExpr(args[0]), polynomialOptions(kw));
  },
  trigsimp: (args, kw) => {
    for (const k of Object.keys(kw)) if (!["old", "deep", "method", "compare"].includes(k)) throw new Unsupported(`kwargs ${k}`);
    const opts = { old: Boolean(kw["old"]), deep: Boolean(kw["deep"]), method: kw["method"] as sj.TrigsimpOptions["method"] };
    // SymPy trigsimp of a tuple (sympified to a Tuple) or a matrix (Matrix._eval_trigsimp): elementwise
    const go = (v: unknown): unknown =>
      v instanceof JsTuple ? new JsTuple(v.items.map(go)) : v instanceof Matrix ? v.map((e) => sj.trigsimp(e, opts)) : sj.trigsimp(asExpr(v), opts);
    return go(args[0]);
  },
  trigsimp_groebner: (args, kw) => {
    const hint = (v: unknown): unknown => v instanceof FnClass ? v.name : v instanceof JsTuple || v instanceof JsList ? v.items.map(hint) : toJs(v, true);
    return sj.trigsimpGroebner(asExpr(args[0]), Object.fromEntries(Object.entries(kw).map(([k, v]) => [camel(k), hint(v)])));
  },
  '.limits': (_args, kw, self) => {
    noKw(kw);
    const limits = (e: unknown): readonly (readonly Expr[])[] => e instanceof sj.Concrete ? e.limits : e instanceof Integral ? [...(e.integrand instanceof Integral ? limits(e.integrand) : []), e.args.slice(1)] : [];
    if (!(self instanceof Integral || self instanceof sj.Concrete)) throw new Unsupported('limits receiver');
    return new JsTuple(limits(self).map((l) => new JsTuple([...l])));
  },
  // SymPy set_norm(None) removes the norm
  '.set_norm': (args, kw, self) => (noKw(kw), (self as sj.Quaternion).setNorm(args[0] === null ? undefined : asExpr(args[0])), null),
  exptrigsimp: exprFn(sj.exptrigsimp),
  besselsimp: exprFn(sj.besselsimp),
  gammasimp: exprFn(sj.gammasimp),
  combsimp: exprFn(sj.combsimp),
  polarify: (args, kw) => {
    for (const k of Object.keys(kw)) if (k !== 'lift' && k !== 'subs') throw new Unsupported(`kwargs ${k}`);
    const r = sj.polarify(asExpr(args[0]), { lift: kw['lift'] === undefined ? undefined : Boolean(kw['lift']), subs: kw['subs'] === undefined ? undefined : Boolean(kw['subs']) });
    return Array.isArray(r) ? new JsTuple([r[0], new JsDict(r[1])]) : r;
  },
  piecewise_exclusive: (args, kw) => {
    for (const k of Object.keys(kw)) if (k !== 'skip_nan') throw new Unsupported(`kwargs ${k}`);
    return sj.piecewiseExclusive(asExpr(args[0]), { skipNan: Boolean(kw['skip_nan']) });
  },
  Id: exprFn((e) => e),
  intervals: (args, kw) => intervalsAdapter(polyOf(args), kw),
  '.intervals': (_a, kw, self) => intervalsAdapter(asPoly(self), kw),
  refine_root: (args, kw) => refineAdapter(polyOf([args[0]]), args.slice(1), kw),
  '.refine_root': (args, kw, self) => refineAdapter(asPoly(self), args, kw),
  Mod: (args, kw) => {
    noKw(kw);
    const [a, m] = args.map(asExpr);
    if (a instanceof sj.Rational && m instanceof sj.Rational && a.isInteger && m.isInteger) return sj.Rational.of(((a.p % m.p) + m.p) % m.p);
    // an unevaluated binomial of integers (SymPy binomial._eval_Mod)
    if (a instanceof sj.AppliedFunction && a.name === 'binomial' && m instanceof sj.Rational && a.args.every((u) => u instanceof sj.Rational && u.isInteger)) {
      return sj.Rational.of(sj.binomialMod((a.args[0] as sj.Rational).p, (a.args[1] as sj.Rational).p, m.p));
    }
    // an unevaluated power or factorial is reduced by Mod itself (SymPy Pow._eval_Mod, factorial._eval_Mod)
    return sj.Mod(a!, m!);
  },
  '.as_poly': (args, kw, self) => {
    noKw(kw);
    let e = asExpr(self);
    if (e instanceof sj.Rel && e.op === 'Eq') e = sj.add(e.lhs, sj.mul(-1, e.rhs));
    // SymPy None (NoMatch) for an expression that is not a polynomial in the generators
    return none(sj.asPoly(e, ...args.map(asExpr)));
  },
  '.permute': (args, kw, self) => {
    for (const k of Object.keys(kw)) if (!['orientation', 'direction'].includes(k)) throw new Unsupported(`kwargs ${k}`);
    if (!(self instanceof Matrix)) throw new Unsupported('permute');
    const swaps = (args[0] as JsTuple).items.map((t) => (t as JsTuple).items.map((v) => Number((v as sj.Rational).p)) as [number, number]);
    const rows = (kw['orientation'] ?? 'rows') === 'rows';
    const order = (kw['direction'] ?? 'forward') === 'forward' ? swaps : [...swaps].reverse();
    let data = rows ? Array.from({ length: self.rows }, (_, i) => self.row(i)) : Array.from({ length: self.cols }, (_, j) => self.col(j));
    for (const [i, j] of order) {
      data = [...data];
      [data[i], data[j]] = [data[j]!, data[i]!];
    }
    return rows ? Matrix.of(data.map((r) => Array.from({ length: self.cols }, (_, j) => r.get(0, j)))) : Matrix.of(Array.from({ length: self.rows }, (_, i) => data.map((c) => c.get(i, 0))));
  },
  gff_list: (args, kw) => {
    noKw(kw);
    const p = polyOf(args);
    return new JsList(p.gffList().map(([h, k]) => new JsTuple([sj.Poly.from(h.asExpr(), p.gens), sj.Rational.of(k)])));
  },
  '.gff_list': (_a, kw, self) => {
    noKw(kw);
    const p = asPoly(self);
    return new JsList(p.gffList().map(([h, k]) => new JsTuple([sj.Poly.from(h.asExpr(), p.gens), sj.Rational.of(k)])));
  },
  factor_nc: exprFn(sj.factorNc),
  arity: (args, kw) => {
    noKw(kw);
    if (args[0] instanceof JsLambda) return sj.Rational.of(args[0].vars.length);
    if (args[0] instanceof FnClass) {
      // functions with optional arguments report (min, max) like SymPy
      const ranges: Record<string, [number, number]> = { log: [1, 2], atan2: [2, 2], polygamma: [2, 2], besselj: [2, 2], zeta: [1, 2], harmonic: [1, 2] };
      const r = ranges[args[0].name] ?? [1, 1];
      return r[0] === r[1] ? sj.Rational.of(r[0]) : new JsTuple(r.map((k) => sj.Rational.of(k)));
    }
    throw new Unsupported('arity');
  },
  '.applyfunc': (args, kw, self) => {
    noKw(kw);
    const f = args[0];
    const callback = f instanceof JsLambda ? (e: Expr) => asExpr(f.call(e)) : (f instanceof JsFunc || f instanceof FnClass) && typeof (sj as unknown as Record<string,unknown>)[f.name] === 'function' ? (sj as unknown as Record<string,(e:Expr)=>Expr>)[f.name] : undefined;
    if (self instanceof sj.MatrixExpr && callback) return self.applyfunc(callback);
    if (!(self instanceof Matrix) || !(f instanceof JsLambda)) throw new Unsupported('applyfunc');
    return self.map((e) => f.call(e));
  },
  '.as_dummy': (_args, kw, self) => {
    noKw(kw);
    if (self instanceof Sym && !(self instanceof sj.Dummy)) return new sj.Dummy(self.name, self.assumptions);
    if (self instanceof sj.Integral && self.args.length === 2) return self;
    if (self instanceof sj.Integral) {
      // bound variable replaced by a Dummy named 0 (SymPy as_dummy)
      const d = new sj.Dummy('0');
      const v = self.args[1]!;
      return new sj.Integral([sj.xreplace(self.args[0]!, [[v, d]]), d, ...self.args.slice(2)]);
    }
    throw new Unsupported('as_dummy');
  },
  LambertW: (args, kw) => (noKw(kw), sj.LambertW(asExpr(args[0]), args[1] === undefined ? undefined : asExpr(args[1]))),
  '.is_same': (args, kw, self) => {
    noKw(kw);
    const a = asExpr(self);
    const b = asExpr(args[0]);
    const fn = args[1] instanceof JsFunc ? args[1].name : undefined;
    // numbers are compared with the given function, everything else structurally
    const num = (x: Expr, y: Expr): boolean => {
      // SymPy equal_valued compares the exact (binary) values
      if (fn === 'equal_valued') return sj.equalValued(x, y);
      if (fn === 'math.isclose') {
        const u = x.toComplex().re;
        const v = y.toComplex().re;
        return Math.abs(u - v) <= 1e-9 * Math.max(Math.abs(u), Math.abs(v));
      }
      return x.key === y.key;
    };
    const same = (x: Expr, y: Expr): boolean =>
      x.isNumber && y.isNumber && x.args.length === 0 && y.args.length === 0
        ? num(x, y)
        : x.kind === y.kind && x.args.length === y.args.length && (x.args.length ? x.args.every((u, i) => same(u, y.args[i]!)) : x.key === y.key);
    return same(a, b);
  },
  '.rcall': (args, kw, self) => {
    noKw(kw);
    // apply every Lambda in the expression to the arguments (SymPy rcall)
    const xs = args.map(asExpr);
    const go = (e: Expr): Expr => (e instanceof sj.Lambda ? e.call(...xs) : e.args.length ? sj.rebuild(e, e.args.map(go)) : e);
    return go(asExpr(self));
  },
  '.fromiter': (args, kw) => (noKw(kw), new JsTuple((args[0] as JsTuple).items)),
  sstr: (args, kw) => {
    for (const k of Object.keys(kw)) if (k !== 'full_prec' && k !== 'perm_cyclic') throw new Unsupported(`kwargs ${k}`);
    // a Cycle prints as its str form
    if (args[0] instanceof sj.Cycle) return args[0].toString();
    // a Python tuple prints as a SymPy Tuple
    const v = args[0] instanceof JsTuple && !args[0].isList ? sj.Tuple(...args[0].items.map(asExpr)) : asExpr(args[0]);
    return sj.sstr(v, { ...(kw['full_prec'] === undefined ? {} : { fullPrec: kw['full_prec'] as boolean }), ...(kw['perm_cyclic'] === undefined ? {} : { permCyclic: kw['perm_cyclic'] as boolean }) });
  },
  rational_interpolate: (args, kw) => {
    for (const k of Object.keys(kw)) if (k !== 'X') throw new Unsupported(`kwargs ${k}`);
    const data = (args[0] as JsTuple | JsList).items.map((t) => (t as JsTuple).items.map(asExpr) as [Expr, Expr]);
    return sj.rationalInterpolate(data, Number((args[1] as sj.Rational).p), kw['X'] ? asSym(kw['X']) : undefined);
  },
  '.is_motzkin': (args, kw) => {
    noKw(kw);
    return sj.isMotzkin((args[0] as sj.Rational).p);
  },
  '.find_motzkin_numbers_in_range': (args, kw) => {
    noKw(kw);
    return new JsList(sj.motzkinNumbersInRange((args[0] as sj.Rational).p, (args[1] as sj.Rational).p).map((v) => sj.Rational.of(v)));
  },
  '.find_first_n_motzkins': (args, kw) => {
    noKw(kw);
    return new JsList(sj.firstMotzkins(Number((args[0] as sj.Rational).p)).map((v) => sj.Rational.of(v)));
  },
  '.factors': (args, kw, self) => {
    noKw(kw);
    if (args.length || !(self instanceof sj.Rational) || !self.isInteger) throw new Unsupported('factors');
    const n = self.p < 0n ? -self.p : self.p;
    return new JsDict([...sj.factorInt(n)].sort((a, b) => (a[0] < b[0] ? -1 : 1)).map(([p, k]) => [sj.Rational.of(p), sj.Rational.of(k)] as const));
  },
  not_empty_in: (args, kw) => {
    noKw(kw);
    if (args.length !== 2) throw new Unsupported('arity');
    return sj.notEmptyIn(args[0] as sj.SetExpr, asSym(args[1]));
  },
  powsimp: (args, kw) => {
    for (const k of Object.keys(kw)) if (!['deep', 'combine', 'force'].includes(k)) throw new Unsupported(`kwargs ${k}`);
    return sj.powsimp(asExpr(args[0]), {
      deep: (kw['deep'] ?? args[1]) as boolean | undefined,
      combine: kw['combine'] as 'all' | 'exp' | 'base' | undefined,
      force: kw['force'] as boolean | undefined,
    });
  },
  powdenest: (args, kw) => {
    for (const k of Object.keys(kw)) if (k !== 'force') throw new Unsupported(`kwargs ${k}`);
    return sj.powdenest(asExpr(args[0]), { force: Boolean(kw['force'] ?? args[1]) });
  },
  logcombine: (args, kw) => {
    for (const k of Object.keys(kw)) if (k !== 'force') throw new Unsupported(`kwargs ${k}`);
    return sj.logcombine(asExpr(args[0]), { force: Boolean(kw['force'] ?? args[1]) });
  },
  posify: (args, kw) => {
    noKw(kw);
    const [e, m] = sj.posify(asExpr(args[0]));
    return new JsTuple([e, new JsDict([...m])]);
  },
  radsimp: (args, kw) => {
    for (const k of Object.keys(kw)) if (k !== 'symbolic' && k !== 'max_terms') throw new Unsupported(`kwargs ${k}`);
    return sj.radsimp(asExpr(args[0]), { symbolic: kw['symbolic'] !== false, ...(kw['max_terms'] ? { maxTerms: Number((kw['max_terms'] as sj.Rational).p) } : {}) });
  },
  collect: (args, kw) => {
    const exact = kw['exact'];
    for (const k of Object.keys(kw)) if (k !== 'exact') throw new Unsupported(`kwargs ${k}`);
    if (args.length === 3 && args[2] instanceof JsFunc) {
      // collect(expr, syms, func): func applied to each collected coefficient
      const f = ADAPTERS[args[2].name];
      if (!f) throw new Unsupported('collect func');
      const syms = args[1] instanceof JsTuple ? args[1].items.map(asExpr) : [asExpr(args[1])];
      return sj.collect(asExpr(args[0]), syms, { func: (c) => f([c], {}) as Expr });
    }
    if (args.length !== 2) throw new Unsupported('collect arity');
    const syms = args[1] instanceof JsTuple ? args[1].items.map(asExpr) : [asExpr(args[1])];
    return sj.collect(asExpr(args[0]), syms, exact === undefined ? {} : exact === null ? { exact: null } : { exact: Boolean(exact) });
  },
  fraction: (args, kw) => {
    for (const k of Object.keys(kw)) if (k !== 'exact') throw new Unsupported(`kwargs ${k}`);
    return new JsTuple(sj.fraction(asExpr(args[0]), { exact: Boolean(kw['exact']) }));
  },
  diff: (args, kw) => (noKw(kw), diffArgs(asExpr(args[0]), args.slice(1))),
  integrate: (args, kw) => {
    for (const k of Object.keys(kw)) if (k !== 'conds') throw new Unsupported(`kwargs ${k}`);
    // a formal power series: its definite integral is that of its function (SymPy FormalPowerSeries.integrate)
    if (args[0] instanceof sj.FormalPowerSeries && args[1] instanceof JsTuple && args[1].items.length === 3) {
      const [v, lo, hi] = args[1].items;
      return args[0].integrate(asSym(v), [asExpr(lo), asExpr(hi)]);
    }
    const conds = kw['conds'] === undefined ? 'piecewise' : String(kw['conds']);
    let f = asExpr(args[0]);
    let lims = args.slice(1);
    if (!lims.length) {
      const fs = [...sj.freeSymbols(f)];
      if (fs.length !== 1) throw new Unsupported('integrate arity');
      lims = [fs[0]];
    }
    for (const v of lims) {
      if (v instanceof Sym) f = sj.integrate(f, v);
      else if (v instanceof JsTuple && v.items.length === 3)
        f = sj.integrate(f, asSym(v.items[0]), [asExpr(v.items[1]), asExpr(v.items[2])], { conds: conds === 'none' ? 'none' : 'piecewise' });
      else if (v instanceof JsTuple && v.items.length === 1) f = sj.integrate(f, asSym(v.items[0]));
      else throw new Unsupported('integrate limits');
    }
    if (conds === 'separate') {
      // (value, condition) instead of a Piecewise
      if (f instanceof sj.Piecewise && f.pairs.length === 2) return new JsTuple([f.pairs[0]![0], f.pairs[0]![1]]);
      return f;
    }
    return f;
  },
  roots: (args, kw) => {
    for (const k of Object.keys(kw)) if (!['multiple', 'quintics'].includes(k)) throw new Unsupported(`kwargs ${k}`);
    if (args[0] instanceof JsTuple) {
      // a list of coefficients
      const cs = args[0].items.map(asExpr);
      const t = new Sym('x');
      const result = sj.roots(sj.add(...cs.map((c, i) => sj.mul(c, sj.pow(t, cs.length - 1 - i)))), t, { multiple: true, skipQuintic: true, quintics: kw['quintics'] === true });
      return kw['multiple'] === true ? new JsList(result) : rootsDict(result);
    }
    const e = asExprOrPoly(args[0]);
    const syms = [...sj.freeSymbols(e)].filter((s) => s instanceof Sym);
    const x = args[1] ? asSym(args[1]) : args[0] instanceof sj.Poly ? (args[0].gens[0] as Sym) : syms.length === 1 ? syms[0]! : undefined;
    if (!x) throw new Unsupported('roots generator');
    const roots = sj.roots(e, x, { multiple: true, skipQuintic: true, quintics: kw['quintics'] === true });
    return kw['multiple'] === true ? new JsList(roots) : rootsDict(roots);
  },
  solve: (args, kw) => {
    for (const k of Object.keys(kw)) if (!['check', 'cubics', 'set', 'implicit'].includes(k)) throw new Unsupported(`kwargs ${k}`);
    if (kw['implicit'] === true && args.length === 2 && args[1] instanceof Sym) {
      // implicit=True: occurrences of x inside other functions are treated as constants
      const x = args[1];
      const reps: [Expr, Expr][] = [];
      const e0 = sj.mapBottomUp(asExpr(args[0]), (u) => {
        if (u.has(x) && (u instanceof sj.AppliedFunction || (u instanceof sj.Pow && u.exp.has(x)))) {
          const d = new sj.Dummy(`f${reps.length}`);
          reps.push([d, u]);
          return d;
        }
        return u;
      });
      return new JsList(sj.solve(e0, x).map((v) => sj.xreplace(v, reps)));
    }
    if (kw['set'] === true) {
      // set=True: ([symbols], {(solution,), ...}) for one equation in one unknown
      if (args.length !== 2 || args[0] instanceof JsTuple || args[0] instanceof JsList) throw new Unsupported('solve set form');
      const t = asExpr(args[1]);
      const d = t instanceof Sym ? t : new sj.Dummy('_t');
      const e = t instanceof Sym ? asExpr(args[0]) : sj.subs(asExpr(args[0]), [[t, d]]);
      const sols = sj.solve(e, d);
      return new JsTuple([new JsList([t]), new JsSet(sols.map((v) => new JsTuple([v])))]);
    }
    const check = kw['check'] === undefined ? undefined : Boolean(kw['check']);
    const cubics = kw['cubics'] === false ? false : undefined;
    const first = args[0];
    // systems of inequalities in one symbol
    if (first instanceof JsTuple && first.items.length && first.items.every((i) => i instanceof sj.Rel && i.op !== 'Eq' && i.op !== 'Ne')) {
      const syms = args.slice(1).filter((a) => a instanceof Sym) as Sym[];
      return sj.reduceInequalities(first.items.map(asExpr), syms);
    }
    // equations mixed with inequalities in one symbol (SymPy _solve_system with inequalities)
    if ((first instanceof JsTuple || first instanceof JsList) && first.items.some((i) => i instanceof sj.Rel && i.op !== 'Eq' && i.op !== 'Ne') && first.items.some((i) => !(i instanceof sj.Rel) || i.op === 'Eq')) {
      const isEq = (i: unknown) => !(i instanceof sj.Rel) || i.op === 'Eq';
      const syms = args.slice(1).filter((a) => a instanceof Sym) as Sym[];
      const eqs = first.items.filter(isEq).map(asExpr);
      if (syms.length !== 1 || eqs.length !== 1) throw new Unsupported('mixed system');
      const sols = sj.solve(eqs[0]!, syms[0]!);
      if (sols.length !== 1) throw new Unsupported('mixed system');
      const ineq = sj.reduceInequalities(first.items.filter((i) => !isEq(i)).map(asExpr), syms);
      return sj.And(ineq, sj.Eq(syms[0]!, sols[0]!));
    }
    // systems of equations
    if (first instanceof JsTuple) {
      // unknowns that are not symbols (x + 2, x*y) are solved for as dummies, like SymPy
      const targets = (args[1] instanceof JsTuple || args[1] instanceof JsSet ? args[1].items : args.slice(1)).map(asExpr);
      const syms = targets.map((t, i) => (t instanceof Sym ? t : new sj.Dummy(`_t${i}`)));
      const reps = targets.map((t, i) => [t, syms[i]!] as [Expr, Expr]).filter(([t]) => !(t instanceof Sym));
      const back = (v: Expr) => targets[syms.indexOf(v as Sym)] ?? v;
      // like SymPy, equations free of the requested symbols are dropped
      const eqs = first.items.map((e) => (reps.length ? sj.subs(asExpr(e), reps) : asExpr(e))).filter((e) => !syms.length || syms.some((s) => e.has(s)));
      const vars = syms.length ? syms : allSymbols(eqs);
      if (isLinearSystem(eqs, vars)) {
        const s = sj.linsolve(eqs, vars);
        if (!Array.isArray(s)) return new JsList([]);
        // underdetermined: SymPy lists only the solved (pivot) symbols
        return new JsDict(vars.map((v, i) => [back(v), s[i]!] as const).filter(([v, e]) => v.key !== e.key));
      }
      const sols = sj.nonlinsolve(eqs, vars);
      return new JsList(sols.map((t) => new JsDict(vars.map((v, i) => [back(v), t[i]!] as const))));
    }
    if (first instanceof JsList && first.items.some((i) => i instanceof sj.Rel && i.op !== 'Eq')) {
      const syms = args.slice(1).filter((a) => a instanceof Sym) as Sym[];
      const isEq = (i: unknown) => !(i instanceof sj.Rel) || i.op === 'Eq';
      if (first.items.some(isEq)) {
        // equations and inequalities in one symbol (SymPy _solve_system with inequalities)
        const eqs = first.items.filter(isEq).map(asExpr);
        if (syms.length !== 1 || eqs.length !== 1) throw new Unsupported('mixed system');
        const sols = sj.solve(eqs[0]!, syms[0]!);
        if (sols.length !== 1) throw new Unsupported('mixed system');
        const ineq = sj.reduceInequalities(first.items.filter((i) => !isEq(i)).map(asExpr), syms);
        return sj.And(ineq, sj.Eq(syms[0]!, sols[0]!));
      }
      return sj.reduceInequalities(first.items.map(asExpr), syms);
    }
    const e = first instanceof sj.Poly ? first.asExpr() : asExpr(first);
    if (e instanceof sj.Rel && e.op !== 'Eq' && e.op !== 'Ne') {
      return sj.reduceInequalities([e], args[1] instanceof Sym ? [args[1]] : []);
    }
    if (args[1] instanceof JsTuple) {
      // a single equation in several unknowns with other free symbols: undetermined coefficients
      const coeffs = args[1].items.map(asSym);
      const others = [...sj.freeSymbols(e)].filter((s) => s instanceof Sym).filter((s) => !coeffs.some((c) => c.key === s.key));
      if (!others.length) throw new Unsupported('solve for several symbols');
      const sols = sj.solveUndeterminedCoeffs(e, coeffs, others as Sym[]);
      if (sols.length !== 1) throw new Unsupported('solve for several symbols');
      return new JsDict(coeffs.map((c, i) => [c, sols[0]![i]!] as const));
    }
    const syms = [...sj.freeSymbols(e)].filter((s) => s instanceof Sym);
    if (args[1] instanceof sj.Rational) {
      // solving for a number: its occurrences (and those of its negative) become the unknown
      const n = args[1];
      const t = new sj.Dummy('t');
      const neg = sj.Rational.of(-n.p, n.q);
      const g = sj.mapBottomUp(e, (u) => (u.key === n.key ? t : u.key === neg.key && !n.isZero ? sj.mul(-1, t) : u));
      return new JsList(sj.solve(g, t));
    }
    if (args.length === 1 && syms.length > 1) {
      // several unknowns and none given: each factor solved for its first symbol (SymPy order)
      const sorted = sj.ordered(syms) as Sym[];
      const factors = e instanceof sj.Mul ? e.args.filter((f) => f.freeSymbols().size) : [e];
      const out: JsDict[] = [];
      for (const f of factors) {
        const u = sorted.find((s) => f.has(s) && sj.solve(f, s).length);
        if (!u) throw new Unsupported('solve form');
        for (const v of sj.solve(f, u)) out.push(new JsDict([[u, v]]));
      }
      return new JsList(out);
    }
    const x =
      args[1] instanceof Sym
        ? args[1]
        : args[1] instanceof Expr && !(args[1] instanceof sj.Rational)
          ? (args[1] as Sym)
          : args.length === 1 && syms.length === 1
            ? syms[0]!
            : undefined;
    if (args.length === 1 && syms.length === 0) return new JsList([]);
    if (!x || args.length > 2) throw new Unsupported('solve form');
    return new JsList(sj.solve(e, x, { ...(check === undefined ? {} : { check }), ...(cubics === false ? { cubics } : {}) }));
  },
  checksol: (args, kw) => {
    noKw(kw);
    const e = asExpr(args[0]);
    let reps: [Expr, Expr][];
    if (args[1] instanceof JsDict) reps = args[1].entries.map(([k, v]) => [asExpr(k), asExpr(v)]);
    else reps = [[asExpr(args[1]), asExpr(args[2])]];
    return none(sj.checksol(e, new Map(reps)));
  },
  linsolve: (args, kw) => {
    noKw(kw);
    const first = args[0];
    const syms = args[1] instanceof JsTuple ? args[1].items.map(asSym) : args.slice(1).map(asSym);
    let sol: Expr[] | undefined;
    if (first instanceof JsTuple && first.items.length === 2 && first.items[0] instanceof Matrix) {
      const [A, b] = first.items as [Matrix, Matrix];
      if (!syms.length) {
        // no symbols: free parameters are tau0, tau1, ... (SymPy gauss_jordan_solve)
        try {
          return new JsSet([new JsTuple(sj.gaussJordanSolve(A, b)[0].data)]);
        } catch {
          return 'EmptySet';
        }
      }
      sol = solveAug(A.hstack(b), syms);
    } else if (first instanceof Matrix) {
      sol = solveAug(first, syms);
    } else if (first instanceof JsTuple) {
      if (first.items.length === 0) return 'EmptySet';
      const r = sj.linsolve(first.items.map(asExpr), syms);
      sol = Array.isArray(r) ? r : undefined;
    } else throw new Unsupported('linsolve form');
    return sol ? new JsSet([new JsTuple(sol)]) : 'EmptySet';
  },
  solve_poly_system: (args, kw) => polySystemSolutions(args, kw),
  solve_triangulated: (args, kw) => {
    for (const k of Object.keys(kw)) if (k !== 'extension') throw new Unsupported(`kwargs ${k}`);
    // without extension only rational solutions are reported, with it all of them as CRootOf (SymPy)
    const sols = polySystemSolutions(args, {}, !kw['extension']) as JsList;
    if (!kw['extension']) return sols;
    const x0 = asSym(args[1]);
    const asRoot = (v: unknown): unknown => {
      if (!(v instanceof Expr) || v instanceof sj.Rational) return v;
      const mp = sj.minimalPolynomial(v, x0);
      const rs = sj.Poly.from(mp, [x0]).allRoots();
      const target = v.toComplex();
      const idx = rs.findIndex((r) => {
        const c = r.toComplex();
        return Math.hypot(c.re - target.re, c.im - target.im) < 1e-9;
      });
      return idx < 0 ? v : new sj.CRootOf(mp, idx);
    };
    // SymPy sorts the solutions (algebraic numbers printed as CRootOf) by default_sort_key
    const tuples = sols.items.map((t) => (t as JsTuple).items.map(asRoot) as Expr[]);
    tuples.sort((a, b) => sj.compareKeys(sj.sortKey(sj.Basic(...a)), sj.sortKey(sj.Basic(...b))));
    return new JsList(tuples.map((t) => new JsTuple(t)));
  },
  substitution: (args, kw) => {
    noKw(kw);
    const exprs = (value: unknown): Expr[] => (value as JsTuple).items.map(asExpr);
    const eqs = exprs(args[0]);
    const syms = (args[1] as JsTuple).items.map(asSym);
    const results = args[2] instanceof JsTuple ? args[2].items.map((d) => new Map((d as JsDict).entries.map(([k, v]) => [asSym(k), asExpr(v)]))) : undefined;
    const known = args[3] instanceof JsTuple ? args[3].items.map(asSym) : undefined;
    const exclude = args[4] instanceof JsSet || args[4] instanceof JsTuple ? args[4].items.map(asExpr) : undefined;
    const all = args[5] instanceof JsTuple ? args[5].items.map(asSym) : undefined;
    const solutions = sj.substitution(eqs, syms, results, known, exclude, all);
    return solutions.length ? new JsSet(solutions.map((t) => new JsTuple(t))) : 'EmptySet';
  },
  nonlinsolve: (args, kw) => {
    noKw(kw);
    const eqs = (args[0] as JsTuple).items.map(asExpr);
    const syms = (args[1] as JsTuple).items.map(asSym);
    const sols = sj.nonlinsolve(eqs, syms);
    return sols.length ? new JsSet(sols.map((t) => new JsTuple(t))) : 'EmptySet';
  },
  solve_linear: (args, kw) => {
    const opts: { symbols?: Sym[]; exclude?: Sym[] } = {};
    if (kw['symbols']) opts.symbols = (kw['symbols'] as JsTuple).items.map(asSym);
    if (kw['exclude']) opts.exclude = (kw['exclude'] as JsTuple).items.map(asSym);
    if (args.length > 1) opts.symbols = args.slice(1).map(asSym);
    return new JsTuple(sj.solveLinear(asExpr(args[0]), opts));
  },
  solve_linear_system_LU: (args, kw) => ADAPTERS['solve_linear_system']!([args[0], ...(args[1] instanceof JsList || args[1] instanceof JsTuple ? args[1].items : args.slice(1))], kw),
  solve_linear_system: (args, kw) => {
    noKw(kw);
    const syms = args.slice(1).map(asSym);
    const s = solveAug(args[0] as Matrix, syms);
    // free variables (solved as themselves) are not listed, like SymPy
    return s ? new JsDict(syms.map((v, i) => [v, s[i]!] as const).filter(([v, e]) => v.key !== e.key)) : null;
  },
  solve_undetermined_coeffs: (args, kw) => {
    const dict = Boolean(kw['dict']);
    for (const k of Object.keys(kw)) if (k !== 'dict') throw new Unsupported(`kwargs ${k}`);
    const coeffs = (args[1] as JsTuple).items.map(asSym);
    const syms = args[2] === undefined ? [] : args[2] instanceof JsTuple ? args[2].items.map(asSym) : [asSym(args[2])];
    const sols = sj.solveUndeterminedCoeffs(asExpr(args[0]), coeffs, syms);
    const dicts = sols.map((t) => new JsDict(coeffs.map((v, i) => [v, t[i]!] as const)));
    if (dict) return new JsList(dicts);
    return dicts.length === 1 ? dicts[0] : new JsList(dicts);
  },
  nsolve: (args, kw) => {
    for (const k of Object.keys(kw)) if (!['prec', 'solver', 'verify'].includes(k)) throw new Unsupported(`kwargs ${k}`);
    const opts = kw['prec'] === undefined ? {} : { prec: Number((kw['prec'] as sj.Rational).p) };
    if (args[0] instanceof JsTuple && args[1] instanceof JsTuple && args[2] instanceof JsTuple) return sj.nsolve(args[0].items.map(asExpr), args[1].items.map(asSym), args[2].items.map(asExpr), opts);
    const e = asExpr(args[0]);
    const last = args[args.length - 1];
    if (last instanceof JsTuple && last.items.length === 2) {
      // an interval: bisection (solver='bisect')
      const xs = args.length === 3 ? asSym(args[1]) : ([...sj.freeSymbols(e)].filter((s) => s instanceof Sym)[0] as Sym);
      return sj.nsolve(e, xs, [asExpr(last.items[0]), asExpr(last.items[1])], { solver: 'bisect' });
    }
    if (args.length === 3) return sj.nsolve(e, asSym(args[1]), asExpr(args[2]), opts);
    const syms = [...sj.freeSymbols(e)].filter((s) => s instanceof Sym);
    if (syms.length !== 1) throw new Unsupported('nsolve form');
    return sj.nsolve(e, syms[0]!, asExpr(args[1]), opts);
  },
  Matrix: (args, kw) => {
    noKw(kw);
    const a = args[0];
    if (a instanceof Matrix) return a;
    if (a instanceof JsTuple && a.items.every((r) => r instanceof JsTuple)) {
      return Matrix.of(a.items.map((r) => (r as JsTuple).items.map((x) => (x instanceof Matrix ? x : asExpr(x)))));
    }
    if (a instanceof JsTuple) return Matrix.col(...a.items.map(asExpr));
    if (a === undefined) return Matrix.zeros(0, 0);
    if (a instanceof sj.Rational && args[1] instanceof sj.Rational && args[2] instanceof JsLambda) {
      const f = args[2];
      return Matrix.fromFunction(Number(a.p), Number(args[1].p), (i, j) => f.call(sj.Rational.of(i), sj.Rational.of(j)));
    }
    if (a instanceof sj.Rational && args[1] instanceof sj.Rational && args[2] instanceof JsTuple) {
      const r = Number(a.p);
      const c = Number(args[1].p);
      const items = (args[2] as JsTuple).items.map(asExpr);
      return Matrix.fromFunction(r, c, (i, j) => items[i * c + j]!);
    }
    throw new Unsupported('Matrix constructor');
  },
  // SymPy's sparse constructor forms: (rows, cols, dict | list | lambda), (None, data), a ragged list of rows
  SparseMatrix: (args, kw) => (noKw(kw), new sj.SparseMatrix(...(args.map((a) => toJs(a, true)) as sj.SparseMatrixArgs))),
  MutableSparseMatrix: (args, kw) => (noKw(kw), new sj.MutableSparseMatrix(...(args.map((a) => toJs(a, true)) as sj.SparseMatrixArgs))),
  ImmutableSparseMatrix: (args, kw) => (noKw(kw), new sj.ImmutableSparseMatrix(...(args.map((a) => toJs(a, true)) as sj.SparseMatrixArgs))),
  jordan_cell: (args, kw) => (noKw(kw), sj.jordanBlock(intArg(args[1]), asExpr(args[0]))),
  matrix_multiply_elementwise: (args, kw) => (noKw(kw), sj.multiplyElementwise(args[0] as Matrix, args[1] as Matrix)),
  '.diag': (args, kw, self) => {
    if (!(self instanceof TypeRef)) throw new Unsupported('diag on instance');
    return ADAPTERS['diag']!(args, kw);
  },
  '.hstack': (args, kw, self) => typeMethod(self, 'Matrix', () => (args[0] as Matrix).hstack(...(args.slice(1) as Matrix[])), kw),
  '.vstack': (args, kw, self) => typeMethod(self, 'Matrix', () => (args[0] as Matrix).vstack(...(args.slice(1) as Matrix[])), kw),
  '.jordan_block': (args, kw, self) => {
    if (!(self instanceof TypeRef)) throw new Unsupported('jordan_block');
    for (const k of Object.keys(kw)) if (!['size', 'eigenvalue', 'band'].includes(k)) throw new Unsupported(`kwargs ${k}`);
    const size = intArg(kw['size'] ?? args[0]);
    const ev = asExpr(kw['eigenvalue'] ?? args[1]);
    return sj.jordanBlock(size, ev, (kw['band'] as 'upper' | 'lower' | undefined) ?? 'upper');
  },
  '.companion': (args, kw, self) => typeMethod(self, 'Matrix', () => {
    const p = asPoly(args[0]);
    const m = p.monic();
    return sj.companion(m.allCoeffs());
  }, kw),
  '.from_dok': (args, kw, self) => typeMethod(self, 'Matrix', () => {
    const r = intArg(args[0]);
    const c = intArg(args[1]);
    const d = args[2] as JsDict;
    const m = new Map(d.entries.map(([k, v]) => [(k as JsTuple).items.map(intArg).join(','), asExpr(v)] as const));
    return Matrix.fromFunction(r, c, (i, j) => m.get(`${i},${j}`) ?? 0);
  }, kw),
  '.copy': matrixMethod((m) => m),
  '.flat': matrixMethod((m) => new JsList(m.data)),
  '.values': matrixMethod((m) => new JsList(m.data.filter((x) => !(x instanceof sj.Rational && x.isZero)))),
  '.is_symbolic': matrixMethod((m) => m.data.some((x) => sj.freeSymbols(x).size > 0)),
  '.hat': matrixMethod((m) => {
    const [a, b, c] = m.data as Expr[];
    return Matrix.of([[0, sj.mul(-1, c!), b!], [c!, 0, sj.mul(-1, a!)], [sj.mul(-1, b!), a!, 0]]);
  }),
  '.vee': matrixMethod((m) => Matrix.col(m.get(2, 1), m.get(0, 2), m.get(1, 0))),
  '.per': matrixMethod((m) => sj.permanent(m)),
  '.charpoly': matrixMethod((m, a) => {
    const lam = a[0] instanceof Sym ? a[0] : new Sym('lambda');
    return sj.Poly.from(m.charpoly(lam), [lam], { pure: true });
  }),
  '.todok': matrixMethod((m) => {
    const out: (readonly [unknown, unknown])[] = [];
    const [r, c] = m.shape;
    for (let i = 0; i < r; i++) for (let j = 0; j < c; j++) {
      const v = m.get(i, j);
      if (!(v instanceof sj.Rational && v.isZero)) out.push([new JsTuple([i, j]), v]);
    }
    return new JsDict(out);
  }),
  '.todod': matrixMethod((m) => {
    const out: (readonly [unknown, unknown])[] = [];
    const [r, c] = m.shape;
    for (let i = 0; i < r; i++) {
      const row: (readonly [unknown, unknown])[] = [];
      for (let j = 0; j < c; j++) {
        const v = m.get(i, j);
        if (!(v instanceof sj.Rational && v.isZero)) row.push([j, v]);
      }
      if (row.length) out.push([i, new JsDict(row)]);
    }
    return new JsDict(out);
  }),
  '.connected_components': matrixMethod((m) => new JsList(sj.connectedComponents(m).map((c) => new JsList(c)))),
  '.strongly_connected_components': matrixMethod((m) => new JsList(sj.stronglyConnectedComponents(m).map((c) => new JsList(c)))),
  '.condition_number': matrixMethod((m) => {
    const sv = sj.singularValues(m);
    return sj.mul(sj.Max(...sv), sj.pow(sj.Min(...sv), -1));
  }),
  '.left_eigenvects': matrixMethod((m) => new JsList(sj.eigenvects(m.transpose()).map(([v, k, vs]) => new JsTuple([v, k, new JsList(vs.map((x) => x.transpose()))])))),
  eye: (args, kw) => (noKw(kw), Matrix.eye(Number((args[0] as sj.Rational).p))),
  ones: (args, kw) => {
    noKw(kw);
    const [r, c] = args.map((a) => Number((a as sj.Rational).p));
    return Matrix.zeros(r!, c ?? r!).map(() => S.One);
  },
  '.eye': (args, kw) => ADAPTERS['eye']!(args, kw),
  '.zeros': (args, kw) => ADAPTERS['zeros']!(args, kw),
  '.ones': (args, kw) => ADAPTERS['ones']!(args, kw),
  GramSchmidt: (args, kw) => {
    noKw(kw);
    const vs = (args[0] as JsList).items as Matrix[];
    return new JsList(sj.GramSchmidt(vs, Boolean(args[1])));
  },
  hessian: (args, kw) => {
    noKw(kw);
    const vs = args[1] instanceof JsTuple || args[1] instanceof JsList ? args[1].items.map(asExpr) : args[1] instanceof Matrix ? args[1].data : [asExpr(args[1])];
    return sj.hessian(asExpr(args[0]), vs);
  },
  wronskian: (args, kw) => (noKw(kw), sj.wronskian((args[0] as JsList).items.map(asExpr), asExpr(args[1]))),
  casoratian: (args, kw) => {
    for (const k of Object.keys(kw)) if (k !== 'zero') throw new Unsupported(`kwargs ${k}`);
    return sj.casoratian((args[0] as JsList).items.map(asExpr), asExpr(args[1]), kw['zero'] === undefined ? true : Boolean(kw['zero']));
  },
  '.solve': matrixMethod((m, [b]) => sj.matrixSolve(m, b as Matrix)),
  '.LUsolve': matrixMethod((m, [b]) => sj.matrixSolve(m, b as Matrix)),
  '.QRsolve': matrixMethod((m, [b]) => sj.matrixSolve(m, b as Matrix)),
  '.LDLsolve': matrixMethod((m, [b]) => sj.matrixSolve(m, b as Matrix)),
  '.cholesky_solve': matrixMethod((m, [b]) => sj.matrixSolve(m, b as Matrix)),
  '.cramer_solve': matrixMethod((m, [b]) => sj.matrixSolve(m, b as Matrix)),
  '.upper_triangular_solve': matrixMethod((m, [b]) => sj.matrixSolve(m, b as Matrix)),
  '.lower_triangular_solve': matrixMethod((m, [b]) => sj.matrixSolve(m, b as Matrix)),
  '.diagonal_solve': matrixMethod((m, [b]) => sj.matrixSolve(m, b as Matrix)),
  '.gauss_jordan_solve': (_args, kw, self) => {
    const b = _args[0] as Matrix;
    return new JsTuple(kw['freevar'] === true ? sj.gaussJordanSolve(self as Matrix, b, { freevar: true }) : sj.gaussJordanSolve(self as Matrix, b));
  },
  '.solve_least_squares': matrixMethod((m, [b]) => sj.solveLeastSquares(m, b as Matrix)),
  '.normalized': matrixMethod((m) => sj.normalized(m)),
  '.multiply': matrixMethod((m, [b]) => m.mul(b as Matrix)),
  '.minorEntry': matrixMethod((m, [i, j]) => sj.linalg.minorDet(m, Number((i as sj.Rational).p), Number((j as sj.Rational).p))),
  '.minorMatrix': matrixMethod((m, [i, j]) => m.minor(Number((i as sj.Rational).p), Number((j as sj.Rational).p))),
  '.cofactorMatrix': matrixMethod((m) => m.cofactorMatrix()),
  '.inverse_GE': matrixMethod((m) => m.inv()),
  '.inverse_LU': matrixMethod((m) => m.inv()),
  '.inverse_ADJ': matrixMethod((m) => m.inv()),
  '.inverse_CH': matrixMethod((m) => m.inv()),
  '.inverse_LDL': matrixMethod((m) => m.inv()),
  '.inverse_QR': matrixMethod((m) => m.inv()),
  '.inverse_BLOCK': matrixMethod((m) => m.inv()),
  '.det_bareis': matrixMethod((m) => m.det()),
  '.det_LU_decomposition': matrixMethod((m) => m.det()),
  '.berkowitz_det': matrixMethod((m) => m.det()),
  '.berkowitz_charpoly': (args, kw, self) => ADAPTERS['.charpoly']!(args, kw, self),
  '.adjoint': (_args, kw, self) => (noKw(kw), self instanceof Matrix ? self.dagger() : sj.adjoint(asExpr(self))),
  zeros: (args, kw) => {
    noKw(kw);
    const [r, c] = args.map((a) => Number((a as sj.Rational).p));
    return Matrix.zeros(r!, c ?? r!);
  },
  diag: (args, kw) => {
    const unpack = Boolean(kw['unpack']);
    const blocks: (Matrix | Expr)[] = [];
    for (const a of args) {
      if (a instanceof Matrix) blocks.push(a);
      else if (a instanceof JsTuple) {
        if (unpack && args.length === 1) a.items.forEach((x) => blocks.push(asExpr(x)));
        else if (a.items.every((r) => r instanceof JsTuple)) {
          // SymPy pads ragged rows with zeros
          const rows = a.items.map((r) => (r as JsTuple).items.map(asExpr));
          const w = Math.max(...rows.map((r) => r.length));
          blocks.push(Matrix.of(rows.map((r) => [...r, ...Array.from({ length: w - r.length }, () => S.Zero)])));
        }
        else blocks.push(Matrix.col(...a.items.map(asExpr)));
      } else blocks.push(asExpr(a));
    }
    return sj.blockDiag(...blocks);
  },
  limit: (args, kw) => {
    const dir = (kw['dir'] as string | undefined) ?? (typeof args[3] === 'string' ? (args[3] as string) : '+');
    for (const k of Object.keys(kw)) if (k !== 'dir') throw new Unsupported(`kwargs ${k}`);
    return sj.limit(asExpr(args[0]), asSym(args[1]), asExpr(args[2]), dir as '+' | '-' | '+-');
  },
  Limit: (args, kw) => {
    const dir = (kw['dir'] as string | undefined) ?? '+';
    return new sj.Limit([asExpr(args[0]), asSym(args[1]), asExpr(args[2])], dir as '+' | '-' | '+-');
  },
  series: (args, kw) => {
    const x0 = kw['x0'] ?? args[2] ?? 0;
    const n = kw['n'] ?? args[3] ?? 6;
    const dir = (kw['dir'] ?? args[4] ?? '+') as '+' | '-';
    for (const k of Object.keys(kw)) if (!['x0', 'n', 'dir'].includes(k)) throw new Unsupported(`kwargs ${k}`);
    const e = asExpr(args[0]);
    const syms = [...sj.freeSymbols(e)].filter((s) => s instanceof Sym);
    const x = args[1] ? asSym(args[1]) : syms.length === 1 ? syms[0]! : undefined;
    if (!x) throw new Unsupported('series variable');
    return sj.series(e, x, asExpr(x0), Number((asExpr(n) as sj.Rational).p), dir);
  },
  O: (args, kw) => (noKw(kw), orderNode(asExpr(args[0]), args.slice(1))),
  Sum: (args, kw) => (noKw(kw), concreteNode('Sum', [asExpr(args[0]), ...args.slice(1)])),
  Product: (args, kw) => (noKw(kw), concreteNode('Product', [asExpr(args[0]), ...args.slice(1)])),
  summation: (args, kw) => (noKw(kw), concreteDoit(concreteNode('Sum', [asExpr(args[0]), ...args.slice(1)]))),
  product: (args, kw) => (noKw(kw), concreteDoit(concreteNode('Product', [asExpr(args[0]), ...args.slice(1)]))),
  '.reverse_order': (args, kw, self) => {
    noKw(kw);
    if (!(self instanceof sj.Concrete)) throw new Unsupported('reverse_order');
    return sj.reverseOrder(self, ...args.map((a) => (a instanceof Sym ? a : Number((a as sj.Rational).p))));
  },
  Order: (args, kw) => (noKw(kw), orderNode(asExpr(args[0]), args.slice(1))),
  Integral: (args, kw) => (noKw(kw), integralNode([asExpr(args[0]), ...args.slice(1)])),
  det: (args, kw) => {
    noKw(kw);
    if (!(args[0] instanceof Matrix)) throw new Unsupported('det');
    return args[0].det();
  },

  // ---- Expr methods
  '.expand': (args, kw, self) => {
    if (args.length) throw new Unsupported('expand args');
    return sj.expand(asExpr(self), expandHints(kw));
  },
  // Matrix.simplify() works in place in SymPy and returns None
  '.simplify': (_args, _kw, self) => (self instanceof Matrix ? null : sj.simplify(asExpr(self))),
  '.factor': exprMethod(sj.factor),
  '.together': exprMethod(sj.together),
  numer: exprFn((e) => sj.fraction(e)[0]),
  kroneckersimp: exprFn(sj.kroneckersimp),
  ratsimpmodprime: (args, kw) => {
    for (const k of Object.keys(kw)) if (k !== 'order' && k !== 'quick') throw new Unsupported(`kwargs ${k}`);
    const G = (args[1] as JsList).items.map(asExpr);
    const gens = args.slice(2).map(asSym);
    return sj.ratsimpmodprime(asExpr(args[0]), G, gens, { ...(kw['order'] ? { order: kw['order'] as 'lex' } : {}), ...(kw['quick'] === false ? { quick: false } : {}) });
  },
  '.aseries': (args, kw, self) => {
    for (const k of Object.keys(kw)) if (k !== 'n' && k !== 'hir') throw new Unsupported(`kwargs ${k}`);
    const x = args[0] === undefined ? ([...sj.freeSymbols(asExpr(self))][0] as Sym) : asSym(args[0]);
    const n = Number(((kw['n'] ?? args[2] ?? sj.Rational.of(6)) as sj.Rational).p);
    return sj.aseries(asExpr(self), x, n, Boolean(kw['hir']));
  },
  classify_ode: (args, kw) => {
    noKw(kw);
    const eq = asExpr(args[0]);
    let fx = args[1] === undefined ? undefined : asExpr(args[1]);
    if (!fx) {
      const found = new Map<string, Expr>();
      const walk = (e: Expr) => {
        if (e.kind === 'Undef') found.set(e.key, e);
        e.args.forEach(walk);
      };
      walk(eq);
      fx = [...found.values()][0];
    }
    return new JsTuple(sj.classifyOde(eq, fx as never));
  },
  line_integrate: (args, kw) => (noKw(kw), sj.lineIntegrate(asExpr(args[0]), args[1] as sj.Curve, (args[2] as JsList).items.map(asSym))),
  minimal_polynomial: (args, kw) => {
    for (const k of Object.keys(kw)) if (k !== 'polys' && k !== 'compose') throw new Unsupported(`kwargs ${k}`);
    const x = args[1] instanceof Sym ? args[1] : undefined;
    return sj.minimalPolynomial(asExpr(args[0]), x, { compose: kw['compose'] !== false, polys: Boolean(kw['polys']) });
  },
  KroneckerDelta: (args, kw) => (noKw(kw), sj.KroneckerDelta(asExpr(args[0]), asExpr(args[1]))),
  hyper: (args, kw) => {
    for (const k of Object.keys(kw)) if (k !== 'evaluate') throw new Unsupported(`kwargs ${k}`);
    return sj.hyper((args[0] as JsTuple).items.map(asExpr), (args[1] as JsTuple).items.map(asExpr), asExpr(args[2]), { evaluate: kw['evaluate'] !== false });
  },
  ...Object.fromEntries(ZETA_FAMILY_NAMES.map((n) => [n, ((args, kw) => (noKw(kw), sj.fn(n, args.map(asExpr)))) as Adapter])),
  jn: (args, kw) => (noKw(kw), sj.jn(asExpr(args[0]), asExpr(args[1]))),
  yn: (args, kw) => (noKw(kw), sj.yn(asExpr(args[0]), asExpr(args[1]))),
  denom: exprFn((e) => sj.fraction(e)[1]),
  ln: exprFn((e) => sj.log(e)),
  Rem: (args, kw) => (noKw(kw), sj.Rem(asExpr(args[0]), asExpr(args[1]))),
  '.as_powers_dict': (_a, kw, self) => (noKw(kw), new JsDefaultDict([...sj.asPowersDict(asExpr(self))])),
  '.as_coeff_exponent': (args, kw, self) => (noKw(kw), new JsTuple(sj.asCoeffExponent(asExpr(self), asExpr(args[0])))),
  '.as_coeff_Add': (_a, kw, self) => {
    noKw(kw);
    const e = asExpr(self);
    if (e instanceof sj.Add && e.args[0]!.isNumber) return new JsTuple([e.args[0]!, sj.add(...e.args.slice(1))]);
    return new JsTuple([e.isNumber ? e : S.Zero, e.isNumber ? S.Zero : e]);
  },
  '.count': (args, kw, self) => (noKw(kw), sj.Rational.of(sj.count(asExpr(self), asExpr(args[0])))),
  '.normal': exprMethod((e) => {
    const [n, d] = sj.fraction(sj.together(e));
    return sj.mul(n, sj.pow(d, -1));
  }),
  '.equals': (args, kw, self) => {
    noKw(kw);
    if (self instanceof Matrix) return (self as Matrix).equals(args[0] as Matrix);
    // SymPy PermutationGroup.equals: the same group, whatever its generators
    if (self instanceof sj.PermutationGroup) return self.equals(args[0] as sj.PermutationGroup);
    // SymPy GeometryEntity.equals: the same entity, whatever its representation
    if (self instanceof sj.GeometryEntity) return self.equals(args[0] as Expr);
    // SymPy Vector.equals: equal for all values of the symbols, in any coordinate system
    if (self instanceof sj.Vector) return self.equals(args[0] as Expr);
    if (self instanceof sj.BoolOp || self instanceof sj.AppliedPredicate || self instanceof sj.BoolAtom) return none(sj.booleanEquals(self, asExpr(args[0])));
    if (self instanceof sj.MatrixExpr) return none(self.equalsExplicit(args[0] instanceof Matrix ? sj.ImmutableMatrix(args[0]) : asExpr(args[0])));
    const d = sj.simplify(sj.sub(asExpr(self), asExpr(args[0])));
    return d instanceof sj.Rational && d.isZero ? true : d.isNumber ? false : null;
  },
  '.getO': (_a, kw, self) => {
    noKw(kw);
    const e = asExpr(self);
    const o = (e instanceof sj.Add ? e.args : [e]).find((t) => t instanceof sj.Order);
    return o ?? null;
  },
  '.apart': (args, kw, self) => ADAPTERS['apart']!([self, ...args], kw),
  '.collect': (args, kw, self) => ADAPTERS['collect']!([self, ...args], kw),
  '.nsimplify': (args, kw, self) => ADAPTERS['nsimplify']!([self, ...args], kw),
  '.powsimp': (args, kw, self) => ADAPTERS['powsimp']!([self, ...args], kw),
  '.radsimp': (args, kw, self) => ADAPTERS['radsimp']!([self, ...args], kw),
  '.ratsimp': (args, kw, self) => ADAPTERS['ratsimp']!([self, ...args], kw),
  '.cancel': (args, kw, self) => {
    if (!(self instanceof sj.Poly)) return exprMethod(sj.cancel)(args, kw, self);
    for (const k of Object.keys(kw)) if (k !== 'include') throw new Unsupported(`kwargs ${k}`);
    // SymPy Poly.cancel over ZZ: f/g = cp/cq * p/q
    const g = asPoly(args[0]);
    if (self.domain !== 'ZZ' || g.domain !== 'ZZ') throw new Unsupported('Poly.cancel over a field');
    const h = self.gcd(g);
    let P = self.exquo(h);
    let Q = g.exquo(h);
    let cp: Expr = S.One;
    const neg = (q: sj.Poly) => (q.LC() as sj.Rational).isNegative;
    if (neg(P) && neg(Q)) [P, Q] = [P.neg(), Q.neg()];
    else if (neg(P)) [cp, P] = [S.NegOne, P.neg()];
    else if (neg(Q)) [cp, Q] = [S.NegOne, Q.neg()];
    if (kw['include']) return new JsTuple([P.mul(sj.Poly.from(cp, P.gens)), Q]);
    return new JsTuple([cp, P, Q]);
  },
  '.trigsimp': exprMethod(sj.trigsimp),
  '.fdiff': (args, kw, self) => (noKw(kw), sj.fdiff(asExpr(self), args.length ? intArg(args[0]) : 1)),
  '.is_simple': (args, kw, self) => (noKw(kw), sj.isSimple(asExpr(self), asExpr(args[0]))),
  '.conjugate': exprMethod(sj.conjugate),
  '.subs': (args, kw, self0) => {
    // a SymPy Tuple substitutes like any expression
    const self = self0 instanceof JsTuple && !self0.isList ? sj.Tuple(...self0.items.map(asExpr)) : self0;
    const simultaneous = Boolean(kw['simultaneous']);
    for (const k of Object.keys(kw)) if (k !== 'simultaneous') throw new Unsupported(`kwargs ${k}`);
    if (simultaneous) {
      const a = args[0];
      const pairs = a instanceof JsDict ? a.entries : a instanceof JsTuple ? a.items.map((p) => (p as JsTuple).items) : undefined;
      if (!pairs) throw new Unsupported('subs simultaneous');
      return sj.subs(asExpr(self), pairs.map(([k, v]) => [asExpr(k), asExpr(v)] as const), { simultaneous: true });
    }
    if (self instanceof Matrix) {
      if (args.length !== 2) throw new Unsupported('Matrix.subs');
      return self.subs(asExpr(args[0]), asExpr(args[1]));
    }
    return subsArgs(asExpr(self), args);
  },
  '.diff': (args, kw, self) => {
    noKw(kw);
    if (self instanceof sj.Poly) {
      if (args.length && args.every((a) => a instanceof JsTuple)) {
        // Poly.diff((gen_index, order), ...)
        let p: sj.Poly = self;
        for (const a of args as JsTuple[]) {
          const gen = p.gens[Number((a.items[0] as sj.Rational).p)]!;
          for (let i = 0; i < Number((a.items[1] as sj.Rational).p); i++) p = p.diff(gen);
        }
        return p;
      }
      return self.diff(args[0] === undefined ? undefined : asExpr(args[0]));
    }
    if (self instanceof Matrix) {
      // SymPy MatrixBase.diff by a matrix or an array: ArrayDerivative, evaluated by derive_by_array
      if (args.length === 1 && (args[0] instanceof Matrix || args[0] instanceof sj.NDimArray)) return sj.deriveByArray(self, args[0]);
      return self.map((e) => diffArgs(e, args));
    }
    return diffArgs(asExpr(self), args);
  },
  '.integrate': (args, kw, self) =>
    self instanceof sj.Poly
      ? (() => {
          noKw(kw);
          if (!args.length) return self.integrate();
          let p: sj.Poly = self;
          for (const spec of args) {
            const [g, m] = spec instanceof JsTuple ? spec.items : [spec, 1];
            const gen = g instanceof sj.Rational ? p.gens[Number(g.p)]! : asExpr(g);
            for (let i = 0; i < Number(m instanceof sj.Rational ? m.p : m); i++) p = p.integrate(gen);
          }
          return p;
        })()
      : self instanceof Matrix ? self.map((e) => asExpr(ADAPTERS['integrate']!([e, ...args], kw))) : ADAPTERS['integrate']!([self, ...args], kw),
  '.series': (args, kw, self) => ADAPTERS['series']!([self, ...args], kw),
  '.limit': (args, kw, self) =>
    self instanceof Matrix ? self.map((e) => asExpr(ADAPTERS['limit']!([e, ...args], kw))) : ADAPTERS['limit']!([self, ...args], kw),
  '.removeO': exprMethod((e) => (e instanceof sj.Add ? sj.add(...e.args.filter((a) => !(a instanceof sj.Order))) : e instanceof sj.Order ? S.Zero : e)),
  '.doit': (args, kw, self) => {
    for (const k of Object.keys(kw)) if (k !== 'deep') throw new Unsupported(`kwargs ${k}`);
    if (args.length) throw new Unsupported('doit args');
    // the stats nodes evaluate with their own hints (SymPy Expectation.doit(deep=False)); a Density of a finite distribution is a dict
    if (self instanceof sj.Density) return fromJs(self.compute());
    if (self instanceof sj.ExpectationNode || self instanceof sj.ProbabilityNode) return self.doit({ deep: kw['deep'] === undefined ? true : Boolean(kw['deep']) });
    // SymPy MatrixBase.doit: the entries evaluated
    if (self instanceof Matrix && kw['deep'] === undefined) return sj.doit(self);
    const e = asExpr(self);
    // deep=False: only the top-level object is evaluated
    if (kw['deep'] === false && !(e instanceof sj.Integral || e instanceof sj.Derivative || e instanceof sj.Limit || e instanceof sj.Concrete || e instanceof sj.Subs)) return e;
    return sj.doit(e);
  },
  '.evalf': (args, kw, self) => evalfAdapter(self, args, kw),
  '.n': (args, kw, self) => evalfAdapter(self, args, kw),
  '.round': (args, kw, self) => {
    noKw(kw);
    return sj.round(asExpr(self), args.length ? intArg(args[0]) : undefined);
  },
  '.has': (args, kw, self) => {
    noKw(kw);
    const e = self instanceof Matrix ? self.data : [asExpr(self)];
    return args.some((a) =>
      a instanceof JsFunc
        ? false
        : a instanceof FnClass || a instanceof TypeRef || a instanceof UFnClass
        ? e.some((x) => sj.find(x, toQuery(a)).length > 0)
        : e.some((x) => x.has(asExpr(a))),
    );
  },
  '.match': (args, kw, self) => {
    for (const k of Object.keys(kw)) if (k !== 'old') throw new Unsupported(`kwargs ${k}`);
    return matchDict(sj.match(asExpr(self), asExpr(args[0]), { old: Boolean(kw['old']) }));
  },
  '.replace': (args, kw, self) => {
    if (self instanceof sj.Poly) return (noKw(kw), self.replace(asExpr(args[0]), asExpr(args[1])));
    for (const k of Object.keys(kw)) if (!['exact', 'map'].includes(k)) throw new Unsupported(`kwargs ${k}`);
    const q = toQuery(args[0]);
    const v = args[1];
    let value: sj.Replacement;
    if (v instanceof JsLambda) {
      if (q instanceof Expr) {
        // keyword call by Wild name, values arrive ordered like the Wilds of the pattern
        const ws: sj.Wild[] = [];
        const walk = (e: Expr) => {
          if (e instanceof sj.Wild && !ws.some((w) => w.key === e.key)) ws.push(e);
          e.args.forEach(walk);
        };
        walk(q);
        value = (...vals: Expr[]) =>
          v.call(...v.vars.map((p) => vals[ws.findIndex((w) => w.name === (p as Sym).name)] ?? S.Zero));
      } else value = (...vals: Expr[]) => v.call(...vals);
    } else value = v instanceof FnClass || v instanceof UFnClass ? { fn: v.name } : v instanceof TypeRef ? { type: v.name } : asExpr(v);
    if (self instanceof Matrix) return self.replace(q, value, { exact: kw['exact'] === undefined ? undefined : Boolean(kw['exact']), apply: applyFn });
    const r = sj.replace(asExpr(self), q, value, {
      exact: kw['exact'] === undefined ? undefined : Boolean(kw['exact']),
      map: Boolean(kw['map']),
      apply: applyFn,
    });
    if (Array.isArray(r)) return new JsTuple([r[0], new JsDict([...r[1]])]);
    return r;
  },
  gcd_terms: (args, kw) => {
    for (const k of Object.keys(kw)) if (!['clear', 'fraction', 'isprimitive'].includes(k)) throw new Unsupported(`kwargs ${k}`);
    return sj.gcdTerms(asExpr(args[0]), { clear: kw['clear'] as boolean | undefined, fraction: kw['fraction'] as boolean | undefined, isprimitive: kw['isprimitive'] as boolean | undefined });
  },
  factor_terms: (args, kw) => {
    for (const k of Object.keys(kw)) if (!['clear', 'fraction', 'sign', 'radical'].includes(k)) throw new Unsupported(`kwargs ${k}`);
    if (kw['radical']) throw new Unsupported('radical');
    return sj.factorTerms(asExpr(args[0]), { clear: kw['clear'] as boolean | undefined, fraction: kw['fraction'] as boolean | undefined, sign: kw['sign'] as boolean | undefined });
  },
  collect_const: (args, kw) => {
    for (const k of Object.keys(kw)) if (k !== 'Numbers') throw new Unsupported(`kwargs ${k}`);
    return sj.collectConst(asExpr(args[0]), args.slice(1).map(asExpr), { numbers: kw['Numbers'] === undefined ? true : Boolean(kw['Numbers']) });
  },
  signsimp: (args, kw) => {
    for (const k of Object.keys(kw)) if (k !== 'evaluate') throw new Unsupported(`kwargs ${k}`);
    return sj.signsimp(asExpr(args[0]), kw['evaluate'] === undefined ? true : Boolean(kw['evaluate']));
  },
  '.rewrite': (args, kw, self) => {
    for (const k of Object.keys(kw)) if (k !== 'deep') throw new Unsupported(`kwargs ${k}`);
    const name = (v: unknown): string => {
      if (v instanceof FnClass || v instanceof UFnClass || v instanceof TypeRef) return v.name;
      // a target that SymPy defines as a function (sqrt) rather than a class
      if (v instanceof JsFunc) return v.name.replace(/^.*\./, '');
      if (typeof v === 'string') return v;
      throw new Unsupported('rewrite target');
    };
    if (!args.length) return asExpr(self);
    const target = name(args[args.length - 1]);
    let pattern = args.slice(0, -1);
    if (pattern.length === 1 && (pattern[0] instanceof JsList || pattern[0] instanceof JsTuple)) pattern = [...(pattern[0] as JsList).items];
    return sj.rewrite(asExpr(self), target, { pattern: pattern.map(name), deep: kw['deep'] === undefined ? true : Boolean(kw['deep']) });
  },
  '.find': (args, kw, self) => {
    noKw(kw);
    return new JsSet(sj.find(asExpr(self), toQuery(args[0])));
  },
  count_ops: (args, kw) => {
    for (const k of Object.keys(kw)) if (k !== 'visual') throw new Unsupported(`kwargs ${k}`);
    const visual = Boolean(kw['visual'] ?? args[1]);
    if (args[0] instanceof JsDict) return ADAPTERS['count_ops']!([new JsList(args[0].entries.flat())], kw);
    if (args[0] instanceof JsList || args[0] instanceof JsTuple) {
      // None and booleans count as nothing
      const items = (args[0] as JsList).items.filter((i) => i !== null && typeof i !== 'boolean').map(asExpr);
      return visual ? sj.add(...items.map(sj.countOpsVisual)) : items.reduce((n, e) => n + sj.countOps(e), 0);
    }
    return visual ? sj.countOpsVisual(asExpr(args[0])) : sj.countOps(asExpr(args[0]));
  },
  '.count_ops': (args, kw, self) => ADAPTERS['count_ops']!([self, ...args], kw),

  '.coeff': (args, kw, self) => {
    for (const k of Object.keys(kw)) if (k !== 'right') throw new Unsupported(`kwargs ${k}`);
    // the term of a sequence at a point (SymPy SeqBase.coeff)
    if (self instanceof sj.SeqBase) return self.coeff(asExpr(args[0]));
    const n = args[1] instanceof sj.Rational ? Number(args[1].p) : 1;
    const r = kw['right'];
    return sj.coeff(asExpr(self), asExpr(args[0]), n, r === true || (r instanceof sj.Rational && !r.isZero));
  },
  '.as_independent': (args, kw, self) => {
    const asAdd = kw['as_Add'];
    for (const k of Object.keys(kw)) if (k !== 'as_Add') throw new Unsupported(`kwargs ${k}`);
    const opts = asAdd === undefined ? {} : { asAdd: Boolean(asAdd) };
    return new JsTuple(sj.asIndependent(asExpr(self), args.map(asExpr), opts));
  },
  '.as_coeff_add': (args, kw, self) => {
    noKw(kw);
    const [c, t] = sj.asCoeffAdd(asExpr(self), args.map(asExpr));
    return new JsTuple([c, new JsTuple(t)]);
  },
  '.as_coeff_mul': (args, kw, self) => {
    noKw(kw);
    const [c, t] = sj.asCoeffMul(asExpr(self), args.map(asExpr));
    return new JsTuple([c, new JsTuple(t)]);
  },
  '.as_coeff_Mul': exprMethod((e) => new JsTuple(sj.splitCoeff(e))),
  '.primitive': (_a, kw, self) => {
    noKw(kw);
    if (self instanceof sj.Poly) return new JsTuple(self.primitive());
    return new JsTuple(sj.primitive(asExpr(self)));
  },
  '.degree': (args, kw, self) => {
    noKw(kw);
    return asPoly(self).degree(args[0] === undefined ? undefined : asExpr(args[0]));
  },
  '.as_content_primitive': (args, kw, self) => {
    const clear = kw['clear'];
    for (const k of Object.keys(kw)) if (k !== 'clear' && k !== 'radical') throw new Unsupported(`kwargs ${k}`);
    if (args.length) throw new Unsupported('arity');
    return new JsTuple(sj.asContentPrimitive(asExpr(self), { ...(clear === undefined ? {} : { clear: Boolean(clear) }), radical: Boolean(kw['radical']) }));
  },
  '.extract_multiplicatively': (args, kw, self) => (noKw(kw), none(sj.extractMultiplicatively(asExpr(self), asExpr(args[0])))),
  '.extract_additively': (args, kw, self) => (noKw(kw), none(sj.extractAdditively(asExpr(self), asExpr(args[0])))),
  '.as_coefficient': (args, kw, self) => (noKw(kw), none(sj.asCoefficient(asExpr(self), asExpr(args[0])))),
  '.is_polynomial': (args, kw, self) => (noKw(kw), sj.isPolynomial(asExpr(self), args.map(asExpr))),
  '.is_rational_function': (args, kw, self) => (noKw(kw), sj.isRationalFunction(asExpr(self), args.map(asExpr))),
  '.is_constant': (args, kw, self) => {
    noKw(kw);
    return sj.isConstant(asExpr(self), args.map(asSym));
  },
  '.as_real_imag': exprMethod((e) => new JsTuple(sj.asRealImag(e))),
  '.as_numer_denom': exprMethod((e) => new JsTuple(sj.asNumerDenom(e))),
  '.as_base_exp': exprMethod((e) => {
    // SymPy Pow.as_base_exp: (1/q)**e is reported as q**(-e)
    if (e instanceof sj.Pow && e.base instanceof sj.Rational && e.base.p === 1n && e.base.q !== 1n) return new JsTuple([sj.Rational.of(e.base.q), sj.neg(e.exp)]);
    return new JsTuple(sj.asBaseExp(e));
  }),
  '.args_cnc': (args, kw, self) => {
    const split1 = kw['split_1'];
    for (const k of Object.keys(kw)) if (k !== 'split_1' && k !== 'cset') throw new Unsupported(`kwargs ${k}`);
    if (args.length) throw new Unsupported('arity');
    const [c, nc] = sj.argsCncSplit(asExpr(self), split1 === undefined ? true : Boolean(split1));
    return new JsList([kw['cset'] ? new JsSet(c) : new JsList(c), new JsList(nc)]);
  },
  '.xreplace': (args, kw, self) => {
    noKw(kw);
    const d = args[0];
    if (!(d instanceof JsDict)) throw new Unsupported('xreplace mapping');
    const reps = d.entries.map(([k, v]) => [asExpr(k), asExpr(v)] as const);
    if (self instanceof JsTuple) return new JsTuple(self.items.map((e) => sj.xreplace(asExpr(e), reps)));
    return sj.xreplace(asExpr(self), reps);
  },
  '.atoms': (args, kw, self) => {
    noKw(kw);
    if (self instanceof sj.Permutation) return new JsSet([...self.atoms()].map((i) => sj.Rational.of(BigInt(i))));
    const preds = args.map((a) => {
      if (a instanceof FnClass || a instanceof TypeRef || a instanceof UFnClass) {
        const q = toQuery(a);
        return (x: Expr) => ('fn' in (q as object) ? sj.find(x, q).some((y) => y.key === x.key) : sj.isInstance(x, (q as { type: string }).type));
      }
      const t = asExpr(a);
      if (t instanceof Sym) return (x: Expr) => x instanceof Sym;
      if (t instanceof sj.Rational && t.isOne) return (x: Expr) => x instanceof sj.Rational && x.isOne;
      if (t instanceof sj.Rational && t.isInteger) return (x: Expr) => x instanceof sj.Rational && x.isInteger;
      if (t instanceof sj.Rational) return (x: Expr) => x instanceof sj.Rational;
      return (x: Expr) => x.key === t.key;
    });
    const pred = preds.length ? (x: Expr) => preds.some((p) => p(x)) : () => true;
    if (args.some((a) => a instanceof FnClass || a instanceof TypeRef || a instanceof UFnClass)) {
      return new JsSet(sj.find(asExpr(self), pred));
    }
    return new JsSet(sj.atoms(asExpr(self), pred));
  },
  '.as_ordered_terms': (args, kw, self) => {
    noKw(kw);
    // with a monomial ordering ('lex', 'rev-lex', 'grlex', ...)
    if (args.length) return new JsList(sj.asOrderedTerms(asExpr(self), args[0] as sj.TermOrder));
    return exprMethod((e) => new JsList(e instanceof sj.Add ? asOrdered(e) : [e]))(args, kw, self);
  },

  // ---- ODEs
  rsolve_poly: (args, kw) => (noKw(kw), first0(sj.rsolvePoly((args[0] as JsTuple).items.map(asExpr), asExpr(args[1]), asSym(args[2])))),
  rsolve_ratio: (args, kw) => (noKw(kw), first0(sj.rsolveRatio((args[0] as JsTuple).items.map(asExpr), asExpr(args[1]), asSym(args[2])))),
  rsolve_hyper: (args, kw) => (noKw(kw), first0(sj.rsolveHyper((args[0] as JsTuple).items.map(asExpr), asExpr(args[1]), asSym(args[2])))),
  rsolve: (args, kw) => {
    noKw(kw);
    const init = args[2];
    const pairs =
      init instanceof JsDict
        ? init.entries.map(([k, v]) => [asExpr(k), asExpr(v)] as [Expr, Expr])
        : init instanceof JsTuple
          ? init.items.map((v, i) => [sj.sympify(i), asExpr(v)] as [Expr, Expr])
          : undefined;
    return none(sj.rsolve(asExpr(args[0]), asExpr(args[1]), pairs));
  },
  adjoint: (args, kw) => (noKw(kw), args[0] instanceof Matrix ? args[0].dagger() : sj.adjoint(asExpr(args[0]))),
  transpose: (args, kw) => (noKw(kw), args[0] instanceof Matrix ? args[0].transpose() : sj.transpose(asExpr(args[0]))),
  homogeneous_order: (args, kw) => (noKw(kw), none(sj.homogeneousOrder(asExpr(args[0]), ...args.slice(1).map(asExpr)))),
  dsolve: (args, kw) => {
    for (const k of Object.keys(kw)) if (k !== 'ics' && k !== 'hint') throw new Unsupported(`kwargs ${k}`);
    const ics = kw['ics'] instanceof JsDict ? (kw['ics'] as JsDict).entries.map(([k, v]) => [asExpr(k), asExpr(v)] as [Expr, Expr]) : undefined;
    if (args[0] instanceof JsTuple || args[0] instanceof JsList) {
      // a system of ODEs
      const fs = args[1] instanceof JsTuple || args[1] instanceof JsList ? args[1].items.map(asExpr) : undefined;
      return new JsList(sj.dsolve(args[0].items.map(asExpr), fs) as Expr[]);
    }
    const hint = kw['hint'] === undefined ? undefined : String(kw['hint']);
    const r = sj.dsolve(asExpr(args[0]), args[1] === undefined ? undefined : asExpr(args[1]), { ...(ics ? { ics } : {}), ...(hint ? { hint } : {}) });
    return Array.isArray(r) ? new JsList(r) : r;
  },

  // ---- polynomials
  dict_from_expr: (args, kw) => {
    for (const k of Object.keys(kw)) if (k !== 'gens') throw new Unsupported(`kwargs ${k}`);
    const gens = kw['gens'] ?? args[1];
    const p = sj.Poly.from(asExpr(args[0]), gens === undefined ? undefined : gens instanceof JsTuple ? gens.items.map(asExpr) : [asExpr(gens)]);
    return new JsTuple([new JsDict(p.asDict().map(([m, c]) => [new JsTuple(m), c])), new JsTuple([...p.gens])]);
  },
  solve_lin_sys: (args, kw) => {
    for (const k of Object.keys(kw)) if (k !== '_raw') throw new Unsupported(`kwargs ${k}`);
    const K = args[1] as JsDomain;
    const eqs = toJs(args[0], false) as sj.PolyElement[];
    // PolyRing retains nested coefficient fields; the older PolynomialRing
    // domain wrapper flattens them, so reconstruct from the serialized domain.
    const tree = K.definition;
    if (!tree?.['base'] || !tree['symbols']) throw new Unsupported('polynomial ring domain');
    const domain = deserializeDomain(tree['base'] as Tree);
    if (!domain) throw new Unsupported('polynomial coefficient domain');
    const ring = new sj.PolyRing((tree['symbols'] as Tree[]).map((g) => asExpr(deserialize(g))), domain, String(tree['order'] ?? 'lex'));
    const result = sj.solveLinSys(eqs,ring);
    if (sj.isNoMatch(result)) return null;
    // Convert only the low-level coefficient representation expected by Python.
    return new JsDict([...result].map(([k,v]) => [k,kw['_raw'] === false || [...v.freeSymbols()].some((s) => ring.symbols.some((g) => g.key === s.key)) ? v : ring.domain.convert(v)]));
  },
  Poly: (args, kw) => {
    for (const k of Object.keys(kw)) if (!['domain','modulus','extension','gaussian','field'].includes(k)) throw new Unsupported(`kwargs ${k}`);
    const [e, ...gens] = args;
    const extension = kw['extension'];
    if (e instanceof JsList || e instanceof JsTuple) return sj.Poly.fromList(e.items.map((v) => v instanceof sj.PythonMPQ ? sj.QQ.toSympy(v) : asExpr(v)), gens.map(asExpr), polynomialOptions(kw));
    return sj.Poly.from(asExprOrPoly(e), gens.map(asExpr), {
      ...polynomialOptions(kw),
      ...(extension === undefined ? {} : { extension: typeof extension === 'boolean' ? extension : extension instanceof JsTuple ? extension.items.map(asExpr) : asExpr(extension) }),
      ...(kw['gaussian'] === undefined ? {} : { gaussian: Boolean(kw['gaussian']) }),
      ...(kw['field'] === undefined ? {} : { field: Boolean(kw['field']) }),
    });
  },
  degree: (args, kw) => {
    for (const k of Object.keys(kw)) if (k !== 'gen') throw new Unsupported(`kwargs ${k}`);
    const f = args[0] instanceof sj.Poly ? args[0] : asExpr(args[0]);
    const gen = kw['gen'] ?? args[1];
    return sj.degree(f, gen === undefined ? undefined : asExpr(gen));
  },
  total_degree: (args, kw) => {
    noKw(kw);
    const gens = args.slice(1).map(asExpr);
    if (args[0] instanceof sj.Poly && !gens.length) return args[0].totalDegree();
    return sj.Poly.from(asExprOrPoly(args[0]), gens).totalDegree();
  },
  LC: (args, kw) => (noKw(kw), polyOf(args).LC()),
  LM: (args, kw) => (noKw(kw), polyOf(args).LM()),
  LT: (args, kw) => {
    noKw(kw);
    const p = polyOf(args);
    return sj.mul(p.LC(), p.LM());
  },
  gcd: (args, kw) => {
    for (const k of Object.keys(kw)) if (!['domain','modulus','extension'].includes(k)) throw new Unsupported(`kwargs ${k}`);
    if (args.length !== 2) throw new Unsupported('gcd arity');
    const a = args[0] instanceof sj.Poly ? args[0] : asExpr(args[0]), b = args[1] instanceof sj.Poly ? args[1] : asExpr(args[1]);
    const opts = polynomialOptions(kw), r = sj.gcd(a, b, opts);
    if (!(a instanceof sj.Poly)) return r;
    const outputOpts = Object.keys(opts).length ? opts : b instanceof sj.Poly && a.domain === b.domain ? { domain: a.domain } : {};
    return sj.Poly.from(r, a.gens, outputOpts);
  },
  lcm: (args, kw) => {
    for (const k of Object.keys(kw)) if (!['domain','modulus','extension'].includes(k)) throw new Unsupported(`kwargs ${k}`);
    if (args.length !== 2) throw new Unsupported('lcm arity');
    const a = args[0] instanceof sj.Poly ? args[0] : asExpr(args[0]), b = args[1] instanceof sj.Poly ? args[1] : asExpr(args[1]);
    const opts = polynomialOptions(kw), r = sj.lcm(a, b, opts);
    if (!(a instanceof sj.Poly)) return r;
    const outputOpts = Object.keys(opts).length ? opts : b instanceof sj.Poly && a.domain === b.domain ? { domain: a.domain } : {};
    return sj.Poly.from(r, a.gens, outputOpts);
  },
  div: (args, kw) => {
    for (const k of Object.keys(kw)) if (k !== 'domain') throw new Unsupported(`kwargs ${k}`);
    if (kw['domain'] instanceof JsDomain && kw['domain'].name === 'ZZ') return new JsTuple(divOverZZ(asExpr(args[0]), asExpr(args[1])));
    if (args[0] instanceof sj.Poly) return new JsTuple(args[0].div(args[1] as sj.Poly));
    return new JsTuple(sj.polyDiv(asExpr(args[0]), asExpr(args[1])));
  },
  rem: (args, kw) => {
    if (kw['domain'] === undefined) return polyFn(2, ([f, g]) => asPoly(f).rem(asPoly(g)))(args, kw);
    for (const k of Object.keys(kw)) if (k !== 'domain') throw new Unsupported(`kwargs ${k}`);
    if (kw['domain'] instanceof JsDomain && kw['domain'].name === 'ZZ') return divOverZZ(asExpr(args[0]), asExpr(args[1]))[1];
    return args[0] instanceof sj.Poly ? args[0].rem(args[1] as sj.Poly) : sj.polyDiv(asExpr(args[0]), asExpr(args[1]))[1];
  },
  quo: polyFn(2, ([f, g]) => asPoly(f).quo(asPoly(g))),
  factor_list: (args, kw) => {
    for (const k of Object.keys(kw)) if (k !== 'frac') throw new Unsupported(`kwargs ${k}`);
    const gens = args.slice(1).map(asExpr);
    const pairs = (fs: [sj.Expr, sj.Expr][]): JsList => new JsList(fs.map(([f, k]) => new JsTuple([f, k])));
    if (kw['frac'] === true) {
      const [c, fp, fq] = sj.factorList(asExprOrPoly(args[0]), gens, { frac: true });
      return new JsTuple([c, pairs(fp), pairs(fq)]);
    }
    const [c, fs] = sj.factorList(asExprOrPoly(args[0]), gens);
    return new JsTuple([c, pairs(fs)]);
  },
  terms_gcd: (args, kw) => {
    const opts: { expand?: boolean; deep?: boolean; clear?: boolean } = {};
    for (const k of Object.keys(kw)) {
      if (k !== 'expand' && k !== 'deep' && k !== 'clear') throw new Unsupported(`kwargs ${k}`);
      opts[k] = kw[k] === true;
    }
    return sj.termsGcd(asExpr(args[0]), ...args.slice(1).map(asSym), opts);
  },
  horner: (args, kw) => {
    for (const k of Object.keys(kw)) if (k !== 'wrt') throw new Unsupported(`kwargs ${k}`);
    const wrt = kw['wrt'] ?? args[1];
    return sj.horner(asExpr(args[0]), wrt ? asSym(wrt) : undefined);
  },
  interpolate: (args, kw) => {
    noKw(kw);
    const data = args[0];
    const pts =
      data instanceof JsDict
        ? data.entries.map(([k, v]) => [asExpr(k), asExpr(v)] as const)
        : (data as JsTuple).items.map((d) => (d instanceof JsTuple ? ([asExpr(d.items[0]), asExpr(d.items[1])] as const) : asExpr(d)));
    const at = asExpr(args[1]);
    if (at instanceof Sym) return sj.interpolate(pts as never, at);
    const t = new sj.Dummy('x');
    return sj.xreplace(sj.interpolate(pts as never, t), [[t, at]]);
  },
  resultant: (args, kw) => {
    noKw(kw);
    const f = asExprOrPoly(args[0]);
    const g = asExprOrPoly(args[1]);
    const x = args[2] ? asSym(args[2]) : (sj.sortGens([...sj.freeSymbols(f), ...sj.freeSymbols(g)])[0] as Sym);
    return sj.resultant(f, g, x);
  },
  discriminant: (args, kw) => {
    noKw(kw);
    const f = asExprOrPoly(args[0]);
    const x = args[1] ? asSym(args[1]) : (sj.sortGens([...sj.freeSymbols(f)])[0] as Sym);
    return sj.discriminant(f, x);
  },
  '.as_expr': (args, kw, self) => {
    noKw(kw);
    if (self instanceof sj.Poly) {
      if (!args.length) return self.asExpr();
      if (args[0] instanceof JsDict) return self.asExprAt(args[0].entries.map(([k, v]) => [asExpr(k), asExpr(v)] as const));
      return self.asExprAt(args.map(asExpr));
    }
    if (self instanceof Expr) return self;
    if (self instanceof sj.AlgebraicNumber) return self.asExpr();
    throw new Unsupported('as_expr');
  },
  '.total_degree': (_a, kw, self) => (noKw(kw), asPoly(self).totalDegree()),
  '.LC': (_a, kw, self) => (noKw(kw), asPoly(self).LC()),
  // Poly.LT()/ET(): (Monomial, coefficient) of the leading/trailing term
  '.LT': (_a, kw, self) => {
    noKw(kw);
    const p = asPoly(self);
    const [m, c] = p.LT();
    return new JsTuple([new sj.Monomial(m, p.gens), c]);
  },
  '.ET': (_a, kw, self) => {
    noKw(kw);
    const p = asPoly(self);
    const [m, c] = p.terms().at(-1)!;
    return new JsTuple([new sj.Monomial(m, p.gens), c]);
  },
  '.coeffs': (_a, kw, self) => (noKw(kw), new JsList(self instanceof sj.AlgebraicNumber ? self.coeffs() : asPoly(self).coeffs())),
  '.to_root': (_a, kw, self) => {
    noKw(kw);
    if (!(self instanceof sj.AlgebraicNumber)) throw new Unsupported('to_root');
    return self.toRoot();
  },
  '.primitive_element': (_a, kw, self) => {
    noKw(kw);
    if (!(self instanceof sj.AlgebraicNumber)) throw new Unsupported('primitive_element');
    return self.primitiveElement();
  },
  '.all_coeffs': (_a, kw, self) => (noKw(kw), new JsList(asPoly(self).allCoeffs())),
  '.monoms': (_a, kw, self) => (noKw(kw), new JsList(asPoly(self).monoms().map((m) => new JsTuple(m)))),
  '.terms': (_a, kw, self) => (noKw(kw), new JsList(asPoly(self).terms().map(([m, c]) => new JsTuple([new JsTuple(m), c])))),
  '.coeff_monomial': (args, kw, self) => {
    noKw(kw);
    const p = asPoly(self);
    const m = args[0];
    if (m instanceof JsTuple) return p.coeffMonomial(m.items.map((x) => Number((x as sj.Rational).p)));
    const mono = sj.Poly.from(asExpr(m), p.gens);
    return p.coeffMonomial(mono.monoms()[0]!);
  },
  '.eval': (args, kw, self) => {
    noKw(kw);
    const p = asPoly(self);
    if (args[0] instanceof JsDict) return p.evalMany(args[0].entries.map(([k, v]) => [asExpr(k), asExpr(v)] as const));
    if (args[0] instanceof JsTuple) return p.evalMany(args[0].items.map((v, i) => [p.gens[i]!, asExpr(v)] as const));
    if (args.length === 1) return p.eval(asExpr(args[0]));
    return p.eval(asExpr(args[1]), asExpr(args[0]));
  },
  '.monic': (_a, kw, self) => (noKw(kw), asPoly(self).monic()),
  '.gcd': (args, kw, self) => (noKw(kw), asPoly(self).gcd(args[0] as sj.Poly)),
  '.lcm': (args, kw, self) => (noKw(kw), asPoly(self).lcm(args[0] as sj.Poly)),
  '.div': (args, kw, self) => new JsTuple(asPoly(self).divAuto(args[0] as sj.Poly, autoKw(kw))),
  '.rem': (args, kw, self) => asPoly(self).rem(args[0] as sj.Poly, autoKw(kw)),
  '.quo': (args, kw, self) => asPoly(self).quo(args[0] as sj.Poly, autoKw(kw)),
  '.abs': polyM((p) => p.abs()),
  '.neg': polyM((p) => p.neg()),
  '.sqr': polyM((p) => p.sqr()),
  '.add': polyM((p, a) => p.add(polyArg(a[0]))),
  '.sub': polyM((p, a) => p.sub(polyArg(a[0]))),
  '.mul': polyM((p, a) => p.mul(polyArg(a[0]))),
  '.pow': polyM((p, a) => p.pow(intArg(a[0]))),
  '.add_ground': polyM((p, a) => p.addGround(asExpr(a[0]))),
  '.sub_ground': polyM((p, a) => p.subGround(asExpr(a[0]))),
  '.mul_ground': polyM((p, a) => p.mulGround(asExpr(a[0]))),
  '.quo_ground': polyM((p, a) => p.quoGround(asExpr(a[0]))),
  '.exquo_ground': polyM((p, a) => p.exquoGround(asExpr(a[0]))),
  '.all_monoms': polyM((p) => new JsList(p.allMonoms().map((m) => new JsTuple(m)))),
  '.all_terms': polyM((p) => new JsList(p.allTerms().map(([m, c]) => new JsTuple([new JsTuple(m), c])))),
  '.as_dict': polyM((p) => new JsDict(p.asDict().map(([m, c]) => [new JsTuple(m), c] as const))),
  '.cofactors': polyM((p, a) => new JsTuple(p.cofactors(a[0] as sj.Poly))),
  '.compose': polyM((p, a) => p.compose(a[0] as sj.Poly)),
  '.degree_list': polyM((p) => new JsTuple(p.degreeList())),
  '.discriminant': polyM((p) => p.discriminant()),
  '.resultant': (args, kw, self) => {
    for (const k of Object.keys(kw)) if (k !== 'includePRS') throw new Unsupported(`kwargs ${k}`);
    const p = asPoly(self);
    const q = args[0] as sj.Poly;
    if (kw['includePRS']) return new JsTuple([p.resultant(q), new JsList(p.subresultants(q))]);
    return p.resultant(q);
  },
  '.make_monic_over_integers_by_scaling_roots': polyM((p) => new JsTuple(p.makeMonicOverIntegersByScalingRoots())),
  sqf_norm: (args, kw) => {
    for (const k of Object.keys(kw)) if (k !== 'extension') throw new Unsupported(`kwargs ${k}`);
    const e = asExpr(args[0]);
    const x = args[1] instanceof Sym ? args[1] : ([...sj.freeSymbols(e)].filter((s) => s instanceof Sym)[0] as Sym);
    const ext = kw['extension'] instanceof JsList || kw['extension'] instanceof JsTuple ? (kw['extension'] as JsList).items.map(asExpr) : [asExpr(kw['extension'])];
    const [s, g, r] = sj.sqfNorm(e, x, ext);
    return new JsTuple([new JsList(s.map((k) => sj.Rational.of(k))), g, r]);
  },
  '.EC': polyM((p) => p.EC()),
  '.TC': polyM((p) => p.TC()),
  '.nth': polyM((p, a) => p.nth(...a.map(intArg))),
  '.length': polyM((p) => p.length()),
  '.l1_norm': polyM((p) => p.l1Norm()),
  '.max_norm': polyM((p) => p.maxNorm()),
  '.exclude': polyM((p) => p.exclude()),
  '.has_only_gens': polyM((p, a) => p.hasOnlyGens(...a.map(asExpr))),
  '.homogeneous_order': polyM((p) => none(p.homogeneousOrder())),
  '.homogenize': polyM((p, a) => p.homogenize(asExpr(a[0]))),
  '.ltrim': polyM((p, a) => p.ltrim(a[0] instanceof sj.Rational ? Number(a[0].p) : asExpr(a[0]))),
  '.reorder': polyM((p, a) => p.reorder(...a.map(asExpr))),
  '.pdiv': polyM((p, a) => new JsTuple(p.pdiv(a[0] as sj.Poly))),
  '.pexquo': polyM((p, a) => p.pexquo(a[0] as sj.Poly)),
  '.shift': polyM((p, a) => p.shift(asExpr(a[0]))),
  '.sqf_part': polyM((p) => p.sqfPart()),
  '.subresultants': polyM((p, a) => new JsList(p.subresultants(a[0] as sj.Poly))),
  '.terms_gcd': polyM((p) => {
    const [m, q] = p.termsGcd();
    return new JsTuple([new JsTuple(m), q]);
  }),
  '.deflate': polyM((p) => {
    const [m, q] = p.deflate();
    return new JsTuple([new JsTuple(m), q]);
  }),
  '.to_field': polyM((p) => p.toField()),
  '.to_ring': polyM((p) => p.toRing()),
  '.to_exact': polyM((p) => p.toExact()),
  '.principal_value': (args, kw, self) => {
    noKw(kw);
    if (args.length || !(self instanceof sj.Integral)) throw new Unsupported('principal_value');
    return sj.principalValue(self);
  },
  '.transform': (args, kw, self) => {
    if (self instanceof sj.Integral) {
      noKw(kw);
      const spec = args[1];
      if (spec instanceof JsTuple) return sj.transformIntegral(self, asExpr(args[0]), asExpr(spec.items[0]), asSym(spec.items[1]));
      return sj.transformIntegral(self, asExpr(args[0]), asExpr(spec));
    }
    return polyM((p, a) => p.transform(a[0] as sj.Poly, a[1] as sj.Poly))(args, kw, self);
  },
  '.trunc': polyM((p, a) => p.trunc(asExpr(a[0]))),
  '.clear_denoms': (_args, kw, self) => {
    for (const k of Object.keys(kw)) if (k !== 'convert') throw new Unsupported(`kwargs ${k}`);
    return new JsTuple(asPoly(self).clearDenoms(Boolean(kw['convert'])));
  },
  '.gcdex': polyM((p, a) => new JsTuple(p.gcdex(a[0] as sj.Poly))),
  '.half_gcdex': polyM((p, a) => new JsTuple(p.halfGcdex(a[0] as sj.Poly))),
  '.sturm': polyM((p) => new JsList(p.sturm())),
  '.count_roots': polyM((p, a) => {
    return p.countRoots(a[0] === undefined ? undefined : asExpr(a[0]), a[1] === undefined ? undefined : asExpr(a[1]));
  }),
  '.ground_roots': polyM((p) => new JsDict(p.groundRoots())),
  '.revert': polyM((p, a) => p.revert(intArg(a[0]))),
  '.nth_power_roots_poly': polyM((p, a) => p.nthPowerRootsPoly(intArg(a[0]))),
  '.real_roots': polyM((p) => new JsList(p.realRoots())),
  '.all_roots': polyM((p) => new JsList(p.allRoots())),
  '.lift': polyM((p) => p.lift()),
  '.get_modulus': polyM((p) => sj.Rational.of(p.getModulus())),
  '.set_modulus': polyM((p, [m]) => p.setModulus((m as sj.Rational).p)),
  '.eject': (args, kw, self) => (noKw(kw), (self as sj.Poly).eject(...args.map(asExpr))),
  '.inject': (_args, kw, self) => (self as sj.Poly).inject({ front: Boolean(kw['front']) }),
  '.root': polyM((p, a) => p.root(intArg(a[0]))),
  '.which_real_roots': polyM((p, a) => new JsList(p.whichRealRoots((a[0] as JsList).items.map(asExpr)))),
  '.which_all_roots': polyM((p, a) => new JsList(p.whichAllRoots((a[0] as JsList).items.map(asExpr)))),
  '.factor_list_include': polyM((p) => new JsList(p.factorListInclude().map(([f, k]) => new JsTuple([f, k])))),
  '.sqf_list_include': (_args, kw, self) => {
    for (const k of Object.keys(kw)) if (k !== 'all') throw new Unsupported(`kwargs ${k}`);
    return new JsList(asPoly(self).sqfListInclude(Boolean(kw['all'])).map(([f, k]) => new JsTuple([f, k])));
  },
  ground_roots: (args, kw) => {
    for (const k of Object.keys(kw)) if (k !== 'extension') throw new Unsupported(`kwargs ${k}`);
    return new JsDict(polyOf(args).groundRoots({ extension: Boolean(kw['extension']) }));
  },
  real_roots: (args, kw) => {
    for (const k of Object.keys(kw)) if (k !== 'multiple' && k !== 'extension' && k !== 'radicals') throw new Unsupported(`kwargs ${k}`);
    const rs = polyOf(args).realRoots({ extension: Boolean(kw['extension']), radicals: kw['radicals'] === undefined ? true : Boolean(kw['radicals']) });
    if (kw['multiple'] !== false) return new JsList(rs);
    // multiple=False: [(root, multiplicity)] in order
    const out: [Expr, number][] = [];
    for (const r of rs) {
      const last = out[out.length - 1];
      if (last && last[0].key === r.key) last[1]++;
      else out.push([r, 1]);
    }
    return new JsList(out.map(([r, k]) => new JsTuple([r, sj.Rational.of(k)])));
  },
  all_roots: (args, kw) => {
    for (const k of Object.keys(kw)) if (k !== 'extension') throw new Unsupported(`kwargs ${k}`);
    return new JsList(polyOf(args).allRoots({ extension: Boolean(kw['extension']) }));
  },
  count_roots: (args, kw) => {
    noKw(kw);
    const p = args[0] instanceof sj.Poly ? args[0] : sj.Poly.from(asExpr(args[0]));
    return p.countRoots(args[1] === undefined ? undefined : asExpr(args[1]), args[2] === undefined ? undefined : asExpr(args[2]));
  },
  '.pquo': (args, kw, self) => (noKw(kw), asPoly(self).pquo(args[0] as sj.Poly)),
  '.prem': (args, kw, self) => (noKw(kw), asPoly(self).prem(args[0] as sj.Poly)),
  '.exquo': (args, kw, self) => (noKw(kw), asPoly(self).exquo(args[0] as sj.Poly)),
  '.factor_list': (_a, kw, self) => {
    noKw(kw);
    const [c, fs] = asPoly(self).factorList();
    return new JsTuple([c, new JsList(fs.map(([f, k]) => new JsTuple([f, k])))]);
  },
  '.sqf_list': (_a, kw, self) => {
    for (const k of Object.keys(kw)) if (k !== 'all') throw new Unsupported(`kwargs ${k}`);
    const [c, fs] = asPoly(self).sqfListAll(Boolean(kw['all']));
    return new JsTuple([c, new JsList(fs.map(([f, k]) => new JsTuple([f, k])))]);
  },
  '.content': (_a, kw, self) => (noKw(kw), asPoly(self).content()),

  // ---- Matrix methods (linear algebra)
  '.rref': (_args, kw, self) => {
    if (!(self instanceof Matrix)) throw new Unsupported('Matrix');
    const test = kw['iszerofunc'];
    const [r, p] = sj.rref(self, test instanceof JsLambda ? { iszerofunc: (e) => test.call(e) === S.true } : {});
    return new JsTuple([r, new JsTuple(p)]);
  },
  '.echelon_form': matrixMethod((m) => sj.echelonForm(m)),
  '.rank': matrixMethod((m) => sj.rank(m)),
  '.nullspace': matrixMethod((m) => new JsList(sj.nullspace(m))),
  '.columnspace': matrixMethod((m) => new JsList(sj.columnspace(m))),
  '.rowspace': matrixMethod((m) => new JsList(sj.rowspace(m))),
  '.eigenvects': matrixMethod((m) => new JsList(sj.eigenvects(m).map(([v, k, vs]) => new JsTuple([v, k, new JsList(vs)])))),
  '.diagonalize': matrixMethod((m) => new JsTuple(sj.diagonalize(m))),
  '.is_diagonalizable': (_args, kw, self) => {
    if (!(self instanceof Matrix)) throw new Unsupported('Matrix');
    return sj.isDiagonalizable(self, Boolean(kw['reals_only']));
  },
  '.cholesky': (_args, kw, self) => {
    if (!(self instanceof Matrix)) throw new Unsupported('Matrix');
    return sj.cholesky(self, kw['hermitian'] === undefined ? true : Boolean(kw['hermitian']));
  },
  '.LDLdecomposition': matrixMethod((m) => new JsTuple(sj.ldl(m))),
  '.LUdecomposition': matrixMethod((m) => {
    const [L, U, p] = sj.luDecomposition(m);
    return new JsTuple([L, U, new JsList(p.map((x) => new JsList(x)))]);
  }),
  '.QRdecomposition': matrixMethod((m) => new JsTuple(sj.qrDecomposition(m))),
  '.dot': (args, kw, self) => {
    if (!(self instanceof Matrix)) throw new Unsupported('Matrix');
    const b = args[0] instanceof Matrix ? args[0] : args[0] instanceof JsTuple ? Matrix.col(...args[0].items.map(asExpr)) : undefined;
    if (!b) throw new Unsupported('dot argument');
    const conv = (kw['conjugate_convention'] as string | undefined) ?? 'maths';
    return sj.dot(self, b, Boolean(kw['hermitian']), conv === 'physics' || conv === 'right' ? 'physics' : 'maths');
  },
  '.cross': matrixMethod((m, [b]) => sj.cross(m, b as Matrix)),
  '.norm': (args, kw, self) => (self instanceof sj.Poly ? (noKw(kw), self.norm()) : matrixMethod((m, [o]) => sj.norm(m, o as ExprLike | undefined))(args, kw, self)),
  '.gammasimp': exprMethod(sj.gammasimp),
  '.combsimp': exprMethod(sj.combsimp),
  '.singular_values': matrixMethod((m) => new JsList(sj.singularValues(m))),
  '.pinv': matrixMethod((m) => sj.pinv(m)),
  '.jacobian': matrixMethod((m, [y]) => sj.jacobian(m, y instanceof Matrix ? y : (y as JsTuple).items.map(asExpr))),
  '.exp': matrixMethod((m) => sj.matrixExp(m)),
  '.log': matrixMethod((m) => sj.matrixLog(m)),
  '.analytic_func': matrixMethod((m, [f, x]) => sj.analyticFunc(m, asExpr(f), asSym(x))),
  '.upper_triangular': matrixMethod((m, [k]) => sj.linalg.upperTriangular(m, k ? Number((k as sj.Rational).p) : 0)),
  '.lower_triangular': matrixMethod((m, [k]) => sj.linalg.lowerTriangular(m, k ? Number((k as sj.Rational).p) : 0)),
  '.diagonal': matrixMethod((m, [k]) => sj.linalg.diagonal(m, k ? Number((k as sj.Rational).p) : 0)),
  '.extract': matrixMethod((m, [r, c]) =>
    sj.linalg.extract(m, idxList(r), idxList(c)),
  ),
  '.reshape': matrixMethod((m, [r, c]) => sj.linalg.reshape(m, Number((r as sj.Rational).p), Number((c as sj.Rational).p))),
  '.rot90': matrixMethod((m, [k]) => sj.linalg.rot90(m, k ? Number((k as sj.Rational).p) : 1)),
  '.vech': (_args, kw, self) => sj.linalg.vech(self as Matrix, kw['diagonal'] === undefined ? true : Boolean(kw['diagonal'])),
  '.vec': matrixMethod((m) => sj.linalg.vec(m)),
  '.minor': matrixMethod((m, [i, j]) => sj.linalg.minorDet(m, Number((i as sj.Rational).p), Number((j as sj.Rational).p))),
  '.minor_submatrix': matrixMethod((m, [i, j]) => m.minor(Number((i as sj.Rational).p), Number((j as sj.Rational).p))),
  '.cofactor': matrixMethod((m, [i, j]) => sj.linalg.cofactor(m, Number((i as sj.Rational).p), Number((j as sj.Rational).p))),
  '.cofactor_matrix': matrixMethod((m) => m.cofactorMatrix()),
  '.is_anti_symmetric': (_args, kw, self) => fromJs(sj.linalg.isAntiSymmetric(self as Matrix, kw['simplify'] === undefined ? true : Boolean(kw['simplify']))),
  '.is_diagonal': matrixMethod((m) => sj.linalg.isDiagonal(m)),
  '.is_upper': matrixMethod((m) => sj.linalg.isUpper(m)),
  '.is_lower': matrixMethod((m) => sj.linalg.isLower(m)),
  '.is_nilpotent': matrixMethod((m) => sj.linalg.isNilpotent(m)),
  '.multiply_elementwise': matrixMethod((m, [b]) => sj.linalg.multiplyElementwise(m, b as Matrix)),
  '.project': matrixMethod((m, [b]) => sj.linalg.project(m, b as Matrix)),
  '.col_join': matrixMethod((m, [b]) => m.vstack(b as Matrix)),
  '.row_join': matrixMethod((m, [b]) => m.hstack(b as Matrix)),
  '.col_insert': matrixMethod((m, [p, b]) => sj.linalg.colInsert(m, Number((p as sj.Rational).p), b as Matrix)),
  '.row_insert': matrixMethod((m, [p, b]) => sj.linalg.rowInsert(m, Number((p as sj.Rational).p), b as Matrix)),
  '.col': matrixMethod((m, [j]) => m.col(Number((j as sj.Rational).p))),
  '.row': matrixMethod((m, [i]) => m.row(Number((i as sj.Rational).p))),
  rot_axis1: exprFn(sj.rotAxis1),
  rot_axis2: exprFn(sj.rotAxis2),
  rot_axis3: exprFn(sj.rotAxis3),
  rot_ccw_axis1: exprFn(sj.rotCcwAxis1),
  rot_ccw_axis2: exprFn(sj.rotCcwAxis2),
  rot_ccw_axis3: exprFn(sj.rotCcwAxis3),
  rot_givens: (args, kw) => {
    const dim = kw['dim'] ? Number((kw['dim'] as sj.Rational).p) : 3;
    return sj.rotGivens(Number((args[0] as sj.Rational).p), Number((args[1] as sj.Rational).p), asExpr(args[2]), dim);
  },

  // ---- Matrix methods
  '.det': (_args, _kw, self) => {
    if (!(self instanceof Matrix)) throw new Unsupported('Matrix');
    return self.det();
  },
  '.inv': (_args, _kw, self) => {
    if (!(self instanceof Matrix)) throw new Unsupported('Matrix');
    return self.inv();
  },
  '.transpose': matrixMethod((m) => m.transpose()),
  '.adjugate': matrixMethod((m) => m.adjugate()),
  '.trace': matrixMethod((m) => m.trace()),
  '.eigenvals': matrixMethod((m) => rootsDict(m.eigenvals())),
  '.is_symmetric': (_args, _kw, self) => sj.linalg.isSymmetric(self as Matrix),
  '.tolist': matrixMethod((m) => new JsList(m.toArray().map((r) => new JsList(r)))),
};

// ---------------------------------------------------------------------------
// Adapters of SymPy base classes, Expr methods and more Matrix methods
// ---------------------------------------------------------------------------

/** Run an in-place operation of SymPy's mutable Matrix on a copy; like SymPy it returns None. */
const mutating =
  (f: (m: sj.MutableDenseMatrix, args: unknown[]) => void): Adapter =>
  (args, kw, self) => {
    noKw(kw);
    if (!(self instanceof Matrix)) throw new Unsupported('expected a Matrix');
    f(sj.MutableDenseMatrix.from(self), args);
    return null;
  };
const lambdaArg = (v: unknown): ((...xs: Expr[]) => Expr) => {
  if (v instanceof JsLambda) return (...xs: Expr[]) => v.call(...xs);
  throw new Unsupported('function argument');
};
const keyTree = (k: unknown): unknown => (Array.isArray(k) ? new JsTuple(k.map(keyTree)) : typeof k === 'number' ? sj.Rational.of(k) : k);
const generic = (make: (...a: Expr[]) => Expr): Adapter => (args, kw) => (noKw(kw), make(...args.map(asExpr)));
const errorAdapter = (E: new (m: string) => Error): Adapter => (args, kw) => (noKw(kw), new E(args.length ? String(args[0]) : ''));

Object.assign(ADAPTERS, {
  // ---- base classes
  Basic: generic((...a) => sj.Basic(...a)),
  Expr: generic((...a) => sj.genericExpr(...a)),
  Atom: generic((...a) => sj.Atom(...a)),
  AtomicExpr: generic((...a) => sj.AtomicExpr(...a)),
  NumberSymbol: generic((...a) => new sj.BasicNode(a, 'NumberSymbol')),
  Number: (args, kw) => (noKw(kw), sj.SymNumber(typeof args[0] === 'string' ? args[0] : asExpr(args[0]))),
  RealNumber: (args, kw) => ADAPTERS['Float']!(args, kw),
  FunctionClass: (args, kw) => (noKw(kw), new UFnClass(String(args[0]))),
  UnevaluatedExpr: (args, kw) => (noKw(kw), new sj.UnevaluatedExpr(asExpr(args[0]))),
  AlgebraicNumber: (args, kw) => {
    noKw(kw);
    const coeffs = args[1] instanceof JsList || args[1] instanceof JsTuple ? args[1].items.map(asExpr) : undefined;
    return new sj.AlgebraicNumber(asExpr(args[0]), coeffs).asExpr();
  },
  SympifyError: errorAdapter(sj.SympifyError),
  PoleError: errorAdapter(sj.PoleError),
  PrecisionExhausted: errorAdapter(sj.PrecisionExhausted),
  seterr: (args, kw) => {
    sj.seterr({ divide: Boolean(kw['divide'] ?? args[0]) });
    return null;
  },
  DeferredVector: (args, kw) => (noKw(kw), new sj.DeferredVector(String(args[0]))),

  // ---- Expr methods
  '.as_terms': exprMethod((e) => {
    const [terms, gens] = sj.asTerms(e);
    return new JsTuple([
      new JsList(terms.map(([t, [[re, im], monom, nc]]) => new JsTuple([t, new JsTuple([new JsTuple([new JsFloat(re), new JsFloat(im)]), new JsTuple(monom.map((k) => sj.Rational.of(k))), new JsTuple(nc)])]))),
      new JsList(gens),
    ]);
  }),
  '.class_key': exprMethod((e) => keyTree(sj.classKey(e))),
  '.sort_key': (_args, _kw, self) => keyTree(sj.sortKey(asExpr(self))),
  '.dir': (args, kw, self) => (noKw(kw), sj.dir(asExpr(self), asSym(args[0]), asExpr(args[1]))),
  '.separate': (args, kw, self) => sj.separate(asExpr(self), { deep: Boolean(kw['deep'] ?? args[0]), force: Boolean(kw['force'] ?? args[1]) }),
  ask: (args, kw) => (noKw(kw), none(sj.ask(args[0] as Expr | boolean, args[1] === undefined ? true : (args[1] as Expr | boolean)))),
  refine: (args, kw) => (noKw(kw), sj.refine(args[0] as Expr, args[1] === undefined ? true : (args[1] as Expr | boolean))),
  '.refine': (args, kw, self) => {
    noKw(kw);
    const a = args[0] === undefined ? true : (args[0] as Expr | boolean);
    return self instanceof Matrix ? sj.refine(self, a) : sj.refine(asExpr(self), a);
  },
  '.lseries': (args, kw, self) => {
    noKw(kw);
    const x = args[0] === undefined ? ([...sj.freeSymbols(asExpr(self))][0] as Sym) : asSym(args[0]);
    return sj.lseries(asExpr(self), x, args[1] === undefined ? 0 : asExpr(args[1]));
  },
  '.fps': (args, kw, self) => {
    noKw(kw);
    if (args[0] === undefined) return sj.fps(asExpr(self));
    return sj.fps(asExpr(self), asSym(args[0]), args[1] === undefined ? 0 : asExpr(args[1]));
  },
  // ---- sympy.series.sequences, limitseq, residues and sympy.calculus.finite_diff, euler
  '.find_linear_recurrence': (args, kw, self) => {
    if (!(self instanceof sj.SeqBase)) throw new Unsupported('sequence receiver');
    for (const key of Object.keys(kw)) if (!['n', 'd', 'gfvar'].includes(key)) throw new Unsupported(`kwargs ${key}`);
    const n = intArg(args[0] ?? kw['n']);
    const d = args[1] ?? kw['d'] ?? undefined;
    const gfvar = args[2] ?? kw['gfvar'] ?? undefined;
    if (gfvar === undefined) return new JsList(self.findLinearRecurrence(n, d === undefined ? undefined : intArg(d)));
    const [coefficients, generatingFunction] = self.findLinearRecurrence(n, d === undefined ? undefined : intArg(d), asSym(gfvar));
    return new JsTuple([new JsList(coefficients), generatingFunction]);
  },
  sequence: (args, kw) => {
    noKw(kw);
    const seq = args[0] instanceof JsTuple || args[0] instanceof JsList ? args[0].items.map(asExpr) : asExpr(args[0]);
    const lim = args[1] instanceof JsTuple ? (args[1].items.map(asExpr) as unknown as sj.SeqLimits) : undefined;
    return sj.sequence(seq, lim);
  },
  limit_seq: (args, kw) => {
    for (const k of Object.keys(kw)) if (k !== 'trials') throw new Unsupported(`kwargs ${k}`);
    const trials = kw['trials'] ?? args[2];
    return sj.limitSeq(asExpr(args[0]), args[1] === undefined ? undefined : asSym(args[1]), trials === undefined ? undefined : Number(asExpr(trials).toNumber()));
  },
  difference_delta: (args, kw) => {
    noKw(kw);
    return sj.differenceDelta(asExpr(args[0]), args[1] === undefined ? undefined : asSym(args[1]), args[2] === undefined ? undefined : asExpr(args[2]));
  },
  residue: (args, kw) => (noKw(kw), sj.residue(asExpr(args[0]), asSym(args[1]), asExpr(args[2]))),
  euler_equations: (args, kw) => {
    noKw(kw);
    const items = (a: unknown): Expr[] => (a instanceof JsTuple || a instanceof JsList ? a.items.map(asExpr) : a === undefined ? [] : [asExpr(a)]);
    return new JsList(sj.eulerEquations(asExpr(args[0]), items(args[1]), items(args[2])));
  },
  apply_finite_diff: (args, kw) => {
    noKw(kw);
    const items = (a: unknown): Expr[] => (a instanceof JsTuple || a instanceof JsList ? a.items.map(asExpr) : [asExpr(a)]);
    return sj.applyFiniteDiff(Number(asExpr(args[0]).toNumber()), items(args[1]), items(args[2]), args[3] === undefined ? undefined : asExpr(args[3]));
  },
  differentiate_finite: (args, kw) => {
    for (const k of Object.keys(kw)) if (!['points', 'x0', 'wrt'].includes(k)) throw new Unsupported(`kwargs ${k}`);
    const syms = args.slice(1).map((a) => (a instanceof Sym ? a : Number(asExpr(a).toNumber())));
    const pts = kw['points'];
    const points = pts === undefined ? undefined : pts instanceof JsList || pts instanceof JsTuple ? pts.items.map(asExpr) : asExpr(pts);
    return sj.differentiateFinite(asExpr(args[0]), syms, {
      ...(points === undefined ? {} : { points }),
      ...(kw['x0'] === undefined ? {} : { x0: asExpr(kw['x0']) }),
      ...(kw['wrt'] === undefined ? {} : { wrt: asSym(kw['wrt']) }),
    });
  },
  '.fourier_series': (args, kw, self) => {
    noKw(kw);
    const lim = args[0] instanceof JsTuple ? args[0].items : undefined;
    const x = lim ? asSym(lim[0]) : ([...sj.freeSymbols(asExpr(self))][0] as Sym);
    return sj.fourierSeries(asExpr(self), x, lim && lim.length === 3 ? [asExpr(lim[1]), asExpr(lim[2])] : undefined);
  },

  // ---- Matrix methods
  '.berkowitz': matrixMethod((m) => new JsTuple(sj.berkowitz(m).map((r) => new JsTuple(r)))),
  '.berkowitz_minors': matrixMethod((m) => new JsTuple(sj.berkowitzMinors(m))),
  '.bidiagonalize': (_args, kw, self) => sj.bidiagonalize(self as Matrix, kw['upper'] === undefined ? true : Boolean(kw['upper'])),
  '.bidiagonal_decomposition': (_args, kw, self) => new JsTuple(sj.bidiagonalDecomposition(self as Matrix, kw['upper'] === undefined ? true : Boolean(kw['upper']))),
  '.upper_hessenberg_decomposition': matrixMethod((m) => new JsTuple(sj.upperHessenbergDecomposition(m))),
  '.singular_value_decomposition': matrixMethod((m) => new JsTuple(sj.singularValueDecomposition(m))),
  '.LUdecomposition_Simple': matrixMethod((m) => {
    const [lu, swaps] = sj.LUdecompositionSimple(m);
    return new JsTuple([lu, new JsList(swaps.map((s) => new JsList(s.map((k) => sj.Rational.of(k)))))]);
  }),
  '.LUdecompositionFF': matrixMethod((m) => new JsTuple(sj.LUdecompositionFF(m))),
  '.lll': matrixMethod((m) => sj.lll(m)),
  '.lll_transform': matrixMethod((m) => new JsTuple(sj.lllTransform(m))),
  '.elementary_row_op': (args, kw, self) =>
    sj.elementaryRowOp(self as Matrix, {
      op: (kw['op'] ?? args[0] ?? 'n->kn') as sj.ElementaryOp['op'],
      ...(kw['row'] !== undefined ? { index: intArg(kw['row']) } : {}),
      ...(kw['k'] !== undefined ? { k: asExpr(kw['k']) } : {}),
      ...(kw['row1'] !== undefined ? { index1: intArg(kw['row1']) } : {}),
      ...(kw['row2'] !== undefined ? { index2: intArg(kw['row2']) } : {}),
    }),
  '.elementary_col_op': (args, kw, self) =>
    sj.elementaryColOp(self as Matrix, {
      op: (kw['op'] ?? args[0] ?? 'n->kn') as sj.ElementaryOp['op'],
      ...(kw['col'] !== undefined ? { index: intArg(kw['col']) } : {}),
      ...(kw['k'] !== undefined ? { k: asExpr(kw['k']) } : {}),
      ...(kw['col1'] !== undefined ? { index1: intArg(kw['col1']) } : {}),
      ...(kw['col2'] !== undefined ? { index2: intArg(kw['col2']) } : {}),
    }),
  '.permuteFwd': matrixMethod((m, [p]) => sj.permuteFwd(m, (p as JsList).items.map((i) => (i instanceof JsList || i instanceof JsTuple ? (i.items.map(intArg) as [number, number]) : intArg(i))) as never)),
  '.permuteBkwd': matrixMethod((m, [p]) => sj.permuteBkwd(m, (p as JsList).items.map((i) => (i instanceof JsList || i instanceof JsTuple ? (i.items.map(intArg) as [number, number]) : intArg(i))) as never)),
  '.row_del': mutating((m, [i]) => void sj.rowDel(m, intArg(i))),
  '.col_del': mutating((m, [j]) => void sj.colDel(m, intArg(j))),
  '.row_swap': mutating((m, [i, j]) => m.rowSwap(intArg(i), intArg(j))),
  '.col_swap': mutating((m, [i, j]) => m.colSwap(intArg(i), intArg(j))),
  '.row_op': mutating((m, [i, f]) => m.rowOp(intArg(i), (v, j) => lambdaArg(f)(v, sj.Rational.of(j)))),
  '.col_op': mutating((m, [j, f]) => m.colOp(intArg(j), (v, i) => lambdaArg(f)(v, sj.Rational.of(i)))),
  '.zip_row_op': mutating((m, [i, k, f]) => m.zipRowOp(intArg(i), intArg(k), (v, u) => lambdaArg(f)(v, u))),
  '.row_add': mutating((m, [s0, t, k]) => m.rowAdd(intArg(s0), intArg(t), asExpr(k))),
  '.row_mult': mutating((m, [i, k]) => m.rowMult(intArg(i), asExpr(k))),
  '.fill': mutating((m, [v]) => m.fill(asExpr(v))),
  '.copyin_matrix': mutating((m, [key, v]) => {
    const [i, j] = (key as JsTuple).items.map(intArg);
    m.copyinMatrix(i!, j!, v as Matrix);
  }),
  '.copyin_list': mutating((m, [key, v]) => {
    const [i, j] = (key as JsTuple).items.map(intArg);
    const vals = (v as JsList).items.map((r) => (r instanceof JsList ? r.items.map(asExpr) : asExpr(r)));
    m.copyinList(i!, j!, vals as Expr[]);
  }),
  '.get_diag_blocks': matrixMethod((m) => new JsList(sj.getDiagBlocks(m))),
  '.connected_components_decomposition': matrixMethod((m) => new JsTuple(sj.connectedComponentsDecomposition(m))),
  '.strongly_connected_components_decomposition': (_args, kw, self) => new JsTuple(sj.stronglyConnectedComponentsDecomposition(self as Matrix, kw['lower'] === undefined ? true : Boolean(kw['lower']))),
  '.jordan_cell': matrixMethod((_m, [e, n]) => sj.jordanCell(asExpr(e), intArg(n))),
  '.jordan_cells': matrixMethod((m) => {
    const [P, blocks] = sj.jordanCells(m);
    return new JsTuple([P, new JsList(blocks)]);
  }),
  '.dual': matrixMethod((m) => sj.dual(m)),
  '.iter_items': matrixMethod((m) => sj.iterItems(m).map(([[i, j], v]) => new JsTuple([new JsTuple([sj.Rational.of(i), sj.Rational.of(j)]), v]))),
  '.iter_values': matrixMethod((m) => sj.iterValues(m)),
  '.key2ij': matrixMethod((m, [k]) => {
    if (!(k instanceof JsTuple)) return keyTree(sj.key2ij(m, intArg(k)));
    return new JsList(sj.key2ij(m, k.items.map(intArg) as [number, number]).map((v) => sj.Rational.of(v as number)));
  }),
  '.key2bounds': matrixMethod((m, [k]) => keyTree(sj.key2bounds(m, (k as JsTuple).items.map(intArg) as [number, number]))),
  '.print_nonzero': (args, _kw, self) => {
    // SymPy prints the pattern and returns None
    sj.printNonzero(self as Matrix, args[0] === undefined ? 'X' : String(args[0]));
    return null;
  },
  '.table': (args, kw, self) => {
    for (const k of Object.keys(kw)) if (!['rowstart', 'rowend', 'rowsep', 'colsep', 'align'].includes(k)) throw new Unsupported(`kwargs ${k}`);
    const printer = args[0];
    if (!(printer instanceof sj.StrPrinter)) throw new Unsupported('table printer');
    return sj.table(self as Matrix, { ...kw, printer: (e) => printer.doprint(e) } as sj.TableOptions);
  },
  '.to_DM': (_args, kw, self) => sj.toDM(self as Matrix, { field: Boolean(kw['field']) }),
  '.wilkinson': (args, kw) => (noKw(kw), new JsTuple(sj.wilkinson(intArg(args[0])))),
  MatrixBase: (args, kw) => ADAPTERS['Matrix']!(args, kw),
  randMatrix: (args, kw) => {
    const n = (k: string, i: number) => (kw[k] ?? args[i]) as unknown;
    const num = (v: unknown) => (v === undefined || v === null ? undefined : intArg(v));
    return sj.randMatrix(intArg(args[0]), num(n('c', 1)), { min: num(n('min', 2)), max: num(n('max', 3)), seed: num(n('seed', 4)), symmetric: Boolean(n('symmetric', 5)), percent: num(n('percent', 6)) });
  },
  symarray: (args, kw) => {
    const shape = args[1] instanceof JsTuple ? args[1].items.map(intArg) : intArg(args[1]);
    return sj.symarray(String(args[0]), shape, kw as sj.Assumptions);
  },
  matrix2numpy: matrixMethod((m) => sj.matrix2numpy(m)),
  list2numpy: (args, kw) => (noKw(kw), sj.list2numpy((args[0] as JsList).items)),

  // ---- AccumBounds
  AccumBounds: (args, kw) => (noKw(kw), sj.AccumBounds(asExpr(args[0]), asExpr(args[1]))),
  '.intersection': (args, kw, self) => {
    noKw(kw);
    if (self instanceof sj.AccumBoundsNode) return self.intersection(args[0] instanceof sj.AccumBoundsNode ? args[0] : (asSet(args[0]) as unknown as Expr));
    return sj.intersection(asSet(self), asSet(args[0]));
  },
  '.union': (args, kw, self) => {
    noKw(kw);
    if (self instanceof sj.AccumBoundsNode && args[0] instanceof sj.AccumBoundsNode) return self.union(args[0]);
    return sj.union(asSet(self), asSet(args[0]));
  },

  // ---- polys and number theory
  poly_from_expr: (args, kw) => {
    const [p, o] = sj.polyFromExpr(asExpr(args[0]), args.slice(1).map(asExpr), kw['domain'] ? { domain: String(kw['domain']) } : {});
    return new JsTuple([p, new JsDict([['gens', new JsTuple(o.gens)], ['domain', new UFnClass(o.domain)], ['polys', false]])]);
  },
  parallel_poly_from_expr: (args, _kw) => {
    const [ps, o] = sj.parallelPolyFromExpr((args[0] as JsList).items.map(asExpr), args.slice(1).map(asExpr));
    return new JsTuple([new JsList(ps), new JsDict([['gens', new JsTuple(o.gens)], ['domain', new UFnClass(o.domain)], ['polys', false]])]);
  },
  gff: (args, kw) => (noKw(kw), sj.gff(asExpr(args[0]))),
  carmichael: (args, kw) => (noKw(kw), sj.carmichael.isCarmichael(asExpr(args[0]))),
} satisfies Record<string, Adapter>);

// ---------------------------------------------------------------------------
// Runner
// ---------------------------------------------------------------------------

export interface Case {
  fn: string;
  category: string;
  module: string;
  src: string;
  expected: string;
  args?: Tree[];
  kwargs?: Record<string, Tree>;
  self?: Tree;
  /** Component displayed after unpacking the call's result into named targets. */
  pick?: number;
  /** Python builtin applied to the result before comparison: len(...), list(...), tuple(...), [str(r) for r in ...], str(...), repr(...). */
  post?: 'len' | 'list' | 'tuple' | 'str-items' | 'str' | 'repr';
  /** For str()/repr(): the Python lists ('l') and tuples ('t') of the result in preorder (JS arrays are either). */
  brackets?: string;
  unsupportedArg?: string;
  assume?: Tree[];
  /** printed output (print(f(...)), pprint(...), a str result): compared as text */
  text?: boolean;
  /** the doctest compares with NORMALIZE_WHITESPACE */
  ws?: boolean;
  /** the result formatted by Python's %-operator ('%.0e' % value) */
  pyFormat?: string;
}

/** Python's '%.Ne' and '%.Nf' formats of a number (the exponent has at least two digits). */
export function pyNumberFormat(format: string, v: unknown): string {
  const m = /^%(?:\.(\d+))?([eEf])$/.exec(format);
  if (!m || !(v instanceof Expr) || !v.isNumber) throw new Unsupported(`Python format ${format} of ${fmt(v)}`);
  const digits = Number(m[1] ?? '6');
  const x = v.toNumber();
  if (m[2] === 'f') return x.toFixed(digits);
  const s = x.toExponential(digits).replace(/e([+-])(\d)$/, (_m, sign: string, d: string) => `e${sign}0${d}`);
  return m[2] === 'E' ? s.toUpperCase() : s;
}

ADAPTERS['MutablePolyDenseMatrix'] = (args, kw) => new sj.PolyMatrix(...(polyMatrixArgs(args, kw) as sj.PolyMatrixArgument[]));
// The classmethods of PolyMatrix: from_Matrix(M, *gens, ring=...), eye(n, gens), zeros(m, n, gens)
const polyMatrixClassmethod = (method: (args: unknown[]) => unknown, previous: Adapter | undefined): Adapter => (args, kw, self) => {
  if (self instanceof TypeRef && self.name === 'PolyMatrix') return method(polyMatrixArgs(args, kw));
  if (previous === undefined) throw new Unsupported(`classmethod on ${String(self)}`);
  return previous(args, kw, self);
};
ADAPTERS['.from_Matrix'] = polyMatrixClassmethod((a) => sj.PolyMatrix.fromMatrix(...(a as Parameters<typeof sj.PolyMatrix.fromMatrix>)), ADAPTERS['.from_Matrix']);
ADAPTERS['.eye'] = polyMatrixClassmethod((a) => sj.PolyMatrix.eye(...(a as Parameters<typeof sj.PolyMatrix.eye>)), ADAPTERS['.eye']);
{
  const zeros = definedOr(ADAPTERS['.zeros'], '.zeros adapter');
  const arrays = { ImmutableDenseNDimArray: sj.ImmutableDenseNDimArray, MutableDenseNDimArray: sj.MutableDenseNDimArray, ImmutableSparseNDimArray: sj.ImmutableSparseNDimArray, MutableSparseNDimArray: sj.MutableSparseNDimArray };
  ADAPTERS['.zeros'] = (args, kw, self) => {
    if (self instanceof TypeRef && Object.hasOwn(arrays, self.name)) {
      noKw(kw);
      return arrays[self.name as keyof typeof arrays].zeros(...args.map((a) => intArg(a)));
    }
    return zeros(args, kw, self);
  };
}
ADAPTERS['.zeros'] = polyMatrixClassmethod((a) => sj.PolyMatrix.zeros(...(a as Parameters<typeof sj.PolyMatrix.zeros>)), ADAPTERS['.zeros']);

// sympy.crypto LFSRs: symjs takes the values of the GF(p) elements and the modulus
const ffValues = (l: unknown): [bigint[], bigint] => {
  const xs = (l as JsList).items as JsFFElement[];
  return [xs.map((x) => x.v), xs[0]?.mod ?? 2n];
};
ADAPTERS['lfsr_sequence'] = (args, kw) => {
  noKw(kw);
  const [key, mod] = ffValues(args[0]);
  const [fill] = ffValues(args[1]);
  const sym = ((args[0] as JsList).items[0] as JsFFElement).symmetric;
  return new JsList(sj.lfsrSequence(key, fill, Number((args[2] as sj.Rational).p), { modulus: mod }).map((v) => new JsFFElement(v, mod, sym)));
};
ADAPTERS['lfsr_autocorrelation'] = (args, kw) => (noKw(kw), sj.lfsrAutocorrelation(ffValues(args[0])[0], Number((args[1] as sj.Rational).p), Number((args[2] as sj.Rational).p)));
ADAPTERS['lfsr_connection_polynomial'] = (args, kw) => {
  noKw(kw);
  const [s, mod] = ffValues(args[0]);
  return sj.lfsrConnectionPolynomial(s, { modulus: mod });
};

/**
 * A text case: a string result is compared with the printed text (trailing
 * newlines are not significant, and runs of whitespace are one space when
 * the doctest says NORMALIZE_WHITESPACE); other results are compared like
 * any case (print(expand_func(...)) prints str() of the result).
 */
function textMatches(v: unknown, c: Case): boolean {
  if (typeof v !== 'string') return matches(v, c.expected);
  const norm = (t: string): string => (c.ws ? t.replace(/\s+/g, ' ').trim() : t.replace(/\n+$/, ''));
  return norm(v) === norm(c.expected);
}

/** Text cases print like SymPy's doctest runner: pretty printing in ASCII. */
function asDoctest<T>(c: Case, f: () => T): T {
  if (!c.text) return f();
  const prev = sj.pprintUseUnicode(false);
  try {
    return f();
  } finally {
    sj.pprintUseUnicode(prev);
  }
}

// ---------------------------------------------------------------------------
// Printing: SymPy's keyword settings as the options object of the printers
// (integer settings such as long_frac_ratio and terms_per_line are JS numbers,
// dicts such as symbol_names are Maps)
// ---------------------------------------------------------------------------

/** A printer setting: integers as numbers, dicts as Maps, the rest as deserialized. */
function printSetting(v: unknown): unknown {
  // a printer setting given as Python None is the setting's default
  if (v === null) return undefined;
  if (v instanceof sj.Rational && v.q === 1n) return Number(v.p);
  if (v instanceof JsDict) return new Map(v.entries);
  return v;
}
// mat_delim=None prints a matrix without delimiters
const printOptions = (kw: Record<string, unknown>): Record<string, unknown> => Object.fromEntries(Object.entries(kw).map(([k, v]) => [camel(k), k === 'mat_delim' && v === null ? '' : printSetting(v)]));
/** A printable argument: SymPy lists are arrays, dicts Maps, sets Sets. */
function printable(v: unknown): unknown {
  if (v instanceof JsList || v instanceof JsTuple) return v.items.map(printable);
  if (v instanceof JsDict) return new Map(v.entries.map(([k, x]) => [printable(k), printable(x)]));
  if (v instanceof JsSet) return new Set(v.items.map(printable));
  if (v instanceof UFnClass) return sj.SymFunction(v.name, { nargs: v.nargs });
  if (v instanceof JsLambda) return lambdaAsNode(v);
  return v;
}
/** A pretty-printable argument: SymPy tuples are PrettyTuples (printed with parentheses), lists arrays. */
function prettyArg(v: unknown): unknown {
  if (v instanceof JsTuple && !v.isList) return new sj.PrettyTuple(...(v.items.map(prettyArg) as sj.Printable[]));
  if (v instanceof JsTuple) return v.items.map(prettyArg);
  if (v instanceof JsList) return v.items.map(prettyArg);
  if (v instanceof JsDict) return new Map(v.entries.map(([k, x]) => [prettyArg(k), prettyArg(x)]));
  if (v instanceof JsSet) return new Set(v.items.map(prettyArg));
  if (v instanceof UFnClass) return sj.SymFunction(v.name, { nargs: v.nargs });
  return v;
}
ADAPTERS['TableForm'] = (args, kw) => {
  const cell = (v: unknown): sj.TableEntry => v instanceof JsTuple || v instanceof JsList || v instanceof JsDict || v instanceof JsSet ? fmt(v) : v as sj.TableEntry;
  const data = args[0] instanceof Matrix ? args[0] : (args[0] as JsTuple).items.map((r) => (r as JsTuple).items.map(cell));
  const options = Object.fromEntries(Object.entries(kw).map(([k, v]) => [camel(k), printable(v)]));
  return new sj.TableForm(data, options);
};
ADAPTERS['DiagramGrid'] = (args, kw) => (noKw(kw), new categories.DiagramGrid(args[0] as sj.Diagram));
ADAPTERS['.draw'] = (args, kw, self) => {
  if (!(self instanceof categories.XypicDiagramDrawer)) return unsupportedOp('draw');
  const masked = kw['masked'] instanceof JsTuple ? kw['masked'].items : Array.isArray(kw['masked']) ? kw['masked'] : [];
  const options: categories.XypicDrawOptions = { masked: masked as sj.Morphism[] };
  if (typeof kw['diagram_format'] === 'string') options.diagramFormat = kw['diagram_format'];
  return self.draw(args[0] as sj.Diagram, args[1] as categories.DiagramGrid, options);
};
for (const name of ['pretty', 'pprint'] as const) ADAPTERS[name] = (args, kw) => args[0] instanceof categories.DiagramGrid ? args[0].toPretty() + (name === 'pprint' ? '\n' : '') : sj[name](prettyArg(args[0]) as sj.Printable, printOptions(kw));
// a Python tuple of expressions prints as a SymPy Tuple (SymPy _print_tuple)
ADAPTERS['latex'] = (args, kw) => {
  const a = args[0];
  const tuple = a instanceof JsTuple && !a.isList && a.items.every((x) => x instanceof Expr) ? sj.Tuple(...(a.items as Expr[])) : printable(a);
  return sj.latex(tuple as sj.LatexPrintable, printOptions(kw));
};
ADAPTERS['print_latex'] = (args, kw) => sj.printLatex(printable(args[0]) as sj.LatexPrintable, printOptions(kw));
ADAPTERS['multiline_latex'] = (args, kw) => {
  const [lhs, rhs, terms] = args;
  return sj.multilineLatex(lhs as Expr, rhs as Expr, { ...(terms === undefined ? {} : { termsPerLine: printSetting(terms) as number }), ...printOptions(kw) });
};
ADAPTERS['srepr'] = (args, kw) => {
  for (const k of Object.keys(kw)) if (k !== 'perm_cyclic') throw new Unsupported(`kwargs ${k}`);
  return sj.srepr(printable(args[0]) as sj.ReprPrintable, kw['perm_cyclic'] === undefined ? {} : { permCyclic: kw['perm_cyclic'] as boolean });
};
ADAPTERS['mathml'] = (args, kw) => sj.mathml(printable(args[0]) as sj.MathMLPrintable, printOptions(kw));
ADAPTERS['print_mathml'] = (args, kw) => sj.printMathml(printable(args[0]) as sj.MathMLPrintable, printOptions(kw));
ADAPTERS['print_tree'] = (args, kw) => sj.printTree(args[0] as Expr, printOptions(kw));
// sympy.printing.tree.tree is the text print_tree prints, without its final newline
ADAPTERS['tree'] = (args, kw) => sj.printTree(args[0] as Expr, printOptions(kw)).slice(0, -1);
ADAPTERS['dotprint'] = (args, kw) => sj.dotprint(args[0] as Expr, printOptions(kw));

// Matrix.print_nonzero prints the pattern; symjs printNonzero returns it
ADAPTERS['.print_nonzero'] = (args, kw, self) => (noKw(kw), sj.printNonzero(self as Matrix, ...(args as [string?])));
// SymPy minpoly is an alias of minimal_polynomial
ADAPTERS['minpoly'] = ADAPTERS['minimal_polynomial']!;

// diophantine returns a Python set of tuples (a list of arrays in symjs)
ADAPTERS['diophantine'] = (args, kw) => new JsSet(sj.diophantine(asExpr(args[0]), { permute: kw['permute'] === true }).map((t) => new JsTuple(t)));

ADAPTERS['Indexed'] = (args, kw) => {
  noKw(kw);
  const [b, ...ix] = args;
  if (b instanceof sj.IndexedBase) return b.at(...ix.map(asExpr));
  const label = typeof b === 'string' ? sj.symbol(b) : asExpr(b);
  return new sj.Indexed([label, ...ix.map(asExpr)]);
};

ADAPTERS['.as_set'] = (_args, kw, self) => (noKw(kw), sj.asSet(self as Expr | boolean));

// K.of_type(a) of a GF(p) element: the element itself, not its integer value
ADAPTERS['.of_type'] = (args, kw, self0) => {
  noKw(kw);
  const self = self0 instanceof JsDomain ? self0.domain : self0;
  if (!(self instanceof sj.Domain) || !(args[0] instanceof JsFFElement)) throw new Unsupported('no adapter for .of_type');
  return self.ofType(plain(args[0]));
};

// R.is_unit(a) of a univariate old polynomial ring R: its elements are dense polynomials (SymPy DMP), deserialized
// over the placeholder generator _x, which stands for the generator of R
ADAPTERS['.is_unit'] = (args, kw, self0) => {
  noKw(kw);
  const self = self0 instanceof JsDomain ? self0.domain : self0;
  if (!(self instanceof sj.Domain)) throw new Unsupported('no adapter for .is_unit');
  const a = args[0];
  return self.isUnit(a instanceof sj.DMP && self instanceof sj.PolynomialRingBase && self.symbols.length === 1 ? sj.subs(a.toSympy(), [[new Sym('_x'), self.symbols[0]!]]) : a);
};

// assumptions: an AssumptionsContext (global_assumptions) and Q.<predicate>(...)
for (const m of ['add', 'remove', 'clear'] as const) {
  const prev = ADAPTERS[`.${m}`];
  ADAPTERS[`.${m}`] = (args, kw, self) => {
    if (self instanceof sj.AssumptionsContext) {
      noKw(kw);
      if (m === 'clear') self.clear();
      else self[m](...(args as Expr[]));
      return null;
    }
    if (!prev) throw new Unsupported(`.${m}`);
    return prev(args, kw, self);
  };
}
for (const name of Object.keys(sj.Q)) {
  const prev = ADAPTERS[`.${name}`];
  ADAPTERS[`.${name}`] = (args, kw, self) => {
    if (self === sj.Q) return (noKw(kw), sj.Q[name]!(...(args as Expr[])));
    if (!prev) throw new Unsupported(`.${name}`);
    return prev(args, kw, self);
  };
}

// ---------------------------------------------------------------------------
// Generic adapter: SymPy name -> camelCase export or method (snake_case
// keywords become an options object), for the modules whose API follows the
// naming policy directly (logic, combinatorics, utilities, tensor, ntheory).
// ---------------------------------------------------------------------------

/** Categories whose integer arguments are JS numbers (indices, sizes, sequences). */
const NUMERIC_CATEGORIES = new Set(['combinatorics', 'utilities', 'tensor', 'discrete', 'geometry', 'crypto', 'liealgebras']);
/** Functions of other categories whose integer arguments are JS numbers (variable numbers of the integer representation of clauses). */
const NUMERIC_FUNCTIONS = new Set(['dmp_alg_inject', 'solve_de', 'hyper_algorithm', 'bool_maxterm', 'bool_minterm', 'bool_monomial', 'unit_propagate_int_repr', '.reorder_limit', '.__pow__', 'ImmutableMatrix', 'ImmutableDenseMatrix', 'gauss_legendre', 'gauss_laguerre', 'gauss_hermite', 'gauss_gen_laguerre', 'gauss_jacobi', 'gauss_chebyshev_t', 'gauss_chebyshev_u', 'gauss_lobatto']);
/** Python operators recorded as their special methods (the number-field doctests), and the methods that implement them. */
/** A value that symjs arithmetic accepts directly (an expression or a JS number). */
const isScalar = (v: unknown): v is ExprLike => v instanceof Expr || typeof v === 'number' || typeof v === 'bigint';
/** The first of the named methods that the receiver has, called with the arguments. */
function callMethod(self: unknown, names: readonly string[], args: readonly unknown[]): { value: unknown } | undefined {
  if (self === null || (typeof self !== 'object' && typeof self !== 'function')) return undefined;
  for (const n of names) {
    const m = (self as Record<string, unknown>)[n];
    if (typeof m === 'function') return { value: (m as (...a: unknown[]) => unknown).apply(self, [...args]) };
  }
  return undefined;
}
/** A deserialized Python container as the JS value: tuples and lists as arrays, dicts as Maps, sets as Sets. */
function plain(v: unknown): unknown {
  if (v instanceof JsFFElement) return sj.GF(v.mod, v.symmetric).new(v.v);
  if (v instanceof JsTuple || v instanceof JsList) return v.items.map(plain);
  if (v instanceof JsDict || v instanceof JsDefaultDict) return new Map(v.entries.map(([k, x]) => [plain(k), plain(x)]));
  if (v instanceof JsSet) return new Set(v.items.map(plain));
  return v;
}
/** Python == of two values: SymPy structural equality, or the JS equality of plain values and their lists. */
function pyEquals(a0: unknown, b0: unknown): boolean {
  const a = plain(a0);
  const b = plain(b0);
  if (a instanceof Set && b instanceof Set) return a.size === b.size && [...a].every((x) => [...b].some((y) => pyEquals(x, y)));
  if (a instanceof Map && b instanceof Map) return a.size === b.size && [...a].every(([k, x]) => [...b].some(([l, y]) => pyEquals(k, l) && pyEquals(x, y)));
  if (a instanceof sj.GeometryEntity && b instanceof sj.GeometryEntity) return a.key === b.key;
  if (Array.isArray(a) && Array.isArray(b)) return a.length === b.length && a.every((v, i) => pyEquals(v, b[i]));
  if (a instanceof Expr && !isScalar(b)) return false;
  const r = callMethod(a, ['equals', 'eq'], [b]);
  if (r !== undefined) return r.value === true || (r.value instanceof Expr && String(r.value) === 'True');
  if (isScalar(a) && isScalar(b)) return sj.sympify(a).equals(b);
  return a === b;
}
/**
 * Python operators, comparisons, subscripts and calls of SymPy objects (the special methods that the
 * extractor records for g * f, a == b, a[0, 0], Cycle(1, 2)(2, 3)): the receiver's method of that name
 * when it has one, otherwise the symjs function of the operation.
 */
/** Python raises TypeError for an operation its operand types do not define. */
const pythonTypeError = (message: string): never => { throw new TypeError(message); };

const DUNDER: Readonly<Record<string, (self: unknown, args: unknown[]) => unknown>> = {
  '.__add__': (a, [b]) => (b instanceof sj.OrdinalNode && a instanceof sj.Rational && a.q === 1n ? sj.convertOrdinal(a.p).add(b) : undefined) ?? (isScalar(a) && !isScalar(b) ? callMethod(b, ['add'], [a])?.value : undefined) ?? callMethod(a, ['add'], [b])?.value ?? (isScalar(a) && isScalar(b) ? sj.add(a, b) : unsupportedOp('+')),
  // PolyMatrix has no reflected subtraction: a scalar minus a PolyMatrix is a Python TypeError
  '.__sub__': (a, [b]) => (isScalar(a) && b instanceof sj.PolyMatrix ? pythonTypeError("unsupported operand type(s) for -: 'int' and 'PolyMatrix'") : undefined) ?? callMethod(a, ['sub'], [b])?.value ?? (isScalar(a) && isScalar(b) ? sj.sub(a, b) : unsupportedOp('-')),
  '.__mul__': (a, [b]) => (Array.isArray(a) && b instanceof sj.PolyMatrix ? pythonTypeError("can't multiply sequence by non-int of type 'PolyMatrix'") : undefined) ?? (b instanceof sj.NDimArray && isScalar(a) ? b.rmul(a) : undefined) ?? (a instanceof sj.ModuleImplementedIdeal && b instanceof sj.Module ? b.multiplyIdeal(a) : undefined) ?? (Array.isArray(a) && b instanceof sj.Permutation ? new sj.Permutation(a).mul(b) : undefined) ?? (isScalar(a) && !isScalar(b) ? callMethod(b, ['mul'], [a])?.value : undefined) ?? callMethod(a, ['mul', 'compose'], [b])?.value ?? (isScalar(a) && isScalar(b) ? sj.mul(a, b) : unsupportedOp('*')),
  '.__truediv__': (a, [b]) => (a instanceof sj.Domain ? a.quotientRing(b as sj.ModuleImplementedIdeal | Expr[]) : undefined) ?? callMethod(a, ['div', 'truediv', 'quotientModule'], [b])?.value ?? (isScalar(a) && isScalar(b) ? sj.mul(a, sj.pow(b, -1)) : unsupportedOp('/')),
  '.__pow__': (a, [b]) => callMethod(a, ['pow'], [b])?.value ?? (isScalar(a) && isScalar(b) ? sj.pow(a, b) : unsupportedOp('**')),
  '.__floordiv__': (a, [b]) => callMethod(a, ['floordiv'], [b])?.value ?? (isScalar(a) && isScalar(b) ? sj.floor(sj.mul(a, sj.pow(b, -1))) : unsupportedOp('//')),
  '.__mod__': (a, [b]) => callMethod(a, ['mod'], [b])?.value ?? (isScalar(a) && isScalar(b) ? sj.Mod(a, b) : unsupportedOp('%')),
  '.__matmul__': (a, [b]) => callMethod(a, ['matmul', 'mul'], [b])?.value ?? unsupportedOp('@'),
  '.__neg__': (a) => callMethod(a, ['neg'], [])?.value ?? (isScalar(a) ? sj.neg(a) : unsupportedOp('-')),
  '.__invert__': (a) => callMethod(a, ['invert', 'inv', 'inverse'], [])?.value ?? (a instanceof Expr || typeof a === 'boolean' ? sj.Not(a) : unsupportedOp('~')),
  '.__and__': (a, [b]) => callMethod(a, ['and', 'intersect', 'dot'], [b])?.value ?? (a instanceof Expr && b instanceof Expr ? sj.And(a, b) : unsupportedOp('&')),
  '.__or__': (a, [b]) => callMethod(a, ['or', 'union'], [b])?.value ?? (a instanceof Expr && b instanceof Expr ? sj.Or(a, b) : unsupportedOp('|')),
  '.__xor__': (a, [b]) => callMethod(a, ['xor', 'cross', 'symmetricDifference'], [b])?.value ?? (a instanceof Expr && b instanceof Expr ? sj.Xor(a, b) : unsupportedOp('^')),
  '.__rshift__': (a, [b]) => callMethod(a, ['rshift'], [b])?.value ?? ((a instanceof Expr || typeof a === 'boolean') && (b instanceof Expr || typeof b === 'boolean') ? sj.Implies(a, b) : unsupportedOp('>>')),
  '.__lshift__': (a, [b]) => callMethod(a, ['lshift'], [b])?.value ?? (a instanceof Expr && b instanceof Expr ? sj.Implies(b, a) : unsupportedOp('<<')),
  '.__eq__': (a, [b]) => pyEquals(a, b),
  '.__ne__': (a, [b]) => !pyEquals(a, b),
  '.__lt__': (a, [b]) => callMethod(a, ['lt'], [b])?.value ?? (isScalar(a) && isScalar(b) ? sj.Lt(a, b) : unsupportedOp('<')),
  '.__le__': (a, [b]) => callMethod(a, ['le'], [b])?.value ?? (isScalar(a) && isScalar(b) ? sj.Le(a, b) : unsupportedOp('<=')),
  '.__gt__': (a, [b]) => callMethod(a, ['gt'], [b])?.value ?? (isScalar(a) && isScalar(b) ? sj.Gt(a, b) : unsupportedOp('>')),
  '.__ge__': (a, [b]) => callMethod(a, ['ge'], [b])?.value ?? (isScalar(a) && isScalar(b) ? sj.Ge(a, b) : unsupportedOp('>=')),
  '.__contains__': (a, [b]) => {
    if (a instanceof sj.SetExpr && !(a instanceof sj.MatrixSet)) {
      const result = sj.contains(a, Array.isArray(b) ? sj.Tuple(...b.map(asExpr)) : asExpr(b));
      if (result === S.true) return true;
      if (result === S.false) return false;
      throw new TypeError('cannot determine symbolic set membership');
    }
    if (Array.isArray(a)) return a.some((v) => pyEquals(v, b));
    if (a instanceof Map) return [...a.keys()].some((k) => pyEquals(k, b));
    if (a instanceof Set) return [...a].some((k) => pyEquals(k, b));
    if (a instanceof sj.MatrixSet) return a.contains(b as Matrix) === true;
    if (a instanceof sj.SetExpr) return sj.containsQ(a, Array.isArray(b) ? sj.Tuple(...b.map(asExpr)) : asExpr(b)) === true;
    const r = callMethod(a, ['contains', 'has', 'includes'], [b]);
    if (r === undefined) return unsupportedOp('in');
    return r.value instanceof Expr ? String(r.value) === 'True' : r.value === true;
  },
  '.__getitem__': (a, [i]) => {
    if (a instanceof sj.SeriesBase) {
      if (i instanceof sj.Slice) {
        const [start, stop, step] = i.toString().split(':').map((part) => part === '' ? undefined : Number(part));
        return a.slice(start, stop, step);
      }
      return a.getItem(Number(i));
    }
    if (a instanceof sj.PolyMatrix) {
      // M[k], M[i, j], M[start:stop] (a list of the entries) and M[rows, cols] with slices (a submatrix)
      const positions = (v: unknown, n: number): number[] => {
        if (!(v instanceof sj.Slice)) return [Number(v)];
        const [start, stop, step] = v.indices(n);
        return Array.from({ length: Math.max(0, Math.ceil((stop - start) / step)) }, (_, k) => start + k * step);
      };
      if (i instanceof sj.Slice) return new JsList(positions(i, a.length).map((k) => a.get(k)));
      const key = i instanceof JsTuple ? i.items : Array.isArray(i) ? i : undefined;
      if (key === undefined) return a.get(Number(i));
      const [r, c] = key;
      return r instanceof sj.Slice || c instanceof sj.Slice ? a.extract(positions(r, a.rows), positions(c, a.cols)) : a.get(Number(r), Number(c));
    }
    const index = i instanceof JsTuple ? i.items : Array.isArray(i) && (a instanceof Matrix || a instanceof sj.MatrixExpr || a instanceof sj.NDimArray || a instanceof sj.IndexedBase || a instanceof sj.ArraySymbol || a instanceof categories.DiagramGrid) ? i : [i];
    if (index.some((j) => j instanceof sj.Slice)) {
      if (a instanceof sj.MatrixExpr) {
        const spec = (v: unknown): sj.SliceSpec => v instanceof sj.Slice ? v.toString().split(':').map((p) => p === '' ? null : Number(p)) as [number | null, number | null, number | null] : asExpr(v);
        return sj.MatrixSlice(a, spec(index[0]), spec(index[1]));
      }
      if (a instanceof Matrix) {
        const indices = (v: unknown, n: number): number[] => {
          if (!(v instanceof sj.Slice)) return [Number(v)];
          const [start, stop, step] = v.indices(n);
          return Array.from({ length: Math.max(0, Math.ceil((stop - start) / step)) }, (_, k) => start + k * step);
        };
        return a.slice(indices(index[0], a.rows), indices(index[1], a.cols));
      }
    }
    if (a instanceof categories.DiagramGrid) return a.get(Number(index[0]), Number(index[1]));
    // K[x, y]: the polynomial ring over a domain
    if (a instanceof sj.Domain && index.every((g) => g instanceof Sym)) return a.polyRing(...(index as Sym[]));
    if (a instanceof Matrix) {
      const indices = index;
      const n = (v: unknown): number => Number(v);
      if (indices.length === 1) { const k = n(indices[0]); const j = k < 0 ? k + a.rows * a.cols : k; return a.get(Math.floor(j / a.cols), j % a.cols); }
      if (Array.isArray(indices[0]) && Array.isArray(indices[1])) return a.slice(indices[0].map(n), indices[1].map(n));
      return a.get(n(indices[0]), n(indices[1]));
    }
    if (Array.isArray(a) && index.length === 1) {
      const k = Number(index[0]);
      return a[k < 0 ? a.length + k : k];
    }
    if (a instanceof Map) {
      const key = [...a.keys()].find((k) => pyEquals(k, i));
      // a missing key raises like Python's KeyError
      if (key === undefined) throw new RangeError('KeyError: the key is not in the dict');
      return a.get(key);
    }
    if (a instanceof sj.GroebnerBasis || a instanceof sj.ModuleElement) {
      const values = a instanceof sj.GroebnerBasis ? a.exprs : a.data;
      const k = Number(index[0]);
      const value = values[k < 0 ? values.length + k : k];
      if (value === undefined) throw new RangeError('index out of range');
      return value;
    }
    return callMethod(a, a instanceof sj.Transform ? ['at'] : ['getitem', 'get', 'at'], index)?.value ?? unsupportedOp('[]');
  },
  // K(a): an element of a domain or a finite extension
  '.__call__': (a, args) => {
    if (a instanceof sj.LexOrder || a instanceof sj.GradedLexOrder || a instanceof sj.ReversedGradedLexOrder || a instanceof sj.InverseOrder || a instanceof sj.ProductOrder) {
      const tuple = (v: sj.MonomialKey): unknown => Array.isArray(v) ? new JsTuple(v.map(tuple)) : v;
      const monomial = args[0];
      if (!Array.isArray(monomial)) throw new Unsupported('monomial exponent tuple');
      return tuple(a.key(monomial.map(Number)));
    }
    if (a instanceof sj.Poly) {
      let result: sj.Poly | Expr = a;
      for (const x of args) {
        if (!(result instanceof sj.Poly)) throw new RangeError('too many polynomial evaluation arguments');
        result = result.eval(asExpr(x));
      }
      return result;
    }
    return typeof a === 'function' ? a(...args) : a instanceof sj.Domain || a instanceof sj.FiniteExtension ? callMethod(a, ['new'], args.map((x) => x instanceof JsFFElement ? plain(x) : x))?.value : (callMethod(a, ['call', 'apply'], args)?.value ?? unsupportedOp('()'));
  },
};
function unsupportedOp(op: string): never {
  throw new Unsupported(`no adapter for the operator ${op}`);
}

/** SymPy attributes whose symjs function has another name (docs/api-policy.md). */
export const ATTRIBUTE_FUNCTIONS: Readonly<Record<string, string>> = { is_integer: 'isIntegerQ', is_Function: 'isFn', is_Number: 'isNum', canonical: 'canonicalRelation' };
const OPERATOR_METHODS: Readonly<Record<string, string>> = { '.__str__': 'toString', '.__add__': 'add', '.__sub__': 'sub', '.__mul__': 'mul', '.__pow__': 'pow', '.__floordiv__': 'floordiv', '.__mod__': 'mod' };
/** DomainMatrix functions whose integer arguments are sizes, exponents or indices. */
const DOMAIN_MATRIX_INT_FUNCTIONS = new Set(['.eye', '.zeros', '.ones', '.pow', '.getitem', '.from_list_sympy', '.from_dict_sympy', 'sdm_berk']);

/** SymPy names that are JavaScript globals, and the symjs names that do not shadow them. */
export const JS_GLOBAL_RENAMES: Record<string, string> = { Symbol: 'Sym', Number: 'SymNumber', Function: 'SymFunction', Array: 'SymArray', Set: 'SetExpr', Object: 'SymObject' };
/** sympy.vector names that symjs exports under another name (SymPy's top-level Point is the geometric one). */
const VECTOR_RENAMES: Record<string, string> = { Point: 'VectorPoint' };
/** sympy.stats names that symjs exports under another name: E is Euler's number and Chi the hyperbolic cosine integral. */
const STATS_RENAMES: Record<string, string> = { E: 'expectation', probability: 'P', Chi: 'ChiRV' };
/** sympy.combinatorics names that symjs exports under another name (homomorphism and rewrite are taken by agca and simplify). */
const GROUP_RENAMES: Record<string, string> = { homomorphism: 'groupHomomorphism', rewrite: 'reidemeisterRewrite' };
/** sympy.utilities names that symjs exports under another name (replace is the expression operation). */
const UTILITIES_RENAMES: Record<string, string> = { replace: 'replaceString' };
const CATEGORY_RENAMES: Readonly<Record<string, Record<string, string>>> = { vector: VECTOR_RENAMES, stats: STATS_RENAMES, combinatorics: GROUP_RENAMES, utilities: UTILITIES_RENAMES, sets: { SetExpr: 'SetExpression' } };
const camelIn = (n: string, category: string | undefined): string => CATEGORY_RENAMES[category ?? '']?.[n] ?? camel(n);
// (an underscore before a capital is dropped too: solve_linear_system_LU -> solveLinearSystemLU)
const camel = (n: string): string => JS_GLOBAL_RENAMES[n] ?? n.replace(/_([a-zA-Z0-9])/g, (_m, ch: string) => ch.toUpperCase());

/** A deserialized argument as the JS value the API takes. */
function toJs(v: unknown, numbers: boolean, inArray = false): unknown {
  // Python runtime objects used as type filters and sequence callbacks.
  if (v instanceof TypeRef) {
    const builtin = ({ str: String, int: Number, float: Number, bool: Boolean, list: Array, tuple: Array, dict: Map, generator: sj.GeneratorType } as Record<string, unknown>)[v.name];
    if (builtin !== undefined) return builtin;
  }
  if (v instanceof JsFunc && v.name === 'builtins.len') return (x: unknown) => {
    if (typeof x === 'string' || Array.isArray(x)) return x.length;
    if (x instanceof Map || x instanceof Set) return x.size;
    throw new TypeError('len requires a sized value');
  };
  if (v instanceof JsFunc && v.name === '_operator.ge') return (a: number | string, b: number | string) => a >= b;
  // Named series callbacks are callable public algorithms, not harness implementations.
  if (v instanceof TypeRef && (v.name === 'Basic' || v.name === 'Expr')) return v.name;
  if (v instanceof JsFunc && (v.name === 'rs_exp' || v.name === '_tan1')) return v.name === 'rs_exp' ? sj.rsExp : sj.rsTan;
  if ((numbers || inArray) && v instanceof sj.Rational && v.q === 1n) {
    const n = Number(v.p);
    return Number.isSafeInteger(n) ? n : v.p;
  }
  if (v instanceof JsIterator) return (function* () { yield* v.items.map((x) => toJs(x, numbers, true)); })();
  if (v instanceof JsList || v instanceof JsTuple) return v.items.map((x) => toJs(x, numbers, true));
  if (v instanceof JsSet) return new Set(v.items.map((x) => toJs(x, numbers, true)));
  if (v instanceof JsDict) return new Map(v.entries.map(([k, x]) => [toJs(k, numbers, true), toJs(x, numbers, true)]));
  if (v instanceof JsLambda) return (...xs: unknown[]) => xs.some((x) => typeof x === 'string') ? v.callStrings(...xs) : v.call(...xs.map((x) => (typeof x === 'number' ? sj.Rational.of(BigInt(x)) : x)) as Expr[]);
  if (v instanceof JsPred) return (e: Expr) => v.test(e);
  if (v instanceof JsTable) return (...xs: unknown[]) => v.call(...xs);
  if (v instanceof UFnClass) return sj.SymFunction(v.name, { nargs: v.nargs });
  if (v instanceof JsDomain) return v.domain ?? v;
  // a GF(p) element as its integer value (the GF(p) functions take integers and the modulus)
  if (v instanceof JsFFElement) return toJs(sj.Rational.of(v.v), numbers, inArray);
  return v;
}

/** A JS result as the value the formatter compares (generators are materialized). */
function fromJs(v: unknown): unknown {
  if (v !== null && typeof v === 'object' && typeof (v as { next?: unknown }).next === 'function' && typeof (v as { [Symbol.iterator]?: unknown })[Symbol.iterator] === 'function') {
    return new JsList([...(v as Iterable<unknown>)].map(fromJs));
  }
  if (Array.isArray(v)) return new JsList(v.map(fromJs));
  if (v instanceof Map && !(v instanceof JsDict)) return new JsDict([...v].map(([k, x]) => [keyFromJs(k), fromJs(x)]));
  if (v instanceof Set) return new JsSet([...v].map(fromJs));
  if (sj.isNoMatch(v) || sj.isUnsolved(v) || v === 'unknown') return null;
  return v;
}

/** A dict key: arrays are Python tuples. */
const keyFromJs = (k: unknown): unknown => (Array.isArray(k) ? new JsTuple(k.map(keyFromJs)) : fromJs(k));

/** The parameter names of a JS function (from its source). */
function paramNames(f: (...a: unknown[]) => unknown): string[] {
  const src = Function.prototype.toString.call(f);
  const start = src.indexOf('(');
  if (start < 0) return [];
  let depth = 0, token = '';
  const parts: string[] = [];
  for (const ch of src.slice(start + 1)) {
    if (ch === ')' && depth === 0) { parts.push(token); break; }
    if (ch === ',' && depth === 0) { parts.push(token); token = ''; continue; }
    token += ch;
    if ('([{'.includes(ch)) depth++;
    if (')]}'.includes(ch)) depth--;
  }
  // Parameters copied to locals are named xIn (no-param-reassign).
  return parts.map((p) => p.trim().replace(/^\.\.\./, '').split(/[=\s:]/)[0]!.replace(/In$/, '')).filter(Boolean);
}

/** Positional arguments and keywords: a keyword naming a parameter goes to its position, the rest form an options object. */
function placeArgs(f: (...a: unknown[]) => unknown, args: unknown[], kw: Record<string, unknown>, conv: (x: unknown) => unknown): unknown[] {
  const out = args.map(conv);
  const names = paramNames(f);
  const opts: Record<string, unknown> = {};
  for (const [k, x] of Object.entries(kw)) {
    const i = names.indexOf(camel(k));
    if (i >= 0 && i >= args.length && !/^(opts|options)$/.test(names[i]!)) out[i] = conv(x);
    else opts[camel(k)] = conv(x);
  }
  if (Object.keys(opts).length) {
    // the options object goes to the parameter named opts/options, else last
    const k = names.findIndex((n) => /^(opts|options)$/.test(n));
    if (k >= out.length) out[k] = opts;
    else out.push(opts);
  }
  for (let i = 0; i < out.length; i++) if (!(i in out)) out[i] = undefined;
  return out;
}

/**
 * The helpers of sympy.integrals.intpoly (decompose, intersection, norm, ...) share names with other
 * SymPy functions: they are reached through the `intpoly` namespace, with integers as JS numbers
 * (indices, degrees and coordinates).
 */
function intpolyAdapter(c: Case): Adapter | undefined {
  const f = (sj.intpoly as unknown as Record<string, unknown>)[camel(c.fn)];
  if (typeof f !== 'function') return undefined;
  const g = f as (...a: unknown[]) => unknown;
  return (args, kw) => fromJs(g(...placeArgs(g, args, kw, (x) => toJs(x, true))));
}

function fromPolyAdapter(args: unknown[], kw: Record<string, unknown>, self?: unknown): unknown {
  for (const k of Object.keys(kw)) if (!['gens', 'domain', 'field', 'modulus'].includes(k)) throw new Unsupported(`kwargs ${k}`);
  if (self !== sj.Poly && !(self instanceof TypeRef && ['Poly', 'PurePoly'].includes(self.name))) throw new Unsupported('from_poly receiver');
  const p = asPoly(args[0]);
  const gens = kw['gens'] === undefined ? args.slice(1) : [kw['gens']];
  const gs = gens.flatMap((g) => g instanceof JsTuple ? g.items.map(asExpr) : [asExpr(g)]);
  const same = !gs.length || gs.length === p.gens.length && gs.every((g) => p.gens.some((x) => x.key === g.key));
  return sj.Poly.from(p.asExpr(), gs.length ? gs : p.gens, {
    ...(same ? { domain: p.domain } : {}), ...polynomialOptions(kw),
    ...(kw['field'] === undefined ? {} : { field: Boolean(kw['field']) }),
    pure: self instanceof TypeRef ? self.name === 'PurePoly' : false,
  });
}

function autoAdapter(c: Case): Adapter | undefined {
  if (c.self?.t === 'PolyRing' && c.fn === '.dup_isolate_real_roots_list') return (args, kw, self) => {
    const ring = self as sj.PolyRing;
    if (!['ZZ', 'QQ'].includes(String(ring.domain))) throw new sj.DomainError('root isolation requires ZZ or QQ');
    const rational = (v: unknown): sj.Rational => v instanceof sj.PythonMPQ ? sj.Rational.of(v.numerator, v.denominator) : asExpr(v) as sj.Rational;
    const optional = (v: unknown): sj.Rational | undefined => v === undefined || v === null ? undefined : rational(v);
    const polys = (args[0] as JsList | JsTuple).items.map((v) => sj.Poly.from(v instanceof sj.PolyElement ? v.asExpr() : asExpr(v), [...ring.symbols]).allCoeffs().map(rational));
    const roots = sj.isolateRealRootsList(polys, { eps: optional(kw['eps']), inf: optional(kw['inf']), sup: optional(kw['sup']), fast: kw['fast'] === true, strict: kw['strict'] === true });
    return fromJs(kw['basis'] === true ? roots : roots.map(([iv, indices]) => [iv, indices]));
  };
  if (c.fn === 'heugcd') return (args, kw) => {
    noKw(kw);
    const f = args[0] as sj.PolyElement;
    return fromJs(f.ring.dmpZzHeuGcd(f, args[1] as sj.PolyElement));
  };
  if (c.self?.t === 'PolyRing' && ['.dup_isolate_real_roots_sqf', '.dup_isolate_real_roots', '.dup_refine_real_root', '.dup_count_real_roots', '.dup_count_complex_roots'].includes(c.fn)) return (args, kw, self) => {
    const ring = self as sj.PolyRing;
    if (!['ZZ', 'QQ'].includes(String(ring.domain))) throw new sj.DomainError('root isolation requires ZZ or QQ');
    const f = args[0] instanceof sj.PolyElement ? args[0].asExpr() : asExpr(args[0]);
    const p = sj.Poly.from(f, [...ring.symbols], { domain: String(ring.domain) });
    const rational = (v: unknown): sj.Rational => v instanceof sj.PythonMPQ ? sj.Rational.of(v.numerator, v.denominator) : asExpr(v) as sj.Rational;
    const optional = (v: unknown): sj.Rational | undefined => v === undefined || v === null ? undefined : rational(v);
    if (c.fn === '.dup_count_complex_roots') {
      const corner = (v: unknown): [sj.Rational, sj.Rational] | undefined => v === undefined || v === null ? undefined : (v as JsTuple).items.map(rational) as [sj.Rational, sj.Rational];
      const exclude = kw['exclude'];
      return sj.countComplexRoots(p.allCoeffs().map(rational), corner(args[1] ?? kw['inf']), corner(args[2] ?? kw['sup']), exclude instanceof JsList || exclude instanceof JsTuple ? exclude.items.map(String) : exclude === true);
    }
    if (c.fn === '.dup_count_real_roots') return p.countRoots(optional(args[1] ?? kw['inf']), optional(args[2] ?? kw['sup']));
    if (c.fn === '.dup_refine_real_root') {
      const coefficients = p.clearDenoms(true)[1].allCoeffs().map((v) => rational(v).p);
      return fromJs(sj.refineRealRoot(coefficients, rational(args[1]), rational(args[2]), {
        eps: optional(kw['eps']), steps: kw['steps'] === undefined ? undefined : intArg(kw['steps']),
        disjoint: optional(kw['disjoint']), fast: kw['fast'] === true,
      }));
    }
    const opts = { eps: optional(kw['eps']), inf: optional(kw['inf']), sup: optional(kw['sup']), fast: kw['fast'] === true };
    if (kw['basis'] === true) return fromJs(sj.isolateRealRootsList([p.allCoeffs().map(rational)], opts).map(([iv, indices, basis]) => {
      const multiplicity = indices.get(0);
      if (multiplicity === undefined) throw new TypeError('missing polynomial index in root isolation');
      return [iv, multiplicity, basis];
    }));
    const integers = (poly: sj.Poly): bigint[] => poly.clearDenoms(true)[1].allCoeffs().map((v) => rational(v).p);
    if (c.fn === '.dup_isolate_real_roots_sqf') return fromJs(sj.isolateRealRootsSqf(integers(p), opts));
    const factors = new sj.UPoly(p.allCoeffs().map(rational).reverse()).squareFree();
    return fromJs(sj.isolateRealRoots(factors.map(([factor, k]) => [integers(sj.Poly.fromList([...factor.coeffs].reverse(), [...ring.symbols])), k]), opts.eps, opts));
  };
  if (c.category === 'polys' && c.fn === '.from_poly' && c.self?.t === 'Type' && ['Poly', 'PurePoly'].includes(String(c.self['name']))) return fromPolyAdapter;
  if (c.fn === 'xypic_draw_diagram') return (args, kw) => categories.xypicDrawDiagram(args[0] as sj.Diagram, Object.fromEntries(Object.entries(kw).map(([k, v]) => [camel(k), toJs(v, true)])));
  if (c.module.startsWith('sympy.plotting.intervalmath.') && ['And', 'Or', 'intervalMembership'].includes(c.fn)) {
    // Python's None is the third truth value of interval membership
    const truth = (v: unknown): sj.Truth => v === null || v === undefined ? 'unknown' : v === true;
    const membership = (v: unknown): plotting.intervalmath.intervalMembership =>
      v instanceof plotting.intervalmath.intervalMembership ? v : new plotting.intervalmath.intervalMembership(truth((v as JsTuple).items[0]), truth((v as JsTuple).items[1]));
    const tuple = (m: plotting.intervalmath.intervalMembership): JsTuple => new JsTuple([m.value, m.isValid].map((v) => v === 'unknown' ? null : v));
    if (c.fn === 'intervalMembership') return (args) => new plotting.intervalmath.intervalMembership(...(args.map(truth) as [sj.Truth, sj.Truth]));
    const f = c.fn === 'And' ? plotting.intervalmath.And : plotting.intervalmath.Or;
    return (args) => tuple(f(...args.map(membership)));
  }
  if (c.category === 'plotting') {
    const f = (plotting as unknown as Record<string, (...args: unknown[]) => unknown>)[camel(c.fn)];
    if (f) return (args, kw) => {
      const value = f(...placeArgs(f, args, kw, (x) => toJs(x, true)));
      if (c.fn === 'check_arguments') return new JsList((value as unknown[][]).map((row) => new JsTuple(row.map((v) => Array.isArray(v) ? new JsTuple(v) : v))));
      return fromJs(value);
    };
  }
  if (c.fn === 'smoothness_p') return (args, kw) => {
    const flag = (v: unknown): boolean => v === true || (v instanceof sj.Rational && !v.isZero);
    const opts = { ...(kw['m'] === undefined ? {} : { m: intArg(kw['m']) }), power: flag(kw['power']) };
    return fromJs(flag(kw['visual']) ? sj.smoothnessP(asExpr(args[0]), { ...opts, visual: true }) : sj.smoothnessP(asExpr(args[0]), opts));
  };
  // SymPy's class flag is_Relational is an instance test of the relation class
  if (c.fn === '.is_Relational') return (_args, kw, self) => (noKw(kw), self instanceof sj.Rel);
  if (c.fn === '.kind') return (_args, kw, self) => (noKw(kw), sj.kindOf(asExpr(self)));
  if (c.fn === '.nargs') return (_args, kw, self) => (noKw(kw), sj.nargs(self instanceof UFnClass ? sj.SymFunction(self.name, { nargs: self.nargs }) : self as sj.WildFunction));
  const numbers = NUMERIC_CATEGORIES.has(c.category) || NUMERIC_FUNCTIONS.has(c.fn) || (c.module.startsWith('sympy.polys.matrices.') && DOMAIN_MATRIX_INT_FUNCTIONS.has(c.fn));
  const conv = (x: unknown): unknown => {
    // the evaluating constructors of the arithmetic classes (Python calls the class: Pow(b, e))
    const constructors: Readonly<Record<string, unknown>> = { Add: sj.add, Mul: sj.mul, Pow: sj.pow };
    if (c.fn === 'unchanged' && (x instanceof FnClass || x instanceof TypeRef)) return constructors[x.name] ?? (sj as unknown as Record<string, unknown>)[camel(x.name)];
    if (c.fn === 'ElementwiseApplyFunction' && x instanceof FnClass) return (e: Expr) => applyFn(x.name, [e]);
    // The dense tools keep GF(p) coefficients as field elements: a zero-order derivative returns them unchanged.
    const fieldElements = (v: unknown): unknown => v instanceof JsFFElement ? plain(v) : v instanceof JsList ? new JsList(v.items.map(fieldElements)) : v instanceof JsTuple ? new JsTuple(v.items.map(fieldElements)) : v;
    const converted = toJs(c.module === 'sympy.polys.tests.test_densetools' ? fieldElements(x) : x, numbers);
    // The public sparse-ring APIs use Expr coefficients/exponents. Python's
    // ground-domain MPQ wrapper is only a serialized input representation.
    const rationalInputs = (v: unknown): unknown => {
      if (v instanceof sj.PythonMPQ) return sj.Rational.of(v.numerator, v.denominator);
      if (Array.isArray(v)) return v.map(rationalInputs);
      if (v instanceof Map) return new Map([...v].map(([k, a]) => [rationalInputs(k), rationalInputs(a)]));
      return v;
    };
    const expressionCoefficients = ['sympy.polys.puiseux', 'sympy.polys.ring_series', 'sympy.polys.densearith', 'sympy.polys.matrices.dense', 'sympy.polys.densebasic', 'sympy.polys.rootisolation'];
    const polynomialInputs = (v: unknown): unknown => {
      if (v instanceof sj.PolyElement) return v.asExpr();
      if (Array.isArray(v)) return v.map(polynomialInputs);
      return v;
    };
    const normalized = c.module === 'sympy.polys.densebasic' || c.module === 'sympy.polys.tests.test_densetools' || c.fn === '.to_sympy' ? polynomialInputs(converted) : converted;
    return expressionCoefficients.includes(c.module) || c.module.startsWith('sympy.polys.matrices.') ? rationalInputs(normalized) : normalized;
  };
  const dunder = c.fn === '.__str__' ? undefined : DUNDER[c.fn];
  // Python int comparisons defer to a symbolic right operand's reflected method.
  const reflectedNames: Readonly<Record<string, string>> = { '.__lt__': '.__gt__', '.__le__': '.__ge__', '.__gt__': '.__lt__', '.__ge__': '.__le__' };
  const reflectedName = reflectedNames[c.fn];
  const reflected = reflectedName === undefined ? undefined : DUNDER[reflectedName];
  if (reflected !== undefined && c.self?.t === 'Rational' && c.self['py'] === true) return (args, _kw, self) => fromJs(reflected(plain(conv(args[0])), [self]));
  if (dunder !== undefined) return (args, _kw, self0) => fromJs(dunder(plain(self0 instanceof JsDomain ? (self0.domain ?? self0) : self0), args.map((a) => a instanceof JsFFElement ? plain(a) : plain(conv(a)))));
  if (c.fn.startsWith('.')) {
    const name = OPERATOR_METHODS[c.fn] ?? camel(c.fn.slice(1));
    return (args, kw, self0) => {
      // a static method called on the class (Permutation.unrank_lex, ...)
      const self = self0 instanceof JsTuple ? sj.Tuple(...self0.items.map(asExpr)) : self0 instanceof TypeRef ? (sj as unknown as Record<string, unknown>)[self0.name] : self0 instanceof JsDomain ? (self0.domain ?? self0) : self0 instanceof JsLambda ? sj.Lambda(self0.vars, self0.body) : self0;
      if (self === null || (typeof self !== 'object' && typeof self !== 'function')) throw new Unsupported(`no adapter for ${c.fn}`);
      if (name === 'arguments' && self instanceof sj.AppliedPredicate) return new JsTuple(self.arguments);
      if (name === 'func' && self instanceof sj.CRootOf) return new TypeRef('polys.rootoftools.ComplexRootOf');
      // SymPy expr.func read as a value: the class or function, printed as SymPy prints it
      if (name === 'func' && args.length === 0 && self instanceof sj.Expr) {
        const head = self.func;
        const cls = HEAD_CLASSES.get(head);
        if (cls !== undefined) return new TypeRef(cls);
        if (typeof (head as { functionName?: unknown }).functionName === 'string') return head;
        if (self instanceof sj.AppliedFunction) return new FnClass(self.name);
      }
      // expr.func(*expr.args): a Lambda argument stays the same Lambda node (SymPy passes the arg itself)
      if (name === 'func' && args.length > 0 && self instanceof sj.Expr) {
        const head = self.func as (...a: unknown[]) => unknown;
        return fromJs(head(...args.map((a) => (a instanceof JsLambda ? sj.Lambda(a.vars, a.body) : conv(a)))));
      }
      // SymPy names with an uppercase word (to_Matrix -> toMatrix)
      if (name === 'name' && typeof self === 'function' && 'predicateName' in self) return new Sym(String(self.predicateName));
      const upper = name.replace(/_([A-Z])/g, (_m, ch: string) => ch);
      let m = (self as Record<string, unknown>)[name] ?? (self as Record<string, unknown>)[upper];
      if (self instanceof sj.Poly && (name === 'domain' || name === 'getDomain')) return (noKw(kw), new UFnClass(self.domain));
      if (self instanceof sj.Poly && name === 'rep') {
        noKw(kw);
        const finite = /^GF\((\d+)\)$/.exec(self.domain);
        const known: Record<string, sj.Domain> = { RR: sj.RR, CC: sj.CC, EX: sj.EX, ZZ_I: sj.ZZ_I, QQ_I: sj.QQ_I };
        const K = finite ? sj.GF(BigInt(definedOr(finite[1], 'finite modulus'))) : known[self.domain] ?? new sj.PolyRing([], self.domain).domain;
        const ring = new sj.PolyRing(self.gens, K);
        const dense = (v: unknown): unknown => Array.isArray(v) ? new JsList(v.map(dense)) : K instanceof sj.RealField ? { toString: () => K.dtype(v).repr() } : K.convert(v);
        const rep = dense(ring.fromExpr(self.asExpr()).toDense());
        return { toString: () => `DMP_Python(${fmt(rep)}, ${K.toString()})` };
      }
      if (self instanceof sj.SATSolver && name === 'litHeap') return new JsList(self.litHeap.map(([score, lit]) => new JsTuple([new JsFloat(score), lit])));
      if (self instanceof sj.SATSolver && name === 'litScores') return new JsDict([...self.litScores].map(([lit, score]) => [lit, new JsFloat(score)]));
      if (self instanceof sj.CNF && name === 'clauses') return new JsSet(self.clauses.map((clause) => new JsFrozenSet(clause)));
      let thisArg: unknown = self;
      // an instance method called on the class with the instance first (Quaternion.arc_coplanar(q1, q2))
      const proto = typeof self === 'function' ? (self as { prototype?: Record<string, unknown> }).prototype : undefined;
      if (m === undefined && proto !== undefined && typeof proto[name] === 'function' && args[0] instanceof (self as new (...a: unknown[]) => object)) {
        const g = proto[name] as (...a: unknown[]) => unknown;
        return fromJs(g.call(args[0], ...placeArgs(g, args.slice(1), kw, conv)));
      }
      // a classmethod called on an instance (p.unrank_lex(...))
      if (m === undefined && typeof self === 'object') {
        thisArg = (self as object).constructor;
        m = (thisArg as Record<string, unknown>)[name];
      }
      // a classmethod ported as a function (MatrixExpr.from_index_summation -> fromIndexSummation)
      if (m === undefined && typeof self === 'function' && typeof (sj as unknown as Record<string, unknown>)[name] === 'function') {
        const g = (sj as unknown as Record<string, (...a: unknown[]) => unknown>)[name]!;
        return fromJs(g(...placeArgs(g, args, kw, conv)));
      }
      if (typeof m === 'function') {
        if (self instanceof sj.AppliedPredicate && name === 'function') return m;
        // a getter returning a function class (SymPy expr.func): the attribute value, not a call
        if (args.length === 0 && typeof (m as { functionName?: unknown }).functionName === 'string') return m;
        const method = m as (...a: unknown[]) => unknown;
        const placed = placeArgs(method, args, kw, conv);
        // Python IPolys accepts ground constants where a polynomial is expected.
        if (self instanceof sj.PolyRing && /^(dup|dmp)[A-Z]/.test(name)) {
          const names = paramNames(method);
          for (let i = 0; i < placed.length; i++) {
            if (/^(f|g|h)$/.test(names[i] ?? '')) {
              const value = placed[i];
              if (value instanceof sj.PythonMPQ) placed[i] = self.groundNew(sj.Rational.of(value.numerator, value.denominator));
              else if (value instanceof sj.Expr || typeof value === 'number' || typeof value === 'bigint') placed[i] = self.fromExpr(value);
            }
          }
        }
        const result = method.call(thisArg, ...placed);
        // AGCA uses expression coefficients publicly. SymPy prints these as
        // dense DMP objects inside its relation containers; only convert the
        // representation here, using the public sparse-to-dense conversion.
        if (self instanceof sj.SubModule && Array.isArray(result) && (name === 'intersect' || name === 'moduleQuotient')) {
          const K = self.context.domain;
          const R = new sj.PolyRing(self.context.symbols, K);
          const dense = (value: unknown): unknown => Array.isArray(value) ? new JsList(value.map(dense)) : K.convert(value);
          const coefficient = (e: Expr): unknown => ({ toString: () => `DMP_Python(${fmt(dense(R.fromExpr(e).toDense()))}, ${String(K)})` });
          return new JsTuple([result[0], ...result.slice(1).map((rows: Expr[][]) => new JsList(rows.map((row) => name === 'intersect' ? new JsTuple(row.map(coefficient)) : new JsList(row.map(coefficient)))))]);
        }
        return fromJs(result);
      }
      // an assumption attribute without a query function of its own is the predicate asked of the
      // expression (x.is_even -> ask(Q.even(x)); symjs isRational is the class test is_Rational)
      const predicate = /^is_([a-z_]+)$/.exec(c.fn.slice(1))?.[1];
      if (m === undefined && args.length === 0 && predicate !== undefined && self instanceof sj.Expr && sj.Q[predicate] !== undefined
        && (predicate === 'rational' || typeof (sj as unknown as Record<string, unknown>)[ATTRIBUTE_FUNCTIONS[c.fn.slice(1)] ?? name] !== 'function')) {
        return fromJs(sj.ask(sj.Q[predicate](self)));
      }
      // a SymPy method or attribute that symjs exports as a function of the object (x.is_real -> isReal(x),
      // M.is_positive_definite -> isPositiveDefinite(M); docs/api-policy.md)
      const asFunction = (sj as unknown as Record<string, unknown>)[ATTRIBUTE_FUNCTIONS[c.fn.slice(1)] ?? name] ?? (sj as unknown as Record<string, unknown>)[upper];
      if (m === undefined && typeof asFunction === 'function' && typeof self === 'object') {
        const g = asFunction as (...a: unknown[]) => unknown;
        // keyword arguments go to the trailing options object, as in the other function adapters
        const opts = Object.fromEntries(Object.entries(kw).map(([k, v]) => [camel(k), conv(v)]));
        return fromJs(g(self, ...args.map(conv), ...(Object.keys(opts).length ? [opts] : [])));
      }
      if (name === 'args' && Array.isArray(m)) return new JsTuple(m);
      if (m === undefined || args.length) throw new Unsupported(`no adapter for ${c.fn}`);
      return fromJs(m);
    };
  }
  const f = (publicApi as unknown as Record<string, unknown>)[camelIn(c.fn, c.category)] ?? (publicApi as unknown as Record<string, unknown>)[c.fn];
  if (f instanceof sj.Domain) return (args) => fromJs(f.new(...args.map(conv)));
  if (typeof f !== 'function') return undefined;
  const isClass = /^class[\s{]/.test(Function.prototype.toString.call(f));
  return (args, kw) => {
    const a = placeArgs(f as (...a: unknown[]) => unknown, args, kw, conv);
    return fromJs(isClass ? new (f as new (...a: unknown[]) => unknown)(...a) : (f as (...a: unknown[]) => unknown)(...a));
  };
}

/** Explicit public aliases: an adapter by itself is never evidence of an API. */
export const PUBLIC_ALIASES: Readonly<Record<string, string>> = {
  _linear_eq_to_dict: '_linearEqToDict', _lin_eq2dict: '_linEq2dict',
  Catalan: 'S.Catalan', EulerGamma: 'S.EulerGamma', GoldenRatio: 'S.GoldenRatio', TribonacciConstant: 'S.TribonacciConstant',
  Integer: 'Rational.of', Equality: 'Eq', Unequality: 'Ne', GreaterThan: 'Ge', LessThan: 'Le', StrictGreaterThan: 'Gt', StrictLessThan: 'Lt',
  N: 'evalf', ln: 'log', minpoly: 'minimalPolynomial', poly: 'Poly.from',
  heugcd: 'IPolys.prototype.dmpZzHeuGcd',
  zeros: 'Matrix.zeros', ones: 'Matrix.ones', eye: 'Matrix.eye', diag: 'Matrix.diag',
  true: 'S.true', false: 'S.false', FallingFactorial: 'ff', RisingFactorial: 'rf',
};
function publicPathExists(path: string): boolean {
  let value: unknown = publicApi;
  for (const key of path.split('.')) {
    if (value === null || (typeof value !== 'object' && typeof value !== 'function') || !(key in value)) return false;
    value = (value as Record<string, unknown>)[key];
  }
  return value !== undefined;
}
const exprMethods = ['diff', 'integrate', 'limit', 'series', 'expand', 'simplify', 'factor', 'collect', 'cancel', 'apart', 'ratsimp', 'together', 'trigsimp', 'powsimp', 'radsimp', 'nsimplify', 'logcombine', 'powdenest', 'rewrite', 'refine', 'evalf',
      'adjoint', 'argsCnc', 'asBaseExp', 'asCoeffAdd', 'asCoeffMul', 'asCoeffExponent', 'asCoefficient', 'asCoefficientsDict', 'asContentPrimitive', 'asDummy', 'asIndependent', 'asLeadingTerm', 'asNumerDenom', 'asPoly', 'asPowersDict', 'asRealImag', 'asTerms', 'aseries', 'atoms', 'classKey', 'coeff', 'combsimp', 'compare', 'couldExtractMinusSign', 'count', 'countOps', 'dir', 'doit', 'dummyEq', 'extractAdditively', 'extractBranchFactor', 'extractMultiplicatively', 'find', 'fourierSeries', 'fps', 'gammasimp', 'getO', 'getn', 'hasFree', 'hasXfree', 'invert', 'isAlgebraicExpr', 'isConstant', 'isHypergeometric', 'isMeromorphic', 'isPolynomial', 'isRationalFunction', 'isSame', 'leadterm', 'lseries', 'match', 'matches', 'normal', 'primitive', 'rcall', 'removeO', 'replace', 'round', 'separate', 'sortKey', 'taylorTerm', 'transpose', 'xreplace',
      'asExpr', 'asOrderedFactors', 'asOrderedTerms', 'copy', 'nseries'];
export const MEMBER_FUNCTIONS: Readonly<Record<string, readonly string[]>> = {
    Expr: exprMethods,
    Matrix: ['doit', 'berkowitz', 'berkowitzEigenvals', 'berkowitzMinors', 'companion', 'connectedComponents', 'elementaryColOp', 'elementaryRowOp', 'inverseADJ', 'inverseBLOCK', 'inverseCH', 'inverseGE', 'inverseLDL', 'inverseLU', 'inverseQR', 'irregular', 'iterItems', 'iterValues', 'jordanBlock', 'jordanCell', 'key2bounds', 'key2ij', 'per', 'permuteBkwd', 'permuteFwd', 'printNonzero', 'refine', 'singularValueDecomposition', 'stronglyConnectedComponents', 'table', 'toDM', 'upperHessenbergDecomposition', 'wilkinson', 'analyticFunc', 'bidiagonalDecomposition', 'bidiagonalize', 'cholesky', 'choleskySolve', 'cofactor', 'colInsert', 'columnspace', 'conditionNumber', 'connectedComponentsDecomposition', 'cramerSolve', 'cross', 'diagonal', 'diagonalSolve', 'diagonalize', 'dot', 'dual', 'echelonForm', 'eigenvects', 'extract', 'gaussJordanSolve', 'getDiagBlocks', 'hat', 'invMod', 'isAntiSymmetric', 'isDiagonal', 'isDiagonalizable', 'isNilpotent', 'isSymmetric', 'jacobian', 'jordanCells', 'jordanForm', 'leftEigenvects', 'lll', 'lllTransform', 'lowerTriangular', 'lowerTriangularSolve', 'minorSubmatrix', 'multiplyElementwise', 'norm', 'normalized', 'nullspace', 'orthogonalize', 'permanent', 'permuteCols', 'permuteRows', 'pinv', 'pinvSolve', 'project', 'rank', 'rankDecomposition', 'rref', 'rrefRhs', 'rowInsert', 'rowspace', 'singularValues', 'solveLeastSquares', 'stronglyConnectedComponentsDecomposition', 'upperTriangular', 'upperTriangularSolve', 'vech', 'vec'],
    MatrixExpr: ['fromIndexSummation', ...exprMethods],
  };
export const MATRIX_MEMBER_ALIASES: Readonly<Record<string, string>> = {
    LUdecomposition: 'luDecomposition', LDLdecomposition: 'ldl', QRdecomposition: 'qrDecomposition', LUdecompositionFF: 'LUdecompositionFF', LUdecompositionSimple: 'LUdecompositionSimple',
    LUsolve: 'matrixSolve', QRsolve: 'matrixSolve', LDLsolve: 'matrixSolve', solve: 'matrixSolve', exp: 'matrixExp', log: 'matrixLog',
    applyfunc: 'Matrix.prototype.map', colJoin: 'Matrix.prototype.vstack', rowJoin: 'Matrix.prototype.hstack',
    berkowitzCharpoly: 'Matrix.prototype.charpoly', berkowitzDet: 'Matrix.prototype.det', detLUDecomposition: 'Matrix.prototype.det', detBareis: 'Matrix.prototype.det',
  };

/** The actual public export/member supporting a name, or undefined when absent. */
export function counterpartFor(a: { name: string; owner?: string; category?: string }): string | undefined {
  if (camel(a.name) in categories && ['DiagramGrid', 'XypicDiagramDrawer', 'xypicDrawDiagram', 'ArrowStringDescription'].includes(camel(a.name))) return 'categories.' + camel(a.name);
  if (a.category === 'plotting' && camel(a.name) in plotting) return 'plotting.' + camel(a.name);
  const camelMethod = (n: string): string => n.replace(/_([a-zA-Z0-9])/g, (_m, c: string) => c.toUpperCase());
  if (a.category === 'diffgeom' && !a.name.startsWith('.')) {
    const name = camel(a.name);
    return name in diffgeomNamespace ? `@symjs/symjs/diffgeom.${name}` : undefined;
  }
  if (!a.name.startsWith('.')) {
    const alias = PUBLIC_ALIASES[a.name];
    const candidates = [camelIn(a.name, a.category), ...(alias ? [alias] : [])];
    if (!(a.name in JS_GLOBAL_RENAMES)) candidates.push(a.name);
    if (a.category === 'polys') candidates.push('Poly.prototype.' + camelMethod(a.name));
    return candidates.find(publicPathExists);
  }
  const m = camelMethod(a.name.slice(1));
  const owners: Record<string, string> = { Expr: 'Expr', MutableDenseMatrix: 'Matrix', Matrix: 'Matrix', ImmutableDenseNDimArray: 'ImmutableDenseNDimArray', Permutation: 'Permutation', MatrixExpr: 'MatrixExpr' };
  const owner = owners[a.owner ?? ''];
  if (!owner) return undefined;
  const candidates = [`${owner}.prototype.${m}`, `${owner}.${m}`, `${owner}.prototype.${a.name.slice(1)}`];
  // SymPy's mutable matrix methods (row_swap, fill, ...) are members of the mutable class
  if (a.owner === 'MutableDenseMatrix') candidates.push(`MutableDenseMatrix.prototype.${m}`, `MutableDenseMatrix.prototype.${a.name.slice(1)}`);
  // Expression operations may be exposed as free functions. Their concrete path
  // is reported, so a function counterpart is not confused with a fluent method.
  // SymPy's MatrixExpr derives from Expr: its Expr methods are the same functions
  if (MEMBER_FUNCTIONS[owner]?.includes(m)) candidates.push(m);
  if (owner === 'Matrix' && MATRIX_MEMBER_ALIASES[m]) candidates.push(MATRIX_MEMBER_ALIASES[m]!);
  return candidates.find(publicPathExists);
}
export function hasCounterpart(a: { name: string; owner?: string; category?: string }): boolean {
  return counterpartFor(a) !== undefined;
}

export type Outcome = { status: 'pass' } | { status: 'equivalent'; got: string } | { status: 'fail'; got: string } | { status: 'unsupported'; reason: string } | {
  status: 'error';
  reason: string;
};

/**
 * The position of a case among the corpus cases with the same module and
 * source (a doctest source that occurs several times, after different setup
 * lines, has one port per occurrence).
 */
function occurrence(c: Case): number {
  occurrenceCorpus ??= (JSON.parse(readFileSync(new URL('./corpus.json', import.meta.url), 'utf8')) as { cases: Case[] }).cases;
  const same = occurrenceCorpus.filter((d) => d.module === c.module && d.src === c.src);
  return Math.max(0, same.findIndex((d) => d.expected === c.expected));
}
let occurrenceCorpus: Case[] | undefined;

/** Optional observation for assertion corpora; deserialization failures are not API exceptions. */
export type CaseObservation = { value: unknown } | { error: unknown };

export function runCase(c: Case, observe?: (event: CaseObservation) => void): Outcome {
  return asDoctest(c, () => runCase0(c, observe));
}

function isIterableResult(value: unknown): value is Iterable<unknown> {
  return typeof value === 'string' || (value !== null && typeof value === 'object'
    && Symbol.iterator in value && typeof value[Symbol.iterator] === 'function');
}

/** Replay Python's flat unpacking without indexing formatted output. */
function pickResult(value: unknown, index: number): unknown {
  if (!Number.isSafeInteger(index) || index < 0) throw new RangeError(`pick ${index}: expected a nonnegative integer index`);
  if (value instanceof JsTuple || value instanceof JsList || Array.isArray(value)) {
    const items = Array.isArray(value) ? value : value.items;
    if (index >= items.length) throw new RangeError(`pick ${index}: result has only ${items.length} items`);
    return fromJs(items[index]);
  }
  if (isIterableResult(value)) {
    let position = 0;
    for (const item of value) {
      if (position++ === index) return fromJs(item);
    }
    throw new RangeError(`pick ${index}: result has only ${position} items`);
  }
  throw new TypeError(`pick ${index}: call result is not indexable (expected an array, tuple or iterable)`);
}

/** The items of a result that Python iterates (a list, tuple, matrix or other iterable). */
function resultItems(value: unknown, post: string): readonly unknown[] {
  if (value instanceof JsTuple || value instanceof JsList) return value.items;
  if (isIterableResult(value) && typeof value !== 'string') return [...value];
  throw new TypeError(`${post}: call result is not iterable`);
}

/** Apply the Python builtin of an assertion (len, list, tuple, element-wise str) to a call result. */
/**
 * The result with its JS arrays (and the JsLists converted from them) as the Python lists and tuples
 * they stand for: the containers take the recorded kinds in preorder (an array beyond them prints as
 * a tuple, like any result). A JsTuple built by an adapter keeps its own kind.
 */
function withBrackets(value: unknown, kinds: string): unknown {
  let next = 0;
  const kind = (): string | undefined => kinds[next++];
  const walk = (v: unknown): unknown => {
    if (Array.isArray(v) || v instanceof JsList) {
      const isList = kind() === 'l';
      return new JsTuple((Array.isArray(v) ? v : v.items).map(walk), isList);
    }
    if (v instanceof JsTuple) {
      kind();
      return new JsTuple(v.items.map(walk), v.isList);
    }
    if (v instanceof Map || v instanceof JsDict) return new JsDict([...(v instanceof Map ? v : v.entries)].map(([k, x]) => [walk(k), walk(x)]));
    if (v instanceof Set || v instanceof JsSet) return new JsSet([...(v instanceof Set ? v : v.items)].map(walk));
    return v;
  };
  return walk(value);
}

function projectResult(value: unknown, post: NonNullable<Case['post']>, brackets = ''): unknown {
  // Python's str() and repr() of a SymPy object are its sstr form, printed by symjs's str printer;
  // inside containers (and for repr) items print by repr: quoted strings, Permutation(1, 2), ...
  if (post === 'str') return typeof value === 'string' ? value : fmt(withBrackets(value, brackets));
  if (post === 'repr') return fmtItem(withBrackets(value, brackets));
  if (post === 'len') {
    if (typeof value === 'string') return value.length;
    if (value instanceof Map || value instanceof Set) return value.size;
    if (value instanceof JsDict) return value.entries.length;
    if (value instanceof JsSet) return value.items.length;
    if (value !== null && typeof value === 'object' && 'length' in value && typeof value.length === 'number' && !(Symbol.iterator in value)) return value.length;
    return resultItems(value, post).length;
  }
  const items = resultItems(value, post);
  if (post === 'list') return new JsList(items.map(fromJs));
  if (post === 'tuple') return new JsTuple(items.map(fromJs));
  return new JsList(items.map((item) => { const v = fromJs(item); return typeof v === 'string' ? v : fmt(v); }));
}

function runCase0(c: Case, observe?: (event: CaseObservation) => void): Outcome {
  const portEntry = PORTS[`${c.module}:${c.src}`];
  const port = Array.isArray(portEntry) ? (portEntry as readonly (() => unknown)[])[occurrence(c)] : (portEntry as (() => unknown) | undefined);
  if (port) {
    // a doctest that needs Python code (classes, lambdas) runs as its JavaScript translation
    try {
      const result = port();
      const picked = c.pick === undefined ? result : pickResult(result, c.pick);
      const v = fromJs(c.post === undefined ? picked : projectResult(picked, c.post, c.brackets));
      if (c.post === 'str' || c.post === 'repr') return v === c.expected ? { status: 'pass' } : { status: 'fail', got: String(v) };
      return (c.text ? textMatches(v, c) : matches(v, c.expected)) ? { status: 'pass' } : { status: 'fail', got: typeof v === 'string' ? v : fmt(v) };
    } catch (e) {
      return { status: 'error', reason: e instanceof Error ? e.message : String(e) };
    }
  }
  if (c.unsupportedArg) return { status: 'unsupported', reason: `argument type ${c.unsupportedArg}` };
  // a sympy.stats name that symjs exports under another name (stats E is the expectation, not the constant)
  const adapter = diffgeomAdapter(c) ?? (c.module === 'sympy.integrals.intpoly' ? intpolyAdapter(c) : undefined) ?? (c.category === 'stats' && STATS_RENAMES[c.fn] !== undefined ? undefined : ADAPTERS[c.fn]) ?? autoAdapter(c);
  if (!adapter) return { status: 'unsupported', reason: `no adapter for ${c.fn}` };
  try {
    const args = (c.args ?? []).map(deserialize);
    const kwargs = Object.fromEntries(Object.entries(c.kwargs ?? {}).map(([k, v]) => [k, deserialize(v)]));
    const self = c.self ? deserialize(c.self) : undefined;
    const call = (a: Adapter): unknown => (c.assume ? sj.assuming(c.assume.map((t) => deserialize(t) as Expr), () => a(args, kwargs, self)) : a(args, kwargs, self));
    let v: unknown;
    // matrix expressions (MatMul, Trace, BlockMatrix, ...) use their own methods and constructors
    const isMatExpr = (x: unknown) => x instanceof sj.MatrixExpr || x instanceof sj.MatScalar;
    // DomainMatrix, DDM and SDM methods (and their classes' static methods) share names with Matrix and Poly adapters
    const isDomainMatrix = (x: unknown) => x instanceof sj.DomainMatrix || x instanceof sj.DDM || x instanceof sj.SDM || (x instanceof TypeRef && ['DomainMatrix', 'DDM', 'SDM'].includes(x.name));
    // (rewrite targets are SymPy classes, which only the rewrite adapter names)
    const auto0 = (c.fn !== '.rewrite' && (isMatExpr(self) || args.some(isMatExpr))) || isDomainMatrix(self) || self instanceof sj.NDimArray || self instanceof sj.Indexed ? autoAdapter(c) : undefined;
    try {
      v = call(auto0 ?? adapter);
    } catch (e) {
      // an adapter written for another owner of the same method name (Poly.add, ...): try the generic one
      // (or the adapter, when the generic one was tried first for a matrix expression)
      const auto = auto0 ? adapter : adapter === ADAPTERS[c.fn] ? autoAdapter(c) : undefined;
      // (a DomainMatrix error is the method's own result)
      if (!auto || !(e instanceof Unsupported || e instanceof TypeError) || e instanceof sj.DMError) {
        if (!(e instanceof Unsupported)) observe?.({ error: e });
        throw e;
      }
      try {
        v = call(auto);
      } catch (fallbackError) {
        if (!(fallbackError instanceof Unsupported)) observe?.({ error: fallbackError });
        throw fallbackError;
      }
    }
    if (c.pick !== undefined) v = pickResult(v, c.pick);
    if (c.post !== undefined) v = projectResult(v, c.post, c.brackets);
    if (c.pyFormat !== undefined) v = pyNumberFormat(c.pyFormat, v);
    observe?.({ value: v });
    // a printed str()/repr() is compared exactly with Python's text
    if (c.post === 'str' || c.post === 'repr') return v === c.expected ? { status: 'pass' } : { status: 'fail', got: String(v) };
    if (c.text ? textMatches(v, c) : matches(v, c.expected)) return { status: 'pass' };
    if (c.text && typeof v === 'string') return { status: 'fail', got: v };
    const got = fmt(v);
    // the same capability with a different printed form counts as compatible
    const syms = new Map<string, Sym>();
    const collect = (x: unknown): void => {
      if (x instanceof Expr) for (const s of [...sj.freeSymbols(x)].filter((s) => s instanceof Sym)) syms.set(s.name, s);
      else if (x instanceof JsTuple || x instanceof JsList || x instanceof JsSet) x.items.forEach(collect);
      else if (x instanceof JsDict) x.entries.forEach(([k, w]) => (collect(k), collect(w)));
      else if (x instanceof Matrix) x.data.forEach(collect);
    };
    [...args, ...Object.values(kwargs), self].forEach(collect);
    const fmtOrUndefined = (x: unknown): string | undefined => {
      try {
        return fmt(x);
      } catch {
        return undefined; // a Lambda or series object has no printed input
      }
    };
    const input = self !== undefined ? fmtOrUndefined(self) : args.length ? fmtOrUndefined(args[0]) : undefined;
    if (equivalent(got, c.expected, [...syms.values()], { fn: c.fn, input })) return { status: 'equivalent', got };
    // dsolve: a solution in another form that satisfies the equations with as many constants (SymPy checkodesol);
    // this also accepts a correct solution where SymPy's printed one is wrong
    if (['dsolve', 'dsolve_system'].includes(c.fn) && solvesDsolveCase(args[0], v) && constantCount(got) === constantCount(c.expected)) return { status: 'equivalent', got };
    // a doctest whose printed output is mathematically wrong: the correct value counts as compatible
    const erratum = SYMPY_ERRATA[`${c.module}:${c.src}`] ?? SYMPY_ERRATA[c.src];
    if (typeof erratum === 'string' ? erratum === got : erratum?.includes(got)) return { status: 'equivalent', got };
    return { status: 'fail', got };
  } catch (e) {
    if (e instanceof Unsupported) return { status: 'unsupported', reason: e.message };
    return { status: 'error', reason: e instanceof Error ? e.message : String(e) };
  }
}

/**
 * Doctests whose SymPy output is mathematically wrong, with the correct
 * printed value symjs gives (keyed by the doctest source).
 */
const SYMPY_ERRATA: Readonly<Record<string, string | readonly string[]>> = {
  // SymPy mixes Poly.gens=(y,x) with Options.gens=(x,y). Neither published
  // result solves the original pair; these tuples satisfy both equations.
  'sympy.solvers.polysys:solve_biquadratic(a, b, NewOption)': [
    '[(11/9, 5/3), (3, -1)]',
    '[(-1/2 + sqrt(29)/2, -9/2 + sqrt(29)/2), (-sqrt(29)/2 - 1/2, -9/2 - sqrt(29)/2)]',
  ],
  // The documented TR12i result changes tan(a)*tan(b) to tan(a)+tan(b) in
  // the residual denominator. The product is required by the tangent sum identity.
  'sympy.simplify.fu:TR12i(eq.expand())': '-3*tan(a + b)*tan(a + c)/(2*(tan(a)*tan(b) - 1))',
  // The polar Jacobian r gives pi*(5**2 - 2**2), not (5 - 2)*2*pi.
  'sympy.sets.fancysets:c2.measure': '21*pi',
  // SymPy's pdiv with a non-first generator starts the quotient at the generator index (rings.py: `q, r, dr = x, f, df`),
  // so its printed quotient is wrong: m*f != g*q + r for f = x**2 + x*y, g = 2*x + 2, m = (2*x + 2)**2
  'f.pdiv(g, y) # generator is given': '[2*x**3 + 2*x**2*y + 2*x**2 + 2*x*y, 0]',
  'f.pdiv(g, 1) # generator index is given': '[2*x**3 + 2*x**2*y + 2*x**2 + 2*x*y, 0]',
  // d/dx (y - x**2) = -2*x > 0 on (-oo, 0) and vanishes only at the endpoint 0, so the function is strictly increasing
  'is_strictly_increasing(-x**2 + y, Interval(-oo, 0), x)': 'True',
  // n is a positive integer: mobius(1**2) = 1, so the value is not 0 for every n
  'mobius(n**2)': 'mobius(n**2)',
  // a product of symmetric matrices is symmetric only when they commute: X*Z is not known to be symmetric
  'ask(Q.symmetric(X*Z), Q.symmetric(X) & Q.symmetric(Z))': 'None',
  // SymPy evaluates the weight at a rational approximation of the root, which moves the last
  // digit: the exact weight is 1.70630566574432743792195751524918602024548..., so the
  // correctly rounded 40-digit value ends in ...245.
  [`sympy.integrals.tests.test_quadrature:assert [str(r) for r in w] == [
            '0.3379547635663543330553835737094171534907',
            '1.097332224279111467485302294320899710461',
            '1.706305665744327437921957515249186020246']`]: "['0.3379547635663543330553835737094171534907', '1.097332224279111467485302294320899710461', '1.706305665744327437921957515249186020245']",
};

/** The dsolve result v solves the equation (or system) eqArg. */
export function solvesDsolveCase(eqArg: unknown, v: unknown): boolean {
  const eqs = (eqArg instanceof JsTuple || eqArg instanceof JsList ? eqArg.items : [eqArg]).filter((e): e is Expr => e instanceof Expr);
  const items = v instanceof JsTuple || v instanceof JsList || v instanceof JsSet ? v.items : Array.isArray(v) ? v : [v];
  // Systems can have several alternative families; each must solve every equation.
  if (items.length && items.every((s) => s instanceof JsTuple || s instanceof JsList || Array.isArray(s))) return items.every((s) => solvesDsolveCase(eqArg, s));
  const sols = items.filter((e): e is Expr => e instanceof Expr);
  const fns = sols.flatMap((s) => (s instanceof sj.Rel && s.lhs instanceof sj.UndefFn ? [s.lhs] : []));
  const x = fns[0]?.args[0];
  if (!eqs.length || !(x instanceof Sym)) return false;
  return solvesOdeSystem(eqs, x, sols);
}

// ---- solvers.simplex
const lpMatrix = (v: unknown): sj.LPMatrixLike => {
  if (v instanceof Matrix) return v;
  if (v instanceof JsList || v instanceof JsTuple) return v.items.map((r) => (r instanceof JsList || r instanceof JsTuple ? r.items.map(asExpr) : asExpr(r))) as sj.LPMatrixLike;
  throw new Unsupported('linprog matrix');
};
const lpBound = (v: unknown): sj.LPBound => {
  if (!(v instanceof JsTuple) || v.items.length !== 2) throw new Unsupported('linprog bound');
  return [v.items[0] === null ? null : asExpr(v.items[0]), v.items[1] === null ? null : asExpr(v.items[1])];
};
const lpBounds = (v: unknown): sj.LPBounds | undefined => {
  if (v === undefined || v === null) return undefined;
  if (v instanceof JsDict) return new Map(v.entries.map(([k, b]) => [Number((k as sj.Rational).p), lpBound(b)]));
  if (v instanceof JsTuple && !v.isList && v.items.length === 2 && !(v.items[0] instanceof JsTuple)) return lpBound(v);
  if (v instanceof JsList || v instanceof JsTuple) return v.items.map(lpBound);
  throw new Unsupported('linprog bounds');
};
const lpConstraints = (v: unknown): Expr[] => (v instanceof JsList || v instanceof JsTuple ? v.items.map(asExpr) : [asExpr(v)]);
Object.assign(ADAPTERS, {
  lpmin: (args, kw) => (noKw(kw), new JsTuple(sj.lpmin(asExpr(args[0]), lpConstraints(args[1])))),
  lpmax: (args, kw) => (noKw(kw), new JsTuple(sj.lpmax(asExpr(args[0]), lpConstraints(args[1])))),
  linprog: (args, kw) => {
    for (const k of Object.keys(kw)) if (!['A', 'b', 'A_eq', 'b_eq', 'bounds'].includes(k)) throw new Unsupported(`kwargs ${k}`);
    const pick = (i: number, k: string): sj.LPMatrixLike | undefined => {
      const v = args[i] ?? kw[k];
      return v === undefined || v === null ? undefined : lpMatrix(v);
    };
    const [o, p] = sj.linprog(lpMatrix(args[0]), pick(1, 'A'), pick(2, 'b'), pick(3, 'A_eq'), pick(4, 'b_eq'), lpBounds(args[5] ?? kw['bounds']));
    return new JsTuple([o, new JsList(p)]);
  },
} satisfies Record<string, Adapter>);
ADAPTERS['bivariate_type'] = (args, kw) => {
  noKw(kw);
  const r = sj.bivariateType(asExpr(args[0]), args[1] as Sym, args[2] as Sym);
  return sj.isNoMatch(r) ? null : new JsTuple(r);
};

// ---- solvers.ode.single
ADAPTERS['.get_linear_coefficients'] = (args, kw, self) => {
  noKw(kw);
  if (!(self instanceof sj.SingleODEProblem)) throw new Unsupported('get_linear_coefficients');
  const r = self.getLinearCoefficients(asExpr(args[0]), args[1] as sj.UndefFn, Number((args[2] as sj.Rational).p));
  return sj.isNoMatch(r) ? null : new JsDict([...r].map(([k, v]) => [sj.Rational.of(k), v] as const));
};
ADAPTERS['.get_general_solution'] = (_args, kw, self) => {
  for (const k of Object.keys(kw)) if (k !== 'simplify') throw new Unsupported(`kwargs ${k}`);
  if (!(self instanceof sj.SingleODESolver)) throw new Unsupported('get_general_solution');
  return new JsList(self.getGeneralSolution(kw['simplify'] === undefined ? {} : { simplify: Boolean(kw['simplify']) }));
};
// Python's nth=0 is a false flag
ADAPTERS['primorial'] = (args, kw) => {
  for (const k of Object.keys(kw)) if (k !== 'nth') throw new Unsupported(`kwargs ${k}`);
  const nth = kw['nth'];
  return sj.primorial(asExpr(args[0]), nth === undefined ? {} : { nth: !(nth === false || (nth instanceof sj.Rational && nth.isZero)) });
};
ADAPTERS['deconstruct'] = (args, kw) => {
  for (const k of Object.keys(kw)) if (k !== 'variables') throw new Unsupported(`kwargs ${k}`);
  const vs = kw['variables'];
  return sj.usympy.deconstruct(args[0], vs instanceof JsTuple || vs instanceof JsList ? vs.items.map(asExpr) : []);
};
