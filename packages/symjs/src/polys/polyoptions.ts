// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (polys/polyoptions.py), Copyright (c) 2006-2023
// SymPy Development Team, BSD 3-Clause License (see LICENSE).

/**
 * @file Options of the polynomial manipulation functions (SymPy
 * sympy.polys.polyoptions): `Options` is a `Map` from option names to
 * preprocessed values (SymPy's Options is a dict). Each option checks and
 * normalizes its value, may exclude or require other options, and some
 * set derived options afterwards (a `domain` turns `auto` off, `modulus`
 * sets the domain GF(p), `extension` an algebraic field, ...).
 */

import { NotImplementedError } from '../core/errors';
import { Expr, Sym } from '../core/nodes';
import { Tuple, TupleNode } from '../core/containers';
import { cast, defined, expectType } from '../core/guard';
import { CC } from './domains/complexfield';
import { GF } from './domains/finitefield';
import { QQ_I, ZZ_I } from './domains/gaussiandomains';
import './domains/algebraicfield';
import { Domain, EX, QQ, RR, ZZ, groundRational, groundToSympy } from './domains';
import { parse } from '../parsing/parser';
import { FlagError, GeneratorsError, OptionError } from './polyerrors';
import { lex, monomialKey } from './orderings';

/** An option's checks and processing (SymPy Option subclasses). */
interface OptionSpec {
  /** A flag (SymPy Flag): allowed only where the function lists it. */
  flag?: boolean;
  requires?: readonly string[];
  excludes?: readonly string[];
  /** The value when the option is not given (SymPy default). */
  default?: () => unknown;
  preprocess: (value: unknown) => unknown;
  postprocess?: (options: Options) => void;
}

/** SymPy BooleanOption.preprocess. */
function boolean(name: string): (v: unknown) => boolean {
  return (v) => {
    if (v === true || v === false || v === 1 || v === 0) return Boolean(v);
    throw new OptionError(`'${name}' must have a boolean value assigned, got ${String(v)}`);
  };
}

const RE_REALFIELD = /^(R|RR)(_(\d+))?$/;
const RE_COMPLEXFIELD = /^(C|CC)(_(\d+))?$/;
const RE_FINITEFIELD = /^(FF|GF)\((\d+)\)$/;
const RE_POLYNOMIAL = /^(Z|ZZ|Q|QQ|ZZ_I|QQ_I|R|RR|C|CC)\[(.+)\]$/;
const RE_FRACTION = /^(Z|ZZ|Q|QQ)\((.+)\)$/;
const RE_ALGEBRAIC = /^(Q|QQ)<(.+)>$/;
const GROUNDS: Readonly<Record<string, Domain>> = { Z: ZZ, ZZ, Q: QQ, QQ, ZZ_I, QQ_I, R: RR, RR, C: CC, CC, EX };
const ground = (name: string | undefined): Domain => defined(GROUNDS[defined(name)], 'ground domain');
const symbolsOf = (s: string | undefined): Sym[] => defined(s).split(',').map((g) => expectType(parse(g.trim()), (e): e is Sym => e instanceof Sym, 'generator'));

/**
 * Resolves a coefficient domain from a domain object or its string specification.
 *
 * @param domain - Coefficient domain.
 * @returns The coefficient domain.
 * @throws NotImplementedError when the requested floating-point precision is unsupported.
 * @throws OptionError when the domain specification is unrecognized.
 * @see SymPy `sympy.polys.polyoptions.Domain.preprocess`
 */
export function preprocessDomain(domain: unknown): Domain {
  if (domain instanceof Domain) return domain;
  if (typeof domain === 'string') {
    if (['Z', 'ZZ', 'Q', 'QQ', 'ZZ_I', 'QQ_I', 'EX'].includes(domain)) return ground(domain);
    const real = RE_REALFIELD.exec(domain) ?? RE_COMPLEXFIELD.exec(domain);
    if (real !== null) {
      if (real[3] === undefined) return ground(real[1]);
      throw new NotImplementedError(`domains of precision ${real[3]} are not supported`);
    }
    const ff = RE_FINITEFIELD.exec(domain);
    if (ff !== null) return GF(BigInt(defined(ff[2])));
    const poly = RE_POLYNOMIAL.exec(domain);
    if (poly !== null) return ground(poly[1]).polyRing(...symbolsOf(poly[2]));
    const frac = RE_FRACTION.exec(domain);
    if (frac !== null) return ground(frac[1]).fracField(...symbolsOf(frac[2]));
    const alg = RE_ALGEBRAIC.exec(domain);
    if (alg !== null) return QQ.algebraicField(...defined(alg[2]).split(',').map((g) => parse(g.trim())));
  }
  throw new OptionError(`expected a valid domain specification, got ${String(domain)}`);
}

/** A value as an expression (numbers too); throws OptionError otherwise. */
function asExpr(x: unknown): Expr {
  const e = groundToSympy(x);
  if (e instanceof Expr) return e;
  throw new OptionError(`expected an expression, got ${String(x)}`);
}

/** SymPy Gens.preprocess: the generators as a Tuple (printed like SymPy's tuple). */
function preprocessGens(gensIn: unknown): TupleNode {
  let gens: unknown[] = Array.isArray(gensIn) ? gensIn : [gensIn];
  const inner: unknown = gens[0];
  if (gens.length === 1 && Array.isArray(inner)) gens = inner;
  if (gens.length === 1 && (gens[0] === null || gens[0] === undefined)) return Tuple();
  const exprs = gens.map(asExpr);
  if (new Set(exprs.map((g) => g.key)).size !== exprs.length) throw new GeneratorsError(`duplicated generators: (${exprs.map(String).join(', ')})`);
  if (exprs.some((g) => !g.isCommutative)) throw new GeneratorsError(`non-commutative generators: (${exprs.map(String).join(', ')})`);
  return Tuple(...exprs);
}

/** SymPy Extension.preprocess: true, or the set of extension elements. */
function preprocessExtension(ext: unknown): boolean | Expr[] | null {
  if (ext === true || ext === 1) return true;
  if (ext === false || ext === 0) throw new OptionError("'False' is an invalid argument for 'extension'");
  const list: unknown[] = Array.isArray(ext) ? ext : ext instanceof Set ? [...ext] : [ext];
  if (!list.length) return null;
  const out: Expr[] = [];
  for (const e of list.map(asExpr)) if (!out.some((o) => o.key === e.key)) out.push(e);
  return out;
}

const SPECS: Readonly<Record<string, OptionSpec>> = {
  expand: { default: () => true, preprocess: boolean('expand') },
  gens: { default: () => Tuple(), preprocess: preprocessGens },
  wrt: {
    preprocess: (wrt) => {
      if (wrt instanceof Expr) return [String(wrt)];
      if (typeof wrt === 'string') {
        const s = wrt.trim();
        if (s.endsWith(',')) throw new OptionError('Bad input: missing parameter.');
        return s ? s.split(/\s*,\s*|\s+/) : [];
      }
      if (Array.isArray(wrt)) return wrt.map(String);
      throw new OptionError("invalid argument for 'wrt' option");
    },
  },
  sort: {
    default: () => [],
    preprocess: (sort) => {
      if (typeof sort === 'string') return sort.split('>').map((g) => g.trim());
      if (Array.isArray(sort)) return sort.map(String);
      throw new OptionError("invalid argument for 'sort' option");
    },
  },
  order: { default: () => lex, preprocess: (order) => (typeof order === 'string' ? monomialKey(order) : order) },
  field: { excludes: ['domain', 'split', 'gaussian'], preprocess: boolean('field') },
  greedy: { excludes: ['domain', 'split', 'gaussian', 'extension', 'modulus', 'symmetric'], preprocess: boolean('greedy') },
  composite: { default: () => null, excludes: ['domain', 'split', 'gaussian', 'extension', 'modulus', 'symmetric'], preprocess: boolean('composite') },
  domain: {
    excludes: ['field', 'greedy', 'split', 'gaussian', 'extension'],
    preprocess: preprocessDomain,
    postprocess: (o) => {
      const dom = o.get('domain');
      const gens = o.gens;
      if (dom instanceof Domain && dom.symbols.some((s) => gens.some((g) => g.key === s.key))) throw new GeneratorsError('ground domain and generators interfere together');
      if (!gens.length && dom === EX) throw new GeneratorsError('you have to provide generators because EX domain was requested');
    },
  },
  split: {
    excludes: ['field', 'greedy', 'domain', 'gaussian', 'extension', 'modulus', 'symmetric'],
    preprocess: boolean('split'),
    postprocess: (o) => {
      if (o.has('split')) throw new NotImplementedError("'split' option is not implemented yet");
    },
  },
  gaussian: {
    excludes: ['field', 'greedy', 'domain', 'split', 'extension', 'modulus', 'symmetric'],
    preprocess: boolean('gaussian'),
    postprocess: (o) => {
      if (o.get('gaussian') === true) o.set('domain', QQ_I);
    },
  },
  extension: {
    excludes: ['greedy', 'domain', 'split', 'gaussian', 'modulus', 'symmetric'],
    preprocess: preprocessExtension,
    postprocess: (o) => {
      const ext = o.get('extension');
      if (Array.isArray(ext)) o.set('domain', QQ.algebraicField(...ext.map(asExpr)));
    },
  },
  modulus: {
    excludes: ['greedy', 'split', 'domain', 'gaussian', 'extension'],
    preprocess: (m) => {
      const r = groundRational(m);
      if (r?.[1] === 1n && r[0] > 0n) return r[0];
      throw new OptionError(`'modulus' must a positive integer, got ${String(m)}`);
    },
    postprocess: (o) => {
      const m = o.get('modulus');
      if (typeof m === 'bigint') o.set('domain', GF(m, o.get('symmetric') !== false));
    },
  },
  symmetric: { requires: ['modulus'], excludes: ['greedy', 'domain', 'split', 'gaussian', 'extension'], preprocess: boolean('symmetric') },
  strict: { default: () => true, preprocess: boolean('strict') },
  auto: {
    flag: true,
    default: () => true,
    preprocess: boolean('auto'),
    postprocess: (o) => {
      if ((o.has('domain') || o.has('field')) && !o.has('auto')) o.set('auto', false);
    },
  },
  frac: { flag: true, default: () => false, preprocess: boolean('frac') },
  formal: { flag: true, default: () => false, preprocess: boolean('formal') },
  polys: { flag: true, preprocess: boolean('polys') },
  include: { flag: true, default: () => false, preprocess: boolean('include') },
  all: { flag: true, default: () => false, preprocess: boolean('all') },
  gen: {
    flag: true,
    default: () => 0,
    preprocess: (gen) => {
      if (gen instanceof Expr || typeof gen === 'number' || typeof gen === 'bigint') return gen;
      throw new OptionError("invalid argument for 'gen' option");
    },
  },
  series: { flag: true, default: () => false, preprocess: boolean('series') },
  symbols: {
    flag: true,
    preprocess: (symbols) => {
      if (typeof symbols === 'object' && symbols !== null && Symbol.iterator in symbols) return symbols;
      throw new OptionError(`expected an iterator or iterable container, got ${String(symbols)}`);
    },
  },
  method: {
    flag: true,
    preprocess: (method) => {
      if (typeof method === 'string') return method.toLowerCase();
      throw new OptionError(`expected a string, got ${String(method)}`);
    },
  },
};

/** The order in which the options are post-processed (SymPy's topological order of the option dependencies). */
const ORDER = ['expand', 'gens', 'wrt', 'sort', 'order', 'field', 'greedy', 'composite', 'domain', 'split', 'gaussian', 'extension', 'auto', 'modulus', 'symmetric', 'strict', 'frac', 'formal', 'polys', 'include', 'all', 'gen', 'series', 'symbols', 'method'];

/** Option arguments: a Map or a plain object of option values. */
export type OptionArgs = ReadonlyMap<string, unknown> | Readonly<Record<string, unknown>>;
const entriesOf = (args: OptionArgs): [string, unknown][] => (args instanceof Map ? [...(args as ReadonlyMap<string, unknown>)] : Object.entries(args));

/** The spec of an option; throws OptionError for an unknown one. */
function spec(name: string): OptionSpec {
  const s = SPECS[name];
  if (s === undefined) throw new OptionError(`'${name}' is not a valid option`);
  return s;
}

/**
 * The options of a polynomial manipulation function: a Map
 * of the given options, preprocessed and checked, with the derived options
 * set. `get(name)` is the raw entry; the getters (`domain`, `gens`, ...)
 * give an option's default when it is not set.
 *
 * @see SymPy `sympy.polys.polyoptions.Options`
 * @example
 * ```ts
 * import { Options } from '@symjs/symjs';
 *
 * new Options([], { field: true }).field; // => True
 * ```
 */
export class Options extends Map<string, unknown> {
  /**
   * Construct polynomial options from generators and keyword arguments.
   *
   * @param gens - Polynomial generators in the desired order.
   * @param args - Polynomial options keyed by name.
   * @param flags - Option flags allowed in this context.
   * @param strict - Reject flags outside the allowed set.
   * @throws OptionError when generators are specified both positionally and in the options or a flag is not allowed in this context or a required companion option is absent or mutually exclusive options are supplied together.
   */
  constructor(gens: readonly unknown[] | null, args: OptionArgs, flags: readonly string[] | null = null, strict = false) {
    super();
    const given = new Map(entriesOf(args));
    const gensArg = given.get('gens');
    if (gens?.length && Array.isArray(gensArg) && gensArg.length) throw new OptionError("both '*gens' and keyword argument 'gens' supplied");
    if (gens?.length) given.set('gens', gens);
    const preprocessOptions = (opts: ReadonlyMap<string, unknown>): void => {
      for (const [option, value] of opts) {
        const s = spec(option);
        if (s.flag && (flags === null || !flags.includes(option)) && strict) throw new OptionError(`'${option}' flag is not allowed in this context`);
        if (value !== null && value !== undefined) this.set(option, s.preprocess(value));
      }
    };
    preprocessOptions(given);
    for (const option of this.keys()) {
      const s = spec(option);
      for (const r of s.requires ?? []) if (this.get(r) === undefined) throw new OptionError(`'${option}' option is only allowed together with '${r}'`);
      for (const e of s.excludes ?? []) if (this.get(e) !== undefined) throw new OptionError(`'${option}' option is not allowed together with '${e}'`);
    }
    for (const option of ORDER) spec(option).postprocess?.(this);
  }
  /**
   * Looks up the option and uses its default if unset.
   *
   * @param name - Name of the option.
   * @returns The effective option value.
   */
  option(name: string): unknown {
    return this.has(name) ? this.get(name) : (spec(name).default?.() ?? null);
  }
  /**
   * Lists the generators in their defining order.
   *
   * @returns The generator sequence.
   * @see SymPy `sympy.polys.polyoptions.Options.gens`
   */
  get gens(): Expr[] {
    return [...cast(this.option('gens'), TupleNode).args];
  }
  /**
   * Identifies the coefficient domain selected by the options.
   *
   * @returns The configured domain, if supplied.
   * @see SymPy `sympy.polys.polyoptions.Options.domain`
   */
  get domain(): Domain | null {
    const d = this.option('domain');
    return d instanceof Domain ? d : null;
  }
  /**
   * Indicates whether the options request field coefficients.
   *
   * @returns The field preference.
   * @see SymPy `sympy.polys.polyoptions.Options.field`
   */
  get field(): boolean {
    return this.option('field') === true;
  }
  /**
   * Specifies which algebraic extensions to use in the coefficient domain.
   *
   * @returns The extension selection.
   * @see SymPy `sympy.polys.polyoptions.Options.extension`
   */
  get extension(): boolean | Expr[] | null {
    const e = this.option('extension');
    return e === true || (Array.isArray(e) ? e.map(asExpr) : null);
  }
  /**
   * Controls whether coefficient domains may contain polynomial or rational-function generators.
   *
   * @returns The composite-domain preference.
   * @see SymPy `sympy.polys.polyoptions.Options.composite`
   */
  get composite(): boolean | null {
    const c = this.option('composite');
    return typeof c === 'boolean' ? c : null;
  }
  /**
   * Indicates whether to convert the coefficient domain automatically.
   *
   * @returns The automatic-conversion flag.
   * @see SymPy `sympy.polys.polyoptions.Options.auto`
   */
  get auto(): boolean {
    return this.option('auto') === true;
  }
  /**
   * Copies the options and applies the specified replacements.
   *
   * @param updates - Option values to replace.
   * @returns The updated options object.
   * @see SymPy `sympy.polys.polyoptions.Options.clone`
   */
  clone(updates: OptionArgs = {}): Options {
    const o = new Options(null, {});
    for (const [k, v] of this) o.set(k, v);
    for (const [k, v] of entriesOf(updates)) o.set(k, v);
    return o;
  }
  /**
   * Collects the non-flag options while excluding the generators.
   *
   * @returns A map of option names to values.
   * @see SymPy `sympy.polys.polyoptions.Options.args`
   */
  get args(): Map<string, unknown> {
    return new Map([...this].filter(([k, v]) => v !== null && k !== 'gens' && !SPECS[k]?.flag));
  }
}

/**
 * Builds options from generators and keywords, reusing a sole options object when supplied.
 *
 * @param gens - Polynomial generators in the desired order.
 * @param args - Polynomial options keyed by name.
 * @returns The resolved options.
 * @see SymPy `sympy.polys.polyoptions.build_options`
 */
export function buildOptions(gens: readonly unknown[], args: OptionArgs): Options {
  const entries = entriesOf(args);
  const opt = entries.find(([k]) => k === 'opt')?.[1];
  if (entries.length === 1 && opt instanceof Options && !gens.length) return opt;
  return new Options(gens, args);
}

/**
 * Throws FlagError when args contain a flag not in flags, OptionError for an unknown option.
 *
 * @param args - Polynomial options keyed by name.
 * @param flags - Option flags allowed in this context.
 * @throws FlagError when a flag is not allowed in this context.
 * @see SymPy `sympy.polys.polyoptions.allowed_flags`
 * @example
 * ```ts
 * import { allowedFlags, ZZ } from '@symjs/symjs';
 *
 * allowedFlags({ domain: ZZ }, []);
 * allowedFlags({ domain: ZZ, frac: true }, ['frac']);
 * ```
 */
export function allowedFlags(args: OptionArgs, flags: readonly string[]): void {
  for (const [arg] of entriesOf(args)) {
    if (spec(arg).flag && !flags.includes(arg)) throw new FlagError(`'${arg}' flag is not allowed in this context`);
  }
}
