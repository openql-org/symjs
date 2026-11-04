// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Linear recurrences with polynomial coefficients (port of SymPy
 * sympy.solvers.recurr: rsolve_poly, rsolve_ratio, rsolve_hyper, rsolve).
 */

import type { Expr, ExprLike } from '../core/nodes';
import { Add, Dummy, Mul, Rational, Rel, S, Sym, UndefFn } from '../core/nodes';
import { at, defined, first, getOrThrow } from '../core/guard';
import { add, mul, pow, sympify } from '../core/ops';
import { xreplace } from '../core/traverse';
import { asNumerDenom } from '../core/methods';
import { binomial } from '../functions/special/special';
import { Matrix } from '../matrices/matrix';
import { polyCoefficients, roots } from '../polys/poly';
import { Poly, factorListExpr, polyLcm } from '../polys/sympoly';
import { product } from '../concrete/summations';
import { compareKeys, sortKey } from '../printing/sortkey';
import { expandMul as expand } from '../simplify/expand';
import { cancel } from '../simplify/rational';
import { hypersimilar, hypersimp } from '../simplify/gammasimp';
import { simplify } from '../simplify/simplify';
import { linsolve, solveUndeterminedCoeffs } from './solve';

const isZeroE = (e: Expr) => e instanceof Rational && e.isZero;
const isIntR = (e: Expr): e is Rational => e instanceof Rational && e.isInteger;
const subs = (e: Expr, x: Sym, v: ExprLike) => xreplace(e, [[x, sympify(v)]]);
const isPolyIn = (e: Expr, x: Sym) => polyCoefficients(expand(e), x) !== undefined;

/** Degree and leading coefficient of e as a polynomial in x ([-Infinity, 0] for zero). */
function lt(e: Expr, x: Sym): [number, Expr] {
  const pc = defined(polyCoefficients(expand(e), x), 'polynomial coefficients');
  let d = -Infinity;
  for (const [k, c] of pc) if (!isZeroE(c) && k > d) d = k;
  return d === -Infinity ? [d, S.Zero] : [d, getOrThrow(pc, d)];
}

/** Distinct roots of e in x (empty when roots cannot be computed). */
function distinctRoots(e: Expr, x: Sym): Expr[] {
  let rs: Expr[];
  try {
    rs = roots(expand(e), x);
  } catch {
    return [];
  }
  const out = new Map<string, Expr>();
  for (const r of rs) out.set(r.key, r);
  return [...out.values()];
}

/**
 * Largest non-negative integer root of e in x, or undefined (SymPy roots with
 * filter='Z'). When roots() cannot solve a factor of high degree, the integer
 * roots are still those of the linear factors.
 */
function maxNniRoot(e: Expr, x: Sym): number | undefined {
  let rs: Expr[];
  try {
    rs = roots(expand(e), x);
  } catch {
    rs = factorListExpr(expand(e))[1].flatMap(([f]) => {
      const [d, c1] = lt(f, x);
      return d === 1 ? [mul(-1, subs(f, x, 0), pow(c1, -1))] : [];
    });
  }
  const ns = rs.filter((r): r is Rational => isIntR(r) && !r.isNegative).map((r) => Number(r.p));
  return ns.length ? Math.max(...ns) : undefined;
}

let curN: Sym;
const quo = (f: Expr, g: Expr, x: Sym = curN): Expr => Poly.from(expand(f), [x]).div(Poly.from(expand(g), [x]))[0].asExpr();
const gcdN = (f: Expr, g: Expr, x: Sym = curN): Expr => Poly.from(expand(f), [x]).gcd(Poly.from(expand(g), [x])).asExpr();

/**
 * SymPy rsolve_poly: polynomial solutions of sum(coeffs[i] * y(n + i)) = f
 * (Abramov's algorithm). Returns [solution, free constants].
 */
export function rsolvePoly(coeffsIn: readonly ExprLike[], fIn: ExprLike, n: Sym, shift = 0): [Expr, Sym[]] | undefined {
  curN = n;
  const f = sympify(fIn);
  if (!isPolyIn(f, n)) return undefined;
  const homogeneous = isZeroE(expand(f));
  const r = coeffsIn.length - 1;
  const coeffs = coeffsIn.map((c) => expand(sympify(c)));
  const polys: Expr[] = [];
  const terms: [Expr, number][] = [];
  for (let i = 0; i <= r; i++) {
    let p: Expr = S.Zero;
    for (let j = i; j <= r; j++) p = add(p, mul(at(coeffs, j), binomial(j, i)));
    polys.push(expand(p));
    const [d, c] = lt(p, n);
    terms.push([c, d]);
  }
  let d = at(terms, 0)[1];
  let b = at(terms, 0)[1];
  for (let i = 1; i <= r; i++) {
    if (at(terms, i)[1] > d) d = at(terms, i)[1];
    if (at(terms, i)[1] - i > b) b = at(terms, i)[1] - i;
  }
  const x = new Dummy('x');
  let degreePoly: Expr = S.Zero;
  for (let i = 0; i <= r; i++) {
    if (at(terms, i)[1] - i === b) {
      let ffx: Expr = S.One;
      for (let j = 0; j < i; j++) ffx = mul(ffx, add(x, -j));
      degreePoly = add(degreePoly, mul(at(terms, i)[0], ffx));
    }
  }
  const Ns: number[] = [];
  const nr = maxNniRoot(degreePoly, x);
  if (nr !== undefined) Ns.push(nr);
  if (homogeneous) Ns.push(-b - 1);
  else Ns.push(lt(f, n)[0] - b, -b - 1);
  const N = Math.max(...Ns);
  if (N < 0) return homogeneous ? [S.Zero, []] : undefined;

  let C: Sym[];
  let _C: Sym[];
  let result: Expr;
  if (N <= r) {
    C = [];
    let y: Expr = S.Zero;
    for (let i = 0; i <= N; i++) {
      C.push(new Sym(`C${i + shift}`));
      y = add(y, mul(at(C, i), pow(n, i)));
    }
    let E: Expr = S.Zero;
    for (let i = 0; i <= r; i++) E = add(E, mul(at(coeffs, i), subs(y, n, add(n, i))));
    // the coefficients are polynomials (lt above), so E - f is a polynomial in n linear in the constants
    const sols = solveUndeterminedCoeffs(add(E, mul(-1, f)), C, [n]);
    if (!sols.length) return undefined;
    const sol = at(sols, 0);
    _C = C;
    C = C.filter((c, i) => at(sol, i).key === c.key);
    result = xreplace(y, _C.map((c, i) => [c, at(sol, i)] as [Expr, Expr]));
  } else {
    const A = r;
    const U = N + A + b + 1;
    const nra = maxNniRoot(at(polys, r), n);
    const a = nra !== undefined ? nra + 1 : 0;
    const delta = (p: Expr, k: number): Expr => {
      let B: Expr = S.One;
      let D = subs(p, n, a + k);
      for (let i = 1; i <= k; i++) {
        B = mul(B, Rational.of(i - k - 1, i));
        D = add(D, mul(B, subs(p, n, a + k - i)));
      }
      return D;
    };
    const alpha = new Map<number, Expr>();
    for (let i = -A; i <= d; i++) {
      const I: Expr[] = Array.from({ length: d + 1 }, () => S.One);
      for (let k = 1; k <= d; k++) I[k] = mul(at(I, k - 1), add(x, i - k + 1), Rational.of(1, k));
      let al: Expr = S.Zero;
      for (let j = 0; j <= A; j++) {
        for (let k = 0; k <= d; k++) {
          const B = i + j < 0 || i + j > k ? S.Zero : binomial(k, i + j);
          if (isZeroE(B)) continue;
          al = add(al, mul(at(I, k), B, delta(at(polys, j), k)));
        }
      }
      alpha.set(i, al);
    }
    const V: Expr[][] = Array.from({ length: U }, (_, i) => Array.from({ length: A }, (_, j) => (i === j ? S.One : S.Zero)));
    const G: Expr[] = Array.from({ length: U }, () => S.Zero);
    for (let i = A; i < U; i++) {
      const v: Expr[] = Array.from({ length: A }, () => S.Zero);
      let g: Expr = S.Zero;
      for (let k = 1; k <= A + b; k++) {
        if (i - k < 0) break;
        const B = subs(getOrThrow(alpha, k - A), x, i - k);
        for (let j = 0; j < A; j++) v[j] = add(at(v, j), mul(B, at(at(V, i - k), j)));
        if (!homogeneous) g = add(g, mul(B, at(G, i - k)));
      }
      const denom = subs(getOrThrow(alpha, -A), x, i);
      for (let j = 0; j < A; j++) at(V, i)[j] = mul(-1, at(v, j), pow(denom, -1));
      if (!homogeneous) G[i] = mul(add(delta(f, i - A), mul(-1, g)), pow(denom, -1));
    }
    const P: Expr[] = Array.from({ length: U }, () => S.One);
    for (let i = 1; i < U; i++) P[i] = expand(mul(at(P, i - 1), add(n, -a - i + 1), Rational.of(1, i)));
    const Q: Expr[] = [];
    for (let i = 0; i < A; i++) Q.push(add(...V.map((row, j) => expand(mul(at(row, i), at(P, j))))));
    const h = homogeneous ? S.Zero : add(...G.map((g, j) => expand(mul(g, at(P, j)))));
    C = Array.from({ length: A }, (_, i) => new Sym(`C${i + shift}`));
    const gf = (i: number) => add(...C.map((c, j) => mul(c, delta(at(Q, j), i))));
    const E: Expr[] = [];
    for (let i = N + 1; i < U; i++) E.push(homogeneous ? gf(i) : add(gf(i), delta(h, i)));
    let solved = new Map<string, Expr>();
    if (E.length) {
      // a homogeneous system always has the zero solution
      const sol = linsolve(E, C);
      if (!sol) return undefined;
      solved = new Map(C.map((c, i) => [c.key, at(sol, i)] as [string, Expr]).filter(([k, v]) => v.key !== k));
    }
    result = h;
    _C = [...C];
    const remaining: Sym[] = [];
    C.forEach((c, i) => {
      const sv = solved.get(c.key);
      const s = sv ? mul(sv, at(Q, i)) : mul(c, at(Q, i));
      if (!sv) remaining.push(c);
      result = add(result, expand(s));
    });
    C = remaining;
  }
  if (C.length !== _C.length || C.some((c, i) => c.key !== at(_C, i).key)) {
    result = xreplace(result, C.map((c, i) => [c, at(_C, i)] as [Expr, Expr]));
    C = _C.slice(0, C.length);
  }
  return [result, C];
}

/** Resultant of f and g in x via the Sylvester determinant (coefficients may contain other symbols). */
function sylvesterResultant(f: Expr, g: Expr, x: Sym): Expr {
  const cf = (e: Expr) => {
    const pc = defined(polyCoefficients(expand(e), x), 'polynomial coefficients');
    const d = lt(e, x)[0];
    return Array.from({ length: d + 1 }, (_, i) => pc.get(d - i) ?? S.Zero);
  };
  const a = cf(f);
  const b = cf(g);
  const m = a.length - 1;
  const k = b.length - 1;
  const N = m + k;
  if (N === 0) return S.One;
  const rows: Expr[][] = [];
  for (let i = 0; i < k; i++) rows.push(Array.from({ length: N }, (_, j) => (j - i >= 0 && j - i <= m ? at(a, j - i) : S.Zero)));
  for (let i = 0; i < m; i++) rows.push(Array.from({ length: N }, (_, j) => (j - i >= 0 && j - i <= k ? at(b, j - i) : S.Zero)));
  return expand(Matrix.of(rows).det());
}

/** SymPy rsolve_ratio: rational solutions (Abramov). */
export function rsolveRatio(coeffsIn: readonly ExprLike[], fIn: ExprLike, n: Sym): [Expr, Sym[]] | undefined {
  curN = n;
  const f = sympify(fIn);
  if (!isPolyIn(f, n)) return undefined;
  const coeffs = coeffsIn.map((c) => sympify(c));
  const r = coeffs.length - 1;
  let A = expand(subs(at(coeffs, r), n, add(n, -r)));
  let B = at(coeffs, 0);
  const h = new Dummy('h');
  const res = sylvesterResultant(A, subs(B, n, add(n, h)), n);
  const top = maxNniRoot(res, h);
  if (top === undefined) return rsolvePoly(coeffs, f, n);
  let C: Expr = S.One;
  for (let i = top; i >= 0; i--) {
    const d = gcdN(A, expand(subs(B, n, add(n, i))));
    A = quo(A, d);
    B = quo(B, subs(d, n, add(n, -i)));
    for (let j = 0; j <= i; j++) C = mul(C, subs(d, n, add(n, -j)));
  }
  const denoms = coeffs.map((_, i) => subs(C, n, add(n, i)));
  const numers: Expr[] = [];
  for (let i = 0; i <= r; i++) {
    const g = gcdN(expand(at(coeffs, i)), expand(at(denoms, i)));
    numers.push(quo(at(coeffs, i), g));
    denoms[i] = quo(at(denoms, i), g);
  }
  for (let i = 0; i <= r; i++) numers[i] = mul(at(numers, i), ...denoms.slice(0, i), ...denoms.slice(i + 1));
  const result = rsolvePoly(numers, mul(f, ...denoms), n);
  if (!result) return undefined;
  return [simplify(mul(result[0], pow(C, -1))), result[1]];
}

/** Casoratian determinant of the sequences (zero=False). */
function casoratian(seqs: Expr[], n: Sym): Expr {
  const k = seqs.length;
  return Matrix.of(Array.from({ length: k }, (_, i) => seqs.map((s) => subs(s, n, add(n, i))))).det();
}

/** SymPy rsolve_hyper: hypergeometric solutions (Petkovsek). Returns [solution, constants]. */
export function rsolveHyper(coeffsIn: readonly ExprLike[], fIn: ExprLike, n: Sym): [Expr, Sym[]] | undefined {
  curN = n;
  const coeffs = coeffsIn.map((c) => sympify(c));
  const f = sympify(fIn);
  const r = coeffs.length - 1;
  const kernel: Expr[] = [];
  let result: Expr = S.Zero;
  if (!isZeroE(f)) {
    let inhomogeneous: Expr[];
    if (f instanceof Add) {
      const similar: [Expr, Expr][] = [];
      for (const g of expand(f) instanceof Add ? expand(f).args : [expand(f)]) {
        if (!hypersimp(g, n)) return undefined;
        const hit = similar.find(([h]) => hypersimilar(g, h, n));
        if (hit) hit[1] = add(hit[1], g);
        else similar.push([g, S.Zero]);
      }
      inhomogeneous = similar.map(([g, h]) => add(g, h));
    } else if (hypersimp(f, n)) inhomogeneous = [f];
    else return undefined;
    for (let i = 0; i < inhomogeneous.length; i++) {
      const g = at(inhomogeneous, i);
      let coeff: Expr = S.One;
      const polys = [...coeffs];
      const denoms: Expr[] = coeffs.map(() => S.One);
      const s = defined(hypersimp(g, n), 'hypergeometric term ratio');
      for (let j = 1; j <= r; j++) {
        coeff = mul(coeff, subs(s, n, add(n, j - 1)));
        const [p, q] = asNumerDenom(coeff);
        polys[j] = mul(at(polys, j), p);
        denoms[j] = q;
      }
      for (let j = 0; j <= r; j++) polys[j] = mul(at(polys, j), ...denoms.slice(0, j), ...denoms.slice(j + 1));
      let R: Expr | undefined;
      const rr = rsolveRatio(polys, mul(...denoms), n);
      if (rr) R = xreplace(rr[0], rr[1].map((c) => [c, S.Zero] as [Expr, Expr]));
      else R = rsolvePoly(polys, mul(...denoms), n)?.[0];
      if (R === undefined || isZeroE(R)) return undefined;
      inhomogeneous[i] = mul(g, R);
    }
    result = simplify(add(...inhomogeneous));
  }
  const Z = new Dummy('Z');
  const p0 = at(coeffs, 0);
  const qr = subs(at(coeffs, r), n, add(n, -r + 1));
  const pRoots = distinctRoots(p0, n);
  const qRoots = distinctRoots(qr, n);
  let factors: [Expr, Expr][] = [[S.One, S.One]];
  for (const p of pRoots) {
    for (const q of qRoots) {
      if (isIntR(p) && isIntR(q) && p.p <= q.p) continue;
      factors.push([add(n, mul(-1, p)), add(n, mul(-1, q))]);
    }
  }
  factors = [...pRoots.map((p) => [add(n, mul(-1, p)), S.One] as [Expr, Expr]), ...factors, ...qRoots.map((q) => [S.One, add(n, mul(-1, q))] as [Expr, Expr])];
  for (const [A, B] of factors) {
    const polys: Expr[] = [];
    const degrees: number[] = [];
    const D = mul(A, subs(B, n, add(n, r - 1)));
    for (let i = 0; i <= r; i++) {
      const a = mul(...Array.from({ length: i }, (_, j) => subs(A, n, add(n, j))));
      const b = mul(...Array.from({ length: r - i }, (_, j) => subs(B, n, add(n, i + j))));
      const poly = quo(mul(at(coeffs, i), a, b), D);
      polys.push(poly);
      if (!isZeroE(poly)) degrees.push(lt(poly, n)[0]);
    }
    if (!degrees.length) return undefined;
    const d = Math.max(...degrees);
    let zpoly: Expr = S.Zero;
    for (let i = 0; i <= r; i++) {
      const c = defined(polyCoefficients(expand(at(polys, i)), n), 'polynomial coefficients').get(d) ?? S.Zero;
      if (!isZeroE(c)) zpoly = add(zpoly, mul(c, pow(Z, i)));
    }
    for (const z of distinctRoots(zpoly, Z)) {
      if (isZeroE(z)) continue;
      const recurr = polys.map((p, i) => mul(p, pow(z, i)));
      let sol: Expr[];
      if (d === 0 && !isZeroE(expand(add(...recurr.map((c, j) => mul(c, j)))))) sol = [new Sym('C0')];
      else {
        // a homogeneous polynomial recurrence always has a polynomial solution (possibly 0), and each
        // free constant C_i multiplies a nonzero polynomial Q_i
        const [s0, syms] = defined(rsolvePoly(recurr, 0, n, 0), 'homogeneous polynomial solution');
        const s0x = expand(s0);
        sol = syms.map((c) => getOrThrow(defined(polyCoefficients(s0x, c), 'polynomial in the constants'), 1));
      }
      for (const Cn of sol) {
        const ratio = simplify(mul(z, A, subs(Cn, n, add(n, 1)), pow(B, -1), pow(Cn, -1)));
        let n0: Expr = S.Zero;
        for (const nr of distinctRoots(asNumerDenom(ratio)[1], n)) {
          if (nr.has(S.I)) return undefined;
          const cand = add(nr, 1);
          if (cand instanceof Rational && n0 instanceof Rational && cand.value > n0.value) n0 = cand;
        }
        // product over a fresh index (n is also the upper limit) of the ratio in num/den form, which
        // Product evaluates through rising factorials like SymPy's as_numer_denom step
        const k = new Dummy('k');
        let K = product(subs(cancel(ratio), n, k), [k, n0, add(n, -1)]);
        const hasComb = (e: Expr): boolean => ('name' in e && typeof e.name === 'string' && ['factorial', 'ff', 'rf'].includes(e.name)) || e.args.some(hasComb);
        if (hasComb(K)) K = simplify(K);
        if (!isZeroE(simplify(casoratian([...kernel, K], n)))) kernel.push(K);
      }
    }
  }
  kernel.sort((u, v) => compareKeys(sortKey(u), sortKey(v)));
  const consts = kernel.map((_, i) => new Sym(`C${i}`));
  result = add(result, ...kernel.map((k, i) => mul(at(consts, i), k)));
  return [result, consts];
}

/**
 * SymPy rsolve(f, y(n), init): solve a linear recurrence with polynomial
 * coefficients. init maps indices (or y(i)) to values.
 */
export function rsolve(fIn: ExprLike, y: Expr, init?: [ExprLike, ExprLike][]): Expr | undefined {
  let f = sympify(fIn);
  if (f instanceof Rel) f = add(f.lhs, mul(-1, f.rhs));
  if (!(y instanceof UndefFn) || !(y.args[0] instanceof Sym)) throw new TypeError('rsolve: y(n) expected');
  const n = y.args[0];
  const hPart = new Map<number, Expr[]>();
  const iPart: Expr[] = [];
  const e = expand(f);
  for (const g of e instanceof Add ? e.args : [e]) {
    const fs = g instanceof Mul ? g.args : [g];
    const dep = fs.filter((t): t is UndefFn => t instanceof UndefFn && t.name === y.name);
    if (!dep.length) {
      iPart.push(g);
      continue;
    }
    const k = add(first(first(dep).args), mul(-1, n));
    // SymPy raises ValueError for a product of terms y(n + k) (nonlinear) or a shift that is not an integer
    if (dep.length > 1 || !isIntR(k)) throw new TypeError(`rsolve: '${y.name}(${n.name} + k)' expected, got '${g.toString()}'`);
    const coeff = mul(...fs.filter((t) => t !== dep[0]));
    const key = Number(k.p);
    hPart.set(key, [...(hPart.get(key) ?? []), coeff]);
  }
  const H = new Map<number, Expr>([...hPart].map(([k, cs]) => [k, simplify(add(...cs))]));
  let ip = add(...iPart);
  const ipTerms = expand(ip);
  if (!isZeroE(ip) && hypersimp(ip, n) === undefined && !(ipTerms instanceof Add && ipTerms.args.every((t) => hypersimp(t, n) !== undefined))) {
    throw new TypeError(`rsolve: the independent term should be a sum of hypergeometric functions, got '${ip.toString()}'`);
  }
  let common: Expr = S.One;
  for (const c of H.values()) {
    const [num, den] = asNumerDenom(c);
    if (!isPolyIn(num, n) || !isPolyIn(den, n)) throw new TypeError(`rsolve: polynomial or rational function expected, got '${c.toString()}'`);
    if (!isPolyIn(c, n)) common = polyLcm(common, den);
  }
  const [iNum, iDen] = asNumerDenom(ip);
  if (isPolyIn(iDen, n)) common = polyLcm(common, iDen);
  if (!(common instanceof Rational && common.isOne)) {
    for (const [k, c] of H) {
      const [num, den] = asNumerDenom(c);
      H.set(k, mul(num, quo(common, den)));
    }
    ip = mul(iNum, quo(common, iDen));
  }
  const kMin = Math.min(...H.keys());
  let HH = H;
  if (kMin < 0) {
    const K = -kMin;
    ip = expand(subs(ip, n, add(n, K)));
    HH = new Map([...H].map(([k, c]) => [k + K, expand(subs(c, n, add(n, K)))]));
  }
  const kMax = Math.max(...HH.keys());
  const coeffs = Array.from({ length: kMax + 1 }, (_, i) => HH.get(i) ?? S.Zero);
  const res = rsolveHyper(coeffs, mul(-1, ip), n);
  if (!res) return undefined;
  let [solution, symbols] = res;
  // The hypergeometric solutions found may not span the solution space (an
  // order-k recurrence has k independent solutions). Without enough initial
  // values that pin the solution down, such a partial answer (SymPy returns
  // e.g. 0 for y(n+2) - n*y(n+1) - y(n)) is not the general solution.
  const order = kMax;
  const pinned = (init?.length ?? 0) >= order;
  if (symbols.length < order && !pinned) return undefined;
  if (init?.length && symbols.length) {
    const eqs: Expr[] = [];
    for (const [kIn, v] of init) {
      const k = sympify(kIn);
      const i = k instanceof UndefFn ? first(k.args) : k;
      eqs.push(add(subs(solution, n, i), mul(-1, v)));
    }
    const s = linsolve(eqs, symbols);
    if (!s) return undefined;
    solution = xreplace(solution, symbols.map((c, i) => [c, at(s, i)] as [Expr, Expr]));
    symbols = [];
  }
  // a partial family is the answer only when it meets every initial value
  if (init?.length) {
    for (const [kIn, v] of init) {
      const k = sympify(kIn);
      const i = k instanceof UndefFn ? first(k.args) : k;
      const r = simplify(add(subs(solution, n, i), mul(-1, v)));
      if (!(r instanceof Rational && r.isZero)) return undefined;
    }
  }
  return solution;
}
