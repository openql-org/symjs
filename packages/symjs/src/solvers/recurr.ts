// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Linear recurrences with polynomial coefficients (port of SymPy
 * sympy.solvers.recurr: rsolve_poly, rsolve_ratio, rsolve_hyper, rsolve).
 */

import { Add, Dummy, Expr, ExprLike, Mul, Rational, S, Sym, UndefFn } from '../core/nodes';
import { add, mul, pow, sympify } from '../core/ops';
import { xreplace } from '../core/traverse';
import { asNumerDenom } from '../core/methods';
import { binomial } from '../functions/special';
import { Matrix } from '../matrices/matrix';
import { polyCoefficients, roots } from '../polys/poly';
import { Poly, polyLcm } from '../polys/sympoly';
import { product } from '../concrete/summations';
import { compareKeys, sortKey } from '../printing/sortkey';
import { expandMul as expand } from '../simplify/expand';
import { simplify } from '../simplify/simplify';
import { linsolve, solveUndeterminedCoeffs } from './solve';

const isZeroE = (e: Expr) => e instanceof Rational && e.isZero;
const isIntR = (e: Expr): e is Rational => e instanceof Rational && e.isInteger;
const subs = (e: Expr, x: Sym, v: ExprLike) => xreplace(e, [[x, sympify(v)]]);
const isPolyIn = (e: Expr, x: Sym) => polyCoefficients(expand(e), x) !== undefined;

/** Degree and leading coefficient of e as a polynomial in x ([-Infinity, 0] for zero). */
function lt(e: Expr, x: Sym): [number, Expr] {
  const pc = polyCoefficients(expand(e), x)!;
  let d = -Infinity;
  for (const [k, c] of pc) if (!isZeroE(c) && k > d) d = k;
  return d === -Infinity ? [d, S.Zero] : [d, pc.get(d)!];
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

/** Largest non-negative integer root of e in x, or undefined. */
function maxNniRoot(e: Expr, x: Sym): number | undefined {
  const rs = distinctRoots(e, x).filter((r): r is Rational => isIntR(r) && !r.isNegative);
  return rs.length ? Math.max(...rs.map((r) => Number(r.p))) : undefined;
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
    for (let j = i; j <= r; j++) p = add(p, mul(coeffs[j]!, binomial(j, i)));
    polys.push(expand(p));
    const [d, c] = lt(p, n);
    terms.push([c, d]);
  }
  let d = terms[0]![1];
  let b = terms[0]![1];
  for (let i = 1; i <= r; i++) {
    if (terms[i]![1] > d) d = terms[i]![1];
    if (terms[i]![1] - i > b) b = terms[i]![1] - i;
  }
  const x = new Dummy('x');
  let degreePoly: Expr = S.Zero;
  for (let i = 0; i <= r; i++) {
    if (terms[i]![1] - i === b) {
      let ffx: Expr = S.One;
      for (let j = 0; j < i; j++) ffx = mul(ffx, add(x, -j));
      degreePoly = add(degreePoly, mul(terms[i]![0], ffx));
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
      y = add(y, mul(C[i]!, pow(n, i)));
    }
    let E: Expr = S.Zero;
    for (let i = 0; i <= r; i++) E = add(E, mul(coeffs[i]!, subs(y, n, add(n, i))));
    let sols: Expr[][];
    try {
      sols = solveUndeterminedCoeffs(add(E, mul(-1, f)), C, [n]);
    } catch {
      return undefined;
    }
    if (!sols.length) return undefined;
    const sol = sols[0]!;
    _C = C;
    C = C.filter((c, i) => sol[i]!.key === c.key);
    result = xreplace(y, _C.map((c, i) => [c, sol[i]!] as [Expr, Expr]));
  } else {
    const A = r;
    const U = N + A + b + 1;
    const nra = maxNniRoot(polys[r]!, n);
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
      for (let k = 1; k <= d; k++) I[k] = mul(I[k - 1]!, add(x, i - k + 1), Rational.of(1, k));
      let al: Expr = S.Zero;
      for (let j = 0; j <= A; j++) {
        for (let k = 0; k <= d; k++) {
          const B = i + j < 0 || i + j > k ? S.Zero : binomial(k, i + j);
          if (isZeroE(B)) continue;
          al = add(al, mul(I[k]!, B, delta(polys[j]!, k)));
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
        const B = subs(alpha.get(k - A)!, x, i - k);
        for (let j = 0; j < A; j++) v[j] = add(v[j]!, mul(B, V[i - k]![j]!));
        if (!homogeneous) g = add(g, mul(B, G[i - k]!));
      }
      const denom = subs(alpha.get(-A)!, x, i);
      for (let j = 0; j < A; j++) V[i]![j] = mul(-1, v[j]!, pow(denom, -1));
      if (!homogeneous) G[i] = mul(add(delta(f, i - A), mul(-1, g)), pow(denom, -1));
    }
    const P: Expr[] = Array.from({ length: U }, () => S.One);
    for (let i = 1; i < U; i++) P[i] = expand(mul(P[i - 1]!, add(n, -a - i + 1), Rational.of(1, i)));
    const Q: Expr[] = [];
    for (let i = 0; i < A; i++) Q.push(add(...V.map((row, j) => expand(mul(row[i]!, P[j]!)))));
    const h = homogeneous ? S.Zero : add(...G.map((g, j) => expand(mul(g, P[j]!))));
    C = Array.from({ length: A }, (_, i) => new Sym(`C${i + shift}`));
    const gf = (i: number) => add(...C.map((c, j) => mul(c, delta(Q[j]!, i))));
    const E: Expr[] = [];
    for (let i = N + 1; i < U; i++) E.push(homogeneous ? gf(i) : add(gf(i), delta(h, i)));
    let solved = new Map<string, Expr>();
    if (E.length) {
      const sol = linsolve(E, C);
      if (!sol) return homogeneous ? [S.Zero, []] : undefined;
      solved = new Map(C.map((c, i) => [c.key, sol[i]!] as [string, Expr]).filter(([k, v]) => v.key !== k));
    }
    result = h;
    _C = [...C];
    const remaining: Sym[] = [];
    C.forEach((c, i) => {
      const sv = solved.get(c.key);
      const s = sv ? mul(sv, Q[i]!) : mul(c, Q[i]!);
      if (!sv) remaining.push(c);
      result = add(result, expand(s));
    });
    C = remaining;
  }
  if (C.length !== _C.length || C.some((c, i) => c.key !== _C[i]!.key)) {
    result = xreplace(result, C.map((c, i) => [c, _C[i]!] as [Expr, Expr]));
    C = _C.slice(0, C.length);
  }
  return [result, C];
}

/** Resultant of f and g in x via the Sylvester determinant (coefficients may contain other symbols). */
function sylvesterResultant(f: Expr, g: Expr, x: Sym): Expr {
  const cf = (e: Expr) => {
    const pc = polyCoefficients(expand(e), x)!;
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
  for (let i = 0; i < k; i++) rows.push(Array.from({ length: N }, (_, j) => (j - i >= 0 && j - i <= m ? a[j - i]! : S.Zero)));
  for (let i = 0; i < m; i++) rows.push(Array.from({ length: N }, (_, j) => (j - i >= 0 && j - i <= k ? b[j - i]! : S.Zero)));
  return expand(Matrix.of(rows).det());
}

/** SymPy rsolve_ratio: rational solutions (Abramov). */
export function rsolveRatio(coeffsIn: readonly ExprLike[], fIn: ExprLike, n: Sym): [Expr, Sym[]] | undefined {
  curN = n;
  const f = sympify(fIn);
  if (!isPolyIn(f, n)) return undefined;
  const coeffs = coeffsIn.map((c) => sympify(c));
  const r = coeffs.length - 1;
  let A = expand(subs(coeffs[r]!, n, add(n, -r)));
  let B = coeffs[0]!;
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
    const g = gcdN(expand(coeffs[i]!), expand(denoms[i]!));
    numers.push(quo(coeffs[i]!, g));
    denoms[i] = quo(denoms[i]!, g);
  }
  for (let i = 0; i <= r; i++) numers[i] = mul(numers[i]!, ...denoms.slice(0, i), ...denoms.slice(i + 1));
  const result = rsolvePoly(numers, mul(f, ...denoms), n);
  if (!result) return undefined;
  return [simplify(mul(result[0], pow(C, -1))), result[1]];
}

/** f(n+1)/f(n) simplified (SymPy hypersimp), or undefined when not a rational function of n. */
function hypersimp(f: Expr, n: Sym): Expr | undefined {
  const q = simplify(mul(subs(f, n, add(n, 1)), pow(f, -1)));
  const [num, den] = asNumerDenom(q);
  return isPolyIn(num, n) && isPolyIn(den, n) ? q : undefined;
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
        const hit = similar.find(([h]) => {
          const q = simplify(mul(g, pow(h, -1)));
          const [a, b] = asNumerDenom(q);
          return isPolyIn(a, n) && isPolyIn(b, n);
        });
        if (hit) hit[1] = add(hit[1], g);
        else similar.push([g, S.Zero]);
      }
      inhomogeneous = similar.map(([g, h]) => add(g, h));
    } else if (hypersimp(f, n)) inhomogeneous = [f];
    else return undefined;
    for (let i = 0; i < inhomogeneous.length; i++) {
      const g = inhomogeneous[i]!;
      let coeff: Expr = S.One;
      const polys = [...coeffs];
      const denoms: Expr[] = coeffs.map(() => S.One);
      const s = hypersimp(g, n)!;
      for (let j = 1; j <= r; j++) {
        coeff = mul(coeff, subs(s, n, add(n, j - 1)));
        const [p, q] = asNumerDenom(coeff);
        polys[j] = mul(polys[j]!, p);
        denoms[j] = q;
      }
      for (let j = 0; j <= r; j++) polys[j] = mul(polys[j]!, ...denoms.slice(0, j), ...denoms.slice(j + 1));
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
  const p0 = coeffs[0]!;
  const qr = subs(coeffs[r]!, n, add(n, -r + 1));
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
      const poly = quo(mul(coeffs[i]!, a, b), D);
      polys.push(poly);
      if (!isZeroE(poly)) degrees.push(lt(poly, n)[0]);
    }
    if (!degrees.length) return undefined;
    const d = Math.max(...degrees);
    let zpoly: Expr = S.Zero;
    for (let i = 0; i <= r; i++) {
      const c = polyCoefficients(expand(polys[i]!), n)!.get(d) ?? S.Zero;
      if (!isZeroE(c)) zpoly = add(zpoly, mul(c, pow(Z, i)));
    }
    for (const z of distinctRoots(zpoly, Z)) {
      if (isZeroE(z)) continue;
      const recurr = polys.map((p, i) => mul(p, pow(z, i)));
      let sol: Expr[];
      if (d === 0 && !isZeroE(expand(add(...recurr.map((c, j) => mul(c, j)))))) sol = [new Sym('C0')];
      else {
        const rp = rsolvePoly(recurr, 0, n, 0);
        if (!rp) continue;
        const [s0, syms] = rp;
        sol = syms.map((c) => polyCoefficients(expand(s0), c)?.get(1) ?? S.Zero);
      }
      for (const Cn of sol) {
        if (isZeroE(Cn)) continue;
        const ratio = simplify(mul(z, A, subs(Cn, n, add(n, 1)), pow(B, -1), pow(Cn, -1)));
        let n0: Expr = S.Zero;
        for (const nr of distinctRoots(asNumerDenom(ratio)[1], n)) {
          if (nr.has(S.I)) return undefined;
          const cand = add(nr, 1);
          if (cand instanceof Rational && n0 instanceof Rational && cand.value > n0.value) n0 = cand;
        }
        let K = product(ratio, [n, n0, add(n, -1)]);
        const hasComb = (e: Expr): boolean => ['factorial', 'ff', 'rf'].includes((e as { name?: string }).name ?? '') || e.args.some(hasComb);
        if (hasComb(K)) K = simplify(K);
        if (!isZeroE(simplify(casoratian([...kernel, K], n)))) kernel.push(K);
      }
    }
  }
  kernel.sort((u, v) => compareKeys(sortKey(u), sortKey(v)));
  const consts = kernel.map((_, i) => new Sym(`C${i}`));
  result = add(result, ...kernel.map((k, i) => mul(consts[i]!, k)));
  return [result, consts];
}

/**
 * SymPy rsolve(f, y(n), init): solve a linear recurrence with polynomial
 * coefficients. init maps indices (or y(i)) to values.
 */
export function rsolve(fIn: ExprLike, y: Expr, init?: [ExprLike, ExprLike][]): Expr | undefined {
  let f = sympify(fIn);
  if (f.kind === 'Rel') f = add(f.args[0]!, mul(-1, f.args[1]!));
  if (!(y instanceof UndefFn) || !(y.args[0] instanceof Sym)) throw new Error('rsolve: y(n) expected');
  const n = y.args[0];
  const hPart = new Map<number, Expr[]>();
  const iPart: Expr[] = [];
  const e = expand(f);
  for (const g of e instanceof Add ? e.args : [e]) {
    const fs = g instanceof Mul ? g.args : [g];
    const dep = fs.filter((t) => t instanceof UndefFn && t.name === y.name);
    if (!dep.length) {
      iPart.push(g);
      continue;
    }
    if (dep.length > 1) throw new Error('rsolve: nonlinear recurrence');
    const k = add(dep[0]!.args[0]!, mul(-1, n));
    if (!isIntR(k)) throw new Error(`rsolve: '${y.name}(${n.name} + k)' expected`);
    const coeff = mul(...fs.filter((t) => t !== dep[0]));
    const key = Number(k.p);
    hPart.set(key, [...(hPart.get(key) ?? []), coeff]);
  }
  const H = new Map<number, Expr>([...hPart].map(([k, cs]) => [k, simplify(add(...cs))]));
  let ip = add(...iPart);
  let common: Expr = S.One;
  for (const c of H.values()) {
    const [num, den] = asNumerDenom(c);
    if (!isPolyIn(num, n) || !isPolyIn(den, n)) throw new Error('rsolve: polynomial or rational coefficients expected');
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
  if (init && init.length && symbols.length) {
    const eqs: Expr[] = [];
    for (const [kIn, v] of init) {
      const k = sympify(kIn);
      const i = k instanceof UndefFn ? k.args[0]! : k;
      eqs.push(add(subs(solution, n, i), mul(-1, v)));
    }
    const s = linsolve(eqs, symbols);
    if (!s) return undefined;
    solution = xreplace(solution, symbols.map((c, i) => [c, s[i]!] as [Expr, Expr]));
    symbols = [];
  }
  // a partial family is the answer only when it meets every initial value
  if (init && init.length) {
    for (const [kIn, v] of init) {
      const k = sympify(kIn);
      const i = k instanceof UndefFn ? k.args[0]! : k;
      const r = simplify(add(subs(solution, n, i), mul(-1, v)));
      if (!(r instanceof Rational && r.isZero)) return undefined;
    }
  }
  return solution;
}
