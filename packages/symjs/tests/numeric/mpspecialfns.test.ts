// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/numeric/mpspecialfns.ts through evalf. Expected values from
// SymPy 1.14 (str(e.evalf(15)), str(e.evalf(50))).

import { describe, expect, it } from 'vitest';
import { Rational, add, evalf, I, jn, parse, sstr, yn } from '../../src';
import * as F from '../../src/numeric/mpf';
import type { Mpc } from '../../src/numeric/mpfun';
import { mpFns } from '../../src/numeric/mpeval';
import '../../src/numeric/mpspecialfns';

describe('evalf of the special functions equals SymPy', () => {
  const cases: [string, string, string][] = [
    // below -1/e the principal branch is complex
    ['LambertW(-exp(1/2)/2)', '-0.452241436945604 + 1.21427390604918*I', '-0.45224143694560395642763002734131455197143531036268 + 1.2142739060491820848363181897135777395725449076211*I'],
    ['LambertW(-exp(1/2)/2, -1)', '-0.452241436945604 - 1.21427390604918*I', '-0.45224143694560395642763002734131455197143531036268 - 1.2142739060491820848363181897135777395725449076211*I'],
    // the power series of Ai cancels about 2/3 |z|^(3/2) log2(e) bits twice
    ['airyai(30)', '3.20821759155050e-49', '3.2082175915504955710752869331847527965668519217576e-49'],
    // the asymptotic expansions (Ei(10**7) used to sum ~10**7 terms at 14 million bits)
    ['Ei(10**7)', '6.59223319384183e+4342937', '6.5922331938418247960950808669733897996856860955836e+4342937'],
    ['expint(1, 1000)', '5.07089306023517e-438', '5.0708930602351665499272009996859251446672285374922e-438'],
    ['expint(3, -5/2)', '-0.786153989327049 - 9.8174770424681*I', '-0.78615398932704870813829196811547338879365669767189 - 9.8174770424681038701957605727484465131161543730472*I'],
    ['Si(10**7)', '1.57079641752193', '1.5707964175219310319255313594660789637372438054862'],
    ['Ci(-5/2)', '0.285871196365383 + 3.14159265358979*I', '0.28587119636538349538910064792523607196923287667108 + 3.1415926535897932384626433832795028841971693993751*I'],
    ['besselk(0, 30)', '2.13247749646306e-14', '0.000000000000021324774964630563711668960629653764399270618437289'],
  ];
  it.each(cases)('%s', (e, want15, want50) => {
    expect([sstr(evalf(parse(e), 15)), sstr(evalf(parse(e), 50))]).toEqual([want15, want50]);
  });
});

// The functions below are not defined in symjs yet (SymPy dirichlet_eta,
// elliptic_k, elliptic_e); their evaluators are registered under the SymPy
// names. Expected values from mpmath 1.3.0 altzeta at mp.dps = 15 and 50.
describe('evaluators registered for functions symjs does not define yet', () => {
  const call = (name: string, args: Mpc[], d: number): string[] => {
    const f = mpFns[name];
    if (!f) throw new TypeError(name);
    const v = f(args, F.dpsToPrec(d));
    return [F.toStr(v[0], d), F.toStr(v[1], d)];
  };
  const cases: [string, string, [string, string], [string, string][]][] = [
    ["altzeta(3)", "eta", ["3.0", "0.0"], [["0.901542677369696", "0.0"], ["0.90154267736969571404980362113358749307373971925537", "0.0"]]],
    ["altzeta(1)", "eta", ["1.0", "0.0"], [["0.693147180559945", "0.0"], ["0.69314718055994530941723212145817656807550013436025", "0.0"]]],
    ["altzeta(0.5)", "eta", ["0.5", "0.0"], [["0.60489864342163", "0.0"], ["0.60489864342163037024726591423595549975976254513025", "0.0"]]],
    ["altzeta(1.0000001)", "eta", ["1.0000001000000000583867176828789524734020233154296875", "0.0"], [["0.693147196546835", "0.0"], ["0.69314719654683536613158823904330787638748658781457", "0.0"]]],
    ["altzeta(-3)", "eta", ["-3.0", "0.0"], [["-0.125", "0.0"], ["-0.125", "0.0"]]],
    ["altzeta(0.5+14*I)", "eta", ["0.5", "14.0"], [["0.0122208917707548", "-0.2522997666529"], ["0.012220891770754763065992914334065006756920245672902", "-0.2522997666528998332026186378454967217751918995619"]]],
    ["altzeta(2)", "eta", ["2.0", "0.0"], [["0.822467033424113", "0.0"], ["0.8224670334241132182362075833230125946094749506034", "0.0"]]],
  ];
  it.each(cases)('dirichlet_eta: %s', (_, __, [re, im], want) => {
    expect([15, 50].map((d) => call('dirichlet_eta', [[F.fromStr(re, F.dpsToPrec(d)), F.fromStr(im, F.dpsToPrec(d))]], d))).toEqual(want);
  });
  it('elliptic_k, elliptic_e and the unimplemented forms', () => {
    const half: Mpc = [F.fromStr('0.5', 53), F.ZERO];
    // mpmath ellipk(0.5), ellipe(0.5)
    expect(call('elliptic_k', [half], 15)).toEqual(['1.85407467730137', '0.0']);
    expect(call('elliptic_e', [half], 15)).toEqual(['1.35064388104768', '0.0']);
    // mpmath ellipe(0.5, 0.5); dirichlet_eta(s, a) = zeta(s, a) - 2**(1 - s)*zeta(s, (a + 1)/2) as SymPy
    // evaluates it (functions/special/zetafunctions.ts): mpmath zeta(0.5, 0.5) - sqrt(2)*zeta(0.5, 0.75) = 0.9442583142382
    expect(call('elliptic_e', [half, half], 15)).toEqual(['0.489910959792517', '0.0']);
    expect(call('dirichlet_eta', [half, half], 13)).toEqual(['0.9442583142382', '0.0']);
  });
});

describe('arbitrary-precision kernels of functions that had double-precision values only', () => {
  const ev = (e: string, d = 15, subs?: Record<string, string>) =>
    sstr(evalf(parse(e), d, subs ? { subs: Object.fromEntries(Object.entries(subs).map(([k, v]) => [k, parse(v)])) } : undefined));
  it('ff, rf and floor/ceiling equal SymPy at 15 and 50 digits', () => {
    // SymPy N(ff(1/3, 1/7)), N(rf(1/3, 1/7)), N(rf(1 + 2*I, 1/3), 50); poles: rf(1/2, -1/2) = oo, rf(-2, 1/2) = 0
    expect([ev('ff(1/3,1/7)'), ev('ff(1/3,1/7)', 50)]).toEqual(['0.969836281200561', '0.96983628120056115868800462041223595166465318989283']);
    expect([ev('rf(1/3,1/7)'), ev('rf(1/3,1/7)', 50)]).toEqual(['0.694288639004937', '0.69428863900493693903220918313837119649232477350338']);
    expect(ev('rf(1+2*I,1/3)', 50)).toBe('1.1709915795383513625101243998512965184443524695337 + 0.515324519075601473115623769077319168260837934663*I');
    expect([ev('rf(1/2,-1/2)'), ev('rf(-2,1/2)'), ev('ff(5/2,7/2)'), ev('ff(-3,5/2)')]).toEqual(['oo', '0', '0', 'oo']);
    // SymPy floor(x).evalf(subs={x: exp(100) + 1/3}) and N(floor(exp(100) + 1/3), 50) (an integer there)
    expect(ev('floor(x)', 50, { x: 'exp(100) + 1/3' })).toBe('26881171418161354484126255515800135873611119.000000');
    expect(ev('ceiling(x)', 50, { x: 'exp(100) + 1/3' })).toBe('26881171418161354484126255515800135873611120.000000');
    expect(ev('ceiling(x)', 50, { x: '-pi' })).toBe('-3.0000000000000000000000000000000000000000000000000');
  });
  it('Min and Max of real numbers at full precision', () => {
    // SymPy Max(x, exp(-200)).evalf(subs={x: 1/3}), Max(x, 1).evalf(50, subs={x: pi}), Min(x, sqrt(2)).evalf(30, subs={x: 7/5})
    expect(ev('Max(x, exp(-200))', 15, { x: '1/3' })).toBe('0.333333333333333');
    expect(ev('Max(x, 1)', 50, { x: 'pi' })).toBe('3.1415926535897932384626433832795028841971693993751');
    expect(ev('Min(x, sqrt(2))', 30, { x: '7/5' })).toBe('1.40000000000000000000000000000');
    const f = mpFns['Max'];
    if (!f) throw new TypeError('Max');
    expect(() => f([[F.ONE, F.ONE], [F.ONE, F.ZERO]], 53)).toThrow(TypeError);
  });
  it('the kernels of rf (poles cancelling), factorial2 and erf2inv equal mpmath', () => {
    const k = (name: string, args: [string, string][], d: number): string[] => {
      const f = mpFns[name];
      if (!f) throw new TypeError(name);
      const p = F.dpsToPrec(d);
      const r = f(args.map(([a, b]) => [F.fromStr(a, p), F.fromStr(b, p)] as Mpc), p);
      return [F.toStr(r[0], d), F.toStr(r[1], d)];
    };
    // mpmath rf(-3, -2) = 0.05, rf(-3, -1) = -0.25 (gammaprod: the poles cancel in pairs)
    expect(k('rf', [['-3', '0'], ['-2', '0']], 15)).toEqual(['0.05', '0.0']);
    expect(k('rf', [['-3', '0'], ['-1', '0']], 15)).toEqual(['-0.25', '0.0']);
    // mpmath fac2(1/3), fac2(2.5 + 1j), fac2(7)
    expect(k('factorial2', [['0.333333333333333333333333333333333333333333333333333333333333', '0']], 50)).toEqual(['0.98417717502560779229558551308467488520764943993939', '0.0']);
    expect(k('factorial2', [['2.5', '1']], 50)).toEqual(['1.7684872940073224591553381746441104604250567971844', '-1.386061903492397069215928277193751635778688198088']);
    expect(k('factorial2', [['7', '0']], 15)).toEqual(['105.0', '0.0']);
    // mpmath erfinv(erf(1/3) + 1/2); SymPy leaves erf2inv unevaluated (it has no mpmath function)
    expect(ev('erf2inv(1/3, 1/2)', 50)).toBe('1.0505661875336908676385301100272178163792888904188');
    expect(() => k('erf2inv', [['0', '1'], ['0', '0']], 15)).toThrow('complex erf2inv');
    expect(() => k('erf2inv', [['0', '0'], ['1', '0']], 15)).toThrow(RangeError);
    // erfcinv(3): 1 - 3 is outside the domain of erfinv
    expect(() => k('erfcinv', [['3', '0']], 15)).toThrow('erfinv domain');
  });
});

describe('jn and yn of an integer order (SymPy rewrite(besselj)._eval_evalf)', () => {
  it('equal SymPy at 15 and 50 digits', () => {
    const third = Rational.of(1, 3);
    // SymPy N(jn(2, 1/3)), N(yn(2, 1/3), 50), N(yn(3, 2 + I), 50), N(yn(-2, 5/2))
    expect(sstr(evalf(jn(2, third)))).toBe('0.00734879960195811');
    expect(sstr(evalf(jn(2, third), 50))).toBe('0.0073487996019581070371704436256308611774868494544638');
    expect(sstr(evalf(yn(2, third), 50))).toBe('-82.540898626045648414966442900944443775712648552212');
    expect(sstr(evalf(yn(3, add(2, I)), 50))).toBe('-0.20833069433259320268765232865836907234824655659444 + 0.79090604895293097174587374576544199439598102848762*I');
    expect(sstr(evalf(yn(-2, Rational.of(5, 2))))).toBe('-0.416212989275407');
    // a non-integer order is not evaluated (SymPy returns jn(1/2, 2))
    expect(sstr(evalf(jn(Rational.of(1, 2), 2)))).toBe('jn(1/2, 2)');
  });
});
