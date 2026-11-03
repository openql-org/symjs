// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/numeric/mpspecialfns.ts through evalf. Expected values from
// SymPy 1.14 (str(e.evalf(15)), str(e.evalf(50))).

import { describe, expect, it } from 'vitest';
import { evalf, parse, sstr } from '../../src';
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
    // mpmath ellipe(0.5, 0.5); SymPy evaluates dirichlet_eta(s, a), not implemented here
    expect(call('elliptic_e', [half, half], 15)).toEqual(['0.489910959792517', '0.0']);
    expect(() => call('dirichlet_eta', [half, half], 15)).toThrow('dirichlet_eta(s, a)');
  });
});
