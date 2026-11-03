// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/numeric/mpspecial.ts.

import { afterEach, describe, expect, it } from 'vitest';
import { evalf, parse, sstr } from '../../src';
import type { Expr } from '../../src';
import * as C from '../../src/numeric/mpconst';
import * as F from '../../src/numeric/mpf';
import { czeta } from '../../src/numeric/mpspecial';
import { REF, refForm } from './mpconst.ref';

const ref = (c: string, p: number): [string, number] | undefined => REF[c]?.[p];
const p = (s: string) => parse(s);

afterEach(() => C.clearConstantCache());

// The constants through the default method tables and the cache (mpfun mp*
// functions, evalf) against mpmath 1.3.0 / SymPy 1.14.0 (see mpconst.ref.ts).

describe('constants by binary splitting equal mpmath', () => {
  it('zeta(3) is Apery constant (also when evaluated by czeta)', () => {
    const z = czeta([F.fromInt(3n), F.ZERO], 1000);
    expect(refForm(z[0], 1000)).toEqual(ref('apery', 1000));
    expect(F.isZero(z[1])).toBe(true);
    // other arguments still go through Euler-Maclaurin
    expect(F.toStr(czeta([F.fromInt(2n), F.ZERO], 60)[0], 15)).toBe('1.64493406684823');
    expect(F.toStr(czeta([F.fromInt(3n), F.ZERO], 60, [F.fromInt(2n), F.ZERO])[0], 15)).toBe('0.202056903159594');
  });

  it('zeta(5) by binary splitting in czeta', () => {
    const z = czeta([F.fromInt(5n), F.ZERO], 1000);
    expect(refForm(z[0], 1000)).toEqual(ref('zeta5', 1000));
    expect(F.isZero(z[1])).toBe(true);
    expect(F.toStr(czeta([F.fromInt(5n), F.ZERO], 100, [F.fromInt(2n), F.ZERO])[0], 25)).toBe('0.03692775514336992633136549');
  });
});

// Expected values from SymPy 1.14: f.evalf(30, subs={...}). SymPy does not
// evaluate erf2 and erfcinv numerically; their values are from
// (erf(y) - erf(x)).evalf(30) and erfinv(1 - x).evalf(30).

describe('arbitrary-precision special functions (evalf at 30 digits)', () => {
  const cases: [string, Record<string, Expr>, string][] = [
    ['loggamma(x)', { x: p('3/2 + 2*I') }, '-1.49919637258509548836373883707 + 0.733280681690997876125188005154*I'],
    ['loggamma(x)', { x: p('-5/2 + I/3') }, '-0.508109407764131970187068003201 - 9.05639347366177129181262553023*I'],
    ['loggamma(x)', { x: p('1/3') }, '0.985420646927767069187174036978'],
    ['loggamma(x)', { x: p('40') }, '106.631760260643459126201078917'],
    ['gamma(x)', { x: p('-7/2') }, '0.270088205852269108921625521271'],
    ['gamma(x)', { x: p('1/3 + I') }, '0.1747093144498332477574880816 - 0.494868898934569270515038744685*I'],
    ['factorial(x)', { x: p('5/2') }, '3.32335097044784255118406403126'],
    ['polygamma(1, x)', { x: p('1/3') }, '10.0955971254270940817920040999'],
    ['polygamma(2, x)', { x: p('2 + I') }, '-0.131447068412064828263365457019 + 0.266652850345066212402695377631*I'],
    ['polygamma(0, x)', { x: p('-5/2') }, '1.10315664064524318722569033367'],
    ['harmonic(x)', { x: p('5/2') }, '1.68037230554677604783220242375'],
    ['catalan(x)', { x: p('5/2') }, '3.10427927097334902528260902273'],
    ['beta(x, y)', { x: p('5/2'), y: p('1/3') }, '2.06503182784294173009411900733'],
    ['zeta(x)', { x: p('5/2') }, '1.34148725725091717975676969335'],
    ['zeta(x)', { x: p('1/2 + 14*I') }, '0.022241142609993589246213199204 - 0.103258123266450057902363095553*I'],
    ['erf2(x, y)', { x: p('1/3'), y: p('2') }, '0.632674153252889800753890616219'],
    ['erfinv(x)', { x: p('1/3') }, '0.304570194173985625197290686982'],
    ['erfinv(x)', { x: p('-99/100') }, '-1.82138636771844967304021031862'],
    ['erfinv(x)', { x: p('999999/1000000') }, '3.45891073727950002215092763596'],
    ['erfcinv(x)', { x: p('1/3') }, '0.684070349656622638909098035859'],
    ['erf(x)', { x: p('1 + I') }, '1.31615128169794764488027108024 + 0.190453469237834686284108861969*I'],
    ['erfc(x)', { x: p('3') }, '0.0000220904969985854413727761295823'],
    ['erfi(x)', { x: p('1/2') }, '0.614952094696510980839681185624'],
    ['fresnels(x)', { x: p('3/2') }, '0.697504960082093013080655163187'],
    ['fresnelc(x)', { x: p('1 + I') }, '2.55579377810243902463452238835 + 2.55579377810243902463452238835*I'],
    ['Ei(x)', { x: p('5/2') }, '7.07376589457860071192355196245'],
    // SymPy prints ...352280 from a value 1 ulp below the correctly rounded
    // 103-bit value; mpmath at prec 400 rounded to 103 bits prints ...352281
    ['Ei(x)', { x: p('-2') }, '-0.0489005107080611195672398352281'],
    ['LambertW(x)', { x: p('5/2') }, '0.958586356728702912169866781332'],
    ['LambertW(x, -1)', { x: p('-1/5') }, '-2.54264135777352642429380615666'],
    ['LambertW(x, 1)', { x: p('2 + I') }, '-0.820693227646368789310950459066 + 5.0137881918681247226084589256*I'],
    ['besselj(x, y)', { x: p('1/3'), y: p('5/2') }, '0.198320933418608124684856373291'],
    ['bessely(x, y)', { x: p('1/3'), y: p('5/2') }, '0.461459474191290836687695079384'],
    ['bessely(x, y)', { x: p('2'), y: p('5/2') }, '-0.381335849241803248724464397933'],
    ['bessely(x, y)', { x: p('0'), y: p('3/2') }, '0.382448923797758843955068554978'],
    ['besseli(x, y)', { x: p('1/3'), y: p('5/2') }, '3.17432422972419713569931078505'],
    ['besselk(x, y)', { x: p('1/3'), y: p('5/2') }, '0.0635425374547333698177545732713'],
    ['besselk(x, y)', { x: p('1'), y: p('5/2') }, '0.0738908163477470636489935405912'],
    ['besselk(x, y)', { x: p('0'), y: p('1/2') }, '0.924419071227665861781924167530'],
    ['airyai(x)', { x: p('3/2') }, '0.0717494970081054096735554164897'],
    ['airybi(x)', { x: p('-2') }, '-0.412302587956398488083234054611'],
    ['airyaiprime(x)', { x: p('3/2') }, '-0.0973820128423013192184842182024'],
    // likewise SymPy ...414687; the correctly rounded value (mpmath) prints ...414686
    ['airybiprime(x)', { x: p('1/2 + I') }, '0.0487755192101730614199652414686 + 0.250464037279827965000215843873*I'],
    ['li(x)', { x: p('5/2') }, '1.66729466750632395135968597094'],
    ['Li(x)', { x: p('5') }, '2.58942452991515907954775381767'],
    ['Si(x)', { x: p('5/2') }, '1.77852017344382664210031198174'],
    ['Shi(x)', { x: p('5/2') }, '3.54934040622443522370958998736'],
    ['Ci(x)', { x: p('5/2') }, '0.285871196365383495389100647925'],
    ['Chi(x)', { x: p('5/2') }, '3.52442548835416548821396197509'],
    ['lowergamma(x, y)', { x: p('5/2'), y: p('3/2') }, '0.398820945392344629606384253213'],
    ['uppergamma(x, y)', { x: p('5/2'), y: p('3/2') }, '0.930519442786792390867241359293'],
    ['lowergamma(x, y)', { x: p('1/3 + I'), y: p('2') }, '0.139226541580165692890508382648 - 0.550444594765267950051469809262*I'],
    ['zeta(x, y)', { x: p('5/2'), y: p('1/3') }, '16.3330441628988479732000600399'],
    ['besselk(x, y)', { x: p('2'), y: p('5/2') }, '0.121460206278563836948364361949'],
    ['besselk(x, y)', { x: p('3'), y: p('1/2') }, '62.0579095299302563862380916450'],
    ['erf(x*y)', { x: p('I'), y: p('1') }, '1.65042575879754287602533772956*I'],
    ['zeta(x, y)', { x: p('1/2 + 2*I'), y: p('7/3') }, '-0.687038119782425426820553348547 - 0.0761348472380483197667883090042*I'],
    ['harmonic(x, y)', { x: p('5/2'), y: p('2') }, '1.31457631074799157149961411115'],
    ['harmonic(x, y)', { x: p('5/2'), y: p('1') }, '1.68037230554677604783220242375'],
    ['harmonic(x, y)', { x: p('7/2'), y: p('1/2 + I') }, '1.86910484830541106158288187858 - 1.21662676836172609058913065214*I'],
    ['gamma(x)', { x: p('401/2') }, '5.57316894480137913364320296291e+373'],
    ['loggamma(x)', { x: p('401/2 + I') }, '860.579703525407212001409375217 + 5.29832257481952251530557783852*I'],
  ];
  it('match SymPy', () => {
    const got = cases.map(([e, subs]) => {
      try {
        return sstr(evalf(p(e), 30, { subs }));
      } catch (err) {
        return String(err);
      }
    });
    expect(got).toEqual(cases.map(([, , want]) => want));
  });
  it('leaves values outside the implemented domain unevaluated', () => {
    // SymPy raises ValueError (mpmath erfinv domain) for erfinv(2); SymPy
    // evaluates complex erfinv/erfcinv arguments and polygamma of a non-integer
    // order, which symjs leaves unevaluated
    const ev = (e: string, subs: Record<string, Expr>) => sstr(evalf(p(e), 15, { subs }));
    expect(ev('erfinv(x)', { x: p('2') })).toMatch(/^erfinv\(/);
    expect(ev('erfinv(x)', { x: p('I/2') })).toMatch(/^erfinv\(/);
    expect(ev('erfcinv(x)', { x: p('I/2') })).toMatch(/^erfcinv\(/);
    expect(ev('polygamma(x, 2)', { x: p('1/2') })).toMatch(/^polygamma\(/);
  });
});
