// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/functions/special/sphericalharmonics.ts.
//
// Ynm, Ynm_c and Znm: evaluation rules, derivatives, conjugate, expand_func and numerics. Expected values
// are str() results of SymPy 1.14 (mpmath 1.3 spherharm for the numbers).

import { describe, expect, it } from 'vitest';
import * as sj from '../../../src';
import { EvalfValueError, NotImplementedError, Rational, Ynm, YnmC, Znm, add, conjugate, diff, evalf, expandFunc, mul, neg, symbols } from '../../../src';

const S = (e: unknown): string => String(e);
const [n, m, t, p] = symbols('n m theta phi');

describe('Ynm, Ynm_c and Znm', () => {
  it('evaluation rules', () => {
    expect(S(Ynm(n, m, t, p))).toBe('Ynm(n, m, theta, phi)');
    expect(S(Ynm(n, neg(m), t, p))).toBe('(-1)**m*exp(-2*I*m*phi)*Ynm(n, m, theta, phi)');
    expect(S(Ynm(n, m, neg(t), p))).toBe('Ynm(n, m, theta, phi)');
    expect(S(Ynm(n, m, t, neg(p)))).toBe('exp(-2*I*m*phi)*Ynm(n, m, theta, phi)');
    expect(S(YnmC(n, m, t, p))).toBe('(-1)**(2*m)*exp(-2*I*m*phi)*Ynm(n, m, theta, phi)');
    expect(S(YnmC(n, m, neg(t), p))).toBe('(-1)**(2*m)*exp(-2*I*m*phi)*Ynm(n, m, theta, phi)');
    expect(S(conjugate(Ynm(n, m, t, p)))).toBe('(-1)**(2*m)*exp(-2*I*m*phi)*Ynm(n, m, theta, phi)');
  });
  it('Znm', () => {
    expect(S(Znm(n, m, t, p))).toBe('Znm(n, m, theta, phi)');
    expect(S(Znm(n, 0, t, p))).toBe('Ynm(n, 0, theta, phi)');
    expect(S(Znm(n, 1, t, p))).toBe('sqrt(2)*(Ynm(n, 1, theta, phi) + exp(-2*I*phi)*Ynm(n, 1, theta, phi))/2');
    expect(S(Znm(n, -1, t, p))).toBe('-sqrt(2)*I*(exp(-2*I*phi)*exp(2*I*conjugate(phi))*Ynm(n, 1, theta, phi) - exp(-2*I*phi)*Ynm(n, 1, theta, phi))/2');
  });
  it('derivatives', () => {
    expect(S(diff(Ynm(n, m, t, p), t))).toBe('m*cot(theta)*Ynm(n, m, theta, phi) + sqrt((-m + n)*(m + n + 1))*exp(-I*phi)*Ynm(n, m + 1, theta, phi)');
    expect(S(diff(Ynm(n, m, t, p), p))).toBe('I*m*Ynm(n, m, theta, phi)');
    expect(() => diff(Ynm(n, m, t, p), n)).toThrow(NotImplementedError);
  });
  it('expand_func', () => {
    expect(S(expandFunc(Ynm(n, m, t, p)))).toBe('sqrt((2*n + 1)*factorial(-m + n)/factorial(m + n))*exp(I*m*phi)*assoc_legendre(n, m, cos(theta))/(2*sqrt(pi))');
    expect(S(expandFunc(Ynm(1, 1, t, p)))).toBe('-sqrt(6)*exp(I*phi)*sin(theta)/(4*sqrt(pi))');
    expect(S(expandFunc(Ynm(2, 0, t, p)))).toBe('sqrt(5)*(3*cos(theta)**2/2 - 1/2)/(2*sqrt(pi))');
  });
  it('values (mpmath spherharm)', () => {
    expect(S(evalf(Ynm(2, 1, 1, 1), 20))).toBe('-0.18977477584258449931 - 0.29555670184189363134*I');
    expect(S(evalf(Ynm(3, -2, add(Rational.of(1, 2), mul(Rational.of(1, 3), sj.I)), Rational.of(1, 3)), 20))).toBe('0.32366231230197645702 + 0.073513923986409493771*I');
    expect(S(evalf(Ynm(1, 2, 1, 1)))).toBe('0');
    expect(S(evalf(Ynm(-3, 1, 1, 2), 20))).toBe('0.14616663998211433092 - 0.31937993503991477238*I');
    expect(S(evalf(Ynm(1, -1, 0, 0)))).toBe('0');
    expect(S(evalf(Ynm(0, 0, 1, 1), 20))).toBe('0.28209479177387814347');
    expect(S(evalf(Ynm(4, 3, Rational.of(7, 10), Rational.of(-1, 5)), 30))).toBe('-0.211247076650636651316566283779 + 0.144521900791279392894740078918*I');
    // like SymPy, no automatic evaluation with integer degree and order
    expect(S(Ynm(2, 1, sj.float(1), sj.float(1)))).toBe('Ynm(2, 1, 1.0, 1.0)');
    expect(S(evalf(Ynm(Rational.of(1, 2), 0, 1, 1), 20))).toBe('0.32443750997748914425');
    expect(S(evalf(Ynm(1, Rational.of(1, 2), 1, 1), 20))).toBe('0.021541027485023035556 + 0.011767916948861609184*I');
    const v = sj.toComplex(Ynm(2, 1, 1, 1));
    expect(v.re).toBeCloseTo(-0.1897747758425845, 12);
    expect(v.im).toBeCloseTo(-0.29555670184189364, 12);
  });
  it('non-integer degree or order (SymPy Ynm._eval_evalf, mpmath spherharm), at 15 and 50 digits', () => {
    const P = (x: string) => sj.parse(x);
    const cases: [string[], string, string][] = [
      [['1/2', '0', '1', '1'], '0.324437509977489', '0.32443750997748914424618265289226190298079325773713'],
      [['1/2', '1/3', '7/10', '-1/5'], '0.351863977656701 - 0.0234924124009109*I', '0.35186397765670056962337459900208976313996637745949 - 0.023492412400910913143777018291845588452901509100818*I'],
      [['5/2', '-1', '1', '1'], '0.144903355685259 - 0.22567360547264*I', '0.14490335568525937056769335989693060418153192169085 - 0.22567360547263978751172579432877496352831370574404*I'],
      [['2', '1/2', '1', '1'], '-0.243965780877456 - 0.133279113530039*I', '-0.24396578087745605588344936013239174681856864427455 - 0.1332791135300388587805407725076147843504754842185*I'],
      [['-3/2', '3/10', '2', '2/5'], '0.00547843919548927 - 0.0454343117335995*I', '0.0054784391954892652122627465762808384659740615957985 - 0.045434311733599545365765404656292121055927723101415*I'],
      [['1/2', '2', '1', '1'], '0.0492831796041003 + 0.0225548194487112*I', '0.049283179604100271766275095565751650095833617131582 + 0.022554819448711246750994080640779767630912282348178*I'],
      [['1/3', '1/4', '1/2+I/3', '1/3-I/5'], '0.424832215941968 - 0.0518549653666078*I', '0.42483221594196811747331746215164139027880342101254 - 0.051854965366607843956381605254488436467996760761504*I'],
      [['7/4', '-3/4', '3', '1/2'], '-0.32845603781656 + 0.754889718366439*I', '-0.32845603781655965134911367702415372748832787723404 + 0.75488971836643867696652136595694776614102921538681*I'],
      [['-2', '1/2', '1', '1'], '0.021541027485023 + 0.0117679169488616*I', '0.021541027485023035556234974314199676915732927076346 + 0.011767916948861609184338180811497723480871423895438*I'],
      // theta near pi (2F1 by the 1 - z transformation). SymPy's last digit is ...273393: mpmath at 70 digits
      // gives -0.3783897630610111102973515818955694518736115327339249...*I, which rounds to ...273392
      [['1/2', '1/3', '31/10', '1'], '-1.09281121766364 - 0.378389763061011*I', '-1.0928112176636447594254331964559087347824058671785 - 0.37838976306101111029735158189556945187361153273392*I'],
    ];
    for (const [args, d15, d50] of cases) {
      const [l, mm, th, ph] = args.map(P);
      const y = Ynm(l!, mm!, th!, ph!);
      expect(S(evalf(y, 15))).toBe(d15);
      expect(S(evalf(y, 50))).toBe(d50);
    }
    const [l, mm, th, ph] = ['1/2', '1/3', '7/10', '-1/5'].map(P);
    expect(S(evalf(YnmC(l!, mm!, th!, ph!), 30))).toBe('-0.19627701476371971212711065427 + 0.292976937126887352364447156527*I');
    expect(S(evalf(Znm(l!, mm!, th!, ph!), 30))).toBe('0.110016596525846504395534530324 + 0.19055433485857177797113924574*I');
    expect(S(evalf(Znm(l!, neg(mm!), th!, ph!), 30))).toBe('0.0166116441151150486364603848408 + 0.0287722116046318080338732393539*I');
    // integer c - a - b or a - b in the 2F1 (theta near pi, complex theta): the limit of the perturbed parameters
    const degenerate: [string[], string, string][] = [
      [['1/2', '1', '3', '1'], '-1.1441155457177951663 - 1.781854388798653139*I', '-1.1441155457177951662538175594628053011353038306869 - 1.78185438879865313902184837515744401284570198563*I'],
      [['1/2', '0', '3', '1'], '-0.51332532037093538236', '-0.51332532037093538235964816794148534811953906461083'],
      [['1/2', '1/3', '1+3*I', '1'], '0.83477077516321462809 - 0.68240663976306496595*I', '0.83477077516321462809036626605939313132995434612755 - 0.68240663976306496595033760593579975921082851394158*I'],
      [['1/2', '2', '29/10+I/10', '1'], '2.6843689255276640589 + 7.1959392559357623233*I', '2.6843689255276640588814274761791038113697907862944 + 7.1959392559357623233267953126331251839376206149357*I'],
      [['1/3', '0', '3+I', '1'], '0.11972415517459193316 - 0.32475283165404971083*I', '0.1197241551745919331633467566780765172654767137344 - 0.3247528316540497108315879664268923974260277304026*I'],
    ];
    for (const [args, d20, d50] of degenerate) {
      const [l, mm, th, ph] = args.map(P);
      const y = Ynm(l!, mm!, th!, ph!);
      expect(S(evalf(y, 20))).toBe(d20);
      expect(S(evalf(y, 50))).toBe(d50);
    }
    // a pole of Gamma(l - m + 1): like SymPy, the ValueError of mpmath's hypercomb
    expect(() => evalf(Ynm(Rational.of(1, 2), Rational.of(3, 2), 1, 1))).toThrow(EvalfValueError);
    expect(() => evalf(Ynm(Rational.of(1, 2), Rational.of(-3, 2), 1, 1))).toThrow(/^hypercomb\(\) failed to converge to the requested \d+ bits of accuracy/);
    // theta = pi and (m > 0) theta = 0: mpmath's inf and nan, as SymPy prints them (Ynm, Ynm_c, Znm)
    const singular: [string[], string, string, string][] = [
      [['1/2', '0', 'pi', '1'], 'nan', 'nan', 'nan'],
      [['1/2', '3/10', 'pi', '1'], '-oo - oo*I', '-oo', '-oo'],
      [['1/2', '-3/10', 'pi', '1'], '-oo', '-oo', '-oo'],
      [['1/2', '1/3', '0', '1'], 'oo + oo*I', 'oo', 'oo'],
      [['1/2', '-1/3', '0', '1'], 'oo', 'oo', 'oo'],
      [['1/2', '1', '0', '1'], '-oo - oo*I', '-oo', '-oo'],
      [['1/2', '2', '0', '1'], '-oo - oo*I', '-oo', '-oo'],
      [['1/3', '1/2', 'pi', '1/2'], '-oo - oo*I', '-oo', '-oo'],
      [['1/2+I/3', '1/3', 'pi', '1'], 'nan', 'nan', 'nan'],
      [['1/2', '1/3', '0', '0'], 'nan', 'nan', 'nan'],
      [['1/2', '1/3', 'pi', '0'], 'nan', 'nan', 'nan'],
      [['-3/2', '1/3', 'pi', '1'], 'nan', 'nan', 'nan'],
      [['2', '1/2', '0', '1'], 'oo + oo*I', 'oo', 'oo'],
      [['3/2', '3/10', 'pi', '1'], 'oo + oo*I', 'oo', 'oo'],
    ];
    for (const [args, y, yc, zz] of singular) {
      const [a1, a2, a3, a4] = args.map(P);
      expect(S(evalf(Ynm(a1!, a2!, a3!, a4!)))).toBe(y);
      expect(S(evalf(YnmC(a1!, a2!, a3!, a4!), 30))).toBe(yc);
      expect(S(evalf(Znm(a1!, a2!, a3!, a4!)))).toBe(zz);
    }
    // m = 0 at theta = 0 (mpmath power(0, 0) = 1): Ynm(1/2, 0, 0, 1).evalf() = 0.398942280401433
    expect(S(evalf(Ynm(Rational.of(1, 2), 0, 0, 1)))).toBe('0.398942280401433');
    // l = 2, m = 1/2 at theta = pi is 0 (cos(theta/2)**(1/2) = 0); SymPy prints mpmath's rounding noise,
    // 2.36230655933323e-9 + 1.29053395513806e-9*I at 15 digits and 1.0277...e-16 + 5.6145...e-17*I at 30
    expect(S(evalf(Ynm(2, Rational.of(1, 2), sj.pi, 1)))).toBe('0');
    // a positive integer order at theta = pi: SymPy's values change with the precision
    // (Ynm(1/2, 1, pi, 1).evalf() = -1.38477785008482e+16 - 2.1566637206531e+16*I); left unevaluated
    expect(S(evalf(Ynm(Rational.of(1, 2), 1, sj.pi, 1)))).toBe('Ynm(1/2, 1, pi, 1)');
    // an imaginary order with a terminating 2F1 at theta = pi: cos(theta/2)**(I/4) has no limit; SymPy's values
    // change with the precision (Ynm(2, I/4, pi, 1).evalf() = -0.512182383549076 + 0.0677310016585951*I,
    // .evalf(30) = 0.353177175674003812798582977884 + 0.377073156279551585838906281356*I); symjs gives nan
    expect(S(evalf(Ynm(2, mul(Rational.of(1, 4), sj.I), sj.pi, 1)))).toBe('nan');
    // (a complex order: Znm is not evaluated, as in SymPy)
    expect(S(evalf(Znm(Rational.of(1, 2), add(Rational.of(1, 3), mul(Rational.of(1, 4), sj.I)), sj.pi, 1)))).toBe('Znm(1/2, 1/3 + I/4, pi, 1)');
  });
  it('LaTeX', () => {
    expect(sj.latex(sj.pow(Ynm(n, m, t, p), 2))).toBe('\\left(Y_{n}^{m}\\left(\\theta,\\phi\\right)\\right)^{2}');
    expect(sj.latex(Znm(n, m, t, p))).toBe('Z_{n}^{m}\\left(\\theta,\\phi\\right)');
  });
});
