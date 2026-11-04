// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/simplify/hyperexpand.ts.
// hyperexpand of hypergeometric and Meijer G-functions. Expected values are the str() forms of SymPy 1.14's
// hyperexpand; where symjs writes the same function in another form, SymPy's result is quoted and the value
// at z = 3/10, a = 37/100, b = 8/5 is checked against the value of the function (mpmath).

import { describe, expect, it } from 'vitest';
import { I, Rational, Sym, expPolar, hyper, meijerg, mul, parse, pi, sstr, type Expr } from '../../src';
import { HyperRep, hyperexpand, type HyperRepName } from '../../src/simplify/hyperexpand';
import * as sj from '../../src';

const [z, a, b] = [new Sym('z'), new Sym('a'), new Sym('b')];
const half = Rational.of(1n, 2n);
const P = (q: string): Expr => parse(q, { symbols: [z, a, b] });
type Spec = [string, string[][], string];
const build = ([kind, ps, arg]: Spec): Expr => {
  const l = ps.map((xs) => xs.map(P));
  const at = (i: number): Expr[] => l[i] ?? [];
  return kind === 'H' ? hyper(at(0), at(1), P(arg)) : meijerg(at(0), at(1), at(2), at(3), P(arg));
};
const vals: [Expr, Expr][] = [
  [z, Rational.of(3n, 10n)],
  [a, Rational.of(37n, 100n)],
  [b, Rational.of(8n, 5n)],
];

describe('hyperexpand: the results of SymPy', () => {
  const same: [Spec, string][] = [
    [["H", [[], []], "z"], "exp(z)"],
    [["H", [["a"], []], "z"], "(1 - z)**(-a)"],
    [["H", [["1", "1"], ["2"]], "z"], "-log(1 - z)/z"],
    [["H", [["1", "2"], ["3"]], "z"], "-2/z - 2*log(1 - z)/z**2"],
    [["H", [["1", "1"], ["3"]], "z"], "2/z + (2 - 2*z)*log(1 - z)/z**2"],
    [["H", [["1/2", "1"], ["3/2"]], "z"], "atanh(sqrt(z))/sqrt(z)"],
    [["H", [["1/2", "1"], ["3/2"]], "-z"], "atan(sqrt(z))/sqrt(z)"],
    [["H", [["1/2", "1/2"], ["3/2"]], "z"], "asin(sqrt(z))/sqrt(z)"],
    [["H", [["1/2", "1/2"], ["3/2"]], "-z"], "asinh(sqrt(z))/sqrt(z)"],
    [["H", [["a", "a - 1/2"], ["2*a"]], "z"], "2**(2*a - 1)*(sqrt(1 - z) + 1)**(1 - 2*a)"],
    [["H", [["a", "a + 1/2"], ["1/2"]], "z"], "1/(2*(sqrt(z) + 1)**(2*a)) + 1/(2*(1 - sqrt(z))**(2*a))"],
    [["H", [["a", "-a"], ["1/2"]], "z"], "cos(2*a*asin(sqrt(z)))"],
    [["H", [["1", "1"], ["3/2"]], "z"], "asin(sqrt(z))/(sqrt(z)*sqrt(1 - z))"],
    [["H", [["-1/2", "1", "1"], ["1/2", "2"]], "z"], "-2*sqrt(z)*atanh(sqrt(z))/3 + 2/3 - log(1 - z)/(3*z)"],
    [["H", [["-1/2", "1", "1"], ["2", "2"]], "z"], "sqrt(1 - z)*(4*z/9 - 16/9)/z + 4*log(sqrt(1 - z)/2 + 1/2)/(3*z) + 16/(9*z)"],
    [["H", [["1"], ["b"]], "z"], "z**(1 - b)*(b - 1)*exp(z)*lowergamma(b - 1, z)"],
    [["H", [["a"], ["2*a"]], "z"], "2**(2*a - 1)*z**(1/2 - a)*exp(z/2)*besseli(a - 1/2, z/2)*gamma(a + 1/2)"],
    [["H", [["-1/2"], ["1/2"]], "z"], "I*sqrt(pi)*sqrt(z)*erf(I*sqrt(z)) + exp(z)"],
    [["H", [["1", "1"], ["2", "2"]], "z"], "(-log(z) + Ei(z))/z - EulerGamma/z"],
    [["H", [[], ["1/2"]], "z"], "cosh(2*sqrt(z))"],
    [["H", [[], ["b"]], "z"], "z**(1/2 - b/2)*besseli(b - 1, 2*sqrt(z))*gamma(b)"],
    [["H", [["a"], ["2*a", "a - 1/2"]], "z"], "-2**(2*a - 1)*z**(1/2 - a)*besseli(a - 1/2, sqrt(z))**2*gamma(a + 1/2)**2 + 2**(2*a - 1)*z**(1 - a)*besseli(a - 3/2, sqrt(z))*besseli(a - 1/2, sqrt(z))*gamma(a - 1/2)*gamma(a + 1/2)"],
    [["H", [["1/2"], ["b", "2 - b"]], "z"], "pi*(1 - b)*besseli(1 - b, sqrt(z))*besseli(b - 1, sqrt(z))/sin(pi*b)"],
    [["H", [["1/2"], ["3/2", "3/2"]], "z"], "Shi(2*sqrt(z))/(2*sqrt(z))"],
    [["H", [["1", "1"], ["3/2", "2", "2"]], "z"], "(-log(2*sqrt(z)) + Chi(2*sqrt(z)))/z - EulerGamma/z"],
    [["H", [["-2"], ["1/2"]], "z"], "4*z**2/3 - 4*z + 1"],
    [["H", [["-1", "a"], ["-3"]], "z"], "a*z/3 + 1"],
    [["H", [["3"], ["1"]], "z"], "(z**2/2 + 2*z + 1)*exp(z)"],
    [["H", [["a", "b"], ["5"]], "1"], "24*gamma(-a - b + 5)/(gamma(5 - a)*gamma(5 - b))"],
    [["H", [["a", "b"], ["a - b + 1"]], "-1"], "gamma(a/2 + 1)*gamma(a - b + 1)/(gamma(a + 1)*gamma(a/2 - b + 1))"],
    [["H", [["-3", "b"], ["-b - 2"]], "-1"], "0"],
    [["H", [["1"], ["1/2", "3/2"]], "z"], "hyper((1,), (1/2, 3/2), z)"],
    [["H", [["1", "2", "3"], ["4", "5", "6"]], "z"], "hyper((1, 2, 3), (4, 5, 6), z)"],
    [["H", [["1/3"], ["2/3"]], "z"], "2**(2/3)*z**(1/6)*exp(z/2)*besseli(-1/6, z/2)*gamma(5/6)/2"],
    [["H", [["0"], ["1"]], "z"], "1"],
    [["H", [["a"], ["b"]], "0"], "1"],
    [["G", [["1/2"], ["1/2"], ["0", "1/2"], []], "1"], "sqrt(2)*sqrt(pi)/2"],
    [["G", [["1/2"], ["0"], ["0"], []], "4"], "exp(-1/4)/2"],
    [["G", [["1/2", "1"], [], ["1/2"], ["0"]], "z"], "2*atan(sqrt(z))"],
    [["G", [["1/2"], [], ["1/2"], ["0"]], "z"], "-I*exp(-z)*erf(I*sqrt(z))"],
    [["G", [["-1", "1/2"], ["0"], ["0"], []], "z"], "sqrt(pi)*(-z**(3/2)*sinh(2/sqrt(z))/2 + z*cosh(2/sqrt(z)))/z**2 + sqrt(pi)*(cosh(2/sqrt(z))/2 - sinh(2/sqrt(z))/sqrt(z))/sqrt(z)"],
    [["G", [["-1/2"], ["1/2"], ["0"], []], "z"], "sqrt(pi)*(2*z*(1 - 1/(4*z))*exp(-1/(2*z))*besseli(1, 1/(2*z)) + exp(-1/(2*z))*besseli(2, 1/(2*z))/2)/z**(3/2)"],
    [["G", [["0"], [], ["0", "1/2"], ["-1/2"]], "z"], "-pi*besseli(1, 2*sqrt(z)) + 2*hyper((1,), (1/2, 3/2), z)"],
    [["G", [["1/2"], [], ["0", "1/2"], []], "z"], "pi*exp(z)*erfc(sqrt(z))"],
    [["G", [["0"], [], ["0", "0"], ["0"]], "z"], "meijerg(((0,), ()), ((0, 0), (0,)), z)"],
    [["G", [["a"], [], ["a", "a - 1/2"], []], "z"], "pi*z**(a - 1/2)*exp(z)*erfc(sqrt(z))"],
    [["G", [[], [], ["0", "0"], []], "z"], "meijerg(((), ()), ((0, 0), ()), z)"],
    [["G", [[], [], ["0", "0", "0"], []], "z"], "meijerg(((), ()), ((0, 0, 0), ()), z)"],
    [["G", [["1", "1"], [], ["1"], ["0"]], "z"], "log(z + 1)"],
    [["G", [[], [], ["0"], []], "z"], "exp(-z)"],
    [["G", [["1"], [], [], ["0"]], "z"], "Piecewise((0, Abs(z) < 1), (1, 1/Abs(z) < 1), (meijerg(((1,), ()), ((), (0,)), z), True))"],
    [["G", [[], ["1"], ["0"], []], "z"], "Piecewise((1, Abs(z) < 1), (0, 1/Abs(z) < 1), (meijerg(((), (1,)), ((0,), ()), z), True))"],
    [["G", [["1", "1"], [], [], ["0", "0"]], "z"], "Piecewise((0, Abs(z) < 1), (-log(1/z), 1/Abs(z) < 1), (meijerg(((1, 1), ()), ((), (0, 0)), z), True))"],
    [["G", [[], ["1", "1"], ["0", "0"], []], "z"], "Piecewise((-log(z), Abs(z) < 1), (0, 1/Abs(z) < 1), (meijerg(((), (1, 1)), ((0, 0), ()), z), True))"],
    [["G", [["1"], [], ["1/2"], ["0"]], "z"], "sqrt(pi)*erf(sqrt(z))"],
    [["G", [[], ["1"], ["0", "1/2"], []], "z"], "-sqrt(pi)*erf(sqrt(z)) + sqrt(pi)"],
    [["G", [["a"], [], ["b"], []], "z"], "z**b*(z + 1)**(a - b - 1)*gamma(-a + b + 1)"],
    [["G", [["0"], [], ["0", "1"], []], "z"], "exp(z)*expint(2, z)"],
    [["H", [["-1/2", "1"], ["3/2"]], "z"], "1/2 + (1/2 - z/2)*atanh(sqrt(z))/sqrt(z)"],
    [["H", [["5/2"], ["3/2"]], "z"], "(2*z/3 + 1)*exp(z)"],
    [["H", [["2"], ["1/2"]], "z"], "sqrt(z)*(-z/2 - 3/4)*(-2*sqrt(pi)*erf(sqrt(z)) - 2*exp(-z)/sqrt(z))*exp(z) - 1/2"],
    [["H", [["1", "1"], ["4"]], "z"], "(9*z/2 - 3)/z**2 + (-3*z**2 + 6*z - 3)*log(1 - z)/z**3"],
    [["H", [["-1"], ["-2"]], "z"], "z/2 + 1"],
    [["H", [["-2"], ["-1"]], "z"], "oo"],
    [["H", [["1"], ["-1"]], "z"], "oo"],
    [["H", [["a", "b"], ["a - b + 1"]], "-1"], "gamma(a/2 + 1)*gamma(a - b + 1)/(gamma(a + 1)*gamma(a/2 - b + 1))"],
    [["H", [["-3", "b"], ["-b - 2"]], "-1"], "0"],
    [["H", [["1", "1"], ["2"]], "1"], "zoo"],
    [["H", [["1", "1"], ["3/2"]], "-1"], "sqrt(2)*log(1 + sqrt(2))/2"],
    [["H", [["1/3", "1/2"], ["4/3"]], "z"], "hyper((1/3, 1/2), (4/3,), z)"],
    [["H", [["a + 1"], ["a"]], "z"], "(a + z)*exp(z)/a"],
    [["H", [["1", "2"], ["1/2"]], "-1"], "-3*sqrt(2)*log(1 + sqrt(2))/16 + 1/8"],
    [["G", [["0"], [], ["0", "2"], []], "z"], "2*exp(z)*expint(3, z)"],
    [["G", [["a"], [], ["a", "a - 1/2", "a + 1"], []], "z"], "sqrt(pi)*z**a*(-2*(Si(2*sqrt(z)) - pi/2)*sin(2*sqrt(z)) - 2*cos(2*sqrt(z))*Ci(2*sqrt(z))) + sqrt(pi)*z**(a - 1/2)*(-(Si(2*sqrt(z)) - pi/2)*cos(2*sqrt(z)) + sin(2*sqrt(z))*Ci(2*sqrt(z)))"],
    [["G", [["a"], [], ["a", "a - 1/2", "a + 1"], []], "z"], "sqrt(pi)*z**a*(-2*(Si(2*sqrt(z)) - pi/2)*sin(2*sqrt(z)) - 2*cos(2*sqrt(z))*Ci(2*sqrt(z))) + sqrt(pi)*z**(a - 1/2)*(-(Si(2*sqrt(z)) - pi/2)*cos(2*sqrt(z)) + sin(2*sqrt(z))*Ci(2*sqrt(z)))"],
    [["G", [["a"], [], ["a", "a - 1/2", "a + 1"], []], "z"], "sqrt(pi)*z**a*(-2*(Si(2*sqrt(z)) - pi/2)*sin(2*sqrt(z)) - 2*cos(2*sqrt(z))*Ci(2*sqrt(z))) + sqrt(pi)*z**(a - 1/2)*(-(Si(2*sqrt(z)) - pi/2)*cos(2*sqrt(z)) + sin(2*sqrt(z))*Ci(2*sqrt(z)))"],
    [["G", [["0"], [], ["0", "0", "0"], []], "z"], "meijerg(((0,), ()), ((0, 0, 0), ()), z)"],
    [["G", [["1", "1"], [], ["1"], ["0"]], "1/z"], "log(1 + 1/z)"],
    [["G", [[], [], ["0", "1/2"], []], "z"], "-sqrt(pi)*sinh(2*sqrt(z)) + sqrt(pi)*cosh(2*sqrt(z))"],
    [["G", [["1/2"], [], ["0"], []], "z"], "sqrt(pi)/sqrt(z + 1)"],
    [["G", [[], ["1/2"], ["0"], []], "z"], "Piecewise((1/(sqrt(pi)*sqrt(1 - z)), Abs(z) < 1), (0, 1/Abs(z) < 1), (meijerg(((), (1/2,)), ((0,), ()), z), True))"],
    [["G", [[], [], ["0", "0"], ["1/2"]], "z"], "meijerg(((), ()), ((0, 0), (1/2,)), z)"],
    [["G", [["0", "0"], [], ["0"], []], "z"], "meijerg(((0, 0), ()), ((0,), ()), z)"],
    [["G", [[], [], ["1", "1"], []], "z"], "meijerg(((), ()), ((1, 1), ()), z)"],
    [["G", [["1", "1"], [], ["1/2"], []], "z"], "meijerg(((1, 1), ()), ((1/2,), ()), z)"],
    [["G", [["0"], [], ["-3/2", "0", "0"], []], "z"], "sqrt(pi)*(2*(Si(2*sqrt(z)) - pi/2)*sin(2*sqrt(z)) + 2*cos(2*sqrt(z))*Ci(2*sqrt(z)))/z - 2*sqrt(pi)/z + sqrt(pi)*((Si(2*sqrt(z)) - pi/2)*cos(2*sqrt(z)) - sin(2*sqrt(z))*Ci(2*sqrt(z)))/z**(3/2)"],
    [["G", [["a"], [], ["a", "a", "a - 3/2"], []], "z"], "sqrt(pi)*z**(a - 3/2)*((Si(2*sqrt(z)) - pi/2)*cos(2*sqrt(z)) - sin(2*sqrt(z))*Ci(2*sqrt(z))) + sqrt(pi)*z**(a - 1)*(2*(Si(2*sqrt(z)) - pi/2)*sin(2*sqrt(z)) + 2*cos(2*sqrt(z))*Ci(2*sqrt(z))) - 2*sqrt(pi)*z**(a - 1)"],
    [["G", [["0"], [], ["0", "0", "1/3"], []], "z"], "meijerg(((0,), ()), ((0, 0, 1/3), ()), z)"],
    [["G", [[], [], ["1"], ["0"]], "z"], "sqrt(z)*besselj(1, 2*sqrt(z))"],
    [["G", [["1"], ["0"], [], []], "z"], "meijerg(((1,), (0,)), ((), ()), z)"],
    [["G", [[], ["1"], ["0"], ["1"]], "z"], "0"],
    [["G", [["0"], [], ["1"], []], "z"], "z/(z + 1)**2"],
    [["G", [["1", "1"], [], ["1"], ["1"]], "z"], "z/(z + 1)"],
    [["H", [["a"], ["a + 1"]], "z"], "a*exp(-I*pi*a)*lowergamma(a, z*exp_polar(I*pi))/z**a"],
    [["H", [["1"], ["3/4", "5/4"]], "z"], "sqrt(pi)*(I*sinh(2*sqrt(z))*fresnels(2*z**(1/4)*exp(I*pi/4)/sqrt(pi)) + cosh(2*sqrt(z))*fresnelc(2*z**(1/4)*exp(I*pi/4)/sqrt(pi)))*exp(-I*pi/4)/(2*z**(1/4))"],
    [["H", [["1/2", "a"], ["3/2", "a + 1"]], "z"], "-a*exp(-I*pi*a)*lowergamma(a, z*exp_polar(I*pi))/(z**a*(2*a - 1)) - I*sqrt(pi)*a*erf(I*sqrt(z))/(sqrt(z)*(2*a - 1))"],
    [["H", [[], ["a", "2*a", "a + 1/2"]], "z"], "2**(1 - 2*a)*z**(1/2 - a)*exp(I*pi*(1 - 2*a)/2)*besseli(2*a - 1, 2*sqrt(2)*z**(1/4)*exp_polar(I*pi/4))*besselj(2*a - 1, 2*sqrt(2)*z**(1/4)*exp_polar(I*pi/4))*gamma(2*a)**2"],
    [["H", [["3/4"], ["3/2", "7/4"]], "z"], "3*sqrt(pi)*exp(-3*I*pi/4)*fresnels(2*z**(1/4)*exp(I*pi/4)/sqrt(pi))/(4*z**(3/4))"],
    [["H", [["1/4"], ["1/2", "5/4"]], "z"], "sqrt(pi)*exp(-I*pi/4)*fresnelc(2*z**(1/4)*exp(I*pi/4)/sqrt(pi))/(2*z**(1/4))"],
    [["H", [["1", "1", "a"], ["2", "2", "a + 1"]], "z"], "a*(1 - a)*(log(z*exp_polar(I*pi)) + expint(1, z*exp_polar(I*pi)) + EulerGamma)/(z*(a**2 - 2*a + 1)) - a*exp(z)/(z*(a**2 - 2*a + 1)) + a/(z*(a**2 - 2*a + 1)) + a*(gamma(a) - uppergamma(a, z*exp_polar(I*pi)))/((-1)**a*z**a*(a - 1)**2)"],
    [["G", [[], [], ["a"], ["b"]], "z"], "z**(a/2 + b/2)*exp(I*pi*(-a/2 + b/2))*besseli(a - b, 2*sqrt(z)*exp_polar(I*pi/2))"],
    [["H", [["1/3", "1"], ["4/3", "3"]], "z"], "(z + 2/5)/z**2 + 2*exp(-I*pi/3)*lowergamma(5*exp_polar(I*pi)/3, z*exp_polar(I*pi))/(3*z**(1/3))"],
    [["H", [["1/3", "2"], ["4/3", "4"]], "z"], "(-6*z/5 - 3/2)/z**3 + 2*exp(z)/z**3 + 4*exp(2*I*pi/3)*lowergamma(8*exp_polar(I*pi)/3, z*exp_polar(I*pi))/(3*z**(1/3))"],
  ];
  it.each(same)('%j', (spec, want) => expect(sstr(hyperexpand(build(spec)))).toBe(want));
});

describe('hyperexpand: the same functions in other forms than SymPy', () => {
  const other: [Spec, string, [number, number]][] = [
    // SymPy: z**(1/4 - a/2)*(besseli(2*a - 1, 4*z**(1/4)) + besselj(2*a - 1, 4*z**(1/4)))*gamma(2*a)/2**(2*a)
    [["H", [[], ["1/2", "a", "a + 1/2"]], "z"], "(1/4)**a*z**(1/4 - a/2)*(besseli(2*a - 1, 4*z**(1/4)) + besselj(2*a - 1, 4*z**(1/4)))*gamma(2*a)", [2.937117338405986, 0.0]],
    // SymPy: 2**(2*a - 1)*z**(1/2 - a)*besseli(2*a - b, sqrt(z))*besseli(b - 1, sqrt(z))*gamma(b)*gamma(2*a - b + 1)
    [["H", [["a", "a + 1/2"], ["b", "2*a", "2*a - b + 1"]], "z"], "(1/2)**(1 - 2*a)*z**(1/2 - a)*besseli(2*a - b, sqrt(z))*besseli(b - 1, sqrt(z))*gamma(b)*gamma(2*a - b + 1)", [1.627423567343385, 0.0]],
    // SymPy: (2*z + 1)/(z - 1)**4
    [["H", [["2", "3"], ["1"]], "z"], "(2*z + 1)/(1 - z)**4", [6.663890045814244, 0.0]],
    // SymPy: (3/4 - 3*z/4)/(z*sqrt(1 - z)) + (6*z - 3)*asin(sqrt(z))/(4*z**(3/2))
    [["H", [["1/2", "1/2"], ["5/2"]], "z"], "(3/4 - 3*z/4)/(z*sqrt(1 - z)) + (6*z - 3)*asin(sqrt(z))/(4*z**(3/2))", [1.033377529589727, 0.0]],
    // SymPy: -sqrt(pi)*(2*(Si(2*sqrt(z)) - pi/2)*sin(2*sqrt(z)) + 2*cos(2*sqrt(z))*Ci(2*sqrt(z)))
    [["G", [["0", "1/2"], [], ["0", "0", "1/2"], ["1/2"]], "z"], "-2*sqrt(pi)*((Si(2*sqrt(z)) - pi/2)*sin(2*sqrt(z)) + cos(2*sqrt(z))*Ci(2*sqrt(z)))", [1.0989928362906576, 0.0]],
    // SymPy: -sqrt(pi)*z**(a - 1/2)*(2*(Si(2*sqrt(z)) - pi/2)*cos(2*sqrt(z)) - 2*sin(2*sqrt(z))*Ci(2*sqrt(z)))
    [["G", [["a"], [], ["a", "a", "a - 1/2"], []], "z"], "-2*sqrt(pi)*z**(a - 1/2)*((Si(2*sqrt(z)) - pi/2)*cos(2*sqrt(z)) - sin(2*sqrt(z))*Ci(2*sqrt(z)))", [2.447143820283287, 0.0]],
    // SymPy: -sqrt(pi)*sqrt(z)*(2*(Si(2*sqrt(z)) - pi/2)*cos(2*sqrt(z)) - 2*sin(2*sqrt(z))*Ci(2*sqrt(z)))
    [["G", [["1"], [], ["1/2", "1", "1"], []], "z"], "-2*sqrt(pi)*sqrt(z)*((Si(2*sqrt(z)) - pi/2)*cos(2*sqrt(z)) - sin(2*sqrt(z))*Ci(2*sqrt(z)))", [1.1461616797329164, 0.0]],
    // SymPy: z*((log(z*exp_polar(I*pi)) - Ei(z*exp_polar(I*pi)))/z + EulerGamma/z) - log(z) - EulerGamma
    [["G", [[], ["1"], ["0", "0"], []], "z"], "z*((log(z*exp_polar(I*pi)) - Ei(-z) - I*pi)/z + EulerGamma/z) - log(z) - EulerGamma", [0.9056766516758468, 0.0]],
    // SymPy: z**2*(-((-2*z - 4)/z**2 + (2*z + 2)/z**2)*exp(-z)/2 - ((-2*z - 2)/z**2 + 2/z**2)*(-log(z*exp_polar(I*pi)) + Ei(z*exp_polar(I*pi)))/2 - EulerGamma*((2*z + 2)/z**2 - 2/z**2)/2 - (-2*z - 2)/(2*z**2) - 2/z**2) + z*log(z) - z + EulerGamma*z + 1
    [["G", [[], ["2"], ["0", "1"], []], "z"], "z**2*(-((-2 - 2/z)/z + 2/z**2)*(-log(z*exp_polar(I*pi)) + Ei(-z) + I*pi)/2 - EulerGamma*((2 + 2/z)/z - 2/z**2)/2 - ((2 + 2/z)/z + (-2*z - 4)/z**2)*exp(-z)/2 - (-2 - 2/z)/(2*z) - 2/z**2) + z*log(z) - z + EulerGamma*z + 1", [0.46911522517896387, 0.0]],
    // SymPy: 3/(2*z) + (3*z - 3)*atanh(sqrt(z))/(2*z**(3/2))
    [["H", [["1/2", "1"], ["5/2"]], "z"], "3/(2*z) + (3*z - 3)*atanh(sqrt(z))/(2*z**(3/2))", [1.0693110283741394, 0.0]],
    // SymPy: (z + 1)/(z - 1)**2
    [["H", [["1", "3/2"], ["1/2"]], "z"], "(z + 1)/(1 - z)**2", [2.6530612244897958, 0.0]],
    // SymPy: (z - 2)/((1 - z)*(2*z - 2))
    [["H", [["1", "3"], ["2"]], "z"], "(z - 2)/((1 - z)*(2*z - 2))", [1.7346938775510203, 0.0]],
    // SymPy: -4/z + 4*polylog(2, z)/z**2
    [["H", [["1", "2", "2"], ["3", "3"]], "z"], "hyper((1, 2, 2), (3, 3), z)", [1.1613115589100476, 0.0]],
    // SymPy: (a*(a + 1) + 2*a*(a + 4) + (a + 3)*(a + 4))/((a + 3)*(a + 4))
    [["H", [["-2", "a"], ["a + 3"]], "-1"], "a*(a + 1)/((a + 3)*(a + 4)) + 2*a/(a + 3) + 1", [1.2540045766590389, 0.0]],
    // SymPy: 2*elliptic_k(z)/pi
    [["H", [["1/2", "1/2"], ["1"]], "z"], "hyper((1/2, 1/2), (1,), z)", [1.0910959103627815, 0.0]],
    // SymPy: -sqrt(pi)*z**(a - 1/2)*(2*(Si(2*sqrt(z)) - pi/2)*cos(2*sqrt(z)) - 2*sin(2*sqrt(z))*Ci(2*sqrt(z)))
    [["G", [["a"], [], ["a", "a", "a - 1/2"], []], "z"], "-2*sqrt(pi)*z**(a - 1/2)*((Si(2*sqrt(z)) - pi/2)*cos(2*sqrt(z)) - sin(2*sqrt(z))*Ci(2*sqrt(z)))", [2.447143820283287, 0.0]],
    // SymPy: -sqrt(pi)*sqrt(z)*(2*(Si(2*sqrt(z)) - pi/2)*cos(2*sqrt(z)) - 2*sin(2*sqrt(z))*Ci(2*sqrt(z)))
    [["G", [["1"], [], ["1/2", "1", "1"], []], "z"], "-2*sqrt(pi)*sqrt(z)*((Si(2*sqrt(z)) - pi/2)*cos(2*sqrt(z)) - sin(2*sqrt(z))*Ci(2*sqrt(z)))", [1.1461616797329164, 0.0]],
    // SymPy: Piecewise((0, (Abs(z) < 1) | (1/Abs(z) < 1)), (meijerg(((), (1,)), ((), (0,)), z), True))
    [["G", [[], ["1"], [], ["0"]], "z"], "Piecewise((0, Abs(z) < 1), (0, 1/Abs(z) < 1), (meijerg(((), (1,)), ((), (0,)), z), True))", [0.0, 0.0]],
    // SymPy: -sqrt(pi)*z**a*(2*(Si(2*sqrt(z)) - pi/2)*sin(2*sqrt(z)) + 2*cos(2*sqrt(z))*Ci(2*sqrt(z)))
    [["G", [["a"], [], ["a", "a", "a + 1/2"], []], "z"], "-2*sqrt(pi)*z**a*((Si(2*sqrt(z)) - pi/2)*sin(2*sqrt(z)) + cos(2*sqrt(z))*Ci(2*sqrt(z)))", [0.7039304075732961, 0.0]],
    // SymPy: 2/(5*z) + 2*log(1 - z)/(5*z**2) - 2*log(1 - z**(1/3))/(5*z**(1/3)) - 2*exp(-2*I*pi/3)*log(-z**(1/3)*exp_polar(2*I*pi/3) + 1)/(5*z**(1/3)) - 2*exp(2*I*pi/3)*log(-z**(1/3)*exp_polar(4*I*pi/3) + 1)/(5*z**(1/3))
    [["H", [["1/3", "1", "2"], ["4/3", "3"]], "z"], "hyper((1/3, 1, 2), (4/3, 3), z)", [1.0577721530161595, 0.0]],
    // SymPy: Piecewise((0, (Abs(z) < 1) | (1/Abs(z) < 1)), (meijerg(((), (0,)), ((1,), ()), z), True))
    [["G", [[], ["0"], ["1"], []], "z"], "Piecewise((0, Abs(z) < 1), (0, 1/Abs(z) < 1), (meijerg(((), (0,)), ((1,), ()), z), True))", [0.0, 0.0]],
    // SymPy: Piecewise((0, (Abs(z) < 1) | (1/Abs(z) < 1)), (meijerg(((0,), (1,)), ((0,), (1,)), z), True))
    [["G", [["0"], ["1"], ["0"], ["1"]], "z"], "Piecewise((0, Abs(z) < 1), (0, 1/Abs(z) < 1), (meijerg(((0,), (1,)), ((0,), (1,)), z), True))", [0.0, 0.0]],
  ];
  it.each(other)('%j', (spec, want, [re, im]) => {
    const r = hyperexpand(build(spec));
    expect(sstr(r)).toBe(want);
    const v = r.subs(vals).evalf(20).toComplex();
    expect(Math.hypot(v.re - re, v.im - im)).toBeLessThan(1e-10);
  });
});

describe('hyperexpand options', () => {
  const G1 = meijerg([1, 1], [], [1], [0], z);
  const G2 = meijerg([], [half], [0], [], z);
  it('place: the expansion at zero or at infinity (SymPy place=0 and place=zoo)', () => {
    expect(sstr(hyperexpand(G1, { place: 'zero' }))).toBe('log(z + 1)');
    expect(sstr(hyperexpand(G1, { place: 'infinity' }))).toBe('-log(1/z) + log(1 + 1/z)');
    expect(sstr(hyperexpand(G2, { place: 'zero' }))).toBe('Piecewise((1/(sqrt(pi)*sqrt(1 - z)), Abs(z) < 1), (meijerg(((), (1/2,)), ((0,), ()), z), True))');
    expect(sstr(hyperexpand(G2, { place: 'infinity' }))).toBe('Piecewise((0, 1/Abs(z) < 1), (meijerg(((), (1/2,)), ((0,), ()), z), True))');
  });
  it('allowHyper: G-functions without expansion stay', () => {
    expect(sstr(hyperexpand(meijerg([], [], [0, 0], [half], z), { allowHyper: true }))).toBe('meijerg(((), ()), ((0, 0), (1/2,)), z)');
    expect(sstr(hyperexpand(meijerg([0, 0], [], [0], [], z), { allowHyper: true }))).toBe('meijerg(((0, 0), ()), ((0,), ()), z)');
  });
});

describe('the HyperRep closed forms on the sheets of the logarithm (SymPy rewrite nonrep and nonrepsmall)', () => {
  const [x, a] = [new Sym('x'), new Sym('a')];
  const withA = new Set(['power1', 'power2', 'sqrts1', 'sqrts2', 'cosasin', 'sinasin']);
  // [function, m, target, closed form of HyperRep_function(..., x*exp_polar(m*I*pi))]
  const cases: [HyperRepName, number, 'nonrep' | 'nonrepsmall', string][] = [
    ["power1", 0, "nonrep", "Piecewise(((x - 1)**a*exp(-I*pi*a), Abs(x) > 1), ((1 - x)**a, True))"],
    ["power1", 0, "nonrepsmall", "(1 - x)**a"],
    ["power1", 1, "nonrep", "(x + 1)**a"],
    ["power1", 1, "nonrepsmall", "(x + 1)**a"],
    ["power1", 2, "nonrep", "Piecewise(((x - 1)**a*exp(I*pi*a), Abs(x) > 1), ((1 - x)**a, True))"],
    ["power1", 2, "nonrepsmall", "(1 - x)**a"],
    ["power1", 3, "nonrep", "Piecewise(((x + 1)**a*exp(2*I*pi*a), Abs(x) > 1), ((x + 1)**a, True))"],
    ["power1", 3, "nonrepsmall", "(x + 1)**a"],
    ["power1", 4, "nonrep", "Piecewise(((x - 1)**a*exp(3*I*pi*a), Abs(x) > 1), ((1 - x)**a, True))"],
    ["power1", 4, "nonrepsmall", "(1 - x)**a"],
    ["power2", 0, "nonrep", "Piecewise((2**(2*a - 1)*(-I*sqrt(x - 1) + 1)**(1 - 2*a), Abs(x) > 1), (2**(2*a - 1)*(sqrt(1 - x) + 1)**(1 - 2*a), True))"],
    ["power2", 0, "nonrepsmall", "2**(2*a - 1)*(sqrt(1 - x) + 1)**(1 - 2*a)"],
    ["power2", 1, "nonrep", "2**(2*a - 1)*(sqrt(x + 1) + 1)**(1 - 2*a)"],
    ["power2", 1, "nonrepsmall", "2**(2*a - 1)*(sqrt(x + 1) + 1)**(1 - 2*a)"],
    ["power2", 2, "nonrep", "Piecewise((2**(2*a - 1)*(I*sqrt(x - 1) + 1)**(1 - 2*a), Abs(x) > 1), (2**(2*a - 1)*(sqrt(1 - x) + 1)**(1 - 2*a), True))"],
    ["power2", 2, "nonrepsmall", "2**(2*a - 1)*(sqrt(1 - x) + 1)**(1 - 2*a)"],
    ["power2", 3, "nonrep", "Piecewise((-2**(2*a - 1)*(sqrt(x + 1) - 1)**(1 - 2*a)*exp(-2*I*pi*a), Abs(x) > 1), (2**(2*a - 1)*(sqrt(x + 1) + 1)**(1 - 2*a), True))"],
    ["power2", 3, "nonrepsmall", "2**(2*a - 1)*(sqrt(x + 1) + 1)**(1 - 2*a)"],
    ["power2", 4, "nonrep", "Piecewise((2**(2*a - 1)*(-I*sqrt(x - 1) + 1)**(1 - 2*a)*exp(-4*I*pi*a), Abs(x) > 1), (2**(2*a - 1)*(sqrt(1 - x) + 1)**(1 - 2*a), True))"],
    ["power2", 4, "nonrepsmall", "2**(2*a - 1)*(sqrt(1 - x) + 1)**(1 - 2*a)"],
    ["log1", 0, "nonrep", "Piecewise((log(x - 1) - I*pi, Abs(x) > 1), (log(1 - x), True))"],
    ["log1", 0, "nonrepsmall", "log(1 - x)"],
    ["log1", 1, "nonrep", "log(x + 1)"],
    ["log1", 1, "nonrepsmall", "log(x + 1)"],
    ["log1", 2, "nonrep", "Piecewise((log(x - 1) + I*pi, Abs(x) > 1), (log(1 - x), True))"],
    ["log1", 2, "nonrepsmall", "log(1 - x)"],
    ["log1", 3, "nonrep", "Piecewise((log(x + 1) + 2*I*pi, Abs(x) > 1), (log(x + 1), True))"],
    ["log1", 3, "nonrepsmall", "log(x + 1)"],
    ["log1", 4, "nonrep", "Piecewise((log(x - 1) + 3*I*pi, Abs(x) > 1), (log(1 - x), True))"],
    ["log1", 4, "nonrepsmall", "log(1 - x)"],
    ["atanh", 0, "nonrep", "Piecewise(((acoth(sqrt(x)) + I*pi/2)/sqrt(x), Abs(x) > 1), (atanh(sqrt(x))/sqrt(x), True))"],
    ["atanh", 0, "nonrepsmall", "atanh(sqrt(x))/sqrt(x)"],
    ["atanh", 1, "nonrep", "atan(sqrt(x))/sqrt(x)"],
    ["atanh", 1, "nonrepsmall", "atan(sqrt(x))/sqrt(x)"],
    ["atanh", 2, "nonrep", "Piecewise(((acoth(sqrt(x)) - I*pi/2)/sqrt(x), Abs(x) > 1), (atanh(sqrt(x))/sqrt(x), True))"],
    ["atanh", 2, "nonrepsmall", "atanh(sqrt(x))/sqrt(x)"],
    ["atanh", 3, "nonrep", "Piecewise(((atan(sqrt(x)) - pi)/sqrt(x), Abs(x) > 1), (atan(sqrt(x))/sqrt(x), True))"],
    ["atanh", 3, "nonrepsmall", "atan(sqrt(x))/sqrt(x)"],
    ["atanh", 4, "nonrep", "Piecewise(((acoth(sqrt(x)) + I*pi/2)/sqrt(x), Abs(x) > 1), (atanh(sqrt(x))/sqrt(x), True))"],
    ["atanh", 4, "nonrepsmall", "atanh(sqrt(x))/sqrt(x)"],
    ["asin1", 0, "nonrep", "Piecewise((I*acosh(sqrt(x))/sqrt(x) + pi/(2*sqrt(x)), Abs(x) > 1), (asin(sqrt(x))/sqrt(x), True))"],
    ["asin1", 0, "nonrepsmall", "asin(sqrt(x))/sqrt(x)"],
    ["asin1", 1, "nonrep", "asinh(sqrt(x))/sqrt(x)"],
    ["asin1", 1, "nonrepsmall", "asinh(sqrt(x))/sqrt(x)"],
    ["asin1", 2, "nonrep", "Piecewise((-I*acosh(sqrt(x))/sqrt(x) + pi/(2*sqrt(x)), Abs(x) > 1), (asin(sqrt(x))/sqrt(x), True))"],
    ["asin1", 2, "nonrepsmall", "asin(sqrt(x))/sqrt(x)"],
    ["asin1", 3, "nonrep", "Piecewise((-asinh(sqrt(x))/sqrt(x) - I*pi/sqrt(x), Abs(x) > 1), (asinh(sqrt(x))/sqrt(x), True))"],
    ["asin1", 3, "nonrepsmall", "asinh(sqrt(x))/sqrt(x)"],
    ["asin1", 4, "nonrep", "Piecewise((I*acosh(sqrt(x))/sqrt(x) - 3*pi/(2*sqrt(x)), Abs(x) > 1), (asin(sqrt(x))/sqrt(x), True))"],
    ["asin1", 4, "nonrepsmall", "asin(sqrt(x))/sqrt(x)"],
    ["asin2", 0, "nonrep", "Piecewise((I*(I*acosh(sqrt(x))/sqrt(x) + pi/(2*sqrt(x)))/sqrt(x - 1), Abs(x) > 1), (asin(sqrt(x))/(sqrt(x)*sqrt(1 - x)), True))"],
    ["asin2", 0, "nonrepsmall", "asin(sqrt(x))/(sqrt(x)*sqrt(1 - x))"],
    ["asin2", 1, "nonrep", "asinh(sqrt(x))/(sqrt(x)*sqrt(x + 1))"],
    ["asin2", 1, "nonrepsmall", "asinh(sqrt(x))/(sqrt(x)*sqrt(x + 1))"],
    ["asin2", 2, "nonrep", "Piecewise((-I*(-I*acosh(sqrt(x))/sqrt(x) + pi/(2*sqrt(x)))/sqrt(x - 1), Abs(x) > 1), (asin(sqrt(x))/(sqrt(x)*sqrt(1 - x)), True))"],
    ["asin2", 2, "nonrepsmall", "asin(sqrt(x))/(sqrt(x)*sqrt(1 - x))"],
    ["asin2", 3, "nonrep", "Piecewise((-(-asinh(sqrt(x))/sqrt(x) - I*pi/sqrt(x))/sqrt(x + 1), Abs(x) > 1), (asinh(sqrt(x))/(sqrt(x)*sqrt(x + 1)), True))"],
    ["asin2", 3, "nonrepsmall", "asinh(sqrt(x))/(sqrt(x)*sqrt(x + 1))"],
    ["asin2", 4, "nonrep", "Piecewise((I*(I*acosh(sqrt(x))/sqrt(x) - 3*pi/(2*sqrt(x)))/sqrt(x - 1), Abs(x) > 1), (asin(sqrt(x))/(sqrt(x)*sqrt(1 - x)), True))"],
    ["asin2", 4, "nonrepsmall", "asin(sqrt(x))/(sqrt(x)*sqrt(1 - x))"],
    ["sqrts1", 0, "nonrep", "Piecewise(((sqrt(x) - 1)**(2*a)*exp(-2*I*pi*a)/2 + (sqrt(x) + 1)**(2*a)/2, Abs(x) > 1), ((1 - sqrt(x))**(2*a)/2 + (sqrt(x) + 1)**(2*a)/2, True))"],
    ["sqrts1", 0, "nonrepsmall", "(1 - sqrt(x))**(2*a)/2 + (sqrt(x) + 1)**(2*a)/2"],
    ["sqrts1", 1, "nonrep", "(x + 1)**a*cos(2*a*atan(sqrt(x)))"],
    ["sqrts1", 1, "nonrepsmall", "(x + 1)**a*cos(2*a*atan(sqrt(x)))"],
    ["sqrts1", 2, "nonrep", "Piecewise(((sqrt(x) - 1)**(2*a)*exp(2*I*pi*a)/2 + (sqrt(x) + 1)**(2*a)/2, Abs(x) > 1), ((1 - sqrt(x))**(2*a)/2 + (sqrt(x) + 1)**(2*a)/2, True))"],
    ["sqrts1", 2, "nonrepsmall", "(1 - sqrt(x))**(2*a)/2 + (sqrt(x) + 1)**(2*a)/2"],
    ["sqrts1", 3, "nonrep", "Piecewise(((x + 1)**a*exp(2*I*pi*a)*cos(2*a*atan(sqrt(x)) - 2*pi*a), Abs(x) > 1), ((x + 1)**a*cos(2*a*atan(sqrt(x))), True))"],
    ["sqrts1", 3, "nonrepsmall", "(x + 1)**a*cos(2*a*atan(sqrt(x)))"],
    ["sqrts1", 4, "nonrep", "Piecewise(((sqrt(x) - 1)**(2*a)*exp(2*I*pi*a)/2 + (sqrt(x) + 1)**(2*a)*exp(4*I*pi*a)/2, Abs(x) > 1), ((1 - sqrt(x))**(2*a)/2 + (sqrt(x) + 1)**(2*a)/2, True))"],
    ["sqrts1", 4, "nonrepsmall", "(1 - sqrt(x))**(2*a)/2 + (sqrt(x) + 1)**(2*a)/2"],
    // SymPy: Piecewise((sqrt(x)*((sqrt(x) - 1)**(2*a)*exp(-2*I*pi*a) - (sqrt(x) + 1)**(2*a))/2, Abs(x) > 1), (sqrt(x)*((1 - sqrt(x))**(2*a) - (sqrt(x) + 1)**(2*a))/2, True)) (the same function at x = 3/10 and x = 3)
    ["sqrts2", 0, "nonrep", "Piecewise((sqrt(x)*((sqrt(x) - 1)**(2*a)*exp(-2*I*pi*a) - (sqrt(x) + 1)**(2*a))/2, Abs(x) > 1), (sqrt(x)*((1 - sqrt(x))**(2*a)/2 - (sqrt(x) + 1)**(2*a)/2), True))"],
    // SymPy: sqrt(x)*((1 - sqrt(x))**(2*a) - (sqrt(x) + 1)**(2*a))/2 (the same function at x = 3/10 and x = 3)
    ["sqrts2", 0, "nonrepsmall", "sqrt(x)*((1 - sqrt(x))**(2*a)/2 - (sqrt(x) + 1)**(2*a)/2)"],
    ["sqrts2", 1, "nonrep", "sqrt(x)*(x + 1)**a*sin(2*a*atan(sqrt(x)))"],
    ["sqrts2", 1, "nonrepsmall", "sqrt(x)*(x + 1)**a*sin(2*a*atan(sqrt(x)))"],
    // SymPy: Piecewise((sqrt(x)*((sqrt(x) - 1)**(2*a)*exp(2*I*pi*a) - (sqrt(x) + 1)**(2*a))/2, Abs(x) > 1), (sqrt(x)*((1 - sqrt(x))**(2*a) - (sqrt(x) + 1)**(2*a))/2, True)) (the same function at x = 3/10 and x = 3)
    ["sqrts2", 2, "nonrep", "Piecewise((sqrt(x)*((sqrt(x) - 1)**(2*a)*exp(2*I*pi*a) - (sqrt(x) + 1)**(2*a))/2, Abs(x) > 1), (sqrt(x)*((1 - sqrt(x))**(2*a)/2 - (sqrt(x) + 1)**(2*a)/2), True))"],
    // SymPy: sqrt(x)*((1 - sqrt(x))**(2*a) - (sqrt(x) + 1)**(2*a))/2 (the same function at x = 3/10 and x = 3)
    ["sqrts2", 2, "nonrepsmall", "sqrt(x)*((1 - sqrt(x))**(2*a)/2 - (sqrt(x) + 1)**(2*a)/2)"],
    ["sqrts2", 3, "nonrep", "Piecewise((sqrt(x)*(x + 1)**a*exp(2*I*pi*a)*sin(2*a*atan(sqrt(x)) - 2*pi*a), Abs(x) > 1), (sqrt(x)*(x + 1)**a*sin(2*a*atan(sqrt(x))), True))"],
    ["sqrts2", 3, "nonrepsmall", "sqrt(x)*(x + 1)**a*sin(2*a*atan(sqrt(x)))"],
    // SymPy: Piecewise((sqrt(x)*((sqrt(x) - 1)**(2*a)*exp(2*I*pi*a) - (sqrt(x) + 1)**(2*a)*exp(4*I*pi*a))/2, Abs(x) > 1), (sqrt(x)*((1 - sqrt(x))**(2*a) - (sqrt(x) + 1)**(2*a))/2, True)) (the same function at x = 3/10 and x = 3)
    ["sqrts2", 4, "nonrep", "Piecewise((sqrt(x)*((sqrt(x) - 1)**(2*a)*exp(2*I*pi*a) - (sqrt(x) + 1)**(2*a)*exp(4*I*pi*a))/2, Abs(x) > 1), (sqrt(x)*((1 - sqrt(x))**(2*a)/2 - (sqrt(x) + 1)**(2*a)/2), True))"],
    // SymPy: sqrt(x)*((1 - sqrt(x))**(2*a) - (sqrt(x) + 1)**(2*a))/2 (the same function at x = 3/10 and x = 3)
    ["sqrts2", 4, "nonrepsmall", "sqrt(x)*((1 - sqrt(x))**(2*a)/2 - (sqrt(x) + 1)**(2*a)/2)"],
    ["log2", 0, "nonrep", "Piecewise((log(sqrt(x)/2) + I*asin(1/sqrt(x)) - I*pi/2, Abs(x) > 1), (log(sqrt(1 - x)/2 + 1/2), True))"],
    ["log2", 0, "nonrepsmall", "log(sqrt(1 - x)/2 + 1/2)"],
    ["log2", 1, "nonrep", "log(sqrt(x + 1)/2 + 1/2)"],
    ["log2", 1, "nonrepsmall", "log(sqrt(x + 1)/2 + 1/2)"],
    ["log2", 2, "nonrep", "Piecewise((log(sqrt(x)/2) - I*asin(1/sqrt(x)) + I*pi/2, Abs(x) > 1), (log(sqrt(1 - x)/2 + 1/2), True))"],
    ["log2", 2, "nonrepsmall", "log(sqrt(1 - x)/2 + 1/2)"],
    ["log2", 3, "nonrep", "Piecewise((log(sqrt(x + 1)/2 - 1/2) + I*pi, Abs(x) > 1), (log(sqrt(x + 1)/2 + 1/2), True))"],
    ["log2", 3, "nonrepsmall", "log(sqrt(x + 1)/2 + 1/2)"],
    ["log2", 4, "nonrep", "Piecewise((log(sqrt(x)/2) + I*asin(1/sqrt(x)) + 3*I*pi/2, Abs(x) > 1), (log(sqrt(1 - x)/2 + 1/2), True))"],
    ["log2", 4, "nonrepsmall", "log(sqrt(1 - x)/2 + 1/2)"],
    ["cosasin", 0, "nonrep", "Piecewise((cosh(2*a*acosh(sqrt(x)) - I*pi*a), Abs(x) > 1), (cos(2*a*asin(sqrt(x))), True))"],
    ["cosasin", 0, "nonrepsmall", "cos(2*a*asin(sqrt(x)))"],
    ["cosasin", 1, "nonrep", "cosh(2*a*asinh(sqrt(x)))"],
    ["cosasin", 1, "nonrepsmall", "cosh(2*a*asinh(sqrt(x)))"],
    ["cosasin", 2, "nonrep", "Piecewise((cosh(2*a*acosh(sqrt(x)) + I*pi*a), Abs(x) > 1), (cos(2*a*asin(sqrt(x))), True))"],
    ["cosasin", 2, "nonrepsmall", "cos(2*a*asin(sqrt(x)))"],
    ["cosasin", 3, "nonrep", "Piecewise((cosh(2*a*asinh(sqrt(x)) + 2*I*pi*a), Abs(x) > 1), (cosh(2*a*asinh(sqrt(x))), True))"],
    ["cosasin", 3, "nonrepsmall", "cosh(2*a*asinh(sqrt(x)))"],
    ["cosasin", 4, "nonrep", "Piecewise((cosh(2*a*acosh(sqrt(x)) + 3*I*pi*a), Abs(x) > 1), (cos(2*a*asin(sqrt(x))), True))"],
    ["cosasin", 4, "nonrepsmall", "cos(2*a*asin(sqrt(x)))"],
    ["sinasin", 0, "nonrep", "Piecewise((-sinh(2*a*acosh(sqrt(x)) - I*pi*a)/sqrt(1 - 1/x), Abs(x) > 1), (sqrt(x)*sin(2*a*asin(sqrt(x)))/sqrt(1 - x), True))"],
    ["sinasin", 0, "nonrepsmall", "sqrt(x)*sin(2*a*asin(sqrt(x)))/sqrt(1 - x)"],
    ["sinasin", 1, "nonrep", "Piecewise((-sinh(2*a*asinh(sqrt(x)))/sqrt(1 + 1/x), Abs(x) > 1), (-sqrt(x)*sinh(2*a*asinh(sqrt(x)))/sqrt(x + 1), True))"],
    ["sinasin", 1, "nonrepsmall", "-sqrt(x)*sinh(2*a*asinh(sqrt(x)))/sqrt(x + 1)"],
    ["sinasin", 2, "nonrep", "Piecewise((-sinh(2*a*acosh(sqrt(x)) + I*pi*a)/sqrt(1 - 1/x), Abs(x) > 1), (sqrt(x)*sin(2*a*asin(sqrt(x)))/sqrt(1 - x), True))"],
    ["sinasin", 2, "nonrepsmall", "sqrt(x)*sin(2*a*asin(sqrt(x)))/sqrt(1 - x)"],
    ["sinasin", 3, "nonrep", "Piecewise((-sinh(2*a*asinh(sqrt(x)) + 2*I*pi*a)/sqrt(1 + 1/x), Abs(x) > 1), (-sqrt(x)*sinh(2*a*asinh(sqrt(x)))/sqrt(x + 1), True))"],
    ["sinasin", 3, "nonrepsmall", "-sqrt(x)*sinh(2*a*asinh(sqrt(x)))/sqrt(x + 1)"],
    ["sinasin", 4, "nonrep", "Piecewise((-sinh(2*a*acosh(sqrt(x)) + 3*I*pi*a)/sqrt(1 - 1/x), Abs(x) > 1), (sqrt(x)*sin(2*a*asin(sqrt(x)))/sqrt(1 - x), True))"],
    ["sinasin", 4, "nonrepsmall", "sqrt(x)*sin(2*a*asin(sqrt(x)))/sqrt(1 - x)"],
  ];
  it('an integer exponent has no branch', () => {
    expect(sstr(new HyperRep('power1', [Rational.of(2n), mul(x, expPolar(mul(2, I, pi)))]).closedForm('nonrep'))).toBe('(1 - x)**2');
    expect(sstr(new HyperRep('power1', [Rational.of(2n), mul(x, expPolar(mul(I, pi)))]).closedForm('nonrep'))).toBe('(x + 1)**2');
  });
  it.each(cases)('%s %d %s', (name, m, target, want) => {
    const arg = m ? mul(x, expPolar(mul(m, I, pi))) : x;
    expect(sstr(new HyperRep(name, withA.has(name) ? [a, arg] : [arg]).closedForm(target))).toBe(want);
  });
});

describe('the public hyperexpand and its parameter objects (SymPy Hyper_Function, G_Function)', () => {
  const x = new sj.Sym('x');
  const r = (p: bigint, q: bigint) => sj.Rational.of(p, q);
  it('expands hyper and meijerg like SymPy, also through expand_func', () => {
    // SymPy: hyperexpand(hyper([], [S(1)/2], -x**2/4)) = cos(x), hyperexpand(x*hyper([S(1)/2, S(1)/2], [S(3)/2], x**2)) = asin(x)
    expect(String(sj.hyperexpand(sj.hyper([], [r(1n, 2n)], sj.mul(r(-1n, 4n), sj.pow(x, 2)))))).toBe('cos(x)');
    expect(String(sj.hyperexpand(sj.mul(x, sj.hyper([r(1n, 2n), r(1n, 2n)], [r(3n, 2n)], sj.pow(x, 2)))))).toBe('asin(x)');
    // expand_func(hyper((a, b), (c,), 1)) = gamma(c)*gamma(-a - b + c)/(gamma(-a + c)*gamma(-b + c))
    const [a, b, c] = sj.symbols('a b c') as [sj.Sym, sj.Sym, sj.Sym];
    expect(String(sj.expandFunc(sj.hyper([a, b], [c], 1)))).toBe('gamma(c)*gamma(-a - b + c)/(gamma(-a + c)*gamma(-b + c))');
  });
  it('builds the invariants of Hyper_Function', () => {
    // SymPy: Hyper_Function((S.Half, S.One/3, S(-1)/2, -2), (1, 2)).build_invariants() = (1, ((0, 1), (1/3, 1), (1/2, 2)), ((0, 2),))
    const f = new sj.Hyper_Function([r(1n, 2n), r(1n, 3n), r(-1n, 2n), -2], [1, 2]);
    expect(f.ap.map(String)).toEqual(['1/2', '1/3', '-1/2', '-2']);
    expect(f.bq.map(String)).toEqual(['1', '2']);
    const [g, ai, bi] = f.buildInvariants();
    expect(g).toBe(1);
    expect(ai.map(([m, n]) => `${String(m)}:${n}`)).toEqual(['0:1', '1/3:1', '1/2:2']);
    expect(bi.map(([m, n]) => `${String(m)}:${n}`)).toEqual(['0:2']);
    // SymPy: Hyper_Function((S.Half,), (1,)).gamma = 0
    expect(new sj.Hyper_Function([r(1n, 2n)], [1]).gamma).toBe(0);
  });
  it('computes the buckets of G_Function', () => {
    // SymPy: G_Function([1, 3, 2, S(3)/2], [1 + y, y, 2, y + 3], [2], [y]).compute_buckets()
    //   = ({0: [3, 2, 1], 1/2: [3/2]}, {y: [y, y + 1, y + 3], 0: [2]}, {0: [2]}, {y: [y]})
    const y = new sj.Sym('y');
    const g = new sj.G_Function([1, 3, 2, r(3n, 2n)], [sj.add(1, y), y, 2, sj.add(y, 3)], [2], [y]);
    expect([g.an, g.ap, g.bm, g.bq].map((l) => l.length)).toEqual([4, 4, 1, 1]);
    const show = (m: Map<sj.Expr, sj.Expr[]>) => [...m].map(([k, v]) => `${String(k)}: [${v.map(String).join(', ')}]`).join('; ');
    expect(g.computeBuckets().map(show)).toEqual(['0: [3, 2, 1]; 1/2: [3/2]', 'y: [y, y + 1, y + 3]; 0: [2]', '0: [2]', 'y: [y]']);
  });
});

describe('Operator (SymPy sympy.simplify.hyperexpand.Operator)', () => {
  const [x, y, z] = [new Sym('x'), new Sym('y'), new Sym('z')];
  it('applies the polynomial in its generator', () => {
    // op = Operator(); op._poly = Poly(x**2 + z*x + y, x); op.apply(z**7, lambda f: f.diff(z))
    const op = new sj.Operator(parse('x**2 + z*x + y'), x);
    expect(sstr(op.apply(parse('z**7'), (f) => sj.diff(f, z)))).toBe('y*z**7 + 7*z**7 + 42*z**5');
    expect(op.poly.map(sstr)).toEqual(['y', 'z', '1']);
    // a missing power of the generator has the coefficient 0: (D**2 + y)(z**3) = 6*z + y*z**3
    const op2 = new sj.Operator(parse('x**2 + y'), x);
    expect(op2.poly.map(sstr)).toEqual(['y', '0', '1']);
    expect(sstr(op2.apply(parse('z**3'), (f) => sj.diff(f, z)))).toBe('y*z**3 + 6*z');
  });
  it('a constant operator without a generator, and the zero operator', () => {
    expect(sstr(new sj.Operator(3).apply(y, (f) => sj.diff(f, y)))).toBe('3*y');
    expect(sstr(new sj.Operator().apply(y, (f) => f))).toBe('0');
  });
  it('rejects a polynomial that is not one in the generator', () => {
    // SymPy Poly(1/x, x) raises PolynomialError
    expect(() => new sj.Operator(parse('1/x'), x)).toThrow(sj.PolynomialError);
  });
});
