// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/printing/mathml.ts. Expected values from SymPy 1.14 mathml(...) and print_mathml(...).

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { mul, pow } from '../../src';
import { Dummy, Float, Integral, Limit, Rational, S, Sym } from '../../src/core/nodes';
import type { Expr } from '../../src/core/nodes';
import { MathMLContentPrinter, MathMLElement, MathMLPresentationPrinter, mathml, printMathml } from '../../src/printing/mathml';
import type { MathMLPrintable, MathMLPrintOptions } from '../../src/printing/mathml';
import * as Sets from '../../src/sets/sets';
import { BoolOp } from '../../src/core/boolalg';
import { fromStr } from '../../src/numeric/mpf';

const [x, y, z] = sj.symbols('x y z') as [Sym, Sym, Sym];
const n = sj.symbol('n', { integer: true });
const f = sj.SymFunction('f');
const R = (p: number, q = 1): Rational => Rational.of(BigInt(p), BigInt(q));
const M = (rows: sj.ExprLike[][]): sj.Matrix => sj.Matrix.of(rows);
const SYM = sj.add(sj.symbol('x_1^2'), sj.symbol('alpha_beta'), sj.symbol('y^a'), sj.symbol('z_a_b'));

describe('mathml (SymPy doctests)', () => {
  it('content and presentation MathML of x + 1', () => {
    expect(mathml(sj.add(x, 1))).toBe('<apply><plus/><ci>x</ci><cn>1</cn></apply>');
    expect(mathml(sj.add(x, 1), { printer: 'presentation' })).toBe('<mrow><mi>x</mi><mo>+</mo><mn>1</mn></mrow>');
  });
  it('print_mathml indents with tabs', () => {
    expect(printMathml(sj.add(x, 1))).toBe('<apply>\n\t<plus/>\n\t<ci>x</ci>\n\t<cn>1</cn>\n</apply>\n\n');
    expect(printMathml(sj.add(x, 1), { printer: 'presentation' })).toBe('<mrow>\n\t<mi>x</mi>\n\t<mo>+</mo>\n\t<mn>1</mn>\n</mrow>\n\n');
    expect(printMathml(sj.add(sj.sqrt(x), 1))).toBe("<apply>\n\t<plus/>\n\t<apply>\n\t\t<root/>\n\t\t<ci>x</ci>\n\t</apply>\n\t<cn>1</cn>\n</apply>\n\n");
    expect(printMathml(sj.symbol('x_1'), { printer: 'presentation' })).toBe("<msub>\n\t<mi>x</mi>\n\t<mi>1</mi>\n</msub>\n\n");
  });
});

describe('mathml of the nodes and settings', () => {
  const cases: [string, () => MathMLPrintable, MathMLPrintOptions, string][] = [
    ["Matrix([[1, x], [y, 2]])", () => M([[1, x], [y, 2]]), {}, "<matrix><matrixrow><cn>1</cn><ci>x</ci></matrixrow><matrixrow><ci>y</ci><cn>2</cn></matrixrow></matrix>"],
    ["Matrix p", () => M([[1, x], [y, 2]]), {"printer": "presentation"}, "<mrow><mo>[</mo><mtable><mtr><mtd><mn>1</mn></mtd><mtd><mi>x</mi></mtd></mtr><mtr><mtd><mi>y</mi></mtd><mtd><mn>2</mn></mtd></mtr></mtable><mo>]</mo></mrow>"],
    ["Matrix p (", () => M([[1]]), {"printer": "presentation", "matDelim": "("}, "<mrow><mo>(</mo><mtable><mtr><mtd><mn>1</mn></mtd></mtr></mtable><mo>)</mo></mrow>"],
    ["Matrix p none", () => M([[1]]), {"printer": "presentation", "matDelim": ""}, "<mtable><mtr><mtd><mn>1</mn></mtd></mtr></mtable>"],
    ["list", () => [x, 1], {}, "<list><ci>x</ci><cn>1</cn></list>"],
    ["Integral c", () => new Integral([x, x, S.Zero, S.One]), {}, "<apply><int/><bvar><ci>x</ci></bvar><lowlimit><cn>0</cn></lowlimit><uplimit><cn>1</cn></uplimit><ci>x</ci></apply>"],
    ["Integral2 c", () => new Integral([new Integral([mul(x, y), x, S.Zero, S.One]), y, S.Zero, S.Two]), {}, "<apply><int/><bvar><ci>y</ci></bvar><lowlimit><cn>0</cn></lowlimit><uplimit><cn>2</cn></uplimit><apply><int/><bvar><ci>x</ci></bvar><lowlimit><cn>0</cn></lowlimit><uplimit><cn>1</cn></uplimit><apply><times/><ci>x</ci><ci>y</ci></apply></apply></apply>"],
    ["Integral x c", () => new Integral([x, x]), {}, "<apply><int/><bvar><ci>x</ci></bvar><ci>x</ci></apply>"],
    ["Integral p", () => new Integral([x, x, S.Zero, S.One]), {"printer": "presentation"}, "<mrow><msubsup><mo>&#x222B;</mo><mn>0</mn><mn>1</mn></msubsup><mi>x</mi><mo>&dd;</mo><mi>x</mi></mrow>"],
    ["Integral x p", () => new Integral([x, x]), {"printer": "presentation"}, "<mrow><mo>&#x222B;</mo><mi>x</mi><mo>&dd;</mo><mi>x</mi></mrow>"],
    ["Integral xy p", () => new Integral([new Integral([mul(x, y), x]), y]), {"printer": "presentation"}, "<mrow><mo>&#x222C;</mo><mrow><mi>x</mi><mo>&InvisibleTimes;</mo><mi>y</mi></mrow><mo>&dd;</mo><mi>y</mi><mo>&dd;</mo><mi>x</mi></mrow>"],
    ["Integral 4 p", () => new Integral([new Integral([new Integral([new Integral([mul(x, y, z, n), x]), y]), z]), n]), {"printer": "presentation"}, "<mrow><mo>&#x222B;</mo><mo>&#x222B;</mo><mo>&#x222B;</mo><mo>&#x222B;</mo><mrow><mi>n</mi><mo>&InvisibleTimes;</mo><mi>x</mi><mo>&InvisibleTimes;</mo><mi>y</mi><mo>&InvisibleTimes;</mo><mi>z</mi></mrow><mo>&dd;</mo><mi>n</mi><mo>&dd;</mo><mi>z</mi><mo>&dd;</mo><mi>y</mi><mo>&dd;</mo><mi>x</mi></mrow>"],
    ["Integral mixed p", () => new Integral([new Integral([mul(x, y), x, S.Zero, S.One]), y]), {"printer": "presentation"}, "<mrow><mo>&#x222B;</mo><msubsup><mo>&#x222B;</mo><mn>0</mn><mn>1</mn></msubsup><mrow><mi>x</mi><mo>&InvisibleTimes;</mo><mi>y</mi></mrow><mo>&dd;</mo><mi>y</mi><mo>&dd;</mo><mi>x</mi></mrow>"],
    ["Sum c", () => sj.Sum(x, [x, 1, 3]), {}, "<apply><sum/><bvar><ci>x</ci></bvar><lowlimit><cn>1</cn></lowlimit><uplimit><cn>3</cn></uplimit><ci>x</ci></apply>"],
    ["Sum p", () => sj.Sum(x, [x, 1, 3]), {"printer": "presentation"}, "<mrow><munderover><mo>&#x2211;</mo><mrow><mi>x</mi><mo>=</mo><mn>1</mn></mrow><mn>3</mn></munderover><mi>x</mi></mrow>"],
    ["Sum add p", () => sj.Sum(sj.add(x, 1), [x, 1, 3]), {"printer": "presentation"}, "<mrow><munderover><mo>&#x2211;</mo><mrow><mi>x</mi><mo>=</mo><mn>1</mn></mrow><mn>3</mn></munderover><mrow><mo>(</mo><mrow><mi>x</mi><mo>+</mo><mn>1</mn></mrow><mo>)</mo></mrow></mrow>"],
    ["Product c", () => sj.Product(x, [x, 1, 3]), {}, "<product><ci>x</ci><tuple><ci>x</ci><cn>1</cn><cn>3</cn></tuple></product>"],
    ["Product p", () => sj.Product(x, [x, 1, 3]), {"printer": "presentation"}, "<mrow><mi>product</mi><mrow><mo>(</mo><mi>x</mi><mo>,</mo><mrow><mo>(</mo><mi>x</mi><mo>,</mo><mn>1</mn><mo>,</mo><mn>3</mn><mo>)</mo></mrow><mo>)</mo></mrow></mrow>"],
    ["Limit c", () => new Limit([mul(sj.sin(x), pow(x, -1)), x, S.Zero]), {}, "<apply><limit/><bvar><ci>x</ci></bvar><lowlimit><cn>0</cn></lowlimit><apply><divide/><apply><sin/><ci>x</ci></apply><ci>x</ci></apply></apply>"],
    ["Limit p", () => new Limit([mul(sj.sin(x), pow(x, -1)), x, S.Zero]), {"printer": "presentation"}, "<mrow><munder><mi>lim</mi><mrow><mi>x</mi><mo>&#x2192;</mo><mn>0</mn></mrow></munder><mrow><mfrac><mrow><mi>sin</mi><mrow><mo>(</mo><mi>x</mi><mo>)</mo></mrow></mrow><mi>x</mi></mfrac></mrow></mrow>"],
    ["Piecewise c", () => sj.Piecewise([x, sj.Lt(x, 0)], [1, true]), {}, "<piecewise><piece><ci>x</ci><apply><lt/><ci>x</ci><cn>0</cn></apply></piece><otherwise><cn>1</cn></otherwise></piecewise>"],
    ["Derivative c", () => sj.Derivative(f(x), [x, 2]), {}, "<apply><diff/><bvar><ci>x</ci><degree><cn>2</cn></degree></bvar><apply><f/><ci>x</ci></apply></apply>"],
    ["Derivative partial c", () => sj.Derivative(f(x, y), x, y), {}, "<apply><partialdiff/><bvar><ci>y</ci><ci>x</ci></bvar><apply><f/><ci>x</ci><ci>y</ci></apply></apply>"],
    ["Derivative p", () => sj.Derivative(f(x), [x, 2]), {"printer": "presentation"}, "<mrow><mfrac><mrow><msup><mo>&dd;</mo><mn>2</mn></msup></mrow><mrow><msup><mo>&dd;</mo><mn>2</mn></msup><mi>x</mi></mrow></mfrac><mrow><mi>f</mi><mrow><mo>(</mo><mi>x</mi><mo>)</mo></mrow></mrow></mrow>"],
    ["Derivative partial p", () => sj.Derivative(f(x, y), x, y), {"printer": "presentation"}, "<mrow><mfrac><mrow><msup><mo>&#x2202;</mo><mn>2</mn></msup></mrow><mrow><mo>&#x2202;</mo><mi>y</mi><mo>&#x2202;</mo><mi>x</mi></mrow></mfrac><mrow><mi>f</mi><mrow><mo>(</mo><mi>x</mi><mo>,</mo><mi>y</mi><mo>)</mo></mrow></mrow></mrow>"],
    ["Interval p", () => Sets.Lopen(0, 1), {"printer": "presentation"}, "<mrow><mo>(</mo><mn>0</mn><mo>,</mo><mn>1</mn><mo>]</mo></mrow>"],
    ["FiniteSet c", () => Sets.finiteSet(2, 1), {}, "<set><cn>1</cn><cn>2</cn></set>"],
    ["FiniteSet p", () => Sets.finiteSet(2, 1), {"printer": "presentation"}, "<mrow><mo>{</mo><mn>1</mn><mo>,</mo><mn>2</mn><mo>}</mo></mrow>"],
    ["Union c", () => Sets.union(Sets.interval(0, 1), Sets.finiteSet(3)), {}, "<apply><union/><interval><cn>0</cn><cn>1</cn><false/><false/></interval><set><cn>3</cn></set></apply>"],
    ["Union p", () => Sets.union(Sets.interval(0, 1), Sets.finiteSet(3)), {"printer": "presentation"}, "<mrow><mrow><mo>[</mo><mn>0</mn><mo>,</mo><mn>1</mn><mo>]</mo></mrow><mo>&#x222A;</mo><mrow><mo>{</mo><mn>3</mn><mo>}</mo></mrow></mrow>"],
    ["Intersection c", () => new Sets.SetOp('Intersection', [Sets.interval(0, x), Sets.finiteSet(y)]), {}, "<apply><intersect/><interval><cn>0</cn><ci>x</ci><false/><false/></interval><set><ci>y</ci></set></apply>"],
    ["Intersection p", () => new Sets.SetOp('Intersection', [Sets.interval(0, x), Sets.finiteSet(y)]), {"printer": "presentation"}, "<mrow><mrow><mo>[</mo><mn>0</mn><mo>,</mo><mi>x</mi><mo>]</mo></mrow><mo>&#x2229;</mo><mrow><mo>{</mo><mi>y</mi><mo>}</mo></mrow></mrow>"],
    ["Complement c", () => new Sets.SetOp('Complement', [Sets.interval(0, 1), Sets.finiteSet(x)]), {}, "<apply><setdiff/><interval><cn>0</cn><cn>1</cn><false/><false/></interval><set><ci>x</ci></set></apply>"],
    ["Complement p", () => new Sets.SetOp('Complement', [Sets.interval(0, 1), Sets.finiteSet(x)]), {"printer": "presentation"}, "<mrow><mrow><mo>[</mo><mn>0</mn><mo>,</mo><mn>1</mn><mo>]</mo></mrow><mo>&#x2216;</mo><mrow><mo>{</mo><mi>x</mi><mo>}</mo></mrow></mrow>"],
    ["Union in Intersection p", () => new Sets.SetOp('Intersection', [new Sets.SetOp('Union', [Sets.interval(0, 1), Sets.interval(2, 3)]), Sets.interval(x, y)]), {"printer": "presentation"}, "<mrow><mrow><mo>(</mo><mrow><mrow><mo>[</mo><mn>0</mn><mo>,</mo><mn>1</mn><mo>]</mo></mrow><mo>&#x222A;</mo><mrow><mo>[</mo><mn>2</mn><mo>,</mo><mn>3</mn><mo>]</mo></mrow></mrow><mo>)</mo></mrow><mo>&#x2229;</mo><mrow><mo>[</mo><mi>x</mi><mo>,</mo><mi>y</mi><mo>]</mo></mrow></mrow>"],
    ["Naturals0 p", () => Sets.Naturals0, {"printer": "presentation"}, "<msub><mi mathvariant=\"normal\">&#x2115;</mi><mn>0</mn></msub>"],
    ["Reals p", () => Sets.Reals, {"printer": "presentation"}, "<mi mathvariant=\"normal\">&#x211D;</mi>"],
    ["EmptySet c", () => Sets.EmptySet, {}, "<emptyset/>"],
    ["EmptySet p", () => Sets.EmptySet, {"printer": "presentation"}, "<mo>&#x2205;</mo>"],
    ["Reals c", () => Sets.Reals, {}, "<reals/>"],
    ["And c", () => sj.And(sj.Lt(x, 1), sj.Lt(y, 1)), {}, "<apply><and/><apply><lt/><ci>x</ci><cn>1</cn></apply><apply><lt/><ci>y</ci><cn>1</cn></apply></apply>"],
    ["And p", () => sj.And(sj.Lt(x, 1), sj.Lt(y, 1)), {"printer": "presentation"}, "<mrow><mrow><mi>x</mi><mo><</mo><mn>1</mn></mrow><mo>&#x2227;</mo><mrow><mi>y</mi><mo><</mo><mn>1</mn></mrow></mrow>"],
    ["Or p", () => sj.Or(sj.Lt(x, 1), sj.Not(sj.Lt(y, 1))), {"printer": "presentation"}, "<mrow><mrow><mi>y</mi><mo>&#x2265;</mo><mn>1</mn></mrow><mo>&#x2228;</mo><mrow><mi>x</mi><mo><</mo><mn>1</mn></mrow></mrow>"],
    ["Not p", () => sj.Not(sj.And(sj.Lt(x, 1), sj.Lt(y, 1))), {"printer": "presentation"}, "<mrow><mo>&#xAC;</mo><mrow><mo>(</mo><mrow><mrow><mi>x</mi><mo><</mo><mn>1</mn></mrow><mo>&#x2227;</mo><mrow><mi>y</mi><mo><</mo><mn>1</mn></mrow></mrow><mo>)</mo></mrow></mrow>"],
    ["Implies p", () => sj.Implies(sj.Lt(x, 1), sj.Lt(y, 1)), {"printer": "presentation"}, "<mrow><mrow><mi>x</mi><mo><</mo><mn>1</mn></mrow><mo>&#x21D2;</mo><mrow><mi>y</mi><mo><</mo><mn>1</mn></mrow></mrow>"],
    ["Xor c", () => sj.Xor(sj.Lt(x, 1), sj.Lt(y, 1)), {}, "<apply><xor/><apply><lt/><ci>x</ci><cn>1</cn></apply><apply><lt/><ci>y</ci><cn>1</cn></apply></apply>"],
    ["Xor p", () => sj.Xor(sj.Lt(x, 1), sj.Lt(y, 1)), {"printer": "presentation"}, "<mrow><mrow><mi>x</mi><mo><</mo><mn>1</mn></mrow><mo>&#x22BB;</mo><mrow><mi>y</mi><mo><</mo><mn>1</mn></mrow></mrow>"],
    ["Lambda c", () => sj.Lambda(x, pow(x, 2)), {}, "<lambda><bvar><ci>x</ci></bvar><apply><power/><ci>x</ci><cn>2</cn></apply></lambda>"],
    ["Lambda p", () => sj.Lambda(x, pow(x, 2)), {"printer": "presentation"}, "<mrow><mo>(</mo><mi>x</mi><mo>&#x21A6;</mo><msup><mi>x</mi><mn>2</mn></msup><mo>)</mo></mrow>"],
    ["Lambda2 p", () => sj.Lambda([x, y], sj.add(x, y)), {"printer": "presentation"}, "<mrow><mo>(</mo><mrow><mo>(</mo><mi>x</mi><mo>,</mo><mi>y</mi><mo>)</mo></mrow><mo>&#x21A6;</mo><mrow><mi>x</mi><mo>+</mo><mi>y</mi></mrow><mo>)</mo></mrow>"],
    ["Tuple p", () => sj.Tuple(x, 1), {"printer": "presentation"}, "<mrow><mo>(</mo><mi>x</mi><mo>,</mo><mn>1</mn><mo>)</mo></mrow>"],
    ["Tuple c", () => sj.Tuple(x, 1), {}, "<tuple><ci>x</ci><cn>1</cn></tuple>"],
    ["true p", () => S.true, {"printer": "presentation"}, "<mi>True</mi>"],
    ["true c", () => S.true, {}, "<true/>"],
    ["false c", () => S.false, {}, "<false/>"],
    ["consts c", () => [sj.pi, sj.E, sj.I, S.Infinity, S.NegativeInfinity, S.NaN, S.EulerGamma, S.GoldenRatio], {}, "<list><pi/><exponentiale/><imaginaryi/><infinity/><apply><minus/><infinity/></apply><notanumber/><eulergamma/><cn>&#966;</cn></list>"],
    ["consts p", () => sj.Tuple(sj.pi, sj.E, sj.I, S.Infinity, S.NegativeInfinity, S.NaN, S.ComplexInfinity, S.EulerGamma, S.GoldenRatio, S.TribonacciConstant), {"printer": "presentation"}, "<mrow><mo>(</mo><mi>&pi;</mi><mo>,</mo><mi>&ExponentialE;</mi><mo>,</mo><mi>&ImaginaryI;</mi><mo>,</mo><mi>&#x221E;</mi><mo>,</mo><mrow><mo>-</mo><mi>&#x221E;</mi></mrow><mo>,</mo><mi>NaN</mi><mo>,</mo><mover><mo>&#x221E;</mo><mo>~</mo></mover><mo>,</mo><mi>&#x3B3;</mi><mo>,</mo><mi>&#x3A6;</mi><mo>,</mo><mi>TribonacciConstant</mi><mo>)</mo></mrow>"],
    ["zoo c", () => S.ComplexInfinity, {}, "<complexinfinity/>"],
    ["Catalan c", () => S.Catalan, {}, "<catalan/>"],
    ["Float c", () => new Float(1.25), {}, "<cn>1.25</cn>"],
    ["Float p", () => new Float(1.25e-30), {"printer": "presentation"}, "<mrow><mn>1.25</mn><mo>&#xB7;</mo><msup><mn>10</mn><mn>-30</mn></msup></mrow>"],
    ["Float p sep", () => new Float(1.25e30), {"printer": "presentation", "mulSymbolMathmlNumbers": "&#xD7;"}, "<mrow><mn>1.25</mn><mo>&#xD7;</mo><msup><mn>10</mn><mn>30</mn></msup></mrow>"],
    ["sym c", () => SYM, {}, "<apply><plus/><ci><mml:msub><mml:mi>&#945;</mml:mi><mml:mi>&#946;</mml:mi></mml:msub></ci><ci><mml:msubsup><mml:mi>x</mml:mi><mml:mi>1</mml:mi><mml:mi>2</mml:mi></mml:msubsup></ci><ci><mml:msup><mml:mi>y</mml:mi><mml:mi>a</mml:mi></mml:msup></ci><ci><mml:msub><mml:mi>z</mml:mi><mml:mrow><mml:mi>a</mml:mi><mml:mo> </mml:mo><mml:mi>b</mml:mi></mml:mrow></mml:msub></ci></apply>"],
    ["sym p", () => SYM, {"printer": "presentation"}, "<mrow><msub><mi>&#945;</mi><mi>&#946;</mi></msub><mo>+</mo><msubsup><mi>x</mi><mi>1</mi><mi>2</mi></msubsup><mo>+</mo><msup><mi>y</mi><mi>a</mi></msup><mo>+</mo><msub><mi>z</mi><mrow><mi>a</mi><mo> </mo><mi>b</mi></mrow></msub></mrow>"],
    ["sym disable p", () => sj.symbol('x_1'), {"printer": "presentation", "disableSplitSuperSub": true}, "<mi>x_1</mi>"],
    ["MatrixSymbol bold p", () => sj.MatrixSymbol('A', 2, 2), {"printer": "presentation", "matSymbolStyle": "bold"}, "<mi mathvariant=\"bold\">A</mi>"],
    ["MatrixSymbol c", () => sj.MatrixSymbol('A', 2, 2), {}, "<ci>A</ci>"],
    ["fold short p", () => sj.add(mul(x, R(1, 2)), R(1, 3)), {"printer": "presentation", "foldShortFrac": true}, "<mrow><mrow><mfrac bevelled=\"true\"><mi>x</mi><mn>2</mn></mfrac></mrow><mo>+</mo><mfrac bevelled=\"true\"><mn>1</mn><mn>3</mn></mfrac></mrow>"],
    ["fold frac powers p", () => sj.add(pow(x, R(2, 3)), pow(y, R(-2, 3))), {"printer": "presentation", "foldFracPowers": true}, "<mrow><msup><mi>x</mi><mfrac bevelled=\"true\"><mn>2</mn><mn>3</mn></mfrac></msup><mo>+</mo><mfrac><mn>1</mn><msup><mi>y</mi><mfrac bevelled=\"true\"><mn>2</mn><mn>3</mn></mfrac></msup></mfrac></mrow>"],
    ["pow neg p", () => sj.add(pow(x, -3), pow(y, mul(-1, x))), {"printer": "presentation"}, "<mrow><msup><mi>y</mi><mrow><mo>-</mo><mi>x</mi></mrow></msup><mo>+</mo><mfrac><mn>1</mn><msup><mi>x</mi><mn>3</mn></msup></mfrac></mrow>"],
    ["root c", () => sj.add(pow(x, R(1, 3)), sj.sqrt(y)), {}, "<apply><plus/><apply><root/><degree><cn>3</cn></degree><ci>x</ci></apply><apply><root/><ci>y</ci></apply></apply>"],
    ["root off c", () => sj.sqrt(y), {"rootNotation": false}, "<apply><power/><ci>y</ci><apply><divide/><cn>1</cn><cn>2</cn></apply></apply>"],
    ["root off p", () => sj.add(sj.sqrt(y), pow(y, R(-1, 3))), {"printer": "presentation", "rootNotation": false}, "<mrow><msup><mi>y</mi><mfrac><mn>1</mn><mn>2</mn></mfrac></msup><mo>+</mo><mfrac><mn>1</mn><msup><mi>y</mi><mfrac><mn>1</mn><mn>3</mn></mfrac></msup></mfrac></mrow>"],
    ["mul times p", () => mul(2, x, y), {"printer": "presentation", "mulSymbol": "times"}, "<mrow><mn>2</mn><mo>&#xD7;</mo><mi>x</mi><mo>&#xD7;</mo><mi>y</mi></mrow>"],
    ["mul dot p", () => mul(2, x, y), {"printer": "presentation", "mulSymbol": "dot"}, "<mrow><mn>2</mn><mo>&#xB7;</mo><mi>x</mi><mo>&#xB7;</mo><mi>y</mi></mrow>"],
    ["mul ldot p", () => mul(2, x, y), {"printer": "presentation", "mulSymbol": "ldot"}, "<mrow><mn>2</mn><mo>&#x2024;</mo><mi>x</mi><mo>&#x2024;</mo><mi>y</mi></mrow>"],
    ["mul custom p", () => mul(2, x, y), {"printer": "presentation", "mulSymbol": "*"}, "<mrow><mn>2</mn><mo>*</mo><mi>x</mi><mo>*</mo><mi>y</mi></mrow>"],
    ["ln p", () => sj.log(x), {"printer": "presentation", "lnNotation": true}, "<mrow><mi>ln</mi><mrow><mo>(</mo><mi>x</mi><mo>)</mo></mrow></mrow>"],
    ["log c", () => sj.log(x), {}, "<apply><ln/><ci>x</ci></apply>"],
    ["funcs p", () => sj.Tuple(sj.floor(x), sj.ceiling(x), sj.factorial(x), sj.factorial2(x), sj.binomial(x, y), sj.conjugate(x), sj.re(x), sj.im(x), sj.Abs(x), sj.Min(x, y), sj.Max(x, y), sj.polylog(x, y), sj.bernoulli(n), sj.bernoulli(n, x), sj.exp(x), sj.gamma(x), f(x)), {"printer": "presentation"}, "<mrow><mo>(</mo><mrow><mo>&#8970;</mo><mi>x</mi><mo>&#8971;</mo></mrow><mo>,</mo><mrow><mo>&#8968;</mo><mi>x</mi><mo>&#8969;</mo></mrow><mo>,</mo><mrow><mi>x</mi><mo>!</mo></mrow><mo>,</mo><mrow><mi>x</mi><mo>!!</mo></mrow><mo>,</mo><mrow><mo>(</mo><mfrac linethickness=\"0\"><mi>x</mi><mi>y</mi></mfrac><mo>)</mo></mrow><mo>,</mo><menclose notation=\"top\"><mi>x</mi></menclose><mo>,</mo><mrow><mi>&#8476;</mi><mrow><mo>(</mo><mi>x</mi><mo>)</mo></mrow></mrow><mo>,</mo><mrow><mi>&#8465;</mi><mrow><mo>(</mo><mi>x</mi><mo>)</mo></mrow></mrow><mo>,</mo><mrow><mo>|</mo><mi>x</mi><mo>|</mo></mrow><mo>,</mo><mrow><mo>min</mo><mrow><mo>(</mo><mi>x</mi><mo>,</mo><mi>y</mi><mo>)</mo></mrow></mrow><mo>,</mo><mrow><mo>max</mo><mrow><mo>(</mo><mi>x</mi><mo>,</mo><mi>y</mi><mo>)</mo></mrow></mrow><mo>,</mo><mrow><msub><mi>Li</mi><mi>x</mi></msub><mrow><mo>(</mo><mi>y</mi><mo>)</mo></mrow></mrow><mo>,</mo><msub><mi>B</mi><mi>n</mi></msub><mo>,</mo><mrow><msub><mi>B</mi><mi>n</mi></msub><mrow><mo>(</mo><mi>x</mi><mo>)</mo></mrow></mrow><mo>,</mo><msup><mi>&ExponentialE;</mi><mi>x</mi></msup><mo>,</mo><mrow><mi>&#x393;</mi><mrow><mo>(</mo><mi>x</mi><mo>)</mo></mrow></mrow><mo>,</mo><mrow><mi>f</mi><mrow><mo>(</mo><mi>x</mi><mo>)</mo></mrow></mrow><mo>)</mo></mrow>"],
    ["funcs c", () => sj.Tuple(sj.floor(x), sj.Abs(x), sj.Min(x, y), sj.exp(x), sj.gamma(x), f(x), sj.asin(x)), {}, "<tuple><apply><floor/><ci>x</ci></apply><apply><abs/><ci>x</ci></apply><apply><min/><ci>x</ci><ci>y</ci></apply><apply><exp/><ci>x</ci></apply><apply><gamma/><ci>x</ci></apply><apply><f/><ci>x</ci></apply><apply><arcsin/><ci>x</ci></apply></tuple>"],
    ["neg mul c", () => sj.add(mul(-1, x, y), 3), {}, "<apply><plus/><apply><minus/><apply><times/><ci>x</ci><ci>y</ci></apply></apply><cn>3</cn></apply>"],
    ["mul paren p", () => mul(x, sj.add(y, 1)), {"printer": "presentation"}, "<mrow><mi>x</mi><mo>&InvisibleTimes;</mo><mrow><mo>(</mo><mrow><mi>y</mi><mo>+</mo><mn>1</mn></mrow><mo>)</mo></mrow></mrow>"],
    ["dummy c", () => new Dummy('d'), {}, "<ci>d</ci>"],
    ["Range p", () => Sets.Range.of(1, 5), {"printer": "presentation"}, "<mrow><mo>{</mo><mn>1</mn><mo>,</mo><mn>2</mn><mo>,</mo><mn>3</mn><mo>,</mo><mn>4</mn><mo>}</mo></mrow>"],
  ];
  it.each(cases)('%s', (_label, build, options, expected) => {
    expect(mathml(build(), options)).toBe(expected);
  });
});

describe('the rest of the MathML printers', () => {
  it('a Piecewise without a True condition is an error in content MathML (SymPy ValueError)', () => {
    expect(() => mathml(sj.Piecewise([x, sj.Lt(x, 0)], [1, sj.Gt(x, 0)]))).toThrow(RangeError);
  });
  it('a list in presentation MathML prints like a tuple (SymPy fails)', () => {
    expect(mathml([x, 1], { printer: 'presentation' })).toBe('<mrow><mo>(</mo><mi>x</mi><mo>,</mo><mn>1</mn><mo>)</mo></mrow>');
    expect(mathml(2, { printer: 'presentation' })).toBe('<mn>2</mn>');
    expect(mathml(2n)).toBe('<cn>2</cn>');
  });
  it('more sets and logic (SymPy 1.14)', () => {
    const P = { printer: 'presentation' } as const;
    expect(mathml(Sets.Range.of(0, S.Infinity), P)).toBe('<mrow><mo>{</mo><mn>0</mn><mo>,</mo><mn>1</mn><mo>,</mo><mi>&#8230;</mi><mo>}</mo></mrow>');
    expect(mathml(Sets.Range.of(1, 20, 2), P)).toBe('<mrow><mo>{</mo><mn>1</mn><mo>,</mo><mn>3</mn><mo>,</mo><mi>&#8230;</mi><mo>,</mo><mn>19</mn><mo>}</mo></mrow>');
    expect(mathml(Sets.Naturals, P)).toBe('<mi mathvariant="normal">&#x2115;</mi>');
    expect(mathml(Sets.Integers, P)).toBe('<mi mathvariant="normal">&#x2124;</mi>');
    expect(mathml(Sets.Complexes, P)).toBe('<mi mathvariant="normal">&#x2102;</mi>');
    const I01 = Sets.interval(0, 1);
    expect(mathml(new Sets.SymmetricDifferenceNode([I01, Sets.finiteSet(3)]), P)).toBe('<mrow><mrow><mo>[</mo><mn>0</mn><mo>,</mo><mn>1</mn><mo>]</mo></mrow><mo>&#x2206;</mo><mrow><mo>{</mo><mn>3</mn><mo>}</mo></mrow></mrow>');
    const PS = sj.ProductSet(I01, Sets.finiteSet(3));
    expect(mathml(PS, P)).toBe('<mrow><mrow><mo>[</mo><mn>0</mn><mo>,</mo><mn>1</mn><mo>]</mo></mrow><mo>&#x00d7;</mo><mrow><mo>{</mo><mn>3</mn><mo>}</mo></mrow></mrow>');
    expect(mathml(PS)).toBe('<apply><cartesianproduct/><interval><cn>0</cn><cn>1</cn><false/><false/></interval><set><cn>3</cn></set></apply>');
    expect(mathml(new Sets.SetOp('Union', [PS, Sets.finiteSet(9)]), P)).toBe(
      '<mrow><mrow><mo>{</mo><mn>9</mn><mo>}</mo></mrow><mo>&#x222A;</mo><mrow><mo>(</mo><mrow><mrow><mo>[</mo><mn>0</mn><mo>,</mo><mn>1</mn><mo>]</mo></mrow><mo>&#x00d7;</mo><mrow><mo>{</mo><mn>3</mn><mo>}</mo></mrow></mrow><mo>)</mo></mrow></mrow>',
    );
    expect(mathml(sj.Equivalent(sj.Lt(x, 1), sj.Gt(x, 0)), P)).toBe('<mrow><mrow><mi>x</mi><mo>></mo><mn>0</mn></mrow><mo>&#x21D4;</mo><mrow><mi>x</mi><mo><</mo><mn>1</mn></mrow></mrow>');
    expect(mathml(mul(-1, x, R(1, 2)), P)).toBe('<mrow><mo>-</mo><mfrac><mi>x</mi><mn>2</mn></mfrac></mrow>');
    expect(mathml(mul(-1, x, R(1, 2)))).toBe('<apply><minus/><apply><divide/><ci>x</ci><cn>2</cn></apply></apply>');
    expect(mathml(mul(3, x))).toBe('<apply><times/><cn>3</cn><ci>x</ci></apply>');
  });
  it('quotients, sums with negative terms, roots, floats, constants and Piecewise (SymPy 1.14)', () => {
    const P = { printer: 'presentation' } as const;
    const pn = sj.symbol('n', { positive: true });
    const cases: [Expr, MathMLPrintOptions, string][] = [
      [mul(pow(x, 2), pow(y, -1)), {}, '<apply><divide/><apply><power/><ci>x</ci><cn>2</cn></apply><ci>y</ci></apply>'],
      [mul(3, x, R(1, 2)), {}, '<apply><divide/><apply><times/><cn>3</cn><ci>x</ci></apply><cn>2</cn></apply>'],
      [mul(pow(x, mul(-1, pn)), y), {}, '<apply><divide/><ci>y</ci><apply><power/><ci>x</ci><ci>n</ci></apply></apply>'],
      [mul(pow(x, mul(-1, y)), z), {}, '<apply><divide/><ci>z</ci><apply><power/><ci>x</ci><ci>y</ci></apply></apply>'],
      [new Float(fromStr('1.5', 103), 103), {}, '<cn>1.5</cn>'],
      [sj.sub(x, y), {}, '<apply><minus/><ci>x</ci><ci>y</ci></apply>'],
      [sj.add(sj.sub(x, y), z), {}, '<apply><plus/><apply><minus/><ci>x</ci><ci>y</ci></apply><ci>z</ci></apply>'],
      [sj.sub(sj.add(x, y), z), {}, '<apply><plus/><ci>x</ci><apply><minus/><ci>y</ci><ci>z</ci></apply></apply>'],
      [mul(-1, x), {}, '<apply><minus/><ci>x</ci></apply>'],
      [mul(-2, x), {}, '<apply><minus/><apply><times/><cn>2</cn><ci>x</ci></apply></apply>'],
      [R(-1, 2), P, '<mrow><mo>-</mo><mfrac><mn>1</mn><mn>2</mn></mfrac></mrow>'],
      [S.Catalan, P, '<mrow><mi>catalan</mi><mrow><mo>(</mo><mo>)</mo></mrow></mrow>'],
      [S.false, P, '<mi>False</mi>'],
      [sj.Piecewise([x, sj.Lt(x, 0)], [1, true]), P, '<mrow><mi>piecewise</mi><mrow><mo>(</mo><mrow><mo>(</mo><mi>x</mi><mo>,</mo><mrow><mi>x</mi><mo><</mo><mn>0</mn></mrow><mo>)</mo></mrow><mo>,</mo><mrow><mo>(</mo><mn>1</mn><mo>,</mo><mi>True</mi><mo>)</mo></mrow><mo>)</mo></mrow></mrow>'],
      [new Float(1.5), P, '<mn>1.5</mn>'],
      [sj.sub(x, y), P, '<mrow><mi>x</mi><mo>-</mo><mi>y</mi></mrow>'],
      [sj.sqrt(x), P, '<msqrt><mi>x</mi></msqrt>'],
      [pow(x, R(1, 3)), P, '<mroot><mi>x</mi><mn>3</mn></mroot>'],
      [pow(x, R(-1, 2)), P, '<mfrac><mn>1</mn><msqrt><mi>x</mi></msqrt></mfrac>'],
      [pow(x, -1), P, '<mfrac><mn>1</mn><mi>x</mi></mfrac>'],
      [sj.Not(x), P, '<mrow><mo>&#xAC;</mo><mi>x</mi></mrow>'],
      [new BoolOp('ITE', [x, y, z]), P, '<mrow><mi>ite</mi><mrow><mo>(</mo><mi>x</mi><mo>,</mo><mi>y</mi><mo>,</mo><mi>z</mi><mo>)</mo></mrow></mrow>'],
      [sj.ITE(x, y, z), P, '<mrow><mi>ite</mi><mrow><mo>(</mo><mi>x</mi><mo>,</mo><mi>y</mi><mo>,</mo><mi>z</mi><mo>)</mo></mrow></mrow>'],
      [sj.And(sj.Or(x, y), z), P, '<mrow><mi>z</mi><mo>&#x2227;</mo><mrow><mo>(</mo><mrow><mi>x</mi><mo>&#x2228;</mo><mi>y</mi></mrow><mo>)</mo></mrow></mrow>'],
      [sj.Nand(x, y), P, '<mrow><mo>&#xAC;</mo><mrow><mo>(</mo><mrow><mi>x</mi><mo>&#x2227;</mo><mi>y</mi></mrow><mo>)</mo></mrow></mrow>'],
      [sj.And(x, sj.Not(y)), P, '<mrow><mi>x</mi><mo>&#x2227;</mo><mrow><mo>&#xAC;</mo><mi>y</mi></mrow></mrow>'],
      [Sets.Ropen(0, 1), P, '<mrow><mo>[</mo><mn>0</mn><mo>,</mo><mn>1</mn><mo>)</mo></mrow>'],
      [new Sets.ConditionSet(x, sj.Gt(x, 0), Sets.Reals), P, '<mrow><mi>conditionset</mi><mrow><mo>(</mo><mi>x</mi><mo>,</mo><mrow><mi>x</mi><mo>></mo><mn>0</mn></mrow><mo>,</mo><mi mathvariant="normal">&#x211D;</mi><mo>)</mo></mrow></mrow>'],
      [mul(-1, x), P, '<mrow><mo>-</mo><mi>x</mi></mrow>'],
      [mul(x, pow(y, -1)), P, '<mrow><mfrac><mi>x</mi><mi>y</mi></mfrac></mrow>'],
      [mul(pow(x, 2), pow(y, -1), z), P, '<mrow><mfrac><mrow><msup><mi>x</mi><mn>2</mn></msup><mo>&InvisibleTimes;</mo><mi>z</mi></mrow><mi>y</mi></mfrac></mrow>'],
      [mul(2, x, R(1, 3)), P, '<mrow><mfrac><mrow><mn>2</mn><mo>&InvisibleTimes;</mo><mi>x</mi></mrow><mn>3</mn></mfrac></mrow>'],
    ];
    for (const [e, o, expected] of cases) expect(mathml(e, o)).toBe(expected);
  });
  it('a Range with unknown elements prints like any node (SymPy raises an error)', () => {
    const r = Sets.Range.of(n, sj.symbol('m', { integer: true }));
    expect(mathml(r, { printer: 'presentation' }).startsWith('<mrow><mi>range</mi>')).toBe(true);
  });
  it('the printer classes', () => {
    expect(new MathMLContentPrinter().doprint(x)).toBe('<ci>x</ci>');
    expect(new MathMLPresentationPrinter({ mulSymbol: 'dot' }).doprint(mul(2, x))).toBe('<mrow><mn>2</mn><mo>&#xB7;</mo><mi>x</mi></mrow>');
  });
  it('the XML elements', () => {
    const e = new MathMLElement('msup').append(new MathMLElement('mi').append('x'), '&#x2020;').set('a', 'b');
    expect(e.toxml()).toBe('<msup a="b"><mi>x</mi>&#x2020;</msup>');
    expect(e.toprettyxml()).toBe('<msup a="b">\n\t<mi>x</mi>\n\t&#x2020;\n</msup>\n');
    expect(new MathMLElement('mrow').append('', new MathMLElement('mi').append('y')).toprettyxml()).toBe('<mrow>\n\t<mi>y</mi>\n</mrow>\n');
  });
  it('nodes printed with their class name (SymPy _print_Basic and _print_Function)', () => {
    class Node extends sj.ExtensionExpr {
      constructor(args: readonly Expr[]) {
        super('Node', args);
      }
      withArgs(args: readonly Expr[]): Expr {
        return new Node(args);
      }
    }
    expect(mathml(new Node([x]))).toBe('<node><ci>x</ci></node>');
    expect(mathml(new Node([x]), { printer: 'presentation' })).toBe('<mrow><mi>node</mi><mrow><mo>(</mo><mi>x</mi><mo>)</mo></mrow></mrow>');
    expect(mathml(sj.Mod(x, 2), { printer: 'presentation' })).toBe('<mrow><mi>mod</mi><mrow><mo>(</mo><mi>x</mi><mo>,</mo><mn>2</mn><mo>)</mo></mrow></mrow>');
    expect(mathml(sj.sin(x), { printer: 'presentation' })).toBe('<mrow><mi>sin</mi><mrow><mo>(</mo><mi>x</mi><mo>)</mo></mrow></mrow>');
  });
});
