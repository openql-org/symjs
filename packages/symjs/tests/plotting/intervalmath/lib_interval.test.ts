// Generated from SymPy 1.14 intervalmath tests (BSD-3-Clause).
import { expect, it } from 'vitest';
import { symbol } from '../../../src/core';
import { intervalmath as li } from '../../../src/plotting';
import { iv, membership, op, unary, bool, item, lengthOf, iterator, nextItem, range, hashInterval, intervalLambda } from '../interval-reference-helpers';
const { Abs, acos, acosh, And, asin, asinh, atan, atanh, ceil, cos, cosh, exp, floor, imax, imin, log, log10, Or, sin, sinh, sqrt, tan, tanh } = li;

it("test_interval_pow", () => {
let a: any = op("eq", op("pow", 2, iv(1, 2)), iv(2, 4));
expect(bool(op("eq", a, [true, true])), "test_interval_functions.py:18").toBe(true);
a = op("eq", op("pow", iv(1, 2), iv(1, 2)), iv(1, 4));
expect(bool(op("eq", a, [true, true])), "test_interval_functions.py:20").toBe(true);
a = op("pow", iv(unary("USub", 1), 1), iv(0.5, 2));
expect(bool(op("is", a.isValid, 'unknown')), "test_interval_functions.py:22").toBe(true);
a = op("pow", iv(unary("USub", 2), unary("USub", 1)), iv(1, 2));
expect(bool(op("is", a.isValid, false)), "test_interval_functions.py:24").toBe(true);
a = op("pow", iv(unary("USub", 2), unary("USub", 1)), op("div", 1.0, 2));
expect(bool(op("is", a.isValid, false)), "test_interval_functions.py:26").toBe(true);
a = op("pow", iv(unary("USub", 1), 1), op("div", 1.0, 2));
expect(bool(op("is", a.isValid, 'unknown')), "test_interval_functions.py:28").toBe(true);
a = op("eq", op("pow", iv(unary("USub", 1), 1), op("div", 1.0, 3)), iv(unary("USub", 1), 1));
expect(bool(op("eq", a, [true, true])), "test_interval_functions.py:30").toBe(true);
a = op("eq", op("pow", iv(unary("USub", 1), 1), 2), iv(0, 1));
expect(bool(op("eq", a, [true, true])), "test_interval_functions.py:32").toBe(true);
a = op("eq", op("pow", iv(unary("USub", 1), 1), op("div", 1.0, 29)), iv(unary("USub", 1), 1));
expect(bool(op("eq", a, [true, true])), "test_interval_functions.py:34").toBe(true);
a = op("eq", unary("USub", op("pow", 2, iv(1, 1))), iv(unary("USub", 2), unary("USub", 2)));
expect(bool(op("eq", a, [true, true])), "test_interval_functions.py:36").toBe(true);
a = op("pow", iv(1, 2, {isValid: false}), 2);
expect(bool(op("is", a.isValid, false)), "test_interval_functions.py:39").toBe(true);
a = op("pow", unary("USub", 3), iv(1, 2));
expect(bool(op("is", a.isValid, false)), "test_interval_functions.py:42").toBe(true);
a = op("pow", unary("USub", 4), iv(0.5, 0.5));
expect(bool(op("is", a.isValid, false)), "test_interval_functions.py:44").toBe(true);
expect(bool(op("eq", op("eq", op("pow", unary("USub", 3), iv(1, 1)), iv(unary("USub", 3), unary("USub", 3))), [true, true])), "test_interval_functions.py:45").toBe(true);
a = op("pow", iv(8, 64), op("div", 2.0, 3));
expect(bool(op("lt", Math.abs(op("sub", a.start, 4)), 1e-10)), "test_interval_functions.py:48").toBe(true);
expect(bool(op("lt", Math.abs(op("sub", a.end, 16)), 1e-10)), "test_interval_functions.py:49").toBe(true);
a = op("pow", iv(unary("USub", 8), 64), op("div", 2.0, 3));
expect(bool(op("lt", Math.abs(op("sub", a.start, 0)), 1e-10)), "test_interval_functions.py:51").toBe(true);
expect(bool(op("lt", Math.abs(op("sub", a.end, 16)), 1e-10)), "test_interval_functions.py:52").toBe(true);
});

it("test_exp", () => {
let a: any = exp(iv(unary("USub", Infinity), 0));
expect(bool(op("eq", a.start, Math.exp(unary("USub", Infinity)))), "test_interval_functions.py:57").toBe(true);
expect(bool(op("eq", a.end, Math.exp(0))), "test_interval_functions.py:58").toBe(true);
a = exp(iv(1, 2));
expect(bool(op("eq", a.start, Math.exp(1))), "test_interval_functions.py:60").toBe(true);
expect(bool(op("eq", a.end, Math.exp(2))), "test_interval_functions.py:61").toBe(true);
a = exp(1);
expect(bool(op("eq", a.start, Math.exp(1))), "test_interval_functions.py:63").toBe(true);
expect(bool(op("eq", a.end, Math.exp(1))), "test_interval_functions.py:64").toBe(true);
});

it("test_log", () => {
let a: any = log(iv(1, 2));
expect(bool(op("eq", a.start, 0)), "test_interval_functions.py:69").toBe(true);
expect(bool(op("eq", a.end, Math.log(2))), "test_interval_functions.py:70").toBe(true);
a = log(iv(unary("USub", 1), 1));
expect(bool(op("is", a.isValid, 'unknown')), "test_interval_functions.py:72").toBe(true);
a = log(iv(unary("USub", 3), unary("USub", 1)));
expect(bool(op("is", a.isValid, false)), "test_interval_functions.py:74").toBe(true);
a = log(unary("USub", 3));
expect(bool(op("is", a.isValid, false)), "test_interval_functions.py:76").toBe(true);
a = log(2);
expect(bool(op("eq", a.start, Math.log(2))), "test_interval_functions.py:78").toBe(true);
expect(bool(op("eq", a.end, Math.log(2))), "test_interval_functions.py:79").toBe(true);
});

it("test_log10", () => {
let a: any = log10(iv(1, 2));
expect(bool(op("eq", a.start, 0)), "test_interval_functions.py:84").toBe(true);
expect(bool(op("eq", a.end, Math.log10(2))), "test_interval_functions.py:85").toBe(true);
a = log10(iv(unary("USub", 1), 1));
expect(bool(op("is", a.isValid, 'unknown')), "test_interval_functions.py:87").toBe(true);
a = log10(iv(unary("USub", 3), unary("USub", 1)));
expect(bool(op("is", a.isValid, false)), "test_interval_functions.py:89").toBe(true);
a = log10(unary("USub", 3));
expect(bool(op("is", a.isValid, false)), "test_interval_functions.py:91").toBe(true);
a = log10(2);
expect(bool(op("eq", a.start, Math.log10(2))), "test_interval_functions.py:93").toBe(true);
expect(bool(op("eq", a.end, Math.log10(2))), "test_interval_functions.py:94").toBe(true);
});

it("test_atan", () => {
let a: any = atan(iv(0, 1));
expect(bool(op("eq", a.start, Math.atan(0))), "test_interval_functions.py:99").toBe(true);
expect(bool(op("eq", a.end, Math.atan(1))), "test_interval_functions.py:100").toBe(true);
a = atan(1);
expect(bool(op("eq", a.start, Math.atan(1))), "test_interval_functions.py:102").toBe(true);
expect(bool(op("eq", a.end, Math.atan(1))), "test_interval_functions.py:103").toBe(true);
});

it("test_sin", () => {
let a: any = sin(iv(0, op("div", Math.PI, 4)));
expect(bool(op("eq", a.start, Math.sin(0))), "test_interval_functions.py:108").toBe(true);
expect(bool(op("eq", a.end, Math.sin(op("div", Math.PI, 4)))), "test_interval_functions.py:109").toBe(true);
a = sin(iv(op("div", unary("USub", Math.PI), 4), op("div", Math.PI, 4)));
expect(bool(op("eq", a.start, Math.sin(op("div", unary("USub", Math.PI), 4)))), "test_interval_functions.py:112").toBe(true);
expect(bool(op("eq", a.end, Math.sin(op("div", Math.PI, 4)))), "test_interval_functions.py:113").toBe(true);
a = sin(iv(op("div", Math.PI, 4), op("div", op("mul", 3, Math.PI), 4)));
expect(bool(op("eq", a.start, Math.sin(op("div", Math.PI, 4)))), "test_interval_functions.py:116").toBe(true);
expect(bool(op("eq", a.end, 1)), "test_interval_functions.py:117").toBe(true);
a = sin(iv(op("div", op("mul", 7, Math.PI), 6), op("div", op("mul", 7, Math.PI), 4)));
expect(bool(op("eq", a.start, unary("USub", 1))), "test_interval_functions.py:120").toBe(true);
expect(bool(op("eq", a.end, Math.sin(op("div", op("mul", 7, Math.PI), 6)))), "test_interval_functions.py:121").toBe(true);
a = sin(iv(0, op("mul", 3, Math.PI)));
expect(bool(op("eq", a.start, unary("USub", 1))), "test_interval_functions.py:124").toBe(true);
expect(bool(op("eq", a.end, 1)), "test_interval_functions.py:125").toBe(true);
a = sin(iv(op("div", Math.PI, 3), op("div", op("mul", 7, Math.PI), 4)));
expect(bool(op("eq", a.start, unary("USub", 1))), "test_interval_functions.py:128").toBe(true);
expect(bool(op("eq", a.end, 1)), "test_interval_functions.py:129").toBe(true);
a = sin(op("div", Math.PI, 4));
expect(bool(op("eq", a.start, Math.sin(op("div", Math.PI, 4)))), "test_interval_functions.py:132").toBe(true);
expect(bool(op("eq", a.end, Math.sin(op("div", Math.PI, 4)))), "test_interval_functions.py:133").toBe(true);
a = sin(iv(1, 2, {isValid: false}));
expect(bool(op("is", a.isValid, false)), "test_interval_functions.py:136").toBe(true);
});

it("test_cos", () => {
let a: any = cos(iv(0, op("div", Math.PI, 4)));
expect(bool(op("eq", a.start, Math.cos(op("div", Math.PI, 4)))), "test_interval_functions.py:141").toBe(true);
expect(bool(op("eq", a.end, 1)), "test_interval_functions.py:142").toBe(true);
a = cos(iv(op("div", unary("USub", Math.PI), 4), op("div", Math.PI, 4)));
expect(bool(op("eq", a.start, Math.cos(op("div", unary("USub", Math.PI), 4)))), "test_interval_functions.py:145").toBe(true);
expect(bool(op("eq", a.end, 1)), "test_interval_functions.py:146").toBe(true);
a = cos(iv(op("div", Math.PI, 4), op("div", op("mul", 3, Math.PI), 4)));
expect(bool(op("eq", a.start, Math.cos(op("div", op("mul", 3, Math.PI), 4)))), "test_interval_functions.py:149").toBe(true);
expect(bool(op("eq", a.end, Math.cos(op("div", Math.PI, 4)))), "test_interval_functions.py:150").toBe(true);
a = cos(iv(op("div", op("mul", 3, Math.PI), 4), op("div", op("mul", 5, Math.PI), 4)));
expect(bool(op("eq", a.start, unary("USub", 1))), "test_interval_functions.py:153").toBe(true);
expect(bool(op("eq", a.end, Math.cos(op("div", op("mul", 3, Math.PI), 4)))), "test_interval_functions.py:154").toBe(true);
a = cos(iv(0, op("mul", 3, Math.PI)));
expect(bool(op("eq", a.start, unary("USub", 1))), "test_interval_functions.py:157").toBe(true);
expect(bool(op("eq", a.end, 1)), "test_interval_functions.py:158").toBe(true);
a = cos(iv(op("div", unary("USub", Math.PI), 3), op("div", op("mul", 5, Math.PI), 4)));
expect(bool(op("eq", a.start, unary("USub", 1))), "test_interval_functions.py:161").toBe(true);
expect(bool(op("eq", a.end, 1)), "test_interval_functions.py:162").toBe(true);
a = cos(iv(1, 2, {isValid: false}));
expect(bool(op("is", a.isValid, false)), "test_interval_functions.py:165").toBe(true);
});

it("test_tan", () => {
let a: any = tan(iv(0, op("div", Math.PI, 4)));
expect(bool(op("eq", a.start, 0)), "test_interval_functions.py:170").toBe(true);
expect(bool(op("eq", a.end, op("div", Math.sin(op("div", Math.PI, 4)), Math.cos(op("div", Math.PI, 4))))), "test_interval_functions.py:172").toBe(true);
a = tan(iv(op("div", Math.PI, 4), op("div", op("mul", 3, Math.PI), 4)));
expect(bool(op("is", a.isValid, 'unknown')), "test_interval_functions.py:176").toBe(true);
});

it("test_sqrt", () => {
let a: any = sqrt(iv(1, 4));
expect(bool(op("eq", a.start, 1)), "test_interval_functions.py:181").toBe(true);
expect(bool(op("eq", a.end, 2)), "test_interval_functions.py:182").toBe(true);
a = sqrt(iv(0.01, 1));
expect(bool(op("eq", a.start, Math.sqrt(0.01))), "test_interval_functions.py:185").toBe(true);
expect(bool(op("eq", a.end, 1)), "test_interval_functions.py:186").toBe(true);
a = sqrt(iv(unary("USub", 1), 1));
expect(bool(op("is", a.isValid, 'unknown')), "test_interval_functions.py:189").toBe(true);
a = sqrt(iv(unary("USub", 3), unary("USub", 1)));
expect(bool(op("is", a.isValid, false)), "test_interval_functions.py:192").toBe(true);
a = sqrt(4);
expect(bool(op("eq", op("eq", a, iv(2, 2)), [true, true])), "test_interval_functions.py:195").toBe(true);
a = sqrt(unary("USub", 3));
expect(bool(op("is", a.isValid, false)), "test_interval_functions.py:198").toBe(true);
});

it("test_imin", () => {
let a: any = imin(iv(1, 3), iv(2, 5), iv(unary("USub", 1), 3));
expect(bool(op("eq", a.start, unary("USub", 1))), "test_interval_functions.py:203").toBe(true);
expect(bool(op("eq", a.end, 3)), "test_interval_functions.py:204").toBe(true);
a = imin(unary("USub", 2), iv(1, 4));
expect(bool(op("eq", a.start, unary("USub", 2))), "test_interval_functions.py:207").toBe(true);
expect(bool(op("eq", a.end, unary("USub", 2))), "test_interval_functions.py:208").toBe(true);
a = imin(5, iv(3, 4), iv(unary("USub", 2), 2, {isValid: false}));
expect(bool(op("eq", a.start, 3)), "test_interval_functions.py:211").toBe(true);
expect(bool(op("eq", a.end, 4)), "test_interval_functions.py:212").toBe(true);
});

it("test_imax", () => {
let a: any = imax(iv(unary("USub", 2), 2), iv(2, 7), iv(unary("USub", 3), 9));
expect(bool(op("eq", a.start, 2)), "test_interval_functions.py:217").toBe(true);
expect(bool(op("eq", a.end, 9)), "test_interval_functions.py:218").toBe(true);
a = imax(8, iv(1, 4));
expect(bool(op("eq", a.start, 8)), "test_interval_functions.py:221").toBe(true);
expect(bool(op("eq", a.end, 8)), "test_interval_functions.py:222").toBe(true);
a = imax(iv(1, 2), iv(3, 4), iv(unary("USub", 2), 2, {isValid: false}));
expect(bool(op("eq", a.start, 3)), "test_interval_functions.py:225").toBe(true);
expect(bool(op("eq", a.end, 4)), "test_interval_functions.py:226").toBe(true);
});

it("test_sinh", () => {
let a: any = sinh(iv(unary("USub", 1), 1));
expect(bool(op("eq", a.start, Math.sinh(unary("USub", 1)))), "test_interval_functions.py:231").toBe(true);
expect(bool(op("eq", a.end, Math.sinh(1))), "test_interval_functions.py:232").toBe(true);
a = sinh(1);
expect(bool(op("eq", a.start, Math.sinh(1))), "test_interval_functions.py:235").toBe(true);
expect(bool(op("eq", a.end, Math.sinh(1))), "test_interval_functions.py:236").toBe(true);
});

it("test_cosh", () => {
let a: any = cosh(iv(1, 2));
expect(bool(op("eq", a.start, Math.cosh(1))), "test_interval_functions.py:241").toBe(true);
expect(bool(op("eq", a.end, Math.cosh(2))), "test_interval_functions.py:242").toBe(true);
a = cosh(iv(unary("USub", 2), unary("USub", 1)));
expect(bool(op("eq", a.start, Math.cosh(unary("USub", 1)))), "test_interval_functions.py:244").toBe(true);
expect(bool(op("eq", a.end, Math.cosh(unary("USub", 2)))), "test_interval_functions.py:245").toBe(true);
a = cosh(iv(unary("USub", 2), 1));
expect(bool(op("eq", a.start, 1)), "test_interval_functions.py:248").toBe(true);
expect(bool(op("eq", a.end, Math.cosh(unary("USub", 2)))), "test_interval_functions.py:249").toBe(true);
a = cosh(1);
expect(bool(op("eq", a.start, Math.cosh(1))), "test_interval_functions.py:252").toBe(true);
expect(bool(op("eq", a.end, Math.cosh(1))), "test_interval_functions.py:253").toBe(true);
});

it("test_tanh", () => {
let a: any = tanh(iv(unary("USub", 3), 3));
expect(bool(op("eq", a.start, Math.tanh(unary("USub", 3)))), "test_interval_functions.py:258").toBe(true);
expect(bool(op("eq", a.end, Math.tanh(3))), "test_interval_functions.py:259").toBe(true);
a = tanh(3);
expect(bool(op("eq", a.start, Math.tanh(3))), "test_interval_functions.py:262").toBe(true);
expect(bool(op("eq", a.end, Math.tanh(3))), "test_interval_functions.py:263").toBe(true);
});

it("test_asin", () => {
let a: any = asin(iv(unary("USub", 0.5), 0.5));
expect(bool(op("eq", a.start, Math.asin(unary("USub", 0.5)))), "test_interval_functions.py:268").toBe(true);
expect(bool(op("eq", a.end, Math.asin(0.5))), "test_interval_functions.py:269").toBe(true);
a = asin(iv(unary("USub", 1.5), 1.5));
expect(bool(op("is", a.isValid, 'unknown')), "test_interval_functions.py:272").toBe(true);
a = asin(iv(unary("USub", 2), unary("USub", 1.5)));
expect(bool(op("is", a.isValid, false)), "test_interval_functions.py:274").toBe(true);
a = asin(iv(0, 2));
expect(bool(op("is", a.isValid, 'unknown')), "test_interval_functions.py:277").toBe(true);
a = asin(iv(2, 5));
expect(bool(op("is", a.isValid, false)), "test_interval_functions.py:280").toBe(true);
a = asin(0.5);
expect(bool(op("eq", a.start, Math.asin(0.5))), "test_interval_functions.py:283").toBe(true);
expect(bool(op("eq", a.end, Math.asin(0.5))), "test_interval_functions.py:284").toBe(true);
a = asin(1.5);
expect(bool(op("is", a.isValid, false)), "test_interval_functions.py:287").toBe(true);
});

it("test_acos", () => {
let a: any = acos(iv(unary("USub", 0.5), 0.5));
expect(bool(op("eq", a.start, Math.acos(0.5))), "test_interval_functions.py:292").toBe(true);
expect(bool(op("eq", a.end, Math.acos(unary("USub", 0.5)))), "test_interval_functions.py:293").toBe(true);
a = acos(iv(unary("USub", 1.5), 1.5));
expect(bool(op("is", a.isValid, 'unknown')), "test_interval_functions.py:296").toBe(true);
a = acos(iv(unary("USub", 2), unary("USub", 1.5)));
expect(bool(op("is", a.isValid, false)), "test_interval_functions.py:298").toBe(true);
a = acos(iv(0, 2));
expect(bool(op("is", a.isValid, 'unknown')), "test_interval_functions.py:301").toBe(true);
a = acos(iv(2, 5));
expect(bool(op("is", a.isValid, false)), "test_interval_functions.py:304").toBe(true);
a = acos(0.5);
expect(bool(op("eq", a.start, Math.acos(0.5))), "test_interval_functions.py:307").toBe(true);
expect(bool(op("eq", a.end, Math.acos(0.5))), "test_interval_functions.py:308").toBe(true);
a = acos(1.5);
expect(bool(op("is", a.isValid, false)), "test_interval_functions.py:311").toBe(true);
});

it("test_ceil", () => {
let a: any = ceil(iv(0.2, 0.5));
expect(bool(op("eq", a.start, 1)), "test_interval_functions.py:316").toBe(true);
expect(bool(op("eq", a.end, 1)), "test_interval_functions.py:317").toBe(true);
a = ceil(iv(0.5, 1.5));
expect(bool(op("eq", a.start, 1)), "test_interval_functions.py:320").toBe(true);
expect(bool(op("eq", a.end, 2)), "test_interval_functions.py:321").toBe(true);
expect(bool(op("is", a.isValid, 'unknown')), "test_interval_functions.py:322").toBe(true);
a = ceil(iv(unary("USub", 5), 5));
expect(bool(op("is", a.isValid, 'unknown')), "test_interval_functions.py:325").toBe(true);
a = ceil(5.4);
expect(bool(op("eq", a.start, 6)), "test_interval_functions.py:328").toBe(true);
expect(bool(op("eq", a.end, 6)), "test_interval_functions.py:329").toBe(true);
});

it("test_floor", () => {
let a: any = floor(iv(0.2, 0.5));
expect(bool(op("eq", a.start, 0)), "test_interval_functions.py:334").toBe(true);
expect(bool(op("eq", a.end, 0)), "test_interval_functions.py:335").toBe(true);
a = floor(iv(0.5, 1.5));
expect(bool(op("eq", a.start, 0)), "test_interval_functions.py:338").toBe(true);
expect(bool(op("eq", a.end, 1)), "test_interval_functions.py:339").toBe(true);
expect(bool(op("is", a.isValid, 'unknown')), "test_interval_functions.py:340").toBe(true);
a = floor(iv(unary("USub", 5), 5));
expect(bool(op("is", a.isValid, 'unknown')), "test_interval_functions.py:343").toBe(true);
a = floor(5.4);
expect(bool(op("eq", a.start, 5)), "test_interval_functions.py:346").toBe(true);
expect(bool(op("eq", a.end, 5)), "test_interval_functions.py:347").toBe(true);
});

it("test_asinh", () => {
let a: any = asinh(iv(1, 2));
expect(bool(op("eq", a.start, Math.asinh(1))), "test_interval_functions.py:352").toBe(true);
expect(bool(op("eq", a.end, Math.asinh(2))), "test_interval_functions.py:353").toBe(true);
a = asinh(0.5);
expect(bool(op("eq", a.start, Math.asinh(0.5))), "test_interval_functions.py:356").toBe(true);
expect(bool(op("eq", a.end, Math.asinh(0.5))), "test_interval_functions.py:357").toBe(true);
});

it("test_acosh", () => {
let a: any = acosh(iv(3, 5));
expect(bool(op("eq", a.start, Math.acosh(3))), "test_interval_functions.py:362").toBe(true);
expect(bool(op("eq", a.end, Math.acosh(5))), "test_interval_functions.py:363").toBe(true);
a = acosh(iv(0, 3));
expect(bool(op("is", a.isValid, 'unknown')), "test_interval_functions.py:366").toBe(true);
a = acosh(iv(unary("USub", 3), 0.5));
expect(bool(op("is", a.isValid, false)), "test_interval_functions.py:368").toBe(true);
a = acosh(0.5);
expect(bool(op("is", a.isValid, false)), "test_interval_functions.py:371").toBe(true);
a = acosh(2);
expect(bool(op("eq", a.start, Math.acosh(2))), "test_interval_functions.py:374").toBe(true);
expect(bool(op("eq", a.end, Math.acosh(2))), "test_interval_functions.py:375").toBe(true);
});

it("test_atanh", () => {
let a: any = atanh(iv(unary("USub", 0.5), 0.5));
expect(bool(op("eq", a.start, Math.atanh(unary("USub", 0.5)))), "test_interval_functions.py:380").toBe(true);
expect(bool(op("eq", a.end, Math.atanh(0.5))), "test_interval_functions.py:381").toBe(true);
a = atanh(iv(0, 3));
expect(bool(op("is", a.isValid, 'unknown')), "test_interval_functions.py:384").toBe(true);
a = atanh(iv(unary("USub", 3), unary("USub", 2)));
expect(bool(op("is", a.isValid, false)), "test_interval_functions.py:387").toBe(true);
a = atanh(0.5);
expect(bool(op("eq", a.start, Math.atanh(0.5))), "test_interval_functions.py:390").toBe(true);
expect(bool(op("eq", a.end, Math.atanh(0.5))), "test_interval_functions.py:391").toBe(true);
a = atanh(1.5);
expect(bool(op("is", a.isValid, false)), "test_interval_functions.py:394").toBe(true);
});

it("test_Abs", () => {
expect(bool(op("eq", op("eq", Abs(iv(unary("USub", 0.5), 0.5)), iv(0, 0.5)), [true, true])), "test_interval_functions.py:398").toBe(true);
expect(bool(op("eq", op("eq", Abs(iv(unary("USub", 3), unary("USub", 2))), iv(2, 3)), [true, true])), "test_interval_functions.py:399").toBe(true);
expect(bool(op("eq", op("eq", Abs(unary("USub", 3)), iv(3, 3)), [true, true])), "test_interval_functions.py:400").toBe(true);
});

it("test_And", () => {
let args: any = [[true, true], [true, false], [true, 'unknown']];
expect(bool(op("eq", And(...args), [true, false])), "test_interval_functions.py:405").toBe(true);
args = [[false, true], ['unknown', 'unknown'], [true, true]];
expect(bool(op("eq", And(...args), [false, 'unknown'])), "test_interval_functions.py:408").toBe(true);
});

it("test_Or", () => {
let args: any = [[true, true], [true, false], [false, 'unknown']];
expect(bool(op("eq", Or(...args), [true, true])), "test_interval_functions.py:413").toBe(true);
args = [['unknown', 'unknown'], [false, 'unknown'], [false, false]];
expect(bool(op("eq", Or(...args), ['unknown', 'unknown'])), "test_interval_functions.py:415").toBe(true);
});

void [symbol, iv, membership, op, unary, bool, item, lengthOf, iterator, nextItem, range, hashInterval, intervalLambda, Abs, acos, acosh, And, asin, asinh, atan, atanh, ceil, cos, cosh, exp, floor, imax, imin, log, log10, Or, sin, sinh, sqrt, tan, tanh];
