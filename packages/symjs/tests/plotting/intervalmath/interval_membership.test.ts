// Generated from SymPy 1.14 intervalmath tests (BSD-3-Clause).
import { expect, it } from 'vitest';
import { symbol } from '../../../src/core';
import { intervalmath as li } from '../../../src/plotting';
import { iv, membership, op, unary, bool, item, lengthOf, iterator, nextItem, range, hashInterval, intervalLambda } from '../interval-reference-helpers';
const { Abs, acos, acosh, And, asin, asinh, atan, atanh, ceil, cos, cosh, exp, floor, imax, imin, log, log10, Or, sin, sinh, sqrt, tan, tanh } = li;

it("test_creation", () => {
expect(bool(membership(true, true)), "test_interval_membership.py:9").toBe(true);
expect(() => membership(true)).toThrow();
expect(() => membership(true, true, true)).toThrow();
});

it("test_getitem", () => {
let a: any = membership(true, false);
expect(bool(op("is", item(a, 0), true)), "test_interval_membership.py:16").toBe(true);
expect(bool(op("is", item(a, 1), false)), "test_interval_membership.py:17").toBe(true);
expect(() => item(a, 2)).toThrow();
});

it("test_str", () => {
let a: any = membership(true, false);
expect(bool(op("eq", String(a), "intervalMembership(True, False)")), "test_interval_membership.py:23").toBe(true);
expect(bool(op("eq", String(a), "intervalMembership(True, False)")), "test_interval_membership.py:24").toBe(true);
});

it("test_equivalence", () => {
let a: any = membership(true, true);
let b: any = membership(true, false);
expect(bool(op("is", op("eq", a, b), false)), "test_interval_membership.py:30").toBe(true);
expect(bool(op("is", op("ne", a, b), true)), "test_interval_membership.py:31").toBe(true);
a = membership(true, false);
b = membership(true, false);
expect(bool(op("is", op("eq", a, b), true)), "test_interval_membership.py:35").toBe(true);
expect(bool(op("is", op("ne", a, b), false)), "test_interval_membership.py:36").toBe(true);
});

it("test_not", () => {
let x: any = symbol("x");
let r1: any = op("gt", x, unary("USub", 1));
let r2: any = op("le", x, unary("USub", 1));
let i: any = iv;
let f1: any = intervalLambda([x], r1);
let f2: any = intervalLambda([x], r2);
let tt: any = i(unary("USub", 0.1), 0.1, {isValid: true});
let tn: any = i(unary("USub", 0.1), 0.1, {isValid: 'unknown'});
let tf: any = i(unary("USub", 0.1), 0.1, {isValid: false});
expect(bool(op("eq", f1(tt), unary("Invert", f2(tt)))), "test_interval_membership.py:54").toBe(true);
expect(bool(op("eq", f1(tn), unary("Invert", f2(tn)))), "test_interval_membership.py:55").toBe(true);
expect(bool(op("eq", f1(tf), unary("Invert", f2(tf)))), "test_interval_membership.py:56").toBe(true);
let nt: any = i(0.9, 1.1, {isValid: true});
let nn: any = i(0.9, 1.1, {isValid: 'unknown'});
let nf: any = i(0.9, 1.1, {isValid: false});
expect(bool(op("eq", f1(nt), unary("Invert", f2(nt)))), "test_interval_membership.py:62").toBe(true);
expect(bool(op("eq", f1(nn), unary("Invert", f2(nn)))), "test_interval_membership.py:63").toBe(true);
expect(bool(op("eq", f1(nf), unary("Invert", f2(nf)))), "test_interval_membership.py:64").toBe(true);
let ft: any = i(1.9, 2.1, {isValid: true});
let fn: any = i(1.9, 2.1, {isValid: 'unknown'});
let ff: any = i(1.9, 2.1, {isValid: false});
expect(bool(op("eq", f1(ft), unary("Invert", f2(ft)))), "test_interval_membership.py:70").toBe(true);
expect(bool(op("eq", f1(fn), unary("Invert", f2(fn)))), "test_interval_membership.py:71").toBe(true);
expect(bool(op("eq", f1(ff), unary("Invert", f2(ff)))), "test_interval_membership.py:72").toBe(true);
});

it("test_boolean", () => {
let s: any = [membership(false, false), membership('unknown', 'unknown'), membership(true, true)];
let a1: any = [membership(false, false), membership(false, false), membership(false, false), membership(false, false), membership('unknown', 'unknown'), membership('unknown', 'unknown'), membership(false, false), membership('unknown', 'unknown'), membership(true, true)];
let a1Iter: any = iterator(a1);
for (const i of range(lengthOf(s))) {
for (const j of range(lengthOf(s))) {
expect(bool(op("eq", op("and", item(s, i), item(s, j)), nextItem(a1Iter))), "test_interval_membership.py:99").toBe(true);
}
}
a1 = [membership(false, false), membership('unknown', false), membership(true, false), membership('unknown', false), membership('unknown', 'unknown'), membership(true, 'unknown'), membership(true, false), membership(true, 'unknown'), membership(true, true)];
a1Iter = iterator(a1);
for (const i of range(lengthOf(s))) {
for (const j of range(lengthOf(s))) {
expect(bool(op("eq", op("or", item(s, i), item(s, j)), nextItem(a1Iter))), "test_interval_membership.py:116").toBe(true);
}
}
a1 = [membership(false, false), membership('unknown', false), membership(true, false), membership('unknown', false), membership('unknown', 'unknown'), membership('unknown', 'unknown'), membership(true, false), membership('unknown', 'unknown'), membership(false, true)];
a1Iter = iterator(a1);
for (const i of range(lengthOf(s))) {
for (const j of range(lengthOf(s))) {
expect(bool(op("eq", op("xor", item(s, i), item(s, j)), nextItem(a1Iter))), "test_interval_membership.py:133").toBe(true);
}
}
a1 = [membership(true, false), membership('unknown', 'unknown'), membership(false, true)];
a1Iter = iterator(a1);
for (const i of range(lengthOf(s))) {
expect(bool(op("eq", unary("Invert", item(s, i)), nextItem(a1Iter))), "test_interval_membership.py:143").toBe(true);
}
});

it("test_boolean_errors", () => {
let a: any = membership(true, true);
expect(() => op("and", a, 1)).toThrow();
expect(() => op("or", a, 1)).toThrow();
expect(() => op("xor", a, 1)).toThrow();
});

void [symbol, iv, membership, op, unary, bool, item, lengthOf, iterator, nextItem, range, hashInterval, intervalLambda, Abs, acos, acosh, And, asin, asinh, atan, atanh, ceil, cos, cosh, exp, floor, imax, imin, log, log10, Or, sin, sinh, sqrt, tan, tanh];
