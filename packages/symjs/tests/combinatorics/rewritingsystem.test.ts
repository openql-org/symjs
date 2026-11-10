// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Rewriting systems of finitely presented groups; expected values from SymPy 1.14.0.
import { describe, expect, it } from 'vitest';
import { FpGroup, FreeGroup, FreeGroupElement, RewritingRulesExceeded, RewritingSystem, State, StateMachine, freeGroup } from '../../src/combinatorics';

const [F, x, y] = freeGroup('x, y') as [FreeGroup, FreeGroupElement, FreeGroupElement];
const S4 = (): FpGroup => new FpGroup(F, [x.pow(2), y.pow(3), x.mul(y).pow(4)]);

describe('RewritingSystem', () => {
  it('the initial rules and confluence', () => {
    const R = S4().rewritingSystem;
    expect(R.rules.size).toBe(13);
    expect(R.isConfluent).toBe(false);
    expect(R.alphabet.map(String)).toEqual(['x', 'y']);
    expect(String(R.reductionAutomaton)).toBe('Reduction automaton for <fp group on the generators (x, y)>');
  });
  it('Knuth-Bendix completion with redundancy removal', () => {
    const R = S4().rewritingSystem;
    R.tidyint = 1;
    expect(R.makeConfluent()).toBe(true);
    expect(R.rules.size).toBe(9);
    expect(R.isConfluent).toBe(true);
    expect(String(R.reduce(x.mul(y).pow(3)))).toBe('y**-1*x**-1');
    expect(String(R.reduceUsingAutomaton(x.mul(y).pow(3)))).toBe('y**-1*x');
    expect([...R.addRule(x.pow(5), y, true)].map(String).sort()).toEqual(['x**-1*y*x**-2', 'x**-2*y*x**-1', 'x**-3*y', 'x**3', 'x**4', 'x*y**-1*x', 'y**-1*x**2', 'y**-1*x**3', 'y*x**-2', 'y*x**-3']);
    expect(R.addRule(x, x).size).toBe(0);
    // a repeated rule is cached
    expect(R.addRule(x.pow(5), y, true).size).toBe(0);
  });
  it('redundancy removal after every new rule', () => {
    const R = S4().rewritingSystem;
    R.tidyint = 0;
    expect(R.makeConfluent()).toBe(true);
    expect(R.rules.size).toBe(9);
  });
  it('the maximum number of rules', () => {
    const R = S4().rewritingSystem;
    R.setMax(10);
    expect(R.makeConfluent()).toBe(false);
    expect(R.isConfluent).toBe(false);
    expect(R.makeConfluent()).toBe(false);
    R.setMax(100000);
    expect(R.makeConfluent()).toBe(true);
    expect(R.rules.size).toBe(9);
    R.setMax(5);
    expect(() => R.addRule(x.pow(7), y.pow(2))).toThrow(RewritingRulesExceeded);
  });
  it('the rules cache holds the last 50 rules', () => {
    const R = new FpGroup(F, []).rewritingSystem;
    for (let i = 1; i <= 52; i++) R.addRule(x.pow(i + 3), y.pow(i), true);
    expect(R.addRule(x.pow(4), y, true).size).toBeGreaterThan(0);
    expect(R.addRule(x.pow(55), y.pow(52), true).size).toBe(0);
  });
  it('letters outside every rule (SymPy raises KeyError)', () => {
    const R = new FpGroup(F, [x.pow(2)]).rewritingSystem;
    expect(R.rules.size).toBe(3);
    expect(String(R.reduceUsingAutomaton(x.pow(3)))).toBe('x**-1');
    expect(String(R.reduceUsingAutomaton(y.mul(x.pow(3)).mul(y)))).toBe('y*x**-1*y');
    R.addRule(y.pow(3), F.identity);
    expect(String(R.reduceUsingAutomaton(y.pow(4).mul(x.pow(2))))).toBe('y');
  });
  it('an explicit system and state machine', () => {
    const R = new RewritingSystem(new FpGroup(F, [x.pow(3)]));
    expect([...R.rules].map(([k, v]) => `${String(k)} -> ${String(v)}`)).toEqual(['x**-2 -> x', 'x**2 -> x**-1']);
    const M = new StateMachine('M', [x, y]);
    M.addState(x, 'accept');
    expect([...M.states.keys()].map(String)).toEqual(['start', 'x']);
    const s = new State(y, M, 'dead', x);
    s.addTransition(x, 'start');
    expect(s.stateType).toBe('d');
    expect(s.transitions.get(x.key)).toBe('start');
    expect(String(M)).toBe('M');
  });
});
