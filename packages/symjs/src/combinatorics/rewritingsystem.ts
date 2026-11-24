// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (sympy/combinatorics/rewritingsystem.py and
// rewritingsystem_fsm.py), Copyright (c) 2006-2023 SymPy Development Team,
// BSD 3-Clause License.

/**
 * @file SymPy sympy.combinatorics.rewritingsystem: the rewriting system of a
 * finitely presented group (reduction rules from the relators, completion by
 * the Knuth-Bendix procedure) and its reduction automaton
 * (rewritingsystem_fsm: State, StateMachine).
 */

import { at, defined, getOrThrow } from '../core/guard';
import type { FreeGroup, FreeGroupElement } from './freegroups';

/** The part of a finitely presented group a rewriting system uses. */
export interface RewritingGroup {
  /** The free group on the generators. */
  readonly freeGroup: FreeGroup;
  /** The generators in their defining order. */
  readonly generators: readonly FreeGroupElement[];
  /** The words imposed as defining relations. */
  readonly relators: readonly FreeGroupElement[];
  /**
   * Formats the object as plain text.
   * @returns The printable representation.
   */
  toString(): string;
}

/** The name of a state: a word, or 'start'. */
export type StateName = FreeGroupElement | 'start';
const nameKey = (n: StateName): string => (n === 'start' ? 'start' : `w:${n.key}`);

/**
 * A state of a reduction automaton, with its transitions on letters.
 * @see SymPy `sympy.combinatorics.rewritingsystem_fsm.State`
 */
export class State {
  /**
   * The identifying name.
   * @see SymPy `sympy.combinatorics.rewritingsystem_fsm.State.name`
   */
  readonly name: StateName;
  /**
   * The automaton containing this state.
   * @see SymPy `sympy.combinatorics.rewritingsystem_fsm.State.state_machine`
   */
  readonly stateMachine: StateMachine;
  /**
   * The state role, encoded as `s` for start, `a` for accept or `d` for a completed rule pattern.
   * @see SymPy `sympy.combinatorics.rewritingsystem_fsm.State.state_type`
   */
  stateType: string;
  /**
   * The right-hand side of the rule of a dead state.
   * @see SymPy `sympy.combinatorics.rewritingsystem_fsm.State.rh_rule`
   */
  rhRule: FreeGroupElement | undefined;
  /**
   * The next state for each letter (by the letter's key).
   * @see SymPy `sympy.combinatorics.rewritingsystem_fsm.State.transitions`
   */
  readonly transitions = new Map<string, StateName>();

  /**
   * Constructs a `State`.
   * @param name - The name used to identify the object.
   * @param stateMachine - The automaton containing the state.
   * @param stateType - The role of the state in recognizing a rewrite rule.
   * @param rhRule - The right-hand side of a recognized rule.
   */
  constructor(name: StateName, stateMachine: StateMachine, stateType: string, rhRule?: FreeGroupElement) {
    this.name = name;
    this.stateMachine = stateMachine;
    this.stateType = stateType.charAt(0);
    this.rhRule = rhRule;
  }

  /**
   * Add a transition from the current state to a new state.
   * @param letter - The generator or inverse generator.
   * @param state - The target state reached by the transition.
   * @see SymPy `sympy.combinatorics.rewritingsystem_fsm.State.add_transition`
   */
  addTransition(letter: FreeGroupElement, state: StateName): void {
    this.transitions.set(letter.key, state);
  }
}

/**
 * A finite state machine, starting with the state 'start'.
 * @see SymPy `sympy.combinatorics.rewritingsystem_fsm.StateMachine`
 */
export class StateMachine {
  /**
   * The identifying name.
   * @see SymPy `sympy.combinatorics.rewritingsystem_fsm.StateMachine.name`
   */
  readonly name: string;
  /**
   * The letters recognized by the automaton.
   * @see SymPy `sympy.combinatorics.rewritingsystem_fsm.StateMachine.automaton_alphabet`
   */
  readonly automatonAlphabet: readonly FreeGroupElement[];
  /** The states by name key. @internal */
  readonly stateMap = new Map<string, State>();

  /**
   * Constructs a `StateMachine`.
   * @param name - The name used to identify the object.
   * @param automatonAlphabet - The generator letters recognized by the automaton.
   */
  constructor(name: string, automatonAlphabet: readonly FreeGroupElement[]) {
    this.name = name;
    this.automatonAlphabet = automatonAlphabet;
    this.addState('start', 's');
  }

  /**
   * Instantiate a state object and stores it in the 'states' dictionary.
   * @param stateName - The label of the state.
   * @param stateType - The role of the state in recognizing a rewrite rule.
   * @param rhRule - The right-hand side of a recognized rule.
   * @see SymPy `sympy.combinatorics.rewritingsystem_fsm.StateMachine.add_state`
   */
  addState(stateName: StateName, stateType: string, rhRule?: FreeGroupElement): void {
    this.stateMap.set(nameKey(stateName), new State(stateName, this, stateType, rhRule));
  }

  /**
   * Gets the states by name.
   * @returns The states by name.
   * @see SymPy `sympy.combinatorics.rewritingsystem_fsm.StateMachine.states`
   */
  get states(): Map<StateName, State> {
    return new Map([...this.stateMap.values()].map((s) => [s.name, s]));
  }

  /**
   * Whether a state has this name.
   * @param name - The name used to identify the object.
   * @returns Whether a state with this name exists.
   * @internal
   */
  hasState(name: StateName): boolean {
    return this.stateMap.has(nameKey(name));
  }

  /**
   * Returns the state with this name.
   * @param name - The name used to identify the object.
   * @returns The state with this name.
   * @internal
   */
  state(name: StateName): State {
    return getOrThrow(this.stateMap, nameKey(name));
  }

  /**
   * Formats the object as plain text.
   * @returns The printable representation.
   */
  toString(): string {
    return this.name;
  }
}

/** Python's RuntimeError of a rewriting system that exceeds its maximum number of rules. */
export class RewritingRulesExceeded extends RangeError {
  /** Constructs a `RewritingRulesExceeded`. */
  constructor() {
    super('Too many rules were defined.');
    this.name = 'RewritingRulesExceeded';
  }
}

/** Rules in insertion order, keyed by the left-hand side (a Python dict of words). */
type Rules = Map<string, [FreeGroupElement, FreeGroupElement]>;

/**
 * Reduction rules lhs -> rhs (lhs > rhs in
 * the order of words) that hold in a finitely presented group.
 * @see SymPy `sympy.combinatorics.rewritingsystem.RewritingSystem`
 */
export class RewritingSystem {
  /**
   * The group to which the words belong.
   * @see SymPy `sympy.combinatorics.rewritingsystem.RewritingSystem.group`
   */
  readonly group: RewritingGroup;
  /**
   * The letters used in the rewrite rules.
   * @see SymPy `sympy.combinatorics.rewritingsystem.RewritingSystem.alphabet`
   */
  readonly alphabet: readonly FreeGroupElement[];
  /**
   * The maximum number of rules.
   * @see SymPy `sympy.combinatorics.rewritingsystem.RewritingSystem.maxeqns`
   */
  maxeqns = 32767;
  /**
   * The number of new rules after which redundant ones are removed.
   * @see SymPy `sympy.combinatorics.rewritingsystem.RewritingSystem.tidyint`
   */
  tidyint = 100;
  #isConfluent: boolean | undefined;
  #maxExceeded = false;
  /**
   * The automaton recognizing left-hand sides of rewrite rules.
   * @see SymPy `sympy.combinatorics.rewritingsystem.RewritingSystem.reduction_automaton`
   */
  readonly reductionAutomaton: StateMachine;
  #newRules: Rules = new Map();
  /** The mapping from reducible group words to their replacements. @internal */
  readonly ruleMap: Rules = new Map();
  #rulesCache: [string, string][] = [];
  #automatonReady = false;

  /**
   * Constructs a `RewritingSystem`.
   * @param group - The ambient group.
   */
  constructor(group: RewritingGroup) {
    this.group = group;
    this.alphabet = group.generators;
    const identity = group.freeGroup.identity;
    for (const r of group.relators) this.addRule(r, identity);
    this.#removeRedundancies();
    const generators = [...this.alphabet, ...this.alphabet.map((g) => g.inverse())];
    this.reductionAutomaton = new StateMachine(`Reduction automaton for ${String(group)}`, generators);
    this.#automatonReady = true;
    this.constructAutomaton();
  }

  /**
   * Gets the reduction rules, left-hand side to right-hand side.
   * @returns The reduction rules, left-hand side to right-hand side.
   * @see SymPy `sympy.combinatorics.rewritingsystem.RewritingSystem.rules`
   */
  get rules(): Map<FreeGroupElement, FreeGroupElement> {
    return new Map(this.ruleMap.values());
  }

  /**
   * The maximum number of rules.
   * @param n - The number of positions.
   * @see SymPy `sympy.combinatorics.rewritingsystem.RewritingSystem.set_max`
   */
  setMax(n: number): void {
    if (n > this.maxeqns) this.#maxExceeded = false;
    this.maxeqns = n;
  }

  /**
   * Whether the rules are confluent (computed once).
   * @returns Whether the object is confluent.
   * @see SymPy `sympy.combinatorics.rewritingsystem.RewritingSystem.is_confluent`
   */
  get isConfluent(): boolean {
    return (this.#isConfluent ??= this.#checkConfluence());
  }

  #addRuleRaw(r1: FreeGroupElement, r2: FreeGroupElement): void {
    if (this.ruleMap.size + 1 > this.maxeqns) {
      this.#isConfluent = this.#checkConfluence();
      this.#maxExceeded = true;
      throw new RewritingRulesExceeded();
    }
    this.ruleMap.set(r1.key, [r1, r2]);
    if (this.#automatonReady) this.#newRules.set(r1.key, [r1, r2]);
  }

  /**
   * Add w1 = w2 and the rules it implies;
   * the new left-hand sides (with `check`, those that would be added).
   * @param w1In - The first group word.
   * @param w2In - The second group word.
   * @param check - Whether to verify that the images respect the relations.
   * @returns The left-hand sides of newly introduced rules.
   * @see SymPy `sympy.combinatorics.rewritingsystem.RewritingSystem.add_rule`
   */
  addRule(w1In: FreeGroupElement, w2In: FreeGroupElement, check = false): Set<FreeGroupElement> {
    const newKeys = new Map<string, FreeGroupElement>();
    const add = (w: FreeGroupElement): void => void newKeys.set(w.key, w);
    let w1 = w1In;
    let w2 = w2In;
    if (w1.equals(w2)) return new Set();
    if (w1.lt(w2)) [w1, w2] = [w2, w1];
    if (this.#rulesCache.some(([a, b]) => a === w1.key && b === w2.key)) return new Set();
    this.#rulesCache.push([w1.key, w2.key]);
    // a deque of length 50
    if (this.#rulesCache.length > 50) this.#rulesCache.shift();
    let s1 = w1;
    let s2 = w2;
    if (s1.length - s2.length < 3) {
      if (!this.ruleMap.has(s1.key)) {
        add(s1);
        if (!check) this.#addRuleRaw(s1, s2);
      }
      if (s2.inverse().gt(s1.inverse()) && !this.ruleMap.has(s2.inverse().key)) {
        add(s2.inverse());
        if (!check) this.#addRuleRaw(s2.inverse(), s1.inverse());
      }
    }
    while (s1.length - s2.length > -1) {
      const g = s1.getItem(s1.length - 1);
      s1 = s1.subword(0, s1.length - 1);
      s2 = s2.mul(g.inverse());
      if (s1.length - s2.length < 0) {
        if (!this.ruleMap.has(s2.key)) {
          if (!check) this.#addRuleRaw(s2, s1);
          add(s2);
        }
      } else if (s1.length - s2.length < 3) for (const k of this.addRule(s1, s2, check)) add(k);
    }
    while (w1.length - w2.length > -1) {
      const g = w1.getItem(0);
      w1 = w1.subword(1, w1.length);
      w2 = g.inverse().mul(w2);
      if (w1.length - w2.length < 0) {
        if (!this.ruleMap.has(w2.key)) {
          if (!check) this.#addRuleRaw(w2, w1);
          add(w2);
        }
      } else if (w1.length - w2.length < 3) for (const k of this.addRule(w1, w2, check)) add(k);
    }
    return new Set(newKeys.values());
  }

  #removeRedundancies(): [Map<string, FreeGroupElement>, Map<string, FreeGroupElement>] {
    const removed = new Map<string, FreeGroupElement>();
    const added = new Map<string, FreeGroupElement>();
    const rules = [...this.ruleMap.values()];
    for (const [r, rhs] of rules) {
      const v = this.reduce(r, r);
      const w = this.reduce(rhs);
      if (!v.equals(r)) {
        this.ruleMap.delete(r.key);
        removed.set(r.key, r);
        if (v.gt(w)) {
          added.set(v.key, v);
          this.ruleMap.set(v.key, [v, w]);
        } else if (v.lt(w)) {
          added.set(w.key, w);
          this.ruleMap.set(w.key, [w, v]);
        }
      } else this.ruleMap.set(v.key, [v, w]);
    }
    return [removed, added];
  }

  /**
   * Complete the rules by the Knuth-Bendix
   * procedure (with `check`, only test confluence). Whether the system is
   * confluent; false when the maximum number of rules stopped the completion.
   * @param check - Whether to verify that the images respect the relations.
   * @returns Whether all overlapping reductions agree.
   * @see SymPy `sympy.combinatorics.rewritingsystem.RewritingSystem.make_confluent`
   */
  makeConfluent(check = false): boolean {
    // the confluence was checked when the maximum was exceeded
    if (this.#maxExceeded) return Boolean(this.#isConfluent);
    let lhs = [...this.ruleMap.values()].map(([k]) => k);
    const overlaps = (r1: FreeGroupElement, r2: FreeGroupElement): FreeGroupElement[] => {
      const len1 = r1.length;
      const len2 = r2.length;
      const result: FreeGroupElement[] = [];
      for (let j = 1; j < len1 + len2; j++) {
        if (r1.subword(len1 - j, len1 + len2 - j, false).equals(r2.subword(j - len1, j, false))) {
          const a = r1.subword(0, len1 - j, false).mul(r2.subword(0, j - len1, false));
          const b = r2.subword(j - len1, j, false);
          const c = r2.subword(j, len2, false).mul(r1.subword(len1 + len2 - j, len1, false));
          result.push(a.mul(b).mul(c));
        }
      }
      return result;
    };
    // the new left-hand sides; 'exceeded' when the maximum number of rules was reached
    const processOverlap = (w: FreeGroupElement, r1: FreeGroupElement, r2: FreeGroupElement): FreeGroupElement[] | 'exceeded' => {
      const s = this.reduce(w.eliminateWord(r1, this.#rhs(r1)));
      const t = this.reduce(w.eliminateWord(r2, this.#rhs(r2)));
      if (s.equals(t)) return [];
      if (check) return [s];
      try {
        return [...this.addRule(t, s, check)];
      } catch {
        // addRule raises only RewritingRulesExceeded
        return 'exceeded';
      }
    };
    let added = 0;
    let i = 0;
    while (i < lhs.length) {
      const r1 = at(lhs, i);
      i++;
      let j = 0;
      while (j < lhs.length) {
        const r2 = at(lhs, j);
        j++;
        if (r1.equals(r2)) continue;
        const os = [...overlaps(r1, r2), ...overlaps(r1.inverse(), r2)];
        if (!os.length) continue;
        let exceeded = false;
        for (const w of os) {
          const newKeys = processOverlap(w, r1, r2);
          if (newKeys === 'exceeded') {
            exceeded = true;
            break;
          }
          if (newKeys.length) {
            if (check) return false;
            lhs.push(...newKeys);
            added += newKeys.length;
          }
        }
        if (exceeded) return Boolean(this.#isConfluent);
        if (added > this.tidyint && !check) {
          const [r, a] = this.#removeRedundancies();
          added = 0;
          // SymPy: i = min(lhs.index(s) for s in r) when rules were removed
          i = [...r.keys()].map((k) => lhs.findIndex((l) => l.key === k)).reduce((m, v, n) => (n === 0 ? v : Math.min(m, v)), i);
          lhs = lhs.filter((l) => !r.has(l.key));
          lhs.push(...a.values());
          if (r.has(r1.key)) break;
        }
      }
    }
    this.#isConfluent = true;
    if (!check) this.#removeRedundancies();
    return true;
  }

  #rhs(r: FreeGroupElement): FreeGroupElement {
    return defined(this.ruleMap.get(r.key), 'rule')[1];
  }

  #checkConfluence(): boolean {
    return this.makeConfluent(true);
  }

  /**
   * The normal form of word under the rules (without the rule for exclude).
   * @param word - The group word to examine.
   * @param exclude - The rule to skip during reduction.
   * @returns The resulting group word.
   * @see SymPy `sympy.combinatorics.rewritingsystem.RewritingSystem.reduce`
   */
  reduce(word: FreeGroupElement, exclude?: FreeGroupElement): FreeGroupElement {
    const rules = [...this.ruleMap.values()].filter(([r]) => exclude === undefined || !r.equals(exclude));
    let again = true;
    let w = word;
    while (again) {
      again = false;
      for (const [r, v] of rules) {
        const prev = w;
        w = v.inverse().gt(r.inverse()) ? w.eliminateWord(r, v, true, false) : w.eliminateWord(r, v, true);
        if (!w.equals(prev)) again = true;
      }
    }
    return w;
  }

  /**
   * Add the rules (and their inverses) to the reduction automaton.
   * @see SymPy `sympy.combinatorics.rewritingsystem.RewritingSystem.construct_automaton`
   */
  constructAutomaton(): void {
    this.#addToAutomaton(this.ruleMap);
  }

  #addToAutomaton(rules: Rules): void {
    const automaton = this.reductionAutomaton;
    const alphabet = new Map<string, FreeGroupElement>();
    const inverseRules: Rules = new Map();
    for (const [r, v] of rules.values()) {
      const ki = r.inverse();
      const vi = v.inverse();
      if (vi.lt(ki)) inverseRules.set(ki.key, [ki, vi]);
      else inverseRules.set(vi.key, [vi, ki]);
    }
    // SymPy updates the given rules (the system's own rules or the new ones) with their inverses
    for (const [k, rule] of inverseRules) rules.set(k, rule);
    const acceptStates: FreeGroupElement[] = [];
    for (const [rule, rhs] of rules.values()) {
      const letters = rule.letterFormElm;
      for (const l of letters) alphabet.set(l.key, l);
      for (let i = 1; i < letters.length; i++) {
        letters[i] = at(letters, i - 1).mul(at(letters, i));
        const elem = at(letters, i - 1);
        if (!automaton.hasState(elem)) {
          automaton.addState(elem, 'a');
          acceptStates.push(elem);
        }
      }
      const k = acceptStates.findIndex((s) => s.equals(rule));
      if (k >= 0) {
        const st = automaton.state(rule);
        st.stateType = 'd';
        st.rhRule = rhs;
        acceptStates.splice(k, 1);
      }
      if (!automaton.hasState(rule)) automaton.addState(rule, 'd', rhs);
    }
    const next = (name: FreeGroupElement, letter: FreeGroupElement): StateName => {
      let w = name.mul(letter);
      while (w.length && !automaton.hasState(w)) w = w.subword(1, w.length);
      return w.length ? w : 'start';
    };
    for (const state of automaton.stateMap.values()) {
      if (state.stateType === 's') {
        // every letter of a rule is a state (a proper prefix, or a one-letter rule)
        for (const letter of alphabet.values()) state.addTransition(letter, letter);
      } else if (state.stateType === 'a' && state.name !== 'start') {
        for (const letter of alphabet.values()) state.addTransition(letter, next(state.name, letter));
      }
    }
    if (automaton.automatonAlphabet.length !== alphabet.size) {
      for (const state of acceptStates) for (const letter of automaton.automatonAlphabet) automaton.state(state).addTransition(letter, next(state, letter));
    }
  }

  /**
   * The reduced word, found with the reduction automaton.
   * @param wordIn - The group word to examine.
   * @returns The resulting group word.
   * @see SymPy `sympy.combinatorics.rewritingsystem.RewritingSystem.reduce_using_automaton`
   */
  reduceUsingAutomaton(wordIn: FreeGroupElement): FreeGroupElement {
    if (this.#newRules.size) {
      this.#addToAutomaton(this.#newRules);
      this.#newRules = new Map();
    }
    const automaton = this.reductionAutomaton;
    let word = wordIn;
    let flag = true;
    while (flag) {
      flag = false;
      let current = automaton.state('start');
      const letters = word.letterFormElm;
      for (let i = 0; i < letters.length; i++) {
        // a letter that occurs in no rule leads back to the start
        const nextName = current.transitions.get(at(letters, i).key) ?? 'start';
        const nextState = automaton.state(nextName);
        if (nextState.stateType === 'd' && nextName !== 'start') {
          word = word.substitutedWord(i - nextName.length + 1, i + 1, defined(nextState.rhRule, 'rule'));
          flag = true;
          break;
        }
        current = nextState;
      }
    }
    return word;
  }
}
