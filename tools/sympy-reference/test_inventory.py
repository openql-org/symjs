# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
"""Synthetic measurements exercise strict completeness independently of the corpus."""
import ast
import copy
import json
from pathlib import Path
import unittest

from inventory import (PublicContracts, api_criterion, evaluate_completeness,
                       DOCTEST_EXCLUSIONS, DOCTEST_OMISSIONS, UNIT_OMISSIONS,
                       build_inventory, public_outline, test_module_for)


class CompletenessTests(unittest.TestCase):
    def setUp(self):
        self.module = 'sympy.example.widget'
        self.test_module = test_module_for(self.module)
        self.api = {'exports': {'Widget': {'kind': 'function', 'entries': ['./subpath'],
                                        'prototype': ['getValue', 'size'], 'static': ['make']},
                                'getWidget': {'kind': 'function', 'entries': ['.'], 'prototype': [], 'static': []}}}
        self.contract = {'names': ['Widget', 'get_widget'],
                         'classes': {'Widget': {'members': ['get_value', 'size', 'make'], 'families': ['Widget']}},
                         'unresolvedBases': []}
        self.unit = {'exists': True, 'caseCount': 1, 'gaps': [], 'timeouts': [], 'omitted': [], 'tests': []}
        self.evidence = {'doctests': {self.module: [{'src': 'get_widget()'}]},
                         'doctestOmissions': {}, 'doctestGaps': [], 'doctestExclusions': {},
                         'units': {self.test_module: self.unit}, 'limitations': []}

    def evaluate(self, **kwargs):
        return evaluate_completeness(self.module, self.contract, self.api, self.evidence, **kwargs)

    def test_all_criteria_pass(self):
        self.assertTrue(all(c['pass'] for c in self.evaluate(documented_examples=1).values()))
        self.assertEqual(self.test_module, 'sympy.example.tests.test_widget')
        self.assertEqual(test_module_for('sympy'), 'sympy.tests.test_sympy')
        self.assertEqual(test_module_for('sympy.tensor.toperators'), 'sympy.tensor.tests.test_tensor_operators')
        self.assertEqual(test_module_for('sympy.liealgebras.type_e'), 'sympy.liealgebras.tests.test_type_E')
        del self.evidence['units'][self.test_module]
        self.assertFalse(self.evaluate(documented_examples=1)['unitTests']['pass'])
        self.evidence['upstreamTests'] = set()
        result = self.evaluate(documented_examples=1)['unitTests']
        self.assertTrue(result['pass'])
        self.assertFalse(result['applicable'])
        self.evidence['upstreamTests'] = {self.test_module}
        self.assertFalse(self.evaluate(documented_examples=1)['unitTests']['pass'])

    def test_missing_export_and_members_are_concrete(self):
        del self.api['exports']['getWidget']
        self.api['exports']['Widget']['prototype'].remove('size')
        self.api['exports']['Unrelated'] = {'prototype': ['size'], 'static': []}
        result = self.evaluate()['publicApi']
        self.assertFalse(result['pass'])
        self.assertEqual(result['missingNames'], ['Widget.size', 'get_widget'])

    def test_python_specific_names_are_listed_without_blocking(self):
        self.contract['classes']['Widget']['members'] += ['__floordiv__', 'is_Widget']
        result = self.evaluate()['publicApi']
        self.assertTrue(result['pass'])
        self.assertEqual(result['missingNames'], [])
        self.assertEqual(result['pythonSpecificNames'], ['Widget.__floordiv__', 'Widget.is_Widget'])
        self.contract['classes']['Widget']['members'].append('is_widget')
        result = self.evaluate()['publicApi']
        self.assertFalse(result['pass'])
        self.assertEqual(result['missingNames'], ['Widget.is_widget'])

    def test_deprecated_and_internal_sympy_names_are_listed_without_blocking(self):
        contract = {'names': ['Expr'], 'classes': {'Expr': {'members': ['expr_free_symbols', 'class_key', 'fromiter', 'subs'], 'families': ['Expr']}}}
        api = {'exports': {'Expr': {'kind': 'function', 'prototype': ['subs'], 'static': []}}}
        result = api_criterion('sympy.core.expr', contract, api)
        self.assertTrue(result['pass'])
        self.assertEqual(result['internalNames'], ['Expr.class_key', 'Expr.expr_free_symbols'])
        self.assertEqual(result['pythonSpecificNames'], ['Expr.fromiter'])
        contract['classes']['Expr']['members'].append('canonical_variables')
        self.assertEqual(api_criterion('sympy.core.expr', contract, api)['missingNames'], ['Expr.canonical_variables'])

    def test_expression_members_are_provided_by_expr_and_its_functions(self):
        api = {'exports': {'Expr': {'kind': 'function', 'prototype': ['has'], 'static': []},
                           'sin': {'kind': 'function', 'prototype': [], 'static': []},
                           'isPositive': {'kind': 'function', 'prototype': [], 'static': []},
                           'subs': {'kind': 'function', 'prototype': [], 'static': []}}}
        api['exports']['fdiff'] = {'kind': 'function', 'prototype': [], 'static': []}
        contract = {'names': ['sin'], 'classes': {'sin': {'members': ['args', 'eval', 'fdiff', 'has', 'is_positive', 'subs', 'is_composite'], 'families': ['Basic', 'Expr', 'Function']}}}
        api['exports']['isExtendedNonnegative'] = {'kind': 'function', 'prototype': [], 'static': []}
        api['exports']['isNonNegative'] = {'kind': 'function', 'prototype': [], 'static': []}
        contract['classes']['sin']['members'] += ['is_extended_nonnegative', 'is_nonnegative']
        result = api_criterion('sympy.functions.elementary.trigonometric', contract, api)
        self.assertEqual(result['missingNames'], ['sin.is_composite'])
        self.assertEqual(result['internalNames'], ['sin.eval'])
        del api['exports']['subs']
        self.assertEqual(api_criterion('sympy.functions.elementary.trigonometric', contract, api)['missingNames'], ['sin.is_composite', 'sin.subs'])

    def test_function_form_requires_documented_owner_and_real_export(self):
        self.api['policy'] = {'attributeFunctions': {'canonical': 'canonicalRelation'}}
        self.contract['classes']['Widget'] = {'members': ['canonical'], 'families': ['Relational']}
        self.assertFalse(self.evaluate()['publicApi']['pass'])
        self.api['exports']['canonicalRelation'] = {'kind': 'function', 'prototype': [], 'static': []}
        self.assertTrue(self.evaluate()['publicApi']['pass'])
        self.contract['classes']['Widget']['families'] = ['Unrelated']
        self.assertFalse(self.evaluate()['publicApi']['pass'])

    def test_class_names_renames_and_aliases(self):
        api = {'exports': {'Sym': {'prototype': [], 'static': []}, 'Legacy': {'prototype': [], 'static': []}},
               'policy': {'renames': {'Symbol': 'Sym'}, 'aliases': {'old_name': 'Legacy'}}}
        self.assertTrue(api_criterion(self.module, {'names': ['Symbol', 'old_name'], 'classes': {}}, api)['pass'])
        # a snake_case SymPy class is a function class: its counterpart is the camelCase function
        self.contract['names'] = ['lower_case']
        self.contract['classes'] = {'lower_case': {'members': [], 'families': []}}
        self.assertEqual(self.evaluate()['publicApi']['missingNames'], ['lower_case'])
        self.api['exports']['lowerCase'] = {'prototype': [], 'static': []}
        self.assertEqual(self.evaluate()['publicApi']['missingNames'], [])
        # A geometric Point is not evidence of the ECM Point's API.
        self.assertFalse(api_criterion('sympy.ntheory.ecm', {'names': ['Point'], 'classes': {}}, {'exports': {'Point': {}}})['pass'])

    def test_documented_class_alias_supplies_its_members(self):
        self.api['exports']['RenamedWidget'] = self.api['exports'].pop('Widget')
        self.api['policy'] = {'aliases': {'Widget': 'RenamedWidget'}}
        self.assertTrue(self.evaluate()['publicApi']['pass'])
        self.api['exports']['RenamedWidget']['prototype'].remove('size')
        self.assertEqual(self.evaluate()['publicApi']['missingNames'], ['Widget.size'])

    def test_gaps_and_non_python_exclusions_fail_even_if_no_case_remains(self):
        self.evidence['doctestGaps'] = [self.module + ': get_widget() #hash']
        self.assertEqual(self.evaluate()['doctests']['gapCount'], 1)
        self.evidence['doctestGaps'] = []
        for reason in ['null input', 'plotting', 'pmf evaluated at its argument', 'test utility', 'unknown']:
            with self.subTest(reason=reason):
                self.evidence['doctestExclusions'] = {self.module + ': f()': reason}
                self.assertFalse(self.evaluate()['doctests']['pass'])
        for reason in DOCTEST_EXCLUSIONS:
            self.evidence['doctestExclusions'] = {self.module + ': f()': reason}
            self.assertTrue(self.evaluate()['doctests']['pass'])

    def test_doctest_omission_allowlist(self):
        for reason in DOCTEST_OMISSIONS | {'non-call-expression', 'unsupported-result-type', 'not-exported-api', 'serialization-error', 'printing-expression', 'private-api', 'statement-or-setup', 'unknown'}:
            with self.subTest(reason=reason):
                self.evidence['doctestOmissions'] = {self.module: [{'reason': reason, 'count': 3}]}
                row = self.evaluate()['doctests']
                self.assertEqual(row['pass'], reason in DOCTEST_OMISSIONS)
                self.assertEqual(row['disallowedOmissions'], {} if reason in DOCTEST_OMISSIONS else {reason: 3})

    def test_unmeasured_documentation_fails(self):
        self.assertFalse(self.evaluate(documented_examples=2)['doctests']['pass'])
        self.assertFalse(self.evaluate(documented_examples=1, selected=False)['doctests']['pass'])
        self.evidence['doctests'] = {}
        self.assertTrue(self.evaluate(documented_examples=0, selected=False)['doctests']['pass'])

    def test_unit_file_and_nonempty_corpus_required(self):
        for changes in [{'exists': False}, {'caseCount': 0}]:
            original = copy.deepcopy(self.unit)
            self.unit.update(changes)
            self.assertFalse(self.evaluate()['unitTests']['pass'])
            self.unit.update(original)
        self.evidence['units'] = {}
        self.assertFalse(self.evaluate()['unitTests']['pass'])

    def test_unit_gaps_and_timeouts_block_completion(self):
        self.unit['gaps'] = ['a', 'b']
        self.unit['timeouts'] = ['b', 'c']
        row = self.evaluate()['unitTests']
        self.assertFalse(row['pass'])
        self.assertEqual(row['gapCount'], 3)
        self.assertEqual(row['timeoutCount'], 2)

    def test_every_unit_omission_reason_fails_closed(self):
        disallowed = {'marked-slow', 'marked-tooslow', 'non-call-expression', 'unsupported-assertion', 'not-exported-api', 'unserializable-input', 'stateful-iterator-input', 'serialization-error', 'test-timeout', 'not-executed', 'unsupported-raises', 'upstream-skip', 'reference-exception', 'unknown'}
        for reason in UNIT_OMISSIONS | disallowed:
            with self.subTest(reason=reason):
                self.unit['omitted'] = [{'reason': reason, 'count': 4}, {'reason': reason, 'count': 2}]
                row = self.evaluate()['unitTests']
                self.assertEqual(row['pass'], reason in UNIT_OMISSIONS)
                self.assertEqual(row['disallowedOmissions'], {} if reason in UNIT_OMISSIONS else {reason: 6})
        self.unit['omitted'] = []
        self.unit['tests'] = [{'status': 'test-timeout'}]
        self.assertFalse(self.evaluate()['unitTests']['pass'])

    def test_notes_and_capabilities_block_completion(self):
        self.assertFalse(self.evaluate(limitation='Known limitation')['limitations']['pass'])
        self.assertFalse(self.evaluate(limitation='')['limitations']['pass'])
        self.evidence['limitations'] = [{'area': 'Example', 'modules': ['sympy.example'], 'remaining': ['Missing behavior']}]
        result = self.evaluate()['limitations']
        self.assertFalse(result['pass'])
        self.assertEqual(result['capabilities'][0]['remaining'], ['Missing behavior'])
        self.evidence['limitations'][0]['modules'] = ['sympy.examples']
        self.assertTrue(self.evaluate()['limitations']['pass'])

    def test_static_contract_keeps_methods_properties_and_operators(self):
        tree = ast.parse('''
from abc import ABC
class Base:
    def inherited(self): pass
class Widget(Base, ABC):
    __slots__ = ()
    @property
    def size(self): pass
    @classmethod
    def make(cls): pass
    @staticmethod
    def get_value(): pass
    def __add__(self, other): pass
    def __radd__(self, other): pass
    def __eq__(self, other): pass
    def __repr__(self): pass
    def __hash__(self): pass
    def __getstate__(self): pass
    def __getitem__(self, i): pass
    def _sympystr(self, printer): pass
    def _private(self): pass
''')
        contract = PublicContracts({self.module: tree}).contract(self.module)
        self.assertEqual(contract['classes']['Widget']['members'], ['__add__', '__eq__', '__radd__', 'get_value', 'inherited', 'make', 'size'])
        self.assertEqual(contract['unresolvedBases'], [])
        self.assertEqual(PublicContracts({self.module: public_outline(tree)}).contract(self.module), contract)

    def test_imported_inheritance_and_explicit_exports(self):
        a = ast.parse('class Base:\n    def public(self): pass')
        b = ast.parse('from .base import Base as Parent\nclass Widget(Parent): pass\n__all__ = ["Parent", "Widget"]')
        contract = PublicContracts({'sympy.example.base': a, self.module: b}).contract(self.module)
        self.assertEqual(contract['classes']['Widget']['members'], ['public'])
        self.assertEqual(contract['classes']['Parent']['members'], ['public'])
        package = ast.parse('from .base import Base\nAlias = Base')
        package.is_package = True
        c = ast.parse('from sympy.example import Base, Alias\nfrom typing import NamedTuple\nclass Widget(Base): pass\nclass Other(Alias, NamedTuple): pass\nclass Row(list[int]): pass')
        trees = {'sympy.example.base': a, 'sympy.example': package, self.module: c}
        contract = PublicContracts(trees).contract(self.module)
        self.assertEqual(contract['classes']['Widget']['members'], ['public'])
        self.assertEqual(contract['classes']['Other']['members'], ['public'])
        self.assertEqual(contract['unresolvedBases'], [])
        self.assertEqual(PublicContracts({k: public_outline(copy.deepcopy(v)) for k, v in trees.items()}).contract(self.module), contract)
        unknown = ast.parse('class Widget(External): pass')
        contract = PublicContracts({self.module: unknown}).contract(self.module)
        self.assertFalse(api_criterion(self.module, contract, self.api)['pass'])

    def test_committed_inventory_is_reproducible(self):
        root = Path(__file__).resolve().parents[2]
        expected = json.loads((root / 'tools/sympy-reference/scope-inventory.json').read_text())
        self.assertEqual(build_inventory(root), expected)
        modules = {m['module'] for m in expected['modules']}
        for area in self.evidence_from_repository(root)['areas']:
            self.assertTrue(area['modules'], area['area'])
            self.assertTrue(set(area['modules']) <= modules, area['area'])

    @staticmethod
    def evidence_from_repository(root):
        return json.loads((root / 'tools/sympy-reference/capabilities.json').read_text())


if __name__ == '__main__':
    unittest.main()
