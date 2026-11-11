# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
"""Execution and accounting contracts of the independent unit-test extractor."""

import os
import json
import textwrap
import unittest
from unittest.mock import patch

import extract_tests as unit


class UnitTestExtractorTests(unittest.TestCase):
    def extract(self, source, timeout=2):
        source = "from sympy import *\nfrom sympy.testing.pytest import raises, XFAIL, slow, SKIP\n" + textwrap.dedent(source)
        events, tests, sites = unit.execute_source(source, "sympy.core.tests.test_fixture", "core", "test_fixture.py", timeout)
        result = unit.corpus_from_events(events, tests, sites)
        audit = result["extraction"]
        self.assertEqual(audit["examined"], len(result["cases"]) + sum(audit["reasons"].values()))
        self.assertEqual(audit["categories"]["core"]["examined"], audit["examined"])
        return result

    def test_calls_operators_attributes_subscripts_and_boolean_forms(self):
        corpus = self.extract('''
            def test_forms():
                x = Symbol('x', positive=True)
                assert expand((x + 1)**2) == x*x + 2*x + 1
                assert Integer(2) != Integer(3)
                assert x.is_positive is True
                assert x.is_integer is None
                assert x.is_real
                assert not x.is_negative
                assert x + 1 == Add(x, 1)
                assert Tuple(x, 2)[0] == x
                assert x.diff(x) == Integer(1)
        ''')
        self.assertEqual([c["op"] for c in corpus["cases"]], ['==', '!=', 'is', 'is', 'truthy', 'falsy', '==', '==', '=='])
        self.assertEqual(corpus["cases"][3]["expected"], 'None')
        self.assertEqual(corpus["cases"][-2]["fn"], '.__getitem__')
        self.assertTrue(all(c['line'] > 2 and c['test'] == 'test_forms' for c in corpus['cases']))

    def test_each_operand_is_evaluated_once_before_mutation(self):
        corpus = self.extract('''
            def test_mutation():
                calls = []
                m = Matrix([[1, 2]])
                def receiver():
                    calls.append(1)
                    return m
                assert receiver().row_del(0) is None
                assert len(calls) == 1
                assert m.rows == 0
        ''')
        case = corpus['cases'][0]
        self.assertEqual(case['fn'], '.row_del')
        self.assertIn('2', str(case['self']))
        self.assertEqual(corpus['extraction']['testStatuses'], {'completed': 1})

    def test_loops_helpers_and_full_record_deduplication(self):
        corpus = self.extract('''
            def check(i):
                assert Integer(i) == i
            def test_loop():
                for i in [1, 2, 1]:
                    check(i)
        ''')
        self.assertEqual(len(corpus['cases']), 2)
        self.assertEqual(corpus['extraction']['reasons'], {'duplicate': 1})
        self.assertTrue(all(c['test'] == 'test_loop' for c in corpus['cases']))

    def test_both_exception_forms_and_aliases(self):
        corpus = self.extract('''
            from sympy import Integer as Int
            import sympy as sp
            def test_errors():
                raises(ValueError, lambda: Int('invalid'))
                with raises(ValueError):
                    sp.Integer('invalid')
                with raises(TypeError):
                    value = Symbol()
        ''')
        self.assertEqual([c['raises'] for c in corpus['cases']], ['ValueError', 'ValueError', 'TypeError'])
        self.assertEqual([c['fn'] for c in corpus['cases']], ['Integer', 'Integer', 'Symbol'])
        self.assertEqual(corpus['extraction']['testStatuses'], {'completed': 1})

    def test_omissions_and_unreached_sites_are_accounted_for(self):
        corpus = self.extract('''
            def test_omitted():
                a = 1
                assert a == 1
                assert 1 < 2 < 3
                assert [1][0] == 1
                assert Symbol('x')
                if False:
                    assert Integer(3) == 3
        ''')
        self.assertEqual(corpus['extraction']['reasons'], {
            'non-call-expression': 1, 'unsupported-assertion': 1,
            'python-runtime-api': 1, 'non-boolean-assertion': 1, 'not-executed': 1})

    def test_decorators_dependencies_and_timeouts(self):
        corpus = self.extract('''
            @XFAIL
            def test_xfail():
                assert Integer(1) == 2
            @slow
            def test_slow():
                assert Integer(1) == 1
            @SKIP('reason')
            def test_skip():
                assert Integer(1) == 1
            def test_numpy():
                import numpy as np
                assert Integer(1) == 1
            def test_timeout():
                assert Integer(1) == 1
                while True:
                    try:
                        while True:
                            pass
                    except Exception:
                        pass
            def test_after():
                assert Integer(2) == 2
        ''', timeout=0.05)
        self.assertEqual(len(corpus['cases']), 1)
        self.assertEqual(corpus['extraction']['reasons'], {'marked-xfail': 1, 'marked-slow': 1, 'marked-skip': 1,
                                                         'optional-dependency': 1, 'test-timeout': 1})

    def test_optional_imports_reached_indirectly_are_blocked(self):
        corpus = self.extract('''
            def dependency():
                return __import__('num' + 'py')
            def test_dependency():
                dependency()
                assert Integer(1) == 1
        ''')
        self.assertEqual(corpus['extraction']['testStatuses'], {'optional-dependency': 1})
        self.assertEqual(corpus['extraction']['reasons'], {'optional-dependency': 1})

    def test_iterator_inputs_are_not_consumed_by_capture(self):
        corpus = self.extract('''
            def test_iterators():
                assert Tuple.fromiter(x for x in range(3)) == Tuple(0, 1, 2)
                x, y = symbols('x y')
                assert x.subs(reversed([(x, y)])) == y
        ''')
        self.assertEqual(corpus['extraction']['testStatuses'], {'completed': 1})
        self.assertEqual(corpus['extraction']['reasons'], {'stateful-iterator-input': 2})

    def test_nonfinite_inputs_are_valid_json_and_warnings_keep_their_call_site(self):
        corpus = self.extract('''
            from sympy.testing.pytest import warns_deprecated_sympy
            def test_nonfinite():
                assert sympify(float('inf')) == oo
            def test_warning():
                x = Symbol('x')
                with warns_deprecated_sympy():
                    assert x.expr_free_symbols == {x}
        ''')
        self.assertEqual(corpus['extraction']['testStatuses'], {'completed': 2})
        self.assertEqual(corpus['cases'][0]['args'][0]['v'], 'Infinity')
        json.dumps(corpus, allow_nan=False)

    def test_parametrization_runs_every_row_and_preserves_skip_marks(self):
        corpus = self.extract('''
            import pytest
            @pytest.mark.parametrize('i', [1, 2, pytest.param(3, marks=pytest.mark.skip)])
            @pytest.mark.parametrize('j', [4, 5])
            def test_parameters(i, j):
                assert Integer(i) + j == i + j
        ''')
        self.assertEqual(len(corpus['cases']), 4)
        self.assertEqual(corpus['extraction']['testStatuses'], {'completed': 4, 'marked-skip': 2})

    def test_private_unserializable_and_failed_references(self):
        corpus = self.extract('''
            def test_private():
                assert Symbol('x')._hashable_content() == ('x', ('commutative', True))
            def test_bad_input():
                assert sympify(object(), strict=False) is None
            def test_bad_reference():
                assert Integer(1) == 2
        ''')
        self.assertEqual(len(corpus['cases']), 0)
        self.assertGreater(corpus['extraction']['examined'], 0)

    def test_hash_seed_and_version_are_required(self):
        with patch.object(unit.sympy, '__version__', '0'):
            with self.assertRaisesRegex(RuntimeError, 'pinned'):
                unit.main('unused')
        with patch.dict(os.environ, {'PYTHONHASHSEED': '1'}):
            with self.assertRaisesRegex(RuntimeError, 'PYTHONHASHSEED'):
                unit.main('unused')

    def test_repeat_extraction_is_identical(self):
        source = '''
            def test_deterministic():
                assert Integer(2) == 2
                assert Symbol('x').is_real is None
                assert Dummy().dummy_index != 0
        '''
        self.assertEqual(self.extract(source), self.extract(source))


if __name__ == '__main__':
    unittest.main()
