# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
"""Execution and accounting contracts of the independent unit-test extractor."""

import os
import json
import textwrap
import tempfile
from pathlib import Path
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

    def test_order_identity_membership_and_undecided_forms(self):
        corpus = self.extract('''
            def test_forms():
                x = Symbol('x')
                assert abs(Float(2) - 2) < 1e-10
                assert sin(x).func is sin
                assert sin(x) not in (False, True)
                assert not x.is_positive
                assert Integer(2) >= 3
        ''')
        self.assertEqual([(c["fn"], c["op"], c["expected"]) for c in corpus["cases"]],
                         [(".__lt__", "truthy", "True"), (".func", "is", "sin"), (".__contains__", "falsy", "False"), (".is_positive", "falsy", "None")])
        self.assertEqual(corpus["extraction"]["reasons"], {"reference-assertion-failed": 1})

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

    def test_assertions_about_names_assigned_from_calls(self):
        corpus = self.extract('''
            from sympy.polys.numberfields.galoisgroups import _galois_group_degree_3
            def test_bound():
                x = Symbol('x')
                q, r = div(x**2 + 1, x)
                assert q == x
                assert r == 1
                e = expand((x + 1)**2)
                assert e == x**2 + 2*x + 1
                e = 5
                assert e == 5
                m = Matrix([[1, 2]])
                m[0, 0] = 3
                assert m == Matrix([[3, 2]])
                assert _galois_group_degree_3(Poly(x**3 - 2)) is not None
                assert Integer(2).is_even is (1 == 1)
                assert Integer(2).is_even is not False
                assert Integer(2) is Integer(2)
        ''')
        cases = corpus['cases']
        self.assertEqual([(c['fn'], c.get('pick'), c['op'], c['expected']) for c in cases], [
            ('div', 0, '==', 'x'), ('div', 1, '==', '1'), ('expand', None, '==', 'x**2 + 2*x + 1'),
            ('.is_even', None, 'is', 'True'), ('.is_even', None, 'is not', 'False')])
        self.assertEqual(corpus['extraction']['reasons'], {
            'non-call-expression': 2, 'private-api': 1, 'unsupported-assertion': 1})

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
                assert Tuple(1)
                if False:
                    assert Integer(3) == 3
        ''')
        self.assertEqual(corpus['extraction']['reasons'], {
            'non-call-expression': 1, 'unsupported-assertion': 1,
            'python-runtime-api': 2, 'non-boolean-assertion': 1, 'not-executed': 1})

    def test_bound_names_projections_and_split_assertions(self):
        corpus = self.extract('''
            def _test_disabled():
                assert Integer(4) == 4
            def test_bound():
                x = Symbol('x')
                q, r = div(Poly(x**2 + 1, x), Poly(x, x))
                assert q == Poly(x, x)
                assert [str(c) for c in r.all_coeffs()] == ['1']
                assert len(Tuple(1, 2)) == 2
                assert list(Tuple(1, 2)) == [1, 2]
                assert str(Integer(5)) == '5'
                assert repr(Integer(5)) == '5'
                e = expand((x + 1)**2)
                e2 = e
                assert e2 == x**2 + 2*x + 1
                assert e and Integer(1) == 1
                assert Integer(1) == 1 and [1][0] == 1 and e
                assert Integer(1) == Integer(1) != Integer(2)
                assert Tuple(1, 2, 3)[:2] == Tuple(1, 2)
                m = Matrix([[1]])
                m[0, 0] = 2
                assert m == Matrix([[2]])
                n = Integer(2)
                n = 3
                assert n == 3
                s = Symbol('s')
                assert s
                f = lambda t: 2*t
                assert Lambda(x, f(x))(1) == 2
        ''')
        cases = corpus['cases']
        self.assertEqual(cases[0]['test'], '_test_disabled')
        self.assertEqual([(c['fn'], c.get('pick'), c.get('post')) for c in cases[1:]], [
            ('div', 0, None), ('.all_coeffs', None, 'str-items'), ('Tuple', None, 'len'), ('Tuple', None, 'list'),
            ('Integer', None, 'str'), ('Integer', None, 'repr'), ('Integer', None, None), ('Integer', None, None),
            ('Integer', None, None), ('Integer', None, None), ('.__getitem__', None, None), ('.__call__', None, None)])
        self.assertEqual(cases[2]['expected'], "['1']")
        self.assertTrue(cases[5]['text'])
        self.assertEqual(cases[-2]['args'][0]['t'], 'Slice')
        self.assertEqual(corpus['extraction']['reasons'], {'non-call-expression': 3, 'python-runtime-api': 4})

    def test_str_and_repr_are_replayed_as_printed_text(self):
        corpus = self.extract('''
            from sympy.combinatorics import Permutation, Cycle
            def test_printed():
                x = Symbol('x')
                p = Permutation(1, 2)
                assert str(p) == '(1 2)'
                assert repr(p) == 'Permutation(1, 2)'
                assert str(Cycle(1, 2)(4, 5)) == '(1 2)(4 5)'
                assert str(Tuple(Float(0.5), Symbol("a"))) == "(0.5, a)"
                assert str([Integer(1)]) == '[1]'
                assert str(Poly(x**2 - 1).factor_list()) == "(1, [(Poly(x - 1, x, domain='ZZ'), 1), (Poly(x + 1, x, domain='ZZ'), 1)])"
                assert repr(Rational(1, 2)) == '1/2'
                assert str(expand((x + 1)**2)) != 'x'
                assert str(Integer(1).as_coeff_Mul) != ''
                assert str(Integer(2)) == '3'
        ''')
        cases = corpus['cases']
        self.assertEqual([(c['fn'], c.get('post'), c['op'], c['expected'], c.get('text')) for c in cases], [
            ('Permutation', 'str', '==', '(1 2)', True), ('Permutation', 'repr', '==', 'Permutation(1, 2)', True),
            ('.__call__', 'str', '==', '(1 2)(4 5)', True), ('Tuple', 'str', '==', '(0.5, a)', True),
            ('.factor_list', 'str', '==', "(1, [(Poly(x - 1, x, domain='ZZ'), 1), (Poly(x + 1, x, domain='ZZ'), 1)])", True),
            ('Rational', 'repr', '==', '1/2', True), ('expand', 'str', '!=', 'x', True)])
        self.assertEqual(cases[4]['brackets'], 'tltt')
        self.assertNotIn('brackets', cases[0])
        self.assertEqual(corpus['extraction']['reasons'], {
            'python-object-representation': 1, 'non-call-expression': 1, 'reference-assertion-failed': 1})

    def test_bindings_neither_print_nor_retain_their_values(self):
        corpus = self.extract('''
            import gc, weakref
            import pytest
            from sympy.combinatorics import Permutation
            def test_cache():
                p = Permutation([(0, 3, 1, 2), (4, 5)])
                assert p._cyclic_form is None
                assert p.size == 6
            def test_collected():
                f = Lambda(Symbol('x'), Symbol('x') + 1)
                assert f(1) == 2
                r = weakref.ref(f)
                del f
                gc.collect()
                assert r() is None
            def test_approx():
                c = Point2D(0.5, 0.25).coordinates
                assert c == pytest.approx((0.5, 0.25))
        ''')
        self.assertEqual(corpus['extraction']['testStatuses'], {'completed': 3})
        self.assertEqual(corpus['extraction']['reasons'].get('test-utility'), 1)

    def test_lambda_arguments_are_expressions_or_recorded_tables(self):
        corpus = self.extract('''
            def test_callbacks():
                x, y = symbols('x y')
                assert Matrix([[1, 2]]).applyfunc(lambda e: 2*e) == Matrix([[2, 4]])
                assert Matrix(1, 2, lambda i, j: [x, y][j]) == Matrix([[x, y]])
        ''')
        cases = corpus['cases']
        self.assertEqual(cases[0]['args'][0]['t'], 'JsLambda')
        table = cases[1]['args'][2]
        self.assertEqual(table['t'], 'JsTable')
        self.assertEqual([[a['p'] for a in args] for args, _ in table['entries']], [['0', '0'], ['0', '1']])
        self.assertEqual([value['name'] for _, value in table['entries']], ['x', 'y'])
        self.assertEqual(corpus['extraction']['reasons'], {})
        self.assertEqual(unit.fill_tables({'args': [None]}, {0: [((object(),), 1)]}), {'reason': 'unserializable-input'})

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

    def test_deprecated_matrix_inputs_are_omitted(self):
        corpus = self.extract('''
            from sympy.testing.pytest import warns_deprecated_sympy
            from sympy.matrices.normalforms import invariant_factors
            def test_deprecated():
                x = Symbol('x')
                with warns_deprecated_sympy():
                    m = Matrix([[Poly(x), Poly(1, x)]])
                assert invariant_factors(m, domain=QQ[x]) == (1,)
                n = Matrix([[2, 4]])
                setattr(n, 'ring', ZZ)
                assert invariant_factors(n) == (2,)
                assert invariant_factors(Matrix([[2, 4]])) == (2,)
        ''')
        self.assertEqual(corpus['extraction']['reasons'], {'deprecated-api': 2})
        self.assertEqual([c['fn'] for c in corpus['cases']], ['invariant_factors'])

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
            def test_cant_sympify():
                from sympy.core.sympify import CantSympify
                class no(float, CantSympify):
                    pass
                raises(SympifyError, lambda: sympify(no(1.2)))
        ''')
        self.assertEqual(len(corpus['cases']), 0)
        self.assertGreater(corpus['extraction']['examined'], 0)
        self.assertEqual(corpus['extraction']['reasons']['unserializable-input'], 1)
        # the records cross process boundaries during a full extraction
        import pickle
        pickle.dumps(corpus)

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
            def test_unseeded_generator():
                m = randMatrix(3)
                assert m.det() != Rational(1, 2)
        '''
        first = self.extract(source)
        self.assertEqual(first, self.extract(source))
        self.assertEqual(sum(c['fn'] == '.det' for c in first['cases']), 1)


class CategoryShardTests(unittest.TestCase):
    def test_pinned_printing_and_parsing_files_have_explicit_scope_decisions(self):
        root = Path(unit.sympy.__file__).parent
        for category in ('printing', 'parsing'):
            for path in (root / category).rglob('test_*.py'):
                self.assertIn(path.relative_to(root).as_posix(), unit.FILE_SCOPE)

    def test_plotting_may_use_numpy_but_not_matplotlib(self):
        source = '''
import numpy as np
from sympy.external import import_module
matplotlib = import_module('matplotlib')

def test_numpy():
    assert np.sqrt(4) == 2

def test_matplotlib():
    if not matplotlib:
        return
    assert matplotlib is not None
'''
        tree = unit.ast.parse(source)
        functions = {n.name: n for n in tree.body if isinstance(n, unit.ast.FunctionDef)}
        for category, numpy_reason in (('plotting', None), ('core', 'optional-dependency')):
            optional = unit.OPTIONAL - unit.ALLOWED_OPTIONAL.get(category, set())
            aliases = unit.optional_aliases(tree, optional)
            self.assertEqual(unit.skip_reason(functions['test_numpy'], aliases, functions, optional=optional), numpy_reason)
            self.assertEqual(unit.skip_reason(functions['test_matplotlib'], aliases, functions, optional=optional), 'optional-dependency')

    def test_discovery_includes_nested_areas_and_excludes_mixed_files(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            names = ["polys/tests/test_z.py", "polys/agca/tests/test_a.py",
                     "tensor/array/expressions/tests/test_array.py", "solvers/ode/tests/test_ode.py",
                     "strategies/branch/tests/test_core.py", "functions/special/tests/test_gamma.py",
                     "printing/tests/test_str.py", "printing/pretty/tests/test_pretty.py",
                     "printing/tests/test_c.py", "parsing/tests/test_latex.py",
                     "parsing/tests/test_mathematica.py", "parsing/tests/test_sympy_parser.py",
                     "stats/sampling/tests/test_sample.py", "utilities/_compilation/tests/test_build.py",
                     "categories/tests/test_drawing.py", "physics/tests/test_units.py",
                     "multipledispatch/tests/test_core.py"]
            for name in names:
                path = root / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.touch()
            included, excluded = unit.discover(root)
            self.assertEqual([p.relative_to(root).as_posix() for p in included['polys']], names[:2])
            self.assertEqual(len(included['printing']), 2)
            self.assertEqual(len(included['parsing']), 3)
            self.assertEqual(len(included['categories']), 1)
            self.assertEqual(len(excluded), 5)
            self.assertEqual(sum(map(len, included.values())) + len(excluded), len(names))
            self.assertTrue(all(e['reason'] for e in excluded))

    def test_audit_uses_top_level_category_and_includes_empty_areas(self):
        events = [{"category": "tensor", "module": "sympy.tensor.array.tests.test_x", "reason": "non-call-expression"}]
        corpus = unit.corpus_from_events(events, [], 1, ['tensor', 'unify'])
        self.assertEqual(set(corpus['extraction']['categories']), {'tensor', 'unify'})
        self.assertEqual(corpus['extraction']['categories']['tensor']['examined'], 1)
        self.assertEqual(corpus['extraction']['categories']['unify']['examined'], 0)

    def test_shards_round_trip_record_order_ascii_and_byte_boundaries(self):
        cases = [{"category": "sets", "expected": value} for value in ['α', '\ud800', 'x' * 60, 'z']]
        corpus = unit.corpus_from_events(cases, [], 4, ['sets'])
        with tempfile.TemporaryDirectory() as tmp:
            directory = Path(tmp)
            summary = unit.write_category(directory, 'sets', corpus, max_bytes=130)
            restored = []
            for shard in summary['shards']:
                path = directory / shard['file']
                self.assertLessEqual(path.stat().st_size, 130)
                text = path.read_text(encoding='ascii')
                restored.extend(json.loads(text))
                self.assertEqual(len(text.splitlines()), shard['cases'] + 2)
            self.assertEqual(restored, cases)
            self.assertEqual(summary['cases'], len(cases))
            self.assertEqual(json.loads((directory / summary['auditFile']).read_text()), {'omitted': [], 'tests': []})
            with self.assertRaisesRegex(ValueError, 'Single sets case'):
                unit.write_category(directory, 'sets', corpus, max_bytes=20)

    def test_nonfinite_json_is_rejected_and_other_category_files_are_retained(self):
        with tempfile.TemporaryDirectory() as tmp:
            directory = Path(tmp)
            retained = directory / 'core.json'
            retained.write_bytes(b'[1]\n')
            corpus = unit.corpus_from_events([], [], 0, ['sets'])
            unit.write_category(directory, 'sets', corpus)
            self.assertEqual(retained.read_bytes(), b'[1]\n')
            self.assertEqual(json.loads((directory / 'sets.json').read_text()), [])
            with self.assertRaises(ValueError):
                unit.json_line({'bad': float('nan')})

    def test_legacy_migration_keeps_cases_and_omissions_without_execution(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            path = root / 'core/tests/test_legacy.py'
            path.parent.mkdir(parents=True)
            path.write_text('def test_legacy():\n    assert Integer(1) == 1\n')
            case = {'module': 'sympy.core.tests.test_legacy', 'category': 'core', 'test': 'test_legacy',
                    'line': 2, 'src': 'assert Integer(1) == 1', 'fn': 'Integer', 'args': [],
                    'kwargs': {}, 'expected': '1', 'op': '=='}
            tests = [{'module': case['module'], 'test': case['test'], 'status': 'completed'}]
            baseline = root / 'baseline.json'
            baseline.write_text(json.dumps(unit.corpus_from_events([case], tests, 1)))
            with patch.object(unit.sympy, '__file__', str(root / '__init__.py')), patch.object(unit, 'execute_source') as execute:
                corpus = unit.extract_category('core', [path], 1, baseline)
            execute.assert_not_called()
            self.assertEqual(corpus['cases'], [case])
            self.assertEqual(list(corpus['cases'][0]), list(case))
            self.assertEqual(corpus['extraction']['sourceSites'], 1)
            self.assertEqual(corpus['extraction']['retainedModules'], 1)

    def test_repeated_omissions_are_losslessly_compacted_and_repacking_is_idempotent(self):
        event = {'module': 'sympy.ntheory.tests.test_digits', 'category': 'ntheory',
                 'line': 1, 'src': 'assert f(n) == n', 'reason': 'duplicate'}
        corpus = unit.corpus_from_events([event, event, event], [], 1, ['ntheory'])
        with tempfile.TemporaryDirectory() as tmp:
            directory = Path(tmp)
            summary = unit.write_category(directory, 'ntheory', corpus)
            path = directory / summary['auditFile']
            audit = json.loads(path.read_text())
            self.assertEqual(audit['omitted'], [{**event, 'count': 3}])
            self.assertEqual(summary['examined'], 3)
            (directory / 'index.json').write_text(json.dumps({'categories': {'ntheory': summary}}))
            before = path.read_bytes()
            cases = (directory / 'ntheory.json').read_bytes()
            unit.compact_audits(directory, ['ntheory'])
            self.assertEqual(path.read_bytes(), before)
            self.assertEqual((directory / 'ntheory.json').read_bytes(), cases)

    def test_codegen_measures_only_the_c_math_functions(self):
        self.assertIn('codegen', unit.CATEGORIES)
        self.assertTrue(unit.file_scope(Path('codegen/tests/test_cfunctions.py'))[0])
        for name in ('codegen/tests/test_ast.py', 'codegen/tests/test_rewriting.py', 'codegen/tests/test_approximations.py'):
            keep, reason = unit.file_scope(Path(name))
            self.assertFalse(keep)
            self.assertEqual(reason, unit.EXCLUDED_AREAS['codegen'])

    def test_diffgeom_is_a_regular_base_category(self):
        self.assertIn('diffgeom', unit.CATEGORIES)
        self.assertNotIn('diffgeom', unit.EXCLUDED_AREAS)
        self.assertTrue(unit.file_scope(Path('diffgeom/tests/test_diffgeom.py'))[0])
        source = """
from sympy.diffgeom import Differential
from sympy.diffgeom.rn import R2

def test_field():
    assert R2.e_x(R2.x) == 1
    assert Differential(R2.x).rcall(R2.e_x) == 1
"""
        events, tests, sites = unit.execute_source(
            source, 'sympy.diffgeom.tests.test_fixture', 'diffgeom', 'test_fixture.py')
        corpus = unit.corpus_from_events(events, tests, sites, ['diffgeom'])
        self.assertEqual(len(corpus['cases']), 2)
        self.assertTrue(all(c['category'] == 'diffgeom' for c in corpus['cases']))
        self.assertTrue(all(c['self']['t'] == 'Diffgeom' for c in corpus['cases']))

    def test_unknown_categories_are_rejected(self):
        with patch.dict(os.environ, {'PYTHONHASHSEED': '0'}):
            with self.assertRaisesRegex(ValueError, 'Unknown categories'):
                unit.main('unused', only=['calculus,typo'])


if __name__ == '__main__':
    unittest.main()
