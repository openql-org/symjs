# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
"""Extraction contracts checked against the pinned SymPy reference itself."""

import doctest
import copy
import importlib
import json
import signal
import tempfile
import textwrap
import unittest
from pathlib import Path
from unittest.mock import patch

import sympy
import extract


class ExtractTests(unittest.TestCase):
    def test_serializes_hypergeometric_bases_and_differential_operators(self):
        from sympy.simplify.hyperexpand import FormulaCollection, Hyper_Function, G_Function, reduce_order_meijer
        from sympy.functions.special.hyper import HyperRep_power1
        formula = FormulaCollection().lookup_origin(Hyper_Function([1], []))
        data = extract.ser(formula)
        self.assertEqual(data["cls"], "Formula")
        self.assertEqual(data["args"][0]["cls"], "Hyper_Function")
        self.assertEqual(data["args"][2], extract.ser(list(formula.B)))
        self.assertEqual(data["args"][3], extract.ser(list(formula.C)))
        self.assertEqual(data["args"][4], extract.ser(formula.M.tolist()))
        self.assertEqual(extract.ser(HyperRep_power1(-1, sympy.Symbol("z")))["cls"], "HyperRep")
        reduced, operators = reduce_order_meijer(G_Function([3, 4], [5, 6], [3, 4], [1, 8]))
        self.assertEqual(extract.ser(reduced)["cls"], "G_Function")
        self.assertTrue(operators)
        self.assertEqual(extract.ser(operators[0])["cls"], "Operator")

    def extract_examples(self, source, module="sympy.core.expr"):
        parser = doctest.DocTestParser()
        sources = [source] if isinstance(source, str) else source
        tests = [parser.get_doctest(textwrap.dedent(s), {}, module, None, 0) for s in sources]
        handler = signal.getsignal(signal.SIGALRM)
        try:
            with tempfile.TemporaryDirectory() as tmp:
                target = Path(tmp) / "corpus.json"
                with patch.dict(extract.MODULES, {module: "test"}, clear=True), \
                        patch.object(extract, "ONLY", []), \
                        patch.object(doctest.DocTestFinder, "find", return_value=tests):
                    extract.main(target)
                corpus = json.loads(target.read_text())
        finally:
            signal.signal(signal.SIGALRM, handler)
        self.assertEqual(corpus["extraction"]["examined"],
                         len(corpus["cases"]) + sum(corpus["extraction"]["reasons"].values()))
        return corpus

    def test_assignment_displays_preserve_function_method_and_unpacking(self):
        corpus = self.extract_examples("""
            >>> from sympy.integrals.quadrature import gauss_chebyshev_t
            >>> x, w = gauss_chebyshev_t(3, 5)
            >>> x
            [0.86602, 0, -0.86602]
            >>> w
            [1.0472, 1.0472, 1.0472]
            >>> A = Matrix([[1, 2], [3, 4]])
            >>> [L, U, perm] = A.LUdecomposition()
            >>> L
            Matrix([[1, 0], [3, 1]])
            >>> U
            Matrix([[1, 2], [0, -2]])
            >>> perm
            []
            >>> answer = factor(12)
            >>> answer
            12
            >>> factor = factor(2)
            >>> factor
            2
        """, "sympy.integrals.quadrature")
        cases = corpus["cases"]
        self.assertEqual([c["src"] for c in cases], ["x", "w", "L", "U", "perm", "answer", "factor"])
        self.assertEqual([c["fn"] for c in cases], ["gauss_chebyshev_t"] * 2 + [".LUdecomposition"] * 3 + ["factor"] * 2)
        self.assertEqual([c.get("pick") for c in cases], [0, 1, 0, 1, 2, None, None])
        self.assertEqual(cases[0]["args"], [extract.ser(3), extract.ser(5)])
        self.assertEqual(cases[0]["args"], cases[1]["args"])
        self.assertEqual(cases[2]["self"], extract.ser(sympy.Matrix([[1, 2], [3, 4]])))
        self.assertEqual(cases[2]["expected"], str(sympy.Matrix([[1, 0], [3, 1]])))
        self.assertNotIn("pick", cases[-1])

        corpus = self.extract_examples("""
            >>> columns = Matrix([[1, 2], [3, 4]]).columnspace()
            >>> columns
            [Matrix([[1], [3]]), Matrix([[2], [4]])]
        """)
        self.assertEqual(corpus["cases"][0]["expected"], str(sympy.Matrix([[1, 2], [3, 4]]).columnspace()))
        self.assertIn("\n", corpus["cases"][0]["expected"])

    def test_assignment_snapshots_arguments_keywords_and_receiver_before_mutation(self):
        calls = []

        def mutate(a, options):
            calls.append(1)
            a.append(3)
            options.append(4)
            return a, options

        with patch.object(sympy, "factor", mutate):
            corpus = self.extract_examples("""
                >>> a, b = [1], [2]
                >>> x, w = factor(a, options=b)
                >>> x
                [1, 3]
                >>> w
                [2, 4]
                >>> values = [5, 6]
                >>> value = values.pop(0)
                >>> value
                5
            """)
        x, w, value = corpus["cases"]
        self.assertEqual(calls, [1])
        for case in (x, w):
            self.assertEqual(case["args"], [extract.ser([1])])
            self.assertEqual(case["kwargs"], {"options": extract.ser([2])})
        self.assertEqual(x["expected"], "[1, 3]")
        self.assertEqual(w["expected"], "[2, 4]")
        self.assertEqual(value["self"], extract.ser([5, 6]))
        self.assertEqual(value["args"], [extract.ser(0)])

    def test_assignment_displays_share_text_and_unsupported_result_rules(self):
        corpus = self.extract_examples("""
            >>> text = latex(Symbol('x') + 1)
            >>> text  # doctest: +NORMALIZE_WHITESPACE
            'x + 1'
            >>> value = factor(2)
            >>> value
            2
        """)
        self.assertEqual(corpus["cases"][0]["expected"], "x + 1")
        self.assertTrue(corpus["cases"][0]["text"])
        self.assertTrue(corpus["cases"][0]["ws"])
        self.assertNotIn("text", corpus["cases"][1])
        for result, reason in [(object(), "unsupported-result-type"), ([object()], "unstable-result-representation")]:
            with self.subTest(reason=reason), patch.object(sympy, "factor", lambda: result):
                corpus = self.extract_examples(">>> result = factor()\n>>> result\nopaque\n")
            self.assertEqual(corpus["cases"], [])
            self.assertEqual(corpus["extraction"]["reasons"][reason], 1)
        with patch.object(sympy, "factor", lambda arg: 1):
            corpus = self.extract_examples(">>> result = factor(object())\n>>> result\n1\n")
        self.assertEqual(corpus["cases"][0]["unsupportedArg"], "object")

    def test_assignment_displays_preserve_global_assumptions(self):
        from sympy.assumptions import global_assumptions
        before = set(global_assumptions)
        try:
            corpus = self.extract_examples("""
                >>> from sympy.assumptions import global_assumptions
                >>> x = Symbol('x')
                >>> global_assumptions.add(Q.real(x))
                >>> answer = ask(Q.real(x))
                >>> answer
                True
            """)
            case = next(c for c in corpus["cases"] if c["src"] == "answer")
            self.assertEqual(case["assume"], [extract.ser(sympy.Q.real(sympy.Symbol("x")))])
        finally:
            global_assumptions.clear()
            global_assumptions.update(before)

    def test_any_intervening_non_display_invalidates_the_assignment(self):
        intervening = [
            "a = 3", "x = 10", "a.append(3)", "del x", "import math",
            "factor(4)\n4", "other\n7", "pass", "raise ValueError()",
            "other  # doctest: +SKIP\n7", "other\nObject(...)",
            "x",  # no expected output: not a display
            "fresh = factor(9)", "x, w = factor(1)",  # failed unpacking
        ]
        for statement in intervening:
            with self.subTest(statement=statement):
                corpus = self.extract_examples(
                    ">>> a, other = [1], 7\n>>> x, w = symbols('x w')\n>>> x\nx\n"
                    f">>> {statement}\n>>> w\nw\n")
                self.assertIn("x", [c["src"] for c in corpus["cases"]])
                self.assertNotIn("w", [c["src"] for c in corpus["cases"]])
                self.assertIn({"module": "sympy.core.expr", "src": "w", "reason": "non-call-expression"},
                              corpus["extraction"]["omitted"])

    def test_assignments_do_not_leak_between_doctests_or_without_output(self):
        corpus = self.extract_examples([">>> x = factor(2)\n>>> x\n", ">>> x\nx\n"])
        self.assertEqual(corpus["cases"], [])

    def test_assignment_capture_rejects_unsupported_targets_and_nonpublic_calls(self):
        assignments = [
            "x = factor(*[2])", "x = factor(2, **{})", "x = int(2)",
            "x = Symbol('x')._hashable_content()", "x = 1 + 2",
            "x = y = factor(2)", "x, *tail = symbols('x y')",
            "(x, (y, z)) = (Symbol('x'), symbols('y z'))",
            "x = factor(2); y = 1", "values[0] = factor(2)",
            "x, x = symbols('x y')",
        ]
        for assignment in assignments:
            with self.subTest(assignment=assignment):
                corpus = self.extract_examples(f">>> values = [0]\n>>> {assignment}\n>>> x\nx\n")
                self.assertEqual(corpus["cases"], [])

    def test_serializes_combinatorial_receivers_and_structured_sets(self):
        from sympy.combinatorics import Subset, GrayCode, Prufer
        self.assertEqual(extract.ser(Subset([2], [1, 2]))["cls"], "Subset")
        self.assertEqual(extract.ser(GrayCode(4, rank=4)), {"t": "GrayCode", "n": 4, "current": "0110"})
        tree = [[0, 2], [0, 1], [1, 3]]
        self.assertEqual(extract.ser(Prufer(tree))["args"], [extract.ser(tree)])
        self.assertEqual(extract.ser(sympy.ProductSet(sympy.S.Integers, sympy.S.Rationals))["cls"], "ProductSet")
        self.assertEqual(extract.ser(sympy.S.Rationals), {"t": "NamedSet", "name": "Rationals"})
        self.assertEqual(extract.ser(slice(None, 5, 2))["start"], {"t": "Js", "v": None})

    def test_sat_serialization_freezes_mutable_search_state(self):
        from sympy.logic.algorithms.dpll2 import SATSolver
        solver = SATSolver([{1}, {-1, 2}], {1, 2}, set())
        before = extract.ser(solver)
        frozen = copy.deepcopy(before)
        solver.clauses[0].append(2)
        solver.variable_set[1] = True
        solver.lit_heap[0] = (17.0, 2)
        solver.var_settings.add(2)
        solver.sentinels[2].add(99)
        solver.lit_scores[2] = 5.0
        self.assertEqual(before, frozen)
        self.assertNotEqual(extract.ser(solver), frozen)

    def test_transform_preserves_symbolic_comparisons_and_rejects_opaque_code(self):
        from sympy.core.rules import Transform
        x = sympy.Symbol("x")
        self.assertEqual(extract.callback_expr(lambda x: x % 2 == 1, x), sympy.Eq(sympy.Mod(x, 2), 1))
        self.assertEqual(extract.callback_expr(lambda x: -x + 1, x), 1 - x)
        transform = extract.ser(Transform(lambda x: x + 1, lambda x: x % 2 == 1))
        self.assertEqual(transform["condition"]["t"], "Rel")
        with self.assertRaises(extract.Unsupported):
            extract.ser(Transform(lambda x: str(x)))
        with self.assertRaises(extract.Unsupported):
            extract.ser(Transform(lambda x: x, lambda x: bool(x)))

    def test_property_receivers_preserve_type_and_metadata(self):
        from sympy.combinatorics.partitions import Partition
        from sympy.polys.agca.extensions import FiniteExtension
        from sympy.stats.frv import FiniteDensity
        x = sympy.Symbol("x")
        self.assertEqual(extract.ser(Partition([1, 2], [3]))["t"], "Partition")
        self.assertEqual(extract.ser(FiniteExtension(sympy.Poly(x**2 + 1, x)))["t"], "FiniteExtension")
        self.assertEqual(extract.ser(FiniteDensity({sympy.S.One: sympy.S.One}))["t"], "FiniteDensity")
        self.assertEqual(extract.ser(sympy.Function("f", nargs=(2, 1)))["nargs"], [1, 2])
        self.assertNotIn("nargs", extract.ser(sympy.Function("f")))
        self.assertTrue(extract.ser(sympy.SparseMatrix([[1]]))["sparse"])
        self.assertNotIn("sparse", extract.ser(sympy.Matrix([[1]])))
        self.assertEqual(extract.ser(sympy.Symbol("i", below_fermi=True))["assume"], {"below_fermi": True})

    def test_public_definitions_need_not_be_top_level_exports(self):
        for module, name in [
            ("sympy.simplify.fu", "TR10"),
            ("sympy.utilities.iterables", "common_prefix"),
            ("sympy.solvers.diophantine.diophantine", "diop_DN"),
            ("sympy.logic.boolalg", "ANFform"),
        ]:
            with self.subTest(module=module, name=name):
                self.assertIn(name, extract.subpackage_public(module))
        names = extract.subpackage_public("sympy.simplify.fu")
        self.assertNotIn("_TR56", names)
        self.assertNotIn("Symbol", names)  # imported helper, not defined here

    def test_external_sampling_remains_outside_the_scope(self):
        self.assertTrue(extract.STATS_SAMPLING.isdisjoint(extract.subpackage_public("sympy.stats.rv")))

    def test_reference_calls_and_multiline_results_are_retained(self):
        x, y = sympy.symbols("x y")
        fu = importlib.import_module("sympy.simplify.fu")
        expected_fu = str(fu.TR10(sympy.sin(x + y)))
        expected_matrix = str(sympy.Matrix([[1, 2], [3, 4]]).columnspace())
        hyperexpand = importlib.import_module("sympy.simplify.hyperexpand")
        operators = str(hyperexpand.reduce_order(hyperexpand.Hyper_Function((1,), (1,))))
        self.assertIn(" object at 0x", operators)
        examples = {
            "sympy.simplify.fu":
                ">>> from sympy.simplify.fu import TR10\n"
                ">>> from sympy.abc import x, y\n"
                f">>> TR10(sin(x + y))\n{expected_fu}\n",
            "sympy.matrices.matrixbase":
                f">>> Matrix([[1, 2], [3, 4]]).columnspace()\n{expected_matrix}\n",
            "sympy.simplify.hyperexpand":
                ">>> from sympy.simplify.hyperexpand import reduce_order, Hyper_Function\n"
                f">>> reduce_order(Hyper_Function((1,), (1,)))\n{operators}\n",
        }
        parser = doctest.DocTestParser()

        def find(module):
            return [parser.get_doctest(examples[module.__name__], {}, module.__name__, None, 0)]

        handler = signal.getsignal(signal.SIGALRM)
        try:
            with tempfile.TemporaryDirectory() as tmp:
                target = Path(tmp) / "corpus.json"
                with patch.dict(extract.MODULES, {m: "test" for m in examples}, clear=True), \
                        patch.object(extract, "ONLY", []), \
                        patch.object(doctest.DocTestFinder, "find", side_effect=find):
                    extract.main(target)
                corpus = json.loads(target.read_text())
                # The normal expansion command uses the destination as its own
                # baseline; loading it before writing must preserve all records.
                with patch.dict(extract.MODULES, {m: "test" for m in examples}, clear=True), \
                        patch.object(extract, "ONLY", []), \
                        patch.object(doctest.DocTestFinder, "find", side_effect=find):
                    extract.main(target, target)
                replayed = json.loads(target.read_text())
                self.assertEqual(replayed["cases"], corpus["cases"])
                self.assertEqual(replayed["extraction"]["preservedReferences"], [])
        finally:
            signal.signal(signal.SIGALRM, handler)
        self.assertEqual([c["fn"] for c in corpus["cases"]], ["TR10", ".columnspace"])
        self.assertEqual([c["expected"] for c in corpus["cases"]], [expected_fu, expected_matrix])
        self.assertIn("\n", corpus["cases"][1]["expected"])
        self.assertNotIn("multiline-output", corpus["extraction"]["reasons"])
        self.assertEqual(corpus["extraction"]["reasons"]["unstable-result-representation"], 1)
        self.assertEqual(corpus["extraction"]["examined"],
                         len(corpus["cases"]) + sum(corpus["extraction"]["reasons"].values()))

    def test_reference_version_is_pinned(self):
        with patch.object(sympy, "__version__", "0.0.0"):
            with self.assertRaisesRegex(RuntimeError, "pinned to SymPy 1.14.0"):
                extract.main("unused.json")

    def test_expansion_preserves_anonymous_dummy_inputs(self):
        def record():
            dummy = sympy.Dummy(real=True)
            extract.DUMMY_IDS.clear()
            return {"module": "sympy.core.symbol", "src": "d.is_real", "fn": ".is_real",
                    "self": extract.ser(dummy), "args": [], "kwargs": {}, "expected": str(dummy.is_real)}
        old, fresh = record(), record()
        self.assertNotEqual(old, fresh)
        actual, preserved = extract.preserve_references([fresh], [old])
        self.assertIs(actual[0], old)
        self.assertEqual(len(preserved), 1)
        # The expected value remains part of the matching key.
        with self.assertRaises(ValueError):
            extract.preserve_references([{**fresh, "expected": "False"}], [old])

    def test_expansion_preserves_the_existing_sample_without_accepting_changed_results(self):
        def record(value):
            return {"module": "sympy.stats.rv", "src": "samp in N.pspace.domain.set",
                    "fn": ".__contains__", "self": extract.ser(sympy.S.Reals),
                    "args": [extract.ser(value)], "kwargs": {}, "expected": str(value in sympy.S.Reals)}
        old, fresh = record(1.25), record(2.5)
        snapshot = copy.deepcopy(old)
        actual, preserved = extract.preserve_references([fresh], [old])
        self.assertIs(actual[0], old)
        self.assertEqual(old, snapshot)
        self.assertEqual(len(preserved), 1)
        with self.assertRaises(ValueError):
            extract.preserve_references([{**fresh, "expected": "False"}], [old])

    def test_expansion_retains_occurrences_and_rejects_other_input_changes(self):
        old = {"module": "sympy.functions.elementary.trigonometric", "src": "sin(0)",
               "fn": "sin", "args": [extract.ser(sympy.Integer(0))], "expected": str(sympy.sin(0))}
        extra = {"module": "sympy.functions.elementary.trigonometric", "src": "sin(pi/2)",
                 "fn": "sin", "args": [extract.ser(sympy.pi / 2)], "expected": str(sympy.sin(sympy.pi / 2))}
        actual, preserved = extract.preserve_references([extra, copy.deepcopy(old)], [old])
        self.assertEqual(actual, [old, extra])
        self.assertIs(actual[0], old)
        self.assertEqual(preserved, [])
        with self.assertRaises(ValueError):
            extract.preserve_references([old], [old, old])
        with self.assertRaises(ValueError):
            extract.preserve_references([extra], [old])

    def test_expansion_preserves_legacy_matrix_storage_without_losing_value_checks(self):
        old = {"module": "sympy.matrices.common", "src": "B.has(x)", "fn": ".has",
               "self": extract.ser(sympy.Matrix([[1]])), "args": [extract.ser(sympy.Symbol("x"))],
               "kwargs": {}, "expected": "False"}
        fresh = {**old, "self": extract.ser(sympy.SparseMatrix([[1]]))}
        actual, preserved = extract.preserve_references([fresh], [old])
        self.assertIs(actual[0], old)
        self.assertEqual(len(preserved), 1)
        for changed in [
            {**fresh, "self": extract.ser(sympy.SparseMatrix([[2]]))},
            {**fresh, "expected": "True"}, {**fresh, "args": [extract.ser(sympy.Symbol("y"))]},
        ]:
            with self.subTest(changed=changed), self.assertRaises(ValueError):
                extract.preserve_references([changed], [old])
        # Once storage metadata was recorded, it is part of the contract too.
        with self.assertRaises(ValueError):
            extract.preserve_references([old], [fresh])

    def test_expansion_preserves_legacy_unsupported_dmp_inputs(self):
        from sympy.polys.polyclasses import DMP
        receiver = extract.ser(sympy.Poly(sympy.Symbol("x")**2 + 1))
        old = {"module": "sympy.polys.polytools", "src": "a.per(DMP([ZZ(1), ZZ(1)], ZZ), gens=[y])",
               "fn": ".per", "self": receiver, "unsupportedArg": "DMP_Python",
               "expected": "Poly(y + 1, y, domain='ZZ')"}
        fresh = {k: v for k, v in old.items() if k != "unsupportedArg"}
        fresh.update(args=[extract.ser(DMP([sympy.ZZ(1), sympy.ZZ(1)], sympy.ZZ))],
                     kwargs={"gens": extract.ser([sympy.Symbol("y")])})
        actual, preserved = extract.preserve_references([fresh], [old])
        self.assertIs(actual[0], old)
        self.assertEqual(len(preserved), 1)
        for changed in [
            {**fresh, "self": extract.ser(sympy.Poly(sympy.Symbol("x")**2 + 2))},
            {**fresh, "expected": "Poly(y + 2, y, domain='ZZ')"},
            {**fresh, "src": "another_call()"}, {**fresh, "args": [extract.ser(1)]},
        ]:
            with self.subTest(changed=changed), self.assertRaises(ValueError):
                extract.preserve_references([changed], [old])

    def test_expansion_preserves_simultaneous_replacement_map_order_only(self):
        x, y = sympy.symbols("x y")
        old = {"module": "sympy.core.symbol", "src": "eqs.xreplace(mapping)", "fn": ".xreplace",
               "self": extract.ser(x + y), "args": [extract.ser({x: 1, y: 2})], "expected": "3"}
        fresh = {**old, "args": [extract.ser({y: 2, x: 1})]}
        actual, preserved = extract.preserve_references([fresh], [old])
        self.assertIs(actual[0], old)
        self.assertEqual(len(preserved), 1)
        with self.assertRaises(ValueError):
            extract.preserve_references([{**fresh, "args": [extract.ser({y: 1, x: 2})]}], [old])
        # Sequential substitutions must not get the same order-insensitive rule.
        with self.assertRaises(ValueError):
            extract.preserve_references([{**fresh, "fn": ".subs"}], [{**old, "fn": ".subs"}])


if __name__ == "__main__":
    unittest.main()
