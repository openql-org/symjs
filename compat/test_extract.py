# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
"""Extraction contracts checked against the pinned SymPy reference itself."""

import doctest
import copy
import importlib
import json
import signal
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import sympy
import extract


class ExtractTests(unittest.TestCase):
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


if __name__ == "__main__":
    unittest.main()
