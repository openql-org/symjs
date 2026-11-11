"""Extension serialization preserves chart identity without changing base data."""
import ast
import importlib.util
from pathlib import Path
import unittest
from unittest.mock import patch

import extract
import sympy
from sympy.diffgeom import CoordSystem, Manifold, Patch
from sympy.diffgeom.rn import R2_r

spec = importlib.util.spec_from_file_location('diffgeom_extract', Path(__file__).parent / 'extend/diffgeom/extract.py')
dg = importlib.util.module_from_spec(spec)
spec.loader.exec_module(dg)


class DiffgeomExtractionTests(unittest.TestCase):
    def test_base_serializer_is_unchanged(self):
        x = sympy.Symbol('x')
        for value in (x, x + 1, sympy.Matrix([x, 2]), {'a': (x, 1)}):
            self.assertEqual(dg.serialize(value), extract.ser(value))

    def test_predefined_identity_and_chart_relations(self):
        self.assertEqual(dg.serialize(R2_r), {'t': 'Extension', 'ref': 'R2_r'})
        x = sympy.Symbol('x')
        chart = CoordSystem('A', Patch('P', Manifold('M', 1)), [x], {('A', 'B'): [(x,), (2*x,)]})
        with patch.object(extract, 'ser', dg.serialize):
            tree = dg.serialize(chart)
            symbol = dg.serialize(chart.symbols[0])
        self.assertEqual(tree['cls'], 'CoordSystem')
        self.assertEqual(tree['args'][3]['t'], 'Dict')
        self.assertEqual(symbol['cls'], 'CoordinateSymbol')

    def test_callable_field_is_a_public_call(self):
        field = R2_r.base_scalar(0)
        self.assertIsNone(dg.public_api_reason('f', {'f': field}, set()))
        self.assertEqual(dg.public_api_reason('not_an_api', {}, set()), 'not-exported-api')
        record = {'fn': 'f'}
        previous = extract.ser
        try:
            extract.ser = dg.serialize
            dg.serialize_call(record, ast.parse('f(p)', mode='eval').body,
                              {'f': field, 'p': R2_r.point([1, 2])}, [])
        finally:
            extract.ser = previous
        self.assertEqual(record['fn'], '.__call__')
        self.assertEqual(record['self']['cls'], 'BaseScalarField')


if __name__ == '__main__':
    unittest.main()
