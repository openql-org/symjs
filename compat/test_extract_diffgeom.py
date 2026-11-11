"""Base serialization preserves differential-geometry identity and relations."""
import ast
import unittest

import extract
import sympy
from sympy.diffgeom import CoordSystem, Manifold, Patch
from sympy.diffgeom.rn import R2_r


class DiffgeomExtractionTests(unittest.TestCase):
    def test_predefined_identity_and_chart_relations(self):
        self.assertEqual(extract.ser(R2_r), {'t': 'Diffgeom', 'ref': 'R2_r'})
        x = sympy.Symbol('x')
        chart = CoordSystem('A', Patch('P', Manifold('M', 1)), [x], {('A', 'B'): [(x,), (2*x,)]})
        tree = extract.ser(chart)
        symbol = extract.ser(chart.symbols[0])
        self.assertEqual(tree['cls'], 'CoordSystem')
        self.assertEqual(tree['args'][3]['t'], 'Dict')
        self.assertEqual(symbol['cls'], 'CoordinateSymbol')

    def test_callable_field_is_a_public_call(self):
        field = R2_r.base_scalar(0)
        self.assertIsNone(extract.public_api_reason('f', {'f': field}, set()))
        self.assertEqual(extract.public_api_reason('not_an_api', {}, set()), 'not-exported-api')
        record = {'fn': 'f'}
        extract.serialize_call(record, ast.parse('f(p)', mode='eval').body,
                               {'f': field, 'p': R2_r.point([1, 2])}, [])
        self.assertEqual(record['fn'], '.__call__')
        self.assertEqual(record['self']['cls'], 'BaseScalarField')

    def test_diffgeom_is_in_the_base_inventory(self):
        for module in ('sympy.diffgeom', 'sympy.diffgeom.diffgeom', 'sympy.diffgeom.rn'):
            self.assertEqual(extract.MODULES[module], 'diffgeom')
            self.assertIn('Manifold', extract.subpackage_public(module))
        self.assertIn({'name': 'Manifold', 'category': 'diffgeom'}, extract.api_inventory())


if __name__ == '__main__':
    unittest.main()
