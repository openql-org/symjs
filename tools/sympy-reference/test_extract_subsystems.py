"""Serialization of polynomial, tensor and set-arithmetic receivers."""
import unittest
import sympy as s
import extract
from sympy.tensor.tensor import TensorIndexType, TensorHead
from sympy.tensor.toperators import PartialDerivative
from sympy.polys.polymatrix import PolyMatrix
from sympy.polys.multivariate_resultants import DixonResultant, MacaulayResultant
from sympy.combinatorics.galois import S4TransitiveSubgroups, S6TransitiveSubgroups
from sympy.sets.setexpr import SetExpr


class SubsystemSerialization(unittest.TestCase):
    def test_tensor_derivative(self):
        L = TensorIndexType('L')
        A = TensorHead('A', [L])
        i = s.Symbol('i')
        value = PartialDerivative(A(i), A(i))
        tree = extract.ser(value)
        self.assertEqual(tree['cls'], 'PartialDerivative')
        self.assertEqual(tree['args'], [extract.ser(a) for a in value.args])
        self.assertEqual(tree['args'][0]['indices'][0]['name'], 'L_0')

    def test_polynomial_matrix_ring_and_entries(self):
        x = s.Symbol('x')
        matrix = PolyMatrix([[s.Poly(x, x), s.Poly(0, x)]])
        tree = extract.ser(matrix)
        self.assertEqual(tree['t'], 'PolyMatrix')
        self.assertEqual(tree['ring'], extract.ser(s.ZZ.poly_ring(x)))
        self.assertEqual(tree['entries'], extract.ser([[x, s.Integer(0)]]))

    def test_resultants_preserve_polynomial_order(self):
        x, y = s.symbols('x y')
        for cls, polys in [(DixonResultant, [x+y, x-y, x*y]),
                           (MacaulayResultant, [x+y, x-y])]:
            tree = extract.ser(cls(polys, [x,y]))
            self.assertEqual(tree['cls'], cls.__name__)
            self.assertEqual(tree['args'], [extract.ser(polys), extract.ser([x,y])])

    def test_set_wrapper_and_named_groups(self):
        wrapped = SetExpr(s.Interval(0, 1))
        self.assertEqual(extract.ser(wrapped), {'t':'PublicObject', 'cls':'SetExpression',
                                               'args':[extract.ser(wrapped.set)]})
        for name, degree in [(S4TransitiveSubgroups.V, 4), (S6TransitiveSubgroups.C6, 6)]:
            self.assertEqual(extract.ser(name), {'t':'TransitiveSubgroup', 'degree':degree, 'name':name.name})
