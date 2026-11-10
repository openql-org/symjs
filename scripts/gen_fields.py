"""Generate rational function field references with SymPy 1.14.0."""
import json
from pathlib import Path
import sympy as s
from sympy.polys.fields import field, FracField, sfield

assert s.__version__ == '1.14.0'
references = {}
def record(name, value):
    references[name] = str(value)

F, x, y, z = field('x y z', s.ZZ)
f = (x**2 + 3*y)/z
for name, value in {
    'field': F, 'zero': F.zero, 'one': F.one,
    'fraction': f, 'derivative': ((x**2+y)/(z+1)).diff(x),
    'quotient_derivative': ((x+1)/(x**2+1)).diff(x),
    'evaluate': f.evaluate(x, 0), 'evaluate_reordered': f.evaluate([(z, 2), (x, 1)]),
    'subs': f.subs(x, 0), 'subs_list': f.subs([(x, 1), (y, 2)]),
    'ground_rational': F(s.Rational(2, 3)),
    'cancel_sign': F((2*x.numer**2-2, -4*x.numer+4)),
    'raw': F.raw_new(x.numer**2-1, x.numer-1),
    'raw_zero': F.raw_new(F.ring.zero, x.numer),
    'negative_power': (-x)**-2, 'negative_odd_power': (-x)**-1,
    'compound_denominator': x/(2*y), 'power_denominator': x/y**2,
    'negative_denominator': F.raw_new(x.numer, -F.ring.one),
    'reordered': f.set_field(FracField('z y x', s.QQ)),
    'domain': F.to_domain(),
}.items(): record(name, value)
# Upstream FracElement.evaluate fails on the last generator (upstream XFAIL).
# Independently evaluate the ordinary SymPy expression instead.
record('evaluate_all', f.as_expr().subs(dict(zip(F.symbols, [1, 1, 2]))))
sx, sy = s.symbols('x y')
A = FracField([s.sqrt(sx), 1/sy], s.ZZ)
record('non_symbol_expression', A.from_expr(sx**s.Rational(3, 2)+sy).as_expr())
record('modular_quotient', s.GF(5).to_sympy(s.GF(5).quo(s.GF(5)(2), s.GF(5)(3))))
for name, domain in [('real', s.RR), ('expression', s.EX)]:
    K, t = field('t', domain)
    record(name+'_arithmetic', (t+1)/(t-1)+s.Rational(1,2))
K, t = field('t', s.GF(5))
record('positive_characteristic_derivative', (t**5+1).diff(t))
# symjs stores ground coefficients as expressions. Compare exact values;
# PythonMPQ.__eq__(mpf) is type-sensitive even for the exact value 1/2.
references['ground_equalities'] = [s.Rational(s.Float(1)) == 1,
    s.Rational(1,2) == s.Rational(s.Float(0.5)),
    s.Rational(s.Float(0.1)) == s.Rational(1,10), sx == sx, sx == sy, sx == 1, 1 == sx]

operations = []
for domain_name, domain in [('ZZ', s.ZZ), ('QQ', s.QQ), ('GF(5)', s.GF(5))]:
    K, a, b = field('x y', domain)
    for lhs, rhs in [
        ('(x+1)/(x-1)', '(x-1)/(x+1)'),
        ('(x+y)/(x*y)', '(x-y)/(x*y)'),
        ('0', '(x+1)/(y+1)'), ('x/y', '2' if domain_name == 'GF(5)' else '2/3'),
        ('(x*y+1)/(x+y)', '(x+y)/(x*y+1)'),
    ]:
        A, B = (K.from_expr(s.sympify(e)) for e in [lhs, rhs])
        for op, value in [('add', A+B), ('sub', A-B), ('mul', A*B), ('div', A/B)]:
            operations.append(dict(domain=domain_name, lhs=lhs, rhs=rhs, op=op,
                result=str(value), numer=str(value.numer), denom=str(value.denom)))
references['operations'] = operations

inferred = []
x, y = s.symbols('x y')
for expression, gens, options in [
    ((x**2-1)/(x-1), (), {}), ((x+1)/(y+1), (), {}),
    (x/s.Integer(2), (), {}), ((x+1)/(y+1), (y, x), {'domain': s.QQ, 'order': 'grlex'}),
    ((x+s.log(x))/x**2, (), {}),
    ((x*s.log(x)+4*x**2)*s.exp(1/x+s.log(x)/3)/x**2, (), {}),
    (s.exp(x)*s.exp(s.exp(x)+1+s.log(s.exp(x)+3)/2)**2/(s.exp(x)+3), (), {}),
    ((x+1)/(x*(x+s.log(x))**s.Rational(3,2))-1/(x*s.log(x)**2), (), {}),
]:
    K, value = sfield(expression, *gens, **options)
    inferred.append(dict(input=str(expression), gens=[str(g) for g in gens],
        options={k:str(v) for k,v in options.items()}, field=str(K), result=str(value)))
references['inferred'] = inferred
for name, exprs in [('list', [x/2, (x+1)/(y-1)]), ('constant', s.Rational(1, 2)), ('empty', [])]:
    K, values = sfield(exprs)
    record('inferred_'+name+'_field', K)
    record('inferred_'+name, values)

path = Path('packages/symjs/tests/polys/fields.references.json')
path.write_text(json.dumps(references, indent=2)+'\n')
