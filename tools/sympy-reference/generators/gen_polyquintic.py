"""Regenerate Dummit's coefficient tables from the installed SymPy 1.14 source."""
import ast
import inspect
import json
from pathlib import Path

import sympy as sp
from sympy.polys import polyquinticconst

assert sp.__version__ == "1.14.0"
source = inspect.getsource(polyquinticconst)
cls = next(n for n in ast.parse(source).body if isinstance(n, ast.ClassDef))
variables = sp.symbols("p q r s")
x = sp.Symbol("x")


def terms(expr):
    result = []
    for powers, coefficient in sp.Poly(expr, *variables).terms():
        assert all(0 <= k < 32 for k in powers)
        code = sum(k << (5 * i) for i, k in enumerate(powers))
        result.append(f"[{coefficient}n, {code}]")
    return "[" + ", ".join(result) + "]"


tables = []
for method in cls.body:
    if not isinstance(method, ast.FunctionDef) or method.name not in ("f20", "b", "o", "c", "F"):
        continue
    values = {}
    for node in method.body:
        if not isinstance(node, ast.Assign):
            continue
        target = node.targets[0]
        if isinstance(target, ast.Subscript) or isinstance(target, ast.Name) and target.id in ("f20", "F"):
            values[ast.unparse(target)] = sp.sympify(ast.get_source_segment(source, node.value), locals=dict(zip("pqrs", variables)))
    if method.name == "f20":
        rows = sp.Poly(values["f20"], x).all_coeffs()
    elif method.name == "F":
        rows = [values["F"]]
    elif method.name == "b":
        rows = [values[f"b[{i}][{j}]"] for i in range(1, 5) for j in range(6)]
    else:
        rows = [values[f"{method.name}[{j}]"] for j in range(6)]
    tables.append(f"const {method.name.upper()}_TABLE: readonly (readonly Term[])[] = [\n" + ",\n".join("  " + terms(row) for row in rows) + "\n];")

target = (Path(__file__).resolve().parents[3] / "packages/symjs/src/polys/polyquinticconst.ts")
prefix = target.read_text().split("// BEGIN GENERATED COEFFICIENT TABLES")[0]
target.write_text(prefix + "// BEGIN GENERATED COEFFICIENT TABLES\n// Regenerate with python3 tools/sympy-reference/generators/gen_polyquintic.py (SymPy 1.14.0).\n" + "\n\n".join(tables) + "\n")

# Independent reference values exercise every table coefficient, including fractions.
fixtures = []
for coefficients in [(2, 3, 5, 7), (sp.Rational(1, 2), -3, sp.Rational(5, 7), -11)]:
    p, q, r, s = coefficients
    quintic = polyquinticconst.PolyQuintic(sp.Poly(x**5 + p*x**3 + q*x**2 + r*x + s, x))
    assert quintic.a == [-v for v in quintic.b[1]]
    fixtures.append({
        "coefficients": list(map(str, coefficients)),
        "a": list(map(str, quintic.a)), "b": [list(map(str, row)) for row in quintic.b],
        "c": list(map(str, quintic.c)), "o": list(map(str, quintic.o)), "F": str(quintic.F),
        "f20": list(map(str, quintic.f20.all_coeffs())), "l0": str(quintic.l0(2)),
        "T": list(map(str, quintic.T(2, 3))),
        "order": float(quintic.order(2, 3)), "uv": list(map(float, quintic.uv(2, 3))),
    })
(Path(__file__).resolve().parents[3] / "packages/symjs/tests/polys/polyquinticconst-cases.json").write_text(json.dumps(fixtures, indent=2) + "\n")
