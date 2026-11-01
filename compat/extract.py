#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
"""Extract a SymPy compatibility corpus from SymPy's own doctests.

For every doctest example in the in-scope modules whose source is a single
call ``f(args...)`` or method call ``obj.m(args...)``, the arguments are
evaluated in the doctest namespace and serialized to a JSON tree. The
expected output is ``str()`` of the result computed by the installed SymPy.

Usage: python3 compat/extract.py compat/corpus.json
"""

import os

os.environ.setdefault("MPLBACKEND", "Agg")  # doctests that plot must not open windows

import ast
import doctest
import signal
import importlib
import json
import sys
import warnings

import sympy
from sympy import Basic, MatrixBase

# module -> category
MODULES = {
    # core
    "sympy.core.add": "core",
    "sympy.core.mul": "core",
    "sympy.core.power": "core",
    "sympy.core.expr": "core",
    "sympy.core.basic": "core",
    "sympy.core.function": "core",
    "sympy.core.numbers": "core",
    "sympy.core.symbol": "core",
    "sympy.core.relational": "core",
    "sympy.core.evalf": "core",
    "sympy.core.exprtools": "core",
    "sympy.core.sympify": "core",
    "sympy.core.intfunc": "core",
    # elementary functions
    "sympy.functions.elementary.complexes": "functions",
    "sympy.functions.elementary.exponential": "functions",
    "sympy.functions.elementary.trigonometric": "functions",
    "sympy.functions.elementary.hyperbolic": "functions",
    "sympy.functions.elementary.miscellaneous": "functions",
    "sympy.functions.elementary.integers": "functions",
    "sympy.functions.elementary.piecewise": "functions",
    # simplification
    "sympy.simplify.simplify": "simplify",
    "sympy.simplify.radsimp": "simplify",
    "sympy.simplify.trigsimp": "simplify",
    "sympy.simplify.powsimp": "simplify",
    "sympy.simplify.ratsimp": "simplify",
    "sympy.simplify.sqrtdenest": "simplify",
    "sympy.polys.rationaltools": "simplify",
    "sympy.polys.partfrac": "simplify",
    # polynomials
    "sympy.polys.polytools": "polys",
    "sympy.polys.polyroots": "polys",
    "sympy.polys.polyfuncs": "polys",
    # solvers
    "sympy.solvers.solvers": "solvers",
    "sympy.solvers.solveset": "solvers",
    "sympy.solvers.ode.ode": "ode",
    "sympy.solvers.recurr": "solvers",
    "sympy.solvers.polysys": "solvers",
    "sympy.solvers.inequalities": "solvers",
    # calculus
    "sympy.integrals.integrals": "calculus",
    "sympy.series.limits": "calculus",
    "sympy.series.series": "calculus",
    "sympy.series.order": "calculus",
    "sympy.concrete.summations": "calculus",
    "sympy.concrete.products": "calculus",
    "sympy.calculus.util": "calculus",
    "sympy.calculus.singularities": "calculus",
    # linear algebra
    "sympy.matrices.matrixbase": "matrices",
    "sympy.matrices.dense": "matrices",
    "sympy.matrices.eigen": "matrices",
    "sympy.matrices.decompositions": "matrices",
    "sympy.matrices.solvers": "matrices",
    "sympy.matrices.determinant": "matrices",
    "sympy.matrices.reductions": "matrices",
    "sympy.matrices.subspaces": "matrices",
    "sympy.matrices.inverse": "matrices",
    # combinatorial / special functions (second tier)
    "sympy.functions.combinatorial.factorials": "special",
    "sympy.functions.combinatorial.numbers": "special",
    "sympy.functions.special.gamma_functions": "special",
    "sympy.functions.special.error_functions": "special",
}

ASSUMPTION_KEYS = ["real", "positive", "negative", "nonnegative", "nonpositive", "integer", "commutative"]


class Unsupported(Exception):
    pass


def ser(o):
    """Serialize a SymPy object (or Python value) into a JSON tree."""
    from sympy import Float, Integer, Rational, Symbol, Tuple
    from sympy.core.relational import Relational

    if isinstance(o, bool):
        return {"t": "Py", "v": o}
    if isinstance(o, int):
        return {"t": "Rational", "p": str(o), "q": "1"}
    if isinstance(o, float):
        return {"t": "Float", "v": o}
    if isinstance(o, str):
        return {"t": "Str", "v": o}
    if isinstance(o, (list, tuple, Tuple)):
        return {"t": "Tuple", "items": [ser(i) for i in o]}
    if isinstance(o, dict):
        return {"t": "Dict", "items": [[ser(k), ser(v)] for k, v in o.items()]}
    if isinstance(o, MatrixBase):
        return {"t": "Matrix", "rows": [[ser(o[i, j]) for j in range(o.cols)] for i in range(o.rows)]}
    from sympy.core.function import UndefinedFunction as _UF
    if isinstance(o, _UF):
        return {"t": "UFnClass", "name": o.__name__}
    if isinstance(o, sympy.Poly):
        return {"t": "Poly", "expr": ser(o.as_expr()), "gens": [ser(g) for g in o.gens], "domain": str(o.get_domain()), "pure": isinstance(o, sympy.PurePoly)}
    if not isinstance(o, Basic):
        raise Unsupported(type(o).__name__)
    if o.is_Symbol and type(o) is Symbol:
        a = {k: True for k in ASSUMPTION_KEYS if o._assumptions_orig.get(k) is True}
        if o._assumptions_orig.get("commutative") is False:
            a["commutative"] = False
        a.pop("commutative", None) if a.get("commutative") is True else None
        return {"t": "Symbol", "name": o.name, "assume": a}
    if isinstance(o, (Integer, Rational)) and o.is_Rational:
        return {"t": "Rational", "p": str(o.p), "q": str(o.q)}
    if isinstance(o, Float):
        return {"t": "Float", "v": float(o)}
    named = {sympy.pi: "pi", sympy.E: "E", sympy.I: "I", sympy.oo: "oo", -sympy.oo: "-oo", sympy.zoo: "zoo", sympy.nan: "nan"}
    for k, v in named.items():
        if o == k and type(o) is type(k):
            return {"t": "Const", "name": v}
    from sympy.core.function import AppliedUndef, UndefinedFunction
    if isinstance(o, UndefinedFunction):
        return {"t": "UFnClass", "name": o.__name__}
    if isinstance(o, AppliedUndef):
        return {"t": "UFn", "name": type(o).__name__, "args": [ser(a) for a in o.args]}
    if isinstance(o, sympy.Derivative):
        return {"t": "Derivative", "expr": ser(o.expr), "vc": [[ser(v), int(n)] for v, n in o.variable_count]}
    if o is sympy.true or o is sympy.false:
        return {"t": "Py", "v": bool(o)}
    if isinstance(o, Relational):
        return {"t": "Rel", "op": type(o).__name__, "args": [ser(a) for a in o.args]}
    name = type(o).__name__
    if o.is_Add or o.is_Mul or o.is_Pow:
        return {"t": name, "args": [ser(a) for a in o.args]}
    if isinstance(o, sympy.exp):
        return {"t": "Fn", "name": "exp", "args": [ser(a) for a in o.args]}
    if isinstance(o, (sympy.Sum, sympy.Product)):
        return {"t": "Fn", "name": name, "args": [ser(o.function)] + [ser(tuple(l)) for l in o.limits]}
    if o.is_Function or name in ("Piecewise", "Integral", "Derivative", "Limit", "Order", "Sum", "Product"):
        return {"t": "Fn", "name": name, "args": [ser(a) for a in o.args]}
    raise Unsupported(name)


PUBLIC = set(sympy.__all__)


def api_inventory():
    """In-scope public API: top-level names from the in-scope modules plus public Expr/Matrix methods."""
    out = []
    for name in sorted(PUBLIC):
        obj = getattr(sympy, name)
        mod = getattr(obj, "__module__", None) or ""
        cat = MODULES.get(mod)
        if cat is None:
            # also accept submodules of an in-scope package (e.g. sympy.solvers.ode.*)
            for m, c in MODULES.items():
                if mod.startswith(m + "."):
                    cat = c
        if cat:
            out.append({"name": name, "category": cat})
    for cls, cat in ((sympy.Expr, "core"), (sympy.Matrix, "matrices")):
        for name in sorted(dir(cls)):
            if name.startswith("_"):
                continue
            attr = getattr(cls, name, None)
            if callable(attr):
                out.append({"name": "." + name, "category": cat, "owner": cls.__name__})
    return out


class Timeout(Exception):
    pass


def _alarm(signum, frame):
    raise Timeout()


def main(dst):
    warnings.filterwarnings("ignore")
    signal.signal(signal.SIGALRM, _alarm)
    finder = doctest.DocTestFinder(exclude_empty=True)
    cases = []
    skipped = {}
    for modname, category in MODULES.items():
        try:
            mod = importlib.import_module(modname)
        except Exception:
            continue
        for test in finder.find(mod):
            globs = {}
            exec("from sympy import *", globs)
            for ex in test.examples:
                src = ex.source.strip()
                try:
                    tree = ast.parse(src, mode="eval")
                except SyntaxError:
                    # statements (assignments, imports): just execute
                    try:
                        signal.alarm(10)
                        exec(compile(src, "<doctest>", "exec"), globs)
                    except (Exception, Timeout):
                        pass
                    finally:
                        signal.alarm(0)
                    continue
                call = tree.body
                record = None
                if isinstance(call, ast.Call) and not any(isinstance(a, ast.Starred) for a in call.args):
                    if isinstance(call.func, ast.Name):
                        record = {"fn": call.func.id}
                    elif isinstance(call.func, ast.Attribute):
                        record = {"fn": "." + call.func.attr, "selfSrc": ast.unparse(call.func.value)}
                try:
                    signal.alarm(10)
                    result = eval(compile(tree, "<doctest>", "eval"), globs)
                except (Exception, Timeout):
                    continue
                finally:
                    signal.alarm(0)
                if record is None or "print" in record["fn"] or record["fn"] in ("str", "srepr", "latex", "repr"):
                    continue
                fn = record["fn"]
                # only the public API: top-level sympy names and public methods
                if fn.startswith("."):
                    if fn[1:].startswith("_"):
                        continue
                elif fn not in PUBLIC or fn in globs and getattr(globs[fn], "__module__", "").startswith("__"):
                    continue
                try:
                    if "selfSrc" in record:
                        record["self"] = ser(eval(record.pop("selfSrc"), globs))
                    record["args"] = [ser(eval(compile(ast.Expression(a), "<a>", "eval"), globs)) for a in call.args]
                    record["kwargs"] = {
                        k.arg: ser(eval(compile(ast.Expression(k.value), "<k>", "eval"), globs)) for k in call.keywords
                    }
                except Unsupported as e:
                    # keep the case (it counts as a failure) so the rate is not inflated
                    skipped[str(e)] = skipped.get(str(e), 0) + 1
                    record.pop("selfSrc", None)
                    record["unsupportedArg"] = str(e)
                except Exception:
                    continue
                if isinstance(result, (MatrixBase,)):
                    expected = str(result)
                elif isinstance(result, (Basic, list, tuple, dict, set, int, float, bool)) or result is None:
                    expected = str(result)
                else:
                    continue
                if "\n" in expected:
                    continue
                record.update({"category": category, "module": modname, "src": src, "expected": expected})
                cases.append(record)
    with open(dst, "w", encoding="utf-8") as f:
        json.dump({"sympy": sympy.__version__, "api": api_inventory(), "cases": cases}, f, indent=1, ensure_ascii=False)
        f.write("\n")
    by_cat = {}
    for c in cases:
        by_cat[c["category"]] = by_cat.get(c["category"], 0) + 1
    print(f"TOTAL {len(cases)} cases", by_cat, file=sys.stderr)
    print("skipped (unsupported arg types):", dict(sorted(skipped.items(), key=lambda kv: -kv[1])[:15]), file=sys.stderr)


if __name__ == "__main__":
    main(sys.argv[1])
