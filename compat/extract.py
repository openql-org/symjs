#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
"""Extract a SymPy compatibility corpus from SymPy's own doctests.

For every doctest example in the in-scope modules whose source is a single
call ``f(args...)`` or method call ``obj.m(args...)``, the arguments are
evaluated in the doctest namespace and serialized to a JSON tree. The
expected output is ``str()`` of the result computed by the installed SymPy.

Usage: PYTHONHASHSEED=0 python3 compat/extract.py compat/corpus.json
(the fixed hash seed keeps the order of printed sets reproducible)
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
    # general-purpose packages that many SymPy packages depend on (base candidates)
    "sympy.logic.boolalg": "logic",
    "sympy.logic.inference": "logic",
    "sympy.tensor.array.dense_ndim_array": "tensor",
    "sympy.tensor.array.ndim_array": "tensor",
    "sympy.tensor.array.arrayop": "tensor",
    "sympy.tensor.array.array_derivatives": "tensor",
    "sympy.tensor.indexed": "tensor",
    "sympy.ntheory.factor_": "ntheory",
    "sympy.ntheory.primetest": "ntheory",
    "sympy.ntheory.generate": "ntheory",
    "sympy.ntheory.residue_ntheory": "ntheory",
    "sympy.ntheory.continued_fraction": "ntheory",
    "sympy.ntheory.partitions_": "ntheory",
    "sympy.ntheory.modular": "ntheory",
    "sympy.ntheory.multinomial": "ntheory",
    "sympy.ntheory.digits": "ntheory",
    "sympy.ntheory.egyptian_fraction": "ntheory",
    "sympy.assumptions.ask": "assumptions",
    "sympy.assumptions.refine": "assumptions",
    "sympy.utilities.iterables": "utilities",
    "sympy.combinatorics.permutations": "combinatorics",
    "sympy.printing.pretty.pretty": "printing",
    "sympy.integrals.transforms": "calculus",
    "sympy.integrals.laplace": "calculus",
    "sympy.calculus.accumulationbounds": "calculus",
    "sympy.matrices.expressions.matexpr": "matrices",
    "sympy.matrices.expressions.matmul": "matrices",
    "sympy.matrices.expressions.matadd": "matrices",
    "sympy.matrices.expressions.inverse": "matrices",
    "sympy.matrices.expressions.trace": "matrices",
    "sympy.matrices.expressions.determinant": "matrices",
    "sympy.matrices.expressions.blockmatrix": "matrices",
    "sympy.matrices.expressions.transpose": "matrices",
}

ASSUMPTION_KEYS = ["real", "positive", "negative", "nonnegative", "nonpositive", "integer", "commutative", "polar"]


DUMMY_IDS = {}


class Unsupported(Exception):
    pass


def ser(o):
    """Serialize a SymPy object (or Python value) into a JSON tree."""
    from sympy import Float, Integer, Rational, Symbol, Tuple
    from sympy.core.relational import Relational

    if o is None or isinstance(o, bool):
        return {"t": "Js", "v": o}
    if isinstance(o, int):
        return {"t": "Rational", "p": str(o), "q": "1"}
    if isinstance(o, float):
        return {"t": "Float", "v": o, "py": True}
    if isinstance(o, str):
        return {"t": "Str", "v": o}
    import types as _types
    if isinstance(o, (_types.GeneratorType, zip, map, filter)) or type(o).__name__.endswith("iterator"):
        # iterators are materialized (their values are what the call sees)
        return {"t": "Tuple", "items": [ser(i) for i in list(o)], "list": True}
    if isinstance(o, (_types.FunctionType, _types.BuiltinFunctionType)):
        # a library function passed as an argument (equal_valued, factor, math.isclose, ...)
        mod = getattr(o, "__module__", "") or ""
        if mod.startswith("sympy") or mod == "math":
            return {"t": "JsFunc", "name": ("math." if mod == "math" else "") + o.__name__}
        raise Unsupported("function")
    from sympy.calculus.accumulationbounds import AccumulationBounds as _AB
    if isinstance(o, _AB):
        return {"t": "AccumBounds", "min": ser(o.min), "max": ser(o.max)}
    from sympy.geometry import Curve as _Curve
    if isinstance(o, _Curve):
        return {"t": "Curve", "functions": [ser(f) for f in o.functions], "limits": [ser(l) for l in o.limits]}
    if isinstance(o, sympy.Indexed):
        return {"t": "Indexed", "base": ser(o.base.label), "indices": [ser(i) for i in o.indices]}
    if isinstance(o, sympy.IndexedBase):
        return {"t": "IndexedBase", "label": ser(o.label)}
    if isinstance(o, sympy.CRootOf):
        return {"t": "CRootOf", "poly": ser(o.expr), "index": int(o.index)}
    if isinstance(o, sympy.RootSum):
        return {"t": "RootSum", "poly": ser(o.expr), "fun": ser(o.fun), "var": ser(o.poly.gen)}
    if isinstance(o, sympy.MatrixSymbol):
        return {"t": "MatrixSymbol", "name": o.name, "rows": ser(o.shape[0]), "cols": ser(o.shape[1])}
    if isinstance(o, (set, frozenset)):
        return {"t": "JsSet", "items": [ser(i) for i in o]}
    if isinstance(o, list):
        return {"t": "Tuple", "items": [ser(i) for i in o], "list": True}
    if isinstance(o, range):
        return {"t": "Tuple", "items": [ser(i) for i in o], "list": True}
    if isinstance(o, (tuple, Tuple)):
        return {"t": "Tuple", "items": [ser(i) for i in o]}
    if isinstance(o, dict):
        return {"t": "Dict", "items": [[ser(k), ser(v)] for k, v in o.items()]}
    if isinstance(o, MatrixBase):
        return {"t": "Matrix", "rows": [[ser(o[i, j]) for j in range(o.cols)] for i in range(o.rows)], "shape": [o.rows, o.cols]}
    from sympy.core.function import UndefinedFunction as _UF
    if isinstance(o, _UF):
        return {"t": "UFnClass", "name": o.__name__}
    if isinstance(o, sympy.polys.polytools.GroebnerBasis):
        return {"t": "Groebner", "exprs": [ser(e) for e in o.exprs], "gens": [ser(g) for g in o.gens], "order": str(o.order)}
    if isinstance(o, sympy.Poly):
        return {"t": "Poly", "expr": ser(o.as_expr()), "gens": [ser(g) for g in o.gens], "domain": str(o.get_domain()), "pure": isinstance(o, sympy.PurePoly)}
    if isinstance(o, type) and issubclass(o, Basic) and not isinstance(o, sympy.FunctionClass):
        return {"t": "Type", "name": o.__name__}
    if isinstance(o, type) and o.__name__ in ("Matrix", "MutableDenseMatrix", "ImmutableMatrix", "ImmutableDenseMatrix"):
        return {"t": "Type", "name": "Matrix"}
    from sympy.core.function import WildFunction as _WF
    if isinstance(o, sympy.FunctionClass) and not isinstance(o, _UF):
        return {"t": "FnClass", "name": o.__name__}
    from sympy.polys.domains.domain import Domain as _Domain
    if isinstance(o, _Domain) and str(o) in ("ZZ", "QQ"):
        return {"t": "Domain", "name": str(o)}
    if not isinstance(o, Basic):
        raise Unsupported(type(o).__name__)
    if isinstance(o, sympy.AlgebraicNumber):
        return {"t": "AlgebraicNumber", "root": ser(o.root), "coeffs": [ser(c) for c in o.coeffs()]}
    if isinstance(o, sympy.Interval):
        return {"t": "Interval", "a": ser(o.start), "b": ser(o.end), "lo": bool(o.left_open), "ro": bool(o.right_open)}
    if isinstance(o, sympy.FiniteSet):
        return {"t": "FiniteSet", "items": [ser(i) for i in o.args]}
    if isinstance(o, (sympy.Union, sympy.Intersection, sympy.Complement)):
        return {"t": "SetOp", "op": type(o).__name__, "args": [ser(i) for i in o.args]}
    named_sets = {sympy.S.Reals: "Reals", sympy.S.Integers: "Integers", sympy.S.Naturals: "Naturals",
                  sympy.S.Naturals0: "Naturals0", sympy.S.Complexes: "Complexes", sympy.S.EmptySet: "EmptySet"}
    for k, v in named_sets.items():
        if o is k:
            return {"t": "NamedSet", "name": v}
    if isinstance(o, (sympy.And, sympy.Or)):
        return {"t": "BoolOp", "op": type(o).__name__, "args": [ser(i) for i in o.args]}
    if isinstance(o, sympy.Wild):
        props = []
        for f in o.properties:
            # only predicates of the form lambda k: k.is_X
            names = getattr(getattr(f, "__code__", None), "co_names", ())
            if len(names) != 1 or not names[0].startswith("is_"):
                raise Unsupported("Wild properties")
            props.append(names[0])
        a = {k: True for k in ASSUMPTION_KEYS if o._assumptions_orig.get(k) is True}
        return {"t": "Wild", "name": o.name, "exclude": [ser(e) for e in o.exclude], "assume": a, "props": props}
    if isinstance(o, _WF):
        nargs = o.nargs
        lst = None if nargs == sympy.S.Naturals0 else sorted(int(n) for n in nargs)
        return {"t": "WildFunction", "name": o.name, "nargs": lst}
    if isinstance(o, sympy.Dummy):
        a = {k: True for k in ASSUMPTION_KEYS if o._assumptions_orig.get(k) is True}
        # indices are renumbered per case so that the corpus is reproducible
        idx = DUMMY_IDS.setdefault(o.dummy_index, len(DUMMY_IDS))
        return {"t": "Dummy", "name": o.name, "index": idx, "assume": a}
    if o.is_Symbol and type(o) is Symbol:
        a = {k: True for k in ASSUMPTION_KEYS if o._assumptions_orig.get(k) is True}
        if o._assumptions_orig.get("zero") is False:
            a["zero"] = False
        if o._assumptions_orig.get("commutative") is False:
            a["commutative"] = False
        a.pop("commutative", None) if a.get("commutative") is True else None
        return {"t": "Symbol", "name": o.name, "assume": a}
    if isinstance(o, (Integer, Rational)) and o.is_Rational:
        return {"t": "Rational", "p": str(o.p), "q": str(o.q)}
    if isinstance(o, Float):
        sgn, man, exp, _bc = o._mpf_
        return {"t": "Float", "v": float(o), "man": str(-man if sgn else man), "exp": int(exp), "prec": int(o._prec)}
    named = {sympy.pi: "pi", sympy.E: "E", sympy.I: "I", sympy.oo: "oo", -sympy.oo: "-oo", sympy.zoo: "zoo", sympy.nan: "nan",
             sympy.EulerGamma: "EulerGamma", sympy.Catalan: "Catalan", sympy.GoldenRatio: "GoldenRatio",
             sympy.TribonacciConstant: "TribonacciConstant"}
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
        return {"t": "Js", "v": bool(o)}
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


import sympy.combinatorics as _combinatorics
PUBLIC = set(sympy.__all__) | {"Permutation", "Cycle"}
setattr(sympy, "Permutation", _combinatorics.Permutation)
setattr(sympy, "Cycle", _combinatorics.permutations.Cycle)


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
    owners = ((sympy.Expr, "core"), (sympy.Matrix, "matrices"), (sympy.ImmutableDenseNDimArray, "tensor"),
              (_combinatorics.Permutation, "combinatorics"), (sympy.MatrixExpr, "matrices"))
    for cls, cat in owners:
        for name in sorted(dir(cls)):
            if name.startswith("_"):
                continue
            attr = getattr(cls, name, None)
            if callable(attr):
                out.append({"name": "." + name, "category": cat, "owner": cls.__name__})
    return out


class Timeout(Exception):
    pass


def ser_arg(node, globs):
    """Serialize a call argument; a lambda whose body evaluates to an expression
    when applied to dummies becomes {"t": "JsLambda", params, body}."""
    if isinstance(node, ast.Lambda) and not node.args.vararg and not node.args.kwonlyargs and not node.args.kwarg:
        names = [a.arg for a in node.args.args]
        b = node.body
        if (len(names) == 1 and isinstance(b, ast.Attribute) and isinstance(b.value, ast.Name)
                and b.value.id == names[0] and b.attr.startswith("is_")):
            # a predicate such as lambda e: e.is_Mul
            return {"t": "JsPred", "attr": b.attr}
        ds = [sympy.Dummy(n) for n in names]
        loc = dict(globs)
        loc.update(zip(names, ds))
        try:
            body = eval(compile(ast.Expression(node.body), "<lambda>", "eval"), loc)
        except Exception:
            raise Unsupported("function")
        if not isinstance(body, Basic) or isinstance(body, sympy.logic.boolalg.BooleanAtom):
            raise Unsupported("function")
        return {"t": "JsLambda", "params": [ser(d) for d in ds], "body": ser(body)}
    return ser(eval(compile(ast.Expression(node), "<a>", "eval"), globs))


def _alarm(signum, frame):
    raise Timeout()


def main(dst):
    import random
    random.seed(0)  # randMatrix and friends: keep the corpus reproducible
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
                if ex.options.get(doctest.SKIP):
                    # SymPy does not run these either (random or illustrative output)
                    continue
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
                DUMMY_IDS.clear()
                try:
                    if "selfSrc" in record:
                        record["self"] = ser(eval(record.pop("selfSrc"), globs))
                    record["args"] = [ser_arg(a, globs) for a in call.args]
                    record["kwargs"] = {k.arg: ser_arg(k.value, globs) for k in call.keywords}
                except Unsupported as e:
                    # keep the case (it counts as a failure) so the rate is not inflated
                    skipped[str(e)] = skipped.get(str(e), 0) + 1
                    record.pop("selfSrc", None)
                    record["unsupportedArg"] = str(e)
                except Exception:
                    continue
                from sympy.polys.monomials import Monomial as _Monomial
                if isinstance(result, (MatrixBase,)):
                    expected = str(result)
                elif isinstance(result, tuple) and any(isinstance(i, _Monomial) for i in result):
                    # a Monomial's repr is its address; its str is x**2*y**0
                    expected = "(" + ", ".join(str(i) for i in result) + ")"
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
