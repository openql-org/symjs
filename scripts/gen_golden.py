#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
"""Generate golden outputs from SymPy for the symjs compatibility tests.

Usage: python3 scripts/gen_golden.py packages/symjs/tests/golden/cases.json packages/symjs/tests/golden/expected.json (pnpm golden)
"""

import json
import sys

import sympy
from sympy import Integral, Symbol, cancel, integrate, limit, series, conjugate, expand, factor, latex, roots, simplify, together, trigsimp
from sympy.parsing.sympy_parser import parse_expr


def main(src: str, dst: str) -> None:
    with open(src, encoding="utf-8") as f:
        spec = json.load(f)
    syms = {name: Symbol(name, **assump) for name, assump in spec["symbols"].items()}
    x = syms["x"]

    def run(op: str, e):
        if op == "str":
            return str(e)
        if op == "latex":
            return latex(e)
        if op == "expand":
            return str(expand(e))
        if op == "factor":
            return str(factor(e))
        if op == "simplify":
            return str(simplify(e))
        if op == "trigsimp":
            return str(trigsimp(e))
        if op == "together":
            return str(together(e))
        if op == "cancel":
            return str(cancel(e))
        if op == "conjugate":
            return str(conjugate(e))
        if op == "diff_x":
            return str(e.diff(x))
        if op == "solve_x":
            return [str(r) for r in sympy.solve(e, x)]
        if op == "fps_x":
            return str(sympy.fps(e, x))
        if op.startswith("integrate:"):
            spec_ = op.split(":", 1)[1].split(",")
            var = syms[spec_[0]] if spec_[0] in syms else Symbol(spec_[0])
            if len(spec_) == 3:
                lo = parse_expr(spec_[1], local_dict=dict(syms))
                hi = parse_expr(spec_[2], local_dict=dict(syms))
                return str(integrate(e, (var, lo, hi)))
            return str(integrate(e, var))
        if op == "dsolve":
            from sympy import Function, dsolve
            return str(dsolve(e, Function("f")(x)))
        if op.startswith("series:"):
            spec_ = op.split(":", 1)[1].split(",")
            var = syms[spec_[0]]
            pt = parse_expr(spec_[1], local_dict=dict(syms)) if len(spec_) > 1 else 0
            n = int(spec_[2]) if len(spec_) > 2 else 6
            return str(series(e, var, pt, n))
        if op.startswith("limit:"):
            spec_ = op.split(":", 1)[1].split(",")
            var = syms[spec_[0]] if spec_[0] in syms else Symbol(spec_[0])
            pt = parse_expr(spec_[1], local_dict=dict(syms))
            direction = spec_[2] if len(spec_) > 2 else "+"
            return str(limit(e, var, pt, direction))
        if op.startswith("evalf:"):
            return str(e.evalf(int(op.split(":", 1)[1])))
        if op == "latex_integral":
            return latex(Integral(e, x)) + " | " + latex(Integral(e, (x, 0, 1)))
        if op == "roots_x":
            # sorted list with multiplicity, like symjs `roots`
            rs = roots(e, x)
            out = []
            for r, m in rs.items():
                out += [r] * m
            return sorted((str(r) for r in out))
        raise ValueError(f"unknown op {op}")

    results = []
    for case in spec["cases"]:
        from sympy import Function
        e = parse_expr(case["expr"], local_dict={**syms, "f": Function("f")})
        results.append({"expr": case["expr"], "out": {op: run(op, e) for op in case["ops"]}})
    with open(dst, "w", encoding="utf-8") as f:
        json.dump({"sympy": sympy.__version__, "results": results}, f, indent=2, ensure_ascii=False)
        f.write("\n")


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2])
