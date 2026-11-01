#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
"""Generate golden outputs from SymPy for the symjs compatibility tests.

Usage: python3 scripts/gen_golden.py tests/golden/cases.json tests/golden/expected.json
"""

import json
import sys

import sympy
from sympy import Symbol, cancel, conjugate, expand, factor, latex, roots, simplify, together, trigsimp
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
        e = parse_expr(case["expr"], local_dict=dict(syms))
        results.append({"expr": case["expr"], "out": {op: run(op, e) for op in case["ops"]}})
    with open(dst, "w", encoding="utf-8") as f:
        json.dump({"sympy": sympy.__version__, "results": results}, f, indent=2, ensure_ascii=False)
        f.write("\n")


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2])
