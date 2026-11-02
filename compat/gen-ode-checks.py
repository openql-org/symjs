#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
"""Generate compat/ode-checks.json: representative ODEs for SymPy's dsolve
hints with the output of the installed SymPy.

Usage: python3 compat/gen-ode-checks.py
"""

import json
import re
import signal

import sympy
from sympy import Function, cos, dsolve, exp, log, sin, symbols, tan, sqrt

x = symbols("x")
f = Function("f")
fx = f(x)
d, dd, ddd = fx.diff(x), fx.diff(x, 2), fx.diff(x, 3)

# (hint, equation); the hint names follow SymPy's classify_ode
CASES = [
    ("separable", d - x * fx),
    ("separable", d - fx**2),
    ("separable", d - exp(x + fx)),
    ("1st_linear", d + fx / x - x**2),
    ("1st_linear", d - 2 * fx - exp(x)),
    ("1st_linear", d + fx * cos(x) - sin(2 * x) / 2),
    ("Bernoulli", d + fx / x - fx**2),
    ("Bernoulli", d - fx - x * fx**3),
    ("1st_exact", 2 * x * fx + (x**2 + 1) * d),
    ("1st_exact", sin(x) * cos(fx) + cos(x) * sin(fx) * d),
    ("1st_homogeneous_coeff", d - (x + fx) / x),
    ("1st_homogeneous_coeff", x * fx * d - (x**2 + fx**2)),
    ("almost_linear", x * d + fx - x**2),
    ("Riccati_special_minus2", d + fx**2 + 2 / x**2),
    ("linear_coefficients", d - (x + fx - 1) / (x - fx + 3)),
    ("nth_algebraic", d * (d - 1)),
    ("factorable", (d - 1) * (d - fx)),
    ("nth_linear_constant_coeff_homogeneous", dd + 9 * fx),
    ("nth_linear_constant_coeff_homogeneous", dd - 3 * d + 2 * fx),
    ("nth_linear_constant_coeff_homogeneous", dd + 2 * d + fx),
    ("nth_linear_constant_coeff_homogeneous", ddd - fx),
    ("nth_linear_constant_coeff_homogeneous", dd - 2 * d + 5 * fx),
    ("nth_linear_constant_coeff_undetermined_coefficients", dd + 3 * d + 2 * fx - 4),
    ("nth_linear_constant_coeff_undetermined_coefficients", dd - fx - exp(x)),
    ("nth_linear_constant_coeff_undetermined_coefficients", dd + fx - sin(x)),
    ("nth_linear_constant_coeff_undetermined_coefficients", dd + 4 * fx - x**2),
    ("nth_linear_constant_coeff_undetermined_coefficients", dd - 2 * d + fx - x * exp(x)),
    ("nth_linear_constant_coeff_variation_of_parameters", dd + fx - 1 / cos(x)),
    ("nth_linear_constant_coeff_variation_of_parameters", dd - 2 * d + fx - exp(x) / x),
    ("nth_linear_euler_eq_homogeneous", x**2 * dd + x * d - fx),
    ("nth_linear_euler_eq_homogeneous", x**2 * dd - 2 * fx),
    ("nth_linear_euler_eq_homogeneous", x**2 * dd - x * d + fx),
    ("nth_linear_euler_eq_nonhomogeneous_undetermined_coefficients", x**2 * dd - 2 * x * d + 2 * fx - x**3),
    ("Liouville", dd + d**2),
    ("nth_order_reducible", x * dd - d),
    ("nth_order_reducible", ddd - dd),
    ("2nd_nonlinear_autonomous_conserved", dd + fx),
    ("2nd_linear_airy", dd - x * fx),
    ("2nd_linear_bessel", x**2 * dd + x * d + (x**2 - 4) * fx),
]

ICS = [
    ("ics", d - fx, {f(0): 2}),
    ("ics", dd + fx, {f(0): 0, d.subs(x, 0): 1}),
]


def tostr(e):
    s = str(e)
    # symjs' parser writes higher derivatives with repeated variables
    s = re.sub(r"Derivative\(f\(x\), \(x, (\d+)\)\)", lambda m: "Derivative(f(x), " + ", ".join(["x"] * int(m.group(1))) + ")", s)
    return s


class Timeout(Exception):
    pass


def _alarm(signum, frame):
    raise Timeout()


def main():
    signal.signal(signal.SIGALRM, _alarm)
    out = []
    for hint, eq in CASES:
        try:
            signal.alarm(60)
            r = dsolve(eq, fx)
        except (Exception, Timeout) as e:
            r = None
        finally:
            signal.alarm(0)
        if r is None:
            continue
        out.append({"hint": hint, "eq": tostr(eq), "expected": str(r)})
    for hint, eq, ics in ICS:
        r = dsolve(eq, fx, ics=ics)
        out.append({"hint": hint, "eq": tostr(eq), "ics": [[tostr(k), str(v)] for k, v in ics.items()], "expected": str(r)})
    with open("compat/ode-checks.json", "w", encoding="utf-8") as fh:
        json.dump({"sympy": sympy.__version__, "checks": out}, fh, indent=1)
        fh.write("\n")
    print(len(out), "checks")


if __name__ == "__main__":
    main()
