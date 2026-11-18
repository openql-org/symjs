# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
"""Generate assumption-wrapper reference results with SymPy 1.14."""
import json
from pathlib import Path
from sympy import Symbol,Q
from sympy.assumptions.wrapper import AssumptionsWrapper
names='algebraic antihermitian commutative complex composite even extended_negative extended_nonnegative extended_nonpositive extended_nonzero extended_positive extended_real finite hermitian imaginary infinite integer irrational negative noninteger nonnegative nonpositive nonzero odd positive prime rational real transcendental zero'.split()
x=Symbol('wrapped')
rows=[]
for assumption in ['even','positive','negative','zero','imaginary','rational']:
 w=AssumptionsWrapper(x,getattr(Q,assumption)(x))
 rows.append({'assumption':assumption,'facts':{'is'+''.join(p.title() for p in n.split('_')): 'unknown' if getattr(w,'is_'+n) is None else bool(getattr(w,'is_'+n)) for n in names}})
(Path(__file__).resolve().parents[3] / 'packages/symjs/tests/assumptions/wrapper.references.json').write_text(json.dumps(rows,indent=2)+'\n')
