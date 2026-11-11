# @symjs/diffgeom

Differential geometry for symjs, ported from SymPy 1.14's `sympy.diffgeom`.
Install alongside its peer dependency, `@symjs/symjs`.

```ts
import { add, mul, rcall } from '@symjs/symjs';
import {
  R2, R2R, R2P, Differential, TensorProduct,
  metricToChristoffel2nd, metricToRicciComponents,
} from '@symjs/diffgeom';

rcall(Differential(R2.x.pow(2)), R2.eX); // 2*x
R2R.point([3, 4]).coords(R2P);          // Matrix([[5], [atan(4/3)]])

const metric = add(
  TensorProduct(R2.dr, R2.dr),
  mul(R2.r.pow(2), TensorProduct(R2.dtheta, R2.dtheta)),
);
metricToChristoffel2nd(metric); // polar-coordinate connection
metricToRicciComponents(metric); // zero: the Euclidean plane is flat
```

The package exports manifolds, patches, coordinate systems and symbols, points,
scalar and vector fields, commutators, exterior and Lie derivatives, tensor and
wedge products, covariant derivative operators, integral curves, basis changes,
metric matrices, Christoffel symbols, Riemann and Ricci tensors, and the
predefined two- and three-dimensional Euclidean charts.

Names follow the [public API policy](../../docs/api-policy.md): `R2_r` is `R2R`,
`e_x` is `eX`, `metric_to_Christoffel_2nd` is `metricToChristoffel2nd`.
Construct `Manifold`, `Patch`, `CoordSystem`, `Point`, coordinate symbols and
base fields with `new`. Evaluating constructors such as `Differential` and
`TensorProduct` are functions returning expressions. Apply these expressions
with `rcall`; base fields and derivative operators also provide `.call`.
Use null input slots for partial contractions: `rcall(TensorProduct(R2.dx,
R2.dy), null, R2.eY)` returns `R2.dx`. Public results are never null or undefined.

Coordinate relations are Maps from `[sourceName, targetName]` to
`[sourceSymbols, targetExpressions]`; Lambda values are also accepted.
Missing inverse relations are solved symbolically, and connected paths are
composed automatically. Ambiguous inverse branches raise `RangeError`.
Unavailable inverse solutions raise `NotImplementedError`. `connectTo` also
registers transformations. Transformation objects expose `.call`, `.signature`
and `.expr`; coordinate arrays and Jacobians are base `Matrix` objects.

`intcurveSeries(v, t, point, n, { coordSys, coeffs: true })` returns the list of
Taylor terms (including powers of `t`), while its default result is their sum.
Connection and curvature components use `ImmutableDenseNDimArray`, with
`.get(i, j, k)` and `.flatElements()` for access.

The [independent compatibility report](../../compat/extend/diffgeom/REPORT.md)
measures doctests and unit assertions from SymPy. Run `pnpm compat:diffgeom`;
regenerate references with `pnpm compat:extract-diffgeom`. `pnpm compat` includes
this corpus. Tests mirror the source files and enforce 100% per-file coverage.

Covariant differentiation of forms and partial contractions of exterior
derivatives above degree one raise `NotImplementedError`. Inverse transforms
inherit the base solver's capabilities. Pretty printing uses the base
extension-node fallback. Powers of vector fields are rejected, and Lie
derivatives of forms evaluate the correction tensor on its commutator arguments;
these correct mathematical errors in SymPy 1.14.

MIT; the included LICENSE also reproduces SymPy's BSD 3-Clause notice.
