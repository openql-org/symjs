# @symjs/symjs

The base module of [symjs](https://github.com/openql-org/symjs): a computer algebra system for TypeScript whose results and printed output are compatible with [SymPy](https://www.sympy.org/).

```ts
import { parse, factor, symbols, diff, sin } from '@symjs/symjs';

const [x] = symbols('x');
factor(parse('x**3 - x')).toString(); // 'x*(x - 1)*(x + 1)'
diff(sin(x).pow(2), x).toString();    // '2*sin(x)*cos(x)'
```

The `ex` tagged template writes expressions with ordinary operators and embeds JavaScript values:

```ts
import { ex, symbols } from '@symjs/symjs';

const [x] = symbols('x', { real: true });
ex`(${x} + 1)^2/2`.toString(); // '(x + 1)**2/2'
```

Differential geometry is available through the `@symjs/symjs/diffgeom` subpath:

```ts
import { rcall } from '@symjs/symjs';
import { Differential, R2 } from '@symjs/symjs/diffgeom';

rcall(Differential(R2.x), R2.eX).toString(); // '1'
```

This subpath exposes manifolds, coordinate charts, fields, tensor and wedge
products, connections, integral curves and curvature. Its names are not
re-exported from the root entry.

See the repository README for the feature list, the SymPy compatibility report and the extend modules.

## License

MIT. This package contains code ported from SymPy and mpmath, which is also subject to their BSD 3-Clause licenses; see [LICENSE](LICENSE) for the notices. Not affiliated with or endorsed by the SymPy or mpmath developers.
