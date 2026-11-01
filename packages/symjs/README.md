# @symjs/symjs

The base module of [symjs](https://github.com/openql-org/symjs): a computer algebra system for TypeScript whose results and printed output are compatible with [SymPy](https://www.sympy.org/).

```ts
import { parse, factor, symbols, diff, sin } from '@symjs/symjs';

const [x] = symbols('x');
factor(parse('x**3 - x')).toString(); // 'x*(x - 1)*(x + 1)'
diff(sin(x).pow(2), x).toString();    // '2*sin(x)*cos(x)'
```

See the repository README for the feature list, the SymPy compatibility report and the extend modules.
