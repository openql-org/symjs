# @symjs/mathjs

Extend module of [symjs](https://github.com/openql-org/symjs): conversion between symjs and [math.js](https://mathjs.org) expressions, numbers and matrices.

math.js is **not** a dependency of this package. Functions that create math.js objects take your math.js instance; math.js objects are read by their structure. It requires the base module `@symjs/symjs` (peer dependency).

```ts
import * as math from 'mathjs';
import { parse } from '@symjs/symjs';
import { fromMathjs, toMathjs, toMathjsValue } from '@symjs/mathjs';

const node = toMathjs(parse('2*x**2 + sin(y)'), math); // a math.js expression tree
node.evaluate({ x: 2, y: 1 });                          // 8.841470984807897

fromMathjs(math.parse('x^2 + log(x, 2)'));              // x**2 + log(x)/log(2)

const bigmath = math.create(math.all, { number: 'BigNumber', precision: 40 });
toMathjsValue(parse('1/3'), bigmath, { bignumber: true }); // BigNumber 0.333...
```

| symjs | math.js |
|---|---|
| `toMathjsString(e)` | math.js syntax (`^`, `conj`, `ceil`, ...) |
| `toMathjs(e, math)` / `fromMathjs(node)` / `fromMathjsString(text, math)` | expression trees |
| `toMathjsValue(e, math, { bignumber, fraction })` / `fromMathjsValue(v)` | numbers, BigNumber, Fraction, Complex |
| `toMathjsMatrix(m, math)` / `fromMathjsMatrix(m)` | matrices |

Notes:

- Integers from math.js become exact rationals; other JS numbers become `Float`s.
- symjs `Float`s are binary (mpmath precision) and math.js BigNumbers decimal: converting rounds to the decimal digits of the precision.
- Unknown math.js functions become undefined functions (`f(x)`); pass `{ functions }` or `{ symbols }` to `fromMathjs` to map names.
- Unsupported nodes and values throw a `TypeError`; no function returns `undefined`.
