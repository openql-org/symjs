# @symjs/physics-quantum

Extend module of [symjs](https://github.com/openql-org/symjs) for quantum physics, to be ported from SymPy's `sympy.physics.quantum`. It requires the base module `@symjs/symjs` (peer dependency).

```ts
import { Matrix } from '@symjs/symjs';
import { gates } from '@symjs/physics-quantum';

gates.H().mul(gates.H()).equals(Matrix.eye(2)); // true
```

The current `gates` module is provisional.
