# @symjs/physics-quantum

Extend module of [symjs](https://github.com/openql-org/symjs) for quantum physics, to be ported from SymPy's `sympy.physics.quantum`. It requires the base module `@symjs/symjs` (peer dependency).

```ts
import { Matrix } from '@symjs/symjs';
import { gates } from '@symjs/physics-quantum';

gates.H().mul(gates.H()).equals(Matrix.eye(2)); // true
```

The current `gates` module is provisional.

## License

MIT. This package contains code ported from SymPy (`sympy.physics.quantum`), which is also subject to SymPy's BSD 3-Clause license; see [LICENSE](LICENSE) for the notice. Not affiliated with or endorsed by the SymPy developers.
