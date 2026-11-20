# Scripts

Node scripts for building and checking the published packages. They run with
`node` or `bun` from the repository root unless noted.

| Script | Purpose | Run with |
|---|---|---|
| `build.mjs` | Builds every package with its own `build` script, `packages/symjs` first and then the extend packages that import its declarations | `bun run build` |
| `declarations.mjs` | Rewrites the declarations emitted by `tsc` in a `dist` directory into separate ESM (`.d.ts`) and CommonJS (`.d.cts`) graphs, so that `NodeNext` resolves the conditional exports and the relative imports | the `build` script of each package (`node ../../scripts/declarations.mjs dist`) |
| `check-package.mjs` | Copies the files each package publishes into a temporary `node_modules` and imports every export entry from ESM and CommonJS, outside the workspace's source aliases | `bun run test:package` (builds first) |
| `side-effects.mjs` | Lists the modules of `packages/symjs/src` with top-level side effects and writes them to the `sideEffects` field of `packages/symjs/package.json`; `--check` fails when the field is stale | `bun scripts/side-effects.mjs [--check]` (also `bun run side-effects` in `packages/symjs`) |
| `size.mjs` | Bundles typical imports of the built `packages/symjs/dist` with esbuild and prints the minified and gzipped sizes; `--check` fails when a budget is exceeded, `--json` prints machine-readable output | `bun run build && bun scripts/size.mjs [--check \| --json]` |

Run `side-effects.mjs` after adding or removing top-level registrations in the
sources, and `size.mjs --check` after changes that may affect what a bundler
keeps. The tools for the SymPy reference and the corpus tests are in
[`tools/`](../tools/sympy-reference/README.md).
