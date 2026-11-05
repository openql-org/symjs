import { defineConfig } from 'tsup';
import type { Plugin } from 'esbuild';

/**
 * Keep one output file per source module (relative imports stay imports),
 * so that consumers' bundlers can drop the modules they do not use. The
 * modules that register implementations on load are listed in the
 * `sideEffects` field of package.json (see scripts/side-effects.mjs).
 */
const preserveModules: Plugin = {
  name: 'preserve-modules',
  setup(build) {
    const ext = build.initialOptions.format === 'cjs' ? '.cjs' : '.js';
    build.onResolve({ filter: /^\.\.?\// }, (args) => (args.kind === 'entry-point' ? undefined : { path: args.path + ext, external: true }));
  },
};

/**
 * esbuild lists the export names of a CommonJS module for Node's ESM import
 * (`0 && (module.exports = { name, ... })`) as shorthand properties, which
 * is a syntax error for strict-mode reserved words such as `public` (SymPy's
 * `public` of sympy.utilities.decorator is exported under its name). Such a
 * name is written as a property with a value instead (`public: null`, as
 * esbuild itself writes keywords like `var`).
 */
const STRICT_RESERVED = /^ {2}(implements|interface|let|package|private|protected|public|static|yield)(,?)$/gm;
const cjsReservedExports = {
  name: 'cjs-reserved-exports',
  renderChunk(this: { format: string }, code: string) {
    if (this.format !== 'cjs') return undefined;
    const at = code.indexOf('\n0 && (module.exports = {');
    if (at < 0) return undefined;
    return { code: code.slice(0, at) + code.slice(at).replace(STRICT_RESERVED, '  $1: null$2') };
  },
};

export default defineConfig({
  entry: ['src/**/*.ts'],
  format: ['esm', 'cjs'],
  bundle: true,
  splitting: false,
  dts: false,
  sourcemap: true,
  clean: true,
  target: 'es2022',
  esbuildPlugins: [preserveModules],
  plugins: [cjsReservedExports],
});
