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
});
