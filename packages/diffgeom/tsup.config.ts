import { defineConfig } from 'tsup';

export default defineConfig({
  entry: ['src/index.ts'],
  format: ['esm', 'cjs'],
  dts: false,
  sourcemap: true,
  clean: true,
  target: 'es2022',
  // the base module is a peer dependency: never bundle it
  external: ['@symjs/symjs'],
});
