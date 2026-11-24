// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Classical and public-key ciphers (SymPy sympy.crypto.crypto): shift,
 * affine, substitution, Vigenère, Hill, bifid and rail-fence ciphers, Morse
 * code, linear feedback shift registers, RSA and Kid RSA, ElGamal,
 * Diffie-Hellman, Goldwasser-Micali and Blum-Goldwasser.
 *
 * Integers are bigints. A random `seed` is an integer (which seeds SymPy's
 * shared generator, so results agree with SymPy) or a list of the values
 * to use, as in SymPy.
 */

import type { Expr } from '../core/nodes';
import { Rational, Sym } from '../core/nodes';
import { add, mul, pow } from '../core/ops';
import { at, expectType, getOrThrow } from '../core/guard';
import { gcd } from '../core/numbers';
import type { IntLike } from '../ntheory/intutil';
import { asInt, invert, powmod } from '../ntheory/intutil';
import { isprime } from '../ntheory/primetest';
import { factorint } from '../ntheory/factor';
import { nextprime } from '../ntheory/generate';
import { primitiveRoot } from '../ntheory/residue';
import { rng } from '../ntheory/random';
import { Matrix } from '../matrices/matrix';
import { invMod } from '../matrices/linalg';

/** A random seed: an integer seeds SymPy's shared generator, a list gives the values in turn. */
export type CryptoSeed = IntLike | readonly IntLike[];

const UPPER = 'ABCDEFGHIJKLMNOPQRSTUVWXYZ';
const DIGITS = '0123456789';
const PRINTABLE = `${DIGITS}abcdefghijklmnopqrstuvwxyz${UPPER}!"#$%&'()*+,-./:;<=>?@[\\]^_\`{|}~ \t\n\r\x0b\x0c`;
const bmod = (a: bigint, m: bigint): bigint => ((a % m) + m) % m;
const uniqChars = (s: string): string => [...new Set(chars(s))].join('');
/** The characters of an (ASCII) text. */
const chars = (s: string): string[] => s.split('');

/** Python str.translate: characters of `from` replaced by those of `to`, then those of `del` deleted. */
function translate(s: string, from: string, to: string, del = ''): string {
  const m = new Map(chars(from).map((c, i) => [c, to.charAt(i)] as const));
  return chars(s)
    .filter((c) => !del.includes(c))
    .map((c) => m.get(c) ?? c)
    .join('');
}

/**
 * Extracts the uppercase ASCII letters from each input string. With no argument, returns the uppercase alphabet.
 * @param s - The text or strings to normalize.
 * @returns The normalized text, the array of normalized strings, or the alphabet.
 * @see SymPy `sympy.crypto.crypto.AZ`
 * @example
 * ```ts
 * import { AZ } from '@symjs/symjs';
 * AZ('Hello, world!'); // => HELLOWORLD
 * ```
 */
export function AZ(): string;
export function AZ(s: string): string;
export function AZ(s: readonly string[]): string[];
export function AZ(s?: string | readonly string[]): string | string[] {
  if (s === undefined || s.length === 0) return UPPER;
  const one = (x: string): string => checkAndJoin(x.toUpperCase().split(/\s+/), UPPER, true);
  return typeof s === 'string' ? one(s) : s.map(one);
}

/**
 * The uppercase Bifid alphabet with J omitted.
 * @see SymPy `sympy.crypto.crypto.bifid5`
 */
export const bifid5: string = UPPER.replace('J', '');
/**
 * The uppercase letters followed by the ten decimal digits.
 * @see SymPy `sympy.crypto.crypto.bifid6`
 */
export const bifid6: string = UPPER + DIGITS;
/**
 * The printable ASCII alphabet used by the ten-by-ten Bifid cipher.
 * @see SymPy `sympy.crypto.crypto.bifid10`
 */
export const bifid10: string = PRINTABLE;

/**
 * Places the distinct keyword characters first, followed by the remaining alphabet characters in order.
 * @param key - The keyword defining the substitution alphabet.
 * @param symbols - The ordered alphabet.
 * @returns The keyed alphabet.
 * @throws RangeError when the alphabet contains repeated characters or the key contains characters outside the alphabet.
 * @see SymPy `sympy.crypto.crypto.padded_key`
 * @example
 * ```ts
 * import { paddedKey } from '@symjs/symjs';
 * paddedKey('PUPPY', 'OPQRSTUVWXY'); // => PUYOQRSTVWX
 * ```
 */
export function paddedKey(key: string, symbols: string): string {
  const syms = uniqChars(symbols);
  if (syms.length !== symbols.length) {
    const extra = [...new Set(chars(symbols).filter((c, i) => symbols.indexOf(c) !== i))].sort().join('');
    throw new RangeError(`duplicate characters in symbols: ${extra}`);
  }
  const extra = [...new Set(chars(key).filter((c) => !syms.includes(c)))].sort().join('');
  if (extra) throw new RangeError(`characters in key but not symbols: ${extra}`);
  const key0 = uniqChars(key);
  return key0 + chars(syms).filter((c) => !key0.includes(c)).join('');
}

/**
 * Joins the text fragments and optionally validates or filters their characters against an alphabet.
 * @param phrase - The string or string fragments to join.
 * @param symbols - The ordered alphabet.
 * @param filter - Whether to discard characters outside the alphabet.
 * @returns The validated or filtered text.
 * @throws RangeError when the phrase contains an unrecognized character and filtering is disabled.
 * @see SymPy `sympy.crypto.crypto.check_and_join`
 * @example
 * ```ts
 * import { checkAndJoin } from '@symjs/symjs';
 * checkAndJoin('a phrase'); // => a phrase
 * ```
 */
export function checkAndJoin(phrase: string | readonly string[], symbols?: string | readonly string[], filter = false): string {
  const rv = typeof phrase === 'string' ? phrase : phrase.join('');
  if (symbols === undefined) return rv;
  const syms = checkAndJoin(symbols);
  const missing = [...new Set(chars(rv).filter((c) => !syms.includes(c)))].sort().join('');
  if (!missing) return rv;
  if (!filter) throw new RangeError(`characters in phrase but not symbols: "${missing}"`);
  return translate(rv, '', '', missing);
}

/** SymPy _prep: the message and key filtered to the alphabet (the uppercase letters by default). */
function prep(msg0: string, key0: string, alp0?: string, dflt?: string): [string, string, string] {
  let [msg, key, alp] = [msg0, key0, alp0 ?? ''];
  if (!alp) {
    if (dflt === undefined) {
      alp = UPPER;
      msg = AZ(msg);
      key = AZ(key);
    } else alp = dflt;
  }
  return [checkAndJoin(msg, alp, true), checkAndJoin(key, alp, true), alp];
}

/**
 * Rotates the integers from zero through `n - 1` to the left by `k` positions.
 * @param k - The cyclic shift.
 * @param n - The length of the list before rotation.
 * @returns The indices in rotated order.
 * @see SymPy `sympy.crypto.crypto.cycle_list`
 * @example
 * ```ts
 * import { cycleList } from '@symjs/symjs';
 * cycleList(3, 10); // => [3, 4, 5, 6, 7, 8, 9, 0, 1, 2]
 * ```
 */
export function cycleList(k: number, n: number): number[] {
  const s = ((k % n) + n) % n;
  return [...Array.from({ length: n - s }, (_x, i) => s + i), ...Array.from({ length: s }, (_x, i) => i)];
}

/**
 * Encrypts the message using the Caesar cipher.
 * @param msg - The plaintext to encode.
 * @param key - The number of alphabet positions to shift.
 * @param symbols - The ordered alphabet.
 * @returns The ciphertext.
 * @see SymPy `sympy.crypto.crypto.encipher_shift`
 * @example
 * ```ts
 * import { encipherShift } from '@symjs/symjs';
 * encipherShift('HPOBWZCFBUBSNZ', -1); // => GONAVYBEATARMY
 * ```
 */
export function encipherShift(msg: string, key: number, symbols?: string): string {
  const [m, , A] = prep(msg, '', symbols);
  const shift = A.length - (((key % A.length) + A.length) % A.length);
  return translate(m, A.slice(shift) + A.slice(0, shift), A);
}

/**
 * Recovers the plaintext using the Caesar cipher.
 * @param msg - The ciphertext to decrypt.
 * @param key - The number of alphabet positions to shift.
 * @param symbols - The ordered alphabet.
 * @returns The recovered message.
 * @see SymPy `sympy.crypto.crypto.decipher_shift`
 * @example
 * ```ts
 * import { decipherShift } from '@symjs/symjs';
 * decipherShift('HPOBWZCFBUBSNZ', 1); // => GONAVYBEATARMY
 * ```
 */
export function decipherShift(msg: string, key: number, symbols?: string): string {
  return encipherShift(msg, -key, symbols);
}

/**
 * Encrypts the message using the ROT13 cipher.
 * @param msg - The plaintext to encode.
 * @param symbols - The ordered alphabet.
 * @returns The ciphertext.
 * @see SymPy `sympy.crypto.crypto.encipher_rot13`
 * @example
 * ```ts
 * import { encipherRot13 } from '@symjs/symjs';
 * encipherRot13('ABC'); // => NOP
 * ```
 */
export function encipherRot13(msg: string, symbols?: string): string {
  return encipherShift(msg, 13, symbols);
}

/**
 * Recovers the plaintext using the ROT13 cipher.
 * @param msg - The ciphertext to decrypt.
 * @param symbols - The ordered alphabet.
 * @returns The recovered message.
 * @see SymPy `sympy.crypto.crypto.decipher_rot13`
 * @example
 * ```ts
 * import { decipherRot13 } from '@symjs/symjs';
 * decipherRot13('TBANILORNGNEZL'); // => GONAVYBEATARMY
 * ```
 */
export function decipherRot13(msg: string, symbols?: string): string {
  return decipherShift(msg, 13, symbols);
}

/**
 * Encrypts the message using the affine cipher.
 * @param msg - The plaintext to encode.
 * @param key - The multiplier and offset of the affine substitution.
 * @param symbols - The ordered alphabet.
 * @param inverse - Whether to match the inverse word as well.
 * @returns The ciphertext.
 * @throws RangeError when the multiplier is not invertible modulo the alphabet size.
 * @see SymPy `sympy.crypto.crypto.encipher_affine`
 * @example
 * ```ts
 * import { encipherAffine } from '@symjs/symjs';
 * encipherAffine('GO NAVY BEAT ARMY', [3, 1]); // => TROBMVENBGBALV
 * ```
 */
export function encipherAffine(msg: string, key: readonly [IntLike, IntLike], symbols?: string, inverse = false): string {
  const [m, , A] = prep(msg, '', symbols);
  const N = BigInt(A.length);
  let [a, b] = [asInt(key[0]), asInt(key[1])];
  if (gcd(a, N) !== 1n) throw new RangeError(`the key ${a} is not invertible modulo ${N}`);
  if (inverse) {
    const c = invert(a, N);
    [a, b] = [c, -b * c];
  }
  const B = chars(A).map((_c, i) => at(chars(A), Number(bmod(a * BigInt(i) + b, N)))).join('');
  return translate(m, A, B);
}

/**
 * Recovers the plaintext using the affine cipher.
 * @param msg - The ciphertext to decrypt.
 * @param key - The multiplier and offset of the affine substitution.
 * @param symbols - The ordered alphabet.
 * @returns The recovered message.
 * @throws RangeError when the multiplier is not invertible modulo the alphabet size.
 * @see SymPy `sympy.crypto.crypto.decipher_affine`
 * @example
 * ```ts
 * import { decipherAffine } from '@symjs/symjs';
 * decipherAffine('QTW', [3, 16]); // => ABC
 * ```
 */
export function decipherAffine(msg: string, key: readonly [IntLike, IntLike], symbols?: string): string {
  return encipherAffine(msg, key, symbols, true);
}

/**
 * Encrypts the message using the Atbash cipher.
 * @param msg - The plaintext to encode.
 * @param symbols - The ordered alphabet.
 * @returns The ciphertext.
 * @see SymPy `sympy.crypto.crypto.encipher_atbash`
 * @example
 * ```ts
 * import { encipherAtbash } from '@symjs/symjs';
 * encipherAtbash('GONAVYBEATARMY'); // => TLMZEBYVZGZINB
 * ```
 */
export function encipherAtbash(msg: string, symbols?: string): string {
  return encipherAffine(msg, [25, 25], symbols);
}

/**
 * Recovers the plaintext using the Atbash cipher.
 * @param msg - The ciphertext to decrypt.
 * @param symbols - The ordered alphabet.
 * @returns The recovered message.
 * @see SymPy `sympy.crypto.crypto.decipher_atbash`
 * @example
 * ```ts
 * import { decipherAtbash } from '@symjs/symjs';
 * decipherAtbash('GONAVYBEATARMY'); // => TLMZEBYVZGZINB
 * ```
 */
export function decipherAtbash(msg: string, symbols?: string): string {
  return decipherAffine(msg, [25, 25], symbols);
}

/**
 * Encrypts the message using the substitution cipher.
 * @param msg - The plaintext to encode.
 * @param old - The source alphabet or character substitution map.
 * @param nw - The replacement characters in source-alphabet order.
 * @returns The ciphertext.
 * @throws RangeError when the source and replacement alphabets have different lengths.
 * @see SymPy `sympy.crypto.crypto.encipher_substitution`
 * @example
 * ```ts
 * import { encipherSubstitution } from '@symjs/symjs';
 * encipherSubstitution('60N^V4B3^T^RM4', '034^6', 'OEYAG'); // => GONAVYBEATARMY
 * ```
 */
export function encipherSubstitution(msg: string, old: string | ReadonlyMap<string, string> | Readonly<Record<string, string>>, nw?: string): string {
  if (typeof old === 'string') {
    if (nw === undefined || nw.length !== old.length) throw new RangeError('oldchars and newchars have different lengths');
    return translate(msg, old, nw);
  }
  const pairs = old instanceof Map ? [...old] : Object.entries(old);
  // longer keys first, as SymPy's replace does
  const sorted = [...pairs].sort((p, q) => q[0].length - p[0].length);
  let out = '';
  for (let i = 0; i < msg.length; ) {
    const hit = sorted.find(([k]) => k.length > 0 && msg.startsWith(k, i));
    if (hit) {
      out += hit[1];
      i += hit[0].length;
    } else out += msg.charAt(i++);
  }
  return out;
}

function vigenere(msg: string, key: string, symbols: string | undefined, sign: 1 | -1): string {
  const [m, k, A] = prep(msg, key, symbols);
  const idx = new Map(chars(A).map((c, i) => [c, i] as const));
  const K = chars(k).map((c) => getOrThrow(idx, c));
  const N = A.length;
  return chars(m).map((c, i) => A.charAt((((getOrThrow(idx, c) + sign * at(K, i % K.length)) % N) + N) % N)).join('');
}

/**
 * Encrypts the message using the Vigenère cipher.
 * @param msg - The plaintext to encode.
 * @param key - The keyword repeated along the message.
 * @param symbols - The ordered alphabet.
 * @returns The ciphertext.
 * @see SymPy `sympy.crypto.crypto.encipher_vigenere`
 * @example
 * ```ts
 * import { encipherVigenere } from '@symjs/symjs';
 * encipherVigenere('meet me on monday', 'encrypt'); // => QRGKKTHRZQEBPR
 * ```
 */
export function encipherVigenere(msg: string, key: string, symbols?: string): string {
  return vigenere(msg, key, symbols, 1);
}

/**
 * Recovers the plaintext using the Vigenère cipher.
 * @param msg - The ciphertext to decrypt.
 * @param key - The keyword repeated along the message.
 * @param symbols - The ordered alphabet.
 * @returns The recovered message.
 * @see SymPy `sympy.crypto.crypto.decipher_vigenere`
 * @example
 * ```ts
 * import { decipherVigenere } from '@symjs/symjs';
 * decipherVigenere('QRGK kt HRZQE BPR', 'encrypt'); // => MEETMEONMONDAY
 * ```
 */
export function decipherVigenere(msg: string, key: string, symbols?: string): string {
  return vigenere(msg, key, symbols, -1);
}

function hill(msg: string, key: Matrix, symbols: string | undefined, pad: string, decipher: boolean): string {
  if (key.rows !== key.cols) throw new RangeError('the key must be a square matrix');
  if (pad.length !== 1) throw new RangeError('pad must be one character');
  const [m, p, A] = prep(msg, decipher ? '' : pad, symbols);
  const idx = new Map(chars(A).map((c, i) => [c, i] as const));
  const P = chars(m).map((c) => getOrThrow(idx, c));
  const N = A.length;
  const k = key.cols;
  const r = P.length % k;
  if (r) P.push(...Array<number>(k - r).fill(decipher ? 0 : getOrThrow(idx, p)));
  const K = decipher ? invMod(key, N) : key;
  let out = '';
  for (let j = 0; j < P.length; j += k) {
    const v = K.mul(Matrix.fromFunction(k, 1, (i) => at(P, j + i)));
    for (let i = 0; i < k; i++) {
      const c = v.get(i, 0);
      if (!(c instanceof Rational) || c.q !== 1n) throw new TypeError('the key must be an integer matrix');
      out += A.charAt(Number(bmod(c.p, BigInt(N))));
    }
  }
  return out;
}

/**
 * Encrypts the message using the Hill cipher.
 * @param msg - The plaintext to encode.
 * @param key - The square key matrix, invertible modulo the alphabet length.
 * @param symbols - The ordered alphabet.
 * @param pad - The character used to complete a partial block.
 * @returns The ciphertext.
 * @throws RangeError when the key is not square or the padding is not one character.
 * @throws TypeError when a key entry is not an integer.
 * @see SymPy `sympy.crypto.crypto.encipher_hill`
 * @example
 * ```ts
 * import { Matrix, encipherHill } from '@symjs/symjs';
 * encipherHill('meet me on monday', Matrix.of([[1, 2], [3, 5]])); // => UEQDUEODOCTCWQ
 * ```
 */
export function encipherHill(msg: string, key: Matrix, symbols?: string, pad = 'Q'): string {
  return hill(msg, key, symbols, pad, false);
}

/**
 * Recovers the plaintext using the Hill cipher.
 * @param msg - The ciphertext to decrypt.
 * @param key - The square key matrix, invertible modulo the alphabet length.
 * @param symbols - The ordered alphabet.
 * @returns The recovered message.
 * @throws RangeError when the key is not square.
 * @throws TypeError when a key entry is not an integer.
 * @throws NonInvertibleMatrixError when the key is singular modulo the alphabet length.
 * @see SymPy `sympy.crypto.crypto.decipher_hill`
 * @example
 * ```ts
 * import { Matrix, decipherHill } from '@symjs/symjs';
 * decipherHill('HD', Matrix.of([[1, 1, 1, 2], [0, 1, 1, 0], [2, 2, 3, 4], [1, 1, 0, 1]])); // => ORMV
 * ```
 */
export function decipherHill(msg: string, key: Matrix, symbols?: string): string {
  return hill(msg, key, symbols, 'Q', true);
}

/** The side of the square of an alphabet, or a RangeError. */
function squareSide(n: number): number {
  const N = Math.round(Math.sqrt(n));
  if (N * N !== n) throw new RangeError(`Length of alphabet (${n}) is not a square number.`);
  return N;
}

function bifidTable(key: string, A: string): [Map<string, [number, number]>, number] {
  const N = squareSide(A.length);
  let longKey = chars((uniqChars(key) || A));
  if (longKey.length < N * N) longKey = [...longKey, ...chars(A).filter((x) => !longKey.includes(x))];
  return [new Map(longKey.map((ch, i) => [ch, [Math.floor(i / N), i % N]] as const)), N];
}

/**
 * Encrypts the message using the Bifid cipher.
 * @param msg - The plaintext to encode.
 * @param key - The keyword defining the substitution alphabet.
 * @param symbols - The ordered alphabet.
 * @returns The ciphertext.
 * @throws RangeError when the alphabet length is not a perfect square.
 * @see SymPy `sympy.crypto.crypto.encipher_bifid`
 * @example
 * ```ts
 * import { encipherBifid } from '@symjs/symjs';
 * encipherBifid('hello world!', ''); // => bmtwmg-bIo*w
 * ```
 */
export function encipherBifid(msg: string, key: string, symbols?: string): string {
  const [m, k, A] = prep(msg, key, symbols, PRINTABLE);
  const [rowCol, N] = bifidTable(k, A);
  const rc = chars(m).map((x) => getOrThrow(rowCol, x));
  const seq = [...rc.map(([r]) => r), ...rc.map(([, c]) => c)];
  const ch = new Map([...rowCol].map(([c, [r, q]]) => [r * N + q, c] as const));
  let out = '';
  for (let i = 0; i < seq.length; i += 2) out += getOrThrow(ch, at(seq, i) * N + at(seq, i + 1));
  return out;
}

/**
 * Recovers the plaintext using the Bifid cipher.
 * @param msg - The ciphertext to decrypt.
 * @param key - The keyword defining the substitution alphabet.
 * @param symbols - The ordered alphabet.
 * @returns The recovered message.
 * @throws RangeError when the alphabet length is not a perfect square.
 * @see SymPy `sympy.crypto.crypto.decipher_bifid`
 * @example
 * ```ts
 * import { decipherBifid } from '@symjs/symjs';
 * decipherBifid('\nIEILH\nHFSTS\nFQYEJ', 'GOLDBUG', 'ABCDEFGHIKLMNOPQRSTUVWXYZ'); // => MEETMEONMONDAY
 * ```
 */
export function decipherBifid(msg: string, key: string, symbols?: string): string {
  const [m, , A] = prep(msg, '', symbols, PRINTABLE);
  const [rowCol, N] = bifidTable(key, A);
  const rc = chars(m).flatMap((c) => getOrThrow(rowCol, c));
  const n = m.length;
  const ch = new Map([...rowCol].map(([c, [r, q]]) => [r * N + q, c] as const));
  let out = '';
  for (let i = 0; i < n; i++) out += getOrThrow(ch, at(rc, i) * N + at(rc, n + i));
  return out;
}

/**
 * Arranges the characters of a square-length key into a square matrix.
 * @param key - The keyword defining the substitution alphabet.
 * @returns The resulting matrix.
 * @throws RangeError when the alphabet length is not a perfect square.
 * @see SymPy `sympy.crypto.crypto.bifid_square`
 * @example
 * ```ts
 * import { bifidSquare } from '@symjs/symjs';
 * bifidSquare('ABCD').row(0).toArray()[0]; // => [A, B]
 * ```
 */
export function bifidSquare(key: string | readonly string[]): Matrix {
  const A = uniqChars(typeof key === 'string' ? key : key.join(''));
  const n = squareSide(A.length);
  return Matrix.fromFunction(n, n, (i, j) => new Sym(A.charAt(n * i + j)));
}

function bifidN(msg: string, key: string, alphabet: string, decipher: boolean): string {
  const [m, k] = prep(msg.toUpperCase(), key.toUpperCase(), undefined, alphabet);
  const padded = paddedKey(k, alphabet);
  return decipher ? decipherBifid(m, '', padded) : encipherBifid(m, '', padded);
}

function bifidNSquare(alphabet: string, key?: string): Matrix {
  if (!key) return bifidSquare(alphabet);
  const [, k] = prep('', key.toUpperCase(), undefined, alphabet);
  return bifidSquare(paddedKey(k, alphabet));
}

/**
 * Encrypts the message using the 5-by-5 Bifid cipher.
 * @param msg - The plaintext to encode.
 * @param key - The keyword defining the substitution alphabet.
 * @returns The ciphertext.
 * @see SymPy `sympy.crypto.crypto.encipher_bifid5`
 * @example
 * ```ts
 * import { encipherBifid5 } from '@symjs/symjs';
 * encipherBifid5('meet me on friday', 'gold bug'); // => IEILEHFSTSFXEE
 * ```
 */
export function encipherBifid5(msg: string, key: string): string {
  return bifidN(msg, key, bifid5, false);
}

/**
 * Recovers the plaintext using the 5-by-5 Bifid cipher.
 * @param msg - The ciphertext to decrypt.
 * @param key - The keyword defining the substitution alphabet.
 * @returns The recovered message.
 * @see SymPy `sympy.crypto.crypto.decipher_bifid5`
 * @example
 * ```ts
 * import { decipherBifid5 } from '@symjs/symjs';
 * decipherBifid5('ch', 'c'); // => AB
 * ```
 */
export function decipherBifid5(msg: string, key: string): string {
  return bifidN(msg, key, bifid5, true);
}

/**
 * The 5x5 square of the key padded with the letters without J.
 * @param key - The keyword defining the substitution alphabet.
 * @returns The resulting matrix.
 * @see SymPy `sympy.crypto.crypto.bifid5_square`
 * @example
 * ```ts
 * import { bifid5Square } from '@symjs/symjs';
 * bifid5Square('gold bug').row(0).toArray()[0]; // => [G, O, L, D, B]
 * ```
 */
export function bifid5Square(key?: string): Matrix {
  return bifidNSquare(bifid5, key);
}

/**
 * Encrypts the message using the 6-by-6 Bifid cipher.
 * @param msg - The plaintext to encode.
 * @param key - The keyword defining the substitution alphabet.
 * @returns The ciphertext.
 * @see SymPy `sympy.crypto.crypto.encipher_bifid6`
 * @example
 * ```ts
 * import { encipherBifid6 } from '@symjs/symjs';
 * encipherBifid6('meet me on monday at 8am', 'gold bug'); // => KFKLJJHF5MMMKTFRGPL
 * ```
 */
export function encipherBifid6(msg: string, key: string): string {
  return bifidN(msg, key, bifid6, false);
}

/**
 * Recovers the plaintext using the 6-by-6 Bifid cipher.
 * @param msg - The ciphertext to decrypt.
 * @param key - The keyword defining the substitution alphabet.
 * @returns The recovered message.
 * @see SymPy `sympy.crypto.crypto.decipher_bifid6`
 * @example
 * ```ts
 * import { decipherBifid6 } from '@symjs/symjs';
 * decipherBifid6('ci', 'c'); // => AB
 * ```
 */
export function decipherBifid6(msg: string, key: string): string {
  return bifidN(msg, key, bifid6, true);
}

/**
 * The 6x6 square of the key padded with the letters and digits.
 * @param key - The keyword defining the substitution alphabet.
 * @returns The resulting matrix.
 * @see SymPy `sympy.crypto.crypto.bifid6_square`
 * @example
 * ```ts
 * import { bifid6Square } from '@symjs/symjs';
 * bifid6Square('gold bug').row(0).toArray()[0]; // => [G, O, L, D, B, U]
 * ```
 */
export function bifid6Square(key?: string): Matrix {
  return bifidNSquare(bifid6, key);
}

// ---------------------------------------------------------------------------
// RSA

/** Options of the RSA key functions. */
export interface RsaKeyOptions {
  /** The totient used to determine the exponent, either Euler’s (default) or Carmichael’s. */
  totient?: 'Euler' | 'Carmichael';
  /** With the Carmichael totient: the key plus index times the totient. */
  index?: IntLike;
  /** Accept repeated prime factors. */
  multipower?: boolean;
}

const isOptions = (x: unknown): x is RsaKeyOptions => typeof x === 'object' && x !== null && !(x instanceof Rational);

function rsaKey(argsIn: readonly (IntLike | RsaKeyOptions)[], pub: boolean): [bigint, bigint] | false {
  const last = argsIn[argsIn.length - 1];
  const opts: RsaKeyOptions = isOptions(last) ? last : {};
  const args = argsIn.filter((a): a is IntLike => !isOptions(a)).map((a) => asInt(a));
  if (args.length < 2) return false;
  const totient = opts.totient ?? 'Euler';
  if (!(['Euler', 'Carmichael'] as readonly string[]).includes(totient)) throw new RangeError(`The argument totient=${String(totient)} should either be 'Euler', 'Carmichalel'.`);
  const index = opts.index === undefined ? undefined : asInt(opts.index);
  if (index !== undefined && totient !== 'Carmichael') throw new RangeError("Setting the 'index' keyword argument requires totientnotation to be specified as 'Carmichael'.");
  let primes = args.slice(0, -1);
  const e = at(args, args.length - 1);
  if (!primes.every((p) => isprime(p))) primes = primes.flatMap((p) => factorint(p, { multiple: true }));
  const n = primes.reduce((a, b) => a * b, 1n);
  const tally = new Map<bigint, bigint>();
  for (const p of primes) tally.set(p, (tally.get(p) ?? 0n) + 1n);
  let phi = 1n;
  for (const [p, k] of tally) {
    const t = p === 2n && k >= 3n && totient === 'Carmichael' ? 2n ** (k - 2n) : (p - 1n) * p ** (k - 1n);
    phi = totient === 'Euler' ? phi * t : (phi / gcd(phi, t)) * t;
  }
  if (gcd(e, phi) !== 1n) return false;
  if (pub) return [n, index === undefined ? e : bmod(e, phi) + index * phi];
  const d = invert(e, phi);
  return [n, index === undefined ? d : d + index * phi];
}

/**
 * Constructs the RSA modulus and public exponent.
 * @param args - The factors of the modulus followed by the exponent and optional totient and index settings.
 * @returns The pair `[n, e]`, or `false` for invalid key parameters.
 * @throws RangeError when the totient is unrecognized or an index is requested without the Carmichael totient.
 * @see SymPy `sympy.crypto.crypto.rsa_public_key`
 * @remarks SymPy prints this result as `(3233, 17)`.
 * @example
 * ```ts
 * import { rsaPublicKey } from '@symjs/symjs';
 * rsaPublicKey(61, 53, 17); // => [3233, 17]
 * ```
 */
export function rsaPublicKey(...args: (IntLike | RsaKeyOptions)[]): [bigint, bigint] | false {
  return rsaKey(args, true);
}

/**
 * Constructs the RSA modulus and private exponent.
 * @param args - The factors of the modulus followed by the exponent and optional totient and index settings.
 * @returns The pair `[n, d]`, or `false` for invalid key parameters.
 * @throws RangeError when the totient is unrecognized or an index is requested without the Carmichael totient.
 * @see SymPy `sympy.crypto.crypto.rsa_private_key`
 * @remarks SymPy prints this result as `(3233, 2753)`.
 * @example
 * ```ts
 * import { rsaPrivateKey } from '@symjs/symjs';
 * rsaPrivateKey(61, 53, 17); // => [3233, 2753]
 * ```
 */
export function rsaPrivateKey(...args: (IntLike | RsaKeyOptions)[]): [bigint, bigint] | false {
  return rsaKey(args, false);
}

function rsaPow(iIn: IntLike, key: readonly [IntLike, IntLike], factors?: readonly IntLike[]): bigint {
  const i = asInt(iIn);
  const [n, d] = [asInt(key[0]), asInt(key[1])];
  const fs = (factors ?? []).map((f) => asInt(f));
  const coprime = fs.every((a, j) => fs.slice(j + 1).every((b) => gcd(a, b) === 1n));
  if (!fs.length || fs.reduce((a, b) => a * b, 1n) !== n || !coprime) return powmod(i, d, n);
  // the Chinese remainder theorem over the coprime factors
  let r = 0n;
  for (const p of fs) {
    const M = n / p;
    r += powmod(i, d, p) * M * invert(M % p, p);
  }
  return bmod(r, n);
}

/**
 * Encrypts the message using the RSA cipher.
 * @param i - The integer message representative.
 * @param key - The public key used for encryption.
 * @param factors - The prime factors of the modulus for Chinese remainder evaluation.
 * @returns The ciphertext.
 * @see SymPy `sympy.crypto.crypto.encipher_rsa`
 * @example
 * ```ts
 * import { encipherRsa } from '@symjs/symjs';
 * encipherRsa(12, [15, 7]); // => 3
 * ```
 */
export function encipherRsa(i: IntLike, key: readonly [IntLike, IntLike], factors?: readonly IntLike[]): bigint {
  return rsaPow(i, key, factors);
}

/**
 * Recovers the plaintext using the RSA cipher.
 * @param i - The ciphertext representative.
 * @param key - The private decryption key.
 * @param factors - The prime factors of the modulus for Chinese remainder evaluation.
 * @returns The recovered message.
 * @see SymPy `sympy.crypto.crypto.decipher_rsa`
 * @example
 * ```ts
 * import { decipherRsa } from '@symjs/symjs';
 * decipherRsa(3, [15, 7]); // => 12
 * ```
 */
export function decipherRsa(i: IntLike, key: readonly [IntLike, IntLike], factors?: readonly IntLike[]): bigint {
  return rsaPow(i, key, factors);
}

function kidRsa(a0: IntLike, b0: IntLike, A0: IntLike, B0: IntLike): [bigint, bigint, bigint] {
  const [a, b, A, B] = [asInt(a0), asInt(b0), asInt(A0), asInt(B0)];
  const M = a * b - 1n;
  const e = A * M + a;
  const d = B * M + b;
  return [(e * d - 1n) / M, e, d];
}

/**
 * The Kid RSA public key (n, e).
 * @param a - The first base parameter of the Kid RSA key.
 * @param b - The second base parameter of the Kid RSA key.
 * @param A - The multiplier used to construct the public exponent.
 * @param B - The multiplier used to construct the private exponent.
 * @returns The modulus and public multiplier.
 * @see SymPy `sympy.crypto.crypto.kid_rsa_public_key`
 * @example
 * ```ts
 * import { kidRsaPublicKey } from '@symjs/symjs';
 * kidRsaPublicKey(3, 4, 5, 6); // => [369, 58]
 * ```
 */
export function kidRsaPublicKey(a: IntLike, b: IntLike, A: IntLike, B: IntLike): [bigint, bigint] {
  const [n, e] = kidRsa(a, b, A, B);
  return [n, e];
}

/**
 * The Kid RSA private key (n, d).
 * @param a - The first base parameter of the Kid RSA key.
 * @param b - The second base parameter of the Kid RSA key.
 * @param A - The multiplier used to construct the public exponent.
 * @param B - The multiplier used to construct the private exponent.
 * @returns The modulus and private multiplier.
 * @see SymPy `sympy.crypto.crypto.kid_rsa_private_key`
 * @example
 * ```ts
 * import { kidRsaPrivateKey } from '@symjs/symjs';
 * kidRsaPrivateKey(3, 4, 5, 6); // => [369, 70]
 * ```
 */
export function kidRsaPrivateKey(a: IntLike, b: IntLike, A: IntLike, B: IntLike): [bigint, bigint] {
  const [n, , d] = kidRsa(a, b, A, B);
  return [n, d];
}

/**
 * Encrypts the message using the Kid RSA cipher.
 * @param msg - The plaintext to encode.
 * @param key - The public key used for encryption.
 * @returns The ciphertext.
 * @see SymPy `sympy.crypto.crypto.encipher_kid_rsa`
 * @example
 * ```ts
 * import { encipherKidRsa } from '@symjs/symjs';
 * encipherKidRsa(200, [369, 58]); // => 161
 * ```
 */
export function encipherKidRsa(msg: IntLike, key: readonly [IntLike, IntLike]): bigint {
  return bmod(asInt(msg) * asInt(key[1]), asInt(key[0]));
}

/**
 * Recovers the plaintext using the Kid RSA cipher.
 * @param msg - The ciphertext to decrypt.
 * @param key - The private decryption key.
 * @returns The recovered message.
 * @see SymPy `sympy.crypto.crypto.decipher_kid_rsa`
 * @example
 * ```ts
 * import { decipherKidRsa } from '@symjs/symjs';
 * decipherKidRsa(161, [369, 70]); // => 200
 * ```
 */
export function decipherKidRsa(msg: IntLike, key: readonly [IntLike, IntLike]): bigint {
  return encipherKidRsa(msg, key);
}

// ---------------------------------------------------------------------------
// Morse code

const MORSE: Readonly<Record<string, string>> = {
  '.-': 'A', '-...': 'B', '-.-.': 'C', '-..': 'D', '.': 'E', '..-.': 'F', '--.': 'G', '....': 'H', '..': 'I', '.---': 'J', '-.-': 'K', '.-..': 'L', '--': 'M',
  '-.': 'N', '---': 'O', '.--.': 'P', '--.-': 'Q', '.-.': 'R', '...': 'S', '-': 'T', '..-': 'U', '...-': 'V', '.--': 'W', '-..-': 'X', '-.--': 'Y', '--..': 'Z',
  '-----': '0', '.----': '1', '..---': '2', '...--': '3', '....-': '4', '.....': '5', '-....': '6', '--...': '7', '---..': '8', '----.': '9',
  '.-.-.-': '.', '--..--': ',', '---...': ':', '-.-.-.': ';', '..--..': '?', '-....-': '-', '..--.-': '_', '-.--.': '(', '-.--.-': ')', '.----.': "'",
  '-...-': '=', '.-.-.': '+', '-..-.': '/', '.--.-.': '@', '...-..-': '$', '-.-.--': '!',
};
/**
 * Maps Morse codewords to their text characters.
 * @see SymPy `sympy.crypto.crypto.morse_char`
 */
export const morseChar: ReadonlyMap<string, string> = new Map(Object.entries(MORSE));
/**
 * Maps text characters to their Morse codewords.
 * @see SymPy `sympy.crypto.crypto.char_morse`
 */
export const charMorse: ReadonlyMap<string, string> = new Map(Object.entries(MORSE).map(([k, v]) => [v, k] as const));

/**
 * The Morse code of msg, letters separated by sep and
 * words by sep twice; characters without a code are dropped.
 * @param msg - The plaintext to encode.
 * @param sep - The separator between encoded letters.
 * @param mapping - The mapping from letters to codewords.
 * @returns The Morse code of msg, letters separated by sep and words by sep twice.
 * @throws RangeError when the separator is a character in the mapping.
 * @see SymPy `sympy.crypto.crypto.encode_morse`
 * @example
 * ```ts
 * import { encodeMorse } from '@symjs/symjs';
 * encodeMorse('ATTACK RIGHT FLANK'); // => .-|-|-|.-|-.-.|-.-||.-.|..|--.|....|-||..-.|.-..|.-|-.|-.-
 * ```
 */
export function encodeMorse(msg: string, sep = '|', mapping: ReadonlyMap<string, string> = charMorse): string {
  if (mapping.has(sep)) throw new RangeError('the separator must not be a mapped character');
  const wordSep = sep + sep;
  const suffix = msg.length > 0 && /\s$/.test(msg);
  const words = msg
    .split(/\s+/)
    .filter(Boolean)
    .map((w) => chars(w).filter((c) => mapping.has(c)))
    .filter((w) => w.length);
  return words.map((w) => w.map((c) => getOrThrow(mapping, c)).join(sep)).join(wordSep) + (suffix ? wordSep : '');
}

/**
 * The text of Morse code (letters separated by sep, words by sep twice).
 * @param msg - The ciphertext to decrypt.
 * @param sep - The separator between encoded letters.
 * @param mapping - The mapping from codewords to letters.
 * @returns The formatted text.
 * @see SymPy `sympy.crypto.crypto.decode_morse`
 * @example
 * ```ts
 * import { decodeMorse } from '@symjs/symjs';
 * decodeMorse('--|---|...-|.||.|.-|...|-'); // => MOVE EAST
 * ```
 */
export function decodeMorse(msg: string, sep = '|', mapping: ReadonlyMap<string, string> = morseChar): string {
  const wordSep = sep + sep;
  let s = msg;
  while (s.startsWith(sep)) s = s.slice(1);
  while (s.endsWith(sep)) s = s.slice(0, -1);
  return s
    .split(wordSep)
    .map((w) =>
      w
        .split(sep)
        .map((c) => getOrThrow(mapping, c))
        .join(''),
    )
    .join(' ');
}

// ---------------------------------------------------------------------------
// Linear feedback shift registers

/**
 * The first n terms of the LFSR sequence over GF(p)
 * with the given key (coefficients) and fill (initial terms).
 * @param key - The feedback coefficients in register order.
 * @param fill - The initial contents of the shift register.
 * @param n - The number of terms to generate.
 * @param opts - The modulus of the coefficient field (default 2).
 * @returns The first `n` register outputs.
 * @see SymPy `sympy.crypto.crypto.lfsr_sequence`
 * @example
 * ```ts
 * import { lfsrSequence } from '@symjs/symjs';
 * lfsrSequence([1, 0, 0, 1], [1, 1, 0, 1], 10); // => [1, 1, 0, 1, 0, 1, 1, 0, 0, 1]
 * ```
 */
export function lfsrSequence(key: readonly IntLike[], fill: readonly IntLike[], n: number, opts: { modulus?: IntLike } = {}): bigint[] {
  const p = asInt(opts.modulus ?? 2);
  const K = key.map((x) => asInt(x));
  let s = fill.map((x) => bmod(asInt(x), p));
  const out: bigint[] = [];
  for (let i = 0; i < n; i++) {
    out.push(at(s, 0));
    const x = s.reduce((acc, v, j) => acc + at(K, j) * v, 0n);
    s = [...s.slice(1), bmod(x, p)];
  }
  return out;
}

/**
 * The autocorrelation of the binary sequence L of period P at shift k.
 * @param L - One period of the binary sequence.
 * @param P - The period of the sequence.
 * @param k - The cyclic shift.
 * @returns The normalized correlation at the specified shift.
 * @see SymPy `sympy.crypto.crypto.lfsr_autocorrelation`
 * @example
 * ```ts
 * import { lfsrAutocorrelation } from '@symjs/symjs';
 * lfsrAutocorrelation([1n, 1n, 0n, 1n, 0n, 1n, 1n, 0n, 0n, 1n, 0n, 0n, 0n, 1n, 1n, 1n, 1n, 0n, 1n, 0n], 15, 0); // => 1
 * ```
 */
export function lfsrAutocorrelation(L: readonly IntLike[], P: number, k: number): Expr {
  const L0 = L.slice(0, P).map((x) => asInt(x));
  const L1 = [...L0, ...L0.slice(0, k)];
  let tot = 0n;
  for (let i = 0; i < P; i++) tot += (at(L1, i) + at(L1, i + k)) % 2n === 0n ? 1n : -1n;
  return Rational.of(tot, BigInt(P));
}

/**
 * The connection polynomial (in x) of the
 * LFSR sequence s over GF(p), by the Berlekamp-Massey algorithm.
 * @param sIn - The observed sequence of register outputs.
 * @param opts - The modulus of the coefficient field (default 2).
 * @returns The connection polynomial in `x`.
 * @see SymPy `sympy.crypto.crypto.lfsr_connection_polynomial`
 * @example
 * ```ts
 * import { lfsrConnectionPolynomial } from '@symjs/symjs';
 * lfsrConnectionPolynomial([1n, 0n, 0n, 1n, 0n, 0n, 1n, 0n, 0n, 1n, 0n, 0n, 1n, 0n, 0n, 1n, 0n, 0n, 1n, 0n], { modulus: 2n }); // => x**3 + 1
 * ```
 */
export function lfsrConnectionPolynomial(sIn: readonly IntLike[], opts: { modulus?: IntLike } = {}): Expr {
  const p = asInt(opts.modulus ?? 2);
  const s = sIn.map((v) => asInt(v));
  // polynomials as coefficient lists (index = degree)
  type Pl = bigint[];
  const trim = (c: Pl): Pl => {
    const r = [...c];
    while (r.length > 1 && r[r.length - 1] === 0n) r.pop();
    return r;
  };
  const subShift = (C: Pl, f: bigint, m: number, B: Pl): Pl => {
    const r = [...C];
    B.forEach((c, i) => {
      while (r.length <= i + m) r.push(0n);
      r[i + m] = at(r, i + m) - f * c;
    });
    return trim(r);
  };
  let [C, B, m, b, L, N] = [[1n] as Pl, [1n] as Pl, 1, 1n, 0, 0];
  while (N < s.length) {
    let d = at(s, N);
    if (L > 0) {
      const r = Math.min(L + 1, C.length);
      for (let i = 1; i < r; i++) d += at(C, i) * at(s, N - i);
      d = bmod(d, p);
    }
    if (d === 0n) m++;
    else {
      const f = d * bmod(b ** (p - 2n), p);
      const T = C;
      C = subShift(C, f, m, B);
      if (2 * L > N) m++;
      else {
        L = N + 1 - L;
        m = 1;
        b = d;
        B = T;
      }
    }
    N++;
  }
  const x = new Sym('x');
  return add(...C.map((c, i) => mul(bmod(c, p), pow(x, i))));
}

// ---------------------------------------------------------------------------
// randomness as SymPy's _randrange and _randint

type Rand = (a: bigint, b: bigint) => bigint;

const isSeq = (s: CryptoSeed | undefined): s is readonly IntLike[] => Array.isArray(s);

function fromSeed(seed: CryptoSeed | undefined, inclusive: boolean): Rand {
  if (!isSeq(seed)) {
    if (seed !== undefined) rng.seed(asInt(seed));
    return (a, b) => (inclusive ? rng.randint(a, b) : rng.randrange(a, b));
  }
  const seq = seed.map((x) => asInt(x)).reverse();
  return (a, b) => {
    if (b - a < (inclusive ? 0n : 1n)) throw new RangeError('_randrange got empty range');
    for (;;) {
      const x = seq.pop();
      if (x === undefined) throw new RangeError('_randrange sequence was too short');
      if (a <= x && (inclusive ? x <= b : x < b)) return x;
    }
  };
}

// ---------------------------------------------------------------------------
// ElGamal and Diffie-Hellman

/**
 * Generates an ElGamal private key with a prime modulus, primitive root and secret exponent.
 * @param digit - The exponent defining the lower bound on the prime modulus.
 * @param seed - The seed or prescribed random draws.
 * @returns The prime, primitive root and private exponent.
 * @see SymPy `sympy.crypto.crypto.elgamal_private_key`
 * @example
 * ```ts
 * import { elgamalPrivateKey } from '@symjs/symjs';
 * elgamalPrivateKey(5, [3]); // => [37, 2, 3]
 * ```
 */
export function elgamalPrivateKey(digit = 10, seed?: CryptoSeed): [bigint, bigint, bigint] {
  const randrange = fromSeed(seed, false);
  const p = nextprime(2n ** BigInt(digit));
  return [p, primitiveRootOf(p), randrange(2n, p)];
}

function primitiveRootOf(p: bigint): bigint {
  // a prime has a primitive root
  return expectType(primitiveRoot(p), (x): x is bigint => typeof x === 'bigint', 'primitive root');
}

/**
 * Derives the ElGamal public key from the private exponent.
 * @param key - The private key from which to derive the public key.
 * @returns The prime, primitive root and public residue.
 * @see SymPy `sympy.crypto.crypto.elgamal_public_key`
 * @example
 * ```ts
 * import { elgamalPublicKey } from '@symjs/symjs';
 * elgamalPublicKey([1031, 14, 636]); // => [1031, 14, 212]
 * ```
 */
export function elgamalPublicKey(key: readonly [IntLike, IntLike, IntLike]): [bigint, bigint, bigint] {
  const [p, r, e] = [asInt(key[0]), asInt(key[1]), asInt(key[2])];
  return [p, r, powmod(r, e, p)];
}

/**
 * Encrypts the message using the ElGamal cipher.
 * @param iIn - The integer message representative.
 * @param key - The public key used for encryption.
 * @param seed - The seed or prescribed random draws.
 * @returns The ciphertext.
 * @throws RangeError when the message is outside the residue range.
 * @see SymPy `sympy.crypto.crypto.encipher_elgamal`
 * @example
 * ```ts
 * import { encipherElgamal } from '@symjs/symjs';
 * encipherElgamal(36, [37, 2, 8], [3]); // => [8, 6]
 * ```
 */
export function encipherElgamal(iIn: IntLike, key: readonly [IntLike, IntLike, IntLike], seed?: CryptoSeed): [bigint, bigint] {
  const i = asInt(iIn);
  const [p, r, e] = [asInt(key[0]), asInt(key[1]), asInt(key[2])];
  if (i < 0n || i >= p) throw new RangeError(`Message (${i}) should be in range(${p})`);
  const a = fromSeed(seed, false)(2n, p);
  return [powmod(r, a, p), bmod(i * powmod(e, a, p), p)];
}

/**
 * Recovers the plaintext using the ElGamal cipher.
 * @param msg - The ciphertext to decrypt.
 * @param key - The private decryption key.
 * @returns The recovered message.
 * @see SymPy `sympy.crypto.crypto.decipher_elgamal`
 * @example
 * ```ts
 * import { decipherElgamal } from '@symjs/symjs';
 * decipherElgamal([8, 6], [37, 2, 3]); // => 36
 * ```
 */
export function decipherElgamal(msg: readonly [IntLike, IntLike], key: readonly [IntLike, IntLike, IntLike]): bigint {
  const [p, d] = [asInt(key[0]), asInt(key[2])];
  const [c1, c2] = [asInt(msg[0]), asInt(msg[1])];
  return bmod(invert(powmod(c1, d, p), p) * c2, p);
}

/**
 * Generates a Diffie–Hellman modulus, generator and private exponent.
 * @param digit - The exponent defining the lower bound on the prime modulus.
 * @param seed - The seed or prescribed random draws.
 * @returns The prime, generator and private exponent.
 * @see SymPy `sympy.crypto.crypto.dh_private_key`
 * @example
 * ```ts
 * import { dhPrivateKey } from '@symjs/symjs';
 * dhPrivateKey(5, [3]); // => [37, 2, 3]
 * ```
 */
export function dhPrivateKey(digit = 10, seed?: CryptoSeed): [bigint, bigint, bigint] {
  const p = nextprime(2n ** BigInt(digit));
  const g = primitiveRootOf(p);
  return [p, g, fromSeed(seed, false)(2n, p)];
}

/**
 * Computes the Diffie–Hellman public value from the private exponent.
 * @param key - The private key from which to derive the public key.
 * @returns The prime, generator and public residue.
 * @see SymPy `sympy.crypto.crypto.dh_public_key`
 * @example
 * ```ts
 * import { dhPublicKey } from '@symjs/symjs';
 * dhPublicKey([37, 2, 3]); // => [37, 2, 8]
 * ```
 */
export function dhPublicKey(key: readonly [IntLike, IntLike, IntLike]): [bigint, bigint, bigint] {
  return elgamalPublicKey(key);
}

/**
 * Computes the shared Diffie–Hellman value from a public key and a private exponent.
 * @param key - The other participant’s public key.
 * @param bIn - The private exponent.
 * @returns The shared Diffie–Hellman value from a public key and a private exponent.
 * @throws RangeError when the private exponent is outside the permitted interval.
 * @see SymPy `sympy.crypto.crypto.dh_shared_key`
 * @example
 * ```ts
 * import { dhSharedKey } from '@symjs/symjs';
 * dhSharedKey([37, 2, 8], 5); // => 23
 * ```
 */
export function dhSharedKey(key: readonly [IntLike, IntLike, IntLike], bIn: IntLike): bigint {
  const [p, x] = [asInt(key[0]), asInt(key[2])];
  const b = asInt(bIn);
  if (b <= 1n || b >= p) throw new RangeError(`Value of b should be greater 1 and less than prime ${p}.`);
  return powmod(x, b, p);
}

// ---------------------------------------------------------------------------
// Goldwasser-Micali and Blum-Goldwasser

function legendre(a: bigint, p: bigint): number {
  const sig = powmod(a, (p - 1n) / 2n, p);
  return sig === 1n ? 1 : sig === 0n ? 0 : -1;
}

/**
 * Validates the two primes that form a Goldwasser–Micali private key.
 * @param pIn - The first prime factor.
 * @param qIn - The second prime factor.
 * @returns The pair of private prime factors.
 * @throws RangeError when the prime factors coincide or either factor is not prime or either prime is even.
 * @see SymPy `sympy.crypto.crypto.gm_private_key`
 */
export function gmPrivateKey(pIn: IntLike, qIn: IntLike): [bigint, bigint] {
  const [p, q] = [asInt(pIn), asInt(qIn)];
  if (p === q) throw new RangeError(`expected distinct primes, got two copies of ${p}`);
  if (!isprime(p) || !isprime(q)) throw new RangeError(`first two arguments must be prime, got ${p} of ${q}`);
  if (p === 2n || q === 2n) throw new RangeError(`first two arguments must not be even, got ${p} of ${q}`);
  return [p, q];
}

/**
 * Constructs a Goldwasser–Micali public key using a common quadratic nonresidue of the two primes.
 * @param pIn - The first prime factor.
 * @param qIn - The second prime factor.
 * @param aIn - The candidate quadratic nonresidue.
 * @param seed - The seed or prescribed random draws.
 * @returns The pair `[a, N]`, or `false` if the supplied nonresidue is invalid.
 * @see SymPy `sympy.crypto.crypto.gm_public_key`
 */
export function gmPublicKey(pIn: IntLike, qIn: IntLike, aIn?: IntLike, seed?: CryptoSeed): [bigint, bigint] | false {
  const [p, q] = gmPrivateKey(pIn, qIn);
  const N = p * q;
  let a: bigint;
  if (aIn === undefined) {
    const randrange = fromSeed(seed, false);
    do a = randrange(0n, N);
    while (legendre(a, p) !== -1 || legendre(a, q) !== -1);
  } else {
    a = asInt(aIn);
    if (legendre(a, p) !== -1 || legendre(a, q) !== -1) return false;
  }
  return [a, N];
}

/**
 * Encrypts the message using the Goldwasser–Micali cipher.
 * @param iIn - The integer message representative.
 * @param key - The public key used for encryption.
 * @param seed - The seed or prescribed random draws.
 * @returns The ciphertext.
 * @throws RangeError when the message is negative.
 * @see SymPy `sympy.crypto.crypto.encipher_gm`
 */
export function encipherGm(iIn: IntLike, key: readonly [IntLike, IntLike], seed?: CryptoSeed): bigint[] {
  let i = asInt(iIn);
  if (i < 0n) throw new RangeError(`message must be a non-negative integer: got ${i} instead`);
  const [a, N] = [asInt(key[0]), asInt(key[1])];
  const bits: bigint[] = [];
  while (i > 0n) {
    bits.push(i % 2n);
    i /= 2n;
  }
  const randrange = fromSeed(seed, false);
  const coprime = (): bigint => {
    for (;;) {
      const y = randrange(0n, N);
      if (gcd(y, N) === 1n) return y;
    }
  };
  return bits.reverse().map((b) => bmod(coprime() ** 2n * a ** b, N));
}

/**
 * Recovers the plaintext using the Goldwasser–Micali cipher.
 * @param message - The ciphertext to decrypt.
 * @param key - The private decryption key.
 * @returns The recovered message.
 * @see SymPy `sympy.crypto.crypto.decipher_gm`
 * @example
 * ```ts
 * import { decipherGm } from '@symjs/symjs';
 * decipherGm([], [131, 89]); // => 0
 * ```
 */
export function decipherGm(message: readonly IntLike[], key: readonly [IntLike, IntLike]): bigint {
  const [p, q] = [asInt(key[0]), asInt(key[1])];
  let m = 0n;
  for (const c of message) {
    const x = asInt(c);
    const residue = legendre(x, p) > 0 && legendre(x, q) > 0;
    m = (m << 1n) + (residue ? 0n : 1n);
  }
  return m;
}

/**
 * Encrypts the message using the rail fence cipher.
 * @param message - The plaintext to encode.
 * @param rails - The number of rows in the zigzag.
 * @returns The ciphertext.
 * @see SymPy `sympy.crypto.crypto.encipher_railfence`
 * @example
 * ```ts
 * import { encipherRailfence } from '@symjs/symjs';
 * encipherRailfence('hello world', 3); // => horel ollwd
 * ```
 */
export function encipherRailfence(message: string, rails: number): string {
  const zig = railPattern(rails);
  return chars(message)
    .map((c, i) => [c, at(zig, i % zig.length)] as const)
    .sort((a, b) => a[1] - b[1])
    .map(([c]) => c)
    .join('');
}

/**
 * Recovers the plaintext using the rail fence cipher.
 * @param ciphertext - The ciphertext to decrypt.
 * @param rails - The number of rows in the zigzag.
 * @returns The recovered message.
 * @see SymPy `sympy.crypto.crypto.decipher_railfence`
 * @example
 * ```ts
 * import { decipherRailfence } from '@symjs/symjs';
 * decipherRailfence('horel ollwd', 3); // => hello world
 * ```
 */
export function decipherRailfence(ciphertext: string, rails: number): string {
  const zig = railPattern(rails);
  const idx = Array.from({ length: ciphertext.length }, (_x, i) => i).sort((a, b) => at(zig, a % zig.length) - at(zig, b % zig.length));
  const res = Array<string>(ciphertext.length).fill('');
  idx.forEach((i, j) => (res[i] = ciphertext.charAt(j)));
  return res.join('');
}

/** The rails 0, 1, ..., r - 1, r - 2, ..., 1 of the zigzag. */
function railPattern(rails: number): number[] {
  const r = Array.from({ length: rails }, (_x, i) => i);
  return [...r, ...r.slice(1, -1).reverse()];
}

/**
 * Validates the two primes that form a Blum–Goldwasser private key.
 * @param pIn - The first prime factor.
 * @param qIn - The second prime factor.
 * @returns The pair of private prime factors.
 * @throws RangeError when either factor is not prime or the prime factors coincide or either prime is not congruent to three modulo four.
 * @see SymPy `sympy.crypto.crypto.bg_private_key`
 */
export function bgPrivateKey(pIn: IntLike, qIn: IntLike): [bigint, bigint] {
  const [p, q] = [asInt(pIn), asInt(qIn)];
  if (!isprime(p) || !isprime(q)) throw new RangeError(`the two arguments must be prime, got ${p} and ${q}`);
  if (p === q) throw new RangeError(`the two arguments must be distinct, got two copies of ${p}. `);
  if ((p - 3n) % 4n !== 0n || (q - 3n) % 4n !== 0n) throw new RangeError(`the two arguments must be congruent to 3 mod 4, got ${p} and ${q}`);
  return [p, q];
}

/**
 * Computes the Blum–Goldwasser public modulus from the private primes.
 * @param p - The first prime factor.
 * @param q - The second prime factor.
 * @returns The public modulus.
 * @see SymPy `sympy.crypto.crypto.bg_public_key`
 */
export function bgPublicKey(p: IntLike, q: IntLike): bigint {
  const [a, b] = bgPrivateKey(p, q);
  return a * b;
}

/**
 * Encrypts the message using the Blum–Goldwasser cipher.
 * @param iIn - The integer message representative.
 * @param keyIn - The public key used for encryption.
 * @param seed - The seed or prescribed random draws.
 * @returns The ciphertext.
 * @throws RangeError when the message is negative.
 * @see SymPy `sympy.crypto.crypto.encipher_bg`
 */
export function encipherBg(iIn: IntLike, keyIn: IntLike, seed?: CryptoSeed): [bigint[], bigint] {
  let i = asInt(iIn);
  const key = asInt(keyIn);
  if (i < 0n) throw new RangeError(`message must be a non-negative integer: got ${i} instead`);
  const msg: bigint[] = [];
  while (i > 0n) {
    msg.push(i % 2n);
    i /= 2n;
  }
  msg.reverse();
  const L = BigInt(msg.length);
  const r = fromSeed(seed, true)(2n, key - 1n);
  let x = (r * r) % key;
  const xL = powmod(x, 2n ** L, key);
  const bits: bigint[] = [];
  for (let j = 0; j < msg.length; j++) {
    bits.push(x % 2n);
    x = (x * x) % key;
  }
  return [msg.map((m, j) => m ^ at(bits, j)), xL];
}

/**
 * Recovers the plaintext using the Blum–Goldwasser cipher.
 * @param message - The ciphertext to decrypt.
 * @param key - The private decryption key.
 * @returns The recovered message.
 * @see SymPy `sympy.crypto.crypto.decipher_bg`
 * @example
 * ```ts
 * import { decipherBg } from '@symjs/symjs';
 * decipherBg([[], 9], [11, 43]); // => 0
 * ```
 */
export function decipherBg(message: readonly [readonly IntLike[], IntLike], key: readonly [IntLike, IntLike]): bigint {
  const [p, q] = [asInt(key[0]), asInt(key[1])];
  const bitsIn = message[0].map((b) => asInt(b));
  const y = asInt(message[1]);
  const n = p * q;
  const L = BigInt(bitsIn.length);
  const rp = powmod(y, ((p + 1n) / 4n) ** L, p);
  const rq = powmod(y, ((q + 1n) / 4n) ** L, q);
  let x = bmod(q * invert(q, p) * rp + p * invert(p, q) * rq, n);
  let m = 0n;
  for (const b of bitsIn) {
    m = m * 2n + (b ^ (x % 2n));
    x = (x * x) % n;
  }
  return m;
}
