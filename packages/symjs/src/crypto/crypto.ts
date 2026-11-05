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
 * SymPy AZ: the uppercase letters; or the letters of s (a string or a list
 * of strings) in upper case, other characters removed.
 */
export function AZ(): string;
export function AZ(s: string): string;
export function AZ(s: readonly string[]): string[];
export function AZ(s?: string | readonly string[]): string | string[] {
  if (s === undefined || s.length === 0) return UPPER;
  const one = (x: string): string => checkAndJoin(x.toUpperCase().split(/\s+/), UPPER, true);
  return typeof s === 'string' ? one(s) : s.map(one);
}

/** SymPy bifid5: the 25 letters without J. */
export const bifid5: string = UPPER.replace('J', '');
/** SymPy bifid6: the letters and the digits. */
export const bifid6: string = UPPER + DIGITS;
/** SymPy bifid10: Python's string.printable. */
export const bifid10: string = PRINTABLE;

/**
 * SymPy padded_key: the distinct characters of key followed by the other
 * characters of symbols, in order.
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
 * SymPy check_and_join: the phrase (a string or list of strings) joined;
 * with symbols, characters not among them are an error, or are removed with
 * `filter`.
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

/** SymPy cycle_list: range(n) rotated left by k. */
export function cycleList(k: number, n: number): number[] {
  const s = ((k % n) + n) % n;
  return [...Array.from({ length: n - s }, (_x, i) => s + i), ...Array.from({ length: s }, (_x, i) => i)];
}

/** SymPy encipher_shift: the Caesar cipher, each letter shifted by key places. */
export function encipherShift(msg: string, key: number, symbols?: string): string {
  const [m, , A] = prep(msg, '', symbols);
  const shift = A.length - (((key % A.length) + A.length) % A.length);
  return translate(m, A.slice(shift) + A.slice(0, shift), A);
}

/** SymPy decipher_shift: the inverse of encipher_shift. */
export function decipherShift(msg: string, key: number, symbols?: string): string {
  return encipherShift(msg, -key, symbols);
}

/** SymPy encipher_rot13: the shift cipher with key 13. */
export function encipherRot13(msg: string, symbols?: string): string {
  return encipherShift(msg, 13, symbols);
}

/** SymPy decipher_rot13: the inverse of encipher_rot13 (the same cipher). */
export function decipherRot13(msg: string, symbols?: string): string {
  return decipherShift(msg, 13, symbols);
}

/** SymPy encipher_affine: the letter of index i becomes that of index a*i + b (mod N), for key [a, b]. */
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

/** SymPy decipher_affine: the inverse of encipher_affine. */
export function decipherAffine(msg: string, key: readonly [IntLike, IntLike], symbols?: string): string {
  return encipherAffine(msg, key, symbols, true);
}

/** SymPy encipher_atbash: the affine cipher with key (25, 25). */
export function encipherAtbash(msg: string, symbols?: string): string {
  return encipherAffine(msg, [25, 25], symbols);
}

/** SymPy decipher_atbash: the inverse of encipher_atbash. */
export function decipherAtbash(msg: string, symbols?: string): string {
  return decipherAffine(msg, [25, 25], symbols);
}

/**
 * SymPy encipher_substitution: the characters of old replaced by those of
 * new; old may also be a mapping of substrings to their replacements.
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

/** SymPy encipher_vigenere: the Vigenère cipher. */
export function encipherVigenere(msg: string, key: string, symbols?: string): string {
  return vigenere(msg, key, symbols, 1);
}

/** SymPy decipher_vigenere: the inverse of encipher_vigenere. */
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

/** SymPy encipher_hill: the Hill cipher with an invertible square key matrix (the message padded with pad). */
export function encipherHill(msg: string, key: Matrix, symbols?: string, pad = 'Q'): string {
  return hill(msg, key, symbols, pad, false);
}

/** SymPy decipher_hill: the inverse of encipher_hill. */
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

/** SymPy encipher_bifid: the bifid cipher on the square of the key padded with the alphabet (printable characters by default). */
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

/** SymPy decipher_bifid: the inverse of encipher_bifid. */
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

/** SymPy bifid_square: the square Matrix of the characters of key (as symbols). */
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

/** SymPy encipher_bifid5: the bifid cipher on the 5x5 square of the letters without J. */
export function encipherBifid5(msg: string, key: string): string {
  return bifidN(msg, key, bifid5, false);
}

/** SymPy decipher_bifid5: the inverse of encipher_bifid5. */
export function decipherBifid5(msg: string, key: string): string {
  return bifidN(msg, key, bifid5, true);
}

/** SymPy bifid5_square: the 5x5 square of the key padded with the letters without J. */
export function bifid5Square(key?: string): Matrix {
  return bifidNSquare(bifid5, key);
}

/** SymPy encipher_bifid6: the bifid cipher on the 6x6 square of the letters and digits. */
export function encipherBifid6(msg: string, key: string): string {
  return bifidN(msg, key, bifid6, false);
}

/** SymPy decipher_bifid6: the inverse of encipher_bifid6. */
export function decipherBifid6(msg: string, key: string): string {
  return bifidN(msg, key, bifid6, true);
}

/** SymPy bifid6_square: the 6x6 square of the key padded with the letters and digits. */
export function bifid6Square(key?: string): Matrix {
  return bifidNSquare(bifid6, key);
}

// ---------------------------------------------------------------------------
// RSA

/** Options of the RSA key functions (SymPy keyword arguments). */
export interface RsaKeyOptions {
  /** 'Euler' (the default) or 'Carmichael'. */
  totient?: 'Euler' | 'Carmichael';
  /** With the Carmichael totient: the key plus index times the totient. */
  index?: IntLike;
  /** Accept repeated prime factors (SymPy only suppresses a warning). */
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
 * SymPy rsa_public_key: the public key (n, e) from primes (or numbers that
 * are factored) and the exponent e, the last argument; false when e is not
 * invertible modulo the totient. A trailing options object gives the
 * totient ('Euler' or 'Carmichael') and the index.
 */
export function rsaPublicKey(...args: (IntLike | RsaKeyOptions)[]): [bigint, bigint] | false {
  return rsaKey(args, true);
}

/** SymPy rsa_private_key: the private key (n, d), d the inverse of e modulo the totient, or false. */
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

/** SymPy encipher_rsa: i**e mod n for the key (n, e); with the factors of n, by the Chinese remainder theorem. */
export function encipherRsa(i: IntLike, key: readonly [IntLike, IntLike], factors?: readonly IntLike[]): bigint {
  return rsaPow(i, key, factors);
}

/** SymPy decipher_rsa: c**d mod n for the key (n, d); with the factors of n, by the Chinese remainder theorem. */
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

/** SymPy kid_rsa_public_key: the Kid RSA public key (n, e). */
export function kidRsaPublicKey(a: IntLike, b: IntLike, A: IntLike, B: IntLike): [bigint, bigint] {
  const [n, e] = kidRsa(a, b, A, B);
  return [n, e];
}

/** SymPy kid_rsa_private_key: the Kid RSA private key (n, d). */
export function kidRsaPrivateKey(a: IntLike, b: IntLike, A: IntLike, B: IntLike): [bigint, bigint] {
  const [n, , d] = kidRsa(a, b, A, B);
  return [n, d];
}

/** SymPy encipher_kid_rsa: msg*e mod n. */
export function encipherKidRsa(msg: IntLike, key: readonly [IntLike, IntLike]): bigint {
  return bmod(asInt(msg) * asInt(key[1]), asInt(key[0]));
}

/** SymPy decipher_kid_rsa: msg*d mod n. */
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
/** SymPy morse_char: Morse code -> character. */
export const morseChar: ReadonlyMap<string, string> = new Map(Object.entries(MORSE));
/** SymPy char_morse: character -> Morse code. */
export const charMorse: ReadonlyMap<string, string> = new Map(Object.entries(MORSE).map(([k, v]) => [v, k] as const));

/**
 * SymPy encode_morse: the Morse code of msg, letters separated by sep and
 * words by sep twice; characters without a code are dropped.
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

/** SymPy decode_morse: the text of Morse code (letters separated by sep, words by sep twice). */
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
 * SymPy lfsr_sequence: the first n terms of the LFSR sequence over GF(p)
 * with the given key (coefficients) and fill (initial terms).
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

/** SymPy lfsr_autocorrelation: the autocorrelation of the binary sequence L of period P at shift k. */
export function lfsrAutocorrelation(L: readonly IntLike[], P: number, k: number): Expr {
  const L0 = L.slice(0, P).map((x) => asInt(x));
  const L1 = [...L0, ...L0.slice(0, k)];
  let tot = 0n;
  for (let i = 0; i < P; i++) tot += (at(L1, i) + at(L1, i + k)) % 2n === 0n ? 1n : -1n;
  return Rational.of(tot, BigInt(P));
}

/**
 * SymPy lfsr_connection_polynomial: the connection polynomial (in x) of the
 * LFSR sequence s over GF(p), by the Berlekamp-Massey algorithm.
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

/** SymPy elgamal_private_key: (p, r, d) with p the next prime after 2**digit, r a primitive root and d random. */
export function elgamalPrivateKey(digit = 10, seed?: CryptoSeed): [bigint, bigint, bigint] {
  const randrange = fromSeed(seed, false);
  const p = nextprime(2n ** BigInt(digit));
  return [p, primitiveRootOf(p), randrange(2n, p)];
}

function primitiveRootOf(p: bigint): bigint {
  // a prime has a primitive root
  return expectType(primitiveRoot(p), (x): x is bigint => typeof x === 'bigint', 'primitive root');
}

/** SymPy elgamal_public_key: (p, r, r**d mod p) from the private key (p, r, d). */
export function elgamalPublicKey(key: readonly [IntLike, IntLike, IntLike]): [bigint, bigint, bigint] {
  const [p, r, e] = [asInt(key[0]), asInt(key[1]), asInt(key[2])];
  return [p, r, powmod(r, e, p)];
}

/** SymPy encipher_elgamal: (r**a mod p, i*e**a mod p) for a random a. */
export function encipherElgamal(iIn: IntLike, key: readonly [IntLike, IntLike, IntLike], seed?: CryptoSeed): [bigint, bigint] {
  const i = asInt(iIn);
  const [p, r, e] = [asInt(key[0]), asInt(key[1]), asInt(key[2])];
  if (i < 0n || i >= p) throw new RangeError(`Message (${i}) should be in range(${p})`);
  const a = fromSeed(seed, false)(2n, p);
  return [powmod(r, a, p), bmod(i * powmod(e, a, p), p)];
}

/** SymPy decipher_elgamal: the message of (c1, c2) with the private key (p, r, d). */
export function decipherElgamal(msg: readonly [IntLike, IntLike], key: readonly [IntLike, IntLike, IntLike]): bigint {
  const [p, d] = [asInt(key[0]), asInt(key[2])];
  const [c1, c2] = [asInt(msg[0]), asInt(msg[1])];
  return bmod(invert(powmod(c1, d, p), p) * c2, p);
}

/** SymPy dh_private_key: (p, g, a) with p the next prime after 2**digit, g a primitive root and a random. */
export function dhPrivateKey(digit = 10, seed?: CryptoSeed): [bigint, bigint, bigint] {
  const p = nextprime(2n ** BigInt(digit));
  const g = primitiveRootOf(p);
  return [p, g, fromSeed(seed, false)(2n, p)];
}

/** SymPy dh_public_key: (p, g, g**a mod p). */
export function dhPublicKey(key: readonly [IntLike, IntLike, IntLike]): [bigint, bigint, bigint] {
  return elgamalPublicKey(key);
}

/** SymPy dh_shared_key: x**b mod p for the public key (p, g, x) and the secret b. */
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

/** SymPy gm_private_key: the two distinct odd primes. */
export function gmPrivateKey(pIn: IntLike, qIn: IntLike): [bigint, bigint] {
  const [p, q] = [asInt(pIn), asInt(qIn)];
  if (p === q) throw new RangeError(`expected distinct primes, got two copies of ${p}`);
  if (!isprime(p) || !isprime(q)) throw new RangeError(`first two arguments must be prime, got ${p} of ${q}`);
  if (p === 2n || q === 2n) throw new RangeError(`first two arguments must not be even, got ${p} of ${q}`);
  return [p, q];
}

/** SymPy gm_public_key: (a, N) with a a quadratic non-residue modulo both primes (random unless given), or false. */
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

/** SymPy encipher_gm: the bits of i encrypted with the public key (a, N). */
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

/** SymPy decipher_gm: the integer of the encrypted bits, with the private key (p, q). */
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

/** SymPy encipher_railfence: the rail fence cipher with the given number of rails. */
export function encipherRailfence(message: string, rails: number): string {
  const zig = railPattern(rails);
  return chars(message)
    .map((c, i) => [c, at(zig, i % zig.length)] as const)
    .sort((a, b) => a[1] - b[1])
    .map(([c]) => c)
    .join('');
}

/** SymPy decipher_railfence: the inverse of encipher_railfence. */
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

/** SymPy bg_private_key: the two distinct primes congruent to 3 mod 4. */
export function bgPrivateKey(pIn: IntLike, qIn: IntLike): [bigint, bigint] {
  const [p, q] = [asInt(pIn), asInt(qIn)];
  if (!isprime(p) || !isprime(q)) throw new RangeError(`the two arguments must be prime, got ${p} and ${q}`);
  if (p === q) throw new RangeError(`the two arguments must be distinct, got two copies of ${p}. `);
  if ((p - 3n) % 4n !== 0n || (q - 3n) % 4n !== 0n) throw new RangeError(`the two arguments must be congruent to 3 mod 4, got ${p} and ${q}`);
  return [p, q];
}

/** SymPy bg_public_key: N = p*q. */
export function bgPublicKey(p: IntLike, q: IntLike): bigint {
  const [a, b] = bgPrivateKey(p, q);
  return a * b;
}

/** SymPy encipher_bg: the Blum-Goldwasser encryption of i: the encrypted bits and x_L. */
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

/** SymPy decipher_bg: the integer of a Blum-Goldwasser message (bits, x_L), with the private key (p, q). */
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
