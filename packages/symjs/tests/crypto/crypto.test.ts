// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/crypto/crypto.ts.
// Classical and public-key ciphers. Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import * as C from '../../src/crypto';

const mat = (m: sj.Matrix): string => m.toString();

describe('alphabets and keys', () => {
  it('AZ, padded_key, check_and_join, cycle_list', () => {
    expect(C.AZ()).toBe('ABCDEFGHIJKLMNOPQRSTUVWXYZ');
    expect(C.AZ('Hello, world!')).toBe('HELLOWORLD');
    expect(C.AZ('Hello, world!'.split(' '))).toEqual(['HELLO', 'WORLD']);
    expect(C.AZ('')).toBe('ABCDEFGHIJKLMNOPQRSTUVWXYZ');
    expect(C.paddedKey('b', 'abc')).toBe('bac');
    expect(() => C.paddedKey('ab', 'aab')).toThrow('duplicate characters in symbols: a');
    expect(() => C.paddedKey('dx', 'abc')).toThrow('characters in key but not symbols: dx');
    expect(C.checkAndJoin('a phrase')).toBe('a phrase');
    expect(C.checkAndJoin('a phrase'.toUpperCase().split(' '))).toBe('APHRASE');
    expect(C.checkAndJoin('a phrase!'.toUpperCase().split(' '), 'ARE', true)).toBe('ARAE');
    expect(() => C.checkAndJoin('a phrase!'.toUpperCase().split(' '), 'ARE')).toThrow('characters in phrase but not symbols: "!HPS"');
    expect(C.cycleList(3, 10)).toEqual([3, 4, 5, 6, 7, 8, 9, 0, 1, 2]);
    expect(C.cycleList(-1, 4)).toEqual([3, 0, 1, 2]);
    expect(C.bifid5.length).toBe(25);
    expect(C.bifid6.length).toBe(36);
    expect(C.bifid10.length).toBe(100);
  });
});

describe('classical ciphers', () => {
  it('shift, rot13, affine, atbash, substitution', () => {
    expect(C.encipherShift('GONAVYBEATARMY', 1)).toBe('HPOBWZCFBUBSNZ');
    expect(C.decipherShift('HPOBWZCFBUBSNZ', 1)).toBe('GONAVYBEATARMY');
    expect(C.encipherShift('abc', 1, 'abcd')).toBe('bcd');
    expect(C.encipherRot13('GONAVYBEATARMY')).toBe('TBANILORNGNEZL');
    expect(C.decipherRot13('TBANILORNGNEZL')).toBe('GONAVYBEATARMY');
    expect(C.encipherAffine('GONAVYBEATARMY', [1, 1])).toBe('HPOBWZCFBUBSNZ');
    expect(C.decipherAffine('HPOBWZCFBUBSNZ', [1, 1])).toBe('GONAVYBEATARMY');
    expect(C.encipherAffine('GONAVYBEATARMY', [3, 7])).toBe('ZXUHSBKTHMHGRB');
    expect(() => C.encipherAffine('ABC', [2, 1])).toThrow(RangeError);
    expect(C.encipherAtbash('ABC')).toBe('ZYX');
    expect(C.decipherAtbash('ZYX')).toBe('ABC');
    expect(C.encipherSubstitution('ABC', 'BC', 'CB')).toBe('ACB');
    expect(C.encipherSubstitution('ABAB', { A: 'C', AB: 'XY' })).toBe('XYXY');
    expect(C.encipherSubstitution('ABAB', new Map([['B', 'Z']]))).toBe('AZAZ');
    expect(() => C.encipherSubstitution('ABC', 'AB', 'C')).toThrow('oldchars and newchars have different lengths');
    expect(() => C.encipherSubstitution('ABC', 'AB')).toThrow(RangeError);
  });
  it('Vigenère and Hill', () => {
    expect(C.encipherVigenere('Meet me on Monday', 'LEMON')).toBe('XIQHZPSZABYHMM');
    expect(C.decipherVigenere('XIQHQIZRAZRMEA', 'LEMON')).toBe('MEETDXVFMMGISM');
    const key = sj.Matrix.of([[1, 2], [3, 5]]);
    expect(C.encipherHill('meet me on monday', key)).toBe('UEQDUEODOCTCWQ');
    expect(C.decipherHill('UEQDUEODOCTCWQ', key)).toBe('MEETMEONMONDAY');
    expect(C.encipherHill('ABC', key)).toBe('CFII');
    expect(C.decipherHill('ABC', key)).toBe('CZQG');
    expect(() => C.encipherHill('ABC', sj.Matrix.of([[1, 2]]))).toThrow(RangeError);
    expect(() => C.encipherHill('ABC', key, undefined, 'QQ')).toThrow(RangeError);
    expect(() => C.encipherHill('BC', sj.Matrix.of([[sj.Rational.of(1n, 2n), 0], [0, 1]]))).toThrow(TypeError);
  });
  it('bifid ciphers and squares', () => {
    expect(C.encipherBifid('hello world!', 'gold bug')).toBe('hggsfuei7t|w');
    expect(C.decipherBifid('hggsfuei7t|w', 'gold bug')).toBe('hello world!');
    expect(C.encipherBifid5('meet me on monday', 'gold bug')).toBe('IEILHHFSTSFQYE');
    expect(C.decipherBifid5('IEILEHFSTSFXEE', 'gold bug')).toBe('MEETMEONFRIDAY');
    expect(C.encipherBifid6('meet me on monday at 8am', 'gold bug')).toBe('KFKLJJHF5MMMKTFRGPL');
    expect(C.decipherBifid6('KFKLJJHF5MMMKTFRGPL', 'gold bug')).toBe('MEETMEONMONDAYAT8AM');
    expect(mat(C.bifid5Square('gold bug'))).toBe('Matrix([[G, O, L, D, B], [U, A, C, E, F], [H, I, K, M, N], [P, Q, R, S, T], [V, W, X, Y, Z]])');
    expect(mat(C.bifid5Square())).toBe('Matrix([[A, B, C, D, E], [F, G, H, I, K], [L, M, N, O, P], [Q, R, S, T, U], [V, W, X, Y, Z]])');
    expect(mat(C.bifid6Square('gold bug'))).toBe('Matrix([[G, O, L, D, B, U], [A, C, E, F, H, I], [J, K, M, N, P, Q], [R, S, T, V, W, X], [Y, Z, 0, 1, 2, 3], [4, 5, 6, 7, 8, 9]])');
    expect(mat(C.bifid6Square())).toBe(mat(C.bifidSquare(C.bifid6)));
    expect(mat(C.bifidSquare(['AB', 'CD']))).toBe('Matrix([[A, B], [C, D]])');
    expect(() => C.bifidSquare('ABC')).toThrow('Length of alphabet (3) is not a square number.');
    expect(() => C.encipherBifid('ABC', '', 'ABC')).toThrow('Length of alphabet (3) is not a square number.');
  });
  it('rail fence', () => {
    expect(C.encipherRailfence('hello world', 3)).toBe('horel ollwd');
    expect(C.decipherRailfence('horel ollwd', 3)).toBe('hello world');
    expect(C.encipherRailfence('abc', 1)).toBe('abc');
  });
  it('Morse code', () => {
    expect(C.encodeMorse('ATTACK RIGHT FLANK')).toBe('.-|-|-|.-|-.-.|-.-||.-.|..|--.|....|-||..-.|.-..|.-|-.|-.-');
    expect(C.encodeMorse('ab c ', '*')).toBe('**');
    expect(C.encodeMorse('a#b')).toBe('');
    expect(() => C.encodeMorse('A', 'A')).toThrow(RangeError);
    expect(C.decodeMorse('-.-|.|-.--||.--|---|..-|.-.|-')).toBe('KEY WOURT');
    expect(C.decodeMorse('|-.-||.-|')).toBe('K A');
    expect(C.morseChar.get('.-')).toBe('A');
    expect(C.charMorse.get('A')).toBe('.-');
  });
});

describe('linear feedback shift registers', () => {
  it('sequences, autocorrelation and connection polynomials', () => {
    const s = C.lfsrSequence([1, 0, 0, 1], [1, 0, 0, 1], 20);
    expect(s.slice(0, 10)).toEqual([1n, 0n, 0n, 1n, 0n, 0n, 0n, 1n, 1n, 1n]);
    expect(C.lfsrSequence([1, 2], [1, 2], 8, { modulus: 3 })).toEqual([1n, 2n, 2n, 0n, 2n, 1n, 1n, 0n]);
    expect(sj.str(C.lfsrAutocorrelation(s, 15, 7))).toBe('-1/15');
    expect(sj.str(C.lfsrAutocorrelation(s, 15, 0))).toBe('1');
    expect(sj.str(C.lfsrConnectionPolynomial(s))).toBe('x**4 + x + 1');
    expect(sj.str(C.lfsrConnectionPolynomial(C.lfsrSequence([1, 1, 0], [1, 0, 0], 20)))).toBe('x**3 + x**2 + 1');
    expect(sj.str(C.lfsrConnectionPolynomial(C.lfsrSequence([0, 1, 1], [1, 0, 0], 20)))).toBe('1');
    expect(sj.str(C.lfsrConnectionPolynomial([1, 2, 2, 0, 2, 1, 1, 0, 1, 2, 2, 0], { modulus: 3 }))).toBe('2*x**2 + x + 1');
    expect(sj.str(C.lfsrConnectionPolynomial([1, 1, 0, 0]))).toBe('1');
  });
});

describe('RSA and Kid RSA', () => {
  it('keys', () => {
    expect(C.rsaPublicKey(3, 5, 7)).toEqual([15n, 7n]);
    expect(C.rsaPrivateKey(3, 5, 7)).toEqual([15n, 7n]);
    expect(C.rsaPublicKey(3, 5, 30)).toBe(false);
    expect(C.rsaPublicKey(3)).toBe(false);
    expect(C.rsaPublicKey(61, 53, 17, { totient: 'Carmichael', index: 2 })).toEqual([3233n, 1577n]);
    expect(C.rsaPrivateKey(61, 53, 17, { totient: 'Carmichael', index: 1 })).toEqual([3233n, 1193n]);
    expect(C.rsaPrivateKey(61, 53, 17, { totient: 'Carmichael' })).toEqual([3233n, 413n]);
    expect(C.rsaPublicKey(15, 7)).toEqual([15n, 7n]);
    expect(C.rsaPrivateKey(3, 3, 5, { multipower: true })).toEqual([9n, 5n]);
    expect(C.rsaPrivateKey(2, 2, 2, 3, 5, { totient: 'Carmichael' })).toEqual([24n, 1n]);
    expect(() => C.rsaPublicKey(3, 5, 7, { totient: 'X' as 'Euler' })).toThrow("The argument totient=X should either be 'Euler', 'Carmichalel'.");
    expect(() => C.rsaPublicKey(3, 5, 7, { index: 1 })).toThrow("Setting the 'index' keyword argument requires totientnotation to be specified as 'Carmichael'.");
  });
  it('encryption', () => {
    expect(C.encipherRsa(12, [15, 7])).toBe(3n);
    expect(C.decipherRsa(3, [15, 7])).toBe(12n);
    expect(C.decipherRsa(3, [15, 7], [3, 5])).toBe(12n);
    expect(C.decipherRsa(3, [15, 7], [3, 3])).toBe(12n);
    expect(C.kidRsaPublicKey(3, 4, 5, 6)).toEqual([369n, 58n]);
    expect(C.kidRsaPrivateKey(3, 4, 5, 6)).toEqual([369n, 70n]);
    expect(C.encipherKidRsa(200, [369, 58])).toBe(161n);
    expect(C.decipherKidRsa(161, [369, 70])).toBe(200n);
  });
});

describe('ElGamal, Diffie-Hellman, Goldwasser-Micali, Blum-Goldwasser', () => {
  it('ElGamal and Diffie-Hellman', () => {
    expect(C.elgamalPrivateKey(5, [3])).toEqual([37n, 2n, 3n]);
    expect(C.elgamalPrivateKey(5, 1)).toEqual([37n, 2n, 10n]);
    expect(C.elgamalPrivateKey(5)).toHaveLength(3);
    expect(C.elgamalPrivateKey(5, [100, 3])).toEqual([37n, 2n, 3n]);
    expect(() => C.elgamalPrivateKey(5, [])).toThrow('_randrange sequence was too short');
    expect(() => C.elgamalPrivateKey(0, [1])).toThrow('_randrange got empty range');
    expect(C.elgamalPublicKey([1031, 14, 636])).toEqual([1031n, 14n, 212n]);
    expect(C.encipherElgamal(100, [1031, 14, 212], [3])).toEqual([682n, 747n]);
    expect(C.decipherElgamal([835, 271], [1031, 14, 636])).toBe(100n);
    expect(() => C.encipherElgamal(2000, [1031, 14, 212])).toThrow('Message (2000) should be in range(1031)');
    expect(C.dhPrivateKey(5, [3])).toEqual([37n, 2n, 3n]);
    expect(C.dhPublicKey([37, 2, 3])).toEqual([37n, 2n, 8n]);
    expect(C.dhSharedKey([37, 2, 8], 5)).toBe(23n);
    expect(() => C.dhSharedKey([37, 2, 8], 1)).toThrow('Value of b should be greater 1 and less than prime 37.');
  });
  it('Goldwasser-Micali', () => {
    expect(C.gmPrivateKey(7, 11)).toEqual([7n, 11n]);
    expect(C.gmPublicKey(7, 11, undefined, 1)).toEqual([17n, 77n]);
    expect(C.gmPublicKey(7, 11, 3)).toBe(false);
    expect(C.gmPublicKey(7, 11, 17)).toEqual([17n, 77n]);
    expect(C.gmPublicKey(7, 11, 7)).toBe(false);
    expect(() => C.gmPrivateKey(7, 7)).toThrow('expected distinct primes, got two copies of 7');
    expect(() => C.gmPrivateKey(8, 7)).toThrow('first two arguments must be prime, got 8 of 7');
    expect(() => C.gmPrivateKey(2, 7)).toThrow('first two arguments must not be even, got 2 of 7');
    expect(C.encipherGm(12, [2, 77], [3, 5, 8, 13, 17, 19, 23])).toEqual([18n, 50n, 64n, 15n]);
    expect(C.encipherGm(12, [17, 77], 3)).toEqual([54n, 68n, 64n, 25n]);
    expect(C.decipherGm([54, 68, 64, 25], [7, 11])).toBe(12n);
    expect(C.decipherGm([58, 75, 65, 4], [7, 11])).toBe(6n);
    expect(() => C.encipherGm(-1, [2, 77])).toThrow('message must be a non-negative integer: got -1 instead');
    expect(() => C.encipherGm(12, [2, 77], [3, 4])).toThrow(RangeError);
  });
  it('Blum-Goldwasser', () => {
    expect(C.bgPrivateKey(23, 31)).toEqual([23n, 31n]);
    expect(C.bgPublicKey(23, 31)).toBe(713n);
    expect(C.encipherBg(12, 713, [6])).toEqual([[1n, 0n, 1n, 1n], 625n]);
    expect(C.encipherBg(12, 713, [1, 1000, 6])).toEqual([[1n, 0n, 1n, 1n], 625n]);
    expect(C.decipherBg(C.encipherBg(12, 713, 5), [23, 31])).toBe(12n);
    expect(C.decipherBg([[1, 0, 1, 0], 100], [23, 31])).toBe(7n);
    expect(C.decipherBg([[1, 0, 1, 1], 625], [23, 31])).toBe(12n);
    expect(() => C.bgPrivateKey(8, 7)).toThrow('the two arguments must be prime, got 8 and 7');
    expect(() => C.bgPrivateKey(7, 7)).toThrow('the two arguments must be distinct, got two copies of 7. ');
    expect(() => C.bgPrivateKey(5, 7)).toThrow('the two arguments must be congruent to 3 mod 4, got 5 and 7');
    expect(() => C.encipherBg(-1, 713)).toThrow('message must be a non-negative integer: got -1 instead');
    expect(() => C.encipherBg(12, 713, [1000])).toThrow(RangeError);
  });
});
