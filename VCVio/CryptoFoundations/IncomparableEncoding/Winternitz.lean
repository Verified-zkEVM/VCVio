/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import VCVio.CryptoFoundations.IncomparableEncoding.Winternitz.Code
public import VCVio.CryptoFoundations.IncomparableEncoding.Winternitz.Encoding
public import VCVio.CryptoFoundations.IncomparableEncoding.Winternitz.Collision

/-!
# Winternitz encoding

The Winternitz encoding is Construction 5 of DKKW25.

- `Winternitz.Code`: checksum words and the proof that they form one incomparable code.
- `Winternitz.Encoding`: the encoding and its zero error (Lemma 5).
- `Winternitz.Collision`: the bridge to the message hash and the target-collision bound
  (Lemma 6).

## References

- Drake, Khovratovich, Kudinov and Wagner, *Hash-Based Multi-Signatures for Post-Quantum Ethereum*,
  [ePrint 2025/055](https://eprint.iacr.org/2025/055), Construction 5, Lemmas 5 and 6.
-/
