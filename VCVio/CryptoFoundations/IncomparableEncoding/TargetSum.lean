/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import VCVio.CryptoFoundations.IncomparableEncoding.TargetSum.Basic
public import VCVio.CryptoFoundations.IncomparableEncoding.TargetSum.Counting
public import VCVio.CryptoFoundations.IncomparableEncoding.TargetSum.Error
public import VCVio.CryptoFoundations.IncomparableEncoding.TargetSum.Collision

/-!
# Target-sum encoding

The target-sum encoding is Construction 6 of DKKW25.

- `TargetSum.Basic`: the digit-sum code and the encoding.
- `TargetSum.Counting`: the number of accepted words, the coefficient `η_T`, and the rejection
  probability of a uniform word.
- `TargetSum.Error`: the error bound for an `ε`-uniform message hash (Lemma 7).
- `TargetSum.Collision`: the bridge to the message hash and the target-collision bound (Lemma 8).

## References

- Drake, Khovratovich, Kudinov and Wagner, *Hash-Based Multi-Signatures for Post-Quantum Ethereum*,
  [ePrint 2025/055](https://eprint.iacr.org/2025/055), Construction 6, Lemmas 7 and 8.
-/
