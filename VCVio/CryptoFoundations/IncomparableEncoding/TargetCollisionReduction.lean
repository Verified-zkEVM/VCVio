/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import VCVio.CryptoFoundations.IncomparableEncoding.TargetCollisionReduction.Basic
public import VCVio.CryptoFoundations.IncomparableEncoding.TargetCollisionReduction.Simulation
public import VCVio.CryptoFoundations.IncomparableEncoding.TargetCollisionReduction.Reduction

/-!
# Encoding target collisions reduce to SM-rTCR

A `Bridge` says that an incomparable encoding computes a tweakable hash of the message and the
randomizer at the epoch's tweak, accepts some hash outputs, and maps each accepted output
injectively to its codeword. For such an encoding, `advantage_le_hash` bounds the target-collision
advantage of any adversary by the SM-rTCR advantage of `reduction` applied to it, with the same
record cap and retry cap.

The reduction runs the source adversary, forwards each challenge query to the SM-rTCR challenge
oracle at the epoch's tweak, and maps each returned hash output to its codeword. At the end it
names the first recorded target that the source collision hits.

The Winternitz encoding (`accepts` always true) and the target-sum encoding (`accepts` tests the
digit sum) are the two bridges in the paper.

## References

- Drake, Khovratovich, Kudinov and Wagner, *Hash-Based Multi-Signatures for Post-Quantum Ethereum*,
  [ePrint 2025/055](https://eprint.iacr.org/2025/055), Lemmas 6 and 8.
-/
