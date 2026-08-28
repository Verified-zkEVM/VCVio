/-
Copyright (c) 2026 Nicolas Consigny, Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Consigny, Matthias Meijers
-/

module
public import VCVio.CryptoFoundations.HardnessAssumptions.MultiTarget.Collection
public import VCVio.CryptoFoundations.HardnessAssumptions.MultiTarget.Pre
public import VCVio.CryptoFoundations.HardnessAssumptions.MultiTarget.Tcr

/-!
# Multi-target hash assumptions

The single-function multi-target notions that hash-based signatures such as SLH-DSA / SPHINCS+
reduce to: preimage resistance (`MultiTarget.preAdvantage`, in `MultiTarget.Pre`) and
target-collision resistance (`MultiTarget.tcrAdvantage`, in `MultiTarget.Tcr`), each stated in the
collection form built in `MultiTarget.Collection`.

Unlike plain one-wayness (`HardnessAssumptions.OneWay`) or collision resistance
(`HardnessAssumptions.CollisionResistance`), these are *single-function multi-target* notions: the
adversary picks up to `p` targets and wins by breaking any one of them, against a public seed that
is sampled by the game and withheld from it while it picks. The `p`-fold loss relative to the
single-target notions is left to separate bridge lemmas rather than baked into the advantage.

Each game is packaged in the `Problem` / `Adversary` / `experiment` / `advantage` shape shared with
`LatticeCrypto.HardnessAssumptions.ShortIntegerSolution`.
-/
