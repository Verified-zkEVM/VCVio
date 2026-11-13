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
# Encoding target-collision reduction

Adaptive encoding target collisions reduce to the shared tweakable-hash target game through
an explicit encoding bridge, retaining the public-seed sampler and both target and retry caps.
-/
