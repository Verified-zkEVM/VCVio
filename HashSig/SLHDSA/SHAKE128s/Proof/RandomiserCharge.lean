/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.Target
public import HashSig.SLHDSA.SHAKE128s.Proof.RandomizerGate
public import HashSig.SLHDSA.SHAKE128s.Proof.WarmedCharges
public import HashSig.SLHDSA.SHAKE128s.Proof.StrippedGame
public import HashSig.SLHDSA.SHAKE128s.Proof.HonestProbes

/-!
# The warm cache holds no randomiser input at the walk's own seed

The walk programs the canonical graph and nothing else, a canonical input opens with `PK.seed` and
a `PRF_msg` input with `SK.prf`, and the two seeds differ on a good walk (`Target.GoodWalk`).
So the walk's cache holds no `PRF_msg` entry at the walk's own seed (`walk_cache_prf_fresh`).
-/

@[expose] public section

open OracleComp OracleSpec

namespace SlhDsaSecurity.RandomiserCharge

open Security CanonicalGraph WarmedGame

/-- **The warm cache holds no `PRF_msg` entry at the walk's own seed.** -/
theorem walk_cache_prf_fresh
    {walk : ((Digest × Digest × Digest) × Cells) × QueryCache HashSpec}
    (hwalk : walk ∈ support graphWalk) (hgood : Target.GoodWalk walk)
    (seed : Digest) (message : Bytes) :
    walk.2 (Hashing.randomizerInput walk.1.1.2.1 seed message) = none := by
  by_contra hpresent
  obtain ⟨parent, hcanonical⟩ := WarmedCharges.walk_cache_canonical hwalk _ hpresent
  exact RandomizerGate.canonicalInput_ne_randomizerInput walk.1.1.2.2 walk.1.1.2.1 seed
    walk.1.2 parent message hgood.1 hcanonical.symm

end SlhDsaSecurity.RandomiserCharge
