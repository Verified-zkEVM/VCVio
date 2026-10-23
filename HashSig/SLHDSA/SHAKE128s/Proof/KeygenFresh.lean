/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.Experiment
public import HashSig.SLHDSA.SHAKE128s.Proof.HashSeparation
public import VCVio.OracleComp.QueryTracking.QueryBound

/-!
# The top-tree root query of key generation

Definitions for the freshness of the final key-generation query: `rootAddress` is the address of
the root of the top XMSS tree, `RootQuery` recognises the oracle query that computes it, and
`rom` is the random-oracle implementation of the oracle world, under which this address is
absent throughout the preceding key-generation work.
-/

@[expose] public section

open OracleComp OracleSpec

namespace SlhDsaSecurity.KeygenUniform

/-- The address of the root of the top XMSS tree. -/
def rootAddress : Address :=
  Merkle.nodeAddress (Hypertree.address (layers - 1) 0) subtreeHeight 0

/-- The oracle query computing the top-tree root under `seed` with input `payload`. -/
def RootQuery (seed : Digest) (payload : Bytes) : OracleWorld.Domain → Prop :=
  fun input => input = .inr (Hashing.tweakableInput seed rootAddress payload)

/-- Recognising the root query is decidable. -/
instance (seed : Digest) (payload : Bytes) : DecidablePred (RootQuery seed payload) :=
  fun _ => inferInstanceAs (Decidable (_ = _))

/-- The random-oracle implementation of the oracle world: uniform sampling is forwarded, and
the shared hash answers fresh inputs uniformly and repeated inputs from its cache. -/
noncomputable abbrev rom : QueryImpl OracleWorld (StateT (QueryCache HashSpec) ProbComp) :=
  RandomOracleModel.impl Bytes HashOutput

end SlhDsaSecurity.KeygenUniform
