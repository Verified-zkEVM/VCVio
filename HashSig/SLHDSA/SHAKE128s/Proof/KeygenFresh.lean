/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.Experiment
public import HashSig.SLHDSA.SHAKE128s.Proof.HashSeparation
public import VCVio.OracleComp.QueryTracking.QueryBound

/-! The final top-tree address is absent throughout the preceding key-generation work. -/

@[expose] public section

open OracleComp OracleSpec

set_option backward.isDefEq.respectTransparency false

namespace SlhDsaSecurity.KeygenUniform

def rootAddress : Address :=
  Merkle.nodeAddress (Hypertree.address (layers - 1) 0) subtreeHeight 0

def RootQuery (seed : Digest) (payload : Bytes) : OracleWorld.Domain → Prop :=
  fun input => input = .inr (Hashing.tweakableInput seed rootAddress payload)

instance (seed : Digest) (payload : Bytes) : DecidablePred (RootQuery seed payload) :=
  fun _ => inferInstanceAs (Decidable (_ = _))

noncomputable abbrev rom : QueryImpl OracleWorld (StateT (QueryCache HashSpec) ProbComp) :=
  Xmss.RandomOracleModel.impl Bytes HashOutput

end SlhDsaSecurity.KeygenUniform
