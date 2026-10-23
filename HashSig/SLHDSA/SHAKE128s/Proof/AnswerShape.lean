/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.FinalAssembly
public import HashSig.SLHDSA.SHAKE128s.Proof.Target
public import HashSig.SLHDSA.SHAKE128s.Proof.SigningFaithful
public import HashSig.SLHDSA.SHAKE128s.Proof.AnswerSide

/-!
# The answer side's forgetting map

`forgetRecord` drops the record from a recorder run's result and keeps the whole recorder state.
Events that read only the outcome, the count and the recorder state (the cache and the
recordings) are the *same proposition* at either value type, so a bound proved at the run without
the record transports along this map by `prEvent_map` with nothing lost or assumed. -/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.AnswerShape

open Security CanonicalGraph WarmedGame RoutedSplit Target

/-- The map the answer side's bound is transported along: drop the record, keep the state. -/
def forgetRecord (result : ((Outcome × Multiset Bytes) × Nat) × SplitPrefix.SplitState) :
    (Outcome × Nat) × SplitPrefix.SplitState :=
  ((result.1.1.1, result.1.2), result.2)

end SlhDsaSecurity.AnswerShape
