/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.Target
public import HashSig.SLHDSA.SHAKE128s.Proof.SigningFaithful
public import HashSig.SLHDSA.SHAKE128s.Proof.AnswerSide
public import HashSig.SLHDSA.SHAKE128s.Proof.LateProvenance
public import HashSig.SLHDSA.SHAKE128s.Proof.RedrawCell
public import HashSig.SLHDSA.SHAKE128s.Proof.SignerRandomiser
public import HashSig.SLHDSA.SHAKE128s.Proof.SharedJoin
public import HashSig.SLHDSA.SHAKE128s.Proof.KeygenValue
public import HashSig.SLHDSA.SHAKE128s.Proof.ServedBridge
public import HashSig.SLHDSA.SHAKE128s.Proof.ServingCarrier
public import HashSig.SLHDSA.SHAKE128s.Proof.ChargedProbe

/-!
# The fused presentation's forgetting map

`forgetFused` is what a fused-tail result forgets to: the game's own outcome, count and cache.
The refining tail is the recorder's, and the one equation it owes the target is that its results
forget to the game's. That equation holds as an equality of computations: the recorder answers
every query exactly as the shared oracle does and writes its recordings beside the answer, so
dropping them returns the game.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.FinalAssembly

open Security CanonicalGraph WarmedGame RoutedSplit Target AnswerSide

/-- What a fused result forgets to: the game's own outcome, count and cache. -/
def forgetFused (result : ((Outcome × Multiset Bytes) × Nat) × SplitPrefix.SplitState) :
    (Outcome × Nat) × QueryCache HashSpec :=
  ((result.1.1.1, result.1.2), result.2.1)

end SlhDsaSecurity.FinalAssembly
