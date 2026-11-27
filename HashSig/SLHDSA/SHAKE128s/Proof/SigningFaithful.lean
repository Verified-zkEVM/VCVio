/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Statement.Scheme
public import HashSig.SLHDSA.SHAKE128s.Proof.CacheReplay

/-!
# Signing under successful pure-message framing

An accepted request returns the encoding of its internal signature. The same equation
applies when oracle queries are replayed from a cache.
-/

public section

open OracleComp OracleSpec

namespace SLHDSA.SHAKE128s.SigningFaithful

open CacheReplay

/-- A signer that accepts its framing returns that framing's signature. -/
theorem sign_eq_map {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (sk : SecretKey) (request : Message) (framed : Bytes)
    (hframe : request.frame = some framed) :
    (Scheme.sign sk request : m (Option Bytes)) =
      (fun signature : Signature => some signature.toBytes) <$>
        (Scheme.signInternal sk framed : m Signature) := by
  simp only [Scheme.sign, SignatureAlg.SigningView.Encoding.sign, hframe]
  rfl

/-- The replayed signer, at a framing it accepts, returns the replayed signature's bytes. -/
theorem sign_replay_eq (cache : QueryCache HashSpec) (sk : SecretKey) (request : Message)
    (framed : Bytes) (hframe : request.frame = some framed) :
    @Scheme.sign Id Id.instMonad (replayQuery cache) sk request =
      some (@Scheme.signInternal Id Id.instMonad (replayQuery cache) sk framed).toBytes := by
  rw [@sign_eq_map Id Id.instMonad (replayQuery cache) sk request framed hframe]
  rfl

end SLHDSA.SHAKE128s.SigningFaithful
