/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.RecorderView
public import HashSig.SLHDSA.SHAKE128s.Proof.CoverageRouted
public import HashSig.SLHDSA.SHAKE128s.Proof.RandomizerGate

/-!
# The two recording tests of the coverage event

The coverage charge is stated on a tape whose first block discloses and whose rest is targets.
The recorder files each fresh query on the *left* (disclosing) or the *right* (target) recording
by two tests read at the state in force when the query is answered. This file defines those
tests at the signer instantiation: `disclosingKeep` is the left test (the signer randomised this
input, as the cache says), `narrowClass` is the class the right recording keeps, and `targetKeep`
is the right test, built from an abstract disclosing test by `Served.targetKeep`.

**The tests are abstract over the state.** `Served.targetKeep` takes the class and the
disclosing test as parameters, each read at a `RecorderView.CacheView` state, so the same
construction serves a cache-readable test and the carrier's flag-readable one. The class may
read the view: it is consulted at one input and one view only, the view in force when that
input was answered fresh.
-/

@[expose] public section

open OracleComp OracleSpec

namespace SlhDsaSecurity.SplitWitness

open Security CacheAvailability SplitPrefix

/-! ## The right test over an abstract disclosing test

`served` is the left test, read at the state in force when a query is answered; `narrow` is the
class the right recording keeps, which is the charged class less whatever the instantiation
cannot file. The state is a parameter, at `RecorderView.CacheView`: a flag only the signing
oracle writes can serve as the disclosing test, and nothing here cares which kind it is. -/

namespace Served

open RecorderView

variable {σ : Type} [CacheView σ]

/-- The right test: an input of the narrowed class that is not disclosing. The class may read the
view; `AnswerCarrier.carrierRightKeep` is a class that does, excluding the signer's randomiser
probe by the frame in flight. -/
def targetKeep (narrow : Bytes → σ → Prop) (served : Bytes → σ → Prop) :
    Bytes → σ → Prop :=
  fun input view => narrow input view ∧ ¬ served input view

omit [CacheView σ] in
/-- The right test keeps the narrowed class. -/
theorem targetKeep_narrow (narrow : Bytes → σ → Prop) (served : Bytes → σ → Prop)
    (input : Bytes) (view : σ) (hkeep : targetKeep narrow served input view) :
    narrow input view := hkeep.1

end Served

/-! ## The signer instantiation

The disclosing test reading the cache alone: the signer randomised this input, in the sense that
the `PRF_msg` entry its randomiser truncates from is there. -/

/-- The left test: the signer randomised this input, as the cache in force says. -/
def disclosingKeep (prfSeed : Digest) (pk : PublicKey) :
    Bytes → QueryCache HashSpec → Prop :=
  fun input cache => SignerRandomised prfSeed pk cache input

/-- The class the target recording keeps: the message class, less the `PRF_msg` inputs at the
real seed.

The last clause keeps a served request out of the target recording. The signer's own `PRF_msg`
query on a request framed as `PK.root ‖ m` is a message input by the FIPS 205 format identity,
and it is not signer-randomised when it is made; without the clause the recorder would file it
as a target. It is a syntactic exclusion that works while the byte formats separate the two; the
frame-based exclusion is `AnswerCarrier.carrierRightKeep`'s. -/
def narrowClass (prfSeed : Digest) (pk : PublicKey) : Bytes → Prop :=
  fun input => CombinedCharge.IsMessageInput pk input ∧ ¬ RandomizerGate.PrfClass prfSeed input

/-- The right test at the signer instantiation. -/
def targetKeep (prfSeed : Digest) (pk : PublicKey) : Bytes → QueryCache HashSpec → Prop :=
  Served.targetKeep (fun probe _ => narrowClass prfSeed pk probe) (disclosingKeep prfSeed pk)

end SlhDsaSecurity.SplitWitness
