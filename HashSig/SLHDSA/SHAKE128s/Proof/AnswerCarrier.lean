/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.CarrierTail
public import HashSig.SLHDSA.SHAKE128s.Proof.CarrierCoverage

/-!
# The answer side's run at the carrier tail

`answerCarrierRun` names the run `AnswerShape.forgetRecord <$> CarrierTail.carrierTail rightKeep
adversary walk`, once, so that every statement about the answer side's run at the carrier tail
speaks of the same object. `carrierRightKeep` is the test the target recording is filed under
there: the message class, less the signer's own randomiser probe for the frame in flight
(`FilesRandomiser`), less whatever the carrier's flag already files on the left.
-/

public section

open OracleComp OracleSpec

namespace SlhDsaSecurity.AnswerCarrier

open Security CanonicalGraph WarmedGame Target

/-- The run the answer side owes a bound at, when the tail is the carrier's. -/
@[expose] noncomputable def answerCarrierRun
    (rightKeep : (((Digest × Digest × Digest) × Cells) × QueryCache HashSpec) → Bytes →
      HandlerCarrier.State → Prop)
    (adversary : Adversary)
    (walk : (((Digest × Digest × Digest) × Cells) × QueryCache HashSpec)) :
    ProbComp ((Outcome × Nat) × SplitPrefix.SplitState) :=
  AnswerShape.forgetRecord <$> CarrierTail.carrierTail rightKeep adversary walk

/-! ## The target test at the carrier

At the carrier the test the target recording is filed under reads
`message class ∧ ¬ FilesRandomiser ∧ ¬ CarriedWitness.disclosingKeep`. `FilesRandomiser` is the
honest way to keep the signer's own `PRF_msg` probe out of the target recording: it is the probe
for the frame **in flight**, so it is false at every adversary query (the flag is down at every
boundary) and true exactly while the signer serves that frame. -/

/-- **The signer's own randomiser probe, as the flag sees it.** The `PRF_msg` input for the frame
in flight — the exact counterpart of `HandlerCarrier.FilesLeft`, which is the digest input for
that same frame. -/
@[expose] def FilesRandomiser (prfSeed : Digest) (pk : PublicKey) (state : HandlerCarrier.State)
    (input : Bytes) : Prop :=
  ∃ framed : Bytes, state.framing = some framed ∧
    input = Hashing.randomizerInput prfSeed pk.seed framed

/-- **The target test at the carrier.** The message class, less the probe for the frame in
flight, less whatever the flag is already filing on the left. -/
@[expose] def carrierRightKeep
    (walk : (((Digest × Digest × Digest) × Cells) × QueryCache HashSpec))
    (input : Bytes) (state : HandlerCarrier.State) : Prop :=
  (CombinedCharge.IsMessageInput
      (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2) input ∧
    ¬ FilesRandomiser walk.1.1.2.1
      (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2) state input) ∧
  ¬ CarriedWitness.disclosingKeep
      (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2) input state

/-- **It keeps the message class**, which is all the counting side reads of the target test: the
test lies inside the counted class. -/
theorem carrierRightKeep_class
    (walk : (((Digest × Digest × Digest) × Cells) × QueryCache HashSpec))
    (input : Bytes) (state : HandlerCarrier.State)
    (hkeep : carrierRightKeep walk input state) :
    CombinedCharge.IsMessageInput
      (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2) input :=
  hkeep.1.1

-- Everything after this point treats `answerCarrierRun` as opaque; unfolding it would make the
-- unifier walk into `carrierTail` at every membership.
attribute [local irreducible] answerCarrierRun

end SlhDsaSecurity.AnswerCarrier
