/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.CarrierTail
public import HashSig.SLHDSA.SHAKE128s.Proof.CountedView
public import HashSig.SLHDSA.SHAKE128s.Proof.NoticingTape
public import HashSig.SLHDSA.SHAKE128s.Proof.FusedTape
public import HashSig.SLHDSA.SHAKE128s.Proof.BlockViews

/-!
# The carrier tail is a three-stage recorder run, and so it pays the coverage charge

The last join. `CarrierTail.carrierTail` and `FusedTape.threeStageHandlerRun` are the same three
stages; `CountedView.reassociate` is the bijection between their states, and
`CountedView.forgetsAlong_counted` is the transport. Everything else lined up already: the
initial state re-associates to `(cache, [], [])` exactly, `FusedTape.forgetView` of the
re-association **is** `BracketedRun.forgetCarrier`, and the brackets are `{τ}`-generic so at
`τ := Nat` they already are the maps the tape layer wants.

The chain is three applications of the bind-form transports, which is why those were stated as
binds: `bind_congr` walks them and the continuation is handed over rather than guessed.
-/

public section

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.CarrierCoverage

open Security CarrierTail CountedView RecorderView CarriedWitness PhaseFusion RecordedQueries

/-- The brackets re-associate: raising the framing commutes with the re-encoding. -/
theorem reassociate_startServingOn (request : Message)
    (state : HandlerCarrier.State × ((DigestTape.Record × DigestTape.Record) × Nat)) :
    reassociate (ServedAgreement.startServingOn request state) =
      FusedTape.onCarrier (ServedAgreement.startServingOn request) (reassociate state) := by
  cases hframe : request.frame with
  | none => simp [ServedAgreement.startServingOn, reassociate, FusedTape.onCarrier, hframe]
  | some framed =>
    simp [ServedAgreement.startServingOn, reassociate, FusedTape.onCarrier, hframe]

/-- And lowering it. -/
theorem reassociate_stopServingOn
    (state : HandlerCarrier.State × ((DigestTape.Record × DigestTape.Record) × Nat)) :
    reassociate (ServedAgreement.stopServingOn state) =
      FusedTape.onCarrier ServedAgreement.stopServingOn (reassociate state) := rfl

/-- The value the tail reads, with the final count taken off the carrier. -/
@[expose] def tailValue (_keys : (SecretKey × PublicKey)) (forgery : Forgery)
    (accumulated : Multiplicative Tally) (log : SigningLog)
    (final : Bool × Tally) (carrier : Counted) :
    (Outcome × Multiset Bytes) × Nat :=
  ((({ forgery := forgery
       signed := log
       verified := final.1
       counts := (Multiplicative.toAdd accumulated).1 + final.2.1 } : Outcome),
    (Multiplicative.toAdd accumulated).2 + final.2.2), carrier.2)

/-- **The carrier tail is a three-stage recorder run at the re-encoded state.** Three
applications of the bind-form transports, one per stage, and then the two pure results agree
because `FusedTape.forgetView` of the re-association is `BracketedRun.forgetCarrier`. -/
theorem carrierTail_eq_threeStage
    (rightKeep : BracketedRun.Walk → Bytes → HandlerCarrier.State → Prop)
    (adversary : Adversary) (walk : BracketedRun.Walk) :
    carrierTail rightKeep adversary walk =
      @FusedTape.threeStageHandlerRun Counted (countedView (keyAt walk)) _ _
        (liftTest (disclosingKeep (keyAt walk)))
        (liftTest (rightKeep walk)) _ _ _ _
        (fun keys => recordedAdversaryImpl + recordedSigningOracle (Scheme.sign keys.1))
        ServedAgreement.startServingOn ServedAgreement.stopServingOn
        (Scheme.keygenInternal walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2)
        (fun keys => adversary.main keys.2)
        (fun keys forgery => countRecorded verifierCost
          (Scheme.verify keys.2 forgery.message forgery.signature))
        tailValue (startAt walk.2, 0) [] [] := by
  simp only [carrierTail, FusedTape.threeStageHandlerRun]
  rw [show (((startAt walk.2, 0) : Counted), ([] : DigestTape.Record),
        ([] : DigestTape.Record)) = reassociate (startAt walk.2, (([], []), 0)) from rfl,
    ← ServingForget.bind_of_forgetsAlong reassociate _ _
      (forgetsAlong_counted (keyAt walk) (rightKeep walk))
      (Scheme.keygenInternal walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2)
      (startAt walk.2, (([], []), 0)) _]
  refine bind_congr fun keys => ?_
  rw [← ServingForget.bind_of_fuseServing_conj reassociate _ _ _
      ServedAgreement.startServingOn ServedAgreement.stopServingOn
      (fun request => FusedTape.onCarrier (ServedAgreement.startServingOn request))
      (FusedTape.onCarrier ServedAgreement.stopServingOn)
      reassociate_startServingOn reassociate_stopServingOn
      (forgetsAlong_counted (keyAt walk) (rightKeep walk))
      (adversary.main keys.1.2) 1 [] keys.2 _]
  refine bind_congr fun middle => ?_
  rw [← ServingForget.bind_of_forgetsAlong reassociate _ _
      (forgetsAlong_counted (keyAt walk) (rightKeep walk))
      (countRecorded verifierCost
        (Scheme.verify keys.1.2 middle.1.message middle.1.signature))
      middle.2.2.2 _]
  refine bind_congr fun final => ?_
  rfl

/-! ## The charge at the carrier tail

**Both definitions stay reducible, and testing that was the first thing to do.** Trap one says
to make a game definition opaque before stating support and probability lemmas about it, and I
applied it here by reflex. It is the cause rather than the cure at this join: with `carrierTail`
and `threeStageHandlerRun` irreducible the statement does not elaborate inside four million
heartbeats; with both reducible it elaborates in two seconds. The attribute helps where a
rewrite must *avoid* unfolding; here the unifier has to see through the two runs to match them,
and blocking it makes the search diverge instead of succeed.

The type arguments are supplied rather than inferred, for the usual reason: six metavariables
under a three-stage run is the seventh member of the family that reports `timeout` and names
neither the metavariable nor the cause.
-/

end SlhDsaSecurity.CarrierCoverage
