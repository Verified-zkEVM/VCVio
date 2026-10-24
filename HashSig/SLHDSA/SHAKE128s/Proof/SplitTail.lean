/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.CarrierCoverage
public import HashSig.SLHDSA.SHAKE128s.Proof.SplitCounted

/-!
# The split tail, sitting above the tail

`SplitCounted` says what counts the counted handler admits and gives the split one. This is the
tail at that handler: the same three stages, the same brackets, the same value, and the two
slots carried out beside the value, where the two charges can read them.

**It sits above `CarrierTail.carrierTail` rather than replacing it.** `map_splitCarrierTail`
says the split tail's first component *is* the tail, so an event of the tail is an event of the
split tail through `Prod.fst`, and the tape factorisation does not have to be redone. Nothing in
`BracketedRun`, `CarrierTail` or anything read off them moves.

## How the chain is built

Exactly as `CarrierTail.forget_carrierTail` is: each stage's transport written once as a bind,
then `bind_assoc` flattens both sides and `bind_congr` walks them together. The three transports
are `ServingForget.bind_of_forgetsAlong` twice and `bind_of_fuseServing_conj` once, and the
hypotheses they need are `SplitCounted.forgetsAlong_sumSlots` and the two bracket-commutation
laws. No induction is added here.
-/

public section

open OracleComp OracleSpec
open scoped ENNReal

namespace SlhDsaSecurity.SplitTail

variable {α : Type}

open Security RecorderView CarriedWitness PhaseFusion RecordedQueries BracketedRun
open SplitCounted CarrierTail

/-- The handler a split tail runs under: the tail's handler, counting in two slots. -/
@[expose] noncomputable def splitHandlerAt (inClass : Bytes → Prop) (inside outside : QueryKind)
    (rightKeep : Walk → Bytes → HandlerCarrier.State → Prop) (walk : Walk) :
    QueryImpl OracleWorld (StateT (HandlerCarrier.State ×
      ((DigestTape.Record × DigestTape.Record) × Counts)) ProbComp) :=
  splitCarrierRecorder (keyAt walk) inClass inside outside (rightKeep walk)

/-- **It forgets to the tail's handler**, summing the slots. -/
theorem forgetsAlong_splitHandlerAt (inClass : Bytes → Prop) {inside outside : QueryKind}
    (hne : inside ≠ outside) (rightKeep : Walk → Bytes → HandlerCarrier.State → Prop)
    (walk : Walk) :
    ServingForget.ForgetsAlong (sumSlots inside outside)
      (splitHandlerAt inClass inside outside rightKeep walk) (handlerAt rightKeep walk) :=
  forgetsAlong_sumSlots inClass hne _

/-- **The split tail.** The tail's three stages at the split handler, with the two slots carried
out beside the tail's own value. -/
@[expose] noncomputable def splitCarrierTail (inClass : Bytes → Prop) (inside outside : QueryKind)
    (rightKeep : Walk → Bytes → HandlerCarrier.State → Prop) (adversary : Adversary)
    (walk : Walk) :
    ProbComp ((((Outcome × Multiset Bytes) × Nat) × SplitPrefix.SplitState) × Counts) :=
  (simulateQ (splitHandlerAt inClass inside outside rightKeep walk)
      (Scheme.keygenInternal walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2)).run
    (startAt walk.2, (([], []), 0)) >>= fun keys =>
    (simulateQ (fuseServing (splitHandlerAt inClass inside outside rightKeep walk)
        (recordedAdversaryImpl + recordedSigningOracle (Scheme.sign keys.1.1))
        ServedAgreement.startServingOn ServedAgreement.stopServingOn)
      (adversary.main keys.1.2)).run (1, [], keys.2) >>= fun middle =>
      (simulateQ (splitHandlerAt inClass inside outside rightKeep walk)
        (countRecorded verifierCost
          (Scheme.verify keys.1.2 middle.1.message middle.1.signature))).run
        middle.2.2.2 >>= fun final =>
        (pure (((({
              forgery := middle.1
              signed := middle.2.2.1
              verified := final.1.1
              counts := (Multiplicative.toAdd middle.2.1).1 + final.1.2.1 },
            (Multiplicative.toAdd middle.2.1).2 + final.1.2.2),
            (sumSlots inside outside final.2).2.2),
          forgetCarrier (sumSlots inside outside final.2)), final.2.2.2) :
          ProbComp ((((Outcome × Multiset Bytes) × Nat) × SplitPrefix.SplitState) × Counts))

/-! ## The three stages, each written once as a bind -/

/-- **The first stage, split.** The carrier's run is the split carrier's run with the two
slots summed. -/
theorem split_first_stage_bind (inClass : Bytes → Prop) {inside outside : QueryKind}
    (hne : inside ≠ outside) (rightKeep : Walk → Bytes → HandlerCarrier.State → Prop)
    (walk : Walk) {α : Type} (computation : OracleComp OracleWorld α) :
    (simulateQ (handlerAt rightKeep walk) computation).run
        (startAt walk.2, (([], []), 0)) =
      (simulateQ (splitHandlerAt inClass inside outside rightKeep walk) computation).run
          (startAt walk.2, (([], []), 0)) >>= fun z =>
        (pure (z.1, sumSlots inside outside z.2) : ProbComp (α × CountedState)) := by
  have hforget := forgetsAlong_splitHandlerAt inClass hne rightKeep walk computation
    (startAt walk.2, (([], []), (0 : Counts)))
  rw [show sumSlots inside outside (startAt walk.2, (([], []), (0 : Counts))) =
      (startAt walk.2, (([], []), (0 : Nat))) from rfl] at hforget
  rw [← hforget, map_eq_bind_pure_comp]
  rfl

/-- **The middle stage, split.** The bracketed fused phase over the carrier's handler is
the one over the split carrier's handler with the two slots summed. -/
theorem split_middle_stage_bind (inClass : Bytes → Prop) {inside outside : QueryKind}
    (hne : inside ≠ outside) (rightKeep : Walk → Bytes → HandlerCarrier.State → Prop)
    (walk : Walk) (adversary : Adversary)
    (keys : (SecretKey × PublicKey) × (HandlerCarrier.State ×
      ((DigestTape.Record × DigestTape.Record) × Counts))) :
    (simulateQ (fuseServing (handlerAt rightKeep walk)
        (recordedAdversaryImpl + recordedSigningOracle (Scheme.sign keys.1.1))
        ServedAgreement.startServingOn ServedAgreement.stopServingOn)
        (adversary.main keys.1.2)).run (1, [], sumSlots inside outside keys.2) =
      (simulateQ (fuseServing (splitHandlerAt inClass inside outside rightKeep walk)
          (recordedAdversaryImpl + recordedSigningOracle (Scheme.sign keys.1.1))
          ServedAgreement.startServingOn ServedAgreement.stopServingOn)
          (adversary.main keys.1.2)).run (1, [], keys.2) >>= fun z =>
        (pure (z.1, (z.2.1, z.2.2.1, sumSlots inside outside z.2.2.2)) :
          ProbComp (Forgery × (Multiplicative Tally × SigningLog × CountedState))) := by
  rw [← ServingForget.run_fuseServing_conj (sumSlots inside outside)
      (splitHandlerAt inClass inside outside rightKeep walk) (handlerAt rightKeep walk)
      (recordedAdversaryImpl + recordedSigningOracle (Scheme.sign keys.1.1))
      ServedAgreement.startServingOn ServedAgreement.stopServingOn
      ServedAgreement.startServingOn ServedAgreement.stopServingOn
      (fun request state => sumSlots_startServingOn inside outside request state)
      (fun state => sumSlots_stopServingOn inside outside state)
      (forgetsAlong_splitHandlerAt inClass hne rightKeep walk) (adversary.main keys.1.2)
      1 [] keys.2, map_eq_bind_pure_comp]
  rfl

/-- **The last stage, split.** The carrier's run of the counted verifier is the split
carrier's run with the two slots summed. -/
theorem split_last_stage_bind (inClass : Bytes → Prop) {inside outside : QueryKind}
    (hne : inside ≠ outside) (rightKeep : Walk → Bytes → HandlerCarrier.State → Prop)
    (walk : Walk) (pk : PublicKey) (forgery : Forgery)
    (state : HandlerCarrier.State × ((DigestTape.Record × DigestTape.Record) × Counts)) :
    (simulateQ (handlerAt rightKeep walk) (countRecorded verifierCost
        (Scheme.verify pk forgery.message forgery.signature))).run
        (sumSlots inside outside state) =
      (simulateQ (splitHandlerAt inClass inside outside rightKeep walk)
          (countRecorded verifierCost
            (Scheme.verify pk forgery.message forgery.signature))).run state >>= fun z =>
        (pure (z.1, sumSlots inside outside z.2) :
          ProbComp ((Bool × Tally) × CountedState)) := by
  rw [← forgetsAlong_splitHandlerAt inClass hne rightKeep walk (countRecorded verifierCost
      (Scheme.verify pk forgery.message forgery.signature)) state, map_eq_bind_pure_comp]
  rfl

/-- **The split tail's first component is the tail.** Three stages matched one for one, as in
`CarrierTail.forget_carrierTail`, and no induction added. -/
theorem map_splitCarrierTail (inClass : Bytes → Prop) {inside outside : QueryKind}
    (hne : inside ≠ outside) (rightKeep : Walk → Bytes → HandlerCarrier.State → Prop)
    (adversary : Adversary) (walk : Walk) :
    Prod.fst <$> splitCarrierTail inClass inside outside rightKeep adversary walk =
      carrierTail rightKeep adversary walk := by
  rw [carrierTail, split_first_stage_bind inClass hne rightKeep walk
      (Scheme.keygenInternal walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2), splitCarrierTail]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
  refine bind_congr fun keys => ?_
  rw [split_middle_stage_bind inClass hne rightKeep walk adversary keys]
  simp only [bind_assoc, pure_bind]
  refine bind_congr fun middle => ?_
  rw [split_last_stage_bind inClass hne rightKeep walk keys.1.2 middle.1 middle.2.2.2]
  simp only [bind_assoc, pure_bind]

end SlhDsaSecurity.SplitTail
