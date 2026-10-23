/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.CarrierFiles
public import HashSig.SLHDSA.SHAKE128s.Proof.ServingForget

/-!
# The counter inside the view, so the counted handler is a recorder

`CarrierTail.handlerAt` is `CountedHandler.withCount` of a noticing recorder, with state
`HandlerCarrier.State × ((Record × Record) × Nat)`. The tape machinery is stated at a bare
`RecorderView.noticingRecorderOf` over a general view, whose state is
`RecorderView.StateOf σ = σ × Record × Record`. **Those two are the same data associated
differently**, and nothing above them cares which association it is.

**So the counter moves into the view rather than the predicate changing.** Putting the bump in
`CacheView.onQuery` reproduces `withCount` exactly, and the reason is one arithmetic fact:
`hashCost` is `0` on a coin and `1` on a hash query, and `onQuery` fires on exactly the hash
queries. The bracket mismatch resolves through the same re-encoding at no cost, because
`ServedAgreement.startServingOn` and `stopServingOn` are already stated at
`HandlerCarrier.State × τ` and touch only the carrier, so at the re-encoded state they are a
view-level map in the first component — which is what the tape layer asks of a bracket.

`CarrierTail.handlerAt` itself is untouched. This is a transport, not a change of shape.
-/

@[expose] public section

open OracleComp OracleSpec

namespace SlhDsaSecurity.CountedView

variable {β : Type}

open Security RecorderView HandlerCarrier CarriedWitness

/-- The carrier with its hash counter beside it. -/
abbrev Counted : Type := HandlerCarrier.State × Nat

/-- The counted handler's state, re-associated as a recorder state over `Counted`. -/
def reassociate (state : HandlerCarrier.State ×
    ((DigestTape.Record × DigestTape.Record) × Nat)) : RecorderView.StateOf Counted :=
  ((state.1, state.2.2), state.2.1)

open scoped Classical in
/-- **The carrier-with-counter as a cache view.** The notice bumps the counter, which is what
`withCount` does on a hash query and the only thing it does. -/
@[reducible] noncomputable def countedView (pk : PublicKey) : CacheView Counted where
  cacheOf := fun state => state.1.cache
  update := fun state input answer => (HandlerCarrier.cacheAnswer state.1 input answer, state.2)
  onQuery := fun state input => (servingNotice pk state.1 input, state.2 + 1)
  cache_update := fun _ _ _ => rfl
  cache_onQuery := fun state input => cacheOf_servingNotice pk state.1 input

/-- A test on the carrier, read at the carrier-with-counter. -/
def liftTest (test : Bytes → HandlerCarrier.State → Prop) :
    Bytes → Counted → Prop := fun input state => test input state.1

open scoped Classical in
/-- **One step of the counted carrier recorder is one step of the noticing recorder at the
counted view**, through the re-association. The coin case is where the arithmetic fact is used:
`withCount` adds `hashCost` and the notice does not fire, and both leave the counter alone
because a coin costs nothing. -/
theorem step_counted (pk : PublicKey) (rightKeep : Bytes → HandlerCarrier.State → Prop)
    (queried : OracleWorld.Domain)
    (state : HandlerCarrier.State × ((DigestTape.Record × DigestTape.Record) × Nat)) :
    (fun z : OracleWorld.Range queried × _ => (z.1, reassociate z.2)) <$>
        ((CarrierFiles.countedCarrierRecorder pk rightKeep) queried).run state =
      ((@noticingRecorderOf Counted (countedView pk) (liftTest (disclosingKeep pk))
        (liftTest rightKeep)) queried).run (reassociate state) := by
  classical
  rw [CarrierFiles.countedCarrierRecorder, CountedHandler.withCount_run]
  rcases queried with coin | input
  · show (fun z : OracleWorld.Range (Sum.inl coin) × _ => (z.1, reassociate z.2)) <$>
        ((@recorderOf HandlerCarrier.State (servingView pk) (disclosingKeep pk) rightKeep
            (Sum.inl coin)).run (state.1, state.2.1) >>= fun step =>
          (pure (step.1, (step.2.1, (step.2.2, state.2.2 + 0))) : ProbComp _)) =
      (@recorderOf Counted (countedView pk) (liftTest (disclosingKeep pk)) (liftTest rightKeep)
        (Sum.inl coin)).run (reassociate state)
    rw [@recorderOf_run_inl HandlerCarrier.State (servingView pk) _ _ coin
        (state.1, state.2.1),
      @recorderOf_run_inl Counted (countedView pk) _ _ coin (reassociate state)]
    simp only [map_bind, bind_assoc, pure_bind, map_pure]
    rfl
  · show (fun z : OracleWorld.Range (Sum.inr input) × _ => (z.1, reassociate z.2)) <$>
        ((@recorderOf HandlerCarrier.State (servingView pk) (disclosingKeep pk) rightKeep
            (Sum.inr input)).run (servingNotice pk state.1 input, state.2.1) >>= fun step =>
          (pure (step.1, (step.2.1, (step.2.2, state.2.2 + 1))) : ProbComp _)) =
      (@recorderOf Counted (countedView pk) (liftTest (disclosingKeep pk)) (liftTest rightKeep)
        (Sum.inr input)).run ((servingNotice pk state.1 input, state.2.2 + 1), state.2.1)
    cases hcached : HandlerCarrier.cacheOf (servingNotice pk state.1 input) input with
    | some cached =>
      rw [@recorderOf_run_inr_some HandlerCarrier.State (servingView pk) _ _ input
          (servingNotice pk state.1 input, state.2.1) cached hcached,
        @recorderOf_run_inr_some Counted (countedView pk) _ _ input
          ((servingNotice pk state.1 input, state.2.2 + 1), state.2.1) cached hcached]
      simp only [map_pure, pure_bind]
      rfl
    | none =>
      rw [@recorderOf_run_inr_none HandlerCarrier.State (servingView pk) _ _ input
          (servingNotice pk state.1 input, state.2.1) hcached,
        @recorderOf_run_inr_none Counted (countedView pk) _ _ input
          ((servingNotice pk state.1 input, state.2.2 + 1), state.2.1) hcached]
      simp only [map_bind, map_pure]
      rfl

open scoped Classical in
/-- **The counted carrier recorder forgets along the re-association.** One induction over the
computation on top of the step law. -/
theorem forgetsAlong_counted (pk : PublicKey)
    (rightKeep : Bytes → HandlerCarrier.State → Prop) :
    ServingForget.ForgetsAlong reassociate
      (CarrierFiles.countedCarrierRecorder pk rightKeep)
      (@noticingRecorderOf Counted (countedView pk) (liftTest (disclosingKeep pk))
        (liftTest rightKeep)) := by
  classical
  intro β computation
  induction computation using OracleComp.inductionOn with
  | pure value => intro state; simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind queried next ih =>
    intro state
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
    rw [← step_counted pk rightKeep queried state]
    simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
    refine bind_congr fun step => ?_
    rw [← ih step.1 step.2, map_eq_bind_pure_comp]
    rfl

end SlhDsaSecurity.CountedView
