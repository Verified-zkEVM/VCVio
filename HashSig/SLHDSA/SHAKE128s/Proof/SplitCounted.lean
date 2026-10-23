/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.CarrierFiles
public import HashSig.SLHDSA.SHAKE128s.Proof.ClassGrowth
public import HashSig.SLHDSA.SHAKE128s.Proof.RecordInvariant

/-!
# What counts the counted handler admits

The carrier tail's count is a single `Nat` in the handler's state, put there by
`CountedHandler.withCount`: a bracketed game is not one computation, so there is nothing for an
instrumentation wrapped *around* a computation to wrap. A counted handler admits exactly the
per-query accumulations of a cost into a component beside the carrier, the
`CountedHandler.withExtra` instances.

The split counter is such an accumulation: `ClassGrowth.splitCost inClass inside outside` is a
`Domain → Counts` charging each hash call one unit of one of two slots, so `withSplit` is
`withExtra` at `ω := Counts` with the update `(· + splitCost inClass inside outside queried)`.

## Why this costs nothing downstream

Widening `BracketedRun.CountedState` to carry two slots would be a shape change under every
reader, and it is not needed. `run_withSplit_withCount` says the split-counted run **is** the
counted run with its counter split: map the two slots to their sum and the split handler becomes
`withCount`. So a split tail sits *above* the existing tail rather than replacing it, and
`BracketedRun.CountedState` and `CarrierTail.carrierTail` are untouched. The carrier instance is
`splitCarrierRecorder`, with `run_splitCarrierRecorder_counted`. -/

@[expose] public section

open OracleComp OracleSpec

namespace SlhDsaSecurity.SplitCounted

variable {α : Type}

open Security RecorderView HandlerCarrier CarriedWitness ServedAgreement
open CountedHandler ClassGrowth

variable (pk : PublicKey) {τ : Type}

/-- A handler with a two-slot hash counter beside its carrier: one slot for the class, one for
its complement. -/
noncomputable def withSplit (inClass : Bytes → Prop) (inside outside : QueryKind)
    (impl : QueryImpl OracleWorld (StateT (HandlerCarrier.State × τ) ProbComp)) :
    QueryImpl OracleWorld (StateT (HandlerCarrier.State × (τ × Counts)) ProbComp) :=
  withExtra impl (fun queried counts => counts + splitCost inClass inside outside queried)

/-- One step of the split-counted handler: the handler's step, with the query's split
cost added to the counts. -/
theorem withSplit_run (inClass : Bytes → Prop) (inside outside : QueryKind)
    (impl : QueryImpl OracleWorld (StateT (HandlerCarrier.State × τ) ProbComp))
    (queried : OracleWorld.Domain) (state : HandlerCarrier.State × (τ × Counts)) :
    ((withSplit inClass inside outside impl) queried).run state =
      (impl queried).run (state.1, state.2.1) >>= fun step =>
        (pure (step.1, (step.2.1, (step.2.2,
            state.2.2 + splitCost inClass inside outside queried))) :
          ProbComp (OracleWorld.Range queried × (HandlerCarrier.State × (τ × Counts)))) := rfl

/-! ## The two slots are the counter

`run_withSplit_withCount` is the lemma that keeps the split off the tail's state. It says the
split-counted run is the counted run with the counter split in two: map a state's pair of slots
to their sum and the whole run becomes `withCount`'s, started at the summed counter. Read right
to left it builds a split run over the existing one; read left to right it carries any event or
expectation of the split run down to the counted one. -/

/-- **The split-counted run is the counted run, with the counter split.** -/
theorem run_withSplit_withCount (inClass : Bytes → Prop) {inside outside : QueryKind}
    (hne : inside ≠ outside)
    (impl : QueryImpl OracleWorld (StateT (HandlerCarrier.State × τ) ProbComp)) {α : Type}
    (computation : OracleComp OracleWorld α) :
    ∀ state : HandlerCarrier.State × (τ × Counts),
      (fun z : α × (HandlerCarrier.State × (τ × Counts)) =>
          (z.1, (z.2.1, (z.2.2.1, z.2.2.2 inside + z.2.2.2 outside)))) <$>
          (simulateQ (withSplit inClass inside outside impl) computation).run state =
        (simulateQ (withCount impl) computation).run
          (state.1, (state.2.1, state.2.2 inside + state.2.2 outside)) := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro state
    rw [simulateQ_pure, StateT.run_pure, map_pure, simulateQ_pure, StateT.run_pure]
  | query_bind queried next ih =>
    intro state
    have harith : (state.2.2 + splitCost inClass inside outside queried) inside +
        (state.2.2 + splitCost inClass inside outside queried) outside =
        state.2.2 inside + state.2.2 outside + hashCost queried := by
      rw [Pi.add_apply, Pi.add_apply, ← splitCost_add_eq_hashCost inClass hne queried]
      omega
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind, simulateQ_bind,
      simulateQ_spec_query, StateT.run_bind, withSplit_run, withCount_run, bind_assoc,
      bind_assoc]
    refine bind_congr fun step => ?_
    rw [pure_bind, pure_bind,
      ih step.1 (step.2.1, (step.2.2, state.2.2 + splitCost inClass inside outside queried)),
      harith]

/-- The map a split state is read as a counted state through: sum the two slots. -/
def sumSlots (inside outside : QueryKind)
    (state : HandlerCarrier.State × (τ × Counts)) : HandlerCarrier.State × (τ × Nat) :=
  (state.1, (state.2.1, state.2.2 inside + state.2.2 outside))

/-- **The split-counted handler forgets to the counted one along it.** This is
`run_withSplit_withCount` as the interface a bracketed phase reads a handler through, which is
the form every consumer actually wants. -/
theorem forgetsAlong_sumSlots (inClass : Bytes → Prop) {inside outside : QueryKind}
    (hne : inside ≠ outside)
    (impl : QueryImpl OracleWorld (StateT (HandlerCarrier.State × τ) ProbComp)) :
    ServingForget.ForgetsAlong (sumSlots inside outside)
      (withSplit inClass inside outside impl) (withCount impl) :=
  fun computation state => run_withSplit_withCount inClass hne impl computation state

/-! ### And the brackets commute with it

`ServingForget.run_fuseServing_conj` carries a bracketed phase to a bracketed phase along any
`π` the brackets commute with. The tail's brackets touch the carrier's framing and nothing else,
and summing two counter slots touches the counter and nothing else, so they commute by cases on
the request's frame. That is the last hypothesis a split tail needs over the counted one, and
with it the three stages chain by `bind_of_forgetsAlong` and `bind_of_fuseServing_conj` with no
new induction. -/

/-- Summing the slots commutes with opening a signing bracket. -/
theorem sumSlots_startServingOn (inside outside : QueryKind) (request : Message)
    (state : HandlerCarrier.State × (τ × Counts)) :
    sumSlots inside outside (startServingOn request state) =
      startServingOn request (sumSlots inside outside state) := by
  rw [startServingOn, startServingOn]
  cases request.frame with
  | none => rfl
  | some framed => rfl

/-- Summing the slots commutes with closing a signing bracket. -/
theorem sumSlots_stopServingOn (inside outside : QueryKind)
    (state : HandlerCarrier.State × (τ × Counts)) :
    sumSlots inside outside (stopServingOn state) =
      stopServingOn (sumSlots inside outside state) := rfl

/-! ## At the carrier

The tail's handler is `CarrierFiles.countedCarrierRecorder`, which is `withCount` around the
recorder that notices. Its split counterpart is the same recorder under `withSplit`, and the
three laws the tail reads a handler through come back unchanged. -/

/-- The handler a split-counted carrier tail runs under. -/
noncomputable def splitCarrierRecorder (inClass : Bytes → Prop) (inside outside : QueryKind)
    (rightKeep : Bytes → HandlerCarrier.State → Prop) :
    QueryImpl OracleWorld
      (StateT (HandlerCarrier.State ×
        ((DigestTape.Record × DigestTape.Record) × Counts)) ProbComp) :=
  withSplit inClass inside outside
    (@noticingRecorderOf HandlerCarrier.State (servingView pk) (disclosingKeep pk) rightKeep)

/-- **The split carrier recorder is the counted one, with the counter split.** The carrier
instance of `run_withSplit_withCount`, and the statement a split tail is carried onto the
existing tail by. -/
theorem run_splitCarrierRecorder_counted (inClass : Bytes → Prop) {inside outside : QueryKind}
    (hne : inside ≠ outside) (rightKeep : Bytes → HandlerCarrier.State → Prop) {α : Type}
    (computation : OracleComp OracleWorld α) :
    ∀ state : HandlerCarrier.State × ((DigestTape.Record × DigestTape.Record) × Counts),
      (fun z : α × (HandlerCarrier.State ×
            ((DigestTape.Record × DigestTape.Record) × Counts)) =>
          (z.1, (z.2.1, (z.2.2.1, z.2.2.2 inside + z.2.2.2 outside)))) <$>
          (simulateQ (splitCarrierRecorder pk inClass inside outside rightKeep)
            computation).run state =
        (simulateQ (CarrierFiles.countedCarrierRecorder pk rightKeep) computation).run
          (state.1, (state.2.1, state.2.2 inside + state.2.2 outside)) :=
  run_withSplit_withCount inClass hne _ computation

end SlhDsaSecurity.SplitCounted
