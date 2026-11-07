/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module
public import VCVio.CryptoFoundations.SignatureAlg.CountedExperiment.Meter

/-!
# Full-state consumers of counted query meters

The adaptive client retains normal errors and branches on their actual values.
Zero-weight traffic, arbitrary warm counters and the entire underlying state remain joint.
Separate controls distinguish primitive weights from phase and attempt charges.
-/

public section

namespace VCVioTest.CryptoFoundations.SigningViewCountedMeter

open OracleComp OracleSpec SignatureAlg.SigningView

universe v

/-- Every continuation receives the same complete observation and underlying state. -/
theorem complete_continuation
    {ι Request PK SK Sig Reply σ β : Type} {spec : OracleSpec.{0, 0} ι}
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    (policy : Event spec Request → Nat) (weight : spec.Domain → Nat)
    (ambient : ∀ phase input, policy (.ambient phase input) = weight input)
    (attempt0 : ∀ request, policy (.signingAttempt request) = 0)
    (view : SignatureAlg.SigningView (OracleComp spec) Request PK SK Sig Reply)
    (A : PK → OracleComp (spec + (Request →ₒ Reply)) (Request × Sig))
    (impl : QueryImpl spec (StateT σ m)) (initial : σ) (start : Nat)
    (finish : Observation Request Sig Reply Nat × (σ × Nat) → m β) :
    ((simulateQ (impl.extendState (fun t _ _ _ n => n + weight t))
      (countedExperiment policy view A)).run (initial, start) >>= finish) =
      ((simulateQ impl (countedExperiment policy view A)).run initial >>=
        fun z => finish (z.1, (z.2, start + z.1.cost))) := by
  rw [countedExperiment_extendState_weight_run policy weight ambient attempt0]
  simp only [bind_map_left]

private abbrev traffic : OracleSpec (Bool ⊕ Nat)
  | .inl false => Unit
  | .inl true => Option Nat
  | .inr _ => Nat

private def weight : traffic.Domain → Nat
  | .inl _ => 0
  | .inr _ => 2

private def policy : Event traffic Nat → Nat
  | .ambient _ input => weight input
  | .signingAttempt _ => 0

private def view (seed : Nat) :
    SignatureAlg.SigningView (OracleComp traffic) Nat Nat Unit Nat (Except Nat Nat) where
  keygen := do
    let _ ← liftM (traffic.query (.inl false))
    let pk ← liftM (traffic.query (.inr seed))
    return (pk, ())
  sign _ _ request := do
    let selected : Option Nat ← liftM (traffic.query (.inl true))
    let answer : Nat ← liftM (traffic.query (.inr request))
    return match selected with
      | none => .error answer
      | some old => .ok (old + answer)
  verify _ request _ := do
    let _ ← liftM (traffic.query (.inr request))
    return false
  readback
    | .error _ => none
    | .ok signature => some signature

private def client (request : Nat) (pk : Nat) :
    OracleComp (traffic + (Nat →ₒ Except Nat Nat)) (Nat × Nat) := do
  let reply ← liftM ((traffic + (Nat →ₒ Except Nat Nat)).query (.inr (request + pk)))
  match reply with
  | .error err =>
    let answer ← liftM ((traffic + (Nat →ₒ Except Nat Nat)).query (.inl (.inr err)))
    return (err, answer)
  | .ok signature =>
    let selected ← liftM ((traffic + (Nat →ₒ Except Nat Nat)).query (.inl (.inl true)))
    return (request, signature + selected.getD 0)

private def handler : QueryImpl traffic (StateT (List Nat × Nat) Id)
  | .inl false => StateT.mk fun state => pure ((), state)
  | .inl true => StateT.mk fun state => pure (none, state)
  | .inr input => StateT.mk fun (log, count) =>
      pure (input + count, (log ++ [input], count + 1))

private theorem costed_map {α β : Type} (phase : Phase)
    (f : α → β) (body : OracleComp traffic α) :
    costed policy phase (f <$> body) = f <$> costed policy phase body :=
  simulateQ_map _ body f

-- The error code determines both the client's next query and its final candidate.
private theorem adaptive_base (seed request count : Nat) (log : List Nat) :
    let sent := request + (seed + count)
    let err := sent + (count + 1)
    ((simulateQ handler (countedExperiment policy (view seed) (client request))).run
      (log, count)).run =
      (({ forgery := (err, err + (count + 2)),
          rawLog := [⟨sent, .error err⟩], verified := false, cost := 8 } :
            Observation Nat Nat (Except Nat Nat) Nat),
        (log ++ [seed, sent, err, err], count + 4)) := by
  simp [countedExperiment, countedAfterKeygen, countedPhase, countedPhaseUsing,
    countedHandlerUsing, countedSigningOracleUsing, view, client,
    costed_bind, costed_query, costed_map,
    QueryImpl.withAddCost_apply, QueryImpl.withLogging_apply,
    AddWriterT.runAdd, AddWriterT.addTell, WriterT.run_bind,
    handler, policy, weight, Nat.add_assoc, List.append_assoc]

-- Apply the public law to that same adaptive execution, from every warm starting counter.
private theorem adaptive_warm_full_state (seed request count start : Nat) (log : List Nat) :
    let sent := request + (seed + count)
    let err := sent + (count + 1)
    ((simulateQ (handler.extendState (fun t _ _ _ n => n + weight t))
      (countedExperiment policy (view seed) (client request))).run
        ((log, count), start)).run =
      (({ forgery := (err, err + (count + 2)),
          rawLog := [⟨sent, .error err⟩], verified := false, cost := 8 } :
            Observation Nat Nat (Except Nat Nat) Nat),
        ((log ++ [seed, sent, err, err], count + 4), start + 8)) := by
  rw [countedExperiment_extendState_weight_run policy weight (fun _ _ => rfl) (fun _ => rfl)]
  rw [Id.run_map, adaptive_base]

private abbrev UnitTraffic := Unit →ₒ Unit

private def pureView :
    SignatureAlg.SigningView (OracleComp UnitTraffic) Unit Unit Unit Unit (Except Unit Unit) where
  keygen := pure ((), ())
  sign _ _ _ := pure (.error ())
  verify _ _ _ := pure false
  readback
    | .error _ => none
    | .ok signature => some signature

private def unitHandler : QueryImpl UnitTraffic (StateT Unit Id) := fun _ => pure ()

private theorem pure_boundary (start : Nat) :
    ((simulateQ (unitHandler.extendState (fun _ _ _ _ n => n))
      (countedExperiment (fun _ => 0) pureView (fun _ => pure ((), ())))).run
        ((), start)).run =
      (({ forgery := ((), ()), rawLog := [], verified := false, cost := 0 } :
        Observation Unit Unit (Except Unit Unit) Nat), ((), start)) := by
  simp [countedExperiment, countedAfterKeygen, countedPhase, countedPhaseUsing,
    pureView, costed, AddWriterT.runAdd]

private def oneAttempt (_ : Unit) :
    OracleComp (UnitTraffic + (Unit →ₒ Except Unit Unit)) (Unit × Unit) := do
  let _ ← liftM ((UnitTraffic + (Unit →ₒ Except Unit Unit)).query (.inr ()))
  return ((), ())

private def attemptPolicy : Event UnitTraffic Unit → Nat
  | .ambient _ _ => 0
  | .signingAttempt _ => 1

-- A pure signing request can emit a nonzero attempt cost without any primitive query.
private theorem attempt_charge_not_metered (start : Nat) :
    let result := ((simulateQ (unitHandler.extendState (fun _ _ _ _ n => n))
      (countedExperiment attemptPolicy pureView oneAttempt)).run ((), start)).run
    result.1.cost = 1 ∧ result.2.2 = start := by
  simp [countedExperiment, countedAfterKeygen, countedPhase, countedPhaseUsing,
    countedHandlerUsing, countedSigningOracleUsing, oneAttempt, pureView,
    costed, QueryImpl.withLogging_apply, attemptPolicy,
    AddWriterT.runAdd, AddWriterT.addTell, WriterT.run_bind]

private theorem attempt_charge_breaks_coherence (start : Nat) :
    let result := ((simulateQ (unitHandler.extendState (fun _ _ _ _ n => n))
      (countedExperiment attemptPolicy pureView oneAttempt)).run ((), start)).run
    result.2.2 ≠ start + result.1.cost := by
  obtain ⟨cost, counter⟩ := attempt_charge_not_metered start
  dsimp only
  rw [counter, cost]
  exact Nat.ne_of_lt (Nat.lt_succ_self start)

private def phaseView :
    SignatureAlg.SigningView (OracleComp UnitTraffic) Unit Unit Unit Unit Unit where
  keygen := do
    let _ ← liftM (UnitTraffic.query ())
    return ((), ())
  sign _ _ _ := pure ()
  verify _ _ _ := pure false
  readback := some

private def oneDirect (_ : Unit) :
    OracleComp (UnitTraffic + (Unit →ₒ Unit)) (Unit × Unit) := do
  let _ ← liftM ((UnitTraffic + (Unit →ₒ Unit)).query (.inl ()))
  return ((), ())

private def phasePolicy : Event UnitTraffic Unit → Nat
  | .ambient .keygen _ => 1
  | .ambient _ _ => 2
  | .signingAttempt _ => 0

-- The two identical primitive queries have different declared costs in their two phases.
private theorem phase_charge_not_metered (start : Nat) :
    let result := ((simulateQ (unitHandler.extendState (fun _ _ _ _ n => n + 1))
      (countedExperiment phasePolicy phaseView oneDirect)).run ((), start)).run
    result.1.cost = 3 ∧ result.2.2 = start + 2 := by
  simp [countedExperiment, countedAfterKeygen, countedPhase, countedPhaseUsing,
    countedHandlerUsing, phaseView, oneDirect, costed,
    QueryImpl.withAddCost_apply, phasePolicy, AddWriterT.runAdd, AddWriterT.addTell,
    WriterT.run_bind, unitHandler, QueryImpl.extendState_apply, Nat.add_assoc]

private theorem phase_charge_breaks_coherence (start : Nat) :
    let result := ((simulateQ (unitHandler.extendState (fun _ _ _ _ n => n + 1))
      (countedExperiment phasePolicy phaseView oneDirect)).run ((), start)).run
    result.2.2 ≠ start + result.1.cost := by
  obtain ⟨cost, counter⟩ := phase_charge_not_metered start
  dsimp only
  rw [counter, cost]
  exact Nat.ne_of_lt (Nat.add_lt_add_left (by decide : 2 < 3) start)

end VCVioTest.CryptoFoundations.SigningViewCountedMeter
