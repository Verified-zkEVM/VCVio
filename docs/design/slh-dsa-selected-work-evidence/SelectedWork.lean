/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import VCVio.CryptoFoundations.SignatureAlg.CountedExperiment
public import VCVio.OracleComp.SimSemantics.StateT.StateProjection

/-! # Deterministic signature-experiment event markers -/

@[expose] public section

open OracleSpec OracleComp

universe v

namespace SignatureAlg.SigningView.Events

/-- Native queries together with deterministic phase and signing-attempt markers. -/
abbrev Spec {ι : Type} (spec : OracleSpec.{0, 0} ι) (Request : Type) :
    OracleSpec.{0, 0} (ι ⊕ Event spec Request) :=
  spec + (Event spec Request →ₒ PUnit)

/-- Emit one phase or signing-attempt event. -/
def emit {ι : Type} (spec : OracleSpec.{0, 0} ι) (Request : Type)
    (event : Event spec Request) : OracleComp (Spec spec Request) PUnit :=
  liftM ((Spec spec Request).query (.inr event))

/-- Record an ambient event before forwarding its native query. -/
def phaseImpl {ι : Type} (spec : OracleSpec.{0, 0} ι) (Request : Type)
    (phase : Phase) : QueryImpl spec (OracleComp (Spec spec Request)) :=
  QueryImpl.preInsert
    (fun input => (liftM ((Spec spec Request).query (.inl input)) :
      OracleComp (Spec spec Request) (spec.Range input)))
    (fun input => emit spec Request (.ambient phase input))

/-- Embed the supplied algorithms with their phase and callback-entry events. -/
def viewWithEvents {ι Request PK SK Sig Reply : Type} {spec : OracleSpec.{0, 0} ι}
    (view : SignatureAlg.SigningView (OracleComp spec) Request PK SK Sig Reply) :
    SignatureAlg.SigningView (OracleComp (Spec spec Request)) Request PK SK Sig Reply where
  keygen := simulateQ (phaseImpl spec Request .keygen) view.keygen
  sign pk sk request := do
    emit spec Request (.signingAttempt request)
    simulateQ (phaseImpl spec Request .signer) (view.sign pk sk request)
  verify pk request sig :=
    simulateQ (phaseImpl spec Request .verification) (view.verify pk request sig)
  readback := view.readback

/-- Embed the source adversary's native traffic while forwarding its signing calls. -/
def mainWithEvents {ι Request PK Sig Reply : Type} {spec : OracleSpec.{0, 0} ι}
    (adv : PK → OracleComp (spec + (Request →ₒ Reply)) (Request × Sig)) :
    PK → OracleComp (Spec spec Request + (Request →ₒ Reply)) (Request × Sig) :=
  fun pk => simulateQ
    (QueryImpl.add (spec₁ := spec) (spec₂ := Request →ₒ Reply)
      (fun input => simulateQ
        (fun native => liftM ((Spec spec Request + (Request →ₒ Reply)).query (.inl native)))
        (phaseImpl spec Request .adversary input))
      (fun request => liftM ((Spec spec Request + (Request →ₒ Reply)).query (.inr request))))
    (adv pk)

/-- Interpret native queries with the supplied handler and event markers with unit. -/
def handlerWithEvents {ι Request : Type} {spec : OracleSpec.{0, 0} ι}
    {m : Type → Type v} [Monad m] (handler : QueryImpl spec m) :
    QueryImpl (Spec spec Request) m :=
  fun input => match input with
  | .inl native => handler native
  | .inr _ => pure ⟨⟩

/-- Only deterministic event markers contribute the declared input cost. -/
def inputCost {ι Request : Type} {spec : OracleSpec.{0, 0} ι}
    (policy : Event spec Request → Nat) : (Spec spec Request).Domain → Nat :=
  Sum.elim (fun _ => 0) policy


private def costImpl {ι Request : Type} {spec : OracleSpec.{0, 0} ι}
    (policy : Event spec Request → Nat) : QueryImpl (Spec spec Request) (CostM spec Nat) :=
  fun input => match input with
  | .inl native => liftM (liftM (spec.query native) : OracleComp spec (spec.Range native))
  | .inr event => do
    AddWriterT.addTell (policy event)
    pure ⟨⟩

private theorem simulateQ_phaseImpl {ι Request α : Type} {spec : OracleSpec.{0, 0} ι}
    (policy : Event spec Request → Nat) (phase : Phase) (body : OracleComp spec α) :
    simulateQ (costImpl policy) (simulateQ (phaseImpl spec Request phase) body) =
      costed policy phase body := by
  unfold costed
  apply QueryImpl.simulateQ_simulateQ_eq_of_apply
  intro input
  simp [phaseImpl, emit, costImpl, QueryImpl.withAddCost_apply, monad_norm]

private theorem simulateQ_client {ι Request PK SK Sig Reply : Type}
    {spec : OracleSpec.{0, 0} ι} (policy : Event spec Request → Nat)
    (view : SignatureAlg.SigningView (OracleComp spec) Request PK SK Sig Reply)
    (pk : PK) (sk : SK)
    (adv : PK → OracleComp (spec + (Request →ₒ Reply)) (Request × Sig)) :
    simulateQ (costImpl policy)
      ((viewWithEvents view).runWithSigningOracle pk sk (mainWithEvents adv pk)) =
      countedPhase policy view pk sk (adv pk) := by
  let red : QueryImpl (spec + (Request →ₒ Reply))
      (WriterT (QueryLog (Request →ₒ Reply)) (OracleComp (Spec spec Request))) :=
    ((Spec spec Request).passthrough + (viewWithEvents view).signingOracle pk sk) ∘ₛ
      QueryImpl.add (spec₁ := spec) (spec₂ := Request →ₒ Reply)
        (fun input => simulateQ
          (fun native => liftM ((Spec spec Request + (Request →ₒ Reply)).query (.inl native)))
          (phaseImpl spec Request .adversary input))
        (fun request => liftM ((Spec spec Request + (Request →ₒ Reply)).query (.inr request)))
  rw [runWithSigningOracle, mainWithEvents, ← QueryImpl.simulateQ_compose]
  change simulateQ (costImpl policy) (simulateQ red (adv pk)).run =
    (simulateQ (countedHandler policy view pk sk) (adv pk)).run
  apply simulateQ_WriterT_compose
  intro input
  cases input with
  | inl input =>
    have step : (red (.inl input)).run =
        (fun answer => (answer, [])) <$> (phaseImpl spec Request .adversary input) := by
      simp only [red, QueryImpl.apply_compose, QueryImpl.add]
      have h : simulateQ
          ((Spec spec Request).passthrough + (viewWithEvents view).signingOracle pk sk)
          (simulateQ
            (fun native => liftM ((Spec spec Request + (Request →ₒ Reply)).query (.inl native)))
            (phaseImpl spec Request .adversary input)) =
          simulateQ ((QueryImpl.id' (Spec spec Request)).liftTarget
            (WriterT (QueryLog (Request →ₒ Reply)) (OracleComp (Spec spec Request))))
            (phaseImpl spec Request .adversary input) := by
        apply QueryImpl.simulateQ_simulateQ_eq_of_apply
        intro native
        simp only [simulateQ_spec_query, QueryImpl.passthrough_add, QueryImpl.add_apply_inl]
      rw [h, writerT_run_simulateQ_liftTarget, simulateQ_id']
      rfl
    rw [step, simulateQ_map]
    have h := simulateQ_phaseImpl policy .adversary (liftM (spec.query input))
    simp only [simulateQ_spec_query] at h
    rw [h]
    simp [countedHandler, countedHandlerUsing, costed, QueryImpl.withAddCost_apply]
  | inr request =>
    have step : (red (.inr request)).run =
        (fun answer => (answer, [⟨request, answer⟩])) <$>
          (viewWithEvents view).sign pk sk request := by
      simp [red, QueryImpl.add, signingOracle, QueryImpl.withLogging_apply]
    rw [step, simulateQ_map]
    change (fun answer : Reply => (answer, ([⟨request, answer⟩] : QueryLog (Request →ₒ Reply)))) <$>
      simulateQ (costImpl policy) (emit spec Request (.signingAttempt request) >>= fun _ =>
        simulateQ (phaseImpl spec Request .signer) (view.sign pk sk request)) = _
    have hemit : simulateQ (costImpl policy) (emit spec Request (.signingAttempt request)) =
        AddWriterT.addTell (policy (.signingAttempt request)) := by
      simp [emit, costImpl, AddWriterT.addTell]
    rw [simulateQ_bind, hemit]
    simp [simulateQ_phaseImpl, countedHandler, countedHandlerUsing,
      countedSigningOracleUsing_run, map_bind]

private def accumulate {ι Cache : Type} {spec : OracleSpec.{0, 0} ι}
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    (handler : QueryImpl spec (StateT Cache m)) :
    CostM spec Nat →ᵐ StateT (Cache × Nat) m where
  toFun {_α} body := StateT.mk fun initial =>
    (fun result => (result.1.1, (result.2, initial.2 + result.1.2))) <$>
      (simulateQ handler body.runAdd).run initial.1
  toFun_pure' value := by
    apply StateT.ext
    intro initial
    simp
  toFun_bind' body next := by
    apply StateT.ext
    intro initial
    simp only [StateT.run_mk, AddWriterT.runAdd_bind, simulateQ_bind, StateT.run_bind,
      simulateQ_map, StateT.run_map, map_bind, bind_map_left, Functor.map_map]
    apply bind_congr
    rintro ⟨⟨value, cost⟩, cache⟩
    simp [Nat.add_assoc]

/-- Event-marker interpretation preserves the complete counted outcome, cache and cost. -/
theorem selectedCost_run
    {ι Request PK SK Sig Reply Cache : Type} {spec : OracleSpec.{0, 0} ι}
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    (policy : Event spec Request → Nat)
    (view : SignatureAlg.SigningView (OracleComp spec) Request PK SK Sig Reply)
    (adv : PK → OracleComp (spec + (Request →ₒ Reply)) (Request × Sig))
    (handler : QueryImpl spec (StateT Cache m)) (initial : Cache)
    (initialCost : Nat) :
    (simulateQ
      ((handlerWithEvents (Request := Request) handler).extendState
        (fun input _ _ _ n => n + inputCost policy input))
      ((viewWithEvents view).experiment (mainWithEvents adv))).run (initial, initialCost) =
      (fun result =>
        (erase result.1, (result.2, initialCost + result.1.cost))) <$>
        (simulateQ handler (countedExperiment policy view adv)).run initial := by
  let body : CostM spec Nat (Outcome Request Sig Reply) := do
    let (pk, sk) ← costed policy .keygen view.keygen
    countedAfterKeygen policy view pk sk adv
  have hfree : simulateQ (costImpl policy)
      ((viewWithEvents view).experiment (mainWithEvents adv)) = body := by
    simp only [experiment, simulateQ_bind, simulateQ_pure]
    change (do
      let keys ← simulateQ (costImpl policy)
        (simulateQ (phaseImpl spec Request .keygen) view.keygen)
      let phase ← simulateQ (costImpl policy)
        ((viewWithEvents view).runWithSigningOracle keys.1 keys.2 (mainWithEvents adv keys.1))
      let verified ← simulateQ (costImpl policy)
        (simulateQ (phaseImpl spec Request .verification) (view.verify keys.1 phase.1.1 phase.1.2))
      pure (⟨phase.1, phase.2, verified⟩ : Outcome Request Sig Reply)) = body
    simp_rw [simulateQ_phaseImpl, simulateQ_client]
    rfl
  have hhandlers : (fun input => accumulate handler (costImpl policy input)) =
      (handlerWithEvents (Request := Request) handler).extendState
        (fun input _ _ _ n => n + inputCost policy input) := by
    funext input
    apply StateT.ext
    rintro ⟨cache, n⟩
    cases input with
    | inl input =>
      simp [accumulate, costImpl, handlerWithEvents, inputCost,
        QueryImpl.extendState_apply, AddWriterT.runAdd_liftM]
    | inr event =>
      simp [accumulate, costImpl, handlerWithEvents, inputCost,
        QueryImpl.extendState_apply]
  have natural := PFunctor.FreeM.liftM_natural (costImpl policy) (accumulate handler)
    ((viewWithEvents view).experiment (mainWithEvents adv))
  change accumulate handler (simulateQ (costImpl policy)
      ((viewWithEvents view).experiment (mainWithEvents adv))) =
    simulateQ (fun input => accumulate handler (costImpl policy input))
      ((viewWithEvents view).experiment (mainWithEvents adv)) at natural
  rw [hhandlers] at natural
  rw [← natural, hfree]
  simp [accumulate, body, countedExperiment, erase, Functor.map_map]

#check @selectedCost_run
#print axioms selectedCost_run

end SignatureAlg.SigningView.Events
