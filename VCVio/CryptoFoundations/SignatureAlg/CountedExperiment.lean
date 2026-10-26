/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.CryptoFoundations.SignatureAlg.SigningView
public import VCVio.OracleComp.QueryTracking.WriterCost

/-!
# Phase and input-dependent signature experiment costs

`countedExperiment` runs key generation, a signing-enabled adversary and final verification
in one free-oracle program. `Event` exposes the phase and actual query input, or a signing
attempt's request. A declared policy accumulates costs through the existing additive writer;
its monoid need not be commutative. The ambient oracle interpretation and initial cache remain
outer parameters, shared by every phase.

Cost erasure preserves the complete candidate, raw signing-response log and verification result.
The stateful interpretation laws retain the final cache through arbitrary continuations.
These laws impose no query budget, signing lifetime or probability interpretation.
-/

public section

open OracleSpec OracleComp

namespace SignatureAlg.SigningView

/-- The phase in which an ambient query is made. -/
inductive Phase where
  /-- Queries issued by key generation. -/
  | keygen
  /-- Queries issued directly by the adversary. -/
  | adversary
  /-- Queries issued inside a signing algorithm. -/
  | signer
  /-- Queries issued by the final verifier. -/
  | verification
  deriving DecidableEq, Repr

/-- A policy sees actual query inputs and attempted signing requests. -/
inductive Event {ι : Type} (spec : OracleSpec ι) (Request : Type) where
  /-- An ambient query's execution phase and actual input. -/
  | ambient : Phase → spec.Domain → Event spec Request
  /-- An attempted signing request, observed before its signer executes. -/
  | signingAttempt : Request → Event spec Request

variable {ι : Type} {spec : OracleSpec ι} {Request PK SK Sig Reply C : Type}

/-- Additive cost accumulation over the shared free-oracle computation. -/
abbrev CostM (spec : OracleSpec ι) (C : Type) := AddWriterT C (OracleComp spec)
/-- The chronological raw reply log over the same additive cost computation. -/
abbrev LoggedCostM (spec : OracleSpec ι) (Request Reply C : Type) :=
  WriterT (QueryLog (Request →ₒ Reply)) (CostM spec C)

/-- Run a component while charging each ambient query at its actual input and phase. -/
@[expose] def costed [AddMonoid C] (policy : Event spec Request → C) (phase : Phase)
    {α : Type} (body : OracleComp spec α) : CostM spec C α :=
  simulateQ ((QueryImpl.id' spec).withAddCost (fun input => policy (.ambient phase input))) body

/-- A component without queries emits no cost. -/
@[simp] theorem costed_pure [AddMonoid C] (policy : Event spec Request → C) (phase : Phase)
    {α : Type} (value : α) : costed policy phase (pure value) = pure value := rfl

/-- Sequential component programs retain the writer's chronological cost addition. -/
theorem costed_bind [AddMonoid C] (policy : Event spec Request → C) (phase : Phase)
    {α β : Type} (body : OracleComp spec α) (next : α → OracleComp spec β) :
    costed policy phase (body >>= next) =
      (costed policy phase body >>= fun value => costed policy phase (next value)) :=
  simulateQ_bind _ body next

/-- A query is charged before the ambient handler can answer it from a cache. -/
theorem costed_query [AddMonoid C] (policy : Event spec Request → C) (phase : Phase)
    (input : spec.Domain) :
    costed policy phase (liftM (spec.query input)) = (do
      AddWriterT.addTell (policy (.ambient phase input))
      liftM (liftM (spec.query input) : OracleComp spec (spec.Range input))) := by
  rw [costed, simulateQ_spec_query, QueryImpl.withAddCost_apply]
  rfl

private def forgetCost [AddMonoid C] : CostM spec C →ᵐ OracleComp spec where
  toFun {_α} body := Prod.fst <$> body.run
  toFun_pure' := WriterT.fst_map_run_pure
  toFun_bind' := WriterT.fst_map_run_bind

/-- Removing instrumentation recovers the complete original free-oracle component. -/
theorem costed_erases [AddMonoid C] (policy : Event spec Request → C) (phase : Phase)
    {α : Type} (body : OracleComp spec α) :
    Prod.fst <$> (costed policy phase body).runAdd = body := by
  rw [AddWriterT.fst_map_runAdd]
  simpa only [costed, QueryImpl.withAddCost, simulateQ_id'] using
    QueryImpl.fst_map_run_withCost (QueryImpl.id' spec)
      (fun input => Multiplicative.ofAdd (policy (.ambient phase input))) body

private def forgetCostWithLog [AddMonoid C] :
    LoggedCostM spec Request Reply C →ᵐ
      WriterT (QueryLog (Request →ₒ Reply)) (OracleComp spec) where
  toFun {_α} body := WriterT.mk (forgetCost body.run)
  toFun_pure' value := by
    change forgetCost (pure (value, [])) = pure (value, [])
    exact (forgetCost (spec := spec) (C := C)).mmap_pure _
  toFun_bind' body next := by
    change forgetCost (body.run >>= fun z =>
      Prod.map id (z.2 ++ ·) <$> (next z.1).run) = _
    simp only [MonadHom.mmap_bind, MonadHom.mmap_map]
    rfl

private theorem forgetCost_costed [AddMonoid C] (policy : Event spec Request → C)
    (phase : Phase) {α : Type} (body : OracleComp spec α) :
    forgetCost (costed policy phase body) = body := by
  simpa only [forgetCost, AddWriterT.fst_map_runAdd] using costed_erases policy phase body

private theorem forgetCost_addTell [AddMonoid C] (cost : C) :
    forgetCost (AddWriterT.addTell cost : CostM spec C PUnit) = pure ⟨⟩ := by
  simp [forgetCost]

/-- Charge an attempt before executing its signer and logging the actual reply. -/
@[expose] def countedSigningOracle [AddMonoid C] (policy : Event spec Request → C)
    (view : SignatureAlg.SigningView (OracleComp spec) Request PK SK Sig Reply)
    (pk : PK) (sk : SK) : QueryImpl (Request →ₒ Reply) (LoggedCostM spec Request Reply C) :=
  QueryImpl.withLogging
    (QueryImpl.preInsert (spec := Request →ₒ Reply)
      (fun request => costed policy .signer (view.sign pk sk request))
      (fun request => AddWriterT.addTell (policy (.signingAttempt request))))

/-- Each attempt is charged before any internal signing queries, and its actual reply is logged. -/
theorem countedSigningOracle_run [AddMonoid C] (policy : Event spec Request → C)
    (view : SignatureAlg.SigningView (OracleComp spec) Request PK SK Sig Reply)
    (pk : PK) (sk : SK) (request : Request) :
    (countedSigningOracle policy view pk sk request).run = (do
      AddWriterT.addTell (policy (.signingAttempt request))
      let reply ← costed policy .signer (view.sign pk sk request)
      return (reply, [⟨request, reply⟩])) := by
  simp [countedSigningOracle, QueryImpl.withLogging_apply, monad_norm]

/-- Direct adversary queries have their own phase, while signing replies retain a raw log. -/
@[expose] def countedHandler [AddMonoid C] (policy : Event spec Request → C)
    (view : SignatureAlg.SigningView (OracleComp spec) Request PK SK Sig Reply)
    (pk : PK) (sk : SK) :
    QueryImpl (spec + (Request →ₒ Reply)) (LoggedCostM spec Request Reply C) :=
  QueryImpl.liftTarget (LoggedCostM spec Request Reply C)
    ((QueryImpl.id' spec).withAddCost (fun input => policy (.ambient .adversary input))) +
    countedSigningOracle policy view pk sk

/-- Retain the candidate, chronological raw reply log and accumulated client-phase cost. -/
@[expose] def countedPhase [AddMonoid C] (policy : Event spec Request → C)
    (view : SignatureAlg.SigningView (OracleComp spec) Request PK SK Sig Reply)
    (pk : PK) (sk : SK) {α : Type} (body : OracleComp (spec + (Request →ₒ Reply)) α) :
    CostM spec C (α × QueryLog (Request →ₒ Reply)) :=
  (simulateQ (countedHandler policy view pk sk) body).run

/-- Sequential client phases retain the chronological concatenation of all raw replies. -/
theorem countedPhase_bind [AddMonoid C] (policy : Event spec Request → C)
    (view : SignatureAlg.SigningView (OracleComp spec) Request PK SK Sig Reply)
    (pk : PK) (sk : SK) {α β : Type}
    (body : OracleComp (spec + (Request →ₒ Reply)) α)
    (next : α → OracleComp (spec + (Request →ₒ Reply)) β) :
    countedPhase policy view pk sk (body >>= next) = (do
      let (a, left) ← countedPhase policy view pk sk body
      let (b, right) ← countedPhase policy view pk sk (next a)
      return (b, left ++ right)) := by
  simp [countedPhase]

/-- A signing query keeps its raw response and charges its request and internal signer traffic. -/
theorem countedPhase_signingQuery [AddMonoid C] (policy : Event spec Request → C)
    (view : SignatureAlg.SigningView (OracleComp spec) Request PK SK Sig Reply)
    (pk : PK) (sk : SK) (request : Request) :
    countedPhase policy view pk sk
      (liftM ((spec + (Request →ₒ Reply)).query (.inr request))) = (do
        AddWriterT.addTell (policy (.signingAttempt request))
        let reply ← costed policy .signer (view.sign pk sk request)
        return (reply, [⟨request, reply⟩])) := by
  rw [countedPhase, simulateQ_spec_query]
  exact countedSigningOracle_run policy view pk sk request

private theorem forgetCostWithLog_handler [AddMonoid C]
    (policy : Event spec Request → C)
    (view : SignatureAlg.SigningView (OracleComp spec) Request PK SK Sig Reply)
    (pk : PK) (sk : SK) :
    (fun input => forgetCostWithLog (countedHandler policy view pk sk input)) =
      spec.passthrough + view.signingOracle pk sk := by
  funext input
  cases input with
  | inl input =>
    ext
    simp [countedHandler, forgetCostWithLog, forgetCost,
      QueryImpl.withAddCost_apply, WriterT.run_bind, Functor.map_map]
  | inr request =>
    ext
    simp [countedHandler, countedSigningOracle, forgetCostWithLog,
      QueryImpl.withLogging_apply, MonadHom.mmap_map, forgetCost_addTell,
      forgetCost_costed, signingOracle, Functor.map_map]

/-- Erasing cost preserves the candidate and the entire chronological raw reply log. -/
theorem countedPhase_erases [AddMonoid C] (policy : Event spec Request → C)
    (view : SignatureAlg.SigningView (OracleComp spec) Request PK SK Sig Reply)
    (pk : PK) (sk : SK) {α : Type} (body : OracleComp (spec + (Request →ₒ Reply)) α) :
    Prod.fst <$> (countedPhase policy view pk sk body).runAdd =
      view.runWithSigningOracle pk sk body := by
  rw [AddWriterT.fst_map_runAdd]
  change forgetCost (countedPhase policy view pk sk body) = _
  have h := PFunctor.FreeM.liftM_natural (countedHandler policy view pk sk)
    (forgetCostWithLog (spec := spec) (Request := Request) (Reply := Reply) (C := C)) body
  have natural : forgetCostWithLog (simulateQ (countedHandler policy view pk sk) body) =
      simulateQ (fun input => forgetCostWithLog (countedHandler policy view pk sk input)) body := h
  change (forgetCostWithLog (simulateQ (countedHandler policy view pk sk) body)).run = _
  rw [natural, forgetCostWithLog_handler]
  rfl

/-- The counted experiment's complete output, with the declared cost observation. -/
structure Observation (Request Sig Reply C : Type) extends Outcome Request Sig Reply where
  /-- The declared policy's accumulated additive cost. -/
  cost : C

/-- Erasure keeps the entire candidate, raw reply log and verification result. -/
@[expose] def erase (observation : Observation Request Sig Reply C) : Outcome Request Sig Reply :=
  observation.toOutcome

/-- One accumulated cost log covers keygen, the signing-enabled client and final verification. -/
@[expose] def countedExperiment [AddMonoid C] (policy : Event spec Request → C)
    (view : SignatureAlg.SigningView (OracleComp spec) Request PK SK Sig Reply)
    (adv : PK → OracleComp (spec + (Request →ₒ Reply)) (Request × Sig)) :
    OracleComp spec (Observation Request Sig Reply C) :=
  (fun result => { toOutcome := result.1, cost := result.2 }) <$> (do
    let (pk, sk) ← costed policy .keygen view.keygen
    let (forgery, rawLog) ← countedPhase policy view pk sk (adv pk)
    let verified ← costed policy .verification (view.verify pk forgery.1 forgery.2)
    return (⟨forgery, rawLog, verified⟩ : Outcome Request Sig Reply)).runAdd

/-- Cost erasure recovers the full uncounted experiment without any resource assumption. -/
theorem countedExperiment_erases [AddMonoid C] (policy : Event spec Request → C)
    (view : SignatureAlg.SigningView (OracleComp spec) Request PK SK Sig Reply)
    (adv : PK → OracleComp (spec + (Request →ₒ Reply)) (Request × Sig)) :
    erase <$> countedExperiment policy view adv = view.experiment adv := by
  simp only [countedExperiment, erase, AddWriterT.runAdd, Functor.map_map]
  change forgetCost (do
    let keys ← costed policy .keygen view.keygen
    let phase ← countedPhase policy view keys.1 keys.2 (adv keys.1)
    let verified ← costed policy .verification (view.verify keys.1 phase.1.1 phase.1.2)
    return (⟨phase.1, phase.2, verified⟩ : Outcome Request Sig Reply)) = _
  simp only [MonadHom.mmap_bind, MonadHom.mmap_pure, forgetCost_costed]
  have phaseErase (pk : PK) (sk : SK) :
      forgetCost (countedPhase policy view pk sk (adv pk)) =
        view.runWithSigningOracle pk sk (adv pk) := by
    simpa only [forgetCost, AddWriterT.fst_map_runAdd] using
      countedPhase_erases policy view pk sk (adv pk)
  simp only [phaseErase, experiment]

open scoped Classical in
/-- The total view recovers the original winning program for every declared cost policy. -/
theorem ofTotal_countedWinningProgram [AddMonoid C] (policy : Event spec Request → C)
    (alg : SignatureAlg (OracleComp spec) Request PK SK Sig)
    (adv : SignatureAlg.StrongUnforgeableAdversary alg) :
    (fun observation => decide (Wins (ofTotal alg).readback (erase observation))) <$>
      countedExperiment policy (ofTotal alg) adv.main =
        SignatureAlg.strongUnforgeableExperiment adv := by
  calc
    _ = (fun outcome => decide (Wins (ofTotal alg).readback outcome)) <$>
        (erase <$> countedExperiment policy (ofTotal alg) adv.main) := by
      rw [Functor.map_map]
    _ = _ := by
      rw [countedExperiment_erases]
      exact ofTotal_winningProgram alg adv

/-- Erasure preserves the full output and final state of any chosen ambient interpretation. -/
theorem countedExperiment_erases_run [AddMonoid C]
    (policy : Event spec Request → C)
    (view : SignatureAlg.SigningView (OracleComp spec) Request PK SK Sig Reply)
    (adv : PK → OracleComp (spec + (Request →ₒ Reply)) (Request × Sig))
    {m : Type → Type*} [Monad m] [LawfulMonad m] {Cache : Type}
    (handler : QueryImpl spec (StateT Cache m)) (initial : Cache) :
    Prod.map erase id <$> (simulateQ handler (countedExperiment policy view adv)).run initial =
      (simulateQ handler (view.experiment adv)).run initial := by
  change (fun pair => (erase pair.1, pair.2)) <$>
    (simulateQ handler (countedExperiment policy view adv)).run initial = _
  have equality := congrArg (fun program => (simulateQ handler program).run initial)
    (countedExperiment_erases policy view adv)
  simpa only [simulateQ_map, StateT.run_map] using equality

/-- Changing the cost policy changes no candidate, raw reply log or verifier behavior. -/
theorem countedExperiment_policy_erasure [AddMonoid C] {D : Type} [AddMonoid D]
    (left : Event spec Request → C) (right : Event spec Request → D)
    (view : SignatureAlg.SigningView (OracleComp spec) Request PK SK Sig Reply)
    (adv : PK → OracleComp (spec + (Request →ₒ Reply)) (Request × Sig)) :
    erase <$> countedExperiment left view adv = erase <$> countedExperiment right view adv :=
  (countedExperiment_erases left view adv).trans (countedExperiment_erases right view adv).symm

/-- Every continuation of the complete cost-erased result and final cache is preserved. -/
theorem countedExperiment_erases_run_bind [AddMonoid C]
    (policy : Event spec Request → C)
    (view : SignatureAlg.SigningView (OracleComp spec) Request PK SK Sig Reply)
    (adv : PK → OracleComp (spec + (Request →ₒ Reply)) (Request × Sig))
    {m : Type → Type*} [Monad m] [LawfulMonad m] {Cache β : Type}
    (handler : QueryImpl spec (StateT Cache m)) (initial : Cache)
    (continuation : Outcome Request Sig Reply × Cache → m β) :
    ((simulateQ handler (countedExperiment policy view adv)).run initial >>=
      fun result => continuation (erase result.1, result.2)) =
        ((simulateQ handler (view.experiment adv)).run initial >>= continuation) := by
  have stateEquality := countedExperiment_erases_run policy view adv handler initial
  change ((fun result => (erase result.1, result.2)) <$>
    (simulateQ handler (countedExperiment policy view adv)).run initial) = _ at stateEquality
  have equality := congrArg (fun result => result >>= continuation) stateEquality
  simpa only [bind_map_left] using equality

end SignatureAlg.SigningView
