/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

import HashSig.SLHDSA.SHAKE128s.Bridge.Encodings
import HashSig.SLHDSA.Security.Transport
import VCVio.OracleComp.QueryTracking.LoggingOracle.Core
import VCVio.OracleComp.QueryTracking.RandomOracle.Defer
import VCVio.OracleComp.SimSemantics.StateT.PreservesInv
import VCVio.OracleComp.SimSemantics.StateT.StateProjection
import VCVio.OracleComp.SimSemantics.StateT.StateSeparating
import VCVio.OracleComp.SimSemantics.WriterT.Core
import all HashSig.SLHDSA.SHAKE128s.Bridge.SharedExperiment.Pure
import all HashSig.SLHDSA.Security.CoverageRun
import all HashSig.SLHDSA.Security.NativeCounts
import all HashSig.SLHDSA.Security.NativeRelative
import all HashSig.SLHDSA.Security.SeedCoupling
import all VCVio.CryptoFoundations.SignatureAlg.CountedExperiment
import all VCVio.OracleComp.QueryTracking.RandomOracle.ClassIndexedTape
public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Price.WinningEvent
public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Coupling.Tapes
import all HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Coupling.KeySampler
import all HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Work.Counters
import all HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Coupling.Guarded
import all HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Transcript.DeferredLaw
import all HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Transcript.CacheOrigins
import all HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Transcript.KeyMarginal

/-!
# Nonaborting execution and support of the eager guarded cache

The output of a nonaborting guard retains the physical cache. A supported native terminal with a
conflict-free completion can be realized by the eager interpreter.
-/

public section

section

open OracleComp OracleSpec SignatureAlg
open SLHDSA SLHDSA.Security SLHDSA.SHAKE128s
open SLHDSA.SHAKE128s.Bridge.SharedExperiment
open SLHDSA.SHAKE128s.Bridge.SharedExperiment.Guarded
open MeasureTheory
open SLHDSA.Security.CanonicalGames SLHDSA.DigestTransport
open scoped ENNReal

namespace SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native
private theorem erase_full_signing_events
    {i Request Public Secret Signature Reply : Type} {spec : OracleSpec.{0, 0} i}
    (view : SigningView (OracleComp spec) Request Public Secret Signature Reply)
    (main : Public → OracleComp (spec + (Request →ₒ Reply)) (Request × Signature)) :
    simulateQ (SigningView.Events.handlerWithEvents (Request := Request) (QueryImpl.id' spec))
      (SigningView.Events.fullExperiment view main) = (do
        let keys ← view.keygen
        let (candidate, replies) ← view.runWithSigningOracle keys.1 keys.2 (main keys.1)
        let verified ← view.verify keys.1 candidate.1 candidate.2
        pure (keys, (⟨candidate, replies, verified⟩ : SigningView.Outcome Request Signature Reply)))
  := by
  let policy : SigningView.Event spec Request → Nat := fun _ => 0
  let erase := SigningView.forgetCost (spec := spec) (C := Nat)
  have handlers : (fun input => erase (SigningView.Events.costImpl policy input)) =
      SigningView.Events.handlerWithEvents (Request := Request) (QueryImpl.id' spec) := by
    funext input
    cases input <;>
      simp [erase, SigningView.forgetCost, SigningView.Events.costImpl,
        SigningView.Events.handlerWithEvents, Functor.map_map]
  have natural := PFunctor.FreeM.liftM_natural
    (SigningView.Events.costImpl policy) erase
    (SigningView.Events.fullExperiment view main)
  change erase (simulateQ (SigningView.Events.costImpl policy)
    (SigningView.Events.fullExperiment view main)) =
      simulateQ (fun input => erase (SigningView.Events.costImpl policy input))
        (SigningView.Events.fullExperiment view main) at natural
  rw [handlers, SigningView.Events.simulateQ_fullKeys] at natural
  rw [← natural]
  have client (pk : Public) (sk : Secret) :
      erase (SigningView.countedPhase policy view pk sk (main pk)) =
        view.runWithSigningOracle pk sk (main pk) := by
    simpa only [erase, SigningView.forgetCost, AddWriterT.fst_map_runAdd] using
      SigningView.countedPhase_erases policy view pk sk (main pk)
  have costedErases {β : Type} (phase : SigningView.Phase) (body : OracleComp spec β) :
      erase (SigningView.costed policy phase body) = body := by
    change SigningView.forgetCost (SigningView.costed policy phase body) = body
    exact SigningView.forgetCost_costed policy phase body
  simp only [SigningView.countedAfterKeygen, MonadHom.mmap_bind,
    costedErases, client, MonadHom.mmap_pure, bind_assoc, pure_bind]

/-- A reachable nonaborted guarded result retains the source output and physical cache. -/
private theorem mem_support_source_of_guard_not_aborted
    {ι α Cache C : Type} {spec : OracleSpec.{0, 0} ι}
    [AddMonoid C] [Preorder C] [CanonicallyOrderedAdd C] [DecidableLE C]
    (caps : C) (cost : spec.Domain → C)
    (handler : QueryImpl spec (StateT Cache ProbComp))
    (fallback : (input : spec.Domain) → spec.Range input)
    (program : OracleComp spec α) (initial : Cache)
    (result : α × (Cache × (C × Bool)))
    (hresult : result ∈ support
      ((simulateQ (QueryImpl.guardQueryBudget caps cost handler fallback) program).run
        (initial, (0, false))))
    (hnotAborted : result.2.2.2 = false) :
    (result.1, result.2.1) ∈ support ((simulateQ handler program).run initial) := by
  classical
  let erase : AddWriterT C (StateT Cache ProbComp) →ᵐ StateT Cache ProbComp := {
    toFun := fun {_} action => action.outputs
    toFun_pure' := by
      intro beta value
      exact WriterT.fst_map_run_pure value
    toFun_bind' := by
      intro beta gamma action next
      exact WriterT.fst_map_run_bind action next }
  have hstep (input : spec.Domain) : erase (handler.withAddCost cost input) =
      handler input := by
    funext cache
    simp [erase, AddWriterT.outputs, QueryImpl.withAddCost_apply,
      AddWriterT.run_addTell]
  have herase : erase (simulateQ (handler.withAddCost cost) program) =
      simulateQ handler program := by
    have natural := PFunctor.FreeM.liftM_natural (handler.withAddCost cost) erase program
    change erase (simulateQ (handler.withAddCost cost) program) =
      simulateQ (fun input => erase (handler.withAddCost cost input)) program at natural
    simpa only [hstep] using natural
  let event : (α × C) × Cache → Prop := fun out =>
    out.1.1 = result.1 ∧ out.2 = result.2.1
  have hpositive : 0 < Pr{let out ←
      ((simulateQ (QueryImpl.guardQueryBudget caps cost handler fallback) program).run
        (initial, (0, false)))}[
      event ((out.1, out.2.2.1), out.2.1) ∧ out.2.2.2 = false] := by
    exact (prEvent_pos_iff _ _).2 ⟨result, hresult, ⟨⟨rfl, rfl⟩, hnotAborted⟩⟩
  have same := QueryImpl.prEvent_guardQueryBudget_and_not_aborted_eq_source_and_caps
    caps cost handler fallback program (pure initial) event
  simp only [pure_bind] at same
  rw [same] at hpositive
  obtain ⟨counted, hcounted, hmatching, _⟩ := (prEvent_pos_iff _ _).1 hpositive
  have hproject : (counted.1.1, counted.2) ∈ support
      ((erase (simulateQ (handler.withAddCost cost) program)).run initial) := by
    have runErasure : (erase (simulateQ (handler.withAddCost cost) program)).run initial =
        (fun out : (α × C) × Cache => (out.1.1, out.2)) <$>
          ((simulateQ (handler.withAddCost cost) program).runAdd).run initial := by
      simp only [erase, AddWriterT.outputs, AddWriterT.runAdd, StateT.run_map,
        Functor.map_map]
      rfl
    rw [runErasure, support_map]
    exact ⟨counted, hcounted, rfl⟩
  rw [herase] at hproject
  simpa only [event, hmatching.1, hmatching.2] using hproject

/-! ## Phase-aware native preservation -/

private theorem deferred_guarded_front_run_eq
    (s : FIPS205.core.PkSeed) (adv : Game.Adversary FIPS205.Answer PK)
    (reserve : Bool) (caps : Nat × Nat)
    (fallback : (input : LabCommon.Domain) → LabCommon.Range input) :
  let G := slhGraph FIPS205.core s
  let graph := G.deferredImpl
  let native := eraseObsImpl (Ev := Ev) graph
  let observed := native.extendState (aux (spec := Lab) (metadataCost true s))
  let routed := QueryImpl.Stateful.link (routeLab s) observed
  let charge := Sum.elim (fun _ : A.Domain => (0, 0)) (policy reserve s)
  let reshape := fun result :
      (((Guarded.Full × (PUnit × Paid)) × Raw.QueryCache) × Meta) ×
        CoverageDeferred.D FIPS205.core =>
    (result.1.1.1.1, ((result.1.1.2, (result.2, result.1.2)), result.1.1.1.2.2))
  reshape <$> (simulateQ graph
      (deferredProgram s adv reserve caps fallback)).run ((∅, ∅), []) =
    (simulateQ (QueryImpl.guardQueryBudget caps charge routed fallback)
      (commonSource true s adv)).run
        ((∅, (((∅, ∅), []), (0, .keygen))), ((0, 0), false)) := by
  let _ : MonadLiftT (OracleComp LabCommon) (StateT PUnit.{1} (OracleComp LabCommon)) :=
    ⟨fun action => StateT.lift action⟩
  intro G graph native observed routed charge reshape
  have sameAux : aux (spec := Lab) (Cache := CoverageDeferred.D FIPS205.core)
      (metadataCost true s) =
      CoverageDeferred.phaseCostAux FIPS205.core (metadataCost true s) := by
    funext input before answer after metadata
    cases input with
    | inl native => rfl
    | inr event => cases event <;> rfl
  have observation :
      (simulateQ graph (deferredProgram s adv reserve caps fallback)).run ((∅, ∅), []) =
        (fun result : (((Guarded.Full × (PUnit × Paid)) × Raw.QueryCache) ×
            CoverageDeferred.S FIPS205.core) =>
          ((result.1, result.2.2), result.2.1)) <$>
          (simulateQ observed (guardedRoutedSource s adv reserve caps fallback)).run
            (((∅, ∅), []), (0, .keygen)) := by
    simpa only [observed, native, graph, G, sameAux] using
      SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native.observe_deferred_square s adv reserve caps
        fallback
  rw [observation]
  have guarded := QueryImpl.map_run_simulateQ_guardQueryBudget_free_eq caps charge
    routed fallback (commonSource true s adv)
    (∅, (((∅, ∅), []), (0, .keygen))) (0, 0) false
  simpa only [guardedRoutedSource, routed, QueryImpl.Stateful.simulateQ_link_run,
    QueryImpl.Stateful.Frame.linkReshape, QueryImpl.Stateful.Frame.prod,
    Functor.map_map, Function.comp_def, Prod.map, id_eq, reshape,
    PFunctor.Lens.State.fst_put, PFunctor.Lens.State.snd_put] using guarded

private theorem deferred_forget_metadata_run_eq
    (s : FIPS205.core.PkSeed)
    (program : OracleComp LabCommon Guarded.Full)
    (before : Raw.QueryCache × (CoverageDeferred.D FIPS205.core × Meta)) :
  let G := slhGraph FIPS205.core s
  let graph := G.deferredImpl
  let native := eraseObsImpl (Ev := Ev) graph
  let observed := native.extendState (aux (spec := Lab) (metadataCost true s))
  let routed := QueryImpl.Stateful.link (routeLab s) observed
  let plain := QueryImpl.Stateful.link (routeLab s) native
  Prod.map id (fun current : Raw.QueryCache ×
      (CoverageDeferred.D FIPS205.core × Meta) => (current.1, current.2.1)) <$>
      (simulateQ routed program).run before =
    (simulateQ plain program).run (before.1, before.2.1) := by
  intro G graph native observed routed plain
  apply map_run_simulateQ_eq_of_query_map_eq
  intro input current
  rcases current with ⟨raw, graphState, metadata⟩
  have projected := extendState_run_proj_eq native
    (aux (spec := Lab) (metadataCost true s)) ((routeLab s input).run raw)
    graphState metadata
  have routedProjection := congrArg
    (fun computation : ProbComp
        ((LabCommon.Range input × Raw.QueryCache) × CoverageDeferred.D FIPS205.core) =>
      (fun result => (result.1.1, (result.1.2, result.2))) <$> computation) projected
  have reshapeObserved :
      (QueryImpl.Stateful.Frame.prod Raw.QueryCache
        (CoverageDeferred.D FIPS205.core × Meta)).linkReshape
        (raw, (graphState, metadata)) =
        (fun result : (LabCommon.Range input × Raw.QueryCache) ×
            (CoverageDeferred.D FIPS205.core × Meta) =>
          (result.1.1, (result.1.2, result.2))) := by
    funext result
    rfl
  have reshapePlain :
      (QueryImpl.Stateful.Frame.prod Raw.QueryCache
        (CoverageDeferred.D FIPS205.core)).linkReshape (raw, graphState) =
        (fun result : (LabCommon.Range input × Raw.QueryCache) ×
            CoverageDeferred.D FIPS205.core =>
          (result.1.1, (result.1.2, result.2))) := by
    funext result
    rfl
  simpa only [routed, plain, observed, QueryImpl.Stateful.link_impl_apply_run,
    reshapeObserved, reshapePlain, Functor.map_map, Function.comp_def,
    Prod.map, id_eq] using routedProjection

/-- A conflict-free completion of a supported native terminal can occur with the same projected
output in the eager interpreter. -/
theorem filled_native_mem_support_eager
    (s : FIPS205.core.PkSeed) (adv : Game.Adversary FIPS205.Answer PK)
    (reserve : Bool) (caps : Nat × Nat)
    (fallback : (input : LabCommon.Domain) → LabCommon.Range input)
    (L R : Nat)
    (block : (List HashOutput × List HashOutput) × NativeTerminal)
    (hblock : block ∈ support
      (NoticingTape.blockRunOf (nativeRun s adv reserve caps fallback) L R))
    (filled : LabState FIPS205.core)
    (hfilled : filled ∈ support (RelabelState.endFill block.2.2.1.1.2.1))
    (hnoConflict : ¬(slhGraph FIPS205.core s).Conflict filled) :
    let project := fun result : NativeTerminal =>
      ((((result.1, (PUnit.unit, result.2.2)), result.2.1.1.1), result.2.1.1.2.2),
        result.2.1.1.2.1)
    let target := ((project block.2).1, filled)
    target ∈ support
      ((simulateQ (slhGraph FIPS205.core s).eagerImpl
        (deferredProgram s adv reserve caps fallback)).run (∅, ∅)) := by
  classical
  intro project target
  let G := slhGraph FIPS205.core s
  let program := deferredProgram s adv reserve caps fallback
  have deferred : project block.2 ∈ support
      ((simulateQ G.deferredImpl program).run ((∅, ∅), [])) := by
    have marginal := native_deferred_marginal s adv reserve caps fallback L R
    dsimp only at marginal
    rw [← support_eq_of_evalDistEq marginal, support_map]
    exact ⟨block, hblock, rfl⟩
  have completed : target ∈ support (do
      let out ← (simulateQ G.deferredImpl program).run ((∅, ∅), [])
      let state ← RelabelState.endFill out.2
      pure (out.1, state)) := by
    rw [mem_support_bind_iff]
    refine ⟨project block.2, deferred, ?_⟩
    rw [mem_support_bind_iff]
    exact ⟨filled, hfilled, (mem_support_pure_iff _ _).2 rfl⟩
  have positive : 0 < Pr{let out ← (do
      let out ← (simulateQ G.deferredImpl program).run ((∅, ∅), [])
      let state ← RelabelState.endFill out.2
      pure (out.1, state))}[out = target ∧ ¬G.Conflict out.2] :=
    (prEvent_pos_iff _ _).2 ⟨target, completed, rfl, hnoConflict⟩
  have same := G.prEvent_deferredImpl_endFill_eq_maskedImpl program (∅, ∅)
    (fun out => out = target ∧ ¬G.Conflict out.2)
  simp only [map_bind, bind_pure_comp, Functor.map_map] at positive
  rw [same] at positive
  have upper := G.dominatedUntilBad_maskedImpl.prEvent_simulateQ_run_map_and_not_bad_le
    (QueryImpl.PreservesInv.trivial _) G.preservesInv_conflict_maskedImpl
    program ((∅, ∅), ∅) trivial (fun out => out = target)
  have eagerPositive := lt_of_lt_of_le positive upper
  obtain ⟨out, hout, sameTarget⟩ := (prEvent_pos_iff _ _).1 eagerPositive
  simpa only [sameTarget] using hout

end SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native

end
