/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Coupling.Guarded
public import HashSig.SLHDSA.Security.ByteClash
public import HashSig.SLHDSA.Security.NativeCounts
public import HashSig.SLHDSA.Security.NativeRelative
public import HashSig.SLHDSA.SHAKE128s.Bridge.SharedExperiment.Joint
public import HashSig.SLHDSA.SHAKE128s.Bridge.Encodings
public import HashSig.SLHDSA.SHAKE128s.Proof.NoticingTape
import all HashSig.SLHDSA.Security.CoverageRun
import all HashSig.SLHDSA.Security.CoverageRoles
import all HashSig.SLHDSA.Security.NativeRelative
import all VCVio.OracleComp.QueryTracking.RandomOracle.ClassIndexedTape
import all VCVio.OracleComp.QueryTracking.QueryBound.Simulation
import all VCVio.OracleComp.Coercions.Add.Basic
import all VCVio.OracleComp.Coercions.SubSpec.Basic
import VCVio.OracleComp.SimSemantics.StateT.PreservesInv
import VCVio.OracleComp.SimSemantics.StateT.StateSeparating
import VCVio.OracleComp.SimSemantics.Append.Core
public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Transcript.Program
public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Encoding.EndFill
import all HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Transcript.CacheOrigins
public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Transcript.DeferredLaw

import all HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Transcript.KeygenOrigins

/-! # Public-key marginal of the guarded signing experiment -/

public section
section

open OracleComp OracleSpec SignatureAlg
open SLHDSA SLHDSA.Security SLHDSA.SHAKE128s
open SLHDSA.SHAKE128s.Bridge.SharedExperiment
open SLHDSA.SHAKE128s.Bridge.SharedExperiment.Guarded
open SLHDSA.Security.NativeProvenance
namespace SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native

/-- The actual cold key prefix samples its keys and private graph state without using role tapes. -/
theorem native_cold_keygen_role_factorization
    (s : FIPS205.core.PkSeed) (reserve : Bool) (caps : Nat × Nat)
    (fallback : (input : LabCommon.Domain) → LabCommon.Range input)
    (role : Coverage.RoleState FIPS205.core) :
    letI : MonadLiftT (OracleComp LabCommon) (StateT PUnit (OracleComp LabCommon)) :=
      ⟨fun action => StateT.lift action⟩
    let forwarder := (QueryImpl.id' LabCommon).liftTarget
      (StateT PUnit (OracleComp LabCommon))
    let guarded := (simulateQ (QueryImpl.guardQueryBudget caps
      (Sum.elim (fun _ : A.Domain => (0, 0)) (policy reserve s)) forwarder fallback)
      (simulateQ commonProjection
        (SigningView.Events.viewWithEvents (commonView true s)).keygen)).run
          (PUnit.unit, ((0, 0), false))
    let privateKeygen := (simulateQ (slhGraph FIPS205.core s).deferredImpl
      ((labScheme FIPS205.core (fun pk => pure pk.pkSeed) s).keygen)).run ((∅, ∅), [])
    (simulateQ (Coverage.roleRunImpl FIPS205.core)
      ((simulateQ (CoverageDeferred.relative FIPS205.core s (metadataCost true s))
        ((simulateQ (routeLab s) guarded).run ∅)).run
          (((∅, ∅), []), (0, .keygen)))).run role =
      (fun out => ((((out.1, (PUnit.unit, ((0, 0), false))), ∅),
        (out.2, (0, SigningView.Phase.keygen))), role)) <$> privateKeygen := by
  let _ : MonadLiftT (OracleComp.{0, 0, 0} LabCommon)
      (StateT PUnit.{1} (OracleComp.{0, 0, 0} LabCommon)) :=
    ⟨fun action => StateT.lift action⟩
  let program := (labScheme FIPS205.core (fun pk => pure pk.pkSeed) s).keygen
  let graph := (slhGraph FIPS205.core s).deferredImpl
  let relative := CoverageDeferred.relative FIPS205.core s (metadataCost true s)
  let roles := Coverage.roleRunImpl FIPS205.core
  let inclusion : QueryImpl Lab (OracleComp (Lab + O)) :=
    fun input => liftM ((Lab + O).query (.inl input))
  let inner : QueryImpl Lab
      (StateT (CoverageDeferred.S FIPS205.core)
        (OracleComp (Coverage.roleSpec FIPS205.core))) :=
    fun input => relative (.inl input)
  let combined := (roles.mapStateTBase inner).flattenStateT
  let passive : StateT (CoverageDeferred.D FIPS205.core) ProbComp →ᵐ
      StateT (CoverageDeferred.S FIPS205.core × Coverage.RoleState FIPS205.core) ProbComp := {
    toFun := fun {_} action => StateT.mk fun world =>
      (fun out => (out.1, ((out.2, world.1.2), world.2))) <$> action.run world.1.1
    toFun_pure' := by
      intro alpha answer
      funext world
      rcases world with ⟨⟨graphState, metadata⟩, roleState⟩
      change
        (fun out => (out.1, ((out.2, metadata), roleState))) <$>
            (pure (answer, graphState) : ProbComp (alpha × CoverageDeferred.D FIPS205.core)) =
          pure (answer, ((graphState, metadata), roleState))
      simp only [map_pure]
    toFun_bind' := by
      intro alpha beta action next
      funext world
      change
        (fun out => (out.1, ((out.2, world.1.2), world.2))) <$>
            (action.run world.1.1 >>= fun out => (next out.1).run out.2) =
          ((fun out => (out.1, ((out.2, world.1.2), world.2))) <$>
              action.run world.1.1) >>= fun out =>
            (fun last => (last.1, ((last.2, out.2.1.2), out.2.2))) <$>
              (next out.1).run out.2.1.1
      simp only [map_bind, bind_map_left] }
  have hprogram : AllQueriesSatisfy program
      (fun input => StructuralInput FIPS205.core input ∧ Keygen.NoPublicInput input) :=
    allQueriesSatisfy_bind Keygen.lab_keygen_restricted
      fun _ => allQueriesSatisfy_pure _ _
  have hstep (input : Lab.Domain)
      (hi : StructuralInput FIPS205.core input ∧ Keygen.NoPublicInput input) :
      combined input = passive (graph input) := by
    apply StateT.ext
    rintro ⟨state, roleState⟩
    change ((roles.mapStateTBase inner).flattenStateT input).run (state, roleState) =
      (fun out => (out.1, ((out.2, state.2), roleState))) <$> (graph input).run state.1
    rw [QueryImpl.flattenStateT_mapStateTBase_apply_run]
    dsimp only [inner, relative]
    rw [Keygen.relative_private_run s input hi state]
    simp only [roles, graph, simulateQ_map, StateT.run_map, Coverage.roleRunImpl_liftComp_run,
      Functor.map_map]
  have hagree : simulateQ combined program =
      simulateQ (fun input => passive (graph input)) program :=
    OracleComp.AllQueriesSatisfy.simulateQ_eq_of_query_eq
      (spec := Lab)
      (m := StateT (CoverageDeferred.S FIPS205.core × Coverage.RoleState FIPS205.core)
        ProbComp)
      (program := program)
      (P := fun input => StructuralInput FIPS205.core input ∧
        Keygen.NoPublicInput input)
      (left := combined) (right := fun input => passive (graph input)) hprogram hstep
  have hnatural :
      passive (simulateQ graph program) =
        simulateQ (fun input => passive (graph input)) program := by
    change passive (PFunctor.FreeM.liftM graph program) =
      PFunctor.FreeM.liftM (fun input => passive (graph input)) program
    exact PFunctor.FreeM.liftM_natural graph passive program
  have hrun :
      (simulateQ roles ((simulateQ inner program).run
        (((∅, ∅), []), (0, SigningView.Phase.keygen)))).run role =
      (fun out => ((out.1, (out.2, (0, SigningView.Phase.keygen))), role)) <$>
        (simulateQ graph program).run ((∅, ∅), []) := by
    rw [simulateQ_mapStateTBase_run_eq_map_flattenStateT]
    rw [hagree, ← hnatural]
    change
      (fun out : (PK × PK) ×
          (CoverageDeferred.S FIPS205.core × Coverage.RoleState FIPS205.core) =>
        ((out.1, out.2.1), out.2.2)) <$>
          ((fun out => (out.1, ((out.2, (0, SigningView.Phase.keygen)), role))) <$>
            (simulateQ graph program).run ((∅, ∅), [])) =
        (fun out => ((out.1, (out.2, (0, SigningView.Phase.keygen))), role)) <$>
          (simulateQ graph program).run ((∅, ∅), [])
    simp only [Functor.map_map]
  have hemb : simulateQ relative (simulateQ inclusion program) =
      simulateQ inner program := by
    apply QueryImpl.simulateQ_simulateQ_eq_of_apply
    intro input
    simp only [inclusion, simulateQ_spec_query, inner]
  dsimp only
  rw [Keygen.guarded_routed_keygen_eq s reserve caps fallback]
  simp only [simulateQ_map, StateT.run_map]
  rw [hemb, hrun]
  simp only [Functor.map_map]
  rfl

end SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native

end

section
open OracleComp OracleSpec SignatureAlg
open SLHDSA SLHDSA.Security SLHDSA.SHAKE128s
open SLHDSA.SHAKE128s.Bridge.SharedExperiment.Guarded
namespace SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native
/-! ## The whole-run initial public-key law -/

/-- The actual native run conditions its suffix on the tape-independent private key prefix. -/
private theorem nativeRun_eq_private_keygen_bind
    (s : FIPS205.core.PkSeed) (adv : Game.Adversary FIPS205.Answer PK)
    (reserve : Bool) (caps : Nat × Nat)
    (fallback : (input : LabCommon.Domain) → LabCommon.Range input)
    (leftTape rightTape : List HashOutput) :
    nativeRun s adv reserve caps fallback leftTape rightTape = (do
      let keygenResult ← (simulateQ (slhGraph FIPS205.core s).deferredImpl
        ((labScheme FIPS205.core (fun pk => pure pk.pkSeed) s).keygen)).run ((∅, ∅), [])
      let key := keygenResult.1.1
      let secret := keygenResult.1.2
      let marked := SigningView.Events.viewWithEvents (commonView true s)
      let suffix := simulateQ commonProjection (do
        let (forgery, rawLog) ← marked.runWithSigningOracle key secret
          (SigningView.Events.mainWithEvents (commonMain adv) key)
        let verified ← marked.verify key forgery.1 forgery.2
        return ((key, secret), (⟨forgery, rawLog, verified⟩ : RawOutcome)))
      let _ : MonadLiftT (OracleComp LabCommon) (StateT PUnit (OracleComp LabCommon)) :=
        ⟨fun action => StateT.lift action⟩
      let forwarder := (QueryImpl.id' LabCommon).liftTarget
        (StateT PUnit (OracleComp LabCommon))
      let guarded := (simulateQ (QueryImpl.guardQueryBudget caps
        (Sum.elim (fun _ : A.Domain => (0, 0)) (policy reserve s)) forwarder fallback)
        suffix).run (PUnit.unit, ((0, 0), false))
      let tapes : (which : Coverage.TapeClass) →
          List (Coverage.tapeClassRange FIPS205.core which) := fun
        | .signer => leftTape.map Bridge.answerEquiv
        | .forger => rightTape.map Bridge.answerEquiv
        | .other => []
      let result ← (simulateQ (Coverage.roleRunImpl FIPS205.core)
        ((simulateQ (CoverageDeferred.relative FIPS205.core s (metadataCost true s))
          ((simulateQ (routeLab s) guarded).run ∅)).run
            (keygenResult.2, (0, SigningView.Phase.keygen)))).run
              ((∅, tapes), (AnswerTape.ClassPos.init, ∅))
      return (result.1.1.1.1,
        (((result.1.1.2, result.1.2), result.2), result.1.1.1.2.2))) := by
  let _ : MonadLiftT (OracleComp.{0, 0, 0} LabCommon)
      (StateT PUnit.{1} (OracleComp.{0, 0, 0} LabCommon)) :=
    ⟨fun action => StateT.lift action⟩
  let tapes : (which : Coverage.TapeClass) →
      List (Coverage.tapeClassRange FIPS205.core which)
    | .signer => leftTape.map Bridge.answerEquiv
    | .forger => rightTape.map Bridge.answerEquiv
    | .other => []
  let role : Coverage.RoleState FIPS205.core :=
    ((∅, tapes), (AnswerTape.ClassPos.init, ∅))
  let relative := CoverageDeferred.relative FIPS205.core s (metadataCost true s)
  let roles := Coverage.roleRunImpl FIPS205.core
  let native := QueryImpl.Stateful.link relative roles
  let routed := QueryImpl.Stateful.link (routeLab s) native
  let charge := Sum.elim (fun _ : A.Domain => (0, 0)) (policy reserve s)
  let handler := QueryImpl.guardQueryBudget caps charge routed fallback
  let initial : (Raw.QueryCache × (CoverageDeferred.S FIPS205.core ×
      Coverage.RoleState FIPS205.core)) × Paid :=
    ((∅, ((((∅, ∅), []), (0, .keygen)), role)), ((0, 0), false))
  let reshape {alpha : Type} := fun z :
      (((alpha × (PUnit × Paid)) × Raw.QueryCache) ×
        CoverageDeferred.S FIPS205.core) × Coverage.RoleState FIPS205.core =>
    (z.1.1.1.1, ((z.1.1.2, (z.1.2, z.2)), z.1.1.1.2.2))
  let project := fun z : Guarded.Full ×
      ((Raw.QueryCache × (CoverageDeferred.S FIPS205.core ×
        Coverage.RoleState FIPS205.core)) × Paid) =>
    (z.1, (((z.2.1.1, z.2.1.2.1), z.2.1.2.2), z.2.2))
  have front {alpha : Type} (program : OracleComp LabCommon alpha)
      (before : (Raw.QueryCache × (CoverageDeferred.S FIPS205.core ×
        Coverage.RoleState FIPS205.core)) × Paid) :
      reshape <$> (simulateQ roles
        ((simulateQ relative
          ((simulateQ (routeLab s)
            ((simulateQ (QueryImpl.guardQueryBudget caps charge
              ((QueryImpl.id' LabCommon).liftTarget (StateT PUnit (OracleComp LabCommon)))
              fallback) program).run (PUnit.unit, before.2))).run before.1.1)).run
                before.1.2.1)).run before.1.2.2 =
      (simulateQ handler program).run before := by
    simpa only [reshape, handler, routed, native, relative, roles, charge, Prod.mk.eta] using
      Provenance.native_guarded_frontend s reserve caps fallback program
        before.1.1 before.1.2.1 before.1.2.2 before.2
  let marked := SigningView.Events.viewWithEvents (commonView true s)
  let suffix := fun keys : PK × PK => simulateQ commonProjection (do
    let (forgery, rawLog) ← marked.runWithSigningOracle keys.1 keys.2
      (SigningView.Events.mainWithEvents (commonMain adv) keys.1)
    let verified ← marked.verify keys.1 forgery.1 forgery.2
    return (keys, (⟨forgery, rawLog, verified⟩ : RawOutcome)))
  let graphKeygen := (simulateQ (slhGraph FIPS205.core s).deferredImpl
    ((labScheme FIPS205.core (fun pk => pure pk.pkSeed) s).keygen)).run ((∅, ∅), [])
  have hsource : commonSource true s adv =
      (simulateQ commonProjection marked.keygen >>= suffix) := by
    simp only [commonSource, SigningView.Events.fullExperiment, suffix, marked,
      simulateQ_bind, simulateQ_pure]
  have hfull : nativeRun s adv reserve caps fallback leftTape rightTape =
      project <$> (simulateQ handler (commonSource true s adv)).run initial := by
    rw [← front (commonSource true s adv) initial]
    simp only [nativeRun, guardedRoutedSource, bind_pure_comp, Functor.map_map,
      project, reshape, initial, relative, roles, role, tapes, charge]
    rfl
  have hprefix :
      (simulateQ handler (simulateQ commonProjection marked.keygen)).run initial =
      (fun keygenResult => (keygenResult.1,
        ((∅, ((keygenResult.2, (0, SigningView.Phase.keygen)), role)), ((0, 0), false)))) <$>
          graphKeygen := by
    rw [← front (simulateQ commonProjection marked.keygen) initial]
    have h := congrArg (fun computation => reshape <$> computation)
      (native_cold_keygen_role_factorization s reserve caps fallback role)
    simpa only [Functor.map_map, reshape, initial, graphKeygen, marked,
      relative, roles, charge] using h
  rw [hfull, hsource, simulateQ_bind, StateT.run_bind, hprefix, bind_map_left, map_bind]
  apply bind_congr
  intro keygenResult
  rw [← front (suffix keygenResult.1)
    ((∅, ((keygenResult.2, (0, SigningView.Phase.keygen)), role)), ((0, 0), false))]
  simp only [Functor.map_map, project, reshape, suffix, marked, relative, roles,
    role, tapes, charge, bind_pure_comp]

/-- The initial public-key marginal of the complete native run is its private key-generation law.
The full suffix may depend on that key and the tapes; it is not assumed independent. -/
theorem native_initial_public_key_marginal
    (s : FIPS205.core.PkSeed) (adv : Game.Adversary FIPS205.Answer PK)
    (reserve : Bool) (caps : Nat × Nat)
    (fallback : (input : LabCommon.Domain) → LabCommon.Range input)
    (leftTape rightTape : List HashOutput) :
    (fun terminal : NativeTerminal => terminal.1.1.1) <$>
        nativeRun s adv reserve caps fallback leftTape rightTape =ᵈ
      (fun generated => generated.1.1) <$>
        (simulateQ (slhGraph FIPS205.core s).deferredImpl
          ((labScheme FIPS205.core (fun pk => pure pk.pkSeed) s).keygen)).run ((∅, ∅), []) := by
  let graphKeygen := (simulateQ (slhGraph FIPS205.core s).deferredImpl
    ((labScheme FIPS205.core (fun pk => pure pk.pkSeed) s).keygen)).run ((∅, ∅), [])
  change (fun terminal : NativeTerminal => terminal.1.1.1) <$>
    nativeRun s adv reserve caps fallback leftTape rightTape =ᵈ
      (fun generated => generated.1.1) <$> graphKeygen
  rw [nativeRun_eq_private_keygen_bind, map_bind]
  rw [map_eq_bind_pure_comp]
  change _ =ᵈ graphKeygen >>= fun generated => pure generated.1.1
  apply EvalDistEq.bind_right
  intro generated
  let marked := SigningView.Events.viewWithEvents (commonView true s)
  let body := simulateQ commonProjection (do
    let (forgery, rawLog) ← marked.runWithSigningOracle generated.1.1 generated.1.2
      (SigningView.Events.mainWithEvents (commonMain adv) generated.1.1)
    let verified ← marked.verify generated.1.1 forgery.1 forgery.2
    pure (⟨forgery, rawLog, verified⟩ : RawOutcome))
  have sourceMap : simulateQ commonProjection (do
      let (forgery, rawLog) ← marked.runWithSigningOracle generated.1.1 generated.1.2
        (SigningView.Events.mainWithEvents (commonMain adv) generated.1.1)
      let verified ← marked.verify generated.1.1 forgery.1 forgery.2
      pure ((generated.1.1, generated.1.2),
        (⟨forgery, rawLog, verified⟩ : RawOutcome))) =
      (fun outcome => ((generated.1.1, generated.1.2), outcome)) <$> body := by
    simp only [body, simulateQ_bind, simulateQ_pure, map_bind, map_pure]
  dsimp only
  rw [sourceMap]
  simp only [simulateQ_map, StateT.run_map, Functor.map_map, bind_pure_comp]
  apply EvalDistEq.map_const

end SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native

end
