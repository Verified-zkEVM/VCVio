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

/-! # The guarded and deferred programs on a single signing transcript -/

public section
section
open OracleComp OracleSpec SignatureAlg
open SLHDSA SLHDSA.Security SLHDSA.SHAKE128s
namespace SLHDSA.SHAKE128s.Bridge.SharedExperiment.Guarded
/-- The framed shared view commutes with lifting the internal signing scheme. -/
theorem commonView_eq_rejectingEncoding (useLab : Bool) (s : FIPS205.core.PkSeed) :
    commonView useLab s =
      SigningView.rejectingEncoding
    ((if useLab then labScheme FIPS205.core (fun pk => pure pk.pkSeed) s
      else (deriveScheme FIPS205.core (fun pk => pure pk.pkSeed) s).map
        (labLiftHom FIPS205.core).toMonadHom).map
      (simulateQ' (fun input : Lab.Domain =>
        (liftM (A.query (.inl input)) : OracleComp A (Lab.Range input)))))
    (fun request : Message =>
      (External.encodePureMessage request.context request.message).toOption)
    (SLHDSA.encodeSignature FIPS205.params
      (SLHDSA.Concrete.shakeWireCodec FIPS205.params.params))
    (fun wire => (SLHDSA.decodeSignature FIPS205.params
      (SLHDSA.Concrete.shakeWireCodec FIPS205.params.params) wire).toOption) := by
  symm
  have fields (left right : SigningView (OracleComp A) Message PK PK
      (List Byte) (Option (List Byte)))
      (keygen : left.keygen = right.keygen)
      (sign : left.sign = right.sign)
      (verify : left.verify = right.verify)
      (readback : left.readback = right.readback) : left = right := by
    cases left
    cases right
    cases keygen
    cases sign
    cases verify
    cases readback
    rfl
  apply fields
  · simp only [commonView,
      partialView,
      SigningView.map_keygen, SigningView.rejectingEncoding_keygen,
      SignatureAlg.map_keygen]
  · funext pk sk request
    simp only [commonView,
      partialView,
      SigningView.map_sign, SigningView.rejectingEncoding_sign]
    cases frame : (External.encodePureMessage request.context request.message).toOption with
    | none => simp only [simulateQ_pure]
    | some message => simp only [simulateQ_map, SignatureAlg.map_sign]
  · funext pk request wire
    simp only [commonView,
      partialView,
      SigningView.map_verify, SigningView.rejectingEncoding_verify]
    cases frame : (External.encodePureMessage request.context request.message).toOption with
    | none => simp only [simulateQ_pure]
    | some message =>
      cases decoded : (SLHDSA.decodeSignature FIPS205.params
          (SLHDSA.Concrete.shakeWireCodec FIPS205.params.params) wire).toOption with
      | none => simp only [simulateQ_pure]
      | some signature => simp only [SignatureAlg.map_verify]
  · rfl

/-- Phase markers and their projection preserve any predicate on the lab query port. -/
theorem projected_lab_phase_queries
    (phase : SigningView.Phase) (P : Lab.Domain → Prop)
    {alpha : Type} (program : OracleComp Lab alpha)
    (hprogram : AllQueriesSatisfy program P) :
    AllQueriesSatisfy
      (simulateQ commonProjection
        (simulateQ (SigningView.Events.phaseImpl A Message phase)
          (simulateQ (fun input : Lab.Domain =>
            (liftM (A.query (.inl input)) : OracleComp A (Lab.Range input))) program)))
      (Sum.elim (Sum.elim P (fun _ => True)) (fun _ => True)) := by
  let Allowed : LabCommon.Domain → Prop := Sum.elim
    (Sum.elim P (fun _ => True)) (fun _ => True)
  let liftLab : QueryImpl Lab (OracleComp A) :=
    fun input => liftM (A.query (.inl input))
  let marking := SigningView.Events.phaseImpl A Message phase
  have step (input : Lab.Domain) (hi : P input) :
      AllQueriesSatisfy
        (simulateQ commonProjection
          (simulateQ marking (liftM (A.query (.inl input))))) Allowed := by
    rw [simulateQ_spec_query]
    simp only [marking, SigningView.Events.phaseImpl, QueryImpl.preInsert_apply,
      SigningView.Events.emit]
    change AllQueriesSatisfy
      (simulateQ commonProjection (do
        let _ ← (liftM ((SigningView.Events.Spec A Message).query
          (.inr (.ambient phase (.inl input)))) :
            OracleComp (SigningView.Events.Spec A Message) PUnit)
        (liftM ((SigningView.Events.Spec A Message).query (.inl (.inl input))) :
          OracleComp (SigningView.Events.Spec A Message) (Lab.Range input)))) Allowed
    simp only [simulateQ_bind, simulateQ_spec_query, commonProjection, QueryImpl.add]
    cases commonEvent (.ambient phase (.inl input)) with
    | none =>
      simp only [pure_bind]
      exact (allQueriesSatisfy_query_iff (spec := LabCommon) _ Allowed).2 hi
    | some event =>
      exact allQueriesSatisfy_bind
        ((allQueriesSatisfy_query_iff (spec := LabCommon) (.inr event) Allowed).2 trivial)
        (fun _ =>
          (allQueriesSatisfy_query_iff (spec := LabCommon) (.inl (.inl input)) Allowed).2 hi)
  have h := hprogram.simulateQ
    (impl := commonProjection ∘ₛ (marking ∘ₛ liftLab)) (fun input hi => by
      simpa only [QueryImpl.apply_compose, QueryImpl.simulateQ_compose, liftLab] using
        step input hi)
  simpa only [QueryImpl.simulateQ_compose, liftLab, marking, Allowed] using h

/-- The projected marked callback emits one actual attempt before the unmarked signing body. -/
theorem projected_callback_eq (s : FIPS205.core.PkSeed) (pk sk : PK)
    (request : Message) :
    simulateQ commonProjection
      ((SigningView.Events.viewWithEvents (commonView true s)).sign pk sk request) =
      (do
        let _ ← (liftM (LabCommon.query (.inr (.signingAttempt request))) :
          OracleComp LabCommon PUnit)
        simulateQ commonProjection
          (simulateQ (SigningView.Events.phaseImpl A Message .signer)
            ((commonView true s).sign pk sk request))) := by
  simp only [SigningView.Events.viewWithEvents, SigningView.Events.emit,
    simulateQ_bind, simulateQ_spec_query, commonProjection, commonEvent, QueryImpl.add]

end SLHDSA.SHAKE128s.Bridge.SharedExperiment.Guarded
end
section

open OracleComp OracleSpec SignatureAlg
open SLHDSA SLHDSA.Security SLHDSA.SHAKE128s
open SLHDSA.SHAKE128s.Bridge.SharedExperiment
open SLHDSA.SHAKE128s.Bridge.SharedExperiment.Guarded
namespace SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native
/-- The key and signing outcome together with the raw cache, deferred graph, role state
and budget guard returned by the same execution. -/
abbrev NativeTerminal := Guarded.Full ×
  (((Raw.QueryCache × CoverageDeferred.S FIPS205.core) × Coverage.RoleState FIPS205.core) × Paid)

/-- The native full-state endpoint, with guard BEFORE the whole stateful router. -/
@[expose] noncomputable def nativeRun
    (pkSeed : FIPS205.core.PkSeed) (adv : Game.Adversary FIPS205.Answer PK)
    (reserve : Bool) (caps : Nat × Nat)
    (fallbackCommon : (input : LabCommon.Domain) → LabCommon.Range input)
    (leftTape rightTape : List HashOutput) : ProbComp NativeTerminal := do
  let tapes : (j : Coverage.TapeClass) → List (Coverage.tapeClassRange FIPS205.core j)
    | .signer => leftTape.map Bridge.answerEquiv
    | .forger => rightTape.map Bridge.answerEquiv
    | .other => []
  let result ← (simulateQ (Coverage.roleRunImpl FIPS205.core)
    ((simulateQ
      (CoverageDeferred.relative FIPS205.core pkSeed (metadataCost true pkSeed))
      (guardedRoutedSource pkSeed adv reserve caps fallbackCommon)).run
        (((∅, ∅), []), (0, .keygen)))).run
          ((∅, tapes), (AnswerTape.ClassPos.init, ∅))
  return (result.1.1.1.1,
    (((result.1.1.2, result.1.2), result.2), result.1.1.1.2.2))

/-- Passive observation before the ordinary graph interpretation, using existing state effects. -/
@[expose] noncomputable def deferredProgram
    (pkSeed : FIPS205.core.PkSeed) (adv : Game.Adversary FIPS205.Answer PK)
    (reserve : Bool) (caps : Nat × Nat)
    (fallbackCommon : (input : LabCommon.Domain) → LabCommon.Range input) :=
  letI : MonadLiftT (OracleComp Lab) (StateT Meta (OracleComp Lab)) :=
    ⟨fun action => StateT.lift action⟩
  let observeLab : QueryImpl (Lab + O) (StateT Meta (OracleComp Lab)) :=
    QueryImpl.add
      ((QueryImpl.id' Lab).liftTarget (StateT Meta (OracleComp Lab)))
      (fun event => StateT.mk fun metadata =>
        pure (PUnit.unit, match event with
          | .ambient phase input =>
              (metadata.1 + metadataCost true pkSeed (.ambient phase input), phase)
          | .signingAttempt request =>
              (metadata.1 + metadataCost true pkSeed (.signingAttempt request), .signer)))
  (simulateQ observeLab (guardedRoutedSource pkSeed adv reserve caps fallbackCommon)).run
    (0, .keygen)

end SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native
end
