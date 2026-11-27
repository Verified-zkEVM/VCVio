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

/-! # Private cache origins during SHAKE-128s key generation -/

public section
section

open OracleComp OracleSpec SignatureAlg
open SLHDSA SLHDSA.Security SLHDSA.SHAKE128s
open SLHDSA.SHAKE128s.Bridge.SharedExperiment
open SLHDSA.SHAKE128s.Bridge.SharedExperiment.Guarded
open SLHDSA.Security.NativeProvenance
namespace SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native
namespace Keygen

private def NoPublicInput : Lab.Domain → Prop
  | .inl (.inl _) => False
  | _ => True

/-- The actual root program never invokes its uniform or public-hash ports. -/
private theorem lab_keygen_no_public :
    AllQueriesSatisfy (labKeygen FIPS205.core) NoPublicInput := by
  refine labKeygen_pred FIPS205.core
    (Q := fun oa => AllQueriesSatisfy oa NoPublicInput)
    (fun _ => allQueriesSatisfy_pure _ _)
    (fun _ _ => allQueriesSatisfy_bind) ?_ ?_
  · intro c
    exact (allQueriesSatisfy_query_iff _ _).2 trivial
  · rintro (x | k) <;> exact (allQueriesSatisfy_query_iff _ _).2 trivial

/-- Both restrictions hold of the source; neither is a caller premise. -/
private theorem lab_keygen_restricted :
    AllQueriesSatisfy (labKeygen FIPS205.core)
      (fun input => StructuralInput FIPS205.core input ∧ NoPublicInput input) :=
  (lab_keygen_structural FIPS205.core).and lab_keygen_no_public

private def PrivateState (state : CoverageDeferred.D FIPS205.core) : Prop :=
  state.1.1 = ∅ ∧ ∀ cell,
    (state.1.2 cell).isSome ∨ cell ∈ state.2 → StructuralCell FIPS205.core cell

private theorem privateState_cold :
    PrivateState (((∅, ∅), []) : CoverageDeferred.D FIPS205.core) := by
  refine ⟨rfl, ?_⟩
  intro cell h
  simp at h

/-- A draw changes only the supplied cell and leaves the public cache untouched. -/
private theorem draw_privateState
    (state : CoverageDeferred.D FIPS205.core)
    (cell : DeriveQuery FIPS205.core ⊕ NodeKey FIPS205.core)
    (hc : StructuralCell FIPS205.core cell) (hs : PrivateState state)
    {out : FIPS205.core.Y × LabState FIPS205.core}
    (hout : out ∈ support ((RelabelState.drawCell cell).run state.1)) :
    PrivateState (out.2, state.2) := by
  have hpublic : out.2.1 = state.1.1 := by
    rw [RelabelState.drawCell_run, support_map] at hout
    obtain ⟨w, _, rfl⟩ := hout
    rfl
  refine ⟨hpublic.trans hs.1, ?_⟩
  intro other hother
  rcases hother with hdrawn | hpending
  · by_cases heq : other = cell
    · exact heq.symm ▸ hc
    · have hunchanged := RelabelState.cell_eq_of_mem_support_drawCell hout heq
      exact hs.2 other (.inl (hunchanged ▸ hdrawn))
  · exact hs.2 other (.inr hpending)

/-- The existing deferred handler preserves honest drawn and pending cells. -/
private theorem deferred_private_step (s : FIPS205.core.PkSeed)
    (input : Lab.Domain)
    (hi : StructuralInput FIPS205.core input ∧ NoPublicInput input)
    (state : CoverageDeferred.D FIPS205.core) (hs : PrivateState state)
    {out : Lab.Range input × CoverageDeferred.D FIPS205.core}
    (hout : out ∈ support (((slhGraph FIPS205.core s).deferredImpl input).run state)) :
    PrivateState out.2 := by
  rcases input with ((pubInput | derive) | (touch | node))
  · exact hi.2.elim
  · rw [CanonicalGraph.deferredImpl_run_inl, support_map] at hout
    obtain ⟨w, hw, rfl⟩ := hout
    rw [CanonicalGraph.relabelImpl_apply_inr] at hw
    exact draw_privateState state (.inl derive) hi.1 hs hw
  · rw [CanonicalGraph.deferredImpl_run_touch, support_pure,
      Set.mem_singleton_iff] at hout
    subst out
    refine ⟨hs.1, ?_⟩
    intro cell hc
    rcases hc with hdrawn | hpending
    · exact hs.2 cell (.inl hdrawn)
    · rcases List.mem_append.mp hpending with hold | hnew
      · exact hs.2 cell (.inr hold)
      · have heq : cell = touch := List.mem_singleton.mp hnew
        exact heq.symm ▸ hi.1
  · rw [CanonicalGraph.deferredImpl_run_read, support_map] at hout
    obtain ⟨w, hw, rfl⟩ := hout
    exact draw_privateState state (.inr node) trivial hs hw

/-- The selected native branches are absent because the query is private and structural. -/
private theorem relative_private_run (s : FIPS205.core.PkSeed)
    (input : Lab.Domain)
    (hi : StructuralInput FIPS205.core input ∧ NoPublicInput input)
    (state : CoverageDeferred.S FIPS205.core) :
    (CoverageDeferred.relative FIPS205.core s (metadataCost true s) (.inl input)).run state =
      (fun out => (out.1, (out.2, state.2))) <$>
        liftComp (((slhGraph FIPS205.core s).deferredImpl input).run state.1)
          (Coverage.roleSpec FIPS205.core) := by
  rcases input with ((pubInput | (secret | nonce)) | (touch | node))
  · exact hi.2.elim
  · simp only [CoverageDeferred.relative, StateT.run_mk, map_eq_bind_pure_comp,
      Function.comp_def]
  · exact hi.1.elim
  · simp only [CoverageDeferred.relative, StateT.run_mk, map_eq_bind_pure_comp,
      Function.comp_def]
  · simp only [CoverageDeferred.relative, StateT.run_mk, map_eq_bind_pure_comp,
      Function.comp_def]

/-- Role execution can shrink support but cannot introduce a new deferred-state outcome. -/
private theorem role_relative_private_step (s : FIPS205.core.PkSeed)
    (input : Lab.Domain)
    (hi : StructuralInput FIPS205.core input ∧ NoPublicInput input)
    (state : CoverageDeferred.S FIPS205.core) (hs : PrivateState state.1)
    (role : Coverage.RoleState FIPS205.core)
    {out : (Lab.Range input × CoverageDeferred.S FIPS205.core) ×
      Coverage.RoleState FIPS205.core}
    (hout : out ∈ support ((simulateQ (Coverage.roleRunImpl FIPS205.core)
      ((CoverageDeferred.relative FIPS205.core s (metadataCost true s)
        (.inl input)).run state)).run role)) :
    PrivateState out.1.2.1 ∧ out.1.2.2 = state.2 := by
  have houtput : out.1 ∈ support ((simulateQ (Coverage.roleRunImpl FIPS205.core)
      ((CoverageDeferred.relative FIPS205.core s (metadataCost true s)
        (.inl input)).run state)).run' role) := by
    rw [StateT.run'_eq, support_map]
    exact ⟨out, hout, rfl⟩
  have hsource := support_simulateQ_run'_subset (Coverage.roleRunImpl FIPS205.core)
    ((CoverageDeferred.relative FIPS205.core s (metadataCost true s)
      (.inl input)).run state) role houtput
  rw [relative_private_run s input hi state, support_map] at hsource
  obtain ⟨z, hz, heq⟩ := hsource
  have hz' := mem_support_of_mem_support_liftComp (Coverage.roleSpec FIPS205.core) _ _ hz
  rw [← heq]
  exact ⟨deferred_private_step s input hi state.1 hs hz', rfl⟩

/-- The actual lab key-generation program preserves the cold invariant under the native roles.
The entire resulting role state is retained in the supported outcome. -/
private theorem native_lab_keygen_private (s : FIPS205.core.PkSeed)
    (optRand : PK → ProbComp FIPS205.core.Y)
    (role : Coverage.RoleState FIPS205.core)
    {result : ((PK × PK) × CoverageDeferred.S FIPS205.core) ×
      Coverage.RoleState FIPS205.core}
    (hr : result ∈ support ((simulateQ (Coverage.roleRunImpl FIPS205.core)
      ((simulateQ (CoverageDeferred.relative FIPS205.core s (metadataCost true s))
        (simulateQ (fun input : Lab.Domain =>
          (liftM ((Lab + O).query (.inl input)) :
            OracleComp (Lab + O) (Lab.Range input)))
          ((labScheme FIPS205.core optRand s).keygen))).run
            (((∅, ∅), []), (0, .keygen)))).run role)) :
    result.1.1.2 = result.1.1.1 ∧ result.1.1.1.pkSeed = s ∧
      PrivateState result.1.2.1 ∧ result.1.2.2 = (0, .keygen) := by
  have hprogram : AllQueriesSatisfy (labScheme FIPS205.core optRand s).keygen
      (fun input => StructuralInput FIPS205.core input ∧ NoPublicInput input) :=
    allQueriesSatisfy_bind lab_keygen_restricted fun _ => allQueriesSatisfy_pure _ _
  generalize eqn : (labScheme FIPS205.core optRand s).keygen = program at hr hprogram
  let inner : QueryImpl Lab
      (StateT (CoverageDeferred.S FIPS205.core)
        (OracleComp (Coverage.roleSpec FIPS205.core))) :=
    fun input => CoverageDeferred.relative FIPS205.core s (metadataCost true s) (.inl input)
  let handler := ((Coverage.roleRunImpl FIPS205.core).mapStateTBase inner).flattenStateT
  let initial : CoverageDeferred.S FIPS205.core × Coverage.RoleState FIPS205.core :=
    ((((∅, ∅), []), (0, SigningView.Phase.keygen)), role)
  let inclusion : QueryImpl Lab (OracleComp (Lab + O)) :=
    fun input => liftM ((Lab + O).query (.inl input))
  have hemb : simulateQ (CoverageDeferred.relative FIPS205.core s (metadataCost true s))
      (simulateQ inclusion program) = simulateQ inner program := by
    apply QueryImpl.simulateQ_simulateQ_eq_of_apply
    intro input
    simp only [inclusion, simulateQ_spec_query, inner]
  rw [hemb, simulateQ_mapStateTBase_run_eq_map_flattenStateT, support_map] at hr
  obtain ⟨out, hout, heq⟩ := hr
  have hstate : PrivateState out.2.1.1 ∧ out.2.1.2 = (0, .keygen) := by
    refine hprogram.holds_of_mem_support_run_simulateQ
      (fun state => PrivateState state.1.1 ∧ state.1.2 = (0, .keygen)) ?_
      ⟨privateState_cold, rfl⟩ hout
    intro input hi before hb after ha
    rw [QueryImpl.flattenStateT_mapStateTBase_apply_run, support_map] at ha
    obtain ⟨u, hu, rfl⟩ := ha
    have h := role_relative_private_step s input hi before.1 hb.1 before.2 hu
    exact ⟨h.1, h.2.trans hb.2⟩
  have houtput : out.1 ∈ support ((simulateQ handler program).run' initial) := by
    rw [StateT.run'_eq, support_map]
    exact ⟨out, hout, rfl⟩
  have hkeys := support_simulateQ_run'_subset handler program initial houtput
  rw [← eqn] at hkeys
  change out.1 ∈ support (do
    let root ← labKeygen FIPS205.core
    pure ((⟨s, root⟩, ⟨s, root⟩) : PK × PK)) at hkeys
  rw [mem_support_bind_iff] at hkeys
  obtain ⟨root, _, hreturn⟩ := hkeys
  rw [support_pure, Set.mem_singleton_iff] at hreturn
  rw [← heq]
  refine ⟨?_, ?_, hstate.1, hstate.2⟩
  · rw [hreturn]
  · rw [hreturn]

/-- Key generation has no projected event at a private input. -/
private theorem projected_private_query
    (input : Lab.Domain) (hi : NoPublicInput input) :
    simulateQ commonProjection
      (simulateQ (SigningView.Events.phaseImpl A Message .keygen)
        (liftM (A.query (.inl input)))) =
      (liftM (LabCommon.query (.inl (.inl input))) :
        OracleComp LabCommon (Lab.Range input)) := by
  rcases input with ((pubInput | derive) | label)
  · exact hi.elim
  · simp [SigningView.Events.phaseImpl, QueryImpl.preInsert,
      SigningView.Events.emit, commonProjection, commonEvent, QueryImpl.add]
  · simp [SigningView.Events.phaseImpl, QueryImpl.preInsert,
      SigningView.Events.emit, commonProjection, commonEvent, QueryImpl.add]

/-- The original free guard and raw router preserve their cold state throughout key generation.
All capacities and fallback functions are quantified; every reachable guard cost is zero. -/
private theorem guarded_routed_keygen_eq (s : FIPS205.core.PkSeed)
    (reserve : Bool) (caps : Nat × Nat)
    (fallback : (input : LabCommon.Domain) → LabCommon.Range input) :
    letI : MonadLiftT (OracleComp LabCommon) (StateT PUnit (OracleComp LabCommon)) :=
      ⟨fun action => StateT.lift action⟩
    let forwarder := (QueryImpl.id' LabCommon).liftTarget
      (StateT PUnit (OracleComp LabCommon))
    let guarded := (simulateQ (QueryImpl.guardQueryBudget caps
      (Sum.elim (fun _ : A.Domain => (0, 0)) (policy reserve s)) forwarder fallback)
      (simulateQ commonProjection
        (SigningView.Events.viewWithEvents (commonView true s)).keygen)).run
          (PUnit.unit, ((0, 0), false))
    (simulateQ (routeLab s) guarded).run ∅ =
      (fun keys : PK × PK => ((keys, (PUnit.unit, ((0, 0), false))), ∅)) <$>
        simulateQ (fun input : Lab.Domain =>
          (liftM ((Lab + O).query (.inl input)) :
            OracleComp (Lab + O) (Lab.Range input)))
          ((labScheme FIPS205.core (fun pk => pure pk.pkSeed) s).keygen) := by
  let _ : MonadLiftT (OracleComp LabCommon) (StateT PUnit (OracleComp LabCommon)) :=
    ⟨fun action => StateT.lift action⟩
  let forwarder := (QueryImpl.id' LabCommon).liftTarget
    (StateT PUnit (OracleComp LabCommon))
  let guard := QueryImpl.guardQueryBudget caps
    (Sum.elim (fun _ : A.Domain => (0, 0)) (policy reserve s)) forwarder fallback
  let handler := ((routeLab s).mapStateTBase guard).flattenStateT
  let liftA : QueryImpl Lab (OracleComp A) := fun input => liftM (A.query (.inl input))
  let marked := commonProjection ∘ₛ
    (SigningView.Events.phaseImpl A Message .keygen ∘ₛ liftA)
  let program := (labScheme FIPS205.core (fun pk => pure pk.pkSeed) s).keygen
  let initial : PUnit × Paid := (PUnit.unit, ((0, 0), false))
  have hmarked (input : Lab.Domain) (hi : NoPublicInput input) :
      marked input = liftM (LabCommon.query (.inl (.inl input))) :=
    by
      simpa only [marked, QueryImpl.apply_compose, QueryImpl.simulateQ_compose, liftA]
        using projected_private_query input hi
  have hstep (input : Lab.Domain) (raw : Raw.QueryCache) :
      (handler (.inl (.inl input))).run (initial, raw) =
        (fun answer => (answer, (initial, raw))) <$>
          (liftM ((Lab + O).query (.inl input)) : OracleComp (Lab + O) (Lab.Range input)) := by
    have hcap : ((0, 0) : Nat × Nat) ≤ caps := ⟨Nat.zero_le _, Nat.zero_le _⟩
    simp [handler, guard, forwarder, initial, QueryImpl.guardQueryBudget,
      QueryImpl.flattenStateT_mapStateTBase_apply_run,
      QueryImpl.id', hcap, routeLab, QueryImpl.add, Functor.map_map]
  let liftLab : QueryImpl Lab (OracleComp (Lab + O)) :=
    fun input => liftM ((Lab + O).query (.inl input))
  let Q := fun {α : Type} (oa : OracleComp Lab α) => ∀ raw : Raw.QueryCache,
    (simulateQ (handler ∘ₛ marked) oa).run (initial, raw) =
      (fun answer => (answer, (initial, raw))) <$> simulateQ liftLab oa
  have hpure : ∀ {α : Type} (a : α), Q (pure a) := by
    intro α a raw
    simp
  have hbind : ∀ {α β : Type} (oa : OracleComp Lab α) (ob : α → OracleComp Lab β),
      Q oa → (∀ a, Q (ob a)) → Q (oa >>= ob) := by
    intro α β oa ob hoa hob raw
    simp only [simulateQ_bind, StateT.run_bind, map_bind]
    rw [hoa raw, bind_map_left]
    exact bind_congr fun a => hob a raw
  have htouch : ∀ c, Q (touchCell (some c)) := by
    intro c raw
    simpa [touchCell, QueryImpl.apply_compose, hmarked (.inr (.inl c)) trivial,
      simulateQ_spec_query, liftLab] using hstep (.inr (.inl c)) raw
  have hread : ∀ c, Q (readCell (some c)) := by
    rintro (derive | node) raw
    · simpa [readCell, QueryImpl.apply_compose, hmarked (.inl (.inr derive)) trivial,
        simulateQ_spec_query, liftLab] using hstep (.inl (.inr derive)) raw
    · simpa [readCell, QueryImpl.apply_compose, hmarked (.inr (.inr node)) trivial,
        simulateQ_spec_query, liftLab] using hstep (.inr (.inr node)) raw
  have hprogram : Q program := by
    change Q (labKeygen FIPS205.core >>= fun root =>
      pure ((⟨s, root⟩, ⟨s, root⟩) : PK × PK))
    exact hbind _ _ (labKeygen_pred FIPS205.core hpure hbind htouch hread) fun _ => hpure _
  have hfield : (commonView true s).keygen = simulateQ liftA program := by
    simp only [commonView_eq_rejectingEncoding, SigningView.rejectingEncoding_keygen,
      SignatureAlg.map_keygen]
    rfl
  have hprefix : simulateQ commonProjection
      (SigningView.Events.viewWithEvents (commonView true s)).keygen =
        simulateQ marked program := by
    simp only [SigningView.Events.viewWithEvents, hfield, ← QueryImpl.simulateQ_compose]
    rfl
  change (simulateQ (routeLab s)
    ((simulateQ guard (simulateQ commonProjection
      (SigningView.Events.viewWithEvents (commonView true s)).keygen)).run initial)).run ∅ = _
  rw [hprefix, simulateQ_mapStateTBase_run_eq_map_flattenStateT,
    ← QueryImpl.simulateQ_compose, hprogram ∅]
  simp only [Functor.map_map]
  rfl

end Keygen

/-- Cold native key generation retains its keys and creates only honest private cells. -/
theorem native_cold_keygen_provenance
    (s : FIPS205.core.PkSeed) (reserve : Bool) (caps : Nat × Nat)
    (fallback : (input : LabCommon.Domain) → LabCommon.Range input)
    (leftTape rightTape : List HashOutput) :
    let tapes : (j : Coverage.TapeClass) →
        List (Coverage.tapeClassRange FIPS205.core j)
      | .signer => leftTape.map Bridge.answerEquiv
      | .forger => rightTape.map Bridge.answerEquiv
      | .other => []
    letI : MonadLiftT (OracleComp LabCommon) (StateT PUnit (OracleComp LabCommon)) :=
      ⟨fun action => StateT.lift action⟩
    let forwarder := (QueryImpl.id' LabCommon).liftTarget
      (StateT PUnit (OracleComp LabCommon))
    let guarded := (simulateQ (QueryImpl.guardQueryBudget caps
      (Sum.elim (fun _ : A.Domain => (0, 0)) (policy reserve s)) forwarder fallback)
      (simulateQ commonProjection
        (SigningView.Events.viewWithEvents (commonView true s)).keygen)).run
          (PUnit.unit, ((0, 0), false))
    let keygen := (simulateQ (Coverage.roleRunImpl FIPS205.core)
      ((simulateQ (CoverageDeferred.relative FIPS205.core s (metadataCost true s))
        ((simulateQ (routeLab s) guarded).run ∅)).run
          (((∅, ∅), []), (0, .keygen)))).run
            ((∅, tapes), (AnswerTape.ClassPos.init, ∅))
    ∀ result ∈ support keygen,
      let keys := result.1.1.1.1
      let physicalRaw := result.1.1.2
      let deferred := result.1.2
      let paid := result.1.1.1.2.2
      let C := deferred.1.1.1
      let D := deferred.1.1.2
      let pending := deferred.1.2
      keys.2 = keys.1 ∧ keys.1.pkSeed = s ∧
        physicalRaw = ∅ ∧ deferred.2 = (0, .keygen) ∧
        paid = ((0, 0), false) ∧ C = ∅ ∧
        (∀ k : PrfKey FIPS205.core,
          (D (.inl (.inl k))).isSome ∨ .inl (.inl k) ∈ pending →
            IsHonestKey FIPS205.params FIPS205.core k.1) ∧
        (∀ (o : FIPS205.core.Y) (msg : List Byte),
          D (.inl (.inr (o, msg))) = none ∧ .inl (.inr (o, msg)) ∉ pending)
 := by
  dsimp only
  intro result hr
  rw [Keygen.guarded_routed_keygen_eq s reserve caps fallback] at hr
  simp only [simulateQ_map, StateT.run_map] at hr
  rw [support_map] at hr
  obtain ⟨out, hout, rfl⟩ := hr
  have h := Keygen.native_lab_keygen_private s (fun pk => pure pk.pkSeed)
    ((∅, fun j => match j with
      | .signer => leftTape.map Bridge.answerEquiv
      | .forger => rightTape.map Bridge.answerEquiv
      | .other => []), (AnswerTape.ClassPos.init, ∅)) hout
  rcases h with ⟨hkeys, hseed, hprivate, hmeta⟩
  refine ⟨hkeys, hseed, rfl, hmeta, rfl, hprivate.1, ?_, ?_⟩
  · intro k hk
    exact hprivate.2 (.inl (.inl k)) hk
  · intro o msg
    refine ⟨?_, ?_⟩
    · cases hdraw : out.1.2.1.1.2 (.inl (.inr (o, msg))) with
      | none => rfl
      | some value =>
          have hfalse := hprivate.2 (.inl (.inr (o, msg)))
            (.inl (by simp only [hdraw, Option.isSome_some]))
          exact hfalse.elim
    · intro hpending
      exact hprivate.2 (.inl (.inr (o, msg))) (.inr hpending)

end SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native

end
