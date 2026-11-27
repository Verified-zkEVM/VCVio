/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.NativeRelative
public import HashSig.SLHDSA.SHAKE128s.Bridge.SharedExperiment.Pure
import VCVio.OracleComp.QueryTracking.QueryBound.Simulation
import VCVio.OracleComp.SimSemantics.StateT.PreservesInv
import all HashSig.SLHDSA.Security.CoverageRun

/-! # Marked key generation and its stateful continuation

The existing rejecting source executes through its guard, raw router and relative interpreter.
Private secret derivations and label operations sample only through the forwarded uniform port;
the complete role state is preserved while the private graph and pending cells remain threaded.
-/

public section
namespace SLHDSA.SHAKE128s.MarkedPrefix
open OracleComp OracleSpec SignatureAlg
open SLHDSA SLHDSA.Security SLHDSA.SHAKE128s
open SLHDSA.SHAKE128s.Bridge.SharedExperiment
open Guarded (PK Raw H A O Lab LabCommon Full Paid Meta RawOutcome
  commonView commonMain commonSource commonProjection routeLab policy metadataCost
  guardedRoutedSource)

/-- A partial run with its output, budget state, raw query cache and deferred-coverage state. -/
abbrev Stage (alpha : Type) :=
  ((alpha × (PUnit × Paid)) × Raw.QueryCache) × CoverageDeferred.S FIPS205.core
/-- The full marked experiment output together with the terminal state of the role-indexed tapes. -/
abbrev Outcome := Stage Full × Coverage.RoleState FIPS205.core
/-- The two public keys from the key-generation prefix together with its stage and role states. -/
abbrev PrefixOutcome := Stage (PK × PK) × Coverage.RoleState FIPS205.core

/-- The physical experiment’s public key, secret key and raw forgery outcome. -/
abbrev ActualFull :=
  (PK × SecretKeyCore FIPS205.core) × RawOutcome

/-- The marked key-generation prefix on the labelled common interface at a fixed public seed. -/
noncomputable abbrev keygenSource (seed : FIPS205.core.PkSeed) :
    OracleComp LabCommon (PK × PK) :=
  simulateQ commonProjection
    (SigningView.Events.viewWithEvents (commonView true seed)).keygen

/-- Continue the marked signing and verification run from the two keys returned by its prefix. -/
noncomputable abbrev suffixSource (seed : FIPS205.core.PkSeed)
    (adv : Game.Adversary FIPS205.Answer PK) (pk sk : PK) :
    OracleComp LabCommon Full :=
  let marked := SigningView.Events.viewWithEvents (commonView true seed)
  simulateQ commonProjection (do
    let (forgery, rawLog) ← marked.runWithSigningOracle pk sk
      (SigningView.Events.mainWithEvents (commonMain adv) pk)
    let verified ← marked.verify pk forgery.1 forgery.2
    return ((pk, sk), (⟨forgery, rawLog, verified⟩ : RawOutcome)))

/-- Apply the budget guard, route raw queries and run deferred coverage from the supplied
intermediate states. -/
noncomputable abbrev roleProgram {alpha : Type} (seed : FIPS205.core.PkSeed)
    (caps : Nat × Nat)
    (fallback : (input : LabCommon.Domain) → LabCommon.Range input)
    (source : OracleComp LabCommon alpha) (paid : Paid) (raw : Raw.QueryCache)
    (relative : CoverageDeferred.S FIPS205.core) :
    OracleComp (Coverage.roleSpec FIPS205.core) (Stage alpha) :=
  letI : MonadLiftT (OracleComp LabCommon) (StateT PUnit (OracleComp LabCommon)) :=
    ⟨fun action => StateT.lift action⟩
  let forwarder := (QueryImpl.id' LabCommon).liftTarget
    (StateT PUnit (OracleComp LabCommon))
  let guarded := (simulateQ (QueryImpl.guardQueryBudget caps
    (Sum.elim (fun _ : A.Domain => (0, 0)) (policy true seed)) forwarder fallback)
      source).run (PUnit.unit, paid)
  let routed := (simulateQ (routeLab seed) guarded).run raw
  (simulateQ (CoverageDeferred.relative FIPS205.core seed (metadataCost true seed))
    routed).run relative

/-- Interpret the complete guarded experiment as role-indexed queries from a given deferred-coverage
state. -/
noncomputable abbrev wholeRoleProgram (seed : FIPS205.core.PkSeed)
    (adv : Game.Adversary FIPS205.Answer PK) (caps : Nat × Nat)
    (fallback : (input : LabCommon.Domain) → LabCommon.Range input)
    (relative : CoverageDeferred.S FIPS205.core) :
    OracleComp (Coverage.roleSpec FIPS205.core) (Stage Full) :=
  (simulateQ (CoverageDeferred.relative FIPS205.core seed (metadataCost true seed))
    (guardedRoutedSource seed adv true caps fallback)).run relative

/-- Run the complete marked experiment with the supplied family of role-indexed tapes and an empty
cache. -/
noncomputable abbrev wholeRun (seed : FIPS205.core.PkSeed)
    (adv : Game.Adversary FIPS205.Answer PK) (caps : Nat × Nat)
    (fallback : (input : LabCommon.Domain) → LabCommon.Range input)
    (relative : CoverageDeferred.S FIPS205.core)
    (family : (j : Coverage.TapeClass) → List (Coverage.tapeClassRange FIPS205.core j)) :
    ProbComp Outcome :=
  (simulateQ (Coverage.roleRunImpl FIPS205.core)
    (wholeRoleProgram seed adv caps fallback relative)).run
      ((∅, family), (AnswerTape.ClassPos.init, ∅))

private def NoPublicLab : Lab.Domain → Prop
  | .inl (.inl _) => False
  | .inl (.inr _) | .inr _ => True

private def PrivateLab : Lab.Domain → Prop
  | .inl (.inr (.inl _)) | .inr _ => True
  | _ => False

private def PrivateCommon : LabCommon.Domain → Prop :=
  Sum.elim (Sum.elim PrivateLab (fun _ => False)) (fun _ => False)

private def PrivateRouted : (Lab + O).Domain → Prop :=
  Sum.elim PrivateLab (fun _ => False)

private def UniformRole : (Coverage.roleSpec FIPS205.core).Domain → Prop
  | .inl _ => True
  | .inr _ => False

private theorem lab_keygen_private :
    AllQueriesSatisfy (labKeygen FIPS205.core) PrivateLab := by
  have noPublic : AllQueriesSatisfy (labKeygen FIPS205.core) NoPublicLab := by
    refine labKeygen_pred FIPS205.core
      (Q := fun {alpha : Type} (program : OracleComp Lab alpha) =>
        AllQueriesSatisfy program NoPublicLab)
      (fun _ => allQueriesSatisfy_pure _ _)
      (fun _ _ first rest => allQueriesSatisfy_bind first rest) ?_ ?_
    · intro cell
      exact (allQueriesSatisfy_query_iff _ _).2 trivial
    · rintro (secret | node)
      · exact (allQueriesSatisfy_query_iff _ _).2 trivial
      · exact (allQueriesSatisfy_query_iff _ _).2 trivial
  refine (noPublic.and
    (SLHDSA.Security.NativeProvenance.lab_keygen_structural FIPS205.core)).mono ?_
  rintro ((native | (secret | nonce)) | label) allowed
  · exact allowed.1.elim
  · trivial
  · exact allowed.2.elim
  · trivial

private theorem lab_scheme_keygen_private (seed : FIPS205.core.PkSeed) :
    AllQueriesSatisfy
      ((labScheme FIPS205.core (fun key => pure key.pkSeed) seed).keygen) PrivateLab := by
  change AllQueriesSatisfy
    (do
      let root ← labKeygen FIPS205.core
      return ((⟨seed, root⟩ : PK), (⟨seed, root⟩ : PK))) PrivateLab
  exact allQueriesSatisfy_bind lab_keygen_private (fun _ => allQueriesSatisfy_pure _ _)

private theorem private_marker_silent (input : Lab.Domain) (allowed : PrivateLab input) :
    Guarded.commonEvent (.ambient .keygen (.inl input)) = none := by
  rcases input with (native | (secret | nonce)) | label
  · exact allowed.elim
  · rfl
  · exact allowed.elim
  · cases label <;> rfl

private theorem keygen_source_private (seed : FIPS205.core.PkSeed) :
    AllQueriesSatisfy (keygenSource seed) PrivateCommon := by
  let liftLab : QueryImpl Lab (OracleComp A) :=
    fun input => liftM (A.query (.inl input))
  let marking := SigningView.Events.phaseImpl A Message .keygen
  have step (input : Lab.Domain) (allowed : PrivateLab input) :
      AllQueriesSatisfy
        (simulateQ commonProjection
          (simulateQ marking (liftM (A.query (.inl input))))) PrivateCommon := by
    have projected : simulateQ commonProjection
        (simulateQ marking (liftM (A.query (.inl input)))) =
          (liftM (LabCommon.query (.inl (.inl input))) :
            OracleComp LabCommon (Lab.Range input)) := by
      rw [simulateQ_spec_query]
      simp only [marking, SigningView.Events.phaseImpl, QueryImpl.preInsert_apply,
        SigningView.Events.emit, monadLift_self, simulateQ_bind, simulateQ_spec_query,
        commonProjection, QueryImpl.add, private_marker_silent input allowed, pure_bind]
    rw [projected]
    exact (allQueriesSatisfy_query_iff _ _).2 allowed
  have source := (lab_scheme_keygen_private seed).simulateQ
    (impl := commonProjection ∘ₛ (marking ∘ₛ liftLab)) (fun input allowed => by
      simpa only [QueryImpl.apply_compose, QueryImpl.simulateQ_compose, liftLab]
        using step input allowed)
  simpa only [keygenSource, SigningView.Events.viewWithEvents,
    commonView, Guarded.partialView, ite_true, SigningView.map_keygen,
    SigningView.rejectingEncoding_keygen, SignatureAlg.map_keygen, simulateQ'_apply,
    QueryImpl.simulateQ_compose, liftLab, marking] using source

private theorem private_source_cost_zero (seed : FIPS205.core.PkSeed)
    (input : LabCommon.Domain) (allowed : PrivateCommon input) :
    Sum.elim (fun _ : A.Domain => (0, 0)) (policy true seed) input = (0, 0) := by
  rcases input with (native | raw) | event
  · rfl
  · rfl
  · exact allowed.elim

private theorem lift_uniform_role {alpha : Type} (program : ProbComp alpha) :
    AllQueriesSatisfy (liftComp program (Coverage.roleSpec FIPS205.core)) UniformRole := by
  unfold liftComp
  refine (allQueriesSatisfy_of_forall (fun _ => True.intro) program).simulateQ ?_
  intro sample _
  change AllQueriesSatisfy
    (liftM ((Coverage.roleSpec FIPS205.core).query (.inl sample)) :
      OracleComp (Coverage.roleSpec FIPS205.core) _) UniformRole
  exact (allQueriesSatisfy_query_iff _ _).2 trivial

private theorem role_uniform_step (n : Nat) (state : Coverage.RoleState FIPS205.core) :
    ((Coverage.roleRunImpl FIPS205.core (.inl n)).run state) =
      (fun value => (value, state)) <$>
        (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))) := by
  rw [QueryImpl.extendState_apply]
  simp [AnswerTape.tapeImplFwd, QueryImpl.add_apply_inl,
    AnswerTape.classPosAuxFwd, AnswerTape.freshHitAux]

/-- The actual marked key-generation prefix preserves every supplied role-state field. -/
theorem marked_keygen_uniform_and_role_state_unchanged
    (seed : FIPS205.core.PkSeed) (caps : Nat × Nat)
    (fallback : (input : LabCommon.Domain) → LabCommon.Range input)
    (paid : Paid) (raw : Raw.QueryCache)
    (relative : CoverageDeferred.S FIPS205.core)
    (role : Coverage.RoleState FIPS205.core) :
    let program := roleProgram seed caps fallback (keygenSource seed) paid raw relative
    program.AllQueriesSatisfy
      (fun input => match input with | .inl _ => True | .inr _ => False) ∧
      ∀ outcome ∈ support ((simulateQ (Coverage.roleRunImpl FIPS205.core) program).run role),
        outcome.2 = role := by
  classical
  let _ : MonadLiftT (OracleComp LabCommon) (StateT PUnit (OracleComp LabCommon)) :=
    ⟨fun action => StateT.lift action⟩
  intro program
  let forwarder := (QueryImpl.id' LabCommon).liftTarget
    (StateT PUnit (OracleComp LabCommon))
  let charge := Sum.elim (fun _ : A.Domain => (0, 0)) (policy true seed)
  let guard := QueryImpl.guardQueryBudget caps charge forwarder fallback
  have guarded : AllQueriesSatisfy
      ((simulateQ guard (keygenSource seed)).run (PUnit.unit, paid)) PrivateCommon := by
    refine (keygen_source_private seed).simulateQ_run ?_ (PUnit.unit, paid)
    intro input allowed before
    have free : charge input = (0, 0) := private_source_cost_zero seed input allowed
    by_cases aborted : before.2.2 = true
    · simp [guard, QueryImpl.guardQueryBudget, aborted]
    · by_cases fits : before.2.1 + charge input ≤ caps
      · rw [free] at fits
        have query :=
          (allQueriesSatisfy_query_iff (spec := LabCommon) input PrivateCommon).2 allowed
        simpa [guard, QueryImpl.guardQueryBudget, aborted, free, fits, forwarder,
          QueryImpl.liftTarget_apply, QueryImpl.id', map_eq_bind_pure_comp,
          allQueriesSatisfy_def, isQueryBound_map_iff] using query
      · rw [free] at fits
        simp [guard, QueryImpl.guardQueryBudget, aborted, free, fits]
  have routed : AllQueriesSatisfy
      ((simulateQ (routeLab seed)
        ((simulateQ guard (keygenSource seed)).run (PUnit.unit, paid))).run raw)
      PrivateRouted := by
    refine guarded.simulateQ_run ?_ raw
    rintro ((input | bytes) | event) allowed cache
    · change AllQueriesSatisfy
        ((fun answer => (answer, cache)) <$>
          (liftM ((Lab + O).query (.inl input)) : OracleComp (Lab + O) _)) PrivateRouted
      simpa only [allQueriesSatisfy_def, isQueryBound_map_iff] using
        (allQueriesSatisfy_query_iff (spec := Lab + O) (.inl input) PrivateRouted).2 allowed
    · exact allowed.elim
    · exact allowed.elim
  have relativeStep (input : Lab.Domain) (before : CoverageDeferred.S FIPS205.core) :
      AllQueriesSatisfy
        (do
          let result ← liftComp
            (((slhGraph FIPS205.core seed).deferredImpl input).run before.1)
            (Coverage.roleSpec FIPS205.core)
          pure (result.1, (result.2, before.2))) UniformRole :=
    allQueriesSatisfy_bind (lift_uniform_role _) (fun _ => allQueriesSatisfy_pure _ _)
  have relativeQueries : ∀ input, PrivateRouted input → ∀ before,
      AllQueriesSatisfy
        ((CoverageDeferred.relative FIPS205.core seed (metadataCost true seed) input).run before)
        UniformRole := by
    rintro (input | event) allowed before
    · rcases input with (native | (secret | nonce)) | label
      · exact allowed.elim
      · simpa only [CoverageDeferred.relative, StateT.run_mk] using
          relativeStep (.inl (.inr (.inl secret))) before
      · exact allowed.elim
      · rcases label with touch | node
        · simpa only [CoverageDeferred.relative, StateT.run_mk] using
            relativeStep (.inr (.inl touch)) before
        · simpa only [CoverageDeferred.relative, StateT.run_mk] using
            relativeStep (.inr (.inr node)) before
    · exact allowed.elim
  have uniform : program.AllQueriesSatisfy UniformRole := by
    simpa only [program, roleProgram, guard, charge, forwarder] using
      routed.simulateQ_run relativeQueries relative
  refine ⟨uniform, ?_⟩
  intro outcome member
  exact uniform.holds_of_mem_support_run_simulateQ (fun current => current = role)
    (fun input allowed before hbefore after hafter => by
      rcases input with n | point
      · rw [role_uniform_step, support_map] at hafter
        obtain ⟨value, _, rfl⟩ := hafter
        exact hbefore
      · exact allowed.elim) rfl member

private theorem role_program_bind
    {alpha beta : Type} (seed : FIPS205.core.PkSeed) (caps : Nat × Nat)
    (fallback : (input : LabCommon.Domain) → LabCommon.Range input)
    (source : OracleComp LabCommon alpha) (next : alpha → OracleComp LabCommon beta)
    (paid : Paid) (raw : Raw.QueryCache) (relative : CoverageDeferred.S FIPS205.core) :
    roleProgram seed caps fallback (source >>= next) paid raw relative = (do
      let stageResult ← roleProgram seed caps fallback source paid raw relative
      roleProgram seed caps fallback (next stageResult.1.1.1)
        stageResult.1.1.2.2 stageResult.1.2 stageResult.2) := by
  simp only [roleProgram, simulateQ_bind, StateT.run_bind]

/-- The complete prefix output passes its actual keys and every state to the rejecting suffix. -/
theorem marked_wholeRun_eq_prefix_suffix
    (seed : FIPS205.core.PkSeed) (adv : Game.Adversary FIPS205.Answer PK)
    (caps : Nat × Nat)
    (fallback : (input : LabCommon.Domain) → LabCommon.Range input)
    (relative : CoverageDeferred.S FIPS205.core)
    (family : (j : Coverage.TapeClass) → List (Coverage.tapeClassRange FIPS205.core j)) :
    wholeRun seed adv caps fallback relative family = (do
      let stageResult : PrefixOutcome ← (simulateQ (Coverage.roleRunImpl FIPS205.core)
        (roleProgram seed caps fallback (keygenSource seed) ((0, 0), false) ∅ relative)).run
          ((∅, family), (AnswerTape.ClassPos.init, ∅))
      (simulateQ (Coverage.roleRunImpl FIPS205.core)
        (roleProgram seed caps fallback
          (suffixSource seed adv stageResult.1.1.1.1.1 stageResult.1.1.1.1.2)
          stageResult.1.1.1.2.2 stageResult.1.1.2 stageResult.1.2)).run stageResult.2) := by
  have source : commonSource true seed adv =
      (keygenSource seed >>= fun keys => suffixSource seed adv keys.1 keys.2) := by
    simp only [commonSource, keygenSource, suffixSource, SigningView.Events.fullExperiment,
      simulateQ_bind, simulateQ_pure, Prod.eta]
  change (simulateQ (Coverage.roleRunImpl FIPS205.core)
    (roleProgram seed caps fallback (commonSource true seed adv) ((0, 0), false) ∅ relative)).run
      ((∅, family), (AnswerTape.ClassPos.init, ∅)) = _
  rw [source, role_program_bind]
  simp only [simulateQ_bind, StateT.run_bind]

end SLHDSA.SHAKE128s.MarkedPrefix
