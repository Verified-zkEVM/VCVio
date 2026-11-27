/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.SHAKE128s.Bridge.SharedExperiment.Pure
public import HashSig.SLHDSA.Security.NativeCounts
import all HashSig.SLHDSA.Security.NativeCounts
import all VCVio.OracleComp.QueryTracking.RandomOracle.ClassIndexedTape.Position
import VCVio.OracleComp.SimSemantics.StateT.StateSeparating

/-! # Work accounting for a guarded raw hash call -/

public section
namespace SLHDSA.SHAKE128s.Bridge.SharedExperiment
open OracleComp OracleSpec SignatureAlg
open SLHDSA SLHDSA.Security SLHDSA.SHAKE128s
open Guarded

private theorem guarded_marked_raw_normal_form
    (s : FIPS205.core.PkSeed) (phase : SigningView.Phase) (raw : Raw.Domain)
    (caps : Nat × Nat)
    (fallback : (input : LabCommon.Domain) → LabCommon.Range input)
    (beforePaid : Paid) :
    letI : MonadLiftT (OracleComp LabCommon) (StateT PUnit (OracleComp LabCommon)) :=
      ⟨fun action => StateT.lift action⟩
    let forwarder := (QueryImpl.id' LabCommon).liftTarget
      (StateT PUnit (OracleComp LabCommon))
    let source := simulateQ commonProjection
      (SigningView.Events.phaseImpl A Message phase (.inr raw))
    let event : Ev := .ambient phase (.inr raw)
    let proposed := beforePaid.1 + policy true s event
    (simulateQ (QueryImpl.guardQueryBudget caps
      (Sum.elim (fun _ : A.Domain => (0, 0)) (policy true s)) forwarder fallback)
      source).run (PUnit.unit, beforePaid) =
      if beforePaid.2 then
        pure (fallback (.inl (.inr raw)), (PUnit.unit, beforePaid))
      else if proposed ≤ caps then
        (do
          let _ ← (liftM (LabCommon.query (.inr event)) : OracleComp LabCommon PUnit)
          let answer ← (liftM (LabCommon.query (.inl (.inr raw))) :
            OracleComp LabCommon (Raw.Range raw))
          pure (answer, (PUnit.unit, (proposed, false))))
      else pure (fallback (.inl (.inr raw)), (PUnit.unit, (beforePaid.1, true))) := by
  classical
  let _ : MonadLiftT (OracleComp LabCommon) (StateT PUnit.{1} (OracleComp LabCommon)) :=
    ⟨fun action => StateT.lift action⟩
  dsimp only
  have zeroPair : ((0, 0) : Nat × Nat) = 0 := rfl
  have sourceEq :
      simulateQ commonProjection
        (SigningView.Events.phaseImpl A Message phase (.inr raw)) =
      (do
        let _ ← (liftM (LabCommon.query (.inr (.ambient phase (.inr raw)))) :
          OracleComp LabCommon PUnit)
        (liftM (LabCommon.query (.inl (.inr raw))) : OracleComp LabCommon (Raw.Range raw))) := by
    simp [SigningView.Events.phaseImpl, SigningView.Events.emit,
      commonProjection, commonEvent, QueryImpl.add,
      OracleQuery.input_query, OracleQuery.cont_query, seqRight_eq_bind]
  rw [sourceEq]
  cases aborted : beforePaid.2 with
  | true =>
      simp [simulateQ_bind, StateT.run_bind, QueryImpl.guardQueryBudget, aborted]
  | false =>
      by_cases accepted : beforePaid.1 + policy true s (.ambient phase (.inr raw)) ≤ caps
      · simp [simulateQ_bind, StateT.run_bind, QueryImpl.guardQueryBudget, aborted, accepted,
          zeroPair, add_zero, QueryImpl.liftTarget, QueryImpl.id', Functor.map_map,
          bind_map_left]
      · simp [simulateQ_bind, StateT.run_bind, QueryImpl.guardQueryBudget, aborted, accepted]

/-- An admitted raw marker funds the actual complete native count in its same terminal state. -/
theorem marked_raw_count_offsets
    (seed : FIPS205.core.PkSeed) (phase : SigningView.Phase) (raw : Raw.Domain)
    (hphase : phase = .adversary ∨ phase = .verification)
    (caps : Nat × Nat)
    (fallback : (input : LabCommon.Domain) → LabCommon.Range input)
    (beforePaid : Paid) (beforeRaw : Raw.QueryCache)
    (beforeRelative : CoverageDeferred.S FIPS205.core)
    (beforeRole : Coverage.RoleState FIPS205.core) :
    letI : MonadLiftT (OracleComp LabCommon)
        (StateT PUnit.{1} (OracleComp LabCommon)) :=
      ⟨fun action => StateT.lift action⟩
    let forwarder := (QueryImpl.id' LabCommon).liftTarget
      (StateT PUnit.{1} (OracleComp LabCommon))
    let source : OracleComp LabCommon (Raw.Range raw) :=
      simulateQ commonProjection (SigningView.Events.phaseImpl A Message phase (.inr raw))
    let guarded := (simulateQ (QueryImpl.guardQueryBudget caps
      (Sum.elim (fun _ : A.Domain => (0, 0)) (policy true seed)) forwarder fallback)
      source).run (PUnit.unit, beforePaid)
    let actual := (simulateQ (Coverage.roleRunImpl FIPS205.core)
      ((simulateQ (CoverageDeferred.relative FIPS205.core seed (metadataCost true seed))
        ((simulateQ (routeLab seed) guarded).run beforeRaw)).run beforeRelative)).run beforeRole
    ∀ result ∈ support actual,
      let afterPaid := result.1.1.1.2.2
      let afterRelative := result.1.2
      let afterRole := result.2
      afterPaid.1.2 = beforePaid.1.2 ∧
      afterRole.2.1.cnt .signer ≤ beforeRole.2.1.cnt .signer ∧
      afterRole.2.1.cnt .forger + beforeRelative.2.1 ≤
        beforeRole.2.1.cnt .forger + afterRelative.2.1 ∧
      afterRole.2.1.cnt .forger + beforePaid.1.1 ≤
        beforeRole.2.1.cnt .forger + afterPaid.1.1 := by
  classical
  let _ : MonadLiftT (OracleComp LabCommon) (StateT PUnit.{1} (OracleComp LabCommon)) :=
    ⟨fun action => StateT.lift action⟩
  intro forwarder source guarded actual result hr
  let event : Ev := .ambient phase (.inr raw)
  let cost := policy true seed event
  let proposed := beforePaid.1 + cost
  let selected := metadataCost true seed event
  let marker : CoverageDeferred.S FIPS205.core :=
    (beforeRelative.1, (beforeRelative.2.1 + selected, phase))
  let native := NativeCounts.nativeImpl FIPS205.core seed (metadataCost true seed)
  let transport := QueryImpl.ofLift (unifSpec + H) (OracleComp (Lab + O))
  let handler := native ∘ₛ transport
  let rawProgram := ((encoding seed).tableRouter raw).run beforeRaw
  let frame := fun out : (Raw.Range raw × Raw.QueryCache) ×
      (CoverageDeferred.S FIPS205.core × Coverage.RoleState FIPS205.core) =>
    ((((out.1.1, (PUnit.unit, (proposed, false))), out.1.2), out.2.1), out.2.2)
  have uniformQuery : ∀ n state,
      (handler (.inl n)).run state =
        (fun answer => (answer, state)) <$>
          (liftM (unifSpec.query n) : ProbComp (unifSpec.Range n)) := by
    intro n state
    have included : transport (.inl n) =
        (liftM ((Lab + O).query (.inl (.inl (.inl (.inl n))))) :
          OracleComp (Lab + O) (unifSpec.Range n)) := by rfl
    change (simulateQ native (transport (.inl n))).run state = _
    rw [included, simulateQ_spec_query]
    change ((NativeCounts.nativeImpl FIPS205.core seed (metadataCost true seed)
      (.inl (.inl (.inl (.inl n))))).run state) = _
    rw [NativeCounts.nativeImpl, QueryImpl.flattenStateT_mapStateTBase_apply_run]
    simp only [CoverageDeferred.relative, StateT.run_mk, simulateQ_map, StateT.run_map,
      Coverage.roleRunImpl_liftComp_run, CanonicalGraph.deferredImpl_run_inl,
      CanonicalGraph.relabelImpl_run_unif, Functor.map_map, Prod.eta, bind_pure_comp]
  have publicQuery : ∀ point state,
      (handler (.inr point)).run state =
        (native (.inl (.inl (.inl (.inr point))))).run state := by
    intro point state
    have included : transport (.inr point) =
        (liftM ((Lab + O).query (.inl (.inl (.inl (.inr point))))) :
          OracleComp (Lab + O) (H.Range point)) := by
      rcases point with (⟨seed, key, values⟩ | ⟨R, seed, root, message⟩) | nonce <;> rfl
    change (simulateQ native (transport (.inr point))).run state = _
    rw [included, simulateQ_spec_query]
  -- The raw table reads its cached value or draws one using only the uniform interface.
  have uniformRun (program : ProbComp (Raw.Range raw × Raw.QueryCache)) :
      (simulateQ handler (liftComp program (unifSpec + H))).run (marker, beforeRole) =
        (fun x => (x, (marker, beforeRole))) <$> program := by
    apply QueryImpl.Stateful.simulateQ_liftComp_run_of_query
    intro n state
    rw [liftComp_liftM_query]
    change (simulateQ handler (liftM ((unifSpec + H).query (.inl n)))).run state = _
    rw [simulateQ_spec_query, uniformQuery]
  have rawLink :
      (simulateQ (Coverage.roleRunImpl FIPS205.core)
        ((simulateQ (CoverageDeferred.relative FIPS205.core seed (metadataCost true seed))
          (simulateQ transport rawProgram)).run marker)).run beforeRole =
        (fun z => ((z.1, z.2.1), z.2.2)) <$>
          (simulateQ handler rawProgram).run (marker, beforeRole) := by
    rw [simulateQ_mapStateTBase_run_eq_map_flattenStateT,
      ← QueryImpl.simulateQ_compose]
  have markerRun :
      (simulateQ (Coverage.roleRunImpl FIPS205.core)
        ((CoverageDeferred.relative FIPS205.core seed (metadataCost true seed)
          (.inr event)).run beforeRelative)).run beforeRole =
        pure ((PUnit.unit, marker), beforeRole) := by
    rw [CoverageDeferred.relative_marker]
    rfl
  have normal : actual =
      if beforePaid.2 then
        pure ((((fallback (.inl (.inr raw)), (PUnit.unit, beforePaid)), beforeRaw),
          beforeRelative), beforeRole)
      else if proposed ≤ caps then
        frame <$> (simulateQ handler rawProgram).run (marker, beforeRole)
      else pure ((((fallback (.inl (.inr raw)), (PUnit.unit, (beforePaid.1, true))),
        beforeRaw), beforeRelative), beforeRole) := by
    have original := guarded_marked_raw_normal_form seed phase raw caps fallback beforePaid
    have interpreted := congrArg (fun computation =>
      (simulateQ (Coverage.roleRunImpl FIPS205.core)
        ((simulateQ (CoverageDeferred.relative FIPS205.core seed (metadataCost true seed))
          ((simulateQ (routeLab seed) computation).run beforeRaw)).run beforeRelative)).run
            beforeRole) original
    change actual = _ at interpreted
    rw [interpreted]
    cases aborted : beforePaid.2 with
    | true =>
      simp [simulateQ_pure, StateT.run_pure]
    | false =>
      by_cases admitted : proposed ≤ caps
      · have admitted' :
            beforePaid.1 + policy true seed (.ambient phase (.inr raw)) ≤ caps := admitted
        simp only [admitted, proposed, cost, event, routeLab, QueryImpl.add,
          simulateQ_bind, simulateQ_map, StateT.run_mk, StateT.run_bind, StateT.run_map,
          markerRun, marker, selected, Bool.false_eq_true, ite_false, ite_true, bind_pure_comp,
          simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map]
        change
          (fun p => frame (p.1.1, (p.1.2, p.2))) <$>
            (simulateQ (Coverage.roleRunImpl FIPS205.core)
              ((simulateQ (CoverageDeferred.relative FIPS205.core seed (metadataCost true seed))
                (simulateQ transport rawProgram)).run marker)).run beforeRole =
            frame <$> (simulateQ handler rawProgram).run (marker, beforeRole)
        rw [rawLink]
        simp only [Functor.map_map]
      · have admitted' :
            ¬ beforePaid.1 + policy true seed (.ambient phase (.inr raw)) ≤ caps := admitted
        simp [admitted, proposed, cost, event,
          simulateQ_pure, StateT.run_pure]
  -- The selected-message counter and paid reserve use the same routed input.
  have costs : selected ≤ cost.1 ∧ cost.2 = 0 := by
    cases route : (encoding seed).route raw with
    | none =>
      rcases hphase with rfl | rfl <;>
        simp [selected, cost, event, metadataCost, selectedRaw, policy, originalPolicy,
          Game.Counted.sourcePolicy, Game.Counted.sourceKind, Game.hashCost,
          RandomOracleModel.hashCost, route]
    | some point =>
      rcases point with (⟨_, _, _⟩ | ⟨_, _, _, _⟩) | nonce <;>
        rcases hphase with rfl | rfl <;>
          simp [selected, cost, event, metadataCost, selectedRaw, policy, originalPolicy,
            Game.Counted.sourcePolicy, Game.Counted.sourceKind, Game.hashCost,
            RandomOracleModel.hashCost, reserveExtra, route]
  have paidSecond : proposed.2 = beforePaid.1.2 := by
    simp only [proposed, Prod.snd_add, costs.2, Nat.add_zero]
  have paidFirst : proposed.1 = beforePaid.1.1 + cost.1 := rfl
  rw [normal] at hr
  split_ifs at hr with aborted admitted
  · simp only [support_pure, Set.mem_singleton_iff] at hr
    subst result
    exact ⟨rfl, le_rfl, le_rfl, le_rfl⟩
  · rw [support_map] at hr
    obtain ⟨out, hout, rfl⟩ := hr
    simp only [rawProgram, RandomOracleEncoding.tableRouter, StateT.run_mk,
      simulateQ_bind, StateT.run_bind] at hout
    obtain ⟨draw, hdraw, hout⟩ := (mem_support_bind_iff _ _ _).1 hout
    change draw ∈ support ((simulateQ handler (liftComp
      ((Raw.randomOracle raw).run beforeRaw) (unifSpec + H))).run (marker, beforeRole)) at hdraw
    rw [uniformRun, support_map] at hdraw
    obtain ⟨draw, _, rfl⟩ := hdraw
    cases route : (encoding seed).route raw with
    | none =>
      simp only [route, simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hout
      subst out
      refine ⟨paidSecond, le_rfl, ?_, ?_⟩
      · change beforeRole.2.1.cnt .forger + beforeRelative.2.1 ≤
            beforeRole.2.1.cnt .forger + (beforeRelative.2.1 + selected)
        omega
      · change beforeRole.2.1.cnt .forger + beforePaid.1.1 ≤
            beforeRole.2.1.cnt .forger + proposed.1
        omega
    | some point =>
      simp only [route, simulateQ_map, StateT.run_map,
        support_map] at hout
      obtain ⟨step, hstep, rfl⟩ := hout
      let input : Lab.Domain := .inl (.inl (.inr point))
      change step ∈ support ((simulateQ handler
        (liftM ((unifSpec + H).query (.inr point)))).run (marker, beforeRole)) at hstep
      rw [simulateQ_spec_query, publicQuery] at hstep
      have metadata := NativeCounts.nativeImpl_native_metadata FIPS205.core seed
        (metadataCost true seed) input (marker, beforeRole) step hstep
      have count (j : Coverage.TapeClass) (hj : j ≠ .other) :=
        NativeCounts.native_hmsg_count_le FIPS205.core seed (metadataCost true seed)
          input (marker, beforeRole) step hstep j hj
      have signer := count .signer (by decide)
      have forger := count .forger (by decide)
      have phaseMarker : marker.2.2 = phase := rfl
      have hsigner : step.2.2.2.1.cnt .signer ≤ beforeRole.2.1.cnt .signer := by
        rcases hphase with rfl | rfl <;> simpa [phaseMarker] using signer
      have hforger : step.2.2.2.1.cnt .forger ≤ beforeRole.2.1.cnt .forger + selected := by
        rcases hphase with rfl | rfl <;>
          rcases point with (⟨_, _, _⟩ | ⟨_, _, _, _⟩) | nonce <;>
            simpa [phaseMarker, input, NativeCounts.IsLabHmsg, Coverage.IsHmsgQuery,
              selected, event, metadataCost, selectedRaw, route] using forger
      have hmeta : step.2.1.2.1 = beforeRelative.2.1 + selected := congrArg Prod.fst metadata
      refine ⟨paidSecond, hsigner, ?_, ?_⟩
      · change step.2.2.2.1.cnt .forger + _ ≤ _ + step.2.1.2.1
        omega
      · change step.2.2.2.1.cnt .forger + _ ≤ _ + proposed.1
        omega
  · simp only [support_pure, Set.mem_singleton_iff] at hr
    subst result
    exact ⟨rfl, le_rfl, le_rfl, le_rfl⟩

end SLHDSA.SHAKE128s.Bridge.SharedExperiment
