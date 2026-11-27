/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.SHAKE128s.Bridge.SharedExperiment.Pure
public import HashSig.SLHDSA.Security.NativeCounts
import HashSig.SLHDSA.Security.SecretTraces
import all HashSig.SLHDSA.Security.NativeCounts
import all VCVio.OracleComp.QueryTracking.RandomOracle.ClassIndexedTape.Position
import VCVio.OracleComp.SimSemantics.StateT.StateSeparating

/-!
# Verification costs of accepting and rejecting wire requests

The verifier charges its executed queries on accepting and rejecting runs. Malformed inputs
return before any internal hash, and the count bound follows the queries of a well-formed
verification.
-/

public section
namespace SLHDSA.SHAKE128s.Bridge.SharedExperiment
open OracleComp OracleSpec SignatureAlg
open SLHDSA SLHDSA.Security SLHDSA.SHAKE128s
open Guarded

namespace VerificationOffsets

/-- The budget guard, raw cache, deferred graph state and role counters during verification. -/
abbrev World := Paid × Raw.QueryCache × CoverageDeferred.S FIPS205.core ×
  Coverage.RoleState FIPS205.core
/-- A verifier output together with the states returned by the four handlers. -/
abbrev Result (α : Type) :=
  (((α × (PUnit.{1} × Paid)) × Raw.QueryCache) × CoverageDeferred.S FIPS205.core) ×
    Coverage.RoleState FIPS205.core

/-- Project the post-verification state out of an instrumented result. -/
abbrev world {α : Type} (result : Result α) : World :=
  (result.1.1.1.2.2, result.1.1.2, result.1.2, result.2)

/-- Signing attempts stay fixed during verification. Growth of the forger count is bounded
by charged work and, for a nonweak key, by observed hash work. -/
abbrev offsets (nonweak : Prop) (before after : World) : Prop :=
  after.1.1.2 = before.1.1.2 ∧
    after.2.2.2.2.1.cnt .signer ≤ before.2.2.2.2.1.cnt .signer ∧
    after.2.2.2.2.1.cnt .forger + before.1.1.1 ≤
      before.2.2.2.2.1.cnt .forger + after.1.1.1 ∧
    (nonweak → after.2.2.2.2.1.cnt .forger + before.2.2.1.2.1 ≤
      before.2.2.2.2.1.cnt .forger + after.2.2.1.2.1)

private theorem offsets_refl (p : Prop) (start : World) : offsets p start start :=
  ⟨rfl, le_rfl, le_rfl, fun _ => le_rfl⟩

private theorem offsets_trans {p : Prop} {x y z : World}
    (xy : offsets p x y) (yz : offsets p y z) : offsets p x z := by
  obtain ⟨s, c, zf, m⟩ := xy
  obtain ⟨s', c', zf', m'⟩ := yz
  refine ⟨s'.trans s, c'.trans c, by omega, fun h => ?_⟩
  have := m h
  have := m' h
  omega

/-- Run a marked verifier computation from a specified guard, cache, graph and role state. -/
noncomputable abbrev execute {α : Type} (seed : FIPS205.core.PkSeed) (caps : Nat × Nat)
    (fallback : (input : LabCommon.Domain) → LabCommon.Range input)
    (source : OracleComp LabCommon α) (before : World) : ProbComp (Result α) :=
  letI : MonadLiftT (OracleComp LabCommon) (StateT PUnit.{1} (OracleComp LabCommon)) :=
    ⟨fun action => StateT.lift action⟩
  let forwarder := (QueryImpl.id' LabCommon).liftTarget (StateT PUnit.{1} (OracleComp LabCommon))
  let guarded := (simulateQ (QueryImpl.guardQueryBudget caps
    (Sum.elim (fun _ : A.Domain => (0, 0)) (policy true seed)) forwarder fallback)
    source).run (PUnit.unit, before.1)
  (simulateQ (Coverage.roleRunImpl FIPS205.core)
    ((simulateQ (CoverageDeferred.relative FIPS205.core seed (metadataCost true seed))
      ((simulateQ (routeLab seed) guarded).run before.2.1)).run before.2.2.1)).run before.2.2.2

private noncomputable abbrev markedPoint (point : (publicHashSpec FIPS205.core).Domain) :=
  simulateQ commonProjection
    (SigningView.Events.phaseImpl A Message .verification
      (.inl (.inl (.inl (.inr (.inl point))))))

private def honestHmsg (s : FIPS205.core.PkSeed) (root : FIPS205.core.Y) :
    (publicHashSpec FIPS205.core).Domain → Prop
  | .thash .. => True
  | .hmsg _ seed pkRoot _ => seed = s ∧ pkRoot = root

private theorem point_offsets (s : FIPS205.core.PkSeed) (root : FIPS205.core.Y)
    (q : (publicHashSpec FIPS205.core).Domain) (allowed : honestHmsg s root q)
    (caps : Nat × Nat) (fallback : (input : LabCommon.Domain) → LabCommon.Range input)
    (before : World) (result : Result ((publicHashSpec FIPS205.core).Range q))
    (hr : result ∈ support (execute s caps fallback (markedPoint q) before)) :
    offsets (¬IsWeakKey FIPS205.params (⟨s, root⟩ : PK)) before (world result) := by
  classical
  let _ : MonadLiftT (OracleComp LabCommon) (StateT PUnit.{1} (OracleComp LabCommon)) :=
    ⟨fun action => StateT.lift action⟩
  rcases before with ⟨beforePaid, beforeRaw, beforeDeferred, beforeRole⟩
  let point : H.Domain := .inl q
  let event : Ev := .ambient .verification (.inr (encode FIPS205.params point))
  let cost := policy true s event
  let proposed := beforePaid.1 + cost
  let selected := metadataCost true s event
  let marker : CoverageDeferred.S FIPS205.core :=
    (beforeDeferred.1, (beforeDeferred.2.1 + selected, .verification))
  let source := simulateQ commonProjection
    (SigningView.Events.phaseImpl A Message .verification
      (.inl (.inl (.inl (.inr point)))))
  let forwarder := (QueryImpl.id' LabCommon).liftTarget
    (StateT PUnit.{1} (OracleComp LabCommon))
  let guarded := (simulateQ (QueryImpl.guardQueryBudget caps
    (Sum.elim (fun _ : A.Domain => (0, 0)) (policy true s)) forwarder fallback)
    source).run (PUnit.unit, beforePaid)
  let actual := (simulateQ (Coverage.roleRunImpl FIPS205.core)
    ((simulateQ (CoverageDeferred.relative FIPS205.core s (metadataCost true s))
      ((simulateQ (routeLab s) guarded).run beforeRaw)).run beforeDeferred)).run beforeRole
  let nativeStep := (simulateQ (Coverage.roleRunImpl FIPS205.core)
    ((CoverageDeferred.relative FIPS205.core s (metadataCost true s)
      (.inl (.inl (.inl (.inr point))))).run marker)).run beforeRole
  let frame := fun step : (H.Range point × CoverageDeferred.S FIPS205.core) ×
      Coverage.RoleState FIPS205.core =>
    ((((step.1.1, (PUnit.unit, (proposed, false))), beforeRaw), step.1.2), step.2)
  change result ∈ support actual at hr
  have original : originalPolicy event = (1, 0) := by
    simp [event, originalPolicy, Game.Counted.sourcePolicy, Game.Counted.sourceKind,
      Game.hashCost, RandomOracleModel.hashCost]
  have costFirst : 1 ≤ cost.1 := by
    simp only [cost, policy, original, ite_true, Prod.fst_add]
    omega
  have costSecond : cost.2 = 0 := by
    simp only [cost, policy, original, ite_true, Prod.snd_add, Nat.add_zero]
  have paidSecond : proposed.2 = beforePaid.1.2 := by
    simp only [proposed, Prod.snd_add, costSecond, Nat.add_zero]
  have paidFirst : proposed.1 = beforePaid.1.1 + cost.1 := rfl
  let delta : Nat := if NativeCounts.IsLabHmsg FIPS205.core (.inl (.inl (.inr point))) then 1 else 0
  have deltaPaid : delta ≤ cost.1 := by dsimp only [delta]; split <;> omega
  have deltaMetadata (nonweak : ¬IsWeakKey FIPS205.params (⟨s, root⟩ : PK)) :
      delta ≤ selected := by
    cases q with
    | thash seed adrs values =>
      simp [delta, point, NativeCounts.IsLabHmsg, Coverage.IsHmsgQuery]
    | hmsg randomness seed pkRoot message =>
      obtain ⟨rfl, rfl⟩ := allowed
      have notThash : ¬IsThashString FIPS205.params
          (IsHonestKey FIPS205.params FIPS205.core) seed
          (encode FIPS205.params (.inl (.hmsg randomness seed pkRoot message))) :=
        fun thash => nonweak (isWeakKey_of_isThashString_encode_hmsg (by decide) thash)
      have fixed := shakeEncoding_route_encode_hmsg
        (vp := FIPS205.params) (by decide) (by decide) seed randomness pkRoot message notThash
      change (if NativeCounts.IsLabHmsg FIPS205.core
        (.inl (.inl (.inr (.inl (.hmsg randomness seed pkRoot message))))) then 1 else 0) ≤
        (match (encoding seed).route
          (encode FIPS205.params (.inl (.hmsg randomness seed pkRoot message))) with
          | some (.inl (.hmsg ..)) => 1
          | _ => 0)
      have hf : (encoding seed).route
          (encode FIPS205.params (.inl (.hmsg randomness seed pkRoot message))) =
            some (.inl (.hmsg randomness seed pkRoot message)) := fixed
      rw [hf]
      split <;> first | exact le_rfl | exact Nat.zero_le _
  have sourceEq : source =
      (do
        let _ ← (liftM (LabCommon.query (.inr event)) : OracleComp LabCommon PUnit)
        (liftM (LabCommon.query (.inl (.inl (.inl (.inl (.inr point)))))) :
          OracleComp LabCommon (H.Range point))) := by
    simp [source, event, SigningView.Events.phaseImpl,
      SigningView.Events.emit, commonProjection, commonEvent, sourceInput, QueryImpl.add,
      simulateQ_bind, OracleQuery.input_query, OracleQuery.cont_query, seqRight_eq_bind]
  have markerRun :
      (simulateQ (Coverage.roleRunImpl FIPS205.core)
        ((CoverageDeferred.relative FIPS205.core s (metadataCost true s)
          (.inr event)).run beforeDeferred)).run beforeRole =
        pure ((PUnit.unit, marker), beforeRole) := by
    rw [CoverageDeferred.relative_marker]
    rfl
  have zeroPair : ((0, 0) : Nat × Nat) = 0 := rfl
  have normal : actual =
      if beforePaid.2 then
        pure ((((fallback (.inl (.inl (.inl (.inl (.inr point))))),
          (PUnit.unit, beforePaid)), beforeRaw), beforeDeferred), beforeRole)
      else if proposed ≤ caps then frame <$> nativeStep
      else pure ((((fallback (.inl (.inl (.inl (.inl (.inr point))))),
        (PUnit.unit, (beforePaid.1, true))), beforeRaw), beforeDeferred), beforeRole) := by
    simp only [actual, guarded, sourceEq]
    cases aborted : beforePaid.2 with
    | true =>
        simp [QueryImpl.guardQueryBudget, aborted, simulateQ_bind, StateT.run_bind]
    | false =>
        by_cases accepted : proposed ≤ caps
        · have accepted' : beforePaid.1 + policy true s event ≤ caps := accepted
          simp [QueryImpl.guardQueryBudget, aborted, accepted,
            proposed, cost, zeroPair, add_zero, forwarder,
            QueryImpl.liftTarget, QueryImpl.id', routeLab, QueryImpl.add,
            markerRun,
            simulateQ_bind, simulateQ_map,
             StateT.run_mk, StateT.run_bind, StateT.run_map,
            nativeStep, frame, marker, selected, event, Functor.map_map]
        · simp [QueryImpl.guardQueryBudget, aborted, accepted, proposed, cost,
            simulateQ_bind, StateT.run_bind]
  rw [normal] at hr
  split_ifs at hr with aborted admitted
  · simp only [support_pure, Set.mem_singleton_iff] at hr
    subst result
    exact offsets_refl _ _
  · rw [support_map] at hr
    obtain ⟨step, hstep, rfl⟩ := hr
    let input : Lab.Domain := .inl (.inl (.inr point))
    have hn : (step.1.1, (step.1.2, step.2)) ∈ support
        ((NativeCounts.nativeImpl FIPS205.core s (metadataCost true s) (.inl input)).run
          (marker, beforeRole)) := by
      rw [NativeCounts.nativeImpl, QueryImpl.flattenStateT_mapStateTBase_apply_run, support_map]
      exact ⟨step, hstep, rfl⟩
    have count (j : Coverage.TapeClass) (hj : j ≠ .other) :=
      NativeCounts.native_hmsg_count_le FIPS205.core s (metadataCost true s)
        input (marker, beforeRole) _ hn j hj
    have hs : step.2.2.1.cnt .signer ≤ beforeRole.2.1.cnt .signer := by
      simpa [marker] using count .signer (by decide)
    have hf : step.2.2.1.cnt .forger ≤ beforeRole.2.1.cnt .forger + delta := by
      simpa [marker, delta, input] using count .forger (by decide)
    have hm : step.1.2.2.1 = beforeDeferred.2.1 + selected := congrArg Prod.fst
      (NativeCounts.nativeImpl_native_metadata FIPS205.core s (metadataCost true s) input
        (marker, beforeRole) _ hn)
    refine ⟨paidSecond, hs, ?_, ?_⟩
    · change step.2.2.1.cnt .forger + beforePaid.1.1 ≤ beforeRole.2.1.cnt .forger + proposed.1
      omega
    · intro nw
      have := deltaMetadata nw
      change step.2.2.1.cnt .forger + beforeDeferred.2.1 ≤
        beforeRole.2.1.cnt .forger + step.1.2.2.1
      omega
  · simp only [support_pure, Set.mem_singleton_iff] at hr
    subst result
    exact ⟨rfl, le_rfl, le_rfl, fun _ => le_rfl⟩

private theorem execute_bind {α β : Type}
    (seed : FIPS205.core.PkSeed) (caps : Nat × Nat)
    (fallback : (input : LabCommon.Domain) → LabCommon.Range input)
    (first : OracleComp LabCommon α) (rest : α → OracleComp LabCommon β) (before : World) :
    execute seed caps fallback (first >>= rest) before = (do
      let mid ← execute seed caps fallback first before
      execute seed caps fallback (rest mid.1.1.1.1) (world mid)) := by
  simp only [execute, simulateQ_bind, StateT.run_bind]

private noncomputable abbrev markedLab (input : Lab.Domain) :=
  simulateQ commonProjection (SigningView.Events.phaseImpl A Message .verification (.inl input))

/-- The marked external verifier on one request and a proposed wire signature. -/
noncomputable abbrev verifySource (s : FIPS205.core.PkSeed) (key : PK)
    (request : Message) (wire : List Byte) : OracleComp LabCommon Bool :=
  simulateQ commonProjection
    ((SigningView.Events.viewWithEvents (commonView true s)).verify key request wire)

private theorem verifySource_eq (s : FIPS205.core.PkSeed) (key : PK)
    (request : Message) (wire : List Byte) :
    verifySource s key request wire =
      match (External.encodePureMessage request.context request.message).toOption,
          (SLHDSA.decodeSignature FIPS205.params
            (SLHDSA.Concrete.shakeWireCodec FIPS205.params.params) wire).toOption with
      | some message, some sig => simulateQ markedLab
          ((labScheme FIPS205.core (fun pk => pure pk.pkSeed) s).verify key message sig)
      | _, _ => pure false := by
  simp only [verifySource, SigningView.Events.viewWithEvents, commonView, partialView,
    SigningView.map_verify, SigningView.rejectingEncoding_verify, ite_true]
  cases frame : (External.encodePureMessage request.context request.message).toOption with
  | none => simp only [simulateQ_pure]
  | some message =>
    cases decoded : (SLHDSA.decodeSignature FIPS205.params
        (SLHDSA.Concrete.shakeWireCodec FIPS205.params.params) wire).toOption with
    | none => simp only [simulateQ_pure]
    | some sig =>
      rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose]
      congr 1
      funext input
      simp only [QueryImpl.apply_compose, simulateQ_spec_query, markedLab]

/-- A property closed under sequencing holds for the marked wire verifier when honest
construction-address hashes and message hashes at the retained public key preserve it. -/
private theorem verifySource_preserves (s : FIPS205.core.PkSeed) (root : FIPS205.core.Y)
    (request : Message) (wire : List Byte)
    (P : {α : Type} → OracleComp LabCommon α → Prop)
    (hpure : ∀ {α : Type} (x : α), P (pure x))
    (hbind : ∀ {α β : Type} {p : OracleComp LabCommon α} {f : α → OracleComp LabCommon β},
      P p → (∀ x, P (f x)) → P (p >>= f))
    (hthash : ∀ a ∈ constructionAddresses FIPS205.params, ∀ xs,
      P (markedPoint (.thash s (FIPS205.core.adrsToKey a) xs)))
    (hhmsg : ∀ r msg, P (markedPoint (.hmsg r s root msg))) :
    P (verifySource s ⟨s, root⟩ request wire) := by
  rw [verifySource_eq]
  split
  next message sig _ _ =>
    let Q {α : Type} (p : OracleComp Lab α) := P (simulateQ markedLab p)
    change Q (GeneralScheme.verifyInternalM FIPS205.params FIPS205.core
      message sig (⟨s, root⟩ : PK))
    refine verifyInternalM_pred_of_ledger (m := OracleComp Lab) (Q := @Q) ?_ ?_
      FIPS205.core message sig (⟨s, root⟩ : PK) ?_ ?_
    · intro α x
      simpa only [Q, simulateQ_pure] using hpure x
    · intro α β p f hp hf
      simpa only [Q, simulateQ_bind] using hbind hp hf
    · intro address honest values
      change P (simulateQ markedLab (liftM (Lab.query (.inl (.inl (.inr (.inl
        (.thash s (FIPS205.core.adrsToKey address) values))))))))
      simpa only [simulateQ_spec_query] using hthash address honest values
    · change P (simulateQ markedLab (liftM (Lab.query (.inl (.inl (.inr (.inl
        (.hmsg sig.randomness s root message))))))))
      simpa only [simulateQ_spec_query] using hhmsg sig.randomness message
  next => exact hpure false

/-- Wire or framing rejection returns false with every state preserved. -/
theorem verify_rejected (s : FIPS205.core.PkSeed) (key : PK) (request : Message) (wire : List Byte)
    (invalid : (External.encodePureMessage request.context request.message).toOption = none ∨
      (SLHDSA.decodeSignature FIPS205.params
        (SLHDSA.Concrete.shakeWireCodec FIPS205.params.params) wire).toOption = none)
    (caps : Nat × Nat) (fallback : (input : LabCommon.Domain) → LabCommon.Range input)
    (before : World) :
    execute s caps fallback (verifySource s key request wire) before =
      pure ((((false, (PUnit.unit, before.1)), before.2.1), before.2.2.1), before.2.2.2) := by
  rw [verifySource_eq]
  rcases invalid with frame | decoded
  · simp [frame, execute]
  · cases frame : (External.encodePureMessage request.context request.message).toOption <;>
      simp [decoded, execute]

/-- Paid reserve funds all complete verifier digest calls. The selected-message counter
funds them when the encoded public key avoids the weak-key exception. -/
theorem marked_verify_count_offsets (s : FIPS205.core.PkSeed) (root : FIPS205.core.Y)
    (request : Message) (wire : List Byte) (caps : Nat × Nat)
    (fallback : (input : LabCommon.Domain) → LabCommon.Range input)
    (before : World) (result : Result Bool)
    (member : result ∈ support (execute s caps fallback
      (verifySource s ⟨s, root⟩ request wire) before)) :
    offsets (¬IsWeakKey FIPS205.params (⟨s, root⟩ : PK)) before (world result) := by
  let P {α : Type} (p : OracleComp LabCommon α) := ∀ st (out : Result α),
    out ∈ support (execute s caps fallback p st) →
      offsets (¬IsWeakKey FIPS205.params (⟨s, root⟩ : PK)) st (world out)
  refine verifySource_preserves s root request wire (@P) ?_ ?_
    (fun a _ xs =>
      point_offsets s root (.thash s (FIPS205.core.adrsToKey a) xs) trivial caps fallback)
    (fun r msg => point_offsets s root (.hmsg r s root msg) ⟨rfl, rfl⟩ caps fallback)
    before result member
  · intro α x st out mem
    simp only [execute, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at mem
    exact mem ▸ offsets_refl _ _
  · intro α β p f hp hf st out mem
    rw [execute_bind, mem_support_bind_iff] at mem
    obtain ⟨mid, hm, hz⟩ := mem
    exact offsets_trans (hp st mid hm) (hf _ (world mid) out hz)

end VerificationOffsets
end SLHDSA.SHAKE128s.Bridge.SharedExperiment

open SLHDSA.SHAKE128s.Bridge.SharedExperiment.VerificationOffsets
