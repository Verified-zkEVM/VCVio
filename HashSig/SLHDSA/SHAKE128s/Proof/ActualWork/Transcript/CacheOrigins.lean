/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Coupling.Guarded
public import HashSig.SLHDSA.Security.ByteClash
import HashSig.SLHDSA.Security.SecretTraces
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

public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Transcript.KeygenOrigins
import all HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Transcript.KeygenOrigins

/-! # Public and private cache entries in a guarded signing transcript -/

public section

section

open OracleComp OracleSpec SignatureAlg
open SLHDSA SLHDSA.Security SLHDSA.SHAKE128s
open SLHDSA.SHAKE128s.Bridge.SharedExperiment.Guarded
namespace SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native

/-- The existing raw encoding is a fixed point of the actual router at the initial seed. -/
@[expose] def RouteFixed (s : FIPS205.core.PkSeed) (q : H.Domain) : Prop :=
  shakeRoute FIPS205.params (IsHonestKey FIPS205.params FIPS205.core) s
    (encode FIPS205.params q) = some q

/-- A public query is raw-routed or is the honest Hmsg at the retained initial public key. -/
@[expose] def PublicProvenanceInput (s : FIPS205.core.PkSeed) (initialPK : PK) (q : H.Domain) :
  Prop :=
  RouteFixed s q ∨ ∃ r msg, q = .inl (.hmsg r s initialPK.pkRoot msg)

/-- Existing cells use honest secret addresses; nonce activation is funded by actual Paid. -/
@[expose] def PrivateProvenanceCell (paid : Paid) :
    DeriveQuery FIPS205.core ⊕ NodeKey FIPS205.core → Prop
  | .inl (.inl k) => IsHonestKey FIPS205.params FIPS205.core k.1
  | .inl (.inr _) => 1 ≤ paid.1.2
  | .inr _ => True

/-- Provenance on the existing public cache, private cache and pending cells. -/
@[expose] def NativeStateProvenance (s : FIPS205.core.PkSeed) (initialPK : PK) (paid : Paid)
    (state : CoverageDeferred.D FIPS205.core) : Prop :=
  initialPK.pkSeed = s ∧
    (∀ q, (state.1.1 q).isSome → PublicProvenanceInput s initialPK q) ∧
    ∀ cell, (state.1.2 cell).isSome ∨ cell ∈ state.2 → PrivateProvenanceCell paid cell

/-- The local source restriction constrains public queries, private reads and all touches. -/
@[expose] def NativeProvenanceInput (s : FIPS205.core.PkSeed) (initialPK : PK) (paid : Paid) :
    Lab.Domain → Prop
  | .inl (.inl (.inl _)) => True
  | .inl (.inl (.inr q)) => PublicProvenanceInput s initialPK q
  | .inl (.inr derive) => PrivateProvenanceCell paid (.inl derive)
  | .inr (.inl cell) => PrivateProvenanceCell paid cell
  | .inr (.inr _) => True

end SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native

end

section

open OracleComp OracleSpec SignatureAlg
open SLHDSA SLHDSA.Security SLHDSA.SHAKE128s
open SLHDSA.SHAKE128s.Bridge.SharedExperiment.Guarded
namespace SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native

/-- Every successful raw route yields the actual encode/route fixed-point branch. -/
theorem routeFixed_of_route_eq_some
    (s : FIPS205.core.PkSeed) (bytes : List Byte) (q : H.Domain)
    (hroute : (encoding s).route bytes = some q) : RouteFixed s q := by
  change shakeRoute FIPS205.params (IsHonestKey FIPS205.params FIPS205.core) s bytes =
    some q at hroute
  have hencode := encode_eq_of_shakeRoute_eq_some hroute
  simpa only [RouteFixed, hencode] using hroute

namespace Provenance

/-- Updating only the actual public query preserves public provenance. -/
private theorem public_cache_update
    (s : FIPS205.core.PkSeed) (initialPK : PK) (cache : H.QueryCache)
    (q : H.Domain) (answer : H.Range q)
    (hq : PublicProvenanceInput s initialPK q)
    (hc : ∀ point, (cache point).isSome → PublicProvenanceInput s initialPK point) :
    ∀ point, ((cache.cacheQuery q answer) point).isSome →
      PublicProvenanceInput s initialPK point := by
  intro point hp
  by_cases heq : point = q
  · exact heq.symm ▸ hq
  · rw [QueryCache.cacheQuery_of_ne _ _ heq] at hp
    exact hc point hp

/-- Updating only the supplied cell preserves drawn-or-pending provenance. -/
private theorem private_cache_update
    (s : FIPS205.core.PkSeed) (initialPK : PK) (paid : Paid)
    (state : CoverageDeferred.D FIPS205.core)
    (cell : DeriveQuery FIPS205.core ⊕ NodeKey FIPS205.core)
    (answer : FIPS205.core.Y)
    (hc : PrivateProvenanceCell paid cell)
    (hs : NativeStateProvenance s initialPK paid state) :
    NativeStateProvenance s initialPK paid
      ((state.1.1, state.1.2.cacheQuery cell answer), state.2) := by
  refine ⟨hs.1, hs.2.1, ?_⟩
  intro other hother
  rcases hother with hdrawn | hpending
  · by_cases heq : other = cell
    · exact heq.symm ▸ hc
    · rw [QueryCache.cacheQuery_of_ne _ _ heq] at hdrawn
      exact hs.2.2 other (.inl hdrawn)
  · exact hs.2.2 other (.inr hpending)

/-- Drawing a permitted cell leaves the public cache and every other cell unchanged. -/
private theorem draw_preserves
    (s : FIPS205.core.PkSeed) (initialPK : PK) (paid : Paid)
    (state : CoverageDeferred.D FIPS205.core)
    (cell : DeriveQuery FIPS205.core ⊕ NodeKey FIPS205.core)
    (hc : PrivateProvenanceCell paid cell)
    (hs : NativeStateProvenance s initialPK paid state)
    {out : FIPS205.core.Y × LabState FIPS205.core}
    (hout : out ∈ support ((RelabelState.drawCell cell).run state.1)) :
    NativeStateProvenance s initialPK paid (out.2, state.2) := by
  have hpublic : out.2.1 = state.1.1 := by
    rw [RelabelState.drawCell_run, support_map] at hout
    obtain ⟨w, _, rfl⟩ := hout
    rfl
  refine ⟨hs.1, ?_, ?_⟩
  · simpa only [hpublic] using hs.2.1
  · intro other hother
    rcases hother with hdrawn | hpending
    · by_cases heq : other = cell
      · exact heq.symm ▸ hc
      · have hunchanged := RelabelState.cell_eq_of_mem_support_drawCell hout heq
        exact hs.2.2 other (.inl (hunchanged ▸ hdrawn))
    · exact hs.2.2 other (.inr hpending)

/-- The existing deferred handler introduces only its public point or supplied private cell. -/
private theorem deferred_preserves
    (s : FIPS205.core.PkSeed) (initialPK : PK) (paid : Paid)
    (input : Lab.Domain) (hi : NativeProvenanceInput s initialPK paid input)
    (state : CoverageDeferred.D FIPS205.core)
    (hs : NativeStateProvenance s initialPK paid state)
    {out : Lab.Range input × CoverageDeferred.D FIPS205.core}
    (hout : out ∈ support (((slhGraph FIPS205.core s).deferredImpl input).run state)) :
    NativeStateProvenance s initialPK paid out.2 := by
  rcases input with (((sample | point) | derive) | (touch | node))
  · rw [CanonicalGraph.deferredImpl_run_inl, CanonicalGraph.relabelImpl_run_unif,
      support_map, support_map] at hout
    obtain ⟨w, hw, rfl⟩ := hout
    obtain ⟨_, _, rfl⟩ := hw
    exact hs
  · rw [CanonicalGraph.deferredImpl_run_inl, support_map] at hout
    obtain ⟨w, hw, rfl⟩ := hout
    by_cases hpoint : ∃ k values,
        (slhGraph FIPS205.core s).childVals state.1 k = some values ∧
          (slhGraph FIPS205.core s).pt k values = point
    · obtain ⟨k, values, hk, rfl⟩ := hpoint
      rw [CanonicalGraph.relabelImpl_run_pt (slhGraph FIPS205.core s) hk, support_map] at hw
      obtain ⟨z, hz, rfl⟩ := hw
      exact draw_preserves s initialPK paid state (.inr k) trivial hs hz
    · rw [CanonicalGraph.relabelImpl_run_pub_of_not_exists (slhGraph FIPS205.core s)
          hpoint, support_map] at hw
      obtain ⟨z, hz, rfl⟩ := hw
      refine ⟨hs.1, ?_, hs.2.2⟩
      intro q hq
      rcases (QueryImpl.withCaching_run_isSome_apply_iff _ hz q).1 hq with hold | hnew
      · exact hs.2.1 q hold
      · subst q
        exact hi
  · rw [CanonicalGraph.deferredImpl_run_inl, support_map] at hout
    obtain ⟨w, hw, rfl⟩ := hout
    rw [CanonicalGraph.relabelImpl_apply_inr] at hw
    exact draw_preserves s initialPK paid state (.inl derive) hi hs hw
  · rw [CanonicalGraph.deferredImpl_run_touch, support_pure,
      Set.mem_singleton_iff] at hout
    subst out
    refine ⟨hs.1, hs.2.1, ?_⟩
    intro cell hc
    rcases hc with hdrawn | hpending
    · exact hs.2.2 cell (.inl hdrawn)
    · rcases List.mem_append.mp hpending with hold | hnew
      · exact hs.2.2 cell (.inr hold)
      · have heq : cell = touch := List.mem_singleton.mp hnew
        exact heq.symm ▸ hi
  · rw [CanonicalGraph.deferredImpl_run_read, support_map] at hout
    obtain ⟨w, hw, rfl⟩ := hout
    exact draw_preserves s initialPK paid state (.inr node) trivial hs hw

/-- Lifting the deferred step and pairing unchanged metadata preserves the same invariant. -/
private theorem lifted_source_step
    (s : FIPS205.core.PkSeed) (initialPK : PK) (paid : Paid)
    (input : Lab.Domain) (hi : NativeProvenanceInput s initialPK paid input)
    (state : CoverageDeferred.S FIPS205.core)
    (hs : NativeStateProvenance s initialPK paid state.1)
    {out : Lab.Range input × CoverageDeferred.S FIPS205.core}
    (hout : out ∈ support
      ((fun z => (z.1, (z.2, state.2))) <$>
        liftComp (((slhGraph FIPS205.core s).deferredImpl input).run state.1)
          (Coverage.roleSpec FIPS205.core))) :
    NativeStateProvenance s initialPK paid out.2.1 ∧ out.2.2 = state.2 := by
  rw [support_map] at hout
  obtain ⟨z, hz, rfl⟩ := hout
  have hsource := mem_support_of_mem_support_liftComp (Coverage.roleSpec FIPS205.core) _ _ hz
  exact ⟨deferred_preserves s initialPK paid input hi state.1 hs hsource, rfl⟩

/-- The explicit selected Hmsg/nonce branches mirror only their supplied point or cell. -/
private theorem relative_source_step
    (s : FIPS205.core.PkSeed) (initialPK : PK) (paid : Paid)
    (input : Lab.Domain) (hi : NativeProvenanceInput s initialPK paid input)
    (state : CoverageDeferred.S FIPS205.core)
    (hs : NativeStateProvenance s initialPK paid state.1)
    {out : Lab.Range input × CoverageDeferred.S FIPS205.core}
    (hout : out ∈ support ((CoverageDeferred.relative FIPS205.core s
      (metadataCost true s) (.inl input)).run state)) :
    NativeStateProvenance s initialPK paid out.2.1 ∧ out.2.2 = state.2 := by
  rcases input with (((sample | (hash | prf)) | (secret | nonce)) | (touch | node))
  · apply lifted_source_step s initialPK paid _ hi state hs
    simpa only [CoverageDeferred.relative, StateT.run_mk, map_eq_bind_pure_comp,
      Function.comp_def] using hout
  · cases hash with
    | thash seed address values =>
      apply lifted_source_step s initialPK paid _ hi state hs
      simpa only [CoverageDeferred.relative, StateT.run_mk, map_eq_bind_pure_comp,
        Function.comp_def] using hout
    | hmsg R seed root message =>
      rw [CoverageDeferred.relative_hmsg, mem_support_bind_iff] at hout
      obtain ⟨digest, _, hout⟩ := hout
      rw [support_pure, Set.mem_singleton_iff] at hout
      subst out
      exact ⟨⟨hs.1, public_cache_update s initialPK _ _ _ hi hs.2.1, hs.2.2⟩, rfl⟩
  · apply lifted_source_step s initialPK paid _ hi state hs
    simpa only [CoverageDeferred.relative, StateT.run_mk, map_eq_bind_pure_comp,
      Function.comp_def] using hout
  · apply lifted_source_step s initialPK paid _ hi state hs
    simpa only [CoverageDeferred.relative, StateT.run_mk, map_eq_bind_pure_comp,
      Function.comp_def] using hout
  · rcases nonce with ⟨salt, message⟩
    rw [CoverageDeferred.relative_rand, support_map] at hout
    obtain ⟨R, _, rfl⟩ := hout
    exact ⟨private_cache_update s initialPK paid state.1 _ R hi hs, rfl⟩
  · apply lifted_source_step s initialPK paid _ hi state hs
    simpa only [CoverageDeferred.relative, StateT.run_mk, map_eq_bind_pure_comp,
      Function.comp_def] using hout
  · apply lifted_source_step s initialPK paid _ hi state hs
    simpa only [CoverageDeferred.relative, StateT.run_mk, map_eq_bind_pure_comp,
      Function.comp_def] using hout

end Provenance

/-- A restricted lab input preserves both caches and pending provenance under actual roles.
The existing Paid component is held fixed during this native input; marker entry is separate. -/
theorem native_lab_query_preserves_provenance
    (s : FIPS205.core.PkSeed) (initialPK : PK) (paid : Paid)
    (input : Lab.Domain) (hi : NativeProvenanceInput s initialPK paid input)
    (state : CoverageDeferred.S FIPS205.core)
    (hs : NativeStateProvenance s initialPK paid state.1)
    (role : Coverage.RoleState FIPS205.core) :
    ∀ result ∈ support ((simulateQ (Coverage.roleRunImpl FIPS205.core)
      ((CoverageDeferred.relative FIPS205.core s (metadataCost true s)
        (.inl input)).run state)).run role),
      NativeStateProvenance s initialPK paid result.1.2.1 ∧
        result.1.2.2 = state.2 := by
  intro result hr
  have houtput : result.1 ∈ support ((simulateQ (Coverage.roleRunImpl FIPS205.core)
      ((CoverageDeferred.relative FIPS205.core s (metadataCost true s)
        (.inl input)).run state)).run' role) := by
    rw [StateT.run'_eq, support_map]
    exact ⟨result, hr, rfl⟩
  have hsource := support_simulateQ_run'_subset (Coverage.roleRunImpl FIPS205.core)
    ((CoverageDeferred.relative FIPS205.core s (metadataCost true s)
      (.inl input)).run state) role houtput
  exact Provenance.relative_source_step s initialPK paid input hi state hs hsource

namespace Provenance

/-- Increasing actual admitted attempts preserves every existing nonce activation witness. -/
private theorem state_mono_paid
    (s : FIPS205.core.PkSeed) (initialPK : PK) (paid paid' : Paid)
    (state : CoverageDeferred.D FIPS205.core)
    (hpaid : paid.1.2 ≤ paid'.1.2)
    (hs : NativeStateProvenance s initialPK paid state) :
    NativeStateProvenance s initialPK paid' state := by
  refine ⟨hs.1, hs.2.1, ?_⟩
  intro cell hc
  have hold := hs.2.2 cell hc
  rcases cell with (key | nonce) | node
  · exact hold
  · exact hold.trans hpaid
  · trivial

end Provenance

/-- The real free-guard signing-attempt entry either charges one attempt or freezes native work.
This statement carries the actual existing raw, deferred, role and Paid states. -/
theorem native_signing_entry_preserves_provenance
    (s : FIPS205.core.PkSeed) (initialPK : PK)
    (reserve : Bool) (caps : Nat × Nat)
    (fallback : (input : LabCommon.Domain) → LabCommon.Range input)
    (request : Message) (raw : Raw.QueryCache)
    (state : CoverageDeferred.S FIPS205.core)
    (role : Coverage.RoleState FIPS205.core) (paid : Paid)
    (hs : NativeStateProvenance s initialPK paid state.1) :
    letI : MonadLiftT (OracleComp LabCommon) (StateT PUnit (OracleComp LabCommon)) :=
      ⟨fun action => StateT.lift action⟩
    let forwarder := (QueryImpl.id' LabCommon).liftTarget
      (StateT PUnit (OracleComp LabCommon))
    let guarded := (simulateQ (QueryImpl.guardQueryBudget caps
      (Sum.elim (fun _ : A.Domain => (0, 0)) (policy reserve s)) forwarder fallback)
      (liftM (LabCommon.query (.inr (.signingAttempt request))))).run (PUnit.unit, paid)
    let entry := (simulateQ (Coverage.roleRunImpl FIPS205.core)
      ((simulateQ (CoverageDeferred.relative FIPS205.core s (metadataCost true s))
        ((simulateQ (routeLab s) guarded).run raw)).run state)).run role
    ∀ result ∈ support entry,
      let paid' := result.1.1.1.2.2
      let state' := result.1.2
      let admitted := paid.2 = false ∧ paid.1 + policy reserve s (.signingAttempt request) ≤ caps
      result.1.1.2 = raw ∧ state'.1 = state.1 ∧ result.2 = role ∧
      paid' = (if admitted then (paid.1 + policy reserve s (.signingAttempt request), false)
        else (paid.1, true)) ∧
      state'.2 = (if admitted then (state.2.1, .signer) else state.2) ∧
      NativeStateProvenance s initialPK paid' state'.1 ∧
      (admitted → 1 ≤ paid'.1.2) := by
  let _ : MonadLiftT (OracleComp.{0, 0, 0} LabCommon)
      (StateT PUnit.{1} (OracleComp.{0, 0, 0} LabCommon)) :=
    ⟨fun action => StateT.lift action⟩
  classical
  dsimp only
  intro result hr
  let admitted := paid.2 = false ∧ paid.1 + policy reserve s (.signingAttempt request) ≤ caps
  let paid' : Paid := if admitted then
    (paid.1 + policy reserve s (.signingAttempt request), false) else (paid.1, true)
  let metadata' : Meta := if admitted then (state.2.1, .signer) else state.2
  have hf : fallback (.inr (.signingAttempt request)) = PUnit.unit := by
    exact Subsingleton.elim (α := PUnit) _ _
  have hsecond : (policy reserve s (.signingAttempt request)).2 = 1 := by
    cases reserve <;> simp [policy, originalPolicy, reserveExtra,
      Game.Counted.sourcePolicy]
  have heq : result =
      ((((PUnit.unit, (PUnit.unit, paid')), raw), (state.1, metadata')), role) := by
    by_cases hflag : paid.2 = true
    · have samePaid : (paid.1, true) = paid := by
        apply Prod.ext
        · rfl
        · exact hflag.symm
      simpa [QueryImpl.guardQueryBudget, hflag, hf, routeLab, QueryImpl.add,
        QueryImpl.id', QueryImpl.liftTarget, simulateQ_pure, StateT.run_pure,
        admitted, paid', metadata', samePaid] using hr
    · have hfalse : paid.2 = false := Bool.eq_false_iff.mpr hflag
      by_cases hfit : paid.1 + policy reserve s (.signingAttempt request) ≤ caps
      · simpa [QueryImpl.guardQueryBudget, hfalse, hfit, hf, routeLab, QueryImpl.add,
          QueryImpl.id', QueryImpl.liftTarget, CoverageDeferred.relative,
          CoverageDeferred.phaseCostAux, metadataCost, selectedRaw,
          simulateQ_pure, StateT.run_pure, admitted, paid', metadata'] using hr
      · simpa [QueryImpl.guardQueryBudget, hfalse, hfit, hf, routeLab, QueryImpl.add,
          QueryImpl.id', QueryImpl.liftTarget, simulateQ_pure, StateT.run_pure,
          admitted, paid', metadata'] using hr
  subst result
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · apply Provenance.state_mono_paid s initialPK paid paid' state.1 _ hs
    by_cases ha : admitted <;> simp only [paid', ha, ↓reduceIte, Prod.snd_add]
    · rw [hsecond]
      exact Nat.le_succ _
    · exact le_rfl
  · change admitted → 1 ≤ paid'.1.2
    intro ha
    simp only [paid', ite_eq_left ha, Prod.snd_add, hsecond]
    exact Nat.succ_pos _

namespace Provenance

private def NoPublicInput : Lab.Domain → Prop
  | .inl (.inl _) => False
  | _ => True

/-- The existing generic sign elimination exposes its sole public Hmsg before private work. -/
private theorem internal_sign_inputs
    (s : FIPS205.core.PkSeed) (root R : FIPS205.core.Y) (paid : Paid) (msg : List Byte) :
    let key : PK := ⟨s, root⟩
    AllQueriesSatisfy (labSignInternal FIPS205.core s msg root R)
      (NativeProvenanceInput s key paid) := by
  let publicOnly : Lab.Domain → Prop
    | .inl (.inl (.inr q)) => q = .inl (.hmsg R s root msg)
    | _ => True
  have hpublic : AllQueriesSatisfy (labSignInternal FIPS205.core s msg root R) publicOnly := by
    refine labSignInternal_pred_of_hmsg_bind FIPS205.core
      (Q := fun oa => AllQueriesSatisfy oa NoPublicInput)
      (P := fun oa => AllQueriesSatisfy oa publicOnly)
      (fun _ => allQueriesSatisfy_pure _ _)
      (fun _ _ => allQueriesSatisfy_bind) ?_ ?_ s msg root R ?_
    · intro cell
      exact (allQueriesSatisfy_query_iff _ _).2 trivial
    · rintro (derive | node) <;> exact (allQueriesSatisfy_query_iff _ _).2 trivial
    · intro rest hrest
      refine allQueriesSatisfy_bind ((allQueriesSatisfy_query_iff _ _).2 rfl) fun digest => ?_
      exact (hrest digest).mono (by
        rintro (((sample | point) | derive) | (touch | node)) hi
        · exact hi.elim
        · exact hi.elim
        · trivial
        · trivial
        · trivial)
  have hstruct := SLHDSA.Security.NativeProvenance.lab_internal_sign_structural
    FIPS205.core s msg root R
  refine (hstruct.and hpublic).mono ?_
  rintro (((sample | point) | (secret | nonce)) | (touch | node)) hi
  · trivial
  · exact Or.inr ⟨R, msg, hi.2⟩
  · exact hi.1
  · exact hi.1.elim
  · rcases touch with (secret | nonce) | node
    · exact hi.1
    · exact hi.1.elim
    · trivial
  · trivial

end Provenance

/-- After actual entry funding, honest signing satisfies the same local input restriction. -/
theorem lab_sign_inputs_of_paid_attempt
    (s : FIPS205.core.PkSeed) (root : FIPS205.core.Y) (paid : Paid)
    (hpaid : 1 ≤ paid.1.2) (msg : List Byte) :
    let key : PK := ⟨s, root⟩
    AllQueriesSatisfy
      ((labScheme FIPS205.core (fun pk => pure pk.pkSeed) s).sign key key msg)
      (NativeProvenanceInput s key paid) := by
  dsimp only
  change AllQueriesSatisfy
    ((query (spec := Lab) (.inl (.inr (.inr (s, msg))))) >>= fun R =>
      labSignInternal FIPS205.core s msg root R)
    (NativeProvenanceInput s (⟨s, root⟩ : PK) paid)
  refine allQueriesSatisfy_bind ((allQueriesSatisfy_query_iff _ _).2 hpaid) fun R => ?_
  exact Provenance.internal_sign_inputs s root R paid msg

/-- Honest verification has the retained-root Hmsg and route-fixed public hash inputs. -/
theorem lab_verify_inputs
    (s : FIPS205.core.PkSeed) (root : FIPS205.core.Y) (paid : Paid)
    (msg : List Byte) (sig : GeneralScheme.SignatureCore FIPS205.params FIPS205.core) :
    let key : PK := ⟨s, root⟩
    AllQueriesSatisfy
      ((labScheme FIPS205.core (fun pk => pure pk.pkSeed) s).verify key msg sig)
      (NativeProvenanceInput s key paid) := by
  change AllQueriesSatisfy
    (GeneralScheme.verifyInternalM FIPS205.params FIPS205.core msg sig (⟨s, root⟩ : PK) :
      OracleComp Lab Bool) _
  refine verifyInternalM_pred_of_ledger (m := OracleComp Lab)
    (Q := fun p => AllQueriesSatisfy p (NativeProvenanceInput s (⟨s, root⟩ : PK) paid))
    (fun _ => allQueriesSatisfy_pure _ _) (fun _ _ => allQueriesSatisfy_bind)
    FIPS205.core msg sig (⟨s, root⟩ : PK) ?_ ?_
  · intro a ha xs
    apply (allQueriesSatisfy_query_iff _ _).2
    exact Or.inl (shakeRoute_encode_thash _ _ ⟨a, Or.inl ha, rfl⟩)
  · exact (allQueriesSatisfy_query_iff _ _).2 (Or.inr ⟨sig.randomness, msg, rfl⟩)

end SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native

namespace SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native.Provenance

/-- The actual table router sends every typed input through its encode/route fixed point. -/
private theorem tableRouter_inputs
    (s : FIPS205.core.PkSeed) (initialPK : PK) (paid : Paid)
    (bytes : List Byte) (raw : Raw.QueryCache) :
    AllQueriesSatisfy
      (simulateQ (QueryImpl.ofLift (unifSpec + H) (OracleComp (Lab + O)))
        (((encoding s).tableRouter bytes).run raw))
      (Sum.elim (NativeProvenanceInput s initialPK paid) (fun _ => True)) := by
  refine (OracleComp.RandomOracleEncoding.allQueriesSatisfy_run_tableRouter
    (E := encoding s) bytes raw).simulateQ
      (impl := QueryImpl.ofLift (unifSpec + H) (OracleComp (Lab + O))) ?_
  rintro (sample | point) hi
  · change AllQueriesSatisfy
      (query (spec := Lab + O) (m := OracleComp (Lab + O)) (.inl (.inl (.inl (.inl sample)))))
      (Sum.elim (NativeProvenanceInput s initialPK paid) (fun _ => True))
    exact (allQueriesSatisfy_query_iff _ _).2 trivial
  · have inputEq :
        QueryImpl.ofLift (unifSpec + H) (OracleComp (Lab + O)) (.inr point) =
        (liftM ((Lab + O).query (.inl (.inl (.inl (.inr point))))) :
          OracleComp (Lab + O) (H.Range point)) := by
      rcases point with (⟨seed, key, inputs⟩ | ⟨randomness, seed, root, message⟩) | nonce <;>
        rfl
    rw [inputEq]
    exact (allQueriesSatisfy_query_iff (spec := Lab + O) _ _).2 (Or.inl hi)

end SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native.Provenance

namespace SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native.Provenance

/-- The existing nested native interpretation equals one free guard on the linked state.
Every native cache, pending cell, raw table, metadata, role state and Paid component is retained. -/
private theorem native_guarded_frontend
    {alpha : Type} (s : FIPS205.core.PkSeed) (reserve : Bool) (caps : Nat × Nat)
    (fallback : (input : LabCommon.Domain) → LabCommon.Range input)
    (program : OracleComp LabCommon alpha) (raw : Raw.QueryCache)
    (state : CoverageDeferred.S FIPS205.core)
    (role : Coverage.RoleState FIPS205.core) (paid : Paid) :
    letI : MonadLiftT (OracleComp LabCommon) (StateT PUnit (OracleComp LabCommon)) :=
      ⟨fun action => StateT.lift action⟩
    let charge := Sum.elim (fun _ : A.Domain => (0, 0)) (policy reserve s)
    let relative := CoverageDeferred.relative FIPS205.core s (metadataCost true s)
    let roles := Coverage.roleRunImpl FIPS205.core
    let native := QueryImpl.Stateful.link relative roles
    let routed := QueryImpl.Stateful.link (routeLab s) native
    let forwarder := (QueryImpl.id' LabCommon).liftTarget
      (StateT PUnit (OracleComp LabCommon))
    let guarded := (simulateQ (QueryImpl.guardQueryBudget caps charge forwarder fallback)
      program).run (PUnit.unit, paid)
    let nested := (simulateQ roles
      ((simulateQ relative ((simulateQ (routeLab s) guarded).run raw)).run state)).run role
    let reshape := fun z :
        (((alpha × (PUnit × Paid)) × Raw.QueryCache) ×
          CoverageDeferred.S FIPS205.core) × Coverage.RoleState FIPS205.core =>
      (z.1.1.1.1, ((z.1.1.2, (z.1.2, z.2)), z.1.1.1.2.2))
    reshape <$> nested =
      (simulateQ (QueryImpl.guardQueryBudget caps charge routed fallback) program).run
        ((raw, (state, role)), paid) := by
  let _ : MonadLiftT (OracleComp.{0, 0, 0} LabCommon)
      (StateT PUnit.{1} (OracleComp.{0, 0, 0} LabCommon)) :=
    ⟨fun action => StateT.lift action⟩
  dsimp only
  let relative := CoverageDeferred.relative FIPS205.core s (metadataCost true s)
  let roles := Coverage.roleRunImpl FIPS205.core
  let native := QueryImpl.Stateful.link relative roles
  let routed := QueryImpl.Stateful.link (routeLab s) native
  let charge := Sum.elim (fun _ : A.Domain => (0, 0)) (policy reserve s)
  have h := QueryImpl.map_run_simulateQ_guardQueryBudget_free_eq caps charge
    routed fallback program (raw, (state, role)) paid.1 paid.2
  simpa only [routed, native, QueryImpl.Stateful.simulateQ_link_run,
    QueryImpl.Stateful.Frame.linkReshape, QueryImpl.Stateful.Frame.prod,
    Functor.map_map, Function.comp_def, Prod.map, id_eq, Equiv.coe_fn_mk,
    PFunctor.Lens.State.fst_put, PFunctor.Lens.State.snd_put, relative, roles, charge] using h

/-- An already aborted guard freezes all native state even for an unrestricted source program. -/
private theorem native_aborted_program_state
    {alpha : Type} (s : FIPS205.core.PkSeed) (reserve : Bool) (caps : Nat × Nat)
    (fallback : (input : LabCommon.Domain) → LabCommon.Range input)
    (program : OracleComp LabCommon alpha) (raw : Raw.QueryCache)
    (state : CoverageDeferred.S FIPS205.core)
    (role : Coverage.RoleState FIPS205.core) (counts : Nat × Nat) :
    letI : MonadLiftT (OracleComp LabCommon) (StateT PUnit (OracleComp LabCommon)) :=
      ⟨fun action => StateT.lift action⟩
    let forwarder := (QueryImpl.id' LabCommon).liftTarget
      (StateT PUnit (OracleComp LabCommon))
    let guarded := (simulateQ (QueryImpl.guardQueryBudget caps
      (Sum.elim (fun _ : A.Domain => (0, 0)) (policy reserve s)) forwarder fallback)
      program).run (PUnit.unit, (counts, true))
    let run := (simulateQ (Coverage.roleRunImpl FIPS205.core)
      ((simulateQ (CoverageDeferred.relative FIPS205.core s (metadataCost true s))
        ((simulateQ (routeLab s) guarded).run raw)).run state)).run role
    ∀ result ∈ support run,
      result.1.1.2 = raw ∧ result.1.2 = state ∧ result.2 = role ∧
        result.1.1.1.2.2 = (counts, true) := by
  let _ : MonadLiftT (OracleComp.{0, 0, 0} LabCommon)
      (StateT PUnit.{1} (OracleComp.{0, 0, 0} LabCommon)) :=
    ⟨fun action => StateT.lift action⟩
  classical
  dsimp only
  intro result hr
  let relative := CoverageDeferred.relative FIPS205.core s (metadataCost true s)
  let roles := Coverage.roleRunImpl FIPS205.core
  let native := QueryImpl.Stateful.link relative roles
  let routed := QueryImpl.Stateful.link (routeLab s) native
  let charge := Sum.elim (fun _ : A.Domain => (0, 0)) (policy reserve s)
  let handler := QueryImpl.guardQueryBudget caps charge routed fallback
  let initial := ((raw, (state, role)), (counts, true))
  let reshape := fun z :
      (((alpha × (PUnit × Paid)) × Raw.QueryCache) ×
        CoverageDeferred.S FIPS205.core) × Coverage.RoleState FIPS205.core =>
    (z.1.1.1.1, ((z.1.1.2, (z.1.2, z.2)), z.1.1.1.2.2))
  have frontend :
      reshape <$> (simulateQ roles
        ((simulateQ relative
          ((simulateQ (routeLab s)
            ((simulateQ (QueryImpl.guardQueryBudget caps charge
              ((QueryImpl.id' LabCommon).liftTarget (StateT PUnit (OracleComp LabCommon)))
              fallback) program).run (PUnit.unit, (counts, true)))).run raw)).run state)).run role =
      (simulateQ handler program).run initial := by
    simpa only [reshape, handler, initial, routed, native, relative, roles, charge] using
      native_guarded_frontend s reserve caps fallback program raw state role (counts, true)
  have step : QueryImpl.PreservesInv handler (fun current => current = initial) := by
    intro input before hbefore output hout
    subst before
    change output ∈ support (pure (fallback input, initial) : ProbComp _) at hout
    rw [support_pure, Set.mem_singleton_iff] at hout
    exact congrArg Prod.snd hout
  have hresult : reshape result ∈ support ((simulateQ handler program).run initial) := by
    rw [← frontend, support_map]
    exact ⟨result, hr, rfl⟩
  have hfinal := OracleComp.simulateQ_run_preservesInv handler
    (fun current => current = initial) step program initial rfl (reshape result) hresult
  exact ⟨congrArg (fun current => current.1.1) hfinal,
    congrArg (fun current => current.1.2.1) hfinal,
    congrArg (fun current => current.1.2.2) hfinal,
    congrArg (fun current => current.2) hfinal⟩

end SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native.Provenance

namespace SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native.Provenance

/-- A source with permitted native inputs preserves provenance under the actual nested guard.
The predicate is an internal program obligation; raw inputs and marker events remain arbitrary. -/
private theorem native_guarded_program_preserves_provenance
    {alpha : Type} (s : FIPS205.core.PkSeed) (initialPK : PK)
    (reserve : Bool) (caps : Nat × Nat)
    (fallback : (input : LabCommon.Domain) → LabCommon.Range input)
    (program : OracleComp LabCommon alpha)
    (raw : Raw.QueryCache) (state : CoverageDeferred.S FIPS205.core)
    (role : Coverage.RoleState FIPS205.core) (paid : Paid)
    (hs : NativeStateProvenance s initialPK paid state.1)
    (hprogram : AllQueriesSatisfy program
      (Sum.elim (Sum.elim (NativeProvenanceInput s initialPK paid) (fun _ => True))
        (fun _ => True))) :
    letI : MonadLiftT (OracleComp LabCommon) (StateT PUnit (OracleComp LabCommon)) :=
      ⟨fun action => StateT.lift action⟩
    let forwarder := (QueryImpl.id' LabCommon).liftTarget
      (StateT PUnit (OracleComp LabCommon))
    let guarded := (simulateQ (QueryImpl.guardQueryBudget caps
      (Sum.elim (fun _ : A.Domain => (0, 0)) (policy reserve s)) forwarder fallback)
      program).run (PUnit.unit, paid)
    let run := (simulateQ (Coverage.roleRunImpl FIPS205.core)
      ((simulateQ (CoverageDeferred.relative FIPS205.core s (metadataCost true s))
        ((simulateQ (routeLab s) guarded).run raw)).run state)).run role
    ∀ result ∈ support run,
      let paid' := result.1.1.1.2.2
      let state' := result.1.2
      NativeStateProvenance s initialPK paid' state'.1 ∧ paid.1.2 ≤ paid'.1.2
 := by
  let _ : MonadLiftT (OracleComp.{0, 0, 0} LabCommon)
      (StateT PUnit.{1} (OracleComp.{0, 0, 0} LabCommon)) :=
    ⟨fun action => StateT.lift action⟩
  classical
  dsimp only
  intro result hr
  let relative := CoverageDeferred.relative FIPS205.core s (metadataCost true s)
  let roles := Coverage.roleRunImpl FIPS205.core
  let native := QueryImpl.Stateful.link relative roles
  let routed := QueryImpl.Stateful.link (routeLab s) native
  let charge := Sum.elim (fun _ : A.Domain => (0, 0)) (policy reserve s)
  let guardedHandler := QueryImpl.guardQueryBudget caps charge routed fallback
  let initialCache := (raw, (state, role))
  let Inv := fun world :
      (Raw.QueryCache × (CoverageDeferred.S FIPS205.core ×
        Coverage.RoleState FIPS205.core)) × Paid =>
    NativeStateProvenance s initialPK world.2 world.1.2.1.1 ∧ paid.1.2 ≤ world.2.1.2
  have input_mono {before after : Paid} (h : before.1.2 ≤ after.1.2)
      {input : Lab.Domain} (hi : NativeProvenanceInput s initialPK before input) :
      NativeProvenanceInput s initialPK after input := by
    rcases input with (((sample | point) | (secret | nonce)) | (touch | node))
    · trivial
    · exact hi
    · exact hi
    · exact hi.trans h
    · rcases touch with (secret | nonce) | node
      · exact hi
      · exact hi.trans h
      · trivial
    · trivial
  have native_program {beta : Type} (current : Paid)
      (program : OracleComp (Lab + O) beta)
      (hprogram : AllQueriesSatisfy program
        (Sum.elim (NativeProvenanceInput s initialPK current) (fun _ => True)))
      (cache : CoverageDeferred.S FIPS205.core × Coverage.RoleState FIPS205.core)
      (hc : NativeStateProvenance s initialPK current cache.1.1) :
      ∀ output ∈ support ((simulateQ native program).run cache),
        NativeStateProvenance s initialPK current output.2.1.1 := by
    intro output hout
    refine hprogram.holds_of_mem_support_run_simulateQ
      (fun currentCache => NativeStateProvenance s initialPK current currentCache.1.1)
      ?_ hc hout
    intro input hi before hbefore after hafter
    rcases input with lab | event
    · change after ∈ support
        ((fun z => (z.1.1, (z.1.2, z.2))) <$>
          (simulateQ roles ((relative (.inl lab)).run before.1)).run before.2) at hafter
      rw [support_map] at hafter
      obtain ⟨z, hz, rfl⟩ := hafter
      exact (native_lab_query_preserves_provenance s initialPK current lab hi
        before.1 hbefore before.2 z hz).1
    · change after ∈ support
        ((fun z => (z.1.1, (z.1.2, z.2))) <$>
          (simulateQ roles ((relative (.inr event)).run before.1)).run before.2) at hafter
      simp only [relative, CoverageDeferred.relative_marker, simulateQ_pure,
        StateT.run_pure, map_pure, support_pure, Set.mem_singleton_iff] at hafter
      subst after
      exact hbefore
  have routed_query (current : Paid) (input : LabCommon.Domain)
      (hi : Sum.elim (Sum.elim (NativeProvenanceInput s initialPK current)
        (fun _ => True)) (fun _ => True) input)
      (cache : Raw.QueryCache × (CoverageDeferred.S FIPS205.core ×
        Coverage.RoleState FIPS205.core))
      (hc : NativeStateProvenance s initialPK current cache.2.1.1) :
      ∀ output ∈ support ((routed input).run cache),
        NativeStateProvenance s initialPK current output.2.2.1.1 := by
    have hsource : AllQueriesSatisfy ((routeLab s input).run cache.1)
        (Sum.elim (NativeProvenanceInput s initialPK current) (fun _ => True)) := by
      rcases input with (lab | bytes) | event
      · change AllQueriesSatisfy
          ((liftM ((Lab + O).query (.inl lab))) >>= fun answer => pure (answer, cache.1)) _
        exact allQueriesSatisfy_bind ((allQueriesSatisfy_query_iff _ _).2 hi)
          fun _ => allQueriesSatisfy_pure _ _
      · exact tableRouter_inputs s initialPK current bytes cache.1
      · change AllQueriesSatisfy
          ((liftM ((Lab + O).query (.inr event))) >>= fun answer => pure (answer, cache.1)) _
        exact allQueriesSatisfy_bind ((allQueriesSatisfy_query_iff _ _).2 trivial)
          fun _ => allQueriesSatisfy_pure _ _
    intro output hout
    change output ∈ support
      ((fun z => (z.1.1, (z.1.2, z.2))) <$>
        (simulateQ native ((routeLab s input).run cache.1)).run cache.2) at hout
    rw [support_map] at hout
    obtain ⟨z, hz, rfl⟩ := hout
    exact native_program current _ hsource cache.2 hc z hz
  have guarded_step (input : LabCommon.Domain)
      (hi : Sum.elim (Sum.elim (NativeProvenanceInput s initialPK paid)
        (fun _ => True)) (fun _ => True) input)
      (before : (Raw.QueryCache × (CoverageDeferred.S FIPS205.core ×
        Coverage.RoleState FIPS205.core)) × Paid)
      (hbefore : Inv before) :
      ∀ output ∈ support ((guardedHandler input).run before), Inv output.2 := by
    intro output hout
    rcases before with ⟨cache, counts, flag⟩
    apply QueryImpl.guardQueryBudget_cases_of_mem_support (P := fun out => Inv out.2) hout
    · exact fun _ => hbefore
    · intro _ _ z hz
      have hallowed : Sum.elim (Sum.elim
          (NativeProvenanceInput s initialPK (counts, flag)) (fun _ => True))
          (fun _ => True) input := by
        rcases input with (lab | bytes) | event
        · exact input_mono hbefore.2 hi
        · trivial
        · trivial
      have hstate := routed_query (counts, flag) input hallowed cache hbefore.1 z hz
      have hcounts : counts.2 ≤ (counts + charge input).2 := Nat.le_add_right _ _
      exact ⟨state_mono_paid s initialPK (counts, flag)
        (counts + charge input, false) _ hcounts hstate, hbefore.2.trans hcounts⟩
  have hfold : ∀ output ∈ support
      ((simulateQ guardedHandler program).run (initialCache, paid)), Inv output.2 := by
    intro output hout
    exact hprogram.holds_of_mem_support_run_simulateQ Inv guarded_step ⟨hs, le_rfl⟩ hout
  let reshape := fun z :
      (((alpha × (PUnit × Paid)) × Raw.QueryCache) ×
        CoverageDeferred.S FIPS205.core) × Coverage.RoleState FIPS205.core =>
    (z.1.1.1.1, ((z.1.1.2, (z.1.2, z.2)), z.1.1.1.2.2))
  have frontend :
      reshape <$> (simulateQ roles
        ((simulateQ relative
          ((simulateQ (routeLab s)
            ((simulateQ (QueryImpl.guardQueryBudget caps charge
              ((QueryImpl.id' LabCommon).liftTarget (StateT PUnit (OracleComp LabCommon)))
              fallback) program).run (PUnit.unit, paid))).run raw)).run state)).run role =
      (simulateQ guardedHandler program).run (initialCache, paid) := by
    simpa only [reshape, relative, roles, native, routed, charge, initialCache,
      guardedHandler] using
      native_guarded_frontend s reserve caps fallback program raw state role paid
  have hresult : reshape result ∈ support
      ((simulateQ guardedHandler program).run (initialCache, paid)) := by
    rw [← frontend, support_map]
    exact ⟨result, hr, rfl⟩
  exact hfold (reshape result) hresult

end SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native.Provenance

namespace SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native.Provenance

/-- Phase marking and the actual projection preserve the derived lab input predicate. -/
private theorem projected_lab_phase_inputs
    (s : FIPS205.core.PkSeed) (initialPK : PK) (paid : Paid)
    (phase : SigningView.Phase) {alpha : Type} (program : OracleComp Lab alpha)
    (hprogram : AllQueriesSatisfy program (NativeProvenanceInput s initialPK paid)) :
    AllQueriesSatisfy
      (simulateQ commonProjection
        (simulateQ (SigningView.Events.phaseImpl A Message phase)
          (simulateQ (fun input : Lab.Domain =>
            (liftM (A.query (.inl input)) : OracleComp A (Lab.Range input))) program)))
      (Sum.elim (Sum.elim (NativeProvenanceInput s initialPK paid) (fun _ => True))
        (fun _ => True)) := by
  exact Guarded.projected_lab_phase_queries phase (NativeProvenanceInput s initialPK paid)
    program hprogram

/-- A funded honest signing body, including framing rejection, has permitted projected inputs. -/
private theorem projected_signer_inputs
    (s : FIPS205.core.PkSeed) (root : FIPS205.core.Y) (paid : Paid)
    (hpaid : 1 ≤ paid.1.2) (request : Message) :
    AllQueriesSatisfy
      (simulateQ commonProjection
        (simulateQ (SigningView.Events.phaseImpl A Message .signer)
          ((commonView true s).sign (⟨s, root⟩ : PK) (⟨s, root⟩ : PK) request)))
      (Sum.elim (Sum.elim (NativeProvenanceInput s (⟨s, root⟩ : PK) paid)
        (fun _ => True)) (fun _ => True))
 := by
  let Allowed : LabCommon.Domain → Prop := Sum.elim
    (Sum.elim (NativeProvenanceInput s (⟨s, root⟩ : PK) paid) (fun _ => True))
    (fun _ => True)
  cases hframe : (External.encodePureMessage request.context request.message).toOption with
  | none =>
    simpa only [commonView_eq_rejectingEncoding, ite_true, SigningView.rejectingEncoding_sign,
      hframe,
      simulateQ_pure] using (allQueriesSatisfy_pure (spec := LabCommon) none Allowed)
  | some message =>
    let encodeReply := some ∘ SLHDSA.encodeSignature FIPS205.params
      (SLHDSA.Concrete.shakeWireCodec FIPS205.params.params)
    have hsign := lab_sign_inputs_of_paid_attempt s root paid hpaid message
    have hencoded : AllQueriesSatisfy
        (encodeReply <$> ((labScheme FIPS205.core (fun pk => pure pk.pkSeed) s).sign
          (⟨s, root⟩ : PK) (⟨s, root⟩ : PK) message))
        (NativeProvenanceInput s (⟨s, root⟩ : PK) paid) := by
      simpa only [map_eq_bind_pure_comp, Function.comp_def] using
        (allQueriesSatisfy_bind hsign (fun _ => allQueriesSatisfy_pure _ _))
    have h := projected_lab_phase_inputs s (⟨s, root⟩ : PK) paid .signer
      (encodeReply <$> ((labScheme FIPS205.core (fun pk => pure pk.pkSeed) s).sign
        (⟨s, root⟩ : PK) (⟨s, root⟩ : PK) message)) hencoded
    simpa only [commonView_eq_rejectingEncoding, ite_true, SigningView.rejectingEncoding_sign,
      hframe,
      SignatureAlg.map_sign, simulateQ'_apply, simulateQ_map, encodeReply, Allowed] using h

end SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native.Provenance

namespace SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native

/-- The actual marked callback preserves provenance and monotonically increases admitted attempts.
The internal invariant is supplied by the preceding native prefix. Every invalid-request and
budget-abort branch is retained in the source computation. -/
theorem native_signing_callback_preserves_provenance
    (s : FIPS205.core.PkSeed) (root : FIPS205.core.Y)
    (reserve : Bool) (caps : Nat × Nat)
    (fallback : (input : LabCommon.Domain) → LabCommon.Range input)
    (request : Message) (raw : Raw.QueryCache)
    (state : CoverageDeferred.S FIPS205.core)
    (role : Coverage.RoleState FIPS205.core) (paid : Paid)
    (hs : NativeStateProvenance s (⟨s, root⟩ : PK) paid state.1) :
    letI : MonadLiftT (OracleComp LabCommon) (StateT PUnit (OracleComp LabCommon)) :=
      ⟨fun action => StateT.lift action⟩
    let forwarder := (QueryImpl.id' LabCommon).liftTarget
      (StateT PUnit (OracleComp LabCommon))
    let callback := simulateQ commonProjection
      ((SigningView.Events.viewWithEvents (commonView true s)).sign
        (⟨s, root⟩ : PK) (⟨s, root⟩ : PK) request)
    let guarded := (simulateQ (QueryImpl.guardQueryBudget caps
      (Sum.elim (fun _ : A.Domain => (0, 0)) (policy reserve s)) forwarder fallback)
      callback).run (PUnit.unit, paid)
    let run := (simulateQ (Coverage.roleRunImpl FIPS205.core)
      ((simulateQ (CoverageDeferred.relative FIPS205.core s (metadataCost true s))
        ((simulateQ (routeLab s) guarded).run raw)).run state)).run role
    ∀ result ∈ support run,
      let paid' := result.1.1.1.2.2
      let state' := result.1.2
      NativeStateProvenance s (⟨s, root⟩ : PK) paid' state'.1 ∧
        paid.1.2 ≤ paid'.1.2
 := by
  let _ : MonadLiftT (OracleComp.{0, 0, 0} LabCommon)
      (StateT PUnit.{1} (OracleComp.{0, 0, 0} LabCommon)) :=
    ⟨fun action => StateT.lift action⟩
  classical
  dsimp only
  intro result hr
  let key : PK := ⟨s, root⟩
  let relative := CoverageDeferred.relative FIPS205.core s (metadataCost true s)
  let roles := Coverage.roleRunImpl FIPS205.core
  let native := QueryImpl.Stateful.link relative roles
  let routed := QueryImpl.Stateful.link (routeLab s) native
  let charge := Sum.elim (fun _ : A.Domain => (0, 0)) (policy reserve s)
  let handler := QueryImpl.guardQueryBudget caps charge routed fallback
  let initial := ((raw, (state, role)), paid)
  let callback := simulateQ commonProjection
    ((SigningView.Events.viewWithEvents (commonView true s)).sign key key request)
  let body := simulateQ commonProjection
    (simulateQ (SigningView.Events.phaseImpl A Message .signer)
      ((commonView true s).sign key key request))
  let reshape {alpha : Type} := fun z :
      (((alpha × (PUnit × Paid)) × Raw.QueryCache) ×
        CoverageDeferred.S FIPS205.core) × Coverage.RoleState FIPS205.core =>
    (z.1.1.1.1, ((z.1.1.2, (z.1.2, z.2)), z.1.1.1.2.2))
  have hfront :
      reshape <$> (simulateQ roles
        ((simulateQ relative
          ((simulateQ (routeLab s)
            ((simulateQ (QueryImpl.guardQueryBudget caps charge
              ((QueryImpl.id' LabCommon).liftTarget (StateT PUnit (OracleComp LabCommon)))
              fallback) callback).run (PUnit.unit, paid))).run raw)).run state)).run role =
      (simulateQ handler callback).run initial := by
    simpa only [reshape, handler, initial, routed, native, relative, roles, charge] using
      Provenance.native_guarded_frontend s reserve caps fallback
        callback raw state role paid
  have hflat : reshape result ∈ support ((simulateQ handler callback).run initial) := by
    rw [← hfront, support_map]
    exact ⟨result, hr, rfl⟩
  have split : callback =
      (liftM (LabCommon.query (.inr (.signingAttempt request)))) >>= fun _ => body :=
    Guarded.projected_callback_eq s key key request
  rw [split, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hflat
  obtain ⟨entered, hentered, hbody⟩ := hflat
  have entryFront :
      reshape <$> (simulateQ roles
        ((simulateQ relative
          ((simulateQ (routeLab s)
            ((simulateQ (QueryImpl.guardQueryBudget caps charge
              ((QueryImpl.id' LabCommon).liftTarget (StateT PUnit (OracleComp LabCommon)))
              fallback) (liftM (LabCommon.query (.inr (.signingAttempt request))))).run
                (PUnit.unit, paid))).run raw)).run state)).run role =
      (simulateQ handler (liftM (LabCommon.query (.inr (.signingAttempt request))))).run
        initial := by
    simpa only [reshape, handler, initial, routed, native, relative, roles, charge] using
      Provenance.native_guarded_frontend s reserve caps fallback
        (liftM (LabCommon.query (.inr (.signingAttempt request)))) raw state role paid
  rw [← entryFront, support_map] at hentered
  obtain ⟨entry, hentry, rfl⟩ := hentered
  have entryLaw := native_signing_entry_preserves_provenance s key reserve caps fallback
    request raw state role paid hs entry hentry
  dsimp only at entryLaw
  rcases entryLaw with ⟨_, _, _, hentryPaid, _, hentryInv, hentryFund⟩
  let paidEntry := entry.1.1.1.2.2
  let stateEntry := entry.1.2
  let rawEntry := entry.1.1.2
  let roleEntry := entry.2
  let admitted := paid.2 = false ∧ paid.1 + policy reserve s (.signingAttempt request) ≤ caps
  have hentryMono : paid.1.2 ≤ paidEntry.1.2 := by
    change paid.1.2 ≤ entry.1.1.1.2.2.1.2
    rw [hentryPaid]
    by_cases ha : admitted
    · simp only [admitted] at ha
      simp only [ha]
      exact Nat.le_add_right _ _
    · simp only [admitted] at ha
      simp only [ha, ↓reduceIte]
      exact le_rfl
  have bodyFront :
      reshape <$> (simulateQ roles
        ((simulateQ relative
          ((simulateQ (routeLab s)
            ((simulateQ (QueryImpl.guardQueryBudget caps charge
              ((QueryImpl.id' LabCommon).liftTarget (StateT PUnit (OracleComp LabCommon)))
              fallback) body).run (PUnit.unit, paidEntry))).run rawEntry)).run
                stateEntry)).run roleEntry =
      (simulateQ handler body).run ((rawEntry, (stateEntry, roleEntry)), paidEntry) := by
    simpa only [reshape, handler, routed, native, relative, roles, charge] using
      Provenance.native_guarded_frontend s reserve caps fallback body
        rawEntry stateEntry roleEntry paidEntry
  change reshape result ∈ support
    ((simulateQ handler body).run ((rawEntry, (stateEntry, roleEntry)), paidEntry)) at hbody
  rw [← bodyFront, support_map] at hbody
  obtain ⟨bodyOut, hbodyOut, hshape⟩ := hbody
  let Post := fun output : Option (List Byte) ×
      ((Raw.QueryCache × (CoverageDeferred.S FIPS205.core ×
        Coverage.RoleState FIPS205.core)) × Paid) =>
    NativeStateProvenance s key output.2.2 output.2.1.2.1.1 ∧
      paid.1.2 ≤ output.2.2.1.2
  change Post (reshape result)
  rw [← hshape]
  change NativeStateProvenance s key bodyOut.1.1.1.2.2 bodyOut.1.2.1 ∧
    paid.1.2 ≤ bodyOut.1.1.1.2.2.1.2
  by_cases ha : admitted
  · have hpaidEntry : 1 ≤ paidEntry.1.2 := hentryFund ha
    have allowed := Provenance.projected_signer_inputs
      s root paidEntry hpaidEntry request
    have hfinal := Provenance.native_guarded_program_preserves_provenance
      s key reserve caps fallback body rawEntry stateEntry roleEntry paidEntry
      hentryInv allowed bodyOut hbodyOut
    exact ⟨hfinal.1, hentryMono.trans hfinal.2⟩
  · have haborted : paidEntry = (paid.1, true) := by
      simpa only [paidEntry, admitted, ha, ↓reduceIte] using hentryPaid
    rw [haborted] at hbodyOut
    have frozen := Provenance.native_aborted_program_state s reserve caps
      fallback body rawEntry stateEntry roleEntry paid.1 bodyOut hbodyOut
    have hp : bodyOut.1.1.1.2.2 = paidEntry := frozen.2.2.2.trans haborted.symm
    rw [hp, frozen.2.1]
    exact ⟨hentryInv, hentryMono⟩

end SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native

end

section

open OracleComp OracleSpec SignatureAlg
open SLHDSA SLHDSA.Security SLHDSA.SHAKE128s
open SLHDSA.SHAKE128s.Bridge.SharedExperiment.Guarded
namespace SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native.Provenance

/-- Every framed and decoded verifier query retains the generated public key's provenance.
Invalid frames and undecodable wire signatures retain their ordinary rejecting computation. -/
private theorem projected_verifier_inputs
    (s : FIPS205.core.PkSeed) (root : FIPS205.core.Y) (paid : Paid)
    (request : Message) (wire : List Byte) :
    AllQueriesSatisfy
      (simulateQ commonProjection
        ((SigningView.Events.viewWithEvents (commonView true s)).verify
          (⟨s, root⟩ : PK) request wire))
      (Sum.elim (Sum.elim (NativeProvenanceInput s (⟨s, root⟩ : PK) paid)
        (fun _ => True)) (fun _ => True))
 := by
  let Allowed : LabCommon.Domain → Prop := Sum.elim
    (Sum.elim (NativeProvenanceInput s (⟨s, root⟩ : PK) paid) (fun _ => True))
    (fun _ => True)
  cases hframe : (External.encodePureMessage request.context request.message).toOption with
  | none =>
    simpa only [SigningView.Events.viewWithEvents, commonView_eq_rejectingEncoding, ite_true,
      SigningView.rejectingEncoding_verify, hframe, simulateQ_pure] using
      (allQueriesSatisfy_pure (spec := LabCommon) false Allowed)
  | some message =>
    cases hdecode : (SLHDSA.decodeSignature FIPS205.params
        (SLHDSA.Concrete.shakeWireCodec FIPS205.params.params) wire).toOption with
    | none =>
      simpa only [SigningView.Events.viewWithEvents, commonView_eq_rejectingEncoding, ite_true,
        SigningView.rejectingEncoding_verify, hframe, hdecode, simulateQ_pure] using
        (allQueriesSatisfy_pure (spec := LabCommon) false Allowed)
    | some signature =>
      have h := projected_lab_phase_inputs s (⟨s, root⟩ : PK) paid .verification
        ((labScheme FIPS205.core (fun pk => pure pk.pkSeed) s).verify
          (⟨s, root⟩ : PK) message signature)
        (lab_verify_inputs s root paid message signature)
      simpa only [SigningView.Events.viewWithEvents, commonView_eq_rejectingEncoding, ite_true,
        SigningView.rejectingEncoding_verify, hframe, hdecode,
        SignatureAlg.map_verify, simulateQ'_apply] using h

/-- The actual adaptive client preserves its retained key's provenance while recording
all raw callback replies. The warm-state invariant comes from the preceding native prefix. -/
private theorem native_client_preserves_provenance
    (s : FIPS205.core.PkSeed) (root : FIPS205.core.Y)
    (adv : Game.Adversary FIPS205.Answer PK)
    (reserve : Bool) (caps : Nat × Nat)
    (fallback : (input : LabCommon.Domain) → LabCommon.Range input)
    (raw : Raw.QueryCache) (state : CoverageDeferred.S FIPS205.core)
    (role : Coverage.RoleState FIPS205.core) (paid : Paid)
    (hs : NativeStateProvenance s (⟨s, root⟩ : PK) paid state.1) :
    letI : MonadLiftT (OracleComp LabCommon) (StateT PUnit (OracleComp LabCommon)) :=
      ⟨fun action => StateT.lift action⟩
    let forwarder := (QueryImpl.id' LabCommon).liftTarget
      (StateT PUnit (OracleComp LabCommon))
    let client := simulateQ commonProjection
      ((SigningView.Events.viewWithEvents (commonView true s)).runWithSigningOracle
        (⟨s, root⟩ : PK) (⟨s, root⟩ : PK)
        (SigningView.Events.mainWithEvents (commonMain adv) (⟨s, root⟩ : PK)))
    let guarded := (simulateQ (QueryImpl.guardQueryBudget caps
      (Sum.elim (fun _ : A.Domain => (0, 0)) (policy reserve s)) forwarder fallback)
      client).run (PUnit.unit, paid)
    let run := (simulateQ (Coverage.roleRunImpl FIPS205.core)
      ((simulateQ (CoverageDeferred.relative FIPS205.core s (metadataCost true s))
        ((simulateQ (routeLab s) guarded).run raw)).run state)).run role
    ∀ result ∈ support run,
      NativeStateProvenance s (⟨s, root⟩ : PK) result.1.1.1.2.2 result.1.2.1 ∧
        paid.1.2 ≤ result.1.1.1.2.2.1.2
 := by
  let _ : MonadLiftT (OracleComp.{0, 0, 0} LabCommon)
      (StateT PUnit.{1} (OracleComp.{0, 0, 0} LabCommon)) :=
    ⟨fun action => StateT.lift action⟩
  classical
  dsimp only
  intro result hr
  let key : PK := ⟨s, root⟩
  let Marked := SigningView.Events.Spec A Message
  let marked := SigningView.Events.viewWithEvents (commonView true s)
  let relative := CoverageDeferred.relative FIPS205.core s (metadataCost true s)
  let roles := Coverage.roleRunImpl FIPS205.core
  let native := QueryImpl.Stateful.link relative roles
  let routed := QueryImpl.Stateful.link (routeLab s) native
  let charge := Sum.elim (fun _ : A.Domain => (0, 0)) (policy reserve s)
  let handler := QueryImpl.guardQueryBudget caps charge routed fallback
  let outer : QueryImpl Marked
      (StateT ((Raw.QueryCache × (CoverageDeferred.S FIPS205.core ×
        Coverage.RoleState FIPS205.core)) × Paid) ProbComp) :=
    handler ∘ₛ commonProjection
  let initial := ((raw, (state, role)), paid)
  let Inv := fun world :
      (Raw.QueryCache × (CoverageDeferred.S FIPS205.core ×
        Coverage.RoleState FIPS205.core)) × Paid =>
    NativeStateProvenance s key world.2 world.1.2.1.1 ∧ paid.1.2 ≤ world.2.1.2
  let SourceAllowed : Paid → LabCommon.Domain → Prop := fun current =>
    Sum.elim (Sum.elim (NativeProvenanceInput s key current) (fun _ => True))
      (fun _ => True)
  let AmbientAllowed : A.Domain → Prop :=
    fun input => ∀ current : Paid, SourceAllowed current (.inl input)
  let MarkedAllowed : Marked.Domain → Prop := Sum.elim AmbientAllowed (fun _ => True)
  let reshape {alpha : Type} := fun z :
      (((alpha × (PUnit × Paid)) × Raw.QueryCache) ×
        CoverageDeferred.S FIPS205.core) × Coverage.RoleState FIPS205.core =>
    (z.1.1.1.1, ((z.1.1.2, (z.1.2, z.2)), z.1.1.1.2.2))
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
      native_guarded_frontend s reserve caps fallback program before.1.1 before.1.2.1
        before.1.2.2 before.2
  have preserve {alpha : Type} (program : OracleComp LabCommon alpha)
      (before : (Raw.QueryCache × (CoverageDeferred.S FIPS205.core ×
        Coverage.RoleState FIPS205.core)) × Paid)
      (hbefore : Inv before) (allowed : AllQueriesSatisfy program (SourceAllowed before.2))
      (after : alpha × ((Raw.QueryCache × (CoverageDeferred.S FIPS205.core ×
        Coverage.RoleState FIPS205.core)) × Paid))
      (hafter : after ∈ support ((simulateQ handler program).run before)) : Inv after.2 := by
    rw [← front program before, support_map] at hafter
    obtain ⟨out, hout, rfl⟩ := hafter
    have h := native_guarded_program_preserves_provenance s key reserve caps fallback
      program before.1.1 before.1.2.1 before.1.2.2 before.2 hbefore.1 allowed out hout
    exact ⟨h.1, hbefore.2.trans h.2⟩
  have project_allowed (input : Marked.Domain) (hi : MarkedAllowed input)
      (current : Paid) :
      AllQueriesSatisfy (commonProjection input) (SourceAllowed current) := by
    rcases input with ambient | event
    · change AllQueriesSatisfy
        (liftM (LabCommon.query (.inl ambient)) : OracleComp LabCommon _) _
      exact (allQueriesSatisfy_query_iff (spec := LabCommon) _ _).2 (hi current)
    · cases hevent : commonEvent event with
      | none =>
        simpa only [commonProjection, QueryImpl.add, hevent] using
          (allQueriesSatisfy_pure (spec := LabCommon) PUnit.unit (SourceAllowed current))
      | some rawEvent =>
        simp only [commonProjection, QueryImpl.add, hevent]
        exact (allQueriesSatisfy_query_iff (spec := LabCommon) _ _).2 trivial
  have common_allowed : AllQueriesSatisfy (commonMain adv key)
      (Sum.elim AmbientAllowed (fun _ => True)) := by
    unfold commonMain
    refine (allQueriesSatisfy_of_forall (fun _ => True.intro)
      (Game.Counted.externalMain adv key)).simulateQ ?_
    rintro ((sample | bytes) | request) _
    · change AllQueriesSatisfy
        (liftM ((A + Sign).query (.inl (.inl (.inl (.inl (.inl sample)))))) :
          OracleComp (A + Sign) _) _
      exact (allQueriesSatisfy_query_iff (spec := A + Sign) _ _).2 (fun _ => True.intro)
    · change AllQueriesSatisfy
        (liftM ((A + Sign).query (.inl (.inr bytes))) : OracleComp (A + Sign) _) _
      exact (allQueriesSatisfy_query_iff (spec := A + Sign) _ _).2 (fun _ => True.intro)
    · change AllQueriesSatisfy
        (liftM ((A + Sign).query (.inr request)) : OracleComp (A + Sign) _) _
      exact (allQueriesSatisfy_query_iff (spec := A + Sign) _ _).2 trivial
  have main_allowed : AllQueriesSatisfy
      (SigningView.Events.mainWithEvents (commonMain adv) key)
      (Sum.elim MarkedAllowed (fun _ => True)) := by
    unfold SigningView.Events.mainWithEvents
    refine common_allowed.simulateQ ?_
    rintro (ambient | request) hi
    · simp only [QueryImpl.add, SigningView.Events.phaseImpl,
        QueryImpl.preInsert_apply, SigningView.Events.emit, simulateQ_bind, simulateQ_spec_query]
      change AllQueriesSatisfy
        (do
          let _ ← (liftM ((Marked + Sign).query
            (.inl (.inr (.ambient .adversary ambient)))) : OracleComp (Marked + Sign) PUnit)
          (liftM ((Marked + Sign).query (.inl (.inl ambient))) : OracleComp (Marked + Sign) _)) _
      exact allQueriesSatisfy_bind
        ((allQueriesSatisfy_query_iff (spec := Marked + Sign) _ _).2 trivial)
        (fun _ => (allQueriesSatisfy_query_iff (spec := Marked + Sign) _ _).2 hi)
    · change AllQueriesSatisfy
        (liftM ((Marked + Sign).query (.inr request)) : OracleComp (Marked + Sign) _) _
      exact (allQueriesSatisfy_query_iff (spec := Marked + Sign) _ _).2 trivial
  let I : QueryLog Sign →
      ((Raw.QueryCache × (CoverageDeferred.S FIPS205.core ×
        Coverage.RoleState FIPS205.core)) × Paid) → Prop := fun _ world => Inv world
  have ambient_step (input : Marked.Domain) (hi : MarkedAllowed input)
      (log : QueryLog Sign)
      (before : (Raw.QueryCache × (CoverageDeferred.S FIPS205.core ×
        Coverage.RoleState FIPS205.core)) × Paid) (hbefore : I log before)
      (after : Marked.Range input × ((Raw.QueryCache × (CoverageDeferred.S FIPS205.core ×
        Coverage.RoleState FIPS205.core)) × Paid))
      (hafter : after ∈ support ((outer input).run before)) : I log after.2 := by
    change after ∈ support ((simulateQ handler (commonProjection input)).run before) at hafter
    exact preserve (commonProjection input) before hbefore (project_allowed input hi before.2)
      after hafter
  have signing_step (request : Message) (log : QueryLog Sign)
      (before : (Raw.QueryCache × (CoverageDeferred.S FIPS205.core ×
        Coverage.RoleState FIPS205.core)) × Paid) (hbefore : I log before)
      (after : Sign.Range request × ((Raw.QueryCache × (CoverageDeferred.S FIPS205.core ×
        Coverage.RoleState FIPS205.core)) × Paid))
      (hafter : after ∈ support ((simulateQ outer (marked.sign key key request)).run before)) :
      I (log ++ [⟨request, after.1⟩]) after.2 := by
    rw [QueryImpl.simulateQ_compose] at hafter
    rw [← front (simulateQ commonProjection (marked.sign key key request)) before,
      support_map] at hafter
    obtain ⟨out, hout, rfl⟩ := hafter
    have h := native_signing_callback_preserves_provenance s root reserve caps fallback
      request before.1.1 before.1.2.1 before.1.2.2 before.2 hbefore.1 out hout
    exact ⟨h.1, hbefore.2.trans h.2⟩
  let client := simulateQ commonProjection
    (marked.runWithSigningOracle key key (SigningView.Events.mainWithEvents (commonMain adv) key))
  have hflat : reshape result ∈ support ((simulateQ handler client).run initial) := by
    rw [← front client initial, support_map]
    exact ⟨result, hr, rfl⟩
  change reshape result ∈ support
    ((simulateQ handler (simulateQ commonProjection
      (marked.runWithSigningOracle key key
        (SigningView.Events.mainWithEvents (commonMain adv) key)))).run initial) at hflat
  rw [← QueryImpl.simulateQ_compose] at hflat
  have hfinal := QueryImpl.holds_of_mem_support_run_add_withLogging
    outer (marked.sign key key) I ambient_step signing_step main_allowed
    (log₀ := (∅ : QueryLog Sign)) (s₀ := initial) (z := reshape result)
    (⟨hs, le_rfl⟩ : I ∅ initial)
    (by simpa only [SigningView.runWithSigningOracle, SigningView.signingOracle,
      QueryImpl.passthrough_add, HasQuery.toQueryImpl_eq_id'] using hflat)
  exact hfinal

end SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native.Provenance

namespace SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native

/-- Actual native execution retains its generated key and all public/private provenance.
The support statement includes every terminal branch and every supplied pair of native tapes. -/
theorem native_joint_provenance :
  ∀ (s : FIPS205.core.PkSeed) (adv : Game.Adversary FIPS205.Answer PK)
    (reserve : Bool) (caps : Nat × Nat)
    (fallback : (input : LabCommon.Domain) → LabCommon.Range input)
    (leftTape rightTape : List HashOutput),
  ∀ t ∈ support (nativeRun s adv reserve caps fallback leftTape rightTape),
    let initialPK := t.1.1.1
    let initialSK := t.1.1.2
    let paid := t.2.2
    let state := t.2.1.1.2.1
    initialSK = initialPK ∧ NativeStateProvenance s initialPK paid state
 := by
  intro s adv reserve caps fallback leftTape rightTape terminal hterminal
  let _ : MonadLiftT (OracleComp.{0, 0, 0} LabCommon)
      (StateT PUnit.{1} (OracleComp.{0, 0, 0} LabCommon)) :=
    ⟨fun action => StateT.lift action⟩
  classical
  let tapes : (j : Coverage.TapeClass) → List (Coverage.tapeClassRange FIPS205.core j)
    | .signer => leftTape.map Bridge.answerEquiv
    | .forger => rightTape.map Bridge.answerEquiv
    | .other => []
  let initialRole : Coverage.RoleState FIPS205.core :=
    ((∅, tapes), (AnswerTape.ClassPos.init, ∅))
  let marked := SigningView.Events.viewWithEvents (commonView true s)
  let relative := CoverageDeferred.relative FIPS205.core s (metadataCost true s)
  let roles := Coverage.roleRunImpl FIPS205.core
  let native := QueryImpl.Stateful.link relative roles
  let routed := QueryImpl.Stateful.link (routeLab s) native
  let charge := Sum.elim (fun _ : A.Domain => (0, 0)) (policy reserve s)
  let handler := QueryImpl.guardQueryBudget caps charge routed fallback
  let initial : (Raw.QueryCache × (CoverageDeferred.S FIPS205.core ×
      Coverage.RoleState FIPS205.core)) × Paid :=
    ((∅, ((((∅, ∅), []), (0, .keygen)), initialRole)), ((0, 0), false))
  let reshape {alpha : Type} := fun z :
      (((alpha × (PUnit × Paid)) × Raw.QueryCache) ×
        CoverageDeferred.S FIPS205.core) × Coverage.RoleState FIPS205.core =>
    (z.1.1.1.1, ((z.1.1.2, (z.1.2, z.2)), z.1.1.1.2.2))
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
  have keygen_good (out : (PK × PK) ×
      ((Raw.QueryCache × (CoverageDeferred.S FIPS205.core ×
        Coverage.RoleState FIPS205.core)) × Paid))
      (hout : out ∈ support ((simulateQ handler
        (simulateQ commonProjection marked.keygen)).run initial)) :
      out.1.2 = out.1.1 ∧ NativeStateProvenance s out.1.1 out.2.2 out.2.1.2.1.1 := by
    rw [← front (simulateQ commonProjection marked.keygen) initial, support_map] at hout
    obtain ⟨cold, hcold, rfl⟩ := hout
    have coldLaw := native_cold_keygen_provenance s reserve caps fallback
      leftTape rightTape cold hcold
    dsimp only at coldLaw
    rcases coldLaw with ⟨hkeys, hseed, _, _, _, hC, hprivate, hnonce⟩
    refine ⟨hkeys, hseed, ?_, ?_⟩
    · intro q hq
      rw [hC] at hq
      simp at hq
    · rintro ((secret | nonce) | node) hcell
      · exact hprivate secret hcell
      · rcases nonce with ⟨randomizer, message⟩
        rcases hnonce randomizer message with ⟨hdraw, hpending⟩
        rcases hcell with hcell | hcell
        · have hcell' : (cold.1.2.1.1.2
              (.inl (.inr (randomizer, message)))).isSome := hcell
          simp only [hdraw, Option.isSome_none, Bool.false_eq_true] at hcell'
        · exact (hpending hcell).elim
      · trivial
  simp only [nativeRun, bind_pure_comp, support_map] at hterminal
  obtain ⟨nested, hnested, rfl⟩ := hterminal
  have hflat : reshape nested ∈ support
      ((simulateQ handler (commonSource true s adv)).run initial) := by
    rw [← front (commonSource true s adv) initial, support_map]
    exact ⟨nested, hnested, rfl⟩
  simp only [commonSource, SigningView.Events.fullExperiment,
    simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure] at hflat
  rw [mem_support_bind_iff] at hflat
  obtain ⟨keys, hkeys, hclient⟩ := hflat
  rcases keys with ⟨⟨pk, sk⟩, before⟩
  have keyLaw := keygen_good ((pk, sk), before) hkeys
  rcases keyLaw with ⟨hkeysSame, hkeyInv⟩
  change sk = pk at hkeysSame
  subst sk
  rcases pk with ⟨seed, root⟩
  have hseed : seed = s := hkeyInv.1
  subst seed
  rw [mem_support_bind_iff] at hclient
  obtain ⟨client, hclient, hverify⟩ := hclient
  have clientInv : NativeStateProvenance s (⟨s, root⟩ : PK)
      client.2.2 client.2.1.2.1.1 := by
    rw [← front (simulateQ commonProjection
      (marked.runWithSigningOracle (⟨s, root⟩ : PK) (⟨s, root⟩ : PK)
        (SigningView.Events.mainWithEvents (commonMain adv) (⟨s, root⟩ : PK)))) before,
      support_map] at hclient
    obtain ⟨out, hout, hshape⟩ := hclient
    have h := Provenance.native_client_preserves_provenance
      s root adv reserve caps fallback before.1.1 before.1.2.1
      before.1.2.2 before.2 hkeyInv out hout
    rw [← hshape]
    exact h.1
  rw [mem_support_bind_iff] at hverify
  obtain ⟨verified, hverified, hpure⟩ := hverify
  have verifiedInv : NativeStateProvenance s (⟨s, root⟩ : PK) verified.2.2
      verified.2.1.2.1.1 := by
    rw [← front (simulateQ commonProjection
      (marked.verify (⟨s, root⟩ : PK) client.1.1.1 client.1.1.2)) client.2,
      support_map] at hverified
    obtain ⟨out, hout, hshape⟩ := hverified
    have allowed := Provenance.projected_verifier_inputs
      s root client.2.2 client.1.1.1 client.1.1.2
    have h := Provenance.native_guarded_program_preserves_provenance
      s (⟨s, root⟩ : PK) reserve caps fallback
      (simulateQ commonProjection (marked.verify (⟨s, root⟩ : PK)
        client.1.1.1 client.1.1.2)) client.2.1.1 client.2.1.2.1 client.2.1.2.2
      client.2.2 clientInv allowed out hout
    rw [← hshape]
    exact h.1
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  change (reshape nested).1.1.2 = (reshape nested).1.1.1 ∧
    NativeStateProvenance s (reshape nested).1.1.1
      (reshape nested).2.2 (reshape nested).2.1.2.1.1
  rw [hpure]
  exact ⟨rfl, verifiedInv⟩

end SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native

namespace SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native

theorem native_public_provenance :
  ∀ (s : FIPS205.core.PkSeed) (adv : Game.Adversary FIPS205.Answer PK)
    (reserve : Bool) (caps : Nat × Nat)
    (fallback : (input : LabCommon.Domain) → LabCommon.Range input)
    (leftTape rightTape : List HashOutput),
  ∀ t ∈ support (nativeRun s adv reserve caps fallback leftTape rightTape),
    let initialPK := t.1.1.1
    let C := t.2.1.1.2.1.1.1
    initialPK.pkSeed = s ∧
      ∀ q, (C q).isSome → RouteFixed s q ∨
        ∃ r msg, q = .inl (.hmsg r s initialPK.pkRoot msg) := by
  intro s adv reserve caps fallback leftTape rightTape terminal hterminal
  have h := (native_joint_provenance s adv reserve caps fallback leftTape rightTape
    terminal hterminal).2
  exact ⟨h.1, h.2.1⟩

theorem native_private_provenance :
  ∀ (s : FIPS205.core.PkSeed) (adv : Game.Adversary FIPS205.Answer PK)
    (reserve : Bool) (caps : Nat × Nat)
    (fallback : (input : LabCommon.Domain) → LabCommon.Range input)
    (leftTape rightTape : List HashOutput),
  ∀ t ∈ support (nativeRun s adv reserve caps fallback leftTape rightTape),
    let D := t.2.1.1.2.1.1.2
    let pending := t.2.1.1.2.1.2
    let admittedS := t.2.2.1.2
    (∀ k : PrfKey FIPS205.core,
      (D (.inl (.inl k))).isSome ∨ .inl (.inl k) ∈ pending →
        IsHonestKey FIPS205.params FIPS205.core k.1) ∧
    (∀ (o : FIPS205.core.Y) (msg : List Byte),
      (D (.inl (.inr (o, msg)))).isSome ∨ .inl (.inr (o, msg)) ∈ pending →
        1 ≤ admittedS) := by
  intro s adv reserve caps fallback leftTape rightTape terminal hterminal
  have h := (native_joint_provenance s adv reserve caps fallback leftTape rightTape
    terminal hterminal).2
  refine ⟨?_, ?_⟩
  · intro k hk
    exact h.2.2 (.inl (.inl k)) hk
  · intro randomizer message hnonce
    exact h.2.2 (.inl (.inr (randomizer, message))) hnonce

end SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native
end
