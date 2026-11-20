/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.NativeRelative
import all HashSig.SLHDSA.Security.NativeRelative
public import VCVio.CryptoFoundations.SignatureAlg.CountedExperiment
public import VCVio.OracleComp.Coercions.Add.Basic
public import VCVio.OracleComp.QueryTracking.ObservationOracle
public import VCVio.OracleComp.SimSemantics.StateT.PreservesInv
public import VCVio.OracleComp.SimSemantics.StateT.StateSeparating
public import HashSig.SLHDSA.Security.LabScheme
public import HashSig.SLHDSA.Security.CoverageRun
public import VCVio.OracleComp.QueryTracking.RandomOracle.Defer
import all HashSig.SLHDSA.Security.CoverageRun
import all VCVio.OracleComp.QueryTracking.RandomOracle.ClassIndexedTape
import VCVio.OracleComp.SimSemantics.Append.Core

/-! # Agreement of native and role-indexed digest queries

The deferred graph and its pending cells execute through the existing native role interface.
Message digests and nonces retain their actual inputs and mirror their answers in the graph cache.
Observation markers update the existing metadata without issuing a native query.
`PartialHmsgMirror` records equality of the stored public and role message-digest entries.
Linked execution and deferred filling retain this partial-cache correspondence.
-/

public section
open OracleSpec OracleComp SignatureAlg

namespace SLHDSA.Security.CoverageDeferred

variable {vp : ValidatedParams} (core : CorePrimitives vp.params)
variable {ιm Request : Type} {markerSpec : OracleSpec.{0, 0} ιm}
/-- Stored public and role message-digest entries agree, including absent entries. -/
@[expose] def PartialHmsgMirror (world : S core × Coverage.RoleState core) : Prop :=
  ∀ (randomizer : core.Y) (seed : core.PkSeed) (root : core.Y) (message : List Byte),
    world.1.1.1.1 (.inl (.hmsg randomizer seed root message)) =
      world.2.1.1 (.inl (.inl (.hmsg randomizer seed root message)))

/-- Empty graph and role caches agree for arbitrary initial tapes. -/
theorem PartialHmsgMirror.init
    (tapes : (j : Coverage.TapeClass) → List (Coverage.tapeClassRange core j)) :
    PartialHmsgMirror core
      (((((∅, ∅), []), (0, SigningView.Phase.keygen)) : S core),
        (((∅, tapes), (AnswerTape.ClassPos.init, ∅)) : Coverage.RoleState core)) := by
  intro randomizer seed root message
  rfl

variable [SampleableType core.Y] [SampleableType (Bytes vp.params.m)]
  [DecidableEq core.Y] [DecidableEq core.PkSeed] [DecidableEq core.AdrsKey]
  [DecidableEq core.SkPrf]
/-- A native randomizer query leaves every stored message-digest entry unchanged. -/
private theorem nonce_hmsg_frame (which : Coverage.Role)
    (salt : core.Y) (message : List Byte) (before : Coverage.RoleState core)
    (result : core.Y × Coverage.RoleState core)
    (hresult : result ∈ support
      ((simulateQ (Coverage.roleRunImpl core) (Coverage.roleImpl core which
        (.inr (.inr (salt, message))))).run before))
    (r : core.Y) (seed : core.PkSeed) (root : core.Y) (message' : List Byte) :
    result.2.1.1 (.inl (.inl (.hmsg r seed root message'))) =
      before.1.1 (.inl (.inl (.hmsg r seed root message'))) := by
  cases which <;> simp only [Coverage.roleImpl, simulateQ_spec_query] at hresult
  all_goals
    apply (Coverage.cache_cls_of_mem_support_roleRunImpl_run hresult _).1
    rintro query (hquery | hquery) rfl <;> cases hquery

/-- Every linked relative query preserves the stored message-digest correspondence. -/
theorem relative_preserves_partialHmsgMirror
    {ιm Request : Type} {markerSpec : OracleSpec.{0, 0} ιm}
    (seed : core.PkSeed) (policy : SigningView.Event markerSpec Request → Nat) :
    QueryImpl.PreservesInv
      (QueryImpl.Stateful.link (relative core seed policy) (Coverage.roleRunImpl core))
      (PartialHmsgMirror core) := by
  classical
  let G := slhGraph core seed
  let roles := Coverage.roleRunImpl core
  have uniform {alpha : Type} (program : ProbComp alpha) (role : Coverage.RoleState core) :
      (simulateQ roles (liftComp program (Coverage.roleSpec core))).run role =
        (fun answer => (answer, role)) <$> program := by
    apply QueryImpl.Stateful.simulateQ_liftComp_run_of_query roles
    intro input before
    rw [liftComp_liftM_query]
    change (simulateQ roles
      (liftM ((Coverage.roleSpec core).query (.inl input)))).run before = _
    rw [simulateQ_spec_query]
    dsimp only [roles]
    rw [Coverage.roleRunImpl, AnswerTape.classPosImplFwd,
      QueryImpl.extendState_apply]
    simp only [AnswerTape.tapeImplFwd, QueryImpl.add_apply_inl,
      QueryImpl.liftTarget_apply, StateT.run_liftM, QueryImpl.ofLift,
      AnswerTape.classPosAuxFwd, AnswerTape.freshHitAux, bind_pure_comp,
      Functor.map_map, Prod.eta]
    rfl
  have role_query (which : Coverage.Role) (point : (hashSpec core).Domain)
      (before : Coverage.RoleState core)
      (out : (hashSpec core).Range point × Coverage.RoleState core)
      (hout : out ∈ support
        ((simulateQ roles (Coverage.roleImpl core which (.inl (.inr point)))).run before)) :
      out.2.1.1 (.inl point) = some out.1 ∧
        ∀ other, other ≠ .inl point → out.2.1.1 other = before.1.1 other := by
    cases which <;> simp only [Coverage.roleImpl, simulateQ_spec_query] at hout
    all_goals
      obtain ⟨hv, _⟩ := (QueryImpl.mem_support_extendState_run_iff _ _ _ _ _).1 hout
      have cached := Coverage.cache_of_mem_support_tapeStep_run (by
        simpa [AnswerTape.tapeCachingImplClass_apply_inl,
          AnswerTape.tapeCachingImplClass_apply_inr] using hv)
      exact cached
  have graph_frame (native : (labSpec core).Domain)
      (different : ∀ r seed root message,
        native ≠ .inl (.inl (.inr (.inl (.hmsg r seed root message)))))
      (before : CoverageDeferred.D core) (out)
      (hout : out ∈ support ((G.deferredImpl native).run before))
      (r : core.Y) (seed : core.PkSeed) (root : core.Y) (message : List Byte) :
      out.2.1.1 (.inl (.hmsg r seed root message)) =
        before.1.1 (.inl (.hmsg r seed root message)) := by
    let point : PublicHashQuery core.PkSeed core.AdrsKey core.Y :=
      PublicHashQuery.hmsg r seed root message
    have monotone := (G.le_of_mem_support_deferredImpl hout).1
    cases old : before.1.1 (.inl point) with
    | some value => exact monotone old
    | none =>
      cases fresh : out.2.1.1 (.inl point) with
      | none => rfl
      | some value =>
        have present : (out.2.1.1 (.inl point)).isSome = true := by
          simp only [fresh, Option.isSome_some]
        have added := G.deferredImpl_cachesOnlyQueryPoint native before out hout present
        rcases added with hold | hpoint
        · change (before.1.1 (.inl point)).isSome = true at hold
          simp only [old, Option.isSome_none, Bool.false_eq_true] at hold
        · have notQueried : (Sum.elim
              (Sum.elim (Sum.elim (fun _ => none) some) (fun _ => none))
              (fun _ => none)) native ≠ some (.inl point) := by
            rcases native with (((n | query) | derivation) | (touch | read))
            · simp
            · intro equal
              have queryEq : query = .inl point := Option.some.inj equal
              exact different r seed root message (by cases queryEq; rfl)
            · simp
            · simp
            · simp
          exact (notQueried hpoint).elim
  intro input before hbefore after hafter
  rcases before with ⟨state, role⟩
  rw [QueryImpl.Stateful.link_impl_apply_run, support_map] at hafter
  obtain ⟨nested, hnested, rfl⟩ := hafter
  change ∀ r seed root message,
    nested.1.2.1.1.1 (.inl (.hmsg r seed root message)) =
      nested.2.1.1 (.inl (.inl (.hmsg r seed root message)))
  have other (native : (labSpec core).Domain)
      (hother : ¬CoverageDeferred.IsSelectedNative core native) (out)
      (hout : out ∈ support
        ((simulateQ roles ((CoverageDeferred.relative core seed policy
          (.inl native)).run state)).run role)) :
      ∀ r seed root message,
        out.1.2.1.1.1 (.inl (.hmsg r seed root message)) =
          out.2.1.1 (.inl (.inl (.hmsg r seed root message))) := by
    rw [CoverageDeferred.relative_other core seed policy native hother] at hout
    simp only [bind_pure_comp, simulateQ_map, StateT.run_map, uniform,
      Functor.map_map, support_map] at hout
    obtain ⟨graphOut, hgraphOut, rfl⟩ := hout
    intro r seed root message
    have different : ∀ r seed root message,
        native ≠ .inl (.inl (.inr (.inl (.hmsg r seed root message)))) := by
      intro r' seed' root' message' equal
      exact hother (by rw [equal]; trivial)
    exact (graph_frame native different state.1 graphOut hgraphOut r seed root message).trans
      (hbefore r seed root message)
  rcases input with native | event
  · rcases native with (((n | publicPoint) | (secret | nonce)) | (touch | read))
    · exact other _ (by simp [CoverageDeferred.IsSelectedNative]) nested hnested
    · rcases publicPoint with (⟨seed, key, values⟩ | ⟨randomizer, seed, root, message⟩) | nonce
      · exact other _ (by simp [CoverageDeferred.IsSelectedNative]) nested hnested
      · rw [CoverageDeferred.relative_hmsg] at hnested
        simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
          mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hnested
        obtain ⟨out, hout, rfl⟩ := hnested
        have cached := role_query (CoverageDeferred.phaseRole state.2.2)
          (.inl (.hmsg randomizer seed root message)) role out hout
        intro r seed' root' message'
        by_cases same : (.inl (.hmsg r seed' root' message') : (hashSpec core).Domain) =
            .inl (.hmsg randomizer seed root message)
        · have fields := PublicHashQuery.hmsg.inj (Sum.inl.inj same)
          rcases fields with ⟨rfl, rfl, rfl, rfl⟩
          exact (QueryCache.cacheQuery_self _ _ _).trans cached.1.symm
        · rw [QueryCache.cacheQuery_of_ne _ _ same]
          exact (hbefore r seed' root' message').trans (cached.2 _ (by
            intro equal
            exact same (Sum.inl.inj equal))).symm
      · exact other _ (by simp [CoverageDeferred.IsSelectedNative]) nested hnested
    · exact other _ (by simp [CoverageDeferred.IsSelectedNative]) nested hnested
    · rcases nonce with ⟨salt, message⟩
      rw [CoverageDeferred.relative_rand] at hnested
      simp only [simulateQ_map, StateT.run_map, support_map] at hnested
      obtain ⟨out, hout, rfl⟩ := hnested
      intro r seed root message'
      exact (hbefore r seed root message').trans
        (nonce_hmsg_frame core (CoverageDeferred.phaseRole state.2.2) salt message
          role out hout r seed root message').symm
    · exact other _ (by simp [CoverageDeferred.IsSelectedNative]) nested hnested
    · exact other _ (by simp [CoverageDeferred.IsSelectedNative]) nested hnested
  · rw [CoverageDeferred.relative_marker] at hnested
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hnested
    rw [hnested]
    exact hbefore

/-- The actual linked program retains partial cache correspondence in its returned state. -/
theorem PartialHmsgMirror.of_mem_support_run
    {ιm Request : Type} {markerSpec : OracleSpec.{0, 0} ιm}
    (seed : core.PkSeed) (policy : SigningView.Event markerSpec Request → Nat)
    {α : Type}
    (program : OracleComp (labSpec core + ObsSpec (SigningView.Event markerSpec Request)) α)
    (before : S core × Coverage.RoleState core)
    (after : α × (S core × Coverage.RoleState core))
    (hbefore : PartialHmsgMirror core before)
    (hafter : after ∈ support ((simulateQ
      (QueryImpl.Stateful.link (relative core seed policy) (Coverage.roleRunImpl core))
        program).run before)) :
    PartialHmsgMirror core after.2 := by
  exact simulateQ_run_preservesInv _ _ (relative_preserves_partialHmsgMirror core seed policy)
    program before hbefore after hafter

omit [SampleableType (Bytes vp.params.m)] [DecidableEq core.PkSeed]
  [DecidableEq core.SkPrf] in
/-- Filling deferred cells retains the partial public cache with the role state fixed. -/
theorem PartialHmsgMirror.endFill
    (world : S core × Coverage.RoleState core) (filled : LabState core)
    (hmirror : PartialHmsgMirror core world)
    (hfilled : filled ∈ support (RelabelState.endFill world.1.1)) :
    ∀ (randomizer : core.Y) (seed : core.PkSeed) (root : core.Y) (message : List Byte),
      filled.1 (.inl (.hmsg randomizer seed root message)) =
        world.2.1.1 (.inl (.inl (.hmsg randomizer seed root message))) := by
  intro randomizer seed root message
  exact (congrArg (fun cache => cache (.inl (.hmsg randomizer seed root message)))
    (RelabelState.fst_eq_of_mem_support_endFill hfilled)).trans
      (hmirror randomizer seed root message)

end SLHDSA.Security.CoverageDeferred
