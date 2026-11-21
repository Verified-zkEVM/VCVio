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

/-! # Law of the deferred experiment after erasing the tapes -/

public section
section

open OracleSpec OracleComp SignatureAlg

namespace SLHDSA.Security.CoverageDeferred

variable {vp : ValidatedParams} (core : CorePrimitives vp.params)
variable {ιm Request : Type} {markerSpec : OracleSpec.{0, 0} ιm}

/-- The public message-digest entries and private nonce cells selected by the native cache. -/
def nativeCache (state : D core) : (Coverage.jointSpec core).QueryCache :=
  QueryCache.ofFn fun
  | .inl (.inl (.hmsg R seed root message)) => state.1.1 (.inl (.hmsg R seed root message))
  | .inr (.inr nonce) => state.1.2 (.inl (.inr nonce))
  | _ => none

/-- The selected native cache is initially empty. -/
theorem nativeCache_empty : nativeCache core ((∅, ∅), []) = ∅ := by
  apply QueryCache.ext
  rintro ((hash | prf) | (secret | nonce))
  all_goals (try cases hash) <;> rfl

variable [SampleableType core.Y] [SampleableType (Bytes vp.params.m)]
  [DecidableEq core.Y] [DecidableEq core.PkSeed] [DecidableEq core.AdrsKey]
  [DecidableEq core.SkPrf]

omit [SampleableType core.Y] [SampleableType (Bytes vp.params.m)] in
/-- Mirroring a message digest is the corresponding native cache update. -/
private theorem nativeCache_hmsg (state : D core) (R : core.Y) (seed : core.PkSeed)
    (root : core.Y) (message : List Byte) (digest : Bytes vp.params.m) :
    nativeCache core ((state.1.1.cacheQuery (.inl (.hmsg R seed root message)) digest,
      state.1.2), state.2) =
    (nativeCache core state).cacheQuery (.inl (.inl (.hmsg R seed root message))) digest := by
  apply QueryCache.ext
  rintro ((hash | prf) | (secret | nonce))
  all_goals (try cases hash) <;> simp [nativeCache, QueryCache.cacheQuery, Function.update]
  split_ifs with h
  · rcases h with ⟨rfl, rfl, rfl, rfl⟩
    rfl
  · rfl

omit [SampleableType core.Y] [SampleableType (Bytes vp.params.m)] in
/-- Mirroring a randomizer is the corresponding native cache update. -/
private theorem nativeCache_rand (state : D core) (salt : core.Y) (message : List Byte)
    (R : core.Y) :
    nativeCache core ((state.1.1,
      state.1.2.cacheQuery (.inl (.inr (salt, message))) R), state.2) =
    (nativeCache core state).cacheQuery (.inr (.inr (salt, message))) R := by
  apply QueryCache.ext
  rintro ((hash | prf) | (secret | nonce))
  all_goals (try cases hash) <;> simp [nativeCache, QueryCache.cacheQuery, Function.update]
  split_ifs with h
  · subst nonce
    rfl
  · rfl

omit [SampleableType core.Y] [SampleableType (Bytes vp.params.m)] in
private theorem nativeCache_pub_other (state : D core) (input : (hashSpec core).Domain)
    (answer : (hashSpec core).Range input)
    (h : ∀ R seed root message, Sum.inl (.hmsg R seed root message) ≠ input) :
    nativeCache core ((state.1.1.cacheQuery input answer, state.1.2), state.2) =
      nativeCache core state := by
  apply QueryCache.ext
  rintro ((hash | prf) | (secret | nonce))
  all_goals (try cases hash) <;>
    simp [nativeCache, QueryCache.cacheQuery_of_ne _ _ (h _ _ _ _)]

omit [SampleableType (Bytes vp.params.m)] [DecidableEq core.PkSeed]
  [DecidableEq core.SkPrf] in
private theorem nativeCache_drawCell (state : LabState core)
    (pending pending' : List (DeriveQuery core ⊕ NodeKey core))
    (cell : DeriveQuery core ⊕ NodeKey core)
    (h : ∀ nonce, Sum.inl (Sum.inr nonce) ≠ cell)
    {z : core.Y × LabState core}
    (hz : z ∈ support ((RelabelState.drawCell cell).run state)) :
    nativeCache core (z.2, pending') = nativeCache core (state, pending) := by
  rw [RelabelState.drawCell_run, support_map] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  have he := QueryImpl.withCaching_run_eq_cacheQuery uniformSampleImpl hw
  change nativeCache core ((state.1, w.2), pending') = _
  rw [he]
  apply QueryCache.ext
  rintro ((hash | prf) | (secret | nonce))
  all_goals (try cases hash) <;>
    simp [nativeCache, QueryCache.cacheQuery_of_ne _ _ (h _)]

private theorem nativeCache_deferred_other (pkSeed : core.PkSeed)
    (input : (labSpec core).Domain) (other : ¬IsSelectedNative core input)
    (state : D core) {z : (labSpec core).Range input × D core}
    (hz : z ∈ support (((slhGraph core pkSeed).deferredImpl input).run state)) :
    nativeCache core z.2 = nativeCache core state := by
  rcases input with input | (touch | node)
  · rw [CanonicalGraph.deferredImpl_run_inl, support_map] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    rcases input with (n | query) | (secret | nonce)
    · rw [CanonicalGraph.relabelImpl_run_unif, support_map] at hw
      obtain ⟨_, _, rfl⟩ := hw
      rfl
    · by_cases ready : ∃ node values,
          (slhGraph core pkSeed).childVals state.1 node = some values ∧
            (slhGraph core pkSeed).pt node values = query
      · obtain ⟨node, values, hn, rfl⟩ := ready
        rw [CanonicalGraph.relabelImpl_run_pt _ hn, support_map] at hw
        obtain ⟨v, hv, rfl⟩ := hw
        exact nativeCache_drawCell core state.1 state.2 state.2 (.inr node)
          (fun _ => by simp) hv
      · rw [CanonicalGraph.relabelImpl_run_pub_of_not_exists _ ready, support_map] at hw
        obtain ⟨v, hv, rfl⟩ := hw
        have he := QueryImpl.withCaching_run_eq_cacheQuery uniformSampleImpl hv
        change nativeCache core ((v.2, state.1.2), state.2) = _
        rw [he]
        apply nativeCache_pub_other
        intro R seed root message eq
        subst query
        exact other trivial
    · rw [CanonicalGraph.relabelImpl_apply_inr] at hw
      exact nativeCache_drawCell core state.1 state.2 state.2 (.inl (.inl secret))
        (fun _ => by simp) hw
    · exact (other trivial).elim
  · rw [CanonicalGraph.deferredImpl_run_touch, support_pure, Set.mem_singleton_iff] at hz
    subst z
    rfl
  · rw [CanonicalGraph.deferredImpl_run_read, support_map] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    exact nativeCache_drawCell core state.1 state.2 state.2 (.inr node)
      (fun _ => by simp) hw

private theorem run_role_hash (role : Coverage.Role) (input : (hashSpec core).Domain)
    (cache : (Coverage.jointSpec core).QueryCache) :
    (simulateQ (AnswerTape.dupRandomOracleFwd (Coverage.jointSpec core))
      (Coverage.roleImpl core role (.inl (.inr input)))).run cache =
      ((Coverage.jointSpec core).randomOracle (.inl input)).run cache := by
  cases role <;>
    simp only [Coverage.roleImpl, simulateQ_spec_query, AnswerTape.dupRandomOracleFwd,
      QueryImpl.add_apply_inr, AnswerTape.dupRandomOracle_apply_inl,
      AnswerTape.dupRandomOracle_apply_inr]

private theorem run_role_derive (role : Coverage.Role) (input : DeriveQuery core)
    (cache : (Coverage.jointSpec core).QueryCache) :
    (simulateQ (AnswerTape.dupRandomOracleFwd (Coverage.jointSpec core))
      (Coverage.roleImpl core role (.inr input))).run cache =
      ((Coverage.jointSpec core).randomOracle (.inr input)).run cache := by
  cases role <;>
    simp only [Coverage.roleImpl, simulateQ_spec_query, AnswerTape.dupRandomOracleFwd,
      QueryImpl.add_apply_inr, AnswerTape.dupRandomOracle_apply_inl,
      AnswerTape.dupRandomOracle_apply_inr]

private theorem deferred_hmsg (pkSeed : core.PkSeed) (R : core.Y) (seed : core.PkSeed)
    (root : core.Y) (message : List Byte) (state : D core) :
    ((slhGraph core pkSeed).deferredImpl
      (.inl (.inl (.inr (.inl (.hmsg R seed root message)))))).run state =
      (fun z => (z.1, ((z.2, state.1.2), state.2))) <$>
        ((hashSpec core).randomOracle (.inl (.hmsg R seed root message))).run state.1.1 := by
  have hn : ¬ ∃ node values,
      (slhGraph core pkSeed).childVals state.1 node = some values ∧
        (slhGraph core pkSeed).pt node values = .inl (.hmsg R seed root message) := by
    rintro ⟨node, values, _, eq⟩
    simp only [slhGraph_pt, Sum.inl.injEq] at eq
    cases eq
  rw [CanonicalGraph.deferredImpl_run_inl,
    CanonicalGraph.relabelImpl_run_pub_of_not_exists _ hn, Functor.map_map]

private theorem deferred_rand (pkSeed : core.PkSeed) (salt : core.Y)
    (message : List Byte) (state : D core) :
    ((slhGraph core pkSeed).deferredImpl (.inl (.inr (.inr (salt, message))))).run state =
      (fun z => (z.1, ((state.1.1, z.2), state.2))) <$>
        (((DeriveQuery core ⊕ NodeKey core) →ₒ core.Y).randomOracle
          (.inl (.inr (salt, message)))).run state.1.2 := by
  rw [CanonicalGraph.deferredImpl_run_inl, CanonicalGraph.relabelImpl_apply_inr,
    RelabelState.drawCell_run, Functor.map_map]
  rfl

private theorem cacheQuery_eq_self {ι : Type} {spec : OracleSpec.{0, 0} ι}
    [DecidableEq ι] (cache : spec.QueryCache) (input : ι) (answer : spec.Range input)
    (h : cache input = some answer) : cache.cacheQuery input answer = cache := by
  apply QueryCache.ext
  intro other
  by_cases eq : other = input
  · subst other
    simpa using h.symm
  · simp [QueryCache.cacheQuery_of_ne _ _ eq]

private theorem run_relative_other (pkSeed : core.PkSeed)
    (policy : SigningView.Event markerSpec Request → Nat)
    (input : (labSpec core).Domain) (other : ¬IsSelectedNative core input) (state : S core) :
    (simulateQ (AnswerTape.dupRandomOracleFwd (Coverage.jointSpec core))
      ((relative core pkSeed policy (.inl input)).run state)).run
        (nativeCache core state.1) =
      (fun result => (result, nativeCache core result.2.1)) <$>
        (((eraseObsImpl (Ev := SigningView.Event markerSpec Request)
          (slhGraph core pkSeed).deferredImpl).extendState
            (phaseCostAux core policy)) (.inl input)).run state := by
  rw [relative_other core pkSeed policy input other]
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure]
  rw [AnswerTape.dupRandomOracleFwd,
    QueryImpl.simulateQ_add_liftComp_left, unifFwdImpl.simulateQ_run]
  simp only [bind_map_left, QueryImpl.extendState_apply,
    eraseObsImpl, phaseCostAux]
  simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro z hz
  rw [nativeCache_deferred_other core pkSeed input other state.1 hz]

private theorem run_relative_step (pkSeed : core.PkSeed)
    (policy : SigningView.Event markerSpec Request → Nat)
    (input : (labSpec core + ObsSpec (SigningView.Event markerSpec Request)).Domain)
    (state : S core) :
    (simulateQ (AnswerTape.dupRandomOracleFwd (Coverage.jointSpec core))
      ((relative core pkSeed policy input).run state)).run (nativeCache core state.1) =
      (fun result => (result, nativeCache core result.2.1)) <$>
        (((eraseObsImpl (Ev := SigningView.Event markerSpec Request)
          (slhGraph core pkSeed).deferredImpl).extendState
            (phaseCostAux core policy)) input).run state := by
  cases input with
  | inr event =>
    simp only [relative_marker, simulateQ_pure, StateT.run_pure,
      QueryImpl.extendState_apply, eraseObsImpl,
      StateT.run_pure, pure_bind, map_pure]
  | inl native =>
    by_cases other : ¬IsSelectedNative core native
    · exact run_relative_other core pkSeed policy native other state
    · rcases native with (((n | (hash | prf)) | (secret | nonce)) | (touch | node))
      all_goals (try cases hash)
      all_goals try { exact (other (by change ¬False; exact not_false)).elim }
      · rename_i R seed root message
        rw [relative_hmsg]
        simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure]
        rw [run_role_hash]
        simp only [QueryImpl.extendState_apply, eraseObsImpl,
          phaseCostAux, map_bind]
        rw [deferred_hmsg core pkSeed R seed root message state.1]
        simp only [bind_map_left, map_pure]
        rw [randomOracle.run_eq, randomOracle.run_eq]
        rw [show (nativeCache core state.1) (.inl (.inl (.hmsg R seed root message))) =
          state.1.1.1 (.inl (.hmsg R seed root message)) from rfl]
        cases h : state.1.1.1 (.inl (.hmsg R seed root message)) with
        | some digest => simp [cacheQuery_eq_self _ _ _ h]
        | none => simp [nativeCache_hmsg]
      · rcases nonce with ⟨salt, message⟩
        rw [relative_rand]
        simp only [simulateQ_map, StateT.run_map]
        rw [run_role_derive]
        simp only [QueryImpl.extendState_apply, eraseObsImpl,
          phaseCostAux, map_bind]
        rw [deferred_rand core pkSeed salt message state.1]
        simp only [bind_map_left, map_pure]
        rw [randomOracle.run_eq, randomOracle.run_eq]
        rw [show (nativeCache core state.1) (.inr (.inr (salt, message))) =
          state.1.1.2 (.inl (.inr (salt, message))) from rfl]
        cases h : state.1.1.2 (.inl (.inr (salt, message))) with
        | some R => simp [cacheQuery_eq_self _ _ _ h]
        | none => simp [nativeCache_rand]

private theorem run_relative {α : Type} (pkSeed : core.PkSeed)
    (policy : SigningView.Event markerSpec Request → Nat)
    (program : OracleComp ((labSpec core + ObsSpec (SigningView.Event markerSpec Request))) α)
    (state : S core) :
    (simulateQ (AnswerTape.dupRandomOracleFwd (Coverage.jointSpec core))
      ((simulateQ (relative core pkSeed policy) program).run state)).run
        (nativeCache core state.1) =
      (fun result => (result, nativeCache core result.2.1)) <$>
        (simulateQ ((eraseObsImpl (Ev := SigningView.Event markerSpec Request)
          (slhGraph core pkSeed).deferredImpl).extendState
            (phaseCostAux core policy)) program).run state := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure a => simp
  | query_bind input k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
      simulateQ_bind, StateT.run_bind, map_bind]
    rw [run_relative_step]
    simp only [bind_map_left]
    apply bind_congr
    intro z
    exact ih z.1 z.2

private theorem run_roleRun_projected {α : Type}
    (program : OracleComp (Coverage.roleSpec core) α)
    (tapes : (j : Coverage.TapeClass) → List (Coverage.tapeClassRange core j)) :
    (fun result => (result.1, result.2.1.1)) <$>
        (simulateQ (Coverage.roleRunImpl core) program).run
          ((∅, tapes), (AnswerTape.ClassPos.init, ∅)) =
      (fun result => (result.1, result.2.1)) <$>
        (simulateQ (AnswerTape.tapeImplFwd (Coverage.tapeClassRange core)
          (Coverage.tapeClass core) (Coverage.range_eq_tapeClassRange core)) program).run
            (∅, tapes) := by
  have h := extendState_run_proj_eq
    (AnswerTape.tapeImplFwd (Coverage.tapeClassRange core)
      (Coverage.tapeClass core) (Coverage.range_eq_tapeClassRange core))
    (fun t s u s' pq =>
      (AnswerTape.classPosAuxFwd (Coverage.tapeClassRange core) (Coverage.tapeClass core)
        t s u s' pq.1,
       AnswerTape.freshHitAux (Coverage.IsRandPoint core) (Coverage.randRel core)
        t s u s' pq.2)) program (∅, tapes) (AnswerTape.ClassPos.init, ∅)
  have projected := congrArg (fun p => (fun result => (result.1, result.2.1)) <$> p) h
  simpa only [Coverage.roleRunImpl, AnswerTape.classPosImplFwd, Functor.map_map,
    Function.comp_def, Prod.map, id_eq] using projected

/-- Averaging native tapes preserves the complete deferred observation and selected cache. -/
theorem evalDist_relative_average_eq_deferred {α : Type}
    (pkSeed : core.PkSeed)
    (policy : SigningView.Event markerSpec Request → Nat)
    (program : OracleComp ((labSpec core + ObsSpec (SigningView.Event markerSpec Request)))
      α)
    (initialCost : Nat) (initialPhase : SigningView.Phase)
    (signerLength forgerLength : Nat) :
    let initial : S core := (((∅, ∅), []), (initialCost, initialPhase))
    let lengths : Coverage.TapeClass → Nat := fun
      | .signer => signerLength
      | .forger => forgerLength
      | .other => 0
    letI : MeasurableSpace
      ((α × S core) × (Coverage.jointSpec core).QueryCache) := ⊤
    𝒟[(do
      let tapes ← AnswerTape.tapeFamily (Coverage.tapeClassRange core) lengths
      let result ← (simulateQ (Coverage.roleRunImpl core)
        ((simulateQ (relative core pkSeed policy) program).run initial)).run
          ((∅, tapes), (AnswerTape.ClassPos.init, ∅))
      return (result.1, result.2.1.1))] =
      𝒟[(fun result => (result, nativeCache core result.2.1)) <$>
        (simulateQ
          ((eraseObsImpl (Ev := SigningView.Event markerSpec Request)
            (slhGraph core pkSeed).deferredImpl).extendState
              (phaseCostAux core policy)) program).run initial] := by
  let initial : S core := (((∅, ∅), []), (initialCost, initialPhase))
  let lengths : Coverage.TapeClass → Nat := fun
    | .signer => signerLength
    | .forger => forgerLength
    | .other => 0
  let : MeasurableSpace
      ((α × S core) × (Coverage.jointSpec core).QueryCache) := ⊤
  let source := (simulateQ (relative core pkSeed policy) program).run initial
  have averaged := AnswerTape.evalDist_run_dupRandomOracleFwd_eq_tapeFamily
    (R := Coverage.tapeClassRange core) (Coverage.tapeClass core)
      (Coverage.range_eq_tapeClassRange core) source ∅ lengths
  calc
    _ = 𝒟[(do
      let tapes ← AnswerTape.tapeFamily (Coverage.tapeClassRange core) lengths
      let result ← (simulateQ (AnswerTape.tapeImplFwd (Coverage.tapeClassRange core)
        (Coverage.tapeClass core) (Coverage.range_eq_tapeClassRange core)) source).run (∅, tapes)
      return (result.1, result.2.1))] := by
        congr 1
        apply bind_congr
        intro tapes
        simpa only [map_eq_bind_pure_comp, Function.comp_def] using
          run_roleRun_projected core source tapes
    _ = 𝒟[(simulateQ (AnswerTape.dupRandomOracleFwd (Coverage.jointSpec core))
      source).run ∅] := averaged.symm
    _ = _ := by
      have h := run_relative core pkSeed policy program initial
      simpa only [initial, nativeCache_empty] using congrArg evalDist h

end SLHDSA.Security.CoverageDeferred

end
section

open OracleComp OracleSpec SignatureAlg
open SLHDSA SLHDSA.Security SLHDSA.SHAKE128s
open SLHDSA.SHAKE128s.Bridge.SharedExperiment
open SLHDSA.SHAKE128s.Bridge.SharedExperiment.Guarded
open MeasureTheory
namespace SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native

/-- Converting each independently drawn raw answer gives the typed answer list. -/
private theorem padding_map_answerEquiv (n : Nat) :
    List.map Bridge.answerEquiv <$> DigestTape.padding n =ᵈ
      AnswerTape.tapeList FIPS205.Answer n := by
  induction n with
  | zero => simp [DigestTape.padding, AnswerTape.tapeList_zero]
  | succ n ih =>
    calc
      List.map Bridge.answerEquiv <$> DigestTape.padding (n + 1)
          = (do
              let value ← Bridge.answerEquiv <$> ($ᵗ HashOutput : ProbComp HashOutput)
              let rest ← List.map Bridge.answerEquiv <$> DigestTape.padding n
              pure (value :: rest)) := by
            simp only [DigestTape.padding, map_bind, map_pure, bind_map_left,
              List.map_cons]
      _ =ᵈ (do
              let value ← ($ᵗ FIPS205.Answer : ProbComp FIPS205.Answer)
              let rest ← AnswerTape.tapeList FIPS205.Answer n
              pure (value :: rest)) := by
            exact (Bridge.map_answerEquiv_uniformSample.bind_left _).trans
              (EvalDistEq.bind_right _ fun _ => ih.bind_left _)
      _ = AnswerTape.tapeList FIPS205.Answer (n + 1) :=
        (AnswerTape.tapeList_succ n).symm

/-- The two raw independent padding blocks, converted to typed answers, have the existing
three-class tape-family law. The other class has an empty initial tape. -/
theorem padding_pair_tapeFamily (L R : Nat) :
    (do
      let left ← DigestTape.padding L
      let right ← DigestTape.padding R
      pure (show (j : Coverage.TapeClass) →
          List (Coverage.tapeClassRange FIPS205.core j) from fun
        | .signer => left.map Bridge.answerEquiv
        | .forger => right.map Bridge.answerEquiv
        | .other => ([] : List FIPS205.core.Y))) =ᵈ
      AnswerTape.tapeFamily (Coverage.tapeClassRange FIPS205.core)
        (fun | .signer => L | .forger => R | .other => 0) := by
  let lengths : Coverage.TapeClass → Nat
    | .signer => L
    | .forger => R
    | .other => 0
  let assemble (left right : List FIPS205.Answer) :
      (j : Coverage.TapeClass) → List (Coverage.tapeClassRange FIPS205.core j)
    | .signer => left
    | .forger => right
    | .other => []
  let family := AnswerTape.tapeFamily (Coverage.tapeClassRange FIPS205.core) lengths
  let _ : MeasurableSpace
      ((j : Coverage.TapeClass) → List (Coverage.tapeClassRange FIPS205.core j)) := ⊤
  let _ : DiscreteMeasurableSpace
      ((j : Coverage.TapeClass) → List (Coverage.tapeClassRange FIPS205.core j)) :=
    ⟨fun _ => trivial⟩
  have reconstruct :
      (fun tapes => assemble (tapes .signer) (tapes .forger)) <$> family = family := by
    calc
      _ = family >>= pure := by
        simp only [map_eq_bind_pure_comp]
        apply bind_congr_of_forall_mem_support
        intro tapes htapes
        change (pure (assemble (tapes .signer) (tapes .forger)) : ProbComp _) = pure tapes
        apply congrArg (fun t => (pure t : ProbComp _))
        funext j
        cases j with
        | signer => rfl
        | forger => rfl
        | other =>
          have hlen := AnswerTape.length_of_mem_support_tapeFamily lengths htapes
            Coverage.TapeClass.other
          exact (List.eq_nil_of_length_eq_zero (by simpa only [lengths] using hlen)).symm
      _ = family := by simp
  have joint := AnswerTape.evalDist_tapeFamily_bind_eval₂
    (R := Coverage.tapeClassRange FIPS205.core)
    (j := Coverage.TapeClass.signer) (j' := Coverage.TapeClass.forger)
    (by decide) lengths (fun left right => pure (assemble left right))
  have typed :
      (do
        let left ← AnswerTape.tapeList FIPS205.Answer L
        let right ← AnswerTape.tapeList FIPS205.Answer R
        pure (assemble left right)) =ᵈ family := by
    apply evalDistEq_iff_evalDist_eq.mpr
    calc
      _ = 𝒟[(fun tapes => assemble (tapes .signer) (tapes .forger)) <$> family] := by
        simpa only [family, lengths, map_eq_bind_pure_comp, Function.comp_def,
          Coverage.instSampleableTypeTapeClassRange] using joint.symm
      _ = 𝒟[family] := congrArg evalDist reconstruct
  have converted :
      (do
        let left ← List.map Bridge.answerEquiv <$> DigestTape.padding L
        let right ← List.map Bridge.answerEquiv <$> DigestTape.padding R
        pure (assemble left right)) =ᵈ family := by
    exact (((padding_map_answerEquiv L).bind_left _).trans
      (EvalDistEq.bind_right _ fun _ => (padding_map_answerEquiv R).bind_left _)).trans typed
  simpa only [bind_map_left] using converted

end SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native

end
section

open OracleComp OracleSpec SignatureAlg
open SLHDSA SLHDSA.Security SLHDSA.SHAKE128s
open SLHDSA.SHAKE128s.Bridge.SharedExperiment
open SLHDSA.SHAKE128s.Bridge.SharedExperiment.Guarded
open MeasureTheory
namespace SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native

/-- Passive marker observation and deferred graph simulation differ only in state order. -/
private theorem observe_deferred_square
    (s : FIPS205.core.PkSeed) (adv : Game.Adversary FIPS205.Answer PK)
    (reserve : Bool) (caps : Nat × Nat)
    (fallback : (input : LabCommon.Domain) → LabCommon.Range input) :
    (simulateQ (slhGraph FIPS205.core s).deferredImpl
      (deferredProgram s adv reserve caps fallback)).run ((∅, ∅), []) =
      (fun result : (((Guarded.Full × (PUnit × Paid)) × Raw.QueryCache) ×
          CoverageDeferred.S FIPS205.core) =>
        ((result.1, result.2.2), result.2.1)) <$>
        (simulateQ
          ((eraseObsImpl (Ev := Ev) (slhGraph FIPS205.core s).deferredImpl).extendState
            (CoverageDeferred.phaseCostAux FIPS205.core (metadataCost true s)))
          (guardedRoutedSource s adv reserve caps fallback)).run
            (((∅, ∅), []), (0, .keygen)) := by
  let _ : MonadLiftT (OracleComp Lab) (StateT Meta (OracleComp Lab)) :=
    ⟨fun action => StateT.lift action⟩
  let observer : QueryImpl (Lab + O) (StateT Meta (OracleComp Lab)) :=
    QueryImpl.add
      ((QueryImpl.id' Lab).liftTarget (StateT Meta (OracleComp Lab)))
      (fun event => StateT.mk fun metadata =>
        pure (PUnit.unit, match event with
          | .ambient phase input =>
              (metadata.1 + metadataCost true s (.ambient phase input), phase)
          | .signingAttempt request =>
              (metadata.1 + metadataCost true s (.signingAttempt request), .signer)))
  let actual :=
    (eraseObsImpl (Ev := Ev) (slhGraph FIPS205.core s).deferredImpl).extendState
      (CoverageDeferred.phaseCostAux FIPS205.core (metadataCost true s))
  let combined := ((slhGraph FIPS205.core s).deferredImpl.mapStateTBase observer).flattenStateT
  have square : ∀ input state,
      Prod.map id Prod.swap <$> (combined input).run state =
        (actual input).run (Prod.swap state) := by
    intro input state
    rcases state with ⟨metadata, graph⟩
    rcases input with native | event
    · simp [combined, actual, QueryImpl.flattenStateT, QueryImpl.mapStateTBase,
        observer, eraseObsImpl, QueryImpl.extendState, QueryImpl.add,
        QueryImpl.liftTarget, QueryImpl.id', Functor.map_map, StateT.run_map,
        Prod.map, Prod.swap, CoverageDeferred.phaseCostAux]
    · cases event <;>
        simp [combined, actual, QueryImpl.flattenStateT, QueryImpl.mapStateTBase,
          observer, eraseObsImpl, QueryImpl.extendState, QueryImpl.add,
          QueryImpl.liftTarget, QueryImpl.id',
          Prod.map, Prod.swap, CoverageDeferred.phaseCostAux]
  have h := map_run_simulateQ_eq_of_query_map_eq combined actual Prod.swap square
    (guardedRoutedSource s adv reserve caps fallback) ((0, .keygen), ((∅, ∅), []))
  have forward :
      (fun result : ((((Guarded.Full × (PUnit × Paid)) × Raw.QueryCache) × Meta) ×
          CoverageDeferred.D FIPS205.core) =>
        (result.1.1, (result.2, result.1.2))) <$>
        (simulateQ (slhGraph FIPS205.core s).deferredImpl
          (deferredProgram s adv reserve caps fallback)).run ((∅, ∅), []) =
      (simulateQ actual (guardedRoutedSource s adv reserve caps fallback)).run
        (((∅, ∅), []), (0, .keygen)) := by
    change _ <$> (simulateQ (slhGraph FIPS205.core s).deferredImpl
      ((simulateQ observer (guardedRoutedSource s adv reserve caps fallback)).run
        (0, .keygen))).run ((∅, ∅), []) = _
    rw [simulateQ_mapStateTBase_run_eq_map_flattenStateT]
    simp only [Functor.map_map]
    change (Prod.map id Prod.swap <$> _) = _
    exact h
  have back := congrArg (fun computation =>
    (fun result : (((Guarded.Full × (PUnit × Paid)) × Raw.QueryCache) ×
        CoverageDeferred.S FIPS205.core) =>
      ((result.1, result.2.2), result.2.1)) <$> computation) forward
  simpa [actual, Functor.map_map, Function.comp_def] using back

theorem native_deferred_marginal :
  ∀ (s : FIPS205.core.PkSeed) (adv : Game.Adversary FIPS205.Answer PK)
    (reserve : Bool) (caps : Nat × Nat)
    (fallback : (input : LabCommon.Domain) → LabCommon.Range input) (L R : Nat),
    let project := fun t : NativeTerminal =>
      ((((t.1, (PUnit.unit, t.2.2)), t.2.1.1.1), t.2.1.1.2.2), t.2.1.1.2.1)
    (fun outcome => project outcome.2) <$>
      NoticingTape.blockRunOf (nativeRun s adv reserve caps fallback) L R =ᵈ
        (simulateQ (slhGraph FIPS205.core s).deferredImpl
          (deferredProgram s adv reserve caps fallback)).run ((∅, ∅), [])
 := by
  intro s adv reserve caps fallback L R
  dsimp only
  let program := guardedRoutedSource s adv reserve caps fallback
  let initial : CoverageDeferred.S FIPS205.core := (((∅, ∅), []), (0, .keygen))
  let runTapes := fun tapes =>
    (simulateQ (Coverage.roleRunImpl FIPS205.core)
      ((simulateQ (CoverageDeferred.relative FIPS205.core s (metadataCost true s))
        program).run initial)).run ((∅, tapes), (AnswerTape.ClassPos.init, ∅))
  let regroup := fun result :
      (((Guarded.Full × (PUnit × Paid)) × Raw.QueryCache) × CoverageDeferred.S FIPS205.core) =>
    ((result.1, result.2.2), result.2.1)
  have averaged := CoverageDeferred.evalDist_relative_average_eq_deferred
    FIPS205.core s (metadataCost true s) program 0 .keygen L R
  have eqDist := evalDistEq_iff_evalDist_eq.mpr averaged
  have projected := eqDist.map (fun result => regroup result.1)
  calc
    _ = (do
        let tapes ← (do
          let left ← DigestTape.padding L
          let right ← DigestTape.padding R
          pure (show (j : Coverage.TapeClass) →
              List (Coverage.tapeClassRange FIPS205.core j) from fun
            | .signer => left.map Bridge.answerEquiv
            | .forger => right.map Bridge.answerEquiv
            | .other => ([] : List FIPS205.core.Y)))
        let result ← runTapes tapes
        pure (regroup result.1)) := by
      simp only [NoticingTape.blockRunOf, nativeRun, map_bind, map_pure,
        bind_assoc, pure_bind, runTapes, program, initial, regroup]
      apply bind_congr
      intro left
      apply bind_congr
      intro right
      apply bind_congr
      intro result
      rcases result with ⟨⟨⟨⟨full, ⟨token, paid⟩⟩, raw⟩, ⟨graph, metadata⟩⟩, role⟩
      cases token
      rfl
    _ =ᵈ _ := by
      have average :
          (do
            let tapes ← AnswerTape.tapeFamily (Coverage.tapeClassRange FIPS205.core)
              (fun | .signer => L | .forger => R | .other => 0)
            let result ← runTapes tapes
            pure (regroup result.1)) =ᵈ
          regroup <$>
            (simulateQ
              ((eraseObsImpl (Ev := Ev) (slhGraph FIPS205.core s).deferredImpl).extendState
                (CoverageDeferred.phaseCostAux FIPS205.core (metadataCost true s)))
              program).run initial := by
        have normalized := projected
        simp only [map_bind, map_pure, Functor.map_map, regroup] at normalized
        convert normalized using 1
      have final :
          regroup <$>
            (simulateQ
              ((eraseObsImpl (Ev := Ev) (slhGraph FIPS205.core s).deferredImpl).extendState
                (CoverageDeferred.phaseCostAux FIPS205.core (metadataCost true s)))
              program).run initial =ᵈ
          (simulateQ (slhGraph FIPS205.core s).deferredImpl
            (deferredProgram s adv reserve caps fallback)).run ((∅, ∅), []) := by
        rw [← observe_deferred_square s adv reserve caps fallback]
      exact ((padding_pair_tapeFamily L R).bind_left _).trans (average.trans final)

end SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native

end
