/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Security.NativeRelative
public import VCVio.OracleComp.QueryTracking.Enforcement
import VCVio.OracleComp.Coercions.Add.Basic
import VCVio.OracleComp.QueryTracking.SubSpec
import all HashSig.SLHDSA.Security.NativeRelative
import all VCVio.OracleComp.QueryTracking.RandomOracle.ClassIndexedTape.Position

/-! # Phase and callback counts for marked native execution

Optional observations share a marker policy across native phases and signing callbacks.
Paid work, admitted attempts, native tape counts and independent Nat metadata remain in one run.
The structural lemmas impose no seed-independence or probability hypothesis.
-/

public section
open OracleComp OracleSpec SignatureAlg

namespace SLHDSA.Security.NativeCounts

variable {vp : ValidatedParams} (core : CorePrimitives vp.params)
variable [SampleableType core.Y] [SampleableType (Bytes vp.params.m)]
  [DecidableEq core.Y] [DecidableEq core.PkSeed] [DecidableEq core.AdrsKey]
  [DecidableEq core.SkPrf]

private theorem native_cnt_step
    (input : (Coverage.roleSpec core).Domain) (state : Coverage.RoleState core)
    (result : (Coverage.roleSpec core).Range input × Coverage.RoleState core)
    (hr : result ∈ support ((Coverage.roleRunImpl core input).run state))
    (j : Coverage.TapeClass) :
    result.2.2.1.cnt j = state.2.1.cnt j +
      if AnswerTape.classOf (Coverage.tapeClass core) input = some j then 1 else 0 := by
  obtain ⟨_, haux⟩ := (QueryImpl.mem_support_extendState_run_iff _ _ input state result).mp hr
  rw [congrArg (fun p => p.1.cnt j) haux]
  rcases input with n | t
  · simp [AnswerTape.classPosAuxFwd, AnswerTape.classOf]
  · have hstep : ∀ (k : Coverage.TapeClass) (t : (Coverage.jointSpec core).Domain) s u s'
        (p : AnswerTape.ClassPos (Coverage.jointSpec core).Domain Coverage.TapeClass),
        (AnswerTape.classPosStep (Coverage.tapeClassRange core) k t s u s' p).cnt =
          Function.update p.cnt k (p.cnt k + 1) := by
      intro k t s u s' p
      unfold AnswerTape.classPosStep
      split <;> rfl
    have hcnt : (AnswerTape.classPosAuxFwd (Coverage.tapeClassRange core)
        (Coverage.tapeClass core) (.inr t) state.1 result.1 result.2.1 state.2.1).cnt =
        Function.update state.2.1.cnt (Coverage.tapeClass core t)
          (state.2.1.cnt (Coverage.tapeClass core t) + 1) := by
      rcases t with t | t <;> exact hstep _ t state.1 result.1 result.2.1 state.2.1
    rw [hcnt]
    by_cases hj : Coverage.tapeClass core t = j
    · subst j; simp [AnswerTape.classOf]
    · simp [AnswerTape.classOf, hj, Function.update_of_ne (Ne.symm hj)]

private theorem native_cnt_le {α : Type} (program : OracleComp (Coverage.roleSpec core) α)
    (j : Coverage.TapeClass) {n : Nat}
    (hb : IsQueryBoundP program
      (fun input => AnswerTape.classOf (Coverage.tapeClass core) input = some j) n)
    (initial : Coverage.RoleState core) (result : α × Coverage.RoleState core)
    (hr : result ∈ support ((simulateQ (Coverage.roleRunImpl core) program).run initial)) :
    result.2.2.1.cnt j ≤ initial.2.1.cnt j + n := by
  apply hb.cost_le_of_mem_support_run_simulateQ (fun s => s.2.1.cnt j) _ _ initial result hr
  · intro input hi state result hr
    exact (by simpa [hi] using (native_cnt_step core input state result hr j).le)
  · intro input hi state result hr
    exact (by simpa [hi] using (native_cnt_step core input state result hr j).le)

omit [SampleableType core.Y] [SampleableType (Bytes vp.params.m)]
  [DecidableEq core.Y] [DecidableEq core.PkSeed] [DecidableEq core.AdrsKey]
  [DecidableEq core.SkPrf] in
private theorem uniform_hmsg_bound {α : Type} (program : ProbComp α)
    (j : Coverage.TapeClass) :
    IsQueryBoundP (liftComp program (Coverage.roleSpec core))
      (fun input => AnswerTape.classOf (Coverage.tapeClass core) input = some j) 0 := by
  exact IsQueryBoundP.liftComp_subSpec (p := fun _ => False)
    (fun _ => by simp [SubSpec.onQuery, AnswerTape.classOf])
    (isQueryBoundP_false program 0)

/-- The native tape class of each signing-experiment phase. -/
@[expose]
def phaseClass : SigningView.Phase → Coverage.TapeClass
  | .keygen | .signer => .signer
  | .adversary | .verification => .forger

variable {ιm Request : Type} {markerSpec : OracleSpec.{0, 0} ιm}

/-- The existing secret-free Hmsg predicate lifted to the lab interface. -/
@[expose]
def IsLabHmsg : (labSpec core).Domain → Prop
  | .inl native => Coverage.IsHmsgQuery core native
  | .inr _ => False

instance : DecidablePred (IsLabHmsg core) := fun input =>
  match input with
  | .inl native => inferInstanceAs (Decidable (Coverage.IsHmsgQuery core native))
  | .inr _ => isFalse id



private theorem other_hmsg_bound (pkSeed : core.PkSeed)
    (markerCost : SigningView.Event markerSpec Request → Nat)
    (input : (labSpec core).Domain) (hi : ¬ CoverageDeferred.IsSelectedNative core input)
    (state : CoverageDeferred.S core) (j : Coverage.TapeClass) :
    IsQueryBoundP ((CoverageDeferred.relative core pkSeed markerCost (.inl input)).run state)
      (fun input => AnswerTape.classOf (Coverage.tapeClass core) input = some j) 0 := by
  rw [CoverageDeferred.relative_other core pkSeed markerCost input hi state]
  exact isQueryBoundP_bind (uniform_hmsg_bound core _ j)
    (fun _ _ => isQueryBoundP_pure _ _ 0)

private theorem relative_hmsg_bound (pkSeed : core.PkSeed)
    (markerCost : SigningView.Event markerSpec Request → Nat)
    (input : (labSpec core).Domain) (state : CoverageDeferred.S core)
    (j : Coverage.TapeClass) (hj : j ≠ .other) :
    IsQueryBoundP ((CoverageDeferred.relative core pkSeed markerCost (.inl input)).run state)
      (fun input => AnswerTape.classOf (Coverage.tapeClass core) input = some j)
      (if IsLabHmsg core input ∧ j = phaseClass state.2.2 then 1 else 0) := by
  rcases input with (((n | (hash | prf)) | (secret | nonce)) | (touch | read))
  · exact (other_hmsg_bound core pkSeed markerCost _ (by simp [CoverageDeferred.IsSelectedNative])
      state j).mono (Nat.zero_le _)
  · cases hash with
    | thash seed address values =>
        exact (other_hmsg_bound core pkSeed markerCost _
          (by simp [CoverageDeferred.IsSelectedNative]) state j).mono (Nat.zero_le _)
    | hmsg R seed root message =>
        rw [CoverageDeferred.relative_hmsg]
        rcases state with ⟨graph, cost, phase⟩
        cases phase <;> cases j <;>
          simp_all [CoverageDeferred.phaseRole, Coverage.roleImpl, phaseClass,
            IsLabHmsg, Coverage.IsHmsgQuery, Coverage.tapeClass, AnswerTape.classOf,
            isQueryBoundP_query_iff]
  · exact (other_hmsg_bound core pkSeed markerCost _ (by simp [CoverageDeferred.IsSelectedNative])
      state j).mono (Nat.zero_le _)
  · exact (other_hmsg_bound core pkSeed markerCost _ (by simp [CoverageDeferred.IsSelectedNative])
      state j).mono (Nat.zero_le _)
  · rcases nonce with ⟨salt, message⟩
    rw [CoverageDeferred.relative_rand]
    rcases state with ⟨graph, cost, phase⟩
    cases phase <;> cases j <;>
      simp_all [CoverageDeferred.phaseRole, Coverage.roleImpl, phaseClass,
        IsLabHmsg, Coverage.IsHmsgQuery, Coverage.tapeClass, AnswerTape.classOf,
        isQueryBoundP_query_iff]
  · exact (other_hmsg_bound core pkSeed markerCost _ (by simp [CoverageDeferred.IsSelectedNative])
      state j).mono (Nat.zero_le _)
  · exact (other_hmsg_bound core pkSeed markerCost _ (by simp [CoverageDeferred.IsSelectedNative])
      state j).mono (Nat.zero_le _)

/-- Relative graph execution interpreted by the existing native role handler. -/
noncomputable abbrev nativeImpl (pkSeed : core.PkSeed)
    (markerCost : SigningView.Event markerSpec Request → Nat) :=
  ((Coverage.roleRunImpl core).mapStateTBase
    (CoverageDeferred.relative core pkSeed markerCost)).flattenStateT

/-- Sharp native bound, with arbitrary independent existing metadata cost. -/
theorem native_hmsg_count_le
    {vp : ValidatedParams} (core : CorePrimitives vp.params)
    [SampleableType core.Y] [SampleableType (Bytes vp.params.m)]
    [DecidableEq core.Y] [DecidableEq core.PkSeed] [DecidableEq core.AdrsKey]
    [DecidableEq core.SkPrf] {ιm Request : Type} {markerSpec : OracleSpec.{0, 0} ιm}
    (pkSeed : core.PkSeed) (markerCost : SigningView.Event markerSpec Request → Nat)
    (input : (labSpec core).Domain)
    (state : CoverageDeferred.S core × Coverage.RoleState core)
    (result : (labSpec core).Range input ×
      (CoverageDeferred.S core × Coverage.RoleState core))
    (hr : result ∈ support
      ((((Coverage.roleRunImpl core).mapStateTBase
        (CoverageDeferred.relative core pkSeed markerCost)).flattenStateT
          (.inl input)).run state))
    (j : Coverage.TapeClass) (hj : j ≠ .other) :
    result.2.2.2.1.cnt j ≤ state.2.2.1.cnt j +
      if IsLabHmsg core input ∧ j =
        (match state.1.2.2 with
          | .keygen | .signer => .signer
          | .adversary | .verification => .forger) then 1 else 0 := by
  rw [QueryImpl.flattenStateT_mapStateTBase_apply_run, support_map] at hr
  obtain ⟨out, hout, rfl⟩ := hr
  cases hphase : state.1.2.2 <;>
    simpa only [phaseClass, hphase] using
      native_cnt_le core _ j
        (relative_hmsg_bound core pkSeed markerCost input state.1 j hj) state.2 out hout


/-- Guard marked native execution with a joint work and signing-attempt budget. -/
noncomputable abbrev guardedImpl (pkSeed : core.PkSeed) (caps : Nat × Nat)
    (policy : SigningView.Event markerSpec Request → Nat × Nat)
    (markerCost : SigningView.Event markerSpec Request → Nat)
    (fallback : (input : (labSpec core + ObsSpec
      (SigningView.Event markerSpec Request)).Domain) →
      (labSpec core + ObsSpec (SigningView.Event markerSpec Request)).Range input) :=
  QueryImpl.guardQueryBudget caps (Sum.elim (fun _ => (0, 0)) policy)
    (nativeImpl core pkSeed markerCost) fallback

private theorem nativeImpl_marker (pkSeed : core.PkSeed)
    (markerCost : SigningView.Event markerSpec Request → Nat)
    (event : SigningView.Event markerSpec Request)
    (state : CoverageDeferred.S core × Coverage.RoleState core) :
    (nativeImpl core pkSeed markerCost (.inr event)).run state =
      pure (⟨⟩, ((state.1.1,
        CoverageDeferred.phaseCostAux core markerCost (.inr event)
          state.1.1 ⟨⟩ state.1.1 state.1.2), state.2)) := by
  rw [nativeImpl, QueryImpl.flattenStateT_mapStateTBase_apply_run,
    CoverageDeferred.relative_marker]
  simp

private theorem guardedImpl_aborted (pkSeed : core.PkSeed) (caps : Nat × Nat)
    (policy : SigningView.Event markerSpec Request → Nat × Nat)
    (markerCost : SigningView.Event markerSpec Request → Nat)
    (fallback : (input : (labSpec core + ObsSpec (SigningView.Event markerSpec Request)).Domain) →
      (labSpec core + ObsSpec (SigningView.Event markerSpec Request)).Range input)
    {α : Type} (program : OracleComp (labSpec core + ObsSpec (SigningView.Event markerSpec Request))
      α)
    (initial : (CoverageDeferred.S core × Coverage.RoleState core) × ((Nat × Nat) × Bool))
    (hi : initial.2.2 = true) (result : α ×
      ((CoverageDeferred.S core × Coverage.RoleState core) × ((Nat × Nat) × Bool)))
    (hr : result ∈ support
      ((simulateQ (guardedImpl core pkSeed caps policy markerCost fallback) program).run initial)) :
    result.2 = initial := by
  apply simulateQ_run_preservesInv (guardedImpl core pkSeed caps policy markerCost fallback)
    (fun state => state = initial) _ program initial rfl result hr
  intro input state hs output hout
  subst state
  have heq : output = (fallback input, initial) := by
    simpa [guardedImpl, QueryImpl.guardQueryBudget, hi] using hout
  exact congrArg Prod.snd heq

/-- Native queries with optional observations in an independent marker signature. -/
@[expose]
def phaseObservation
    (observe : (labSpec core).Domain → Option markerSpec.Domain)
    (phase : SigningView.Phase) :
    QueryImpl (labSpec core)
      (OracleComp (labSpec core + ObsSpec (SigningView.Event markerSpec Request))) :=
  QueryImpl.preInsert
    (fun input => (liftM ((labSpec core + ObsSpec
      (SigningView.Event markerSpec Request)).query (.inl input)) :
      OracleComp (labSpec core + ObsSpec (SigningView.Event markerSpec Request))
        ((labSpec core).Range input)))
    (fun input => match observe input with
      | some label => liftM ((labSpec core + ObsSpec
          (SigningView.Event markerSpec Request)).query (.inr (.ambient phase label)))
      | none => pure PUnit.unit)

private theorem nativeImpl_native_metadata (pkSeed : core.PkSeed)
    (markerCost : SigningView.Event markerSpec Request → Nat)
    (input : (labSpec core).Domain)
    (state : CoverageDeferred.S core × Coverage.RoleState core)
    (result : (labSpec core).Range input ×
      (CoverageDeferred.S core × Coverage.RoleState core))
    (hr : result ∈ support ((nativeImpl core pkSeed markerCost (.inl input)).run state)) :
    result.2.1.2 = state.1.2 := by
  rw [nativeImpl, QueryImpl.flattenStateT_mapStateTBase_apply_run, support_map] at hr
  obtain ⟨out, hout, rfl⟩ := hr
  rcases input with (((n | (hash | prf)) | (secret | nonce)) | (touch | read))
  all_goals (try cases hash)
  all_goals
    simp only [CoverageDeferred.relative, StateT.run_mk, simulateQ_bind,
      simulateQ_pure, StateT.run_bind, StateT.run_pure, mem_support_bind_iff] at hout
    obtain ⟨middle, _, hlast⟩ := hout
    simp only [support_pure, Set.mem_singleton_iff] at hlast
    subst out
    rfl

private theorem phase_step
    (observe : (labSpec core).Domain → Option markerSpec.Domain)
    (paidPolicy : SigningView.Event markerSpec Request → Nat × Nat)
    (markerCost : SigningView.Event markerSpec Request → Nat)
    (hselected : ∀ input, IsLabHmsg core input → ∃ label, observe input = some label)
    (hsecond : ∀ phase input label, observe input = some label →
      (paidPolicy (.ambient phase label)).2 = 0)
    (hpaid : ∀ phase input label, observe input = some label →
      IsLabHmsg core input → phaseClass phase = .forger →
      1 ≤ (paidPolicy (.ambient phase label)).1)
    (pkSeed : core.PkSeed) (caps : Nat × Nat)
    (fallback : (input : (labSpec core + ObsSpec
        (SigningView.Event markerSpec Request)).Domain) →
      (labSpec core + ObsSpec (SigningView.Event markerSpec Request)).Range input)
    (phase : SigningView.Phase) (input : (labSpec core).Domain)
    (state : (CoverageDeferred.S core × Coverage.RoleState core) × ((Nat × Nat) × Bool))
    (result : (labSpec core).Range input ×
      ((CoverageDeferred.S core × Coverage.RoleState core) × ((Nat × Nat) × Bool)))
    (hr : result ∈ support ((simulateQ
      (guardedImpl core pkSeed caps paidPolicy markerCost fallback)
      (phaseObservation core observe phase input)).run state)) :
    (result.2.2.1.2 = state.2.1.2 ∧
    result.2.1.2.2.1.cnt .signer ≤ state.1.2.2.1.cnt .signer +
      (if IsLabHmsg core input ∧ .signer = phaseClass phase then 1 else 0) ∧
    result.2.1.2.2.1.cnt .forger + state.2.1.1 ≤
      state.1.2.2.1.cnt .forger + result.2.2.1.1 ∧
    ((∀ label, observe input = some label → IsLabHmsg core input →
        phaseClass phase = .forger → 1 ≤ markerCost (.ambient phase label)) →
      result.2.1.2.2.1.cnt .forger + state.1.1.2.1 ≤
        state.1.2.2.1.cnt .forger + result.2.1.1.2.1)) ∧
    ((state.1.1.2.2 = phase ∧
      (∀ label, markerCost (.ambient phase label) = 0)) →
      result.2.1.1.2 = state.1.1.2) := by
  rcases state with ⟨⟨⟨graph, metadata, oldPhase⟩, native⟩, paid, flag⟩
  cases hobs : observe input with
  | none =>
    have hh : ¬IsLabHmsg core input := by
      intro hi
      obtain ⟨label, hl⟩ := hselected input hi
      rw [hobs] at hl
      cases hl
    simp only [phaseObservation, QueryImpl.preInsert_apply, hobs, pure_bind,
      monadLift_self, simulateQ_spec_query, guardedImpl, QueryImpl.guardQueryBudget,
      StateT.run_mk, Sum.elim_inl, Prod.mk_zero_zero, add_zero] at hr
    split_ifs at hr with hflag hcap
    · have heq : result = (fallback (.inl input),
          (((graph, metadata, oldPhase), native), (paid, flag))) := by
        simpa only [support_pure, Set.mem_singleton_iff] using hr
      subst result
      constructor
      · simp only [hh, false_and, ite_false, Nat.add_zero]
        exact ⟨True.intro, le_rfl, le_rfl, fun _ => le_rfl⟩
      · intro _
        rfl
    · rw [support_map] at hr
      obtain ⟨out, hout, rfl⟩ := hr
      have hc := native_hmsg_count_le core pkSeed markerCost input
        ((graph, metadata, oldPhase), native) out hout .signer (by decide)
      have hn := native_hmsg_count_le core pkSeed markerCost input
        ((graph, metadata, oldPhase), native) out hout .forger (by decide)
      have hm := nativeImpl_native_metadata core pkSeed markerCost input
        ((graph, metadata, oldPhase), native) out hout
      have hmn : out.2.1.2.1 = metadata := congrArg Prod.fst hm
      constructor
      · simp only [hh, false_and, ite_false, Nat.add_zero] at hc hn ⊢
        refine ⟨True.intro, hc, ?_, ?_⟩
        · omega
        · intro _
          omega
      · intro _
        exact hm
    · have heq : result = (fallback (.inl input),
          (((graph, metadata, oldPhase), native), (paid, true))) := by
        simpa only [support_pure, Set.mem_singleton_iff] using hr
      subst result
      constructor
      · simp only [hh, false_and, ite_false, Nat.add_zero]
        exact ⟨True.intro, le_rfl, le_rfl, fun _ => le_rfl⟩
      · intro _
        rfl
  | some label =>
    simp only [phaseObservation, QueryImpl.preInsert_apply, hobs, monadLift_self,
      simulateQ_bind, simulateQ_spec_query, StateT.run_bind] at hr
    rw [mem_support_bind_iff] at hr
    obtain ⟨middle, hm, hr⟩ := hr
    simp only [guardedImpl, QueryImpl.guardQueryBudget, StateT.run_mk] at hm
    split_ifs at hm with hflag hcap
    · have heq : middle = (fallback (.inr (.ambient phase label)),
          (((graph, metadata, oldPhase), native), (paid, flag))) := by
        simpa only [support_pure, Set.mem_singleton_iff] using hm
      subst middle
      have heq : result = (fallback (.inl input),
          (((graph, metadata, oldPhase), native), (paid, flag))) := by
        simpa [guardedImpl, QueryImpl.guardQueryBudget, hflag] using hr
      subst result
      exact ⟨⟨rfl, Nat.le_add_right _ _, le_rfl, fun _ => le_rfl⟩, fun _ => rfl⟩
    · rw [nativeImpl_marker] at hm
      simp only [map_pure, support_pure, Set.mem_singleton_iff] at hm
      subst middle
      simp only [guardedImpl, QueryImpl.guardQueryBudget, StateT.run_mk,
        Sum.elim_inl, Sum.elim_inr, Bool.false_eq_true, ↓reduceIte,
        Prod.mk_zero_zero, add_zero, Prod.le_def, Prod.fst_add, Prod.snd_add] at hr
      have hcap' : paid.1 + (paidPolicy (.ambient phase label)).1 ≤ caps.1 ∧
          paid.2 + (paidPolicy (.ambient phase label)).2 ≤ caps.2 := by
        simpa only [Sum.elim_inr, Prod.le_def, Prod.fst_add, Prod.snd_add] using hcap
      rw [ite_eq_left hcap', support_map] at hr
      obtain ⟨out, hout, rfl⟩ := hr
      have hc := native_hmsg_count_le core pkSeed markerCost input
        ((graph, metadata + markerCost (.ambient phase label), phase), native)
        out hout .signer (by decide)
      have hn := native_hmsg_count_le core pkSeed markerCost input
        ((graph, metadata + markerCost (.ambient phase label), phase), native)
        out hout .forger (by decide)
      have hm := nativeImpl_native_metadata core pkSeed markerCost input
        ((graph, metadata + markerCost (.ambient phase label), phase), native) out hout
      change out.2.2.2.1.cnt .signer ≤ native.2.1.cnt .signer +
        (if IsLabHmsg core input ∧ .signer = phaseClass phase then 1 else 0) at hc
      change out.2.2.2.1.cnt .forger ≤ native.2.1.cnt .forger +
        (if IsLabHmsg core input ∧ .forger = phaseClass phase then 1 else 0) at hn
      have hmn : out.2.1.2.1 = metadata + markerCost (.ambient phase label) :=
        congrArg Prod.fst hm
      have hs := hsecond phase input label hobs
      constructor
      · refine ⟨?_, hc, ?_, ?_⟩
        · simp only [Prod.snd_add, hs, Nat.add_zero]
        · by_cases hi : IsLabHmsg core input ∧ .forger = phaseClass phase
          · have hp := hpaid phase input label hobs hi.1 hi.2.symm
            rw [ite_eq_left hi] at hn
            simp only [Prod.fst_add]
            omega
          · rw [ite_eq_right hi] at hn
            simp only [Nat.add_zero] at hn
            simp only [Prod.fst_add]
            omega
        · intro hmeta
          by_cases hi : IsLabHmsg core input ∧ .forger = phaseClass phase
          · have hp := hmeta label rfl hi.1 hi.2.symm
            rw [ite_eq_left hi] at hn
            dsimp only
            omega
          · rw [ite_eq_right hi] at hn
            simp only [Nat.add_zero] at hn
            dsimp only
            omega
      · rintro ⟨hphase, hfree⟩
        change oldPhase = phase at hphase
        subst oldPhase
        simpa only [hfree label, Nat.add_zero] using hm
    · have heq : middle = (fallback (.inr (.ambient phase label)),
          (((graph, metadata, oldPhase), native), (paid, true))) := by
        simpa only [support_pure, Set.mem_singleton_iff] using hm
      subst middle
      have heq : result = (fallback (.inl input),
          (((graph, metadata, oldPhase), native), (paid, true))) := by
        simpa [guardedImpl, QueryImpl.guardQueryBudget] using hr
      subst result
      exact ⟨⟨rfl, Nat.le_add_right _ _, le_rfl, fun _ => le_rfl⟩, fun _ => rfl⟩

/-- Supported phase runs retain paid counts and conditional metadata offsets jointly. -/
theorem phase_offsets
    (observe : (labSpec core).Domain → Option markerSpec.Domain)
    (paidPolicy : SigningView.Event markerSpec Request → Nat × Nat)
    (markerCost : SigningView.Event markerSpec Request → Nat)
    (hselected : ∀ input, IsLabHmsg core input → ∃ label, observe input = some label)
    (hsecond : ∀ phase input label, observe input = some label →
      (paidPolicy (.ambient phase label)).2 = 0)
    (hpaid : ∀ phase input label, observe input = some label →
      IsLabHmsg core input → phaseClass phase = .forger →
      1 ≤ (paidPolicy (.ambient phase label)).1)
    (pkSeed : core.PkSeed) (caps : Nat × Nat)
    (fallback : (input : (labSpec core + ObsSpec
        (SigningView.Event markerSpec Request)).Domain) →
      (labSpec core + ObsSpec (SigningView.Event markerSpec Request)).Range input)
    {α : Type} (phase : SigningView.Phase)
    (admissible : (labSpec core).Domain → Prop)
    (program : OracleComp (labSpec core) α)
    (hprogram : AllQueriesSatisfy program admissible)
    (state : (CoverageDeferred.S core × Coverage.RoleState core) × ((Nat × Nat) × Bool))
    (result : α ×
      ((CoverageDeferred.S core × Coverage.RoleState core) × ((Nat × Nat) × Bool)))
    (hr : result ∈ support ((simulateQ
      (guardedImpl core pkSeed caps paidPolicy markerCost fallback)
      (simulateQ (phaseObservation core observe phase) program)).run state)) :
    (result.2.2.1.2 = state.2.1.2 ∧
    (phaseClass phase ≠ .signer →
      result.2.1.2.2.1.cnt .signer ≤ state.1.2.2.1.cnt .signer) ∧
    result.2.1.2.2.1.cnt .forger + state.2.1.1 ≤
      state.1.2.2.1.cnt .forger + result.2.2.1.1 ∧
    ((∀ input, admissible input → ∀ label, observe input = some label →
        IsLabHmsg core input → phaseClass phase = .forger →
        1 ≤ markerCost (.ambient phase label)) →
      result.2.1.2.2.1.cnt .forger + state.1.1.2.1 ≤
        state.1.2.2.1.cnt .forger + result.2.1.1.2.1)) ∧
    ((state.1.1.2.2 = phase ∧
      (∀ label, markerCost (.ambient phase label) = 0)) →
      result.2.1.1.2 = state.1.1.2) := by
  let P := fun s : (CoverageDeferred.S core × Coverage.RoleState core) × ((Nat × Nat) × Bool) =>
    (s.2.1.2 = state.2.1.2 ∧
    (phaseClass phase ≠ .signer → s.1.2.2.1.cnt .signer ≤ state.1.2.2.1.cnt .signer) ∧
    s.1.2.2.1.cnt .forger + state.2.1.1 ≤ state.1.2.2.1.cnt .forger + s.2.1.1 ∧
    ((∀ input, admissible input → ∀ label, observe input = some label →
        IsLabHmsg core input → phaseClass phase = .forger →
        1 ≤ markerCost (.ambient phase label)) →
      s.1.2.2.1.cnt .forger + state.1.1.2.1 ≤ state.1.2.2.1.cnt .forger + s.1.1.2.1)) ∧
    ((state.1.1.2.2 = phase ∧
      (∀ label, markerCost (.ambient phase label) = 0)) → s.1.1.2 = state.1.1.2)
  rw [← QueryImpl.simulateQ_compose] at hr
  refine hprogram.holds_of_mem_support_run_simulateQ P ?_
    ⟨⟨rfl, fun _ => le_rfl, le_rfl, fun _ => le_rfl⟩, fun _ => rfl⟩ hr
  intro input hi before hb out hout
  have hs := phase_step core observe paidPolicy markerCost hselected hsecond hpaid
    pkSeed caps fallback phase input before out hout
  dsimp only [P] at hb ⊢
  rcases hs with ⟨⟨hS, hN, hW, hM⟩, hPair⟩
  rcases hb with ⟨⟨hbS, hbN, hbW, hbM⟩, hbPair⟩
  refine ⟨⟨hS.trans hbS, ?_, by omega, ?_⟩, ?_⟩
  · intro hp
    have he : Coverage.TapeClass.signer ≠ phaseClass phase := Ne.symm hp
    simp only [he, and_false, ite_false, Nat.add_zero] at hN
    exact hN.trans (hbN hp)
  · intro hfund
    have hm := hM (fun label hobs hh hp => hfund input hi label hobs hh hp)
    have hbmeta := hbM hfund
    omega
  · intro hfree
    have beforePair := hbPair hfree
    have beforePhase := (congrArg Prod.snd beforePair).trans hfree.1
    exact (hPair ⟨beforePhase, hfree.2⟩).trans beforePair

/-- A bound on exact message-digest queries bounds the signer native count. -/
theorem phase_signer_count_le
    (observe : (labSpec core).Domain → Option markerSpec.Domain)
    (paidPolicy : SigningView.Event markerSpec Request → Nat × Nat)
    (markerCost : SigningView.Event markerSpec Request → Nat)
    (hselected : ∀ input, IsLabHmsg core input → ∃ label, observe input = some label)
    (hsecond : ∀ phase input label, observe input = some label →
      (paidPolicy (.ambient phase label)).2 = 0)
    (hpaid : ∀ phase input label, observe input = some label →
      IsLabHmsg core input → phaseClass phase = .forger →
      1 ≤ (paidPolicy (.ambient phase label)).1)
    (pkSeed : core.PkSeed) (caps : Nat × Nat)
    (fallback : (input : (labSpec core + ObsSpec
        (SigningView.Event markerSpec Request)).Domain) →
      (labSpec core + ObsSpec (SigningView.Event markerSpec Request)).Range input)
    {α : Type} (phase : SigningView.Phase)
    (program : OracleComp (labSpec core) α) {n : Nat}
    (hb : IsQueryBoundP program (IsLabHmsg core) n)
    (state : (CoverageDeferred.S core × Coverage.RoleState core) × ((Nat × Nat) × Bool))
    (result : α ×
      ((CoverageDeferred.S core × Coverage.RoleState core) × ((Nat × Nat) × Bool)))
    (hr : result ∈ support ((simulateQ
      (guardedImpl core pkSeed caps paidPolicy markerCost fallback)
      (simulateQ (phaseObservation core observe phase) program)).run state)) :
    result.2.1.2.2.1.cnt .signer ≤ state.1.2.2.1.cnt .signer + n := by
  rw [← QueryImpl.simulateQ_compose] at hr
  apply hb.cost_le_of_mem_support_run_simulateQ (fun s => s.1.2.2.1.cnt .signer) _ _
    state result hr
  · intro input _hi before out hout
    have hs := (phase_step core observe paidPolicy markerCost hselected hsecond hpaid
      pkSeed caps fallback phase input before out hout).1.2.1
    split_ifs at hs <;> omega
  · intro input hi before out hout
    simpa only [hi, false_and, ite_false, Nat.add_zero] using
      (phase_step core observe paidPolicy markerCost hselected hsecond hpaid
        pkSeed caps fallback phase input before out hout).1.2.1


/-- Signer calls are funded by attempts, and attempts plus forger calls by paid work. -/
@[expose]
def CountInvariant
    (state : (CoverageDeferred.S core × Coverage.RoleState core) × ((Nat × Nat) × Bool)) : Prop :=
  state.1.2.2.1.cnt .signer ≤ state.2.1.2 ∧
    state.2.1.2 + state.1.2.2.1.cnt .forger ≤ state.2.1.1

/-- An attempt marker is absorbed, admitted and charged, or rejected without native work. -/
theorem signing_entry
    (policy : SigningView.Event markerSpec Request → Nat × Nat)
    (markerCost : SigningView.Event markerSpec Request → Nat)
    (pkSeed : core.PkSeed) (caps : Nat × Nat)
    (fallback : (input : (labSpec core + ObsSpec
      (SigningView.Event markerSpec Request)).Domain) →
      (labSpec core + ObsSpec (SigningView.Event markerSpec Request)).Range input)
    (request : Request)
    (hattempt : 1 ≤ (policy (.signingAttempt request)).1 ∧
      (policy (.signingAttempt request)).2 = 1)
    (state : (CoverageDeferred.S core × Coverage.RoleState core) × ((Nat × Nat) × Bool))
    (hI : CountInvariant core state)
    (result : PUnit ×
      ((CoverageDeferred.S core × Coverage.RoleState core) × ((Nat × Nat) × Bool)))
    (hr : result ∈ support ((guardedImpl core pkSeed caps policy markerCost fallback
      (.inr (.signingAttempt request))).run state)) :
    CountInvariant core result.2 ∧
    (state.2.2 = true →
      result = (fallback (.inr (.signingAttempt request)), state)) ∧
    (state.2.2 = false ∧ state.2.1 + policy (.signingAttempt request) ≤ caps →
      result = (PUnit.unit,
        (((state.1.1.1,
          (state.1.1.2.1 + markerCost (.signingAttempt request), .signer)), state.1.2),
          (state.2.1 + policy (.signingAttempt request), false)))) ∧
    (state.2.2 = false ∧ ¬(state.2.1 + policy (.signingAttempt request) ≤ caps) →
      result = (fallback (.inr (.signingAttempt request)),
        (state.1, (state.2.1, true)))) := by
  simp only [guardedImpl, QueryImpl.guardQueryBudget, StateT.run_mk] at hr
  split_ifs at hr with hflag hcap
  · have heq : result = (fallback (.inr (.signingAttempt request)), state) := by
      simpa only [support_pure, Set.mem_singleton_iff] using hr
    subst result
    refine ⟨hI, fun _ => rfl, ?_, ?_⟩
    · rintro ⟨hf, _⟩
      simp_all
    · rintro ⟨hf, _⟩
      simp_all
  · rw [nativeImpl_marker] at hr
    simp only [map_pure, support_pure, Set.mem_singleton_iff] at hr
    subst result
    refine ⟨?_, ?_, fun _ => rfl, ?_⟩
    · dsimp only [CountInvariant] at hI ⊢
      simp only [Sum.elim_inr, Prod.fst_add, Prod.snd_add]
      rcases hattempt with ⟨hw, hs⟩
      constructor <;> omega
    · intro hf
      exact (hflag hf).elim
    · rintro ⟨_, hc⟩
      exact (hc hcap).elim
  · have heq : result = (fallback (.inr (.signingAttempt request)),
        (state.1, (state.2.1, true))) := by
      simpa only [support_pure, Set.mem_singleton_iff] using hr
    subst result
    refine ⟨hI, ?_, ?_, fun _ => rfl⟩
    · intro hf
      exact (hflag hf).elim
    · rintro ⟨_, hc⟩
      exact (hcap hc).elim


/-- Signing retains the invariant and metadata with one charge per admitted attempt. -/
theorem signing_callback {Reply : Type}
    (observe : (labSpec core).Domain → Option markerSpec.Domain)
    (policy : SigningView.Event markerSpec Request → Nat × Nat)
    (markerCost : SigningView.Event markerSpec Request → Nat)
    (hselected : ∀ input, IsLabHmsg core input → ∃ label, observe input = some label)
    (hsecond : ∀ phase input label, observe input = some label →
      (policy (.ambient phase label)).2 = 0)
    (hpaid : ∀ phase input label, observe input = some label →
      IsLabHmsg core input → phaseClass phase = .forger →
      1 ≤ (policy (.ambient phase label)).1)
    (pkSeed : core.PkSeed) (caps : Nat × Nat)
    (fallback : (input : (labSpec core + ObsSpec
      (SigningView.Event markerSpec Request)).Domain) →
      (labSpec core + ObsSpec (SigningView.Event markerSpec Request)).Range input)
    (request : Request)
    (hattempt : 1 ≤ (policy (.signingAttempt request)).1 ∧
      (policy (.signingAttempt request)).2 = 1)
    (hattemptM : markerCost (.signingAttempt request) = 0)
    (hsignerM : ∀ label, markerCost (.ambient .signer label) = 0)
    (body : OracleComp (labSpec core) Reply)
    (hbody : IsQueryBoundP body (IsLabHmsg core) 1)
    (state : (CoverageDeferred.S core × Coverage.RoleState core) × ((Nat × Nat) × Bool))
    (hI : CountInvariant core state)
    (result : Reply ×
      ((CoverageDeferred.S core × Coverage.RoleState core) × ((Nat × Nat) × Bool)))
    (hr : result ∈ support ((simulateQ
      (guardedImpl core pkSeed caps policy markerCost fallback) (do
        let _ ← liftM ((labSpec core + ObsSpec (SigningView.Event markerSpec Request)).query
          (.inr (.signingAttempt request)))
        simulateQ (phaseObservation core observe .signer) body)).run state)) :
    let admitted := state.2.2 = false ∧ state.2.1 + policy (.signingAttempt request) ≤ caps
    CountInvariant core result.2 ∧
    result.2.1.1.2.1 = state.1.1.2.1 ∧
    result.2.2.1.2 = state.2.1.2 + (if admitted then 1 else 0) ∧
    (admitted → result.2.1.1.2.2 = .signer) ∧
    (¬admitted → result.2 = (state.1, (state.2.1, true))) := by
  dsimp only
  rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hr
  obtain ⟨entry, he, hr⟩ := hr
  have hs := signing_entry core policy markerCost pkSeed caps fallback request hattempt
    state hI entry he
  by_cases hadmit : state.2.2 = false ∧ state.2.1 + policy (.signingAttempt request) ≤ caps
  · have entryEq := hs.2.2.1 hadmit
    have entryInv := hs.1
    have entryMeta : entry.2.1.1.2 = (state.1.1.2.1, .signer) := by
      rw [entryEq]
      simp only [hattemptM, Nat.add_zero]
    have entrySigner : entry.2.1.2.2.1.cnt .signer = state.1.2.2.1.cnt .signer := by
      rw [entryEq]
    have entrySecond : entry.2.2.1.2 = state.2.1.2 + 1 := by
      rw [entryEq]
      change state.2.1.2 + (policy (.signingAttempt request)).2 = state.2.1.2 + 1
      rw [hattempt.2]
    have hw := phase_offsets core observe policy markerCost hselected hsecond hpaid
      pkSeed caps fallback .signer (fun _ => True) body
      (allQueriesSatisfy_of_forall (fun _ => True.intro) body) entry.2 result hr
    have hc := phase_signer_count_le core observe policy markerCost hselected hsecond hpaid
      pkSeed caps fallback .signer body hbody entry.2 result hr
    have pair := (hw.2 ⟨congrArg Prod.snd entryMeta, hsignerM⟩).trans entryMeta
    have sameSecond := hw.1.1
    have work := hw.1.2.2.1
    have resultInv : CountInvariant core result.2 := by
      dsimp only [CountInvariant] at hI entryInv ⊢
      constructor <;> omega
    have sameM := congrArg Prod.fst pair
    have samePhase := congrArg Prod.snd pair
    refine ⟨resultInv, sameM, ?_, fun _ => samePhase, fun h => (h hadmit).elim⟩
    simp only [hadmit]
    exact sameSecond.trans entrySecond
  · have entryState : entry.2 = (state.1, (state.2.1, true)) := by
      cases hf : state.2.2 with
      | false =>
          have hc : ¬(state.2.1 + policy (.signingAttempt request) ≤ caps) :=
            fun h => hadmit ⟨hf, h⟩
          exact congrArg Prod.snd (hs.2.2.2 ⟨hf, hc⟩)
      | true =>
          rw [hs.2.1 hf]
          exact Prod.ext rfl (Prod.ext rfl hf)
    have frozen := guardedImpl_aborted core pkSeed caps policy markerCost fallback
      (simulateQ (phaseObservation core observe .signer) body) entry.2
      (by rw [entryState]) result hr
    have resultState := frozen.trans entryState
    refine ⟨?_, ?_, ?_, fun h => (hadmit h).elim, fun _ => resultState⟩
    · rw [resultState]
      exact hI
    · rw [resultState]
    · simp only [resultState, hadmit, ite_false, Nat.add_zero]


/-- Logged signing retains the actual reply and all admitted-attempt accounting facts. -/
theorem logged_signing_callback :
  ∀ {vp : ValidatedParams} (core : CorePrimitives vp.params)
    [SampleableType core.Y] [SampleableType (Bytes vp.params.m)]
    [DecidableEq core.Y] [DecidableEq core.PkSeed] [DecidableEq core.AdrsKey]
    [DecidableEq core.SkPrf] {ιm Request : Type}
    {markerSpec : OracleSpec.{0, 0} ιm}
    {Reply : Type}
    (observe : (labSpec core).Domain → Option markerSpec.Domain)
    (paidPolicy : SigningView.Event markerSpec Request → Nat × Nat)
    (markerCost : SigningView.Event markerSpec Request → Nat)
    (_hselected : ∀ input, IsLabHmsg core input →
      ∃ label, observe input = some label)
    (_hsecond : ∀ phase input label, observe input = some label →
      (paidPolicy (.ambient phase label)).2 = 0)
    (_hpaid : ∀ phase input label, observe input = some label →
      IsLabHmsg core input → phaseClass phase = .forger →
      1 ≤ (paidPolicy (.ambient phase label)).1)
    (_hattempt : ∀ request, 1 ≤ (paidPolicy (.signingAttempt request)).1 ∧
      (paidPolicy (.signingAttempt request)).2 = 1)
    (_hattemptM : ∀ request, markerCost (.signingAttempt request) = 0)
    (_hsignerM : ∀ label, markerCost (.ambient .signer label) = 0)
    (body : Request → OracleComp (labSpec core) Reply)
    (_hbody : ∀ request, IsQueryBoundP (body request) (IsLabHmsg core) 1)
    (pkSeed : core.PkSeed) (caps : Nat × Nat)
    (fallback : (input : (labSpec core + ObsSpec
      (SigningView.Event markerSpec Request)).Domain) →
      (labSpec core + ObsSpec (SigningView.Event markerSpec Request)).Range input),
    let sign : Request → OracleComp
        (labSpec core + ObsSpec (SigningView.Event markerSpec Request)) Reply :=
      fun request => do
        let _ ← liftM ((labSpec core + ObsSpec (SigningView.Event markerSpec Request)).query
          (.inr (.signingAttempt request)))
        simulateQ (phaseObservation core observe .signer) (body request)
    ∀ (request : Request)
      (state : (CoverageDeferred.S core × Coverage.RoleState core) × ((Nat × Nat) × Bool))
      (_hI : CountInvariant core state)
      (result : (Reply × QueryLog (Request →ₒ Reply)) ×
        ((CoverageDeferred.S core × Coverage.RoleState core) × ((Nat × Nat) × Bool)))
      (_hr : result ∈ support ((simulateQ
        (guardedImpl core pkSeed caps paidPolicy markerCost fallback)
        ((QueryImpl.withLogging sign request).run)).run state)),
      let admitted := state.2.2 = false ∧
        state.2.1 + paidPolicy (.signingAttempt request) ≤ caps
      CountInvariant core result.2 ∧
      result.1.2 = [⟨request, result.1.1⟩] ∧
      result.2.1.1.2.1 = state.1.1.2.1 ∧
      result.2.2.1.2 = state.2.1.2 + (if admitted then 1 else 0) ∧
      (admitted → result.2.1.1.2.2 = .signer) ∧
      (¬admitted → result.2 = (state.1, (state.2.1, true))) := by
  intro vp core _ _ _ _ _ _ ιm Request markerSpec Reply observe policy markerCost
    hselected hsecond hpaid hattempt hattemptM hsignerM body hbody pkSeed caps fallback
  dsimp only
  intro request state hI result hr
  rw [QueryImpl.run_withLogging_apply, simulateQ_bind] at hr
  simp only [simulateQ_pure] at hr
  rw [StateT.run_bind] at hr
  simp only [StateT.run_pure] at hr
  rw [mem_support_bind_iff] at hr
  obtain ⟨out, hout, hlast⟩ := hr
  simp only [support_pure, Set.mem_singleton_iff] at hlast
  subst result
  have hs := signing_callback core observe policy markerCost hselected hsecond hpaid
    pkSeed caps fallback request (hattempt request) (hattemptM request) hsignerM
    (body request) (hbody request) state hI out hout
  exact ⟨hs.1, rfl, hs.2.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2⟩

end SLHDSA.Security.NativeCounts
