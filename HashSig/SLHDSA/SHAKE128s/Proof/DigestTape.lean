/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.GrowthCharge
public import HashSig.SLHDSA.SHAKE128s.Proof.ForsAdaptiveTargets
public import HashSig.SLHDSA.SHAKE128s.Proof.ForsDisclosureTape
public import VCVio.OracleComp.QueryTracking.RandomOracle.DeferredSampling
public import HashSig.SLHDSA.SHAKE128s.Proof.KeygenUniform
public import HashSig.SLHDSA.SHAKE128s.Proof.MessageDigest

/-!
# The adaptively recorded digest tape

The signing oracle's `H_msg` inputs depend on the messages the adversary chooses and on the
randomizers it never sees, so the coordinates of a digest tape are selected adaptively during a
run. This file supplies the instrumented random oracle for that.

`recorder keep` is the shared random oracle that records, in query order, the input and answer
of every query that both misses the cache and whose input passes a test `keep` (in the
experiment, "the input is in `H_msg` format"). The recording is a write-only component of the
state: it never influences an answer, so `mem_support_rom` carries every recorded run to a run
of the plain oracle `KeygenUniform.rom`, and an installed answer persists verbatim along a
recorded run (`recorder_cache_value_persists`). The inputs are recorded alongside the answers
because the coverage charge needs two tape coordinates to be *distinct*.

`padding` draws independent uniform values to pad a short recording out to a full tape, and
`viewTape_uniform` says a uniform word of answers has a uniform tape of parsed views.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace SlhDsaSecurity.DigestTape

/-! ## The recording oracle -/

/-- A recording: the inputs queried and the answers they drew, in query order. The input is
carried because the leave-one-out charge needs two coordinates of the tape to be *distinct*,
and distinct inputs are what the game supplies. -/
abbrev Record := List (Bytes × HashOutput)

/-- The cache together with the recording so far. -/
abbrev RecordState := QueryCache HashSpec × Record

open scoped Classical in
/-- The shared random oracle, recording the answer of every *fresh* query whose input passes
`keep`. A cache hit records nothing: it draws no randomness, so it contributes no tape
coordinate. -/
noncomputable def recorder (keep : Bytes → Prop) :
    QueryImpl OracleWorld (StateT RecordState ProbComp) :=
  fun queried state =>
    match queried with
    | Sum.inl coin => do
        let value ← ($ᵗ (OracleWorld.Range (Sum.inl coin)) : ProbComp _)
        pure (value, state)
    | Sum.inr input => do
        let step ← (randomOracle input).run state.1
        pure (step.1, (step.2,
          if keep input ∧ state.1 input = none then state.2 ++ [(input, step.1)]
          else state.2))

open scoped Classical in
/-- On a private uniform sample the recording oracle draws and leaves the state alone. -/
theorem recorder_run_inl (keep : Bytes → Prop) (coin : unifSpec.Domain) (state : RecordState) :
    ((recorder keep) (Sum.inl coin)).run state =
      ($ᵗ (OracleWorld.Range (Sum.inl coin)) : ProbComp _) >>= fun value =>
        (pure (value, state) : ProbComp _) := rfl

open scoped Classical in
/-- On a hash query the recording oracle is the shared oracle followed by the append. -/
theorem recorder_run_inr (keep : Bytes → Prop) (input : Bytes) (state : RecordState) :
    ((recorder keep) (Sum.inr input)).run state =
      (randomOracle input).run state.1 >>= fun step =>
        (pure (step.1, (step.2,
          if keep input ∧ state.1 input = none then state.2 ++ [(input, step.1)]
          else state.2)) :
          ProbComp _) := rfl

/-- The shared oracle on a private uniform sample. -/
theorem rom_run_inl (coin : unifSpec.Domain) (cache : QueryCache HashSpec) :
    (KeygenUniform.rom (Sum.inl coin)).run cache =
      ($ᵗ (OracleWorld.Range (Sum.inl coin)) : ProbComp _) >>= fun value =>
        (pure (value, cache) : ProbComp _) := rfl

/-- The shared oracle on a hash query is the lazily sampled cache. -/
theorem rom_run_inr (input : Bytes) (cache : QueryCache HashSpec) :
    (KeygenUniform.rom (Sum.inr input)).run cache = (randomOracle input).run cache := rfl

/-- A block of `trials` independent uniform answers, used to pad a short recording out to a
full tape. -/
noncomputable def padding : Nat → ProbComp (List HashOutput)
  | 0 => pure []
  | n + 1 => do
      let value ← ($ᵗ HashOutput : ProbComp HashOutput)
      let rest ← padding n
      pure (value :: rest)

/-- Every recorded run is a run: dropping the recording lands in the support of the plain run
of the shared oracle. This lets a fact proved about the game, such as a budget or a cache
shape, be used under the instrumentation. -/
theorem mem_support_rom {α : Type} (keep : Bytes → Prop)
    (computation : OracleComp OracleWorld α) (state : RecordState) (result : α × RecordState)
    (hmem : result ∈ support ((simulateQ (recorder keep) computation).run state)) :
    (result.1, result.2.1) ∈ support ((simulateQ KeygenUniform.rom computation).run state.1) := by
  classical
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, hmem]
  | query_bind queried next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨step, hstep, hrest⟩ := hmem
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff]
    refine ⟨(step.1, step.2.1), ?_, ih step.1 step.2 result hrest⟩
    rcases queried with coin | input
    · rw [recorder_run_inl, mem_support_bind_iff] at hstep
      obtain ⟨value, hvalue, hpure⟩ := hstep
      rw [support_pure, Set.mem_singleton_iff] at hpure
      rw [rom_run_inl, mem_support_bind_iff]
      refine ⟨value, hvalue, ?_⟩
      rw [support_pure, Set.mem_singleton_iff, hpure]
    · rw [recorder_run_inr, mem_support_bind_iff] at hstep
      obtain ⟨inner, hinner, hpure⟩ := hstep
      rw [support_pure, Set.mem_singleton_iff] at hpure
      rw [rom_run_inr]
      have hshape : (step.1, step.2.1) = inner := by
        rw [hpure]
        rfl
      rw [hshape]
      exact hinner

/-! ## Persistence of installed answers -/

/-- An installed answer persists verbatim along a recorded run. -/
theorem recorder_cache_value_persists {α : Type} (keep : Bytes → Prop)
    (computation : OracleComp OracleWorld α) (state : RecordState) (result : α × RecordState)
    (hmem : result ∈ support ((simulateQ (recorder keep) computation).run state))
    (input : Bytes) (answer : HashOutput) (hentry : state.1 input = some answer) :
    result.2.1 input = some answer := by
  classical
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    rw [hmem]
    exact hentry
  | query_bind queried next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨step, hstep, hrest⟩ := hmem
    refine ih step.1 step.2 result hrest ?_
    rcases queried with coin | queried
    · rw [recorder_run_inl, mem_support_bind_iff] at hstep
      obtain ⟨value, -, hpure⟩ := hstep
      rw [support_pure, Set.mem_singleton_iff] at hpure
      rw [hpure]
      exact hentry
    · rw [recorder_run_inr, mem_support_bind_iff] at hstep
      obtain ⟨inner, hinner, hpure⟩ := hstep
      rw [support_pure, Set.mem_singleton_iff] at hpure
      rw [hpure]
      cases hqueried : state.1 queried with
      | none =>
        rw [QueryImpl.withCaching_run_none _ hqueried, support_map] at hinner
        obtain ⟨sampled, -, hpair⟩ := hinner
        have hmid : inner.2 = state.1.cacheQuery queried sampled :=
          (Prod.ext_iff.mp hpair).2.symm
        show inner.2 input = some answer
        rw [hmid]
        have hne : input ≠ queried := by
          intro hsame
          rw [hsame, hqueried] at hentry
          simp at hentry
        rw [QueryCache.cacheQuery_of_ne state.1 sampled hne]
        exact hentry
      | some cached =>
        rw [QueryImpl.withCaching_run_some _ hqueried, support_pure,
          Set.mem_singleton_iff] at hinner
        show inner.2 input = some answer
        rw [hinner]
        exact hentry

/-! ## The padding and the view tape -/

/-- The padding block has exactly the length it was asked for. -/
theorem padding_length (trials : Nat) (pad : List HashOutput)
    (hmem : pad ∈ support (padding trials)) : pad.length = trials := by
  induction trials generalizing pad with
  | zero =>
    rw [padding, support_pure, Set.mem_singleton_iff] at hmem
    rw [hmem]
    rfl
  | succ remaining ih =>
    rw [show padding (remaining + 1) =
      ($ᵗ HashOutput : ProbComp HashOutput) >>= fun value =>
        padding remaining >>= fun rest => (pure (value :: rest) : ProbComp _) from rfl,
      mem_support_bind_iff] at hmem
    obtain ⟨value, -, hrest⟩ := hmem
    rw [mem_support_bind_iff] at hrest
    obtain ⟨rest, hrestMem, hpure⟩ := hrest
    rw [support_pure, Set.mem_singleton_iff] at hpure
    rw [hpure, List.length_cons, ih rest hrestMem]

/-- Padding never fails. -/
theorem padding_neverFails (trials : Nat) : prFail (padding trials) = 0 := by
  induction trials with
  | zero => rw [padding]; simp
  | succ remaining ih =>
    rw [show padding (remaining + 1) =
      ($ᵗ HashOutput : ProbComp HashOutput) >>= fun value =>
        padding remaining >>= fun rest => (pure (value :: rest) : ProbComp _) from rfl]
    simp

/-- Coordinatewise, a uniform word of answers has a uniform tape of parsed views. -/
theorem viewTape_uniform (trials : Nat) :
    ((fun word index => MessageDigest.parse (word index)) <$>
        ($ᵗ (Fin trials → HashOutput) : ProbComp (Fin trials → HashOutput))) =ᵈ
      ($ᵗ (ForsDisclosureTape.Tape trials) :
        ProbComp (ForsDisclosureTape.Tape trials)) := by
  classical
  let coordinate : HashOutput ≃ MessageDigest.View × (BitVec 2 × BitVec 7) :=
    Equiv.ofBijective MessageDigest.split MessageDigest.split_bijective
  let regroup : (Fin trials → HashOutput) ≃
      ForsDisclosureTape.Tape trials × (Fin trials → BitVec 2 × BitVec 7) :=
    (Equiv.piCongrRight (fun _ => coordinate)).trans
      (Equiv.arrowProdEquivProdArrow (Fin trials) (fun _ => MessageDigest.View)
        (fun _ => BitVec 2 × BitVec 7))
  have hmap : (fun word : Fin trials → HashOutput =>
        fun index => MessageDigest.parse (word index)) <$>
        ($ᵗ (Fin trials → HashOutput) : ProbComp (Fin trials → HashOutput)) =
      Prod.fst <$> (regroup <$> ($ᵗ (Fin trials → HashOutput) :
        ProbComp (Fin trials → HashOutput))) := by
    rw [Functor.map_map]
    rfl
  have hinner : regroup <$> ($ᵗ (Fin trials → HashOutput) :
        ProbComp (Fin trials → HashOutput)) =ᵈ
      ($ᵗ (ForsDisclosureTape.Tape trials × (Fin trials → BitVec 2 × BitVec 7)) :
        ProbComp (ForsDisclosureTape.Tape trials × (Fin trials → BitVec 2 × BitVec 7))) :=
    SampleableType.map_uniformSample_evalDistEq_of_bijective regroup.bijective
  rw [hmap]
  refine (hinner.map Prod.fst).trans (EvalDistEq.of_forall_prEvent_eq fun p => ?_)
  rw [prEvent_map]
  exact SampleableType.prEvent_uniformSample_fst p

end SlhDsaSecurity.DigestTape
