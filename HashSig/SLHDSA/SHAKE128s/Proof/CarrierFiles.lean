/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.ServedAgreement
public import HashSig.SLHDSA.SHAKE128s.Proof.CarriedWitness
public import HashSig.SLHDSA.SHAKE128s.Proof.ServingForget
public import HashSig.SLHDSA.SHAKE128s.Proof.CountedHandler

/-!
# The recorder that notices, as a handler the agreement can read

`ServedAgreement.Files` is what the carrier/log agreement asks of a handler. This file shows
that the tail's recorder — the recorder that notices, at the carrier's own view, so that the run
keeps two recordings *and* files on the framing — provides it (`files_carrierRecorder`), and that
it forgets to the shared oracle (`forgetsAlong_carrierRecorder`), the law a bracketed phase reads
its handler through. `countedCarrierRecorder` is the same handler with a counter beside the
carrier, and both laws survive the wrapping.

**The notice is what makes the `Files.queryStep` conjunct true.** A recorder that installed an
answer only on a miss could not file a served request whose digest input was already cached, and
that conjunct — the framing admitted it, so it is served — would be false exactly at the case the
served notion exists for. `RecorderView.noticingRecorderOf` runs `CacheView.onQuery` on both
branches, and at the carrier that is `CarriedWitness.servingNotice`, which files when the flag is
up. So the conjunct holds on a hit for the same reason as on a miss.

Every step fact is one of `CarriedWitness`'s notice lemmas or `HandlerCarrier`'s growth lemmas,
and the run facts are the inductions that carry them.
-/

@[expose] public section

open OracleComp OracleSpec

namespace SlhDsaSecurity.CarrierFiles

open Security RecorderView HandlerCarrier CarriedWitness ServedAgreement

variable (pk : PublicKey)

/-! ## One step -/

open scoped Classical in
/-- **Noticing grows the carrier**: it either files one input or does nothing. -/
theorem grows_servingNotice (state : State) (input : Bytes) :
    Grows state (servingNotice pk state input) := by
  classical
  rw [servingNotice]
  split
  · exact grows_file state input
  · exact Grows.refl state

open scoped Classical in
/-- **A coin step changes nothing.** -/
theorem step_inl (rightKeep : Bytes → State → Prop) (coin : unifSpec.Domain)
    (state : StateOf State) (step : OracleWorld.Range (Sum.inl coin) × StateOf State)
    (hstep : step ∈ support (((@noticingRecorderOf State (servingView pk) (disclosingKeep pk) rightKeep) (Sum.inl coin)).run state)) :
    step.2 = state := by
  classical
  rw [@noticingRecorderOf_run_inl State (servingView pk) (disclosingKeep pk) rightKeep coin state,
    @recorderOf_run_inl State (servingView pk) (disclosingKeep pk) rightKeep coin state,
    mem_support_bind_iff] at hstep
  obtain ⟨value, -, hpure⟩ := hstep
  rw [support_pure, Set.mem_singleton_iff] at hpure
  rw [hpure]

open scoped Classical in
/-- **A hash step, in the two shapes it can have.** -/
theorem step_inr_cases (rightKeep : Bytes → State → Prop) (input : Bytes)
    (state : StateOf State) (step : OracleWorld.Range (Sum.inr input) × StateOf State)
    (hstep : step ∈ support (((@noticingRecorderOf State (servingView pk) (disclosingKeep pk) rightKeep) (Sum.inr input)).run state)) :
    (cacheOf state.1 input = some step.1 ∧ step.2.1 = servingNotice pk state.1 input) ∨
      (cacheOf state.1 input = none ∧
        step.2.1 = cacheAnswer (servingNotice pk state.1 input) input step.1) := by
  classical
  by_cases hsome : ∃ cached : HashOutput, cacheOf state.1 input = some cached
  · obtain ⟨cached, hcached⟩ := hsome
    rw [@noticingRecorderOf_run_inr_some State (servingView pk) (disclosingKeep pk) rightKeep
      input state cached hcached, support_pure, Set.mem_singleton_iff] at hstep
    exact Or.inl ⟨by rw [hstep]; exact hcached, by rw [hstep]; rfl⟩
  · have hfresh : cacheOf state.1 input = none := by
      cases hvalue : cacheOf state.1 input with
      | none => rfl
      | some cached => exact absurd ⟨cached, hvalue⟩ hsome
    rw [@noticingRecorderOf_run_inr_none State (servingView pk) (disclosingKeep pk) rightKeep
      input state hfresh, support_map] at hstep
    obtain ⟨answer, -, hvalue⟩ := hstep
    exact Or.inr ⟨hfresh, by rw [← hvalue]; rfl⟩

open scoped Classical in
/-- **A hash step leaves its own input cached.** -/
theorem step_cached (rightKeep : Bytes → State → Prop) (input : Bytes)
    (state : StateOf State) (step : OracleWorld.Range (Sum.inr input) × StateOf State)
    (hstep : step ∈ support (((@noticingRecorderOf State (servingView pk) (disclosingKeep pk) rightKeep) (Sum.inr input)).run state)) :
    step.2.1.cache input = some step.1 := by
  classical
  rcases step_inr_cases pk rightKeep input state step hstep with ⟨hcached, hstate⟩ | ⟨-, hstate⟩
  · rw [hstate]
    show cacheOf (servingNotice pk state.1 input) input = some step.1
    rw [cacheOf_servingNotice]
    exact hcached
  · rw [hstate]
    exact QueryCache.cacheQuery_self _ _ _

open scoped Classical in
/-- **A hash step leaves the framing alone.** -/
theorem step_framing (rightKeep : Bytes → State → Prop) (input : Bytes)
    (state : StateOf State) (step : OracleWorld.Range (Sum.inr input) × StateOf State)
    (hstep : step ∈ support (((@noticingRecorderOf State (servingView pk) (disclosingKeep pk) rightKeep) (Sum.inr input)).run state)) :
    step.2.1.framing = state.1.framing := by
  classical
  rcases step_inr_cases pk rightKeep input state step hstep with ⟨-, hstate⟩ | ⟨-, hstate⟩
  · rw [hstate]; exact framing_servingNotice pk state.1 input
  · rw [hstate, framing_cacheAnswer]; exact framing_servingNotice pk state.1 input

open scoped Classical in
/-- **A hash step grows the carrier.** -/
theorem step_grows (rightKeep : Bytes → State → Prop) (input : Bytes)
    (state : StateOf State) (step : OracleWorld.Range (Sum.inr input) × StateOf State)
    (hstep : step ∈ support (((@noticingRecorderOf State (servingView pk) (disclosingKeep pk) rightKeep) (Sum.inr input)).run state)) :
    Grows state.1 step.2.1 := by
  classical
  rcases step_inr_cases pk rightKeep input state step hstep with ⟨-, hstate⟩ | ⟨hfresh, hstate⟩
  · rw [hstate]; exact grows_servingNotice pk state.1 input
  · rw [hstate]
    exact Grows.trans (grows_servingNotice pk state.1 input)
      (grows_cacheAnswer _ input step.1
        (by show cacheOf (servingNotice pk state.1 input) input = none
            rw [cacheOf_servingNotice]; exact hfresh))

open scoped Classical in
/-- **A hash step serves its own input when the framing admits it.** The conjunct the notice
exists for, and it holds on a cache hit exactly as on a miss. -/
theorem step_served_self (rightKeep : Bytes → State → Prop) (input : Bytes)
    (state : StateOf State) (step : OracleWorld.Range (Sum.inr input) × StateOf State)
    (hstep : step ∈ support (((@noticingRecorderOf State (servingView pk) (disclosingKeep pk) rightKeep) (Sum.inr input)).run state))
    (hfiles : FilesLeft pk state.1 input) : Served step.2.1 input := by
  classical
  have hnotice : Served (servingNotice pk state.1 input) input :=
    served_servingNotice_self pk state.1 input hfiles
  rcases step_inr_cases pk rightKeep input state step hstep with ⟨-, hstate⟩ | ⟨-, hstate⟩
  · rw [hstate]; exact hnotice
  · rw [hstate]; exact served_cacheAnswer_iff _ input input step.1 hnotice

open scoped Classical in
/-- **A hash step serves nothing but its own input.** -/
theorem step_served (rightKeep : Bytes → State → Prop) (input : Bytes)
    (state : StateOf State) (step : OracleWorld.Range (Sum.inr input) × StateOf State)
    (hstep : step ∈ support (((@noticingRecorderOf State (servingView pk) (disclosingKeep pk) rightKeep) (Sum.inr input)).run state))
    (probe : Bytes) (hserved : Served step.2.1 probe) :
    Served state.1 probe ∨ probe = input := by
  classical
  have hnotice : Served (servingNotice pk state.1 input) probe → Served state.1 probe ∨
      probe = input := by
    rw [servingNotice]
    split
    · intro hmem
      rcases Multiset.mem_cons.mp hmem with rfl | hrest
      · exact Or.inr rfl
      · exact Or.inl hrest
    · exact fun hmem => Or.inl hmem
  rcases step_inr_cases pk rightKeep input state step hstep with ⟨-, hstate⟩ | ⟨-, hstate⟩
  · rw [hstate] at hserved; exact hnotice hserved
  · rw [hstate] at hserved; exact hnotice hserved

/-! ## Whole runs -/

open scoped Classical in
/-- **A step grows the carrier**, at either kind of query. -/
theorem stepGrows (rightKeep : Bytes → State → Prop) (queried : OracleWorld.Domain)
    (state : StateOf State) (step : OracleWorld.Range queried × StateOf State)
    (hstep : step ∈ support (((@noticingRecorderOf State (servingView pk) (disclosingKeep pk) rightKeep) queried).run state)) :
    Grows state.1 step.2.1 := by
  rcases queried with coin | input
  · rw [step_inl pk rightKeep coin state step hstep]
    exact Grows.refl _
  · exact step_grows pk rightKeep input state step hstep

open scoped Classical in
/-- **And therefore a run.** -/
theorem runGrows (rightKeep : Bytes → State → Prop) {α : Type}
    (computation : OracleComp OracleWorld α) :
    ∀ (state : StateOf State) (z : α × StateOf State),
      z ∈ support ((simulateQ (@noticingRecorderOf State (servingView pk) (disclosingKeep pk) rightKeep) computation).run state) →
        Grows state.1 z.2.1 := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro state z hz
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    rw [show z.2 = state from by rw [hz]]
    exact Grows.refl _
  | query_bind queried next ih =>
    intro state z hz
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨step, hstep, hrest⟩ := hz
    exact Grows.trans (stepGrows pk rightKeep queried state step hstep) (ih step.1 step.2 z hrest)

open scoped Classical in
/-- **A step leaves the framing alone.** -/
theorem stepFraming (rightKeep : Bytes → State → Prop) (queried : OracleWorld.Domain)
    (state : StateOf State) (step : OracleWorld.Range queried × StateOf State)
    (hstep : step ∈ support (((@noticingRecorderOf State (servingView pk) (disclosingKeep pk) rightKeep) queried).run state)) :
    step.2.1.framing = state.1.framing := by
  rcases queried with coin | input
  · rw [step_inl pk rightKeep coin state step hstep]
  · exact step_framing pk rightKeep input state step hstep

open scoped Classical in
/-- **And therefore a run.** -/
theorem runFraming (rightKeep : Bytes → State → Prop) {α : Type}
    (computation : OracleComp OracleWorld α) :
    ∀ (state : StateOf State) (z : α × StateOf State),
      z ∈ support ((simulateQ (@noticingRecorderOf State (servingView pk) (disclosingKeep pk) rightKeep) computation).run state) →
        z.2.1.framing = state.1.framing := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro state z hz
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    rw [show z.2 = state from by rw [hz]]
  | query_bind queried next ih =>
    intro state z hz
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨step, hstep, hrest⟩ := hz
    rw [ih step.1 step.2 z hrest, stepFraming pk rightKeep queried state step hstep]

open scoped Classical in
/-- **A property closed under caching and under filing survives a step.** -/
theorem stepInvariant (rightKeep : Bytes → State → Prop) (Inv : State → Prop)
    (hcache : ∀ (carrier : State) (input : Bytes) (answer : HashOutput),
      Inv carrier → Inv (cacheAnswer carrier input answer))
    (hfile : ∀ (carrier : State) (input : Bytes),
      Inv carrier → FilesLeft pk carrier input → Inv (file carrier input))
    (queried : OracleWorld.Domain) (state : StateOf State)
    (step : OracleWorld.Range queried × StateOf State)
    (hstep : step ∈ support (((@noticingRecorderOf State (servingView pk) (disclosingKeep pk) rightKeep) queried).run state))
    (hinv : Inv state.1) : Inv step.2.1 := by
  classical
  rcases queried with coin | input
  · rw [step_inl pk rightKeep coin state step hstep]
    exact hinv
  · have hnoticed : Inv (servingNotice pk state.1 input) := by
      rw [servingNotice]
      split
      · exact hfile state.1 input hinv (by assumption)
      · exact hinv
    rcases step_inr_cases pk rightKeep input state step hstep with ⟨-, hstate⟩ | ⟨-, hstate⟩
    · rw [hstate]; exact hnoticed
    · rw [hstate]; exact hcache _ input step.1 hnoticed

open scoped Classical in
/-- **And therefore a run.** -/
theorem runInvariant (rightKeep : Bytes → State → Prop) (Inv : State → Prop)
    (hcache : ∀ (carrier : State) (input : Bytes) (answer : HashOutput),
      Inv carrier → Inv (cacheAnswer carrier input answer))
    (hfile : ∀ (carrier : State) (input : Bytes),
      Inv carrier → FilesLeft pk carrier input → Inv (file carrier input))
    {α : Type} (computation : OracleComp OracleWorld α) :
    ∀ (state : StateOf State) (z : α × StateOf State),
      z ∈ support ((simulateQ (@noticingRecorderOf State (servingView pk) (disclosingKeep pk) rightKeep) computation).run state) →
        Inv state.1 → Inv z.2.1 := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro state z hz hinv
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    rw [show z.2 = state from by rw [hz]]
    exact hinv
  | query_bind queried next ih =>
    intro state z hz hinv
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨step, hstep, hrest⟩ := hz
    exact ih step.1 step.2 z hrest
      (stepInvariant pk rightKeep Inv hcache hfile queried state step hstep hinv)

open scoped Classical in
/-- **One query of a run, read with its continuation.** -/
theorem queryStep (rightKeep : Bytes → State → Prop) {α : Type} (input : Bytes)
    (next : OracleWorld.Range (Sum.inr input) → OracleComp OracleWorld α)
    (state : StateOf State) (result : α × StateOf State)
    (hresult : result ∈ support ((simulateQ (@noticingRecorderOf State (servingView pk) (disclosingKeep pk) rightKeep)
      ((query (spec := OracleWorld) (Sum.inr input) :
        OracleComp OracleWorld (OracleWorld.Range (Sum.inr input))) >>= next)).run state)) :
    ∃ (answer : HashOutput) (mid : StateOf State),
      mid.1.cache input = some answer ∧ mid.1.framing = state.1.framing ∧
        Grows state.1 mid.1 ∧ (FilesLeft pk state.1 input → Served mid.1 input) ∧
        result ∈ support ((simulateQ (@noticingRecorderOf State (servingView pk) (disclosingKeep pk) rightKeep) (next answer)).run mid) := by
  classical
  rw [simulateQ_bind,
    show simulateQ (@noticingRecorderOf State (servingView pk) (disclosingKeep pk) rightKeep)
        (query (spec := OracleWorld) (Sum.inr input) :
          OracleComp OracleWorld (OracleWorld.Range (Sum.inr input))) =
      (@noticingRecorderOf State (servingView pk) (disclosingKeep pk) rightKeep) (Sum.inr input) from by simp,
    StateT.run_bind, mem_support_bind_iff] at hresult
  obtain ⟨step, hstep, hrest⟩ := hresult
  exact ⟨step.1, step.2, step_cached pk rightKeep input state step hstep,
    step_framing pk rightKeep input state step hstep,
    step_grows pk rightKeep input state step hstep,
    fun hfiles => step_served_self pk rightKeep input state step hstep hfiles, hrest⟩

/-! ## The instance -/

/-- **The recorder that notices files.** The facts the agreement reads a handler through, at the
handler the tail runs. With this, `ServedAgreement.record_length_le_cap` applies to a recorder
run. -/
theorem files_carrierRecorder (rightKeep : Bytes → State → Prop) :
    Files pk (@noticingRecorderOf State (servingView pk) (disclosingKeep pk) rightKeep) where
  queryStep := fun input next state result hresult =>
    queryStep pk rightKeep input next state result hresult
  runPersists := fun computation state z hz => runGrows pk rightKeep computation state z hz
  invariant := fun Inv hcache hfile => runInvariant pk rightKeep Inv hcache hfile
  runFraming := fun computation state z hz => runFraming pk rightKeep computation state z hz
  stepGrows := fun queried state step hstep => stepGrows pk rightKeep queried state step hstep
  stepFraming := fun queried state step hstep =>
    stepFraming pk rightKeep queried state step hstep
  hashCached := fun input state step hstep => step_cached pk rightKeep input state step hstep
  hashServed := fun input state step hstep probe hserved =>
    step_served pk rightKeep input state step hstep probe hserved

/-! ## What the handler forgets to

`ServingForget.run_fuseServing_map` asks one thing of the handler underneath a bracketed phase:
that it commute with the projection the brackets leave alone. For the carrier that projection is
"take the cache", and this is the law — the recorder that notices answers exactly as the shared
oracle does, because the notice is bound to leave the cache alone and the recordings ride along
where the projection does not look.

With it, the equations a carrier tail owes are `run_fuseServing_map` at this `ForgetsAlong`
rather than inductions. -/

open scoped Classical in
/-- **One step of the recorder that notices forgets to one step of the shared oracle.** -/
theorem noticingRecorderOf_forget_step (rightKeep : Bytes → State → Prop)
    (queried : OracleWorld.Domain) (state : StateOf State) :
    (fun z : OracleWorld.Range queried × StateOf State => (z.1, CacheView.cacheOf z.2.1)) <$>
        ((@noticingRecorderOf State (servingView pk) (disclosingKeep pk) rightKeep) queried).run
          state =
      (KeygenUniform.rom queried).run (CacheView.cacheOf state.1) := by
  classical
  rcases queried with coin | input
  · rw [@noticingRecorderOf_run_inl State (servingView pk) (disclosingKeep pk) rightKeep coin
      state]
    exact @recorderOf_forget_step State (servingView pk) (disclosingKeep pk) rightKeep
      (Sum.inl coin) state
  · rw [@noticingRecorderOf_run_inr State (servingView pk) (disclosingKeep pk) rightKeep input
      state]
    refine Eq.trans (@recorderOf_forget_step State (servingView pk) (disclosingKeep pk) rightKeep
      (Sum.inr input) (@CacheView.onQuery State (servingView pk) state.1 input, state.2)) ?_
    exact congrArg _ (cacheOf_servingNotice pk state.1 input)

open scoped Classical in
/-- **And therefore a run.** -/
theorem run_noticingRecorderOf_forget (rightKeep : Bytes → State → Prop) {α : Type}
    (computation : OracleComp OracleWorld α) :
    ∀ state : StateOf State,
      (fun z : α × StateOf State => (z.1, CacheView.cacheOf z.2.1)) <$>
          (simulateQ (@noticingRecorderOf State (servingView pk) (disclosingKeep pk) rightKeep)
            computation).run state =
        (simulateQ KeygenUniform.rom computation).run (CacheView.cacheOf state.1) := by
  classical
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro state
    rw [simulateQ_pure, StateT.run_pure, simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind queried next ih =>
    intro state
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind, simulateQ_bind,
      simulateQ_spec_query, StateT.run_bind,
      ← noticingRecorderOf_forget_step pk rightKeep queried state]
    simp only [map_eq_bind_pure_comp, bind_assoc]
    exact bind_congr fun step => ih step.1 step.2

/-- **The law `ServingForget` asks of the handler under a bracketed phase.** -/
theorem forgetsAlong_carrierRecorder (rightKeep : Bytes → State → Prop) :
    ServingForget.ForgetsAlong (fun state : StateOf State => CacheView.cacheOf state.1)
      (@noticingRecorderOf State (servingView pk) (disclosingKeep pk) rightKeep)
      KeygenUniform.rom :=
  fun computation state => run_noticingRecorderOf_forget pk rightKeep computation state

/-! ## The tail's handler

The recorder that notices, counting. The counter goes beside the carrier rather than around the
computation because a bracketed game is not one computation (see `CountedHandler`), and both
laws the tail reads the handler through survive the wrapping, because neither looks at the
counter. -/

/-- The handler a carrier tail runs under. -/
noncomputable def countedCarrierRecorder (rightKeep : Bytes → State → Prop) :
    QueryImpl OracleWorld
      (StateT (State × ((DigestTape.Record × DigestTape.Record) × Nat)) ProbComp) :=
  CountedHandler.withCount
    (@noticingRecorderOf State (servingView pk) (disclosingKeep pk) rightKeep)

/-- **It files.** -/
theorem files_countedCarrierRecorder (rightKeep : Bytes → State → Prop) :
    Files pk (countedCarrierRecorder pk rightKeep) :=
  CountedHandler.files_withCount pk (files_carrierRecorder pk rightKeep)

/-- **And it forgets to the shared oracle**, which is the law a bracketed phase reads it
through. -/
theorem forgetsAlong_countedCarrierRecorder (rightKeep : Bytes → State → Prop) :
    ServingForget.ForgetsAlong
      (fun state : State × ((DigestTape.Record × DigestTape.Record) × Nat) =>
        CacheView.cacheOf (state.1, state.2.1).1)
      (countedCarrierRecorder pk rightKeep) KeygenUniform.rom :=
  CountedHandler.forgetsAlong_withCount
    (fun state : StateOf State => CacheView.cacheOf state.1) _ KeygenUniform.rom
    (forgetsAlong_carrierRecorder pk rightKeep)

end SlhDsaSecurity.CarrierFiles
