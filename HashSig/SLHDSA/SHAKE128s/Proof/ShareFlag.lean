/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.ShareUntilBad
public import HashSig.SLHDSA.SHAKE128s.Proof.SignedWatch

/-!
# What a step of the shared games does to the state

Three facts about one step of `ShareGame.handler`, at either setting of `lenient`, and what they
give over a run.

* **The record only grows, and what it gains is filed at the current digests**
  (`step_shape`): a step appends a list of inputs, each beside the digests served when the step
  began, and the served digests only grow. The claims append only the candidates not already
  filed at those digests, and nothing once the flag is up (`record_claims`, `length_claims`).
* **The flag is witnessed by the record**: a raised flag means a bad walk or an entry of the
  record that is a guess at the digests it was filed with (`flag_witness`). This is what turns
  the flag of the blind game into a union over record entries, each charged once.
* **The record's length is the cap's weight** (`reportsCost`): at the adversary's own oracles,
  split by `splitter`, a step adds exactly `weight` entries. So the capped adversary files at
  most `limit` entries, whatever the handler answers.
-/

public section

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.ShareFlag

open Security ShareGame

/-! ## The routing leaves the bookkeeping alone -/

/-- A plain oracle step leaves the served list, the record and the log alone. -/
theorem plain_mem_support (state : St) (input : Bytes) (z : HashOutput × St)
    (hz : z ∈ support (plain state input)) :
    z.2.served = state.served ∧ z.2.record = state.record ∧ z.2.log = state.log := by
  unfold plain at hz
  split at hz
  · rw [support_pure, Set.mem_singleton_iff] at hz
    rw [hz]
    exact ⟨rfl, rfl, rfl⟩
  · rw [mem_support_bind_iff] at hz
    obtain ⟨value, -, hz⟩ := hz
    rw [support_pure, Set.mem_singleton_iff] at hz
    rw [hz]
    exact ⟨rfl, rfl, rfl⟩

/-- A `PRF_msg` step leaves the served list, the record and the log alone. -/
theorem prfAt_mem_support (state : St) (frame : Bytes) (z : HashOutput × St)
    (hz : z ∈ support (prfAt state frame)) :
    z.2.served = state.served ∧ z.2.record = state.record ∧ z.2.log = state.log := by
  unfold prfAt at hz
  split at hz
  · rw [support_pure, Set.mem_singleton_iff] at hz
    rw [hz]
    exact ⟨rfl, rfl, rfl⟩
  · rw [mem_support_bind_iff] at hz
    obtain ⟨value, -, hz⟩ := hz
    rw [support_pure, Set.mem_singleton_iff] at hz
    rw [hz]
    exact ⟨rfl, rfl, rfl⟩

/-- A routed hash query leaves the served list, the record and the log alone. -/
theorem route_mem_support (lenient : Bool) (setup : Setup) (state : St) (input : Bytes)
    (z : HashOutput × St) (hz : z ∈ support (route lenient setup state input)) :
    z.2.served = state.served ∧ z.2.record = state.record ∧ z.2.log = state.log := by
  classical
  unfold route at hz
  split at hz
  · rw [support_pure, Set.mem_singleton_iff] at hz
    rw [hz]
    exact ⟨rfl, rfl, rfl⟩
  · split_ifs at hz
    · exact prfAt_mem_support state _ z hz
    · exact plain_mem_support state input z hz

/-! ## One step -/

/-- The entries a list of inputs files at the current digests. -/
@[expose]
def filed (served : List HashOutput) (inputs : List Bytes) : List (Bytes × List HashOutput) :=
  inputs.map fun input => (input, served)

open scoped Classical in
/-- **What one step does**: it files some inputs at the current digests, grows the digests, and
raises the flag only at a bad walk or a guess the new record holds at the current digests —
filed by this step, or, for a claim that repeats an entry, already filed before it. -/
theorem step_shape (lenient : Bool) (setup : Setup) (queried : ShareSpec.Domain)
    (state : St × Bool) (z : ShareSpec.Range queried × (St × Bool))
    (hz : z ∈ support (((handler lenient setup) queried).run state)) :
    ∃ inputs : List Bytes,
      z.2.1.record = state.1.record ++ filed state.1.served inputs ∧
        state.1.served <+: z.2.1.served ∧
          (z.2.2 = true → state.2 = true ∨ ¬ setup.Good ∨
            ∃ input, (input, state.1.served) ∈ z.2.1.record ∧
              Guess setup state.1.served input) := by
  classical
  obtain ⟨inner, flag⟩ := state
  rcases queried with ((world | request) | ⟨request, drawn⟩) | forgery
  · rcases world with coin | input
    · simp only [handler, StateT.run, mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff] at hz
      obtain ⟨value, -, rfl⟩ := hz
      exact ⟨[], by simp [filed], List.prefix_refl _, fun h => Or.inl h⟩
    · simp only [handler, StateT.run, mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff] at hz
      obtain ⟨step, hstep, rfl⟩ := hz
      obtain ⟨hserved, -, -⟩ := route_mem_support lenient setup inner input step hstep
      refine ⟨[input], by simp [filed], by rw [hserved], fun h => ?_⟩
      simp only [Bool.or_eq_true, decide_eq_true_eq] at h
      rcases h with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨input, by simp, h⟩)
  · cases hframe : request.frame with
    | none =>
      simp only [handler, StateT.run, hframe, support_pure, Set.mem_singleton_iff] at hz
      rw [hz]
      exact ⟨[], by simp [filed], List.prefix_refl _, fun h => Or.inl h⟩
    | some framed =>
      simp only [handler, StateT.run, hframe, mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff] at hz
      obtain ⟨seed, hseed, digest, hdigest, rfl⟩ := hz
      obtain ⟨hseedServed, -, -⟩ := prfAt_mem_support inner framed seed hseed
      obtain ⟨hdigestServed, -, -⟩ := route_mem_support lenient setup seed.2 _ digest hdigest
      refine ⟨[Hashing.messageInput (Hashing.truncate seed.1) setup.pk framed],
        by simp [filed], ⟨[digest.1], by rw [hdigestServed, hseedServed]⟩, fun h => ?_⟩
      simp only [Bool.or_eq_true, decide_eq_true_eq] at h
      rcases h with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨_, by simp, h⟩)
  · cases drawn with
    | none =>
      simp only [handler, StateT.run, support_pure, Set.mem_singleton_iff] at hz
      rw [hz]
      exact ⟨[], by simp [filed], List.prefix_refl _, fun h => Or.inl h⟩
    | some pair =>
      obtain ⟨randomizer, digest⟩ := pair
      simp only [handler, StateT.run] at hz
      split_ifs at hz <;>
      · rw [support_pure, Set.mem_singleton_iff] at hz
        rw [hz]
        exact ⟨[], by simp [filed], List.prefix_refl _, fun h => Or.inl h⟩
  · simp only [handler, StateT.run, support_pure, Set.mem_singleton_iff] at hz
    rw [hz]
    cases flag with
    | true => exact ⟨[], by simp [filed], List.prefix_refl _, fun _ => Or.inl rfl⟩
    | false =>
      refine ⟨unfiled inner.record inner.served (claimsOf setup inner forgery), by simp [filed],
        List.prefix_refl _, fun h => ?_⟩
      simp only [Bool.or_eq_true, decide_eq_true_eq] at h
      rcases h with h | h | ⟨candidate, hcandidate, h⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · refine Or.inr (Or.inr ⟨candidate, ?_, h⟩)
        by_cases hold : (candidate, inner.served) ∈ inner.record
        · exact List.mem_append_left _ hold
        · exact List.mem_append_right _
            (List.mem_map.mpr ⟨candidate, mem_unfiled.mpr ⟨hcandidate, hold⟩, rfl⟩)

/-! ## Over a run -/

/-- **The invariant a run keeps**: a raised flag is a bad walk or a guess the record holds. -/
@[expose] def Witnessed (setup : Setup) (state : St × Bool) : Prop :=
  state.2 = true → ¬ setup.Good ∨ ∃ entry ∈ state.1.record, Guess setup entry.2 entry.1

/-! ## The record counts the cap's weight -/

/-- The game's handler, read at the adversary's own oracles. -/
@[expose] noncomputable def advImpl (lenient : Bool) (setup : Setup) :
    QueryImpl (OracleWorld + SigningSpec) (StateT (St × Bool) ProbComp) :=
  QueryImpl.compose (handler lenient setup) splitter

/-- The number of entries a query files: at the claims, the candidates not already filed, and
none once the flag is up. -/
@[expose] noncomputable def added (setup : Setup) (state : St × Bool) : ShareSpec.Domain → Nat
  | Sum.inl (Sum.inl (Sum.inl (Sum.inl _))) => 0
  | Sum.inl (Sum.inl (Sum.inl (Sum.inr _))) => 1
  | Sum.inl (Sum.inl (Sum.inr request)) => if request.frame.isSome then 1 else 0
  | Sum.inl (Sum.inr _) => 0
  | Sum.inr forgery =>
      if state.2 then 0
      else (unfiled state.1.record state.1.served (claimsOf setup state.1 forgery)).length

/-- **The length a step adds.** -/
theorem length_step (lenient : Bool) (setup : Setup) (queried : ShareSpec.Domain)
    (state : St × Bool) (z : ShareSpec.Range queried × (St × Bool))
    (hz : z ∈ support (((handler lenient setup) queried).run state)) :
    z.2.1.record.length = state.1.record.length + added setup state queried := by
  classical
  obtain ⟨inner, flag⟩ := state
  rcases queried with ((world | request) | ⟨request, drawn⟩) | forgery
  · rcases world with coin | input
    · simp only [handler, StateT.run, mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff] at hz
      obtain ⟨value, -, rfl⟩ := hz
      rfl
    · simp only [handler, StateT.run, mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff] at hz
      obtain ⟨step, -, rfl⟩ := hz
      simp [added]
  · cases hframe : request.frame with
    | none =>
      simp only [handler, StateT.run, hframe, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      simp [added, hframe]
    | some framed =>
      simp only [handler, StateT.run, hframe, mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff] at hz
      obtain ⟨seed, -, digest, -, rfl⟩ := hz
      simp [added, hframe]
  · cases drawn with
    | none =>
      simp only [handler, StateT.run, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      rfl
    | some pair =>
      obtain ⟨randomizer, digest⟩ := pair
      simp only [handler, StateT.run] at hz
      split_ifs at hz <;>
      · rw [support_pure, Set.mem_singleton_iff] at hz
        subst hz
        rfl
  · simp only [handler, StateT.run, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    cases flag <;> simp [added]

/-- **What the claims file**: with the flag down, the candidates not already filed at the
current digests; with the flag up, nothing. -/
theorem record_claims (lenient : Bool) (setup : Setup) (forgery : Forgery) (state : St × Bool)
    (z : Unit × (St × Bool))
    (hz : z ∈ support (((handler lenient setup) (Sum.inr forgery)).run state)) :
    (state.2 = false → z.2.1.record = state.1.record ++ filed state.1.served
      (unfiled state.1.record state.1.served (claimsOf setup state.1 forgery))) ∧
    (state.2 = true → z.2.1.record = state.1.record) := by
  obtain ⟨inner, flag⟩ := state
  simp only [handler, StateT.run, support_pure] at hz
  subst hz
  cases flag <;> simp [filed]

/-- **The record's length reports the cap's weight.** -/
theorem reportsCost (lenient : Bool) (setup : Setup) :
    CapComp.ReportsCost (advImpl lenient setup) weight
      (fun state : St × Bool => state.1.record.length) := by
  intro queried state z hz
  rcases queried with (coin | input) | request
  · simp only [advImpl, QueryImpl.apply_compose, splitter, worldQuery] at hz
    have := length_step lenient setup (Sum.inl (Sum.inl (Sum.inl (Sum.inl coin)))) state z
      (by simpa using hz)
    simpa [weight, added] using this
  · simp only [advImpl, QueryImpl.apply_compose, splitter, worldQuery] at hz
    have := length_step lenient setup (Sum.inl (Sum.inl (Sum.inl (Sum.inr input)))) state z
      (by simpa using hz)
    simpa [weight, added] using this
  · simp only [advImpl, QueryImpl.apply_compose, splitter] at hz
    rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨step, hstep, hz⟩ := hz
    have hdraw := length_step lenient setup (Sum.inl (Sum.inl (Sum.inr request))) state step
      (by simpa using hstep)
    have hassemble := length_step lenient setup (Sum.inl (Sum.inr (request, step.1))) step.2 z
      (by simpa using hz)
    simp only [weight, added] at hdraw hassemble ⊢
    omega

end SlhDsaSecurity.ShareFlag
