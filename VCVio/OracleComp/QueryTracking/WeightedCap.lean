/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans, Alexander Hicks
-/

module
public import VCVio.OracleComp.QueryTracking.QueryBound.Basic
public import VCVio.EvalDist.ProbabilityBounds
public import VCVio.OracleComp.EvalDist.Measure

/-!
# Weighted query caps with an explicit stop result

A query is issued only when its weight fits the remaining budget.
A refused query returns outer `none` before the query or its continuation runs.
Zero-weight queries remain allowed at zero budget.
Successful events retain the returned value and the complete terminal handler state jointly.
-/

public section

open OracleSpec

namespace OracleComp.WeightedCap

variable {ι : Type} {spec : OracleSpec ι} {α : Type}

/-- **Truncate once the weighted queries would exceed the limit, returning `none` then.** -/
@[expose] noncomputable def capCompOpt (weight : ι → Nat) :
    Nat → OracleComp spec α → OracleComp spec (Option α) :=
  fun limit oa => OracleComp.construct (C := fun _ => Nat → OracleComp spec (Option α))
    (fun value _ => pure (some value))
    (fun t _ rest remaining =>
      if weight t ≤ remaining then
        liftM (spec.query t) >>= fun answer => rest answer (remaining - weight t)
      else pure none) oa limit

/-- The option-reporting cap returns a pure value as `some`. -/
theorem capCompOpt_pure (weight : ι → Nat) (limit : Nat) (value : α) :
    capCompOpt weight limit (pure value : OracleComp spec α) = pure (some value) := rfl

/-- The option-reporting cap pays for a query it can afford, else returns `none`. -/
theorem capCompOpt_query_bind (weight : ι → Nat) (limit : Nat) (t : ι)
    (next : spec.Range t → OracleComp spec α) :
    capCompOpt weight limit (liftM (spec.query t) >>= next) =
      if weight t ≤ limit then
        liftM (spec.query t) >>= fun answer => capCompOpt weight (limit - weight t)
          (next answer)
      else pure none := rfl

variable {S : Type}

/-- A handler whose state reports the weighted cost, query by query. -/
@[expose] def ReportsCost (impl : QueryImpl spec (StateT S ProbComp)) (weight : ι → Nat)
    (cost : S → Nat) : Prop :=
  ∀ (t : ι) (state : S), ∀ z ∈ support ((impl t).run state), cost z.2 = cost state + weight t

/-- The cost only grows along a run. -/
theorem cost_run_ge (impl : QueryImpl spec (StateT S ProbComp)) (weight : ι → Nat)
    (cost : S → Nat) (hcost : ReportsCost impl weight cost) :
    ∀ (oa : OracleComp spec α) (state : S),
      ∀ z ∈ support ((simulateQ impl oa).run state), cost state ≤ cost z.2 := by
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure value =>
    intro state z hz
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    rw [hz]
  | query_bind t next ih =>
    intro state z hz
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨step, hstep, hrest⟩ := hz
    have := ih step.1 step.2 z hrest
    have hstepCost := hcost t state step hstep
    omega

/-- **The capped run's cost stays within the limit.** -/
theorem cost_capCompOpt_le (impl : QueryImpl spec (StateT S ProbComp)) (weight : ι → Nat)
    (cost : S → Nat) (hcost : ReportsCost impl weight cost) :
    ∀ (oa : OracleComp spec α) (limit : Nat) (state : S),
      ∀ z ∈ support ((simulateQ impl (capCompOpt weight limit oa)).run state),
        cost z.2 ≤ cost state + limit := by
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure value =>
    intro limit state z hz
    rw [capCompOpt_pure, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hz
    rw [hz]
    dsimp only
    omega
  | query_bind t next ih =>
    intro limit state z hz
    rw [capCompOpt_query_bind] at hz
    split_ifs at hz with hweight
    · rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hz
      obtain ⟨step, hstep, hrest⟩ := hz
      have := ih step.1 (limit - weight t) step.2 z hrest
      have hstepCost := hcost t state step hstep
      omega
    · rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      rw [hz]
      dsimp only
      omega

/-- **Where the uncapped run stays within the limit, the capped one never fires.** -/
theorem evalDist_capCompOpt (impl : QueryImpl spec (StateT S ProbComp)) (weight : ι → Nat)
    (cost : S → Nat) (hcost : ReportsCost impl weight cost) :
    ∀ (oa : OracleComp spec α) (limit : Nat) (state : S),
      (∀ z ∈ support ((simulateQ impl oa).run state), cost z.2 ≤ cost state + limit) →
        (simulateQ impl (capCompOpt weight limit oa)).run state =ᵈ
          ((fun z => (some z.1, z.2)) <$> (simulateQ impl oa).run state) := by
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure value =>
    intro limit state _
    rw [capCompOpt_pure, simulateQ_pure, simulateQ_pure, StateT.run_pure, StateT.run_pure,
      map_pure]
  | query_bind t next ih =>
    intro limit state hbound
    rw [capCompOpt_query_bind]
    split_ifs with hweight
    · simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
      refine OracleComp.EvalDistEq.bind_congr_of_support _ ?_
      intro step hstep
      refine ih step.1 (limit - weight t) step.2 fun z hz => ?_
      have hwhole : z ∈ support ((simulateQ impl (liftM (spec.query t) >>= next)).run state) := by
        rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff]
        exact ⟨step, hstep, hz⟩
      have := hbound z hwhole
      have hstepCost := hcost t state step hstep
      omega
    · exfalso
      obtain ⟨step, hstep⟩ := OracleComp.support_nonempty ((impl t).run state)
      obtain ⟨z, hz⟩ := OracleComp.support_nonempty ((simulateQ impl (next step.1)).run step.2)
      have hwhole : z ∈ support ((simulateQ impl (liftM (spec.query t) >>= next)).run state) := by
        rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff]
        exact ⟨step, hstep, hz⟩
      have h1 := hbound z hwhole
      have h2 := cost_run_ge impl weight cost hcost (next step.1) step.2 z hz
      have h3 := hcost t state step hstep
      omega

/-- **A capped run that did not fire is a run of the uncapped computation.** -/
theorem mem_support_of_capCompOpt_some (impl : QueryImpl spec (StateT S ProbComp))
    (weight : ι → Nat) :
    ∀ (oa : OracleComp spec α) (limit : Nat) (state : S) (value : α) (final : S),
      (some value, final) ∈ support ((simulateQ impl (capCompOpt weight limit oa)).run state) →
        (value, final) ∈ support ((simulateQ impl oa).run state) := by
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure value =>
    intro limit state v final hz
    rw [capCompOpt_pure, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hz
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff]
    cases hz
    rfl
  | query_bind t next ih =>
    intro limit state v final hz
    rw [capCompOpt_query_bind] at hz
    split_ifs at hz with hweight
    · rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hz
      obtain ⟨step, hstep, hrest⟩ := hz
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff]
      exact ⟨step, hstep, ih step.1 (limit - weight t) step.2 v final hrest⟩
    · rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      cases hz

/-- Positive selected-query weights bound their number under the cap itself.

No structural or semantic budget premise on the original program is required.
-/
theorem isQueryBoundP_capCompOpt (weight : ι → Nat) (p : ι → Prop) [DecidablePred p]
    (positive : ∀ t, p t → 0 < weight t) :
    ∀ (oa : OracleComp spec α) (limit : Nat),
      IsQueryBoundP (capCompOpt weight limit oa) p limit := by
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure value =>
    intro limit
    rw [capCompOpt_pure]
    exact isQueryBoundP_pure p _ _
  | query_bind t next ih =>
    intro limit
    rw [capCompOpt_query_bind]
    split_ifs with affordable
    · rw [isQueryBoundP_query_bind_iff]
      refine ⟨?_, fun answer => ?_⟩
      · by_cases selected : p t
        · exact Or.inr (by have := positive t selected; omega)
        · exact Or.inl selected
      · apply (ih answer (limit - weight t)).mono
        split_ifs with selected
        · have := positive t selected
          omega
        · exact Nat.sub_le _ _
    · exact isQueryBoundP_pure p _ _

/-- A mandatory unselected unit-weight first query reserves one unit of the cap.

Natural subtraction includes zero: an unaffordable first query returns `none`.
-/
theorem isQueryBoundP_capCompOpt_after_unprotected_unit_query
    (weight : ι → Nat) (p : ι → Prop) [DecidablePred p]
    (positive : ∀ t, p t → 0 < weight t) (first : ι)
    (firstWeight : weight first = 1) (unselected : ¬ p first)
    (next : spec.Range first → OracleComp spec α) (limit : Nat) :
    IsQueryBoundP (capCompOpt weight limit (liftM (spec.query first) >>= next)) p
      (limit - 1) := by
  rw [capCompOpt_query_bind]
  split_ifs with affordable
  · rw [isQueryBoundP_query_bind_iff]
    refine ⟨Or.inl unselected, fun answer => ?_⟩
    simpa [unselected, firstWeight] using
      isQueryBoundP_capCompOpt weight p positive (next answer) (limit - weight first)
  · exact isQueryBoundP_pure p _ _

/-- A successful capped event is dominated by the same full-state uncapped event.

Outer `none` contributes no successful event mass.
No cost-reporting or budget premise on the handler or program is required.
-/
theorem prEvent_run_capCompOpt_some_le {State : Type}
    (impl : QueryImpl spec (StateT State ProbComp)) (weight : ι → Nat)
    (event : α × State → Prop) :
    ∀ (oa : OracleComp spec α) (limit : Nat) (initial : State),
      Pr{let z ← (simulateQ impl (capCompOpt weight limit oa)).run initial}[
        z.1.elim False (fun value => event (value, z.2))] ≤
      Pr{let z ← (simulateQ impl oa).run initial}[event z] := by
  classical
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure value =>
    intro limit initial
    simp [capCompOpt_pure, simulateQ_pure, StateT.run_pure]
  | query_bind t next ih =>
    intro limit initial
    rw [capCompOpt_query_bind]
    split_ifs with affordable
    · simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      exact prEvent_bind_mono_of_forall_le _ _ _ _ _
        (fun step => ih step.1 (limit - weight t) step.2)
    · simp [simulateQ_pure, StateT.run_pure]

/-- A single forwarded query with a pure dependent reply map commutes with the cap.

Matching query weights preserve the exact stopped prefix.
Neither the index map nor the reply map needs an inverse.
-/
theorem simulateQ_capCompOpt_single_query {κ : Type} {target : OracleSpec κ}
    (sourceWeight : ι → Nat) (targetWeight : κ → Nat) (indexMap : ι → κ)
    (replyMap : ∀ i, target.Range (indexMap i) → spec.Range i)
    (compatible : ∀ i, targetWeight (indexMap i) = sourceWeight i)
    (oa : OracleComp spec α) (limit : Nat) :
    simulateQ
        (fun i => replyMap i <$>
          (liftM (target.query (indexMap i)) : OracleComp target (target.Range (indexMap i))))
        (capCompOpt sourceWeight limit oa) =
      capCompOpt targetWeight limit
        (simulateQ
          (fun i => replyMap i <$>
            (liftM (target.query (indexMap i)) : OracleComp target (target.Range (indexMap i))))
          oa) := by
  let impl : QueryImpl spec (OracleComp target) :=
    fun i => replyMap i <$>
      (liftM (target.query (indexMap i)) : OracleComp target (target.Range (indexMap i)))
  change simulateQ impl (capCompOpt sourceWeight limit oa) =
    capCompOpt targetWeight limit (simulateQ impl oa)
  induction oa using OracleComp.inductionOn generalizing limit with
  | pure value => simp [capCompOpt_pure]
  | query_bind i next ih =>
    by_cases affordable : sourceWeight i ≤ limit <;>
      simp [capCompOpt_query_bind, impl, compatible, affordable, bind_map_left, ih]

end OracleComp.WeightedCap
