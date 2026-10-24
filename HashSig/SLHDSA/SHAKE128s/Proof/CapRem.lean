/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.CapComp

/-!
# Caps that report what they leave

`CapComp.capComp` truncates a computation at a weighted budget and returns only its value. A
game that caps two phases against one budget needs the second cap to start from what the first
left, and a game that skips a step after a cap fired needs to know that it fired. So:

* `capCompRem` returns the value with the unspent budget beside it;
* `capCompOpt` returns `none` if the cap fired and `some value` otherwise.

Each comes with the two facts `CapComp` proves for `capComp` — the capped run's cost is within
the limit (`cost_capCompRem_le`, `cost_capCompOpt_le`), and where the uncapped run stays within
it the cap changes nothing (`evalDist_capCompRem`, `evalDist_capCompOpt`) — and with one more:
**a capped run and the uncapped one agree until the cap fires**, so an event of the uncapped run
that also keeps it within the limit is at most as likely as the event of the capped one
(`probEvent_le_capCompRem`).
-/

public section

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.CapRem

open CapComp

variable {ι : Type} {spec : OracleSpec ι} {α : Type}

/-! ## Reporting the remainder -/

/-- **Truncate once the weighted queries would exceed the limit, and report the remainder.** -/
@[expose] noncomputable def capCompRem (weight : ι → Nat) (fallback : α) :
    Nat → OracleComp spec α → OracleComp spec (α × Nat) :=
  fun limit oa => OracleComp.construct (C := fun _ => Nat → OracleComp spec (α × Nat))
    (fun value remaining => pure (value, remaining))
    (fun t _ rest remaining =>
      if weight t ≤ remaining then
        liftM (spec.query t) >>= fun answer => rest answer (remaining - weight t)
      else pure (fallback, 0)) oa limit

/-- The remainder-reporting cap returns a pure value with the whole budget left. -/
theorem capCompRem_pure (weight : ι → Nat) (fallback : α) (limit : Nat) (value : α) :
    capCompRem weight fallback limit (pure value : OracleComp spec α) = pure (value, limit) := rfl

/-- The remainder-reporting cap pays for a query it can afford, else returns the fallback with
nothing left. -/
theorem capCompRem_query_bind (weight : ι → Nat) (fallback : α) (limit : Nat) (t : ι)
    (next : spec.Range t → OracleComp spec α) :
    capCompRem weight fallback limit (liftM (spec.query t) >>= next) =
      if weight t ≤ limit then
        liftM (spec.query t) >>= fun answer => capCompRem weight fallback (limit - weight t)
          (next answer)
      else pure (fallback, 0) := rfl

variable {S : Type}

/-- **The capped run's cost and its remainder together stay within the limit.** -/
theorem cost_capCompRem_le (impl : QueryImpl spec (StateT S ProbComp)) (weight : ι → Nat)
    (cost : S → Nat) (hcost : ReportsCost impl weight cost) (fallback : α) :
    ∀ (oa : OracleComp spec α) (limit : Nat) (state : S),
      ∀ z ∈ support ((simulateQ impl (capCompRem weight fallback limit oa)).run state),
        cost z.2 + z.1.2 ≤ cost state + limit := by
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure value =>
    intro limit state z hz
    rw [capCompRem_pure, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hz
    rw [hz]
  | query_bind t next ih =>
    intro limit state z hz
    rw [capCompRem_query_bind] at hz
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

/-- **Until the cap fires, the capped run is the uncapped one.** An event of the uncapped run,
followed by any continuation, that also keeps the run within the limit is at most as likely as
the event of the capped run followed by the same continuation, read at the reported remainder. -/
theorem probEvent_le_capCompRem (impl : QueryImpl spec (StateT S ProbComp)) (weight : ι → Nat)
    (cost : S → Nat) (hcost : ReportsCost impl weight cost) (fallback : α) {β : Type}
    (event : β → Prop) :
    ∀ (oa : OracleComp spec α) (limit : Nat) (state : S)
      (next : (α × Nat) × S → ProbComp β),
      Pr{let p ← ((simulateQ impl oa).run state >>= fun z =>
            (fun b => (z, b)) <$> next ((z.1, cost state + limit - cost z.2), z.2) :
            ProbComp ((α × S) × β))}[cost p.1.2 ≤ cost state + limit ∧ event p.2] ≤
        Pr{let x ← (simulateQ impl (capCompRem weight fallback limit oa)).run state >>= next}[
          event x] := by
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure value =>
    intro limit state next
    have h : cost state + limit - cost state = limit := by omega
    rw [capCompRem_pure, simulateQ_pure, simulateQ_pure, StateT.run_pure, StateT.run_pure,
      pure_bind, pure_bind, prEvent_map]
    dsimp only
    rw [h]
    exact prEvent_mono _ _ _ fun (b : β) hb => hb.2
  | query_bind t next ih =>
    intro limit state cont
    rw [capCompRem_query_bind]
    split_ifs with hweight
    · rw [simulateQ_bind, simulateQ_bind, simulateQ_spec_query, StateT.run_bind, StateT.run_bind,
        bind_assoc, bind_assoc]
      refine prEvent_bind_mono_of_forall_le_of_support _ _ _ _ _ fun step hstep => ?_
      have hstepCost := hcost t state step hstep
      have hih := ih step.1 (limit - weight t) step.2 cont
      have hlimit : cost step.2 + (limit - weight t) = cost state + limit := by omega
      rw [hlimit] at hih
      exact hih
    · -- the cap fires here: every uncapped run from this query is already over the limit
      refine le_of_eq_of_le (b := 0) ?_ zero_le
      refine prEvent_eq_zero_of_forall_mem_support _ _ fun p hp hev => ?_
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, bind_assoc,
        mem_support_bind_iff, support_map, Set.mem_image] at hp
      obtain ⟨step, hstep, z, hz, b, -, rfl⟩ := hp
      have h2 := cost_run_ge impl weight cost hcost (next step.1) step.2 z hz
      have h3 := hcost t state step hstep
      have h1 := hev.1
      dsimp only at h1
      omega

/-! ## Reporting whether it fired -/

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
      refine evalDist_bind_congr_support _ _ _ fun step hstep => ?_
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

end SlhDsaSecurity.CapRem
