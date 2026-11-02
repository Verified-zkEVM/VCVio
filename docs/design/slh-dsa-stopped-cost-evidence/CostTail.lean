/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import VCVio.OracleComp.SimSemantics.StateT.UntilBad

/-!
# Query costs stopped at a bad state

`QueryImpl.stoppedAtBad` freezes a handler's state after `bad` holds. An input-weighted
counter can retain the cost of the query that first raises `bad` and ignore later queries.

`QueryImpl.prEvent_stopped_cost_gt_le_full_cost_gt` compares the upper tail of this stopped
cost with the complete cost of an implementation related by `QueryImpl.DominatedUntilBad`.
The comparison preserves arbitrary initial counters and does not require the original
handler to preserve `bad`.
-/

public section

open OracleComp OracleSpec MeasureTheory

namespace QueryImpl

/-- Execute `impl` until its state satisfies `bad`, then return `fallback` without changing
the state. The query that first raises `bad` executes normally; subsequent queries are frozen. -/
@[expose]
def stoppedAtBad {ι σ : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec (StateT σ ProbComp))
    (bad : σ → Prop) [DecidablePred bad]
    (fallback : (t : spec.Domain) → spec.Range t) :
    QueryImpl spec (StateT σ ProbComp) :=
  fun t => StateT.mk fun s =>
    if bad s then pure (fallback t, s) else (impl t).run s


private theorem extendState_nat_counter_mono
    {ι σ α : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec (StateT σ ProbComp))
    (aux : (t : spec.Domain) → σ → spec.Range t → σ → Nat → Nat)
    (haux : ∀ t s a s' n, n ≤ aux t s a s' n)
    (program : OracleComp spec α) (state : σ) (n : Nat)
    {z : α × σ × Nat}
    (hz : z ∈ support ((simulateQ (impl.extendState aux) program).run (state, n))) :
    n ≤ z.2.2 := by
  refine simulateQ_run_preservesInv (impl.extendState aux) (fun s => n ≤ s.2) ?_
    program (state, n) le_rfl z hz
  intro t s hs z hz
  have heq := (mem_support_extendState_run_iff impl aux t s z).mp hz
  rw [heq.2]
  exact hs.trans (haux t s.1 z.1 z.2.1 s.2)

private theorem stoppedAtBad_counter_eq
    {ι σ α : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec (StateT σ ProbComp))
    (bad : σ → Prop) [DecidablePred bad]
    (fallback : (t : spec.Domain) → spec.Range t) (cost : spec.Domain → Nat)
    (program : OracleComp spec α) (state : σ) (hb : bad state) (n : Nat)
    {z : α × σ × Nat}
    (hz : z ∈ support ((simulateQ
      ((impl.stoppedAtBad bad fallback).extendState
        (fun t s _ _ n => if bad s then n else n + cost t)) program).run (state, n))) :
    z.2.2 = n := by
  let D := (impl.stoppedAtBad bad fallback).extendState
    (fun t s _ _ n => if bad s then n else n + cost t)
  have hpres : PreservesInv D (fun s => bad s.1 ∧ s.2 = n) := by
    intro t s hs z hz
    have hstep : (D t).run s = pure (fallback t, s) := by
      simp [D, extendState_apply, stoppedAtBad, hs.1]
    rw [hstep, support_pure, Set.mem_singleton_iff] at hz
    subst z
    exact hs
  exact (simulateQ_run_preservesInv D _ hpres program (state,n) ⟨hb,rfl⟩ z hz).2

/-- The upper tail of input-weighted query cost stopped after the first bad state is bounded
by the upper tail of the complete cost under a dominating implementation.

The stopped run charges the query that first raises `bad`, then freezes both its base state
and counter. Both implementations use the same nonnegative input weights and initial counter.
One-step domination on non-bad poststates and preservation of `inv` suffice. -/
theorem prEvent_stopped_cost_gt_le_full_cost_gt
    {ι σD σR α : Type} {spec : OracleSpec ι}
    (deferred : QueryImpl spec (StateT σD ProbComp))
    (real : QueryImpl spec (StateT σR ProbComp))
    (project : σD → σR) (inv bad : σD → Prop) [DecidablePred bad]
    (hdom : DominatedUntilBad deferred real project inv bad)
    (hinv : PreservesInv deferred inv)
    (fallback : (t : spec.Domain) → spec.Range t)
    (cost : spec.Domain → Nat)
    (program : OracleComp spec α) (state : σD) (hstate : inv state)
    (initialCost limit : Nat) :
    Pr{let z ←
        (simulateQ ((stoppedAtBad deferred bad fallback).extendState
          (fun t s _ _ n => if bad s then n else n + cost t)) program).run
          (state, initialCost)}[limit < z.2.2] ≤
      Pr{let z ←
        (simulateQ (real.extendState
          (fun t _ _ _ n => n + cost t)) program).run
          (project state, initialCost)}[limit < z.2.2] := by
  let D := (deferred.stoppedAtBad bad fallback).extendState
    (fun t s _ _ n => if bad s then n else n + cost t)
  let R := real.extendState (fun t _ _ _ n => n + cost t)
  change Pr{let z ← (simulateQ D program).run (state, initialCost)}[limit < z.2.2] ≤
    Pr{let z ← (simulateQ R program).run (project state, initialCost)}[limit < z.2.2]
  induction program using OracleComp.inductionOn generalizing state initialCost with
  | pure x =>
    simp only [simulateQ_pure, StateT.run_pure]
    exact le_rfl
  | query_bind t k ih =>
    by_cases hb : bad state
    · by_cases hn : limit < initialCost
      · have hr : Pr{let z ← (simulateQ R (liftM (OracleSpec.query t) >>= k)).run (project state, initialCost)}[limit < z.2.2] = 1 := by
          refine prEvent_eq_one_of_forall_mem_support _ _ fun z hz => ?_
          exact hn.trans_le (extendState_nat_counter_mono real
            (fun t _ _ _ n => n + cost t) (fun _ _ _ _ _ => Nat.le_add_right _ _)
            _ _ _ hz)
        rw [hr]
        exact prEvent_le_one _
      · rw [prEvent_eq_zero_of_forall_mem_support _ _ (fun z hz hlim => ?_)]
        · exact zero_le
        · exact hn ((stoppedAtBad_counter_eq deferred bad fallback cost _ state hb initialCost hz) ▸ hlim)
    have hd : (D t).run (state, initialCost) =
        ((deferred t).run state >>= fun z => pure (z.1, (z.2, initialCost + cost t))) := by
      simp [D, extendState_apply, stoppedAtBad, hb]
    have hr : (R t).run (project state, initialCost) =
        ((real t).run (project state) >>= fun z => pure (z.1, (z.2, initialCost + cost t))) := rfl
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, hd, hr,
      bind_assoc, pure_bind]
    by_cases hn : limit < initialCost + cost t
    · have hone : Pr{let z ← (real t).run (project state) >>= fun z =>
          (simulateQ R (k z.1)).run (z.2, initialCost + cost t)}[limit < z.2.2] = 1 := by
        refine prEvent_eq_one_of_forall_mem_support _ _ fun z hz => ?_
        rw [mem_support_bind_iff] at hz
        obtain ⟨u, hu, hz⟩ := hz
        exact hn.trans_le (extendState_nat_counter_mono real
          (fun t _ _ _ n => n + cost t) (fun _ _ _ _ _ => Nat.le_add_right _ _)
          _ _ _ hz)
      rw [hone]
      exact prEvent_le_one _
    let _ : MeasurableSpace (spec.Range t × σD) := ⊤
    let _ : MeasurableSpace (spec.Range t × σR) := ⊤
    rw [prEvent_bind_eq_lintegral_of_discrete, prEvent_bind_eq_lintegral_of_discrete]
    let f : spec.Range t × σD → ENNReal := fun z =>
      Pr{let w ← (simulateQ D (k z.1)).run (z.2, initialCost + cost t)}[limit < w.2.2]
    let g : spec.Range t × σR → ENNReal := fun z =>
      Pr{let w ← (simulateQ R (k z.1)).run (z.2, initialCost + cost t)}[limit < w.2.2]
    have hsupp : f.support ⊆ {z | ¬bad z.2} := by
      intro z hz hbad
      apply hz
      apply prEvent_eq_zero_of_forall_mem_support
      intro w hw hlim
      exact hn ((stoppedAtBad_counter_eq deferred bad fallback cost _ z.2 hbad _ hw) ▸ hlim)
    have hae : ∀ᵐ z ∂𝒟[(deferred t).run state], inv z.2 :=
      evalDist.ae_of_forall_mem_support _ _ MeasurableSet.of_discrete
        fun z hz => hinv t state hstate z hz
    have hμ : Measure.map (fun z : spec.Range t × σD => (z.1, project z.2))
        ((𝒟[(deferred t).run state]).restrict {z | ¬bad z.2}) ≤
        𝒟[(real t).run (project state)] := by
      refine Measure.le_iff.2 fun A _ => ?_
      rw [Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete,
        Measure.restrict_apply MeasurableSet.of_discrete]
      simpa only [prEvent_eq_evalDist_of_discrete, Set.inter_def, Set.mem_ofPred_eq,
        Set.mem_preimage, Set.ofPred_mem_eq] using hdom t state hstate hb (· ∈ A)
    calc
      _ = ∫⁻ z in {z | ¬bad z.2}, f z ∂𝒟[(deferred t).run state] :=
        (setLIntegral_eq_of_support_subset hsupp).symm
      _ ≤ ∫⁻ z in {z | ¬bad z.2}, g (z.1, project z.2) ∂𝒟[(deferred t).run state] :=
        setLIntegral_mono_ae Measurable.of_discrete.aemeasurable
          (hae.mono fun z hz _ => ih z.1 z.2 hz (initialCost + cost t))
      _ = ∫⁻ y, g y ∂(Measure.map (fun z : spec.Range t × σD => (z.1, project z.2))
            ((𝒟[(deferred t).run state]).restrict {z | ¬bad z.2})) :=
        (lintegral_map Measurable.of_discrete Measurable.of_discrete).symm
      _ ≤ _ := lintegral_mono' hμ le_rfl

end QueryImpl
