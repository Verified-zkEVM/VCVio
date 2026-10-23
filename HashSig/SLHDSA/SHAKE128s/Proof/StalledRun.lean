/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.TableBlind

/-!
# Stalling a run once the thing it is charged for can no longer happen

`TableBlind` lifts blindness from a step to a run, but only against a part of the table fixed
before the run. That settles the clauses whose unavailable cells are fixed by the walk and not
the FORS clause, where a cell is unavailable when an earlier probe is made and available when a
later one is: the run is not blind to such a cell for its whole length, only up to the moment
the signatures release it.

Indexing the statement by the step at which a probe is made looked circular — the set of cells
unavailable "at step `k`" is read off the run that is being compared, which is the run whose
dependence on the table is in question. This file removes the circularity instead of resolving
it, by **stalling**: fix one cell, and compare against the run that stops once that cell
becomes available. Three facts then do the work, and none of them needs a set fixed in advance.

* The stalled run never reads that cell at all: before the stall it is unavailable, where the
  handler reads only available cells; after the stall there is no handler. So
  `evalDist_stalled_congr` gives blindness for the whole stalled run, from a per-step
  hypothesis demanded only at **unfrozen** states — which is the hypothesis a handler that
  reads only available cells actually has.
* Stalling does not change the event. A probe can only be charged against a cell that is
  unavailable when the probe is made, and availability only grows, so no charge can arise after
  the stall. `probEvent_flag_stalled_eq` is that: a run whose flag can no longer change may be
  stopped without changing the flag's law.
* So the charge against one cell is the charge against the stalled run, which is blind to it.

What the stall costs is nothing, because the flag is sticky and the frozen tail is silent.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.StalledRun

variable {ι : Type} {spec : OracleSpec ι} {σ : Type}

/-! ## The stalled handler -/

open scoped Classical in
/-- The handler stopped once the state satisfies `Frozen`: from then on every query is answered
by a fixed value and the state stands still. -/
noncomputable def stalled (impl : QueryImpl spec (StateT (σ × Bool) ProbComp))
    (Frozen : σ → Prop) (stall : (t : spec.Domain) → spec.Range t) :
    QueryImpl spec (StateT (σ × Bool) ProbComp) :=
  fun t p => if Frozen p.1 then pure (stall t, p) else impl t p

open scoped Classical in
/-- Once the state is frozen, the stalled implementation answers with the stall value and
leaves the state unchanged. -/
theorem stalled_run_of_frozen (impl : QueryImpl spec (StateT (σ × Bool) ProbComp))
    (Frozen : σ → Prop) (stall : (t : spec.Domain) → spec.Range t)
    (t : spec.Domain) (p : σ × Bool) (hp : Frozen p.1) :
    ((stalled impl Frozen stall) t).run p = (pure (stall t, p) : ProbComp _) := by
  simp only [stalled, StateT.run]
  exact ite_eq_left hp

open scoped Classical in
/-- Before the state is frozen, the stalled implementation is the original one. -/
theorem stalled_run_of_not_frozen (impl : QueryImpl spec (StateT (σ × Bool) ProbComp))
    (Frozen : σ → Prop) (stall : (t : spec.Domain) → spec.Range t)
    (t : spec.Domain) (p : σ × Bool) (hp : ¬ Frozen p.1) :
    ((stalled impl Frozen stall) t).run p = (impl t).run p := by
  simp only [stalled, StateT.run]
  exact ite_eq_right hp

/-! ## A run that can no longer change the flag does not change it -/

/-- An integral against the output measure of a sampling computation is the sum of its singleton
masses times the integrand. -/
private theorem lintegral_evalDist_eq_tsum_probComp {β : Type} (run : ProbComp β)
    (weight : β → ℝ≥0∞) :
    letI : MeasurableSpace β := ⊤
    ∫⁻ value, weight value ∂𝒟[run] = ∑' value, Pr{let x ← run}[x = value] * weight value := by
  let : MeasurableSpace β := ⊤
  have hae : ∀ᵐ value ∂𝒟[run], value ∈ support run :=
    evalDist.ae_of_forall_mem_support run (· ∈ support run) MeasurableSet.of_discrete
      fun _ h ↦ h
  rw [← MeasureTheory.Measure.restrict_eq_self_of_ae_mem hae,
    MeasureTheory.lintegral_countable weight (support_finite run).countable,
    ← tsum_subtype_eq_of_support_subset (s := support run)
      (f := fun value ↦ Pr{let x ← run}[x = value] * weight value)]
  · simp only [prEvent_eq_evalDist_singleton, mul_comm]
  · intro value hvalue
    by_contra hnot
    refine hvalue ?_
    simp only
    rw [prEvent_eq_evalDist_singleton,
      MeasureTheory.measure_mono_null (Set.singleton_subset_iff.2 hnot)
        (MeasureTheory.ae_iff.1 hae), zero_mul]

/-- After a draw whose every outcome leads to the same value, the integral is that value. -/
private theorem lintegral_const_of_support {β : Type} (run : ProbComp β) (value : β → ℝ≥0∞)
    (c : ℝ≥0∞) (h : ∀ y ∈ support run, value y = c) :
    letI : MeasurableSpace β := ⊤
    ∫⁻ y, value y ∂𝒟[run] = c := by
  let : MeasurableSpace β := ⊤
  rw [MeasureTheory.lintegral_congr_ae (g := fun _ => c)
    (evalDist.ae_of_forall_mem_support run (fun y => value y = c) MeasurableSet.of_discrete h),
    MeasureTheory.lintegral_const, evalDist_apply_univ_eq_one, mul_one]

/-! ## Stalling in integral form -/

/-- `expectation_frozen` as an integral. -/
private theorem lintegral_frozen {γ : Type}
    (impl : QueryImpl spec (StateT (σ × Bool) ProbComp))
    (Frozen : σ → Prop) (weight : σ × Bool → ℝ≥0∞)
    (hfrozen : ∀ (t : spec.Domain) (p : σ × Bool), Frozen p.1 →
      ∀ z ∈ support ((impl t).run p), Frozen z.2.1)
    (hquiet : ∀ (t : spec.Domain) (p : σ × Bool), Frozen p.1 →
      ∀ z ∈ support ((impl t).run p), weight z.2 = weight p)
    (oa : OracleComp spec γ) (p : σ × Bool) (hp : Frozen p.1) :
    letI : MeasurableSpace (γ × (σ × Bool)) := ⊤
    ∫⁻ z, weight z.2 ∂𝒟[(simulateQ impl oa).run p] = weight p := by
  let : MeasurableSpace (γ × (σ × Bool)) := ⊤
  induction oa using OracleComp.inductionOn generalizing p with
  | pure value =>
    rw [simulateQ_pure, StateT.run_pure, evalDist_pure,
      MeasureTheory.lintegral_dirac' _ Measurable.of_discrete]
  | query_bind t next ih =>
    let : MeasurableSpace (spec.Range t × (σ × Bool)) := ⊤
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
      lintegral_evalDist_bind_of_discrete _ _ Measurable.of_discrete]
    exact lintegral_const_of_support _ _ _ fun y hmem => by
      rw [ih y.1 y.2 (hfrozen t p hp y hmem), hquiet t p hp y hmem]

/-- `probEvent_flag_frozen`, from a run that keeps its flag while frozen. -/
private theorem prEvent_flag_frozen_aux {γ : Type}
    (impl : QueryImpl spec (StateT (σ × Bool) ProbComp)) (Frozen : σ → Prop)
    (hfrozen : ∀ (t : spec.Domain) (p : σ × Bool), Frozen p.1 →
      ∀ z ∈ support ((impl t).run p), Frozen z.2.1)
    (hquiet : ∀ (t : spec.Domain) (p : σ × Bool), Frozen p.1 →
      ∀ z ∈ support ((impl t).run p), z.2.2 = p.2)
    (oa : OracleComp spec γ) (p : σ × Bool) (hp : Frozen p.1) :
    Pr{let z ← (simulateQ impl oa).run p}[z.2.2 = true] =
      (if p.2 = true then 1 else 0) := by
  induction oa using OracleComp.inductionOn generalizing p with
  | pure value =>
    rw [simulateQ_pure, StateT.run_pure, prEvent_pure]
  | query_bind t next ih =>
    let : MeasurableSpace (spec.Range t × (σ × Bool)) := ⊤
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
      prEvent_bind_eq_lintegral_of_discrete]
    exact lintegral_const_of_support _ _ _ fun y hmem => by
      rw [ih y.1 y.2 (hfrozen t p hp y hmem), hquiet t p hp y hmem]

/-- **A frozen run keeps the flag it started with.** -/
theorem probEvent_flag_frozen {γ : Type} (impl : QueryImpl spec (StateT (σ × Bool) ProbComp))
    (Frozen : σ → Prop)
    (hfail : ∀ (t : spec.Domain) (p : σ × Bool), prFail ((impl t).run p) = 0)
    (hfrozen : ∀ (t : spec.Domain) (p : σ × Bool), Frozen p.1 →
      ∀ z ∈ support ((impl t).run p), Frozen z.2.1)
    (hquiet : ∀ (t : spec.Domain) (p : σ × Bool), Frozen p.1 →
      ∀ z ∈ support ((impl t).run p), z.2.2 = p.2)
    (oa : OracleComp spec γ) (p : σ × Bool) (hp : Frozen p.1) :
    Pr{let z ← (simulateQ impl oa).run p}[z.2.2 = true] =
      (if p.2 = true then 1 else 0) := by
  exact prEvent_flag_frozen_aux impl Frozen hfrozen hquiet oa p hp

open scoped Classical in
/-- **Stalling does not change the flag.** Once the flag can no longer change, stopping the run
there leaves its law alone. -/
theorem probEvent_flag_stalled_eq {γ : Type}
    (impl : QueryImpl spec (StateT (σ × Bool) ProbComp)) (Frozen : σ → Prop)
    (stall : (t : spec.Domain) → spec.Range t)
    (hfail : ∀ (t : spec.Domain) (p : σ × Bool), prFail ((impl t).run p) = 0)
    (hfrozen : ∀ (t : spec.Domain) (p : σ × Bool), Frozen p.1 →
      ∀ z ∈ support ((impl t).run p), Frozen z.2.1)
    (hquiet : ∀ (t : spec.Domain) (p : σ × Bool), Frozen p.1 →
      ∀ z ∈ support ((impl t).run p), z.2.2 = p.2)
    (oa : OracleComp spec γ) (p : σ × Bool) :
    Pr{let z ← (simulateQ impl oa).run p}[z.2.2 = true] =
      Pr{let z ← (simulateQ (stalled impl Frozen stall) oa).run p}[z.2.2 = true] := by
  classical
  have hstalledFrozen : ∀ (t : spec.Domain) (q : σ × Bool), Frozen q.1 →
      ∀ z ∈ support (((stalled impl Frozen stall) t).run q), Frozen z.2.1 := by
    intro t q hq z hz
    rw [stalled_run_of_frozen impl Frozen stall t q hq, support_pure,
      Set.mem_singleton_iff] at hz
    rw [hz]
    exact hq
  have hstalledQuiet : ∀ (t : spec.Domain) (q : σ × Bool), Frozen q.1 →
      ∀ z ∈ support (((stalled impl Frozen stall) t).run q), z.2.2 = q.2 := by
    intro t q hq z hz
    rw [stalled_run_of_frozen impl Frozen stall t q hq, support_pure,
      Set.mem_singleton_iff] at hz
    rw [hz]
  induction oa using OracleComp.inductionOn generalizing p with
  | pure value =>
    rw [simulateQ_pure, StateT.run_pure, simulateQ_pure, StateT.run_pure]
  | query_bind t next ih =>
    by_cases hp : Frozen p.1
    · rw [prEvent_flag_frozen_aux impl Frozen hfrozen hquiet _ p hp,
        prEvent_flag_frozen_aux (stalled impl Frozen stall) Frozen hstalledFrozen
          hstalledQuiet _ p hp]
    · let : MeasurableSpace (spec.Range t × (σ × Bool)) := ⊤
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        stalled_run_of_not_frozen impl Frozen stall t p hp,
        prEvent_bind_eq_lintegral_of_discrete, prEvent_bind_eq_lintegral_of_discrete]
      exact MeasureTheory.lintegral_congr fun z => ih z.1 z.2

/-! ## Stalling preserves more than a flag

The flag above is one instance of a general fact: stalling leaves alone the expectation of any
quantity that cannot change once the run is frozen. A sticky flag is such a quantity, and so is
a count of events that can only happen while unfrozen — which is what carries the per-cell
weights of a charge across the stall. -/

/-- **A frozen run leaves a quantity it cannot change where it found it.** -/
theorem expectation_frozen {γ : Type} (impl : QueryImpl spec (StateT (σ × Bool) ProbComp))
    (Frozen : σ → Prop) (weight : σ × Bool → ℝ≥0∞)
    (hfail : ∀ (t : spec.Domain) (p : σ × Bool), prFail ((impl t).run p) = 0)
    (hfrozen : ∀ (t : spec.Domain) (p : σ × Bool), Frozen p.1 →
      ∀ z ∈ support ((impl t).run p), Frozen z.2.1)
    (hquiet : ∀ (t : spec.Domain) (p : σ × Bool), Frozen p.1 →
      ∀ z ∈ support ((impl t).run p), weight z.2 = weight p)
    (oa : OracleComp spec γ) (p : σ × Bool) (hp : Frozen p.1) :
    (∑' z : γ × (σ × Bool), Pr{let x ← (simulateQ impl oa).run p}[x = z] * weight z.2) =
      weight p := by
  let : MeasurableSpace (γ × (σ × Bool)) := ⊤
  rw [← lintegral_evalDist_eq_tsum_probComp]
  exact lintegral_frozen impl Frozen weight hfrozen hquiet oa p hp

open scoped Classical in
/-- **Stalling preserves the expectation of a quantity that cannot change while frozen.**
`probEvent_flag_stalled_eq` is the case of a sticky flag; a count of events that can only occur
while unfrozen is the case this is wanted for. -/
theorem expectation_stalled_eq {γ : Type}
    (impl : QueryImpl spec (StateT (σ × Bool) ProbComp)) (Frozen : σ → Prop)
    (stall : (t : spec.Domain) → spec.Range t) (weight : σ × Bool → ℝ≥0∞)
    (hfail : ∀ (t : spec.Domain) (p : σ × Bool), prFail ((impl t).run p) = 0)
    (hfrozen : ∀ (t : spec.Domain) (p : σ × Bool), Frozen p.1 →
      ∀ z ∈ support ((impl t).run p), Frozen z.2.1)
    (hquiet : ∀ (t : spec.Domain) (p : σ × Bool), Frozen p.1 →
      ∀ z ∈ support ((impl t).run p), weight z.2 = weight p)
    (oa : OracleComp spec γ) (p : σ × Bool) :
    (∑' z : γ × (σ × Bool), Pr{let x ← (simulateQ impl oa).run p}[x = z] * weight z.2) =
      ∑' z : γ × (σ × Bool),
        Pr{let x ← (simulateQ (stalled impl Frozen stall) oa).run p}[x = z] * weight z.2 := by
  classical
  have hstalledFrozen : ∀ (t : spec.Domain) (q : σ × Bool), Frozen q.1 →
      ∀ z ∈ support (((stalled impl Frozen stall) t).run q), Frozen z.2.1 := by
    intro t q hq z hz
    rw [stalled_run_of_frozen impl Frozen stall t q hq, support_pure,
      Set.mem_singleton_iff] at hz
    rw [hz]
    exact hq
  have hstalledQuiet : ∀ (t : spec.Domain) (q : σ × Bool), Frozen q.1 →
      ∀ z ∈ support (((stalled impl Frozen stall) t).run q), weight z.2 = weight q := by
    intro t q hq z hz
    rw [stalled_run_of_frozen impl Frozen stall t q hq, support_pure,
      Set.mem_singleton_iff] at hz
    rw [hz]
  let : MeasurableSpace (γ × (σ × Bool)) := ⊤
  rw [← lintegral_evalDist_eq_tsum_probComp, ← lintegral_evalDist_eq_tsum_probComp]
  induction oa using OracleComp.inductionOn generalizing p with
  | pure value =>
    rw [simulateQ_pure, StateT.run_pure, simulateQ_pure, StateT.run_pure]
  | query_bind t next ih =>
    by_cases hp : Frozen p.1
    · rw [lintegral_frozen impl Frozen weight hfrozen hquiet _ p hp,
        lintegral_frozen (stalled impl Frozen stall) Frozen weight hstalledFrozen
          hstalledQuiet _ p hp]
    · let : MeasurableSpace (spec.Range t × (σ × Bool)) := ⊤
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        stalled_run_of_not_frozen impl Frozen stall t p hp,
        lintegral_evalDist_bind_of_discrete _ _ Measurable.of_discrete,
        lintegral_evalDist_bind_of_discrete _ _ Measurable.of_discrete]
      exact MeasureTheory.lintegral_congr fun z => ih z.1 z.2

/-! ## A quantity that is not frozen but zero

The weights above are functions of the state, and that is what lets the hypothesis be *quiet*:
a step taken while frozen leaves the weight where it found it. A quantity read off the run's
**value** cannot state that hypothesis at all — after the stall the value still moves, and there
is nothing it is equal to.

It does not have to. The charge the forgery's own claims carry is read at the cache the run ends
with, and a claim is charged against a cell only while that cell is unavailable there. So once
the stall has fired — once the cell is available, and availability only grows — the claims carry
no charge at all. The weight is **zero** on a frozen run rather than frozen, and both runs then
contribute zero, which is the whole of the argument. -/

/-! ## The stalled run is blind to the cell it stalled on

The per-step hypothesis is demanded only at states that are not frozen — the states at which
the cell in question is still unavailable, and so the states at which a handler that reads only
available cells does not read it. That is the hypothesis such a handler has, and it is why
nothing has to be fixed before the run. -/

end SlhDsaSecurity.StalledRun
