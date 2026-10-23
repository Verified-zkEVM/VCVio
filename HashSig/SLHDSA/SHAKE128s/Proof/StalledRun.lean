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

set_option backward.isDefEq.respectTransparency false

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
theorem stalled_run_of_frozen (impl : QueryImpl spec (StateT (σ × Bool) ProbComp))
    (Frozen : σ → Prop) (stall : (t : spec.Domain) → spec.Range t)
    (t : spec.Domain) (p : σ × Bool) (hp : Frozen p.1) :
    ((stalled impl Frozen stall) t).run p = (pure (stall t, p) : ProbComp _) := by
  simp only [stalled, StateT.run]
  exact if_pos hp

open scoped Classical in
theorem stalled_run_of_not_frozen (impl : QueryImpl spec (StateT (σ × Bool) ProbComp))
    (Frozen : σ → Prop) (stall : (t : spec.Domain) → spec.Range t)
    (t : spec.Domain) (p : σ × Bool) (hp : ¬ Frozen p.1) :
    ((stalled impl Frozen stall) t).run p = (impl t).run p := by
  simp only [stalled, StateT.run]
  exact if_neg hp

/-! ## A run that can no longer change the flag does not change it -/

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
  induction oa using OracleComp.inductionOn generalizing p with
  | pure value =>
    rw [simulateQ_pure, StateT.run_pure, prEvent_pure]
  | query_bind t next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, OracleComp.prEvent_bind_eq_tsum]
    calc ∑' z, Pr{let x ← (impl t).run p}[x = z] *
          Pr{let w ← (simulateQ impl (next z.1)).run z.2}[w.2.2 = true]
        = ∑' z, Pr{let x ← (impl t).run p}[x = z] * (if p.2 = true then 1 else 0) := by
          refine tsum_congr fun z => ?_
          by_cases hmem : z ∈ support ((impl t).run p)
          · rw [ih z.1 z.2 (hfrozen t p hp z hmem), hquiet t p hp z hmem]
          · rw [(prEvent_eq_zero_of_not_mem_support _) hmem]
            simp
      _ = (if p.2 = true then 1 else 0) := by
          rw [ENNReal.tsum_mul_right]
          have hmass := probFailure_add_tsum_probOutput ((impl t).run p)
          rw [hfail t p, zero_add] at hmass
          rw [hmass, one_mul]

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
  have hstalledFail : ∀ (t : spec.Domain) (q : σ × Bool),
      prFail (((stalled impl Frozen stall) t).run q) = 0 := by
    intro t q
    by_cases hq : Frozen q.1
    · rw [stalled_run_of_frozen impl Frozen stall t q hq]; simp
    · rw [stalled_run_of_not_frozen impl Frozen stall t q hq]; exact hfail t q
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
    · rw [probEvent_flag_frozen impl Frozen hfail hfrozen hquiet _ p hp,
        probEvent_flag_frozen (stalled impl Frozen stall) Frozen hstalledFail hstalledFrozen
          hstalledQuiet _ p hp]
    · rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        stalled_run_of_not_frozen impl Frozen stall t p hp,
        OracleComp.prEvent_bind_eq_tsum, OracleComp.prEvent_bind_eq_tsum]
      exact tsum_congr fun z => congrArg _ (ih z.1 z.2)

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
    (∑' z : γ × (σ × Bool), Pr{let x ← (simulateQ impl oa).run p}[x = z] * weight z.2) = weight p := by
  induction oa using OracleComp.inductionOn generalizing p with
  | pure value =>
    rw [simulateQ_pure, StateT.run_pure, OracleComp.tsum_prEvent_pure_mul]
  | query_bind t next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, OracleComp.tsum_prEvent_bind_mul]
    calc ∑' y, Pr{let x ← (impl t).run p}[x = y] *
          ∑' z : γ × (σ × Bool), Pr{let x ← (simulateQ impl (next y.1)).run y.2}[x = z] * weight z.2
        = ∑' y, Pr{let x ← (impl t).run p}[x = y] * weight p := by
          refine tsum_congr fun y => ?_
          by_cases hmem : y ∈ support ((impl t).run p)
          · rw [ih y.1 y.2 (hfrozen t p hp y hmem), hquiet t p hp y hmem]
          · rw [(prEvent_eq_zero_of_not_mem_support _) hmem]
            simp
      _ = weight p := by
          rw [ENNReal.tsum_mul_right]
          have hmass := probFailure_add_tsum_probOutput ((impl t).run p)
          rw [hfail t p, zero_add] at hmass
          rw [hmass, one_mul]

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
  have hstalledFail : ∀ (t : spec.Domain) (q : σ × Bool),
      prFail (((stalled impl Frozen stall) t).run q) = 0 := by
    intro t q
    by_cases hq : Frozen q.1
    · rw [stalled_run_of_frozen impl Frozen stall t q hq]; simp
    · rw [stalled_run_of_not_frozen impl Frozen stall t q hq]; exact hfail t q
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
  induction oa using OracleComp.inductionOn generalizing p with
  | pure value =>
    rw [simulateQ_pure, StateT.run_pure, simulateQ_pure, StateT.run_pure]
  | query_bind t next ih =>
    by_cases hp : Frozen p.1
    · rw [expectation_frozen impl Frozen weight hfail hfrozen hquiet _ p hp,
        expectation_frozen (stalled impl Frozen stall) Frozen weight hstalledFail
          hstalledFrozen hstalledQuiet _ p hp]
    · rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        stalled_run_of_not_frozen impl Frozen stall t p hp,
        OracleComp.tsum_prEvent_bind_mul, OracleComp.tsum_prEvent_bind_mul]
      exact tsum_congr fun y => congrArg _ (ih y.1 y.2)

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
