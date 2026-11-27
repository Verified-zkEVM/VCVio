/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module
public import VCVio.OracleComp.QueryTracking.RandomOracle.DeferredSampling

/-!
# Simulating with partially observed tables

A stateful query handler can depend on an auxiliary table. If two tables induce the same
step law at every state, then they induce the same joint output and final-state law for
every computation.
-/

public section

open OracleComp OracleSpec ENNReal

namespace SLHDSA.SHAKE128s.TableBlind

/-! ## Lifting blindness from a step to a run -/

/-- Two computations of the same law with continuations of the same law bind to the same law. -/
theorem evalDist_bind_congr {α β : Type} {oa ob : ProbComp α} {f g : α → ProbComp β}
    (hlaw : oa =ᵈ ob) (hcont : ∀ a, f a =ᵈ g a) : oa >>= f =ᵈ ob >>= g :=
  hlaw.bind hcont

/-- **Blindness lifts from a step to a run.** If altering the table within `Agree` leaves every
step's law alone, it leaves the whole run's law alone. -/
theorem evalDist_run_congr_of_step {ι : Type} {spec : OracleSpec ι} {σ Table : Type}
    (impl : Table → QueryImpl spec (StateT σ ProbComp)) (Agree : Table → Table → Prop)
    (hstep : ∀ (t : spec.Domain) (s : σ) (left right : Table), Agree left right →
      (impl left t).run s =ᵈ (impl right t).run s)
    {γ : Type} (oa : OracleComp spec γ) (left right : Table) (hagree : Agree left right)
    (s : σ) :
    (simulateQ (impl left) oa).run s =ᵈ (simulateQ (impl right) oa).run s := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure value => simp only [simulateQ_pure, StateT.run_pure]; exact EvalDistEq.rfl
  | query_bind t next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    exact evalDist_bind_congr (hstep t s left right hagree) fun p => ih p.1 p.2

end SLHDSA.SHAKE128s.TableBlind
