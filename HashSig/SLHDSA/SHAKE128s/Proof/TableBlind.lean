/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.SensitiveQuery
public import VCVio.OracleComp.QueryTracking.RandomOracle.DeferredSampling

/-!
# A run that reads only part of the table is blind to the rest

This file supplies the lifting that turns a *per-step* blindness statement into a run-level one.
A handler is parameterised by the table it may read; `evalDist_run_congr_of_step` says that if
each step's law is unchanged by altering the table within an equivalence `Agree`, so is the
whole run's, hence so is any event about its record. The per-step hypothesis is where the graph
enters: a query at a node all of whose children's cells are available is answered by that node's
own cell, which `CanonicalGraph.available_of_children_available` says is available too, so the
answer is a function of the available cells alone.

The lifting applies to a presentation in which the handler reads the table, which is the lazy
one. In a presentation where the table enters through the *initial cache* instead, the
dependence is in the state rather than in the handler, and the lifting says nothing: two caches
built from tables that differ are told apart by a single query at a canonical input where they
differ, so no run-level congruence holds.

It does not cover a set of unavailable cells that shrinks as signatures are issued: the lifting
is not indexed by prefixes of the run.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace SlhDsaSecurity.TableBlind

open SensitiveQuery

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

variable {Node Index State : Type} [Fintype Index] [DecidableEq Index]

end SlhDsaSecurity.TableBlind
