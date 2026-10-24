/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.ProgramLogic.Library.T1.Lifts
public import VCVio.OracleComp.ProbComp.Basic

/-!
# Tests for the bridges between triples, supports and probabilities
-/

public section

open OracleSpec OracleComp Std.WP OracleComp.ProgramLogic

open scoped OracleComp.Necessary

set_option experimental.vcgen true

namespace BridgesTest

variable {ι : Type} {spec : OracleSpec.{0, 0} ι} {σ α : Type}

/-- The outputs of a simulated run are outputs of the program, with probability one. -/
example (impl : QueryImpl spec (StateT σ ProbComp)) (oa : OracleComp spec α) (s : σ) :
    Pr{let a ← (simulateQ impl oa).run' s}[a ∈ support oa] = 1 :=
  prEvent_run'_eq_one_of_triple <| (triple_stateT_iff_forall_mem_support _ _ _ _).2
    fun _ _ _ _ hz ↦ fst_mem_support_of_mem_support_simulateQ_run impl hz

/-- An output outside the program's support is impossible after any simulation. -/
example (impl : QueryImpl spec (StateT σ ProbComp)) (oa : OracleComp spec α) (s : σ) (x : α)
    (hx : x ∉ support oa) : Pr{let a ← (simulateQ impl oa).run' s}[a = x] = 0 :=
  prEvent_run'_eq_zero_of_triple <| (triple_stateT_iff_forall_mem_support _ _ _ _).2
    fun _ _ _ _ hz h ↦ hx (h ▸ fst_mem_support_of_mem_support_simulateQ_run impl hz)

/-- Under uniform answers, a certain event after `run' s` is a triple from `s`, which composes
with a later step. -/
example (impl : QueryImpl spec (StateT σ ProbComp)) (oa : OracleComp spec ℕ) (s : σ)
    (h : Pr{let n ← (simulateQ impl oa).run' s}[0 < n] = 1) :
    ⦃ fun s' ↦ s' = s ⦄ simulateQ impl (do let n ← oa; pure (n + 1)) ⦃ fun n _ ↦ 1 < n ⦄ := by
  have hoa := (prEvent_run'_eq_one_iff_triple _ s _).1 h
  vcgen [hoa] with finish

/-- A triple over the full run reads as a certain event on output and final state. -/
example [Preorder σ] (impl : QueryImpl spec (StateT σ ProbComp))
    (hstep : ∀ t s, ∀ z ∈ support ((impl t).run s), s ≤ z.2) (oa : OracleComp spec α) (s : σ) :
    Pr{let z ← (simulateQ impl oa).run s}[s ≤ z.2] = 1 :=
  (prEvent_run_eq_one_iff_triple _ s fun _ s' ↦ s ≤ s').2 <|
    (triple_stateT_iff_forall_mem_support _ _ _ _).2 fun _ hs _ _ hz ↦
      hs ▸ le_of_mem_support_simulateQ_run hstep hz

/-- The output-only reading of a triple. -/
example (impl : QueryImpl spec (StateT σ (OracleComp spec))) (oa : OracleComp spec α)
    (P : σ → Prop) (Q : α → Prop) (h : ⦃ fun s ↦ P s ⦄ simulateQ impl oa ⦃ fun a _ ↦ Q a ⦄)
    (s : σ) (hs : P s) : ∀ a ∈ support ((simulateQ impl oa).run' s), Q a :=
  (triple_stateT_iff_forall_mem_support_run' _ _ _ _).1 h s hs

/-- A stateless simulation: a triple proved by `vcgen` makes its postcondition a certain event. -/
example (impl : QueryImpl spec ProbComp) (hh : ∀ t, ⦃ True ⦄ impl t ⦃ fun _ ↦ True ⦄)
    (t : spec.Domain) (f : spec.Range t → α) :
    Pr{let a ← simulateQ impl (do let u ← query t; pure (f u))}[a ∈ Set.range f] = 1 :=
  prEvent_eq_one_of_triple (by vcgen [hh] with finish)


end BridgesTest
