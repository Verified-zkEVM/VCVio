/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Control.Monad.WriterT.WP
public import VCVio.OracleComp.EvalDist.Measure
public import VCVio.ProgramLogic.Library.T1.Support
public import VCVio.ProgramLogic.Unary.WP.Necessary

/-!
# Bridges between necessary triples, supports and probabilities

Under the necessary reading (`open scoped OracleComp.Necessary`), a core triple over
`OracleComp spec'` is a statement about the support, and so is a triple over a `StateT` or
`WriterT` layer on top of it. This file states these readings for arbitrary universes, for the
run and for the output-only `run'` of a stateful computation, and connects them to event
probabilities: a triple with a true precondition makes an event of an `OracleComp` certain
(`= 1`) or impossible (`= 0`), a triple from the starting state `s` does the same after
`run' s`, and the converses hold under uniform answer measures.

The statements are about arbitrary computations `mx : StateT σ (OracleComp spec') α`; for a
simulated program take `mx := simulateQ impl oa`.
-/

public section

open OracleSpec OracleComp Std.WP

open scoped OracleComp.Necessary

universe u' v' w

namespace OracleComp.ProgramLogic

variable {ι' : Type u'} {spec' : OracleSpec.{u', v'} ι'}

/-! ## Triples and supports -/

/-- A necessary triple over `OracleComp` holds when, under the precondition, every possible
output satisfies the postcondition. -/
theorem triple_iff_forall_mem_support {α : Type w} (oa : OracleComp spec' α) (P : Prop)
    (Q : α → Prop) (epost : EStack⟨⟩) :
    Triple oa P Q epost ↔ (P → ∀ a ∈ support oa, Q a) :=
  Triple.iff

/-- A necessary `StateT` triple over `OracleComp` constrains every value-state pair that the run
reaches from a state satisfying the precondition. -/
theorem triple_stateT_iff_forall_mem_support {σ α : Type w}
    (mx : StateT σ (OracleComp spec') α) (P : σ → Prop) (Q : α → σ → Prop) (epost : EStack⟨⟩) :
    Triple mx P Q epost ↔ ∀ s, P s → ∀ a s', (a, s') ∈ support (mx.run s) → Q a s' :=
  Triple.iff.trans <| forall_congr' fun _ ↦ imp_congr_right fun _ ↦
    ⟨fun h a s' ↦ h (a, s'), fun h p ↦ h p.1 p.2⟩

/-- A necessary `StateT` triple whose postcondition ignores the final state constrains every
output of `run'` from a state satisfying the precondition. -/
theorem triple_stateT_iff_forall_mem_support_run' {σ α : Type w}
    (mx : StateT σ (OracleComp spec') α) (P : σ → Prop) (Q : α → Prop) (epost : EStack⟨⟩) :
    Triple mx P (fun a _ ↦ Q a) epost ↔ ∀ s, P s → ∀ a ∈ support (mx.run' s), Q a := by
  simp only [triple_stateT_iff_forall_mem_support, StateT.run'_eq, support_map, Set.mem_image,
    Prod.exists, exists_and_right, exists_eq_right, forall_exists_index]

section writerT

variable {ω α : Type w}

open scoped WriterT.MonoidWP in
/-- A monoid-log `WriterT` triple over `OracleComp`, read by `WriterT.MonoidWP`, constrains every
reachable value with the incoming log multiplied by the written one. -/
theorem triple_writerT_iff_forall_mem_support [Monoid ω] (mx : WriterT ω (OracleComp spec') α)
    (P : ω → Prop) (Q : α → ω → Prop) (epost : EStack⟨⟩) :
    Triple mx P Q epost ↔ ∀ w, P w → ∀ a w', (a, w') ∈ support mx.run → Q a (w * w') :=
  Triple.iff.trans <| forall_congr' fun _ ↦ imp_congr_right fun _ ↦
    ⟨fun h a w' ↦ h (a, w'), fun h p ↦ h p.1 p.2⟩

open scoped WriterT.AppendWP in
/-- An append-log `WriterT` triple over `OracleComp`, read by `WriterT.AppendWP`, constrains
every reachable value with the incoming log extended by the written one. -/
theorem triple_writerT_iff_forall_mem_support_append [EmptyCollection ω] [Append ω]
    [LawfulAppend ω] (mx : WriterT ω (OracleComp spec') α) (P : ω → Prop) (Q : α → ω → Prop)
    (epost : EStack⟨⟩) :
    Triple mx P Q epost ↔ ∀ w, P w → ∀ a w', (a, w') ∈ support mx.run → Q a (w ++ w') :=
  Triple.iff.trans <| forall_congr' fun _ ↦ imp_congr_right fun _ ↦
    ⟨fun h a w' ↦ h (a, w'), fun h p ↦ h p.1 p.2⟩

end writerT

/-! ## Triples and event probabilities -/

section prob

variable {ι' : Type u'} {spec' : OracleSpec.{u', 0} ι'} {σ α : Type}

/-- A necessary triple over `OracleComp` with a true precondition makes its postcondition a
certain event. -/
theorem prEvent_eq_one_of_triple [AnswerMeasure spec'] {oa : OracleComp spec' α}
    {p : α → Prop} (h : ⦃ True ⦄ oa ⦃ fun a ↦ p a ⦄) : Pr{let a ← oa}[p a] = 1 :=
  prEvent_eq_one_of_forall_mem_support oa p ((triple_iff_forall_mem_support oa _ _ _).1 h trivial)

/-- A necessary triple over `OracleComp` with a true precondition refuting an event makes the
event impossible. -/
theorem prEvent_eq_zero_of_triple [AnswerMeasure spec'] {oa : OracleComp spec' α}
    {p : α → Prop} (h : ⦃ True ⦄ oa ⦃ fun a ↦ ¬p a ⦄) : Pr{let a ← oa}[p a] = 0 :=
  prEvent_eq_zero_of_forall_mem_support oa p
    ((triple_iff_forall_mem_support oa _ _ _).1 h trivial)

/-- A triple from the starting state `s` whose postcondition is an event on the output makes the
event certain after `run' s`. -/
theorem prEvent_run'_eq_one_of_triple [AnswerMeasure spec'] {mx : StateT σ (OracleComp spec') α}
    {s : σ} {p : α → Prop} (h : ⦃ fun s' ↦ s' = s ⦄ mx ⦃ fun a _ ↦ p a ⦄) :
    Pr{let a ← mx.run' s}[p a] = 1 :=
  prEvent_eq_one_of_forall_mem_support _ p
    ((triple_stateT_iff_forall_mem_support_run' mx _ p _).1 h s rfl)

/-- A triple from the starting state `s` whose postcondition refutes an event on the output makes
the event impossible after `run' s`. -/
theorem prEvent_run'_eq_zero_of_triple [AnswerMeasure spec'] {mx : StateT σ (OracleComp spec') α}
    {s : σ} {p : α → Prop} (h : ⦃ fun s' ↦ s' = s ⦄ mx ⦃ fun a _ ↦ ¬p a ⦄) :
    Pr{let a ← mx.run' s}[p a] = 0 :=
  prEvent_eq_zero_of_forall_mem_support _ p
    ((triple_stateT_iff_forall_mem_support_run' mx _ (¬p ·) _).1 h s rfl)

/-- Under uniform answer measures, an event on the output is certain after `run' s` exactly when
a triple from `s` establishes it. -/
theorem prEvent_run'_eq_one_iff_triple [UniformAnswerMeasure spec']
    (mx : StateT σ (OracleComp spec') α) (s : σ) (p : α → Prop) :
    Pr{let a ← mx.run' s}[p a] = 1 ↔ ⦃ fun s' ↦ s' = s ⦄ mx ⦃ fun a _ ↦ p a ⦄ := by
  rw [prEvent_eq_one_iff, triple_stateT_iff_forall_mem_support_run']
  exact ⟨fun h _ hs ↦ hs ▸ h, fun h ↦ h s rfl⟩

/-- Under uniform answer measures, an event on the output is impossible after `run' s` exactly
when a triple from `s` refutes it. -/
theorem prEvent_run'_eq_zero_iff_triple [UniformAnswerMeasure spec']
    (mx : StateT σ (OracleComp spec') α) (s : σ) (p : α → Prop) :
    Pr{let a ← mx.run' s}[p a] = 0 ↔ ⦃ fun s' ↦ s' = s ⦄ mx ⦃ fun a _ ↦ ¬p a ⦄ := by
  rw [prEvent_eq_zero_iff, triple_stateT_iff_forall_mem_support_run']
  exact ⟨fun h _ hs ↦ hs ▸ h, fun h ↦ h s rfl⟩

/-- Under uniform answer measures, an event on the output and the final state is certain after
`run s` exactly when a triple from `s` establishes it. -/
theorem prEvent_run_eq_one_iff_triple [UniformAnswerMeasure spec']
    (mx : StateT σ (OracleComp spec') α) (s : σ) (p : α → σ → Prop) :
    Pr{let z ← mx.run s}[p z.1 z.2] = 1 ↔ ⦃ fun s' ↦ s' = s ⦄ mx ⦃ p ⦄ := by
  rw [prEvent_eq_one_iff, triple_stateT_iff_forall_mem_support]
  exact ⟨fun h _ hs a s' hz ↦ h (a, s') (hs ▸ hz), fun h z hz ↦ h s rfl z.1 z.2 hz⟩

end prob

end OracleComp.ProgramLogic
