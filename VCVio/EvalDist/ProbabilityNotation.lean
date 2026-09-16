/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.EvalDist.Defs.Measure.Core

/-!
# Measure events for computation notation

`Pr{...}[...]` interprets an ordinary Lean `do` computation as the successful-output
measure of its Boolean or propositional result. These equations identify that measure
with an event in the underlying computation when the event is measurable.
-/

public section

open MeasureTheory

universe v

/-- Probability of a successful event after an ordinary Lean `do` sequence.
The event is interpreted by the primary measure semantics. -/
syntax (name := prEvent) "Pr{" doSeq "}[" term "]" : term

macro_rules (kind := prEvent)
  -- `doSeqBracketed`
  | `(Pr{{$items*}}[$t]) => `(𝒟[do $items:doSeqItem* return $t:term] {True})
  -- `doSeqIndent`
  | `(Pr{$items*}[$t]) => `(𝒟[do $items:doSeqItem* return $t:term] {True})

/-- A measurable predicate returned by a computation has the probability of its event. -/
theorem prEvent_eq_evalDist {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α : Type} [MeasurableSpace α] (mx : m α) (p : α → Prop)
    (hp : Measurable p) :
    Pr{let x ← mx}[p x] = 𝒟[mx] {x | p x} := by
  change 𝒟[mx >>= (pure ∘ p)] {True} = _
  rw [← map_eq_bind_pure_comp, evalDist_map mx hp,
    Measure.map_apply hp (measurableSet_singleton True)]
  simp

/-- On a discrete output space every predicate is a measurable event. -/
theorem prEvent_eq_evalDist_of_discrete
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α : Type} [MeasurableSpace α] [DiscreteMeasurableSpace α]
    (mx : m α) (p : α → Prop) :
    Pr{let x ← mx}[p x] = 𝒟[mx] {x | p x} :=
  prEvent_eq_evalDist mx p Measurable.of_discrete

/-- Checking a decidable event at the end of a computation gives the same success mass as
returning its decision as a Boolean. -/
theorem prEvent_eq_evalDist_decide_of_discrete
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α : Type} [MeasurableSpace α] [DiscreteMeasurableSpace α]
    (mx : m α) (p : α → Prop) [DecidablePred p] :
    Pr{let x ← mx}[p x] = 𝒟[do let x ← mx; return decide (p x)] {true} := by
  rw [prEvent_eq_evalDist_of_discrete]
  change 𝒟[mx] {x | p x} =
    𝒟[mx >>= (pure ∘ fun x => decide (p x))] {true}
  rw [← map_eq_bind_pure_comp,
    evalDist_map mx (Measurable.of_discrete : Measurable fun x => decide (p x)),
    Measure.map_apply (Measurable.of_discrete : Measurable fun x => decide (p x))
      (measurableSet_singleton true)]
  congr 1
  ext x
  simp

/-- A final decidable event has the same success mass whether it is returned as a proposition
or decided to a Boolean; no measurable structure on intermediate values is needed. -/
theorem prEvent_eq_evalDist_decide
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α : Type} (mx : m α) (p : α → Prop) [DecidablePred p] :
    Pr{let x ← mx}[p x] = 𝒟[do let x ← mx; return decide (p x)] {true} := by
  let : MeasurableSpace α := ⊤
  exact prEvent_eq_evalDist_decide_of_discrete mx p

/-- Pointwise equivalent predicates have the same probability after a common computation. -/
theorem prEvent_congr
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α : Type} (mx : m α) (p q : α → Prop) (h : ∀ x, p x ↔ q x) :
    Pr{let x ← mx}[p x] = Pr{let x ← mx}[q x] := by
  let : MeasurableSpace α := ⊤
  rw [prEvent_eq_evalDist_of_discrete, prEvent_eq_evalDist_of_discrete]
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq, h x]

/-- An event that never occurs has probability zero. -/
theorem prEvent_eq_zero_of_forall_not
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α : Type} (mx : m α) (p : α → Prop) (h : ∀ x, ¬p x) :
    Pr{let x ← mx}[p x] = 0 := by
  let : MeasurableSpace α := ⊤
  rw [prEvent_eq_evalDist_of_discrete]
  have hp : {x : α | p x} = ∅ := by
    ext x
    simp [h x]
  rw [hp, measure_empty]

/-- Implication between events bounds their probabilities on a discrete output space. -/
theorem prEvent_mono_of_discrete
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α : Type} [MeasurableSpace α] [DiscreteMeasurableSpace α]
    (mx : m α) (p q : α → Prop) (hpq : ∀ x, p x → q x) :
    Pr{let x ← mx}[p x] ≤ Pr{let x ← mx}[q x] := by
  rw [prEvent_eq_evalDist_of_discrete,
    prEvent_eq_evalDist_of_discrete]
  exact measure_mono (Set.ofPred_subset_ofPred.mpr hpq)

/-- Implication between final events bounds their probabilities without a measurable-space
argument on the intermediate values. -/
theorem prEvent_mono
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α : Type} (mx : m α) (p q : α → Prop) (hpq : ∀ x, p x → q x) :
    Pr{let x ← mx}[p x] ≤ Pr{let x ← mx}[q x] := by
  let : MeasurableSpace α := ⊤
  exact prEvent_mono_of_discrete mx p q hpq

/-- An observed bind integrates the event probability of each measurable continuation.
Only the common draw needs a selected measurable space; the continuation is observed in `Prop`.
-/
theorem prEvent_bind_eq_lintegral
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α β : Type} [MeasurableSpace α] (mx : m α) (f : α → m β) (p : β → Prop)
    (hf : Measurable fun x ↦ 𝒟[do let y ← f x; return p y]) :
    Pr{let y ← mx >>= f}[p y] = ∫⁻ x, Pr{let y ← f x}[p y] ∂𝒟[mx] := by
  rw [bind_assoc, evalDist_bind _ _ hf,
    Measure.bind_apply (measurableSet_singleton True) hf.aemeasurable]

/-- A discrete common draw discharges the observed continuation's measurability. -/
theorem prEvent_bind_eq_lintegral_of_discrete
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α β : Type} [MeasurableSpace α] [DiscreteMeasurableSpace α]
    (mx : m α) (f : α → m β) (p : β → Prop) :
    Pr{let y ← mx >>= f}[p y] = ∫⁻ x, Pr{let y ← f x}[p y] ∂𝒟[mx] :=
  prEvent_bind_eq_lintegral mx f p Measurable.of_discrete

/-- Pointwise equality of observed continuation probabilities gives equality after a common
draw. Neither the draw nor the continuation outputs need a measurable-space argument. -/
theorem prEvent_bind_congr
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α β γ : Type} (mx : m α) (f : α → m β) (g : α → m γ)
    (p : β → Prop) (q : γ → Prop)
    (h : ∀ x,
      Pr{ let y ← f x}[p y] = Pr{ let z ← g x}[q z]) :
    Pr{let y ← mx >>= f}[p y] = Pr{let z ← mx >>= g}[q z] := by
  let : MeasurableSpace α := ⊤
  rw [prEvent_bind_eq_lintegral_of_discrete, prEvent_bind_eq_lintegral_of_discrete]
  exact lintegral_congr h

/-- An output map composes the final event with that map. -/
@[grind norm]
theorem prEvent_map
    {m : Type → Type v} [Monad m] [LawfulMonad m] [EvalDistSemantics m]
    {α β : Type} (mx : m α) (f : α → β) (p : β → Prop) :
    Pr{let y ← f <$> mx}[p y] = Pr{let x ← mx}[p (f x)] := by
  rw [bind_map_left]

/-- Events of independent draws have the product of their probabilities. -/
@[simp↓ high, grind norm↓]
theorem prEvent_bind_bind_and
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α β : Type} (mx : m α) (my : m β) (p : α → Prop) (q : β → Prop) :
    Pr{let x ← mx; let y ← my}[p x ∧ q y] =
      Pr{let x ← mx}[p x] * Pr{let y ← my}[q y] := by
  calc
    _ = Pr{let z ← (do
          let x ← p <$> mx
          let y ← q <$> my
          return (x, y))}[z.1 ∧ z.2] := by
      simp only [bind_assoc, pure_bind, bind_map_left]
    _ = (𝒟[p <$> mx].prod 𝒟[q <$> my]) ({True} ×ˢ {True}) := by
      rw [prEvent_eq_evalDist_of_discrete, evalDist_pair]
      congr 1
      ext z
      simp [Prod.ext_iff, eq_iff_iff]
    _ = _ := by
      rw [Measure.prod_prod]
      simp only [map_eq_bind_pure_comp, Function.comp_def]
