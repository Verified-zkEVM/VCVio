/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.EvalDist.Defs.Measure.Core
public meta import Lean.PrettyPrinter.Formatter

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

public meta section Formatting

open Lean PrettyPrinter Formatter Syntax.MonadTraverser

/-- Format an event sequence directly after its opening delimiter, keeping the ordinary Lean
formatter for subsequent statements and explicitly braced sequences. Explicit line breaks
after the opening delimiter are preserved. -/
@[formatter prEvent]
def prEventFormatter : Formatter := do
  let stx ← getCur
  let multiline := match stx[0].getTailInfo with
    | .original _ _ trailing _ => trailing.contains '\n'
    | _ => false
  visitArgs do
    symbolNoAntiquot.formatter "]"
    categoryParser.formatter `term
    symbolNoAntiquot.formatter "}["
    let seq ← getCur
    if seq.isOfKind ``Lean.Parser.Term.doSeqIndent then
      let n := seq[0].getArgs.size
      visitArgs <| visitArgs do
        for i in [:n] do
          if i + 1 == n then
            visitArgs do
              optionalNoAntiquot.formatter (symbolNoAntiquot.formatter "; ")
              categoryParser.formatter `doElem
          else
            formatterForKind ``Lean.Parser.Term.doSeqItem
    else
      formatterForKind seq.getKind
    if multiline then
      pushWhitespace "\n"
    symbolNoAntiquot.formatter "Pr{"

end Formatting

macro_rules (kind := prEvent)
  -- `doSeqBracketed`
  | `(Pr{{$items*}}[$t]) => `(𝒟[do $items:doSeqItem* return $t:term] {True})
  -- `doSeqIndent`
  | `(Pr{$items*}[$t]) => `(𝒟[do $items:doSeqItem* return $t:term] {True})

/-- An event is the true mass of its propositional selector. -/
theorem prEvent_eq_evalDist_map
    {m : Type → Type v} [Monad m] [LawfulMonad m] [EvalDistSemantics m]
    {α : Type} (mx : m α) (p : α → Prop) :
    Pr{let x ← mx}[p x] = 𝒟[p <$> mx] {True} := by
  simp only [map_eq_bind_pure_comp, Function.comp_def]

/-- A measurable predicate returned by a computation has the probability of its event. -/
theorem prEvent_eq_evalDist {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α : Type} [MeasurableSpace α] (mx : m α) (p : α → Prop)
    (hp : Measurable p) :
    Pr{let x ← mx}[p x] = 𝒟[mx] {x | p x} := by
  rw [prEvent_eq_evalDist_map, evalDist_map mx hp,
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

/-- Equality to one output has its singleton mass whenever singletons are measurable. -/
theorem prEvent_eq_evalDist_singleton
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α : Type} [MeasurableSpace α] [MeasurableSingletonClass α] (mx : m α) (a : α) :
    Pr{let x ← mx}[x = a] = 𝒟[mx] {a} := by
  simpa only [Set.ofPred_eq_eq_singleton] using
    prEvent_eq_evalDist mx (fun x ↦ x = a) (measurableSet_singleton a).mem

/-- A final decidable event has the same success mass whether it is returned as a proposition
or decided to a Boolean; no measurable structure on intermediate values is needed. -/
theorem prEvent_eq_evalDist_decide
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α : Type} (mx : m α) (p : α → Prop) [DecidablePred p] :
    Pr{let x ← mx}[p x] = 𝒟[do let x ← mx; return decide (p x)] {true} := by
  classical
  calc
    _ = 𝒟[p <$> mx] {True} := prEvent_eq_evalDist_map mx p
    _ = 𝒟[(fun b : Prop ↦ decide b) <$> (p <$> mx)] {true} := by
      rw [evalDist_map (p <$> mx)
        (Measurable.of_discrete : Measurable fun b : Prop ↦ decide b),
        Measure.map_apply Measurable.of_discrete (measurableSet_singleton true)]
      congr 1
      ext b
      simp
    _ = _ := by
      congr 1
      congr 1
      simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
      apply bind_congr
      intro x
      by_cases hx : p x <;> simp [hx]

/-- Pointwise equivalent predicates have the same probability after a common computation. -/
theorem prEvent_congr
    {m : Type → Type v} [Monad m] [EvalDistSemantics m]
    {α : Type} (mx : m α) (p q : α → Prop) (h : ∀ x, p x ↔ q x) :
    Pr{let x ← mx}[p x] = Pr{let x ← mx}[q x] := by
  have hpq : p = q := funext fun x ↦ propext (h x)
  rw [hpq]

/-- Measurable predicates agreeing almost everywhere have equal event probabilities. -/
theorem prEvent_congr_ae
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α : Type} [MeasurableSpace α] (mx : m α) (p q : α → Prop)
    (hp : Measurable p) (hq : Measurable q) (h : ∀ᵐ x ∂𝒟[mx], p x ↔ q x) :
    Pr{let x ← mx}[p x] = Pr{let x ← mx}[q x] := by
  rw [prEvent_eq_evalDist mx p hp, prEvent_eq_evalDist mx q hq]
  exact measure_congr (h.mono fun _ hx ↦ propext hx)

/-- An event that never occurs has probability zero. -/
theorem prEvent_eq_zero_of_forall_not
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α : Type} (mx : m α) (p : α → Prop) (h : ∀ x, ¬p x) :
    Pr{let x ← mx}[p x] = 0 := by
  have hp : p = fun _ ↦ False := funext fun x ↦ propext (iff_false_intro (h x))
  calc
    _ = Pr{let _ ← p <$> mx}[False] := by
      rw [hp]
      simp only [bind_map_left]
    _ = 0 := by
      rw [prEvent_eq_evalDist_of_discrete]
      simp

/-- Almost-everywhere implication bounds probabilities of measurable events. -/
theorem prEvent_mono_ae
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α : Type} [MeasurableSpace α] (mx : m α) (p q : α → Prop)
    (hp : Measurable p) (hq : Measurable q) (hpq : ∀ᵐ x ∂𝒟[mx], p x → q x) :
    Pr{let x ← mx}[p x] ≤ Pr{let x ← mx}[q x] := by
  rw [prEvent_eq_evalDist mx p hp, prEvent_eq_evalDist mx q hq]
  exact measure_mono_ae hpq

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
  let obs : α → Prop × Prop := fun x ↦ (p x, q x)
  let : MeasurableSpace α := MeasurableSpace.comap obs inferInstance
  have hobs : Measurable obs := comap_measurable obs
  exact prEvent_mono_ae mx p q (measurable_fst.comp hobs) (measurable_snd.comp hobs)
    (Filter.Eventually.of_forall hpq)

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

/-- AE equality of measurable observed continuation probabilities gives equality after a draw. -/
theorem prEvent_bind_congr_ae
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α β γ : Type} [MeasurableSpace α] (mx : m α) (f : α → m β) (g : α → m γ)
    (p : β → Prop) (q : γ → Prop)
    (hf : Measurable fun x ↦ 𝒟[do let y ← f x; return p y])
    (hg : Measurable fun x ↦ 𝒟[do let z ← g x; return q z])
    (h : ∀ᵐ x ∂𝒟[mx], Pr{let y ← f x}[p y] = Pr{let z ← g x}[q z]) :
    Pr{let y ← mx >>= f}[p y] = Pr{let z ← mx >>= g}[q z] := by
  rw [prEvent_bind_eq_lintegral mx f p hf, prEvent_bind_eq_lintegral mx g q hg]
  exact lintegral_congr_ae h

/-- Pointwise equality of observed continuation probabilities gives equality after a common
draw. Neither the draw nor the continuation outputs need a measurable-space argument. -/
theorem prEvent_bind_congr
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α β γ : Type} (mx : m α) (f : α → m β) (g : α → m γ)
    (p : β → Prop) (q : γ → Prop)
    (h : ∀ x,
      Pr{let y ← f x}[p y] = Pr{let z ← g x}[q z]) :
    Pr{let y ← mx >>= f}[p y] = Pr{let z ← mx >>= g}[q z] := by
  let obs : α → Measure Prop × Measure Prop := fun x ↦
    (𝒟[do let y ← f x; return p y], 𝒟[do let z ← g x; return q z])
  let : MeasurableSpace α := MeasurableSpace.comap obs inferInstance
  have hobs : Measurable obs := comap_measurable obs
  exact prEvent_bind_congr_ae mx f g p q (measurable_fst.comp hobs)
    (measurable_snd.comp hobs) (Filter.Eventually.of_forall h)

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
