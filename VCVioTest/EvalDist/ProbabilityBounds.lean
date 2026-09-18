/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.OracleComp.Constructions.Fork.Basic
public import ToMathlib.Probability.Kernel.Quadratic

/-!
# Native event probability bounds

These checks exercise conditional-square and selector-partition bounds without a discrete
probability backend, measurable structures on intermediate values, or uniform answer measures.
They also check that event maps and independent conjunctions normalize with `simp` and `grind`.
Occurrence answer marginals and collision bounds infer their mass properties and need no
measurable structures on completion records or main outputs.
-/

public section

open MeasureTheory ProbabilityTheory OracleSpec

run_cmd do
  let env ← Lean.getEnv
  for name in [`PMF, `SPMF] do
    if env.contains name then
      throwError "native probability bounds unexpectedly import {name}"

run_cmd do
  let one ← `(Pr{let x ← (pure 1 : Option Nat)}[x = 1])
  let many ← `(Pr{let x ← (pure 1 : Option Nat); let y ← pure (x + 1)}[y = 2])
  let spaced ← `(Pr{ let x ← (pure 1 : Option Nat)}[x = 1])
  for stx in #[one, many, spaced] do
    let fmt ← Lean.Elab.Command.liftCoreM (Lean.PrettyPrinter.ppTerm stx)
    unless fmt.pretty.startsWith "Pr{let " do
      throwError "unexpected event delimiter formatting: {fmt}"
  let .ok multiline := Lean.Parser.runParserCategory (← Lean.getEnv) `term
      "Pr{\n  let x ← (pure 1 : Option Nat)}[x = 1]"
    | throwError "multiline probability notation did not parse"
  let fmt ← Lean.Elab.Command.liftCoreM (Lean.PrettyPrinter.ppTerm ⟨multiline⟩)
  unless fmt.pretty.startsWith "Pr{\n" do
    throwError "unexpected multiline event formatting: {fmt}"
  let braced ← `(Pr{{let x ← (pure 1 : Option Nat)}}[x = 1])
  let fmt ← Lean.Elab.Command.liftCoreM (Lean.PrettyPrinter.ppTerm braced)
  unless fmt.pretty.startsWith "Pr{{" do
    throwError "unexpected braced event formatting: {fmt}"

namespace VCVioTest.ProbabilityBounds

universe v

section monad

variable {m : Type → Type v} [Monad m] [LawfulMonad m]
  [EvalDistSemantics m] [LawfulEvalDistSemantics m] {α β γ : Type}

example (mx : m α) (f : α → β) (p : β → Prop) :
    Pr{let y ← f <$> mx}[p y] = Pr{let x ← mx}[p (f x)] := by simp

example (mx : m α) (my : m β) (p : α → Prop) (q : β → Prop) :
    Pr{let x ← mx; let y ← my}[p x ∧ q y] =
      Pr{let x ← mx}[p x] * Pr{let y ← my}[q y] := by simp

example (mx : m α) (my : m β) (p : α → Prop) (q : β → Prop) {bound : ENNReal}
    (h : Pr{let x ← mx}[p x] * Pr{let y ← my}[q y] ≤ bound) :
    Pr{let x ← mx; let y ← my}[p x ∧ q y] ≤ bound := by grind

example (source : m α) (f : α → m β) (p : β → Prop) :
    Pr{let y ← source >>= f}[p y] ^ 2 ≤
      Pr{let x ← source; let a ← f x; let b ← f x}[p a ∧ p b] :=
  prEvent_bind_sq_le_bind_pair source f p

example (mx : m α) (p q : α → Prop) (hpq : ∀ x, p x → q x) :
    Pr{let x ← mx}[p x] ^ 2 ≤ Pr{let x ← mx}[q x] ^ 2 := by
  gcongr ?_ ^ 2
  exact prEvent_mono mx p q hpq

example (mx : m α) (p q : α → Prop) (hpq : ∀ x, p x → q x) {bound : ENNReal}
    (h : Pr{let x ← mx}[q x] ≤ bound) : Pr{let x ← mx}[p x] ≤ bound := by
  grw [prEvent_mono mx p q hpq, h]

example [Fintype γ] (mx : m (Option α)) (select : α → Option γ) :
    ∑ k : γ, Pr{let r ← mx}[r.map select = some (some k)] ≤ Pr{let r ← mx}[r.isSome] :=
  sum_prEvent_option_map_eq_some_le_isSome mx select

end monad

example {m : Type → Type} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α : Type} [MeasurableSpace α] [MeasurableSingletonClass α] (mx : m α) (a : α) :
    Pr{let x ← mx}[x = a] = 𝒟[mx] {a} :=
  prEvent_eq_evalDist_singleton mx a

example {m : Type → Type} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (mx : m (α × β)) (a : α) (b : β) :
    Pr{let pair ← mx}[pair = (a, b)] = 𝒟[mx] {(a, b)} :=
  prEvent_eq_evalDist_singleton mx (a, b)

example {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
    (κ : Kernel α β) [IsSFiniteKernel κ] (μ : Measure α) [IsSubprobabilityMeasure μ]
    {s : Set β} (hs : MeasurableSet s) :
    ((κ ∘ₘ μ) s) ^ 2 ≤ ((κ ×ₖ κ) ∘ₘ μ) (s ×ˢ s) :=
  Kernel.comp_apply_sq_le_prod_comp_apply κ μ hs

/-- A measure-only interface whose query always returns `true`. -/
@[expose, reducible] def biasedSpec : OracleSpec Unit := fun _ ↦ Bool

noncomputable instance : IsMeasureSpec biasedSpec where
  toMeasure _ := Measure.dirac true
  isProbabilityMeasure _ := inferInstance

section fork

variable {ι : Type} {spec : OracleSpec ι} {α : Type}
  [∀ t, MeasurableSpace (spec.Range t)] [∀ t, DiscreteMeasurableSpace (spec.Range t)]
  [IsMeasureSpec spec] {main : OracleComp spec α} {i : ι} {n : Nat}

example (occurrence : PFunctor.FreeM.Cursor.Occurrence i main n) :
    𝒟[(fun completion ↦ completion.answer) <$>
      OracleComp.Cursor.completeOccurrence occurrence] =
      IsMeasureSpec.toMeasure (spec := spec) i := by simp

example (occurrence : PFunctor.FreeM.Cursor.Occurrence i main n) (p : spec.Range i → Prop) :
    Pr{let completion ← OracleComp.Cursor.completeOccurrence occurrence}[p completion.answer] =
      Pr{let answer ← (query i : OracleComp spec (spec.Range i))}[p answer] := by simp

example (occurrence : PFunctor.FreeM.Cursor.Occurrence i main n) (p : spec.Range i → Prop)
    {bound : ENNReal}
    (h : Pr{let answer ← (query i : OracleComp spec (spec.Range i))}[p answer] ≤ bound) :
    Pr{let completion ← OracleComp.Cursor.completeOccurrence occurrence}[p completion.answer] ≤
      bound := by grind

example (occurrence : PFunctor.FreeM.Cursor.Occurrence i main n) :
    IsProbabilityMeasure 𝒟[(fun completion ↦ completion.answer) <$>
      OracleComp.Cursor.completeOccurrence occurrence] := inferInstance

example (occurrence : PFunctor.FreeM.Cursor.Occurrence i main n) :
    IsSubprobabilityMeasure 𝒟[(fun completion ↦ completion.answer) <$>
      OracleComp.Cursor.completeOccurrence occurrence] := inferInstance

example {path : PFunctor.FreeM.Path main}
    (located : PFunctor.FreeM.Cursor.Located i main path n) :
    𝒟[(fun view ↦ view.secondAnswer) <$> OracleComp.ofFreeM located.fork] =
      IsMeasureSpec.toMeasure (spec := spec) i := by simp

example {path : PFunctor.FreeM.Path main}
    (located : PFunctor.FreeM.Cursor.Located i main path n) {bound : ENNReal}
    (h : IsMeasureSpec.toMeasure (spec := spec) i {located.completion.answer} ≤ bound) :
    Pr{let view ← OracleComp.ofFreeM located.fork}[view.firstAnswer = view.secondAnswer] ≤
      bound := by grind

example {path : PFunctor.FreeM.Path main}
    (located : PFunctor.FreeM.Cursor.Located i main path n) (accept : α → Prop) :
    Pr{let view ← OracleComp.ofFreeM located.fork}[view.firstAnswer = view.secondAnswer ∧
      accept (PFunctor.FreeM.output main view.firstPath)] ≤
      IsMeasureSpec.toMeasure (spec := spec) i {located.completion.answer} :=
  OracleComp.prEvent_focusCollision_fork_le located accept

end fork

example {ι : Type} {spec : OracleSpec ι} {α : Type}
    [∀ t, MeasurableSpace (spec.Range t)] [∀ t, DiscreteMeasurableSpace (spec.Range t)]
    [IsUniformMeasureSpec spec] {main : OracleComp spec α} {i : ι} {n : Nat}
    {path : PFunctor.FreeM.Path main}
    (located : PFunctor.FreeM.Cursor.Located i main path n) (accept : α → Prop) :
    Pr{let view ← OracleComp.ofFreeM located.fork}[view.firstAnswer = view.secondAnswer ∧
      accept (PFunctor.FreeM.output main view.firstPath)] ≤
      (Fintype.card (spec.Range i) : ENNReal)⁻¹ :=
  OracleComp.prEvent_focusCollision_fork_le_of_uniform located accept

example {α : Type} [MeasurableSpace α] (main : OracleComp biasedSpec α) :
    IsProbabilityMeasure 𝒟[main] := inferInstance

example {α β : Type} (main : OracleComp biasedSpec α) (n : Nat) (observe : α → Option β)
    (value : β) (hselect : OracleComp.OutputSelectsOccurrence main () n observe value) :
    Pr{let output ← main}[observe output = some value] ^ 2 ≤
      Pr{let pair ← OracleComp.observedForkPair main () n observe}[
        pair = some (some value, some value)] :=
  OracleComp.prEvent_sq_le_observedForkPair main () n observe value hselect

end VCVioTest.ProbabilityBounds
