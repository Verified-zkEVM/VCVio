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
-/

public section

open MeasureTheory ProbabilityTheory OracleSpec

run_cmd do
  let env ← Lean.getEnv
  for name in [`PMF, `SPMF] do
    if env.contains name then
      throwError "native probability bounds unexpectedly import {name}"

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
    (h : Pr{ let x ← mx}[p x] * Pr{ let y ← my}[q y] ≤ bound) :
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
    (h : Pr{ let x ← mx}[q x] ≤ bound) : Pr{let x ← mx}[p x] ≤ bound := by
  grw [prEvent_mono mx p q hpq, h]

example [Fintype γ] (mx : m (Option α)) (select : α → Option γ) :
    ∑ k : γ, Pr{let r ← mx}[r.map select = some (some k)] ≤ Pr{let r ← mx}[r.isSome] :=
  sum_prEvent_option_map_eq_some_le_isSome mx select

end monad

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

example {α β : Type} (main : OracleComp biasedSpec α) (n : Nat) (observe : α → Option β)
    (value : β) (hselect : OracleComp.OutputSelectsOccurrence main () n observe value) :
    Pr{let output ← main}[observe output = some value] ^ 2 ≤
      Pr{let pair ← OracleComp.observedForkPair main () n observe}[
        pair = some (some value, some value)] :=
  OracleComp.prEvent_sq_le_observedForkPair main () n observe value hselect

end VCVioTest.ProbabilityBounds
