/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.ProgramLogic.Library.T1.SimulateQ
public import VCVio.ProgramLogic.Unary.WP.Necessary
public import VCVio.ProgramLogic.Unary.WP.Lower
public import PolyFun.Control.Do.Spec
public import PolyFun.Control.Monad.WriterT.WP
public import ToMathlib.Control.WriterT

/-!
# Tests for the structural `simulateQ` specifications

Core `vcgen` walks simulated programs through the rules of
`VCVio.ProgramLogic.Library.T1.SimulateQ`, under the necessary and the lower reading, at
arbitrary universes.
-/

public section

open OracleSpec OracleComp Std.WP OracleComp.ProgramLogic

set_option experimental.vcgen true

universe u w u' v'

namespace SimulateQTest

section necessary

open scoped OracleComp.Necessary

variable {ι : Type u} {spec : OracleSpec.{u, w} ι}

/-- A handler counting its calls, forwarding each query. -/
def countImpl : QueryImpl spec (StateT (ULift.{w} ℕ) (OracleComp spec)) := fun t ↦ do
  modify fun n ↦ ⟨n.down + 1⟩
  liftM (spec.query t)

/-- `vcgen` walks the simulation, the queries and the handler body, at every universe. -/
example (t₁ t₂ : spec.Domain) (n₀ : ℕ) :
    ⦃ fun n ↦ n.down = n₀ ⦄
      (simulateQ countImpl (do let a ← query t₁; let b ← query t₂; pure (a, b)) :
        StateT (ULift ℕ) (OracleComp spec) _)
    ⦃ fun _ n ↦ n.down = n₀ + 2 ⦄ := by
  vcgen [countImpl] with finish

/-- Maps and conditionals in the simulated program. -/
example (t : spec.Domain) (c : Bool) (f : spec.Range t → spec.Range t) (n₀ : ℕ) :
    ⦃ fun n ↦ n.down = n₀ ⦄
      (simulateQ countImpl (if c then f <$> query t else query t) :
        StateT (ULift ℕ) (OracleComp spec) _)
    ⦃ fun _ n ↦ n.down = n₀ + 1 ⦄ := by
  vcgen [countImpl] with finish

variable {ι₁ ι₂ : Type u} {spec₁ : OracleSpec.{u, w} ι₁} {spec₂ : OracleSpec.{u, w} ι₂}
  {ι' : Type u'} {spec' : OracleSpec.{u', v'} ι'} {σ : Type w}

/-- A sum handler dispatches queries lifted from its summands to their specifications. -/
example (h₁ : QueryImpl spec₁ (StateT σ (OracleComp spec')))
    (h₂ : QueryImpl spec₂ (StateT σ (OracleComp spec'))) (I : σ → Prop)
    (hh₁ : ∀ t, ⦃ fun s ↦ I s ⦄ h₁ t ⦃ fun _ s ↦ I s ⦄)
    (hh₂ : ∀ t, ⦃ fun s ↦ I s ⦄ h₂ t ⦃ fun _ s ↦ I s ⦄) (t₁ : spec₁.Domain) (t₂ : spec₂.Domain) :
    ⦃ fun s ↦ I s ⦄
      (simulateQ (h₁ + h₂) (do
        let a ← liftM (spec₁.query t₁)
        let b ← liftM (spec₂.query t₂)
        pure (a, b) : OracleComp (spec₁ + spec₂) _))
    ⦃ fun _ s ↦ I s ⦄ := by
  vcgen [hh₁, hh₂]

/-- A sum handler simulates a computation lifted from a summand by that summand. -/
example (h₁ : QueryImpl spec₁ (StateT σ (OracleComp spec')))
    (h₂ : QueryImpl spec₂ (StateT σ (OracleComp spec'))) (oa : OracleComp spec₁ (ULift.{w} ℕ))
    (P : σ → Prop) (Q : ULift ℕ → σ → Prop) (hoa : ⦃ fun s ↦ P s ⦄ simulateQ h₁ oa ⦃ Q ⦄) :
    ⦃ fun s ↦ P s ⦄
      simulateQ (h₁ + h₂) (liftM oa : OracleComp (spec₁ + spec₂) _) ⦃ Q ⦄ := by
  vcgen [hoa]

section writer

open scoped WriterT.AppendWP

variable {ι : Type} {spec : OracleSpec.{0, 0} ι}

/-- A handler logging its inputs. -/
def logImpl : QueryImpl spec (WriterT (List ι) (OracleComp spec)) := fun t ↦ do
  tell [t]
  monadLift (liftM (spec.query t) : OracleComp spec (spec.Range t))

/-- The same rules for a writer handler, read by `WriterT.AppendWP`. -/
example (t₁ t₂ : spec.Domain) (l₀ : List ι) :
    ⦃ fun l ↦ l = l₀ ⦄ simulateQ logImpl (do let _ ← query t₁; query t₂ : OracleComp spec _)
    ⦃ fun _ l ↦ l = l₀ ++ [t₁, t₂] ⦄ := by
  vcgen [logImpl] with finish

end writer

end necessary

section lower

open scoped OracleComp.Lower ENNReal

variable {ι : Type} {spec : OracleSpec.{0, 0} ι}

/-- The same rules under the lower reading, for a stateless handler into `ProbComp`. -/
example (impl : QueryImpl spec ProbComp) (t₁ t₂ : spec.Domain) (b : ℝ≥0∞)
    (post : spec.Range t₂ → ℝ≥0∞)
    (hh₁ : ⦃ b ⦄ impl t₁ ⦃ fun _ ↦ b ⦄) (hh₂ : ⦃ b ⦄ impl t₂ ⦃ post ⦄) :
    ⦃ b ⦄ simulateQ impl (do let _ ← query t₁; query t₂) ⦃ post ⦄ := by
  vcgen [hh₁, hh₂]

/-- Under the lower reading, for a stateful handler over `ProbComp`, with a conditional. -/
example {σ : Type} (impl : QueryImpl spec (StateT σ ProbComp)) (t₁ t₂ : spec.Domain) (c : Bool)
    (P : σ → ℝ≥0∞) (post : spec.Range t₁ → σ → ℝ≥0∞)
    (hh : ⦃ fun s ↦ P s ⦄ impl t₁ ⦃ post ⦄) (hh' : ⦃ fun s ↦ P s ⦄ impl t₂ ⦃ fun _ s ↦ P s ⦄) :
    ⦃ fun s ↦ P s ⦄
      simulateQ impl (if c then query t₁ else do let _ ← query t₂; query t₁) ⦃ post ⦄ := by
  vcgen [hh, hh']

end lower

end SimulateQTest
