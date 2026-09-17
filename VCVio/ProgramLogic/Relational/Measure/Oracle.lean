/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.ProgramLogic.Relational.Measure.Bind
public import VCVio.OracleComp.EvalDist.Measure
public import PolyFun.Control.Monad.Algebra.Relational

/-!
# Qualitative measure coupling algebra for finite oracle trees

Finite response types give finite operational output sets even when the output type itself is
uncountable. Conditional coupling witnesses can be selected on those concentration sets.
The scoped algebra uses successful-output measures and does not identify their almost sure
postconditions with structural reachability under arbitrary weighted interpretations.
-/

public section

open MeasureTheory

universe u v

namespace OracleComp.MeasureRelational

open OracleSpec MeasureProgramLogic

variable {ι₁ : Type u} {ι₂ : Type v}
  {spec₁ : OracleSpec.{u, 0} ι₁} {spec₂ : OracleSpec.{v, 0} ι₂}
  [∀ t, MeasurableSpace (spec₁.Range t)] [∀ t, MeasurableSpace (spec₂.Range t)]
  [IsMeasureSpec spec₁] [IsMeasureSpec spec₂]

/-- Qualitative coupling WP observes outputs with their discrete measurable structures. -/
@[expose]
noncomputable def wp {α β : Type} (mx : OracleComp spec₁ α) (my : OracleComp spec₂ β)
    (post : α → β → Prop) : Prop :=
  let : MeasurableSpace α := ⊤
  let : MeasurableSpace β := ⊤
  RelWP mx my post

/-- Pure leaves have the exact relational postcondition. -/
@[simp]
theorem wp_pure_pure {α β : Type} (a : α) (b : β) (post : α → β → Prop) :
    wp (pure a : OracleComp spec₁ α) (pure b : OracleComp spec₂ β) post ↔ post a b := by
  simp [wp]

/-- Implication of postconditions preserves qualitative oracle coupling WP. -/
theorem wp_mono {α β : Type} {mx : OracleComp spec₁ α} {my : OracleComp spec₂ β}
    {post post' : α → β → Prop} (h : ∀ a b, post a b → post' a b) :
    wp mx my post → wp mx my post' := by
  let : MeasurableSpace α := ⊤
  let : MeasurableSpace β := ⊤
  intro hwp
  exact relWP_mono hwp h

variable [∀ t, DiscreteMeasurableSpace (spec₁.Range t)]
  [∀ t, DiscreteMeasurableSpace (spec₂.Range t)]

/-- Finite response types discharge the countable choice and concentration obligations of the
qualitative sequential coupling rule. No positivity of response masses is required. -/
theorem wp_bind {α β γ δ : Type}
    [∀ t, Finite (spec₁.Range t)] [∀ t, Finite (spec₂.Range t)]
    (mx : OracleComp spec₁ α) (my : OracleComp spec₂ β)
    (f : α → OracleComp spec₁ γ) (g : β → OracleComp spec₂ δ)
    (post : γ → δ → Prop)
    (h : wp mx my (fun a b ↦ wp (f a) (g b) post)) :
    wp (mx >>= f) (my >>= g) post := by
  let : MeasurableSpace α := ⊤
  let : MeasurableSpace β := ⊤
  let : MeasurableSpace γ := ⊤
  let : MeasurableSpace δ := ⊤
  rw [wp, RelWP, evalDist_bind_of_discrete, evalDist_bind_of_discrete]
  rw [wp, RelWP] at h
  exact h.bind_of_countable_of_ae_mem
    (PFunctor.FreeM.support_finite mx).countable
    (PFunctor.FreeM.support_finite my).countable
    (PFunctor.FreeM.support_finite (mx >>= f)).countable
    (PFunctor.FreeM.support_finite (my >>= g)).countable
    (ae_of_forall_mem_support mx _ fun _ h ↦ h)
    (ae_of_forall_mem_support my _ fun _ h ↦ h)
    .of_discrete .of_discrete
    (fun a ha ↦ ae_of_forall_mem_support (f a) _ fun x hx ↦
      MonadAttach.mem_support_bind.mpr ⟨a, ha, hx⟩)
    (fun b hb ↦ ae_of_forall_mem_support (g b) _ fun y hy ↦
      MonadAttach.mem_support_bind.mpr ⟨b, hb, hy⟩)
    (fun _ _ _ _ h ↦ by simpa only [wp, RelWP] using h)

end OracleComp.MeasureRelational

namespace MeasureProgramLogic.Relational

open OracleSpec OracleComp.MeasureRelational

variable {ι₁ : Type u} {ι₂ : Type v}
  {spec₁ : OracleSpec.{u, 0} ι₁} {spec₂ : OracleSpec.{v, 0} ι₂}
  [∀ t, MeasurableSpace (spec₁.Range t)] [∀ t, MeasurableSpace (spec₂.Range t)]
  [∀ t, DiscreteMeasurableSpace (spec₁.Range t)]
  [∀ t, DiscreteMeasurableSpace (spec₂.Range t)]
  [IsMeasureSpec spec₁] [IsMeasureSpec spec₂]

/-- Measure-valued qualitative relational algebra for finite oracle response types. -/
noncomputable scoped instance (priority := 1100) instMAlgRelOrdered
    [∀ t, Finite (spec₁.Range t)] [∀ t, Finite (spec₂.Range t)] :
    MAlgRelOrdered (OracleComp spec₁) (OracleComp spec₂) Prop where
  rwp := wp
  rwp_pure a b post := propext (wp_pure_pure a b post)
  rwp_mono h := wp_mono h
  rwp_bind_le mx my f g post := wp_bind mx my f g post

/-- The scoped relational algebra observes the native oracle coupling judgment. -/
theorem relWP_eq_wp {α β : Type}
    [∀ t, Finite (spec₁.Range t)] [∀ t, Finite (spec₂.Range t)]
    (mx : OracleComp spec₁ α) (my : OracleComp spec₂ β) (post : α → β → Prop) :
    MAlgRelOrdered.RelWP mx my post = wp mx my post := rfl

end MeasureProgramLogic.Relational
