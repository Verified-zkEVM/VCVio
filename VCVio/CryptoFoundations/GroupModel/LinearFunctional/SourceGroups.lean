/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.Interaction

/-! # Separately tracked pairing source groups

The two source sorts remain distinct even when their carrier types coincide. Lists record
only group inputs; ordinary oracle arguments and scalar messages belong to the data channel.
-/

public section

namespace GroupModel.LinearFunctional

/-- Two separately indexed source groups for an algebraic pairing protocol. -/
abbrev SourceGroup (G₁ G₂ : Type) : Bool → Type
  | false => G₁
  | true => G₂

/-- Each source sort inherits the corresponding additive operations. -/
instance {G₁ G₂ : Type} [AddMonoid G₁] [AddMonoid G₂] (s : Bool) :
    AddMonoid (SourceGroup G₁ G₂ s) := by cases s <;> dsimp [SourceGroup] <;> infer_instance

/-- Scalar multiplication is inherited separately at each source sort. -/
instance {F G₁ G₂ : Type} [SMul F G₁] [SMul F G₂] (s : Bool) :
    SMul F (SourceGroup G₁ G₂ s) := by cases s <;> dsimp [SourceGroup] <;> infer_instance

/-- A pair of chronological input lists, one for each source group. -/
@[expose] def sourceInputs {G₁ G₂ : Type} (xs : List G₁) (ys : List G₂) :
    Interaction.Groups (SourceGroup G₁ G₂)
  | false => xs
  | true => ys

end GroupModel.LinearFunctional
