/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Model.Domain

/-!
# Polymorphic values and recursive declaration groups

A schema denotes a suspended family over every valid instantiation. An outer
bottom or error is distinct from a returned family whose individual instances
are partial. Recursive groups take one simultaneous least fixed point across
all declarations and all instantiations. This domain supports calls at a
different instantiation; it does not assume a finite monomorphization.

These are semantic building blocks. The resolved syntax currently supports
closed instantiations, so a frontend-to-family preservation theorem is separate.
-/

public section

open OmegaCompletePartialOrder

namespace Interop.Cryptol.Schema

/-- The result type at a checked instantiation of a schema. -/
@[expose] def resultType (s : Schema) (i : s.Instantiation) : ClosedTy :=
  s.body.instantiate (fun n => n.eval i.numbers) i.types

/-- A polymorphic value retains every valid type and numeric instantiation. -/
abbrev Family (s : Schema) := (i : s.Instantiation) → Computation (s.resultType i)

/-- The quantified expression can itself diverge or fail before it returns a family. -/
abbrev Suspended (s : Schema) := DomainResult EvalError s.Family

/-- Type application demands the quantified expression, then selects its instance. -/
@[expose] noncomputable def apply (s : Schema) (i : s.Instantiation) :
    s.Suspended →𝒄 Computation (s.resultType i) :=
  DomainResult.bind (.ofFun (fun f => f i))

@[simp] theorem apply_value (s : Schema) (f : s.Family) (i : s.Instantiation) :
    s.apply i (.value f) = f i := rfl

@[simp] theorem apply_bot (s : Schema) (i : s.Instantiation) : s.apply i ⊥ = ⊥ := rfl

@[simp] theorem apply_error (s : Schema) (i : s.Instantiation) (e : EvalError) :
    s.apply i (.error e) = .error e := rfl

/-- An available polymorphic value with divergent instances is not outer divergence. -/
theorem value_bottom_ne_bot (s : Schema) :
    (DomainResult.value (⊥ : s.Family) : s.Suspended) ≠ ⊥ := DomainResult.value_ne_bot _

/-- One environment contains every member of a recursive group at its declared schema. -/
abbrev Group {ι : Type} (schemas : ι → Schema) := (i : ι) → (schemas i).Suspended

/-- Mutual and polymorphic recursion use a single least fixed point of the whole group. -/
@[expose] noncomputable def recursiveGroup {ι : Type} {schemas : ι → Schema}
    (body : Group schemas →𝒄 Group schemas) : Group schemas := body.fix

/-- The group equations hold simultaneously, including at other instantiations. -/
theorem recursiveGroup_unfold {ι : Type} {schemas : ι → Schema}
    (body : Group schemas →𝒄 Group schemas) : body (recursiveGroup body) = recursiveGroup body :=
  body.map_fix

/-- Recursive interpretation selects the least solution, not an arbitrary fixed point. -/
theorem recursiveGroup_le {ι : Type} {schemas : ι → Schema}
    (body : Group schemas →𝒄 Group schemas) (candidate : Group schemas)
    (h : body candidate ≤ candidate) : recursiveGroup body ≤ candidate := body.fix_le h

/-- A strict continuous translation preserving recursive bodies preserves their least solutions. -/
theorem recursiveGroup_fusion {ι κ : Type} {schemas : ι → Schema} {targets : κ → Schema}
    (body : Group schemas →𝒄 Group schemas) (target : Group targets →𝒄 Group targets)
    (translate : Group schemas →𝒄 Group targets) (strict : translate ⊥ = ⊥)
    (commutes : ∀ env, translate (body env) = target (translate env)) :
    translate (recursiveGroup body) = recursiveGroup target :=
  body.fix_fusion target translate strict commutes

end Interop.Cryptol.Schema
