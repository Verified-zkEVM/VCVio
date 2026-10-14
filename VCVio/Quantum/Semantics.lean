/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.EvalDist.Defs.Semantics.Core
public import VCVio.Quantum.Observe

/-!
# Bundled semantics of subinstruments

`Quantum.SubInstrument.semanticsVia` packages the outcome measure of subinstruments on a register,
from a fixed initial substate, as a bundled `SemanticsVia` on the monad `SubInstrument M M`.
Observation fixes the initial state and discards the final one, so it is not a monad morphism.

This is the only part of the quantum core that depends on the rest of VCVio: the outcome measure
itself is defined in `VCVio.Quantum.Observe`.
-/

public section

universe u w

namespace Quantum

namespace SubInstrument

variable {M : Type u} [Fintype M]

/-- The bundled semantics of subinstruments on the register `M` started from the substate `ρ₀`:
a subinstrument is observed through the measure of its classical results, and the final state
of the register is discarded. -/
@[expose]
noncomputable def semanticsVia (ρ₀ : SubState M) : SemanticsVia (SubInstrument.{u, u, w} M M) where
  Sem := SubInstrument M M
  instMonadSem := inferInstance
  interpret := MonadHom.id (SubInstrument M M)
  observe := fun p ↦ p.outcomeMeasure ρ₀
  observe_apply_univ_le_one := fun p ↦ p.outcomeMeasure_apply_univ_le_one ρ₀

/-- The denotation of a subinstrument under `Quantum.SubInstrument.semanticsVia ρ₀` is its
outcome measure from `ρ₀`. -/
@[simp]
theorem semanticsVia_evalDist (ρ₀ : SubState M) {α : Type w} [MeasurableSpace α]
    (p : SubInstrument M M α) : (semanticsVia ρ₀).evalDist p = p.outcomeMeasure ρ₀ :=
  rfl

end SubInstrument

end Quantum
