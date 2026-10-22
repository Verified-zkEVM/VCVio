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

`Quantum.SubInstrument.semanticsVia ρ₀` presents subinstruments on a register `M` as a VCVio
`SemanticsVia`, so that the generic VCVio notions of probability and equivalence apply to them.
Its three parts are: the semantic monad `SubInstrument M M`; the identity interpretation into it;
and the observation `p ↦ p.outcomeMeasure ρ₀`, which runs `p` from the fixed initial substate
`ρ₀`, keeps the distribution of the classical outcome and discards the final quantum state.

The interpretation is a monad morphism; the observation does not in general preserve `bind`.
The distribution of the outcome of `p.bind k` depends on the quantum state that `p` leaves behind,
which the distribution of the outcome of `p` forgets. The composition law is the chain rule
`Quantum.DSubInstrument.outcomeMeasure_bind`.

This is the only part of the quantum core that imports the rest of VCVio; the outcome measure
itself is defined in `VCVio.Quantum.Observe`.
-/

public section

universe u w

namespace Quantum

namespace SubInstrument

variable {M : Type u} [Fintype M]

/-- Subinstruments on the register `M`, observed from the initial substate `ρ₀`: the semantic
monad is `SubInstrument M M`, the interpretation is the identity, and the observation is
`p ↦ p.outcomeMeasure ρ₀`, which keeps the distribution of the classical outcome and discards the
final quantum state. The observation does not in general preserve `bind`; see
`DSubInstrument.outcomeMeasure_bind`. -/
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
