/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import VCVio.EvalDist.PFunctorMeasure
public import Mathlib.InformationTheory.KullbackLeibler.DataProcessing

/-!
# Kullback-Leibler divergence between denoted programs

The measure denotation of `VCVio.EvalDist.PFunctorMeasure` puts VCVio programs inside Mathlib's
probability library, and this module spends that access on the Kullback-Leibler divergence.

Nothing here is a port. `Measure.bind` *is* composition of a measure with a kernel — Mathlib
writes it `κ ∘ₘ μ` — so a program's `>>=` is already the object
`InformationTheory.klDiv_comp_right_le` quantifies over, and `<$>` is already the object
`klDiv_map_le` quantifies over. The work is to package a program-valued continuation as a
`ProbabilityTheory.Kernel` and read the inequalities off.

## The game-hopping reading

`klDiv_denote_bind_le` says that post-processing two computations by the *same* continuation
cannot increase the divergence between them. That is the shape a reduction step is usually
argued in: whatever an adversary does after the point where two games differ, it cannot recover
information the two distributions do not already distinguish.

`klDiv_denote_bind_congr` is the corresponding exact statement — binding the same continuation to
a common prefix leaves the divergence unchanged — which is Mathlib's `klDiv_compProd_left`.

## Divergences and the discrete layer

VCVio's existing quantitative theory (`VCVio.EvalDist.TVDist`,
`VCVio.EvalDist.RenyiDivergence`) is stated over `SPMF` and reaches only countably supported
distributions. Kullback-Leibler is not available there at all. The statements below hold for any
measurable output type, so they apply to programs whose answers are continuous.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory

universe u uA

namespace PFunctor.FreeM

variable {P : PFunctor.{uA, u}} [∀ a, MeasurableSpace (P.B a)] [P.IsMeasureSpec]
  [∀ a, DiscreteMeasurableSpace (P.B a)] {α β : Type u}
  [MeasurableSpace α] [DiscreteMeasurableSpace α] [MeasurableSpace β]

/-! ### A continuation as a Markov kernel -/

/-- A program-valued continuation out of a discrete type, read as a Markov kernel.

Measurability is `Measurable.of_discrete`: the *domain* is discrete, so no constraint is placed
on the output type, which may be continuous. -/
noncomputable def denoteKernel (f : α → FreeM P β) : Kernel α β :=
  ⟨fun x => denote (f x), Measurable.of_discrete⟩

omit [∀ a, DiscreteMeasurableSpace (P.B a)] in
@[simp]
theorem denoteKernel_apply (f : α → FreeM P β) (x : α) :
    denoteKernel f x = denote (f x) := rfl

instance isMarkovKernel_denoteKernel (f : α → FreeM P β) :
    IsMarkovKernel (denoteKernel f) :=
  ⟨fun x => isProbabilityMeasure_denote (f x)⟩

/-- Binding a continuation is composing with its kernel. -/
theorem denote_bind_eq_comp (program : FreeM P α) (f : α → FreeM P β) :
    denote (program >>= f) = denoteKernel f ∘ₘ denote program :=
  denote_bind_of_discrete program f

/-- Mapping a function is pushing the denotation forward along it. -/
theorem denote_map (g : α → β) (program : FreeM P α) :
    denote (g <$> program) = (denote program).map g := by
  have h : (g <$> program) = program >>= fun x => pure (g x) := by simp
  rw [h, denote_bind_of_discrete]
  exact Measure.bind_dirac_eq_map _ Measurable.of_discrete

/-! ### Data processing -/

/-- **Data processing inequality** for program composition: running the same continuation on two
computations cannot increase the Kullback-Leibler divergence between them.

This is Mathlib's `InformationTheory.klDiv_comp_right_le`, applied to `denoteKernel`. -/
theorem klDiv_denote_bind_le (mx my : FreeM P α) (f : α → FreeM P β) :
    klDiv (denote (mx >>= f)) (denote (my >>= f)) ≤ klDiv (denote mx) (denote my) := by
  have := isProbabilityMeasure_denote (P := P) mx
  have := isProbabilityMeasure_denote (P := P) my
  rw [denote_bind_eq_comp, denote_bind_eq_comp]
  exact klDiv_comp_right_le _ _ (denoteKernel f)

/-- **Data processing inequality** for post-processing by a function. -/
theorem klDiv_denote_map_le (g : α → β) (mx my : FreeM P α) :
    klDiv (denote (g <$> mx)) (denote (g <$> my)) ≤ klDiv (denote mx) (denote my) := by
  have := isProbabilityMeasure_denote (P := P) mx
  have := isProbabilityMeasure_denote (P := P) my
  rw [denote_map, denote_map]
  exact klDiv_map_le _ _ Measurable.of_discrete

end PFunctor.FreeM
