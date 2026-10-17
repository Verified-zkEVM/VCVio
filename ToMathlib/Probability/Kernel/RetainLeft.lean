/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import Mathlib.Probability.Kernel.Composition.ParallelComp
public import Mathlib.Probability.Kernel.Composition.Comp

/-!
# Applying a kernel while retaining an observation

`retainLeft` transports the second component of a pair and keeps its first component.
It is the parallel composition of the identity with the supplied kernel.
-/

public section

open MeasureTheory
open scoped ProbabilityTheory

namespace ProbabilityTheory.Kernel

variable {A S T U : Type*} [MeasurableSpace A] [MeasurableSpace S]
  [MeasurableSpace T] [MeasurableSpace U]

/-- Apply a state kernel while retaining the already produced observation. -/
noncomputable def retainLeft (A : Type*) [MeasurableSpace A] (R : Kernel S T) :
    Kernel (A × S) (A × T) := Kernel.id ∥ₖ R

instance (R : Kernel S T) [IsMarkovKernel R] : IsMarkovKernel (retainLeft A R) := by
  unfold retainLeft
  infer_instance

/-- Retaining an observation is a pushforward of the state law. -/
theorem retainLeft_apply (R : Kernel S T) [IsSFiniteKernel R] (out : A × S) :
    retainLeft A R out = (R out.2).map (Prod.mk out.1) := by
  rw [retainLeft, parallelComp_apply, id_apply, Measure.dirac_prod]

/-- A continuation sees the retained observation and the reconstructed state. -/
theorem bind_retainLeft (R : Kernel S T) [IsSFiniteKernel R]
    (f : A × T → Measure U) (hf : Measurable f) (out : A × S) :
    (retainLeft A R out).bind f = (R out.2).bind (fun t => f (out.1, t)) := by
  rw [retainLeft_apply, Measure.bind_map measurable_prodMk_left.aemeasurable hf.aemeasurable]

/-- A probability reconstruction leaves the observation marginal unchanged. -/
theorem map_fst_retainLeft (R : Kernel S T) [IsMarkovKernel R] (out : A × S) :
    (retainLeft A R out).map Prod.fst = Measure.dirac out.1 := by
  rw [retainLeft_apply, Measure.map_map measurable_fst measurable_prodMk_left]
  exact (Measure.map_const (R out.2) out.1).trans (by simp)

/-- Reconstructing private state after a run preserves its output law. -/
theorem map_fst_bind_retainLeft (R : Kernel S T) [IsMarkovKernel R] (μ : Measure (A × S)) :
    (μ.bind (retainLeft A R)).map Prod.fst = μ.map Prod.fst := by
  rw [Measure.map_bind (retainLeft A R).aemeasurable measurable_fst.aemeasurable]
  simp_rw [map_fst_retainLeft]
  exact Measure.bind_dirac_eq_map μ measurable_fst

/-- Deterministic reconstruction is ordinary state projection. -/
theorem retainLeft_deterministic (f : S → T) (hf : Measurable f) :
    retainLeft A (deterministic f hf) =
      deterministic (fun out => (out.1, f out.2))
        (measurable_fst.prodMk (hf.comp measurable_snd)) := by
  ext out : 1
  rw [retainLeft_apply, deterministic_apply, deterministic_apply,
    Measure.map_dirac' measurable_prodMk_left]

end ProbabilityTheory.Kernel
