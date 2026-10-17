/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import Mathlib.Probability.Kernel.IonescuTulcea.Traj
public import Mathlib.Probability.Process.Filtration
public import ToMathlib.MeasureTheory.Measure.TotalVariation.Projective

/-!
# Infinite trajectories of measurable services

Mathlib's Ionescu–Tulcea construction supplies the path law of an explicitly measurable
transition kernel. History-dependent transitions are supported directly; a state kernel is
embedded by reading the most recent state. Emitted traffic can be retained in that state.
Finite-prefix laws determine the full law, and a uniform finite-prefix variation bound also
controls every event in the full product σ-algebra.
-/

public section

open MeasureTheory ProbabilityTheory Finset Preorder
open scoped ENNReal

namespace ProbabilityTheory.Kernel

variable {S : Type*} [MeasurableSpace S]

/-- Use the last state of a finite history as input to a measurable transition. -/
noncomputable def historyStep (step : Kernel S S) (n : ℕ) :
    Kernel (Finset.Iic n → S) S :=
  step.comap (fun history => history ⟨n, Finset.mem_Iic.mpr le_rfl⟩)
    (measurable_pi_apply _)

instance (step : Kernel S S) [IsMarkovKernel step] (n : ℕ) :
    IsMarkovKernel (historyStep step n) := by unfold historyStep; infer_instance

/-- The infinite path law of a Markov service with the supplied initial law. -/
noncomputable def pathLaw (step : Kernel S S) [IsMarkovKernel step] (initial : Measure S) :
    Measure (ℕ → S) := trajMeasure initial (historyStep step)

instance (step : Kernel S S) [IsMarkovKernel step] (initial : Measure S)
    [IsProbabilityMeasure initial] : IsProbabilityMeasure (pathLaw step initial) := by
  unfold pathLaw
  infer_instance

/-- The law of each finite prefix is Mathlib's finite iterated-kernel trajectory law. -/
theorem pathLaw_map_prefix (step : Kernel S S) [IsMarkovKernel step]
    (initial : Measure S) (n : ℕ) :
    (pathLaw step initial).map (Preorder.frestrictLe n) =
      (partialTraj (X := fun _ : ℕ => S) (historyStep step) 0 n) ∘ₘ
        (initial.map (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => S)).symm) := by
  rw [pathLaw, trajMeasure, Measure.map_comp _ _ (measurable_frestrictLe n),
    traj_map_frestrictLe]

/-- The next coordinate's law is obtained by applying the transition to the current marginal. -/
theorem pathLaw_map_succ (step : Kernel S S) [IsMarkovKernel step]
    (initial : Measure S) [IsProbabilityMeasure initial] (n : ℕ) :
    (pathLaw step initial).map (fun path => path (n + 1)) =
      ((pathLaw step initial).map (fun path => path n)).bind step := by
  have h := congrArg Measure.snd
    (map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
      (X := fun _ : ℕ => S) (μ₀ := initial) (κ := historyStep step) (a := n))
  rw [Measure.snd_compProd, Measure.snd_map_prodMk (measurable_frestrictLe n)
    (measurable_pi_apply (n + 1))] at h
  rw [show ⇑(historyStep step n) =
    (fun history => step (history ⟨n, Finset.mem_Iic.mpr le_rfl⟩)) from rfl] at h
  have hm : Measurable (fun history : Finset.Iic n → S =>
      step (history ⟨n, Finset.mem_Iic.mpr le_rfl⟩)) :=
    step.measurable.comp (measurable_pi_apply _)
  rw [Measure.bind_map (measurable_frestrictLe n).aemeasurable hm.aemeasurable] at h
  rw [Measure.bind_map (measurable_pi_apply n).aemeasurable step.aemeasurable]
  exact h.symm

end ProbabilityTheory.Kernel

namespace MeasureTheory.Measure

variable {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]

/-- A uniform finite-prefix bound extends to events on complete infinite paths. -/
theorem etvDist_le_of_prefixes (μ ν : Measure (Π n, X n))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (ε : ℝ≥0∞)
    (h : ∀ n, (μ.map (Preorder.frestrictLe n)).etvDist
      (ν.map (Preorder.frestrictLe n)) ≤ ε) : μ.etvDist ν ≤ ε := by
  apply etvDist_le_of_finite_marginals μ ν ε
  intro keys
  have hsubset := keys.subset_Iic_sup_id
  have heq : (keys.restrict : (Π n, X n) → _) =
      Finset.restrict₂ hsubset ∘ Preorder.frestrictLe (keys.sup id) :=
    (Finset.restrict₂_comp_restrict hsubset).symm
  rw [heq, ← Measure.map_map (measurable_restrict₂ hsubset) (measurable_frestrictLe _),
    ← Measure.map_map (measurable_restrict₂ hsubset) (measurable_frestrictLe _)]
  exact (etvDist_map_le _ _ _ (measurable_restrict₂ hsubset)).trans (h _)

/-- Equality of every finite-prefix law determines equality of full path laws. -/
theorem eq_of_prefixes (μ ν : Measure (Π n, X n)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ n, μ.map (Preorder.frestrictLe n) = ν.map (Preorder.frestrictLe n)) : μ = ν := by
  apply etvDist_eq_zero_iff.mp
  apply le_antisymm _ bot_le
  exact etvDist_le_of_prefixes μ ν 0 (fun n => by rw [h n, etvDist_self])

end MeasureTheory.Measure
