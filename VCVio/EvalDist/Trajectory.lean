/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import Mathlib.Probability.Kernel.IonescuTulcea.Traj
public import Mathlib.Probability.Process.Filtration
public import ToMathlib.MeasureTheory.Measure.TotalVariation.Projective
public import ToMathlib.MeasureTheory.MeasurableSpace.Fin
public import ToMathlib.Probability.Kernel.MapWithInput

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

/-- The first coordinate has the supplied initial law. -/
@[simp] theorem pathLaw_map_zero (step : Kernel S S) [IsMarkovKernel step]
    (initial : Measure S) :
    (pathLaw step initial).map (fun path => path 0) = initial := by
  have h := congrArg (fun μ : Measure (Finset.Iic 0 → S) =>
    μ.map (fun history => history ⟨0, Finset.mem_Iic.mpr le_rfl⟩))
      (pathLaw_map_prefix step initial 0)
  have heval : Measurable (fun history : Finset.Iic 0 → S =>
    history ⟨0, Finset.mem_Iic.mpr le_rfl⟩) := measurable_pi_apply _
  simp only [partialTraj_self, Measure.id_comp] at h
  rw [Measure.map_map heval (measurable_frestrictLe 0),
    Measure.map_map heval (MeasurableEquiv.measurable _)] at h
  simpa [Function.comp_def] using h

/-- The joint law of successive finite observations extends by the actual conditional step. -/
theorem pathLaw_map_fin_succ (step : Kernel S S) [IsMarkovKernel step]
    (initial : Measure S) [IsProbabilityMeasure initial] (n : ℕ) :
    (pathLaw step initial).map (fun path (i : Fin (n + 2)) => path i) =
      ((pathLaw step initial).map (fun path (i : Fin (n + 1)) => path i)).bind
        (fun history => (step (history (Fin.last n))).map (Fin.snoc history)) := by
  let restrict : (Finset.Iic n → S) → Fin (n + 1) → S :=
    fun history i => history ⟨i, Finset.mem_Iic.mpr (Nat.le_of_lt_succ i.isLt)⟩
  have hrestrict : Measurable restrict := Measurable.of_eval fun _ => measurable_pi_apply _
  let append : (Finset.Iic n → S) × S → Fin (n + 2) → S :=
    fun pair => Fin.snoc (restrict pair.1) pair.2
  have happend : Measurable append := (measurable_fin_snoc (n + 1)).comp
    ((hrestrict.comp measurable_fst).prodMk measurable_snd)
  have hmap : Measurable (fun history : Fin (n + 1) → S =>
      (step (history (Fin.last n))).map
        (fun next => (Fin.snoc history next : Fin (n + 2) → S))) := by
    simpa only [comap_apply] using
      (step.comap (fun history : Fin (n + 1) → S => history (Fin.last n))
        (measurable_pi_apply _)).measurable_map_withInput (measurable_fin_snoc (n + 1))
  have h := congrArg (fun μ => μ.map append)
    (map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
      (X := fun _ : ℕ => S) (μ₀ := initial) (κ := historyStep step) (a := n))
  rw [Measure.map_compProd_eq_bind _ _ happend,
    Measure.map_map happend ((measurable_frestrictLe n).prodMk
      (measurable_pi_apply (n + 1)))] at h
  have hextend : append ∘ (fun path : ℕ → S => (Preorder.frestrictLe n path, path (n + 1))) =
      (fun path (i : Fin (n + 2)) => path i) := by
    funext path i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Function.comp_def, append, Fin.snoc_last, Fin.val_last]
    · simp only [Function.comp_def, append, Fin.snoc_castSucc, restrict,
        Preorder.frestrictLe_apply, Fin.val_castSucc]
  rw [hextend] at h
  rw [show (fun path : ℕ → S => fun i : Fin (n + 1) => path i) =
      restrict ∘ Preorder.frestrictLe n from rfl,
    ← Measure.map_map hrestrict (measurable_frestrictLe n),
    Measure.bind_map hrestrict.aemeasurable hmap.aemeasurable]
  exact h.symm

/-- A measurable almost-sure transition invariant holds at every step of the path. -/
theorem pathLaw_ae_rel (step : Kernel S S) [IsMarkovKernel step]
    (initial : Measure S) [IsProbabilityMeasure initial] (relation : S → S → Prop)
    (hrelation : MeasurableSet {pair : S × S | relation pair.1 pair.2})
    (hstep : ∀ state, ∀ᵐ next ∂step state, relation state next) :
    ∀ᵐ path ∂pathLaw step initial, ∀ n, relation (path n) (path (n + 1)) := by
  rw [ae_all_iff]
  intro n
  have hmeas : Measurable (fun pair : (Finset.Iic n → S) × S =>
      (pair.1 ⟨n, Finset.mem_Iic.mpr le_rfl⟩, pair.2)) :=
    ((measurable_pi_apply _).comp measurable_fst).prodMk measurable_snd
  have hlocal : ∀ᵐ pair ∂((pathLaw step initial).map (Preorder.frestrictLe n)) ⊗ₘ
      historyStep step n, relation (pair.1 ⟨n, Finset.mem_Iic.mpr le_rfl⟩) pair.2 :=
    Measure.ae_compProd_of_ae_ae (hmeas hrelation)
      (Filter.Eventually.of_forall fun history => hstep (history ⟨n, Finset.mem_Iic.mpr le_rfl⟩))
  rw [pathLaw, map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure] at hlocal
  exact ae_of_ae_map ((measurable_frestrictLe n).prodMk
    (measurable_pi_apply (n + 1))).aemeasurable hlocal

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

/-- Finite tuples suffice to bound variation on all infinite-path events. -/
theorem etvDist_le_of_fin_prefixes (μ ν : Measure (Π n, X n))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (ε : ℝ≥0∞)
    (h : ∀ n, (μ.map (fun path (i : Fin (n + 1)) => path i)).etvDist
      (ν.map (fun path (i : Fin (n + 1)) => path i)) ≤ ε) : μ.etvDist ν ≤ ε := by
  apply etvDist_le_of_prefixes μ ν ε
  intro n
  let restrict : (Π i : Fin (n + 1), X i) → (Π i : Finset.Iic n, X i) :=
    fun history i => history ⟨i, Nat.lt_succ_of_le (Finset.mem_Iic.mp i.property)⟩
  have hm : Measurable restrict := Measurable.of_eval fun _ => measurable_pi_apply _
  have heq : Preorder.frestrictLe n =
      restrict ∘ (fun path : Π n, X n => fun i : Fin (n + 1) => path i) := rfl
  rw [heq, ← Measure.map_map hm (Measurable.of_eval fun _ => measurable_pi_apply _),
    ← Measure.map_map hm (Measurable.of_eval fun _ => measurable_pi_apply _)]
  exact (etvDist_map_le _ _ _ hm).trans (h n)

/-- Equality of finite tuple laws determines the law on infinite paths. -/
theorem eq_of_fin_prefixes (μ ν : Measure (Π n, X n)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ n, μ.map (fun path (i : Fin (n + 1)) => path i) =
      ν.map (fun path (i : Fin (n + 1)) => path i)) : μ = ν := by
  apply etvDist_eq_zero_iff.mp
  apply le_antisymm _ bot_le
  exact etvDist_le_of_fin_prefixes μ ν 0 (fun n => by rw [h n, etvDist_self])

end MeasureTheory.Measure
