/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import Mathlib.Probability.HasCondDistrib
public import Mathlib.Probability.Independence.Conditional

/-!
# Public-view simulators and conditional independence

A supplied kernel simulates leakage from the permitted public view alone. Its correctness law
retains the secret alongside the public view, so it states absence of additional secret
information, rather than just equality of leakage marginals. Measurable postprocessing preserves
this property. Standard Borel assumptions enter only in the bridge to Mathlib's conditional
independence, whose definition uses a regular conditional distribution.

These are distributional assertions. A simulator kernel need not have an efficient executable
realization; cryptographic efficiency certificates remain a separate obligation.
-/

public section

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory

variable {Ω Secret Public Leak : Type*} [MeasurableSpace Ω] [MeasurableSpace Secret]
  [MeasurableSpace Public] [MeasurableSpace Leak]

/-- The named simulator reproduces leakage given the public view, even with the secret retained. -/
def SimulatesView (secret : Ω → Secret) (publicView : Ω → Public) (leak : Ω → Leak)
    (sim : Kernel Public Leak) (μ : Measure Ω) : Prop :=
  HasCondDistrib leak (fun ω => (publicView ω, secret ω)) (sim.prodMkRight Secret) μ

namespace SimulatesView

variable {secret : Ω → Secret} {publicView : Ω → Public} {leak : Ω → Leak}
  {sim : Kernel Public Leak} {μ : Measure Ω} [SFinite μ] [IsSFiniteKernel sim]

/-- Forgetting the secret recovers the simulator's conditional law given the public view. -/
theorem public_law (h : SimulatesView secret publicView leak sim μ) :
    HasCondDistrib leak publicView sim μ :=
  h.comp_right (hf := measurable_fst)

/-- Any measurable processing of the leakage is simulated by the corresponding kernel map. -/
theorem postprocess {L : Type*} [MeasurableSpace L]
    (h : SimulatesView secret publicView leak sim μ) {f : Leak → L} (hf : Measurable f) :
    SimulatesView secret publicView (f ∘ leak) (sim.map f) μ := by
  unfold SimulatesView
  rw [← Kernel.map_prodMkRight]
  exact h.comp_left hf

end SimulatesView

/-- Independence from the entire public/secret pair gives a constant named simulator. -/
theorem SimulatesView.of_indepFun {secret : Ω → Secret} {publicView : Ω → Public}
    {leak : Ω → Leak} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hsecret : Measurable secret) (hpublic : Measurable publicView) (hleak : Measurable leak)
    (h : IndepFun (fun ω => (publicView ω, secret ω)) leak μ)
    (ν : Measure Leak) [SFinite ν] (hlaw : μ.map leak = ν) :
    SimulatesView secret publicView leak (Kernel.const Public ν) μ := by
  unfold SimulatesView
  have hk : (Kernel.const Public ν).prodMkRight Secret = Kernel.const (Public × Secret) ν := by
    ext x : 1
    rfl
  rw [hk]
  refine ⟨((hpublic.prodMk hsecret).prodMk hleak).aemeasurable, ?_⟩
  rw [Measure.compProd_const,
    h.map_prod_eq_prod_map_map (hpublic.prodMk hsecret).aemeasurable hleak.aemeasurable, hlaw]

/-- A public-view simulator implies conditional independence of secret and leakage.
The identities of regular conditional laws are only almost everywhere. -/
theorem SimulatesView.condIndepFun [StandardBorelSpace Ω]
    [StandardBorelSpace Secret] [Nonempty Secret] [StandardBorelSpace Leak] [Nonempty Leak]
    {secret : Ω → Secret} {publicView : Ω → Public} {leak : Ω → Leak}
    {sim : Kernel Public Leak} [IsMarkovKernel sim] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hsecret : Measurable secret) (hpublic : Measurable publicView) (hleak : Measurable leak)
    (h : SimulatesView secret publicView leak sim μ) : secret ⟂ᵢ[publicView, hpublic; μ] leak := by
  rw [condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight hleak hsecret hpublic]
  have hfull := condDistrib_ae_eq_of_measure_eq_compProd
    (hpublic.prodMk hsecret).aemeasurable hleak.aemeasurable h.map_eq
  have hpub := condDistrib_ae_eq_of_measure_eq_compProd
    hpublic.aemeasurable hleak.aemeasurable h.public_law.map_eq
  have hpull : ∀ᵐ pair ∂μ.map (fun ω => (publicView ω, secret ω)),
      condDistrib leak publicView μ pair.1 = sim pair.1 := by
    apply ae_of_ae_map (μ := μ.map (fun ω => (publicView ω, secret ω)))
      (f := Prod.fst) (p := fun v => condDistrib leak publicView μ v = sim v)
      measurable_fst.aemeasurable
    rwa [Measure.map_map measurable_fst (hpublic.prodMk hsecret)]
  filter_upwards [hfull, hpull] with pair hf hp
  simpa only [Kernel.prodMkRight_apply] using hf.trans hp.symm

end ProbabilityTheory
