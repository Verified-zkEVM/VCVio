/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.OracleComp.Constructions.SampleableType
public import ToMathlib.MeasureTheory.DiscreteInstances
import VCVio.EvalDist.Monad.Measure
import Mathlib.Logic.Equiv.Bool

/-!
# Native measure laws for uniform sampling constructions

Finite-range sampling and transport through an equivalence preserve the native
uniform output measure certified by `SampleableType`.
-/

public section

open MeasureTheory ProbabilityTheory

namespace SampleableType

/-- A uniform finite sample satisfies a decidable event with its accepted fraction of outputs. -/
@[simp↓ high, grind norm↓]
theorem prEvent_uniformSample {α : Type} [SampleableType α] [_root_.Fintype α]
    (p : α → Prop) [DecidablePred p] :
    Pr{let x ← $ᵗ α}[p x] = (Finset.univ.filter p).card / (Fintype.card α : ENNReal) := by
  classical
  let : MeasurableSpace α := ⊤
  rw [prEvent_eq_evalDist_of_discrete, SampleableType.evalDist_uniformSample, uniformOn_univ]
  have hset : {x | p x} = (Finset.univ.filter p : Finset α) := by ext x; simp
  rw [hset, Measure.count_apply_finset]

/-- The finite sampler directly denotes a uniform measure. -/
theorem evalDist_fin (n : ℕ) :
    𝒟[(SampleableType.Fin n).selectElem] = uniformOn Set.univ :=
  (SampleableType.Fin n).evalDist_selectElem_eq_uniform

/-- A sample from any nonempty `Fin n` denotes its uniform measure. -/
theorem evalDist_fin_neZero (n : ℕ) [NeZero n] :
    𝒟[$ᵗ (_root_.Fin n)] = uniformOn Set.univ := by
  exact SampleableType.evalDist_uniformSample

/-- Transporting a uniformly distributed sampler through an equivalence stays uniform. -/
theorem evalDist_ofEquiv {α β : Type} [SampleableType α]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (e : α ≃ β) :
    𝒟[(SampleableType.ofEquiv e).selectElem] = uniformOn Set.univ :=
  (SampleableType.ofEquiv e).evalDist_selectElem_eq_uniform

/-- Finite enumeration gives a native uniform sampler. -/
theorem evalDist_finEnum {α : Type} [h : FinEnum α] [_root_.Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] :
    𝒟[(FinEnum.SampleableType α).selectElem] = uniformOn Set.univ :=
  (FinEnum.SampleableType α).evalDist_selectElem_eq_uniform

/-- Independent uniform samples give the uniform measure on a product type. -/
theorem evalDist_prod {α β : Type} [SampleableType α] [SampleableType β]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace β] [MeasurableSingletonClass β] :
    𝒟[$ᵗ (α × β)] = uniformOn Set.univ :=
  SampleableType.evalDist_uniformSample

/-- A sampled bit vector has the native uniform measure. -/
@[simp]
theorem evalDist_bitVec (n : ℕ) :
    𝒟[$ᵗ BitVec n] = uniformOn Set.univ :=
  SampleableType.evalDist_uniformSample

end SampleableType

namespace ProbComp

open OracleComp OracleSpec ENNReal

/-- Complementing a fair hidden bit does not change the measure of any subsequent computation. -/
theorem evalDist_bind_not_uniformBool {α : Type} [MeasurableSpace α]
    (f : Bool → ProbComp α) :
    𝒟[do let b ← ($ᵗ Bool); f (!b)] = 𝒟[do let b ← ($ᵗ Bool); f b] :=
  evalDist_bind_bijective_of_uniform ($ᵗ Bool : ProbComp Bool)
    SampleableType.evalDist_uniformSample Bool.not Bool.not_bijective f

/-- A fair hidden bit is guessed with probability one half when the guess distribution does not
depend on that bit. -/
theorem evalDist_decide_eq_uniformBool_half
    (f : Bool → ProbComp Bool) (heq : 𝒟[f true] = 𝒟[f false]) :
    𝒟[do let b ← ($ᵗ Bool); let b' ← f b; return decide (b = b')] {true} = 1 / 2 := by
  have hinner (b : Bool) :
      𝒟[do let b' ← f b; return decide (b = b')] {true} = 𝒟[f b] {b} := by
    rw [← prEvent_eq_evalDist_decide (mx := f b) (p := fun b' => b = b'),
      prEvent_eq_evalDist_of_discrete]
    congr 1
    ext x
    simp [eq_comm]
  change 𝒟[($ᵗ Bool : ProbComp Bool) >>= fun b => do
    let b' ← f b
    return decide (b = b')] {true} = _
  rw [evalDist_bind_of_discrete,
    Measure.bind_apply (measurableSet_singleton true) (Measurable.of_discrete).aemeasurable]
  simp_rw [hinner]
  rw [lintegral_fintype, Fintype.sum_bool, heq]
  have hbool : 𝒟[($ᵗ Bool : ProbComp Bool)] = uniformOn Set.univ :=
    SampleableType.evalDist_uniformSample
  rw [hbool]
  simp only [uniformOn_univ_apply_singleton, Fintype.card_bool]
  have hmass : 𝒟[f false] {true} + 𝒟[f false] {false} = 1 := by
    have hprob : 𝒟[f false] Set.univ = 1 :=
      OracleComp.evalDist_apply_univ_eq_one (f false)
    have hset : (Set.univ : Set Bool) = {true} ∪ {false} := by
      ext b
      cases b <;> simp
    rw [hset, measure_union (by simp) (measurableSet_singleton false)] at hprob
    exact hprob
  rw [← add_mul, hmass]
  norm_num

end ProbComp
