/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.OracleComp.Constructions.SampleableType
public import VCVio.OracleComp.Constructions.UniformFinMeasure
public import ToMathlib.MeasureTheory.Measure.UniformTable
public import ToMathlib.MeasureTheory.DiscreteInstances

/-!
# Native measure laws for uniform sampling constructions

Finite-range sampling and transport through an equivalence preserve the native
uniform output measure. The hypotheses select an explicit measure interpretation
for the uniform oracle.
-/

public section

open MeasureTheory ProbabilityTheory

namespace SampleableType

/-- The finite sampler directly denotes a uniform measure. -/
theorem evalDist_fin [OracleSpec.IsUniformMeasureSpec unifSpec] (n : ℕ) :
    𝒟[(SampleableType.Fin n).selectElem] = uniformOn Set.univ := by
  change 𝒟[ProbComp.uniformFin n] = _
  exact ProbComp.evalDist_uniformFin n

/-- A sample from any nonempty `Fin n` denotes its uniform measure. -/
theorem evalDist_fin_neZero [OracleSpec.IsUniformMeasureSpec unifSpec]
    (n : ℕ) [NeZero n] :
    𝒟[$ᵗ (_root_.Fin n)] = uniformOn Set.univ := by
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n =>
      change 𝒟[(SampleableType.Fin n).selectElem] = _
      exact evalDist_fin n

/-- Transporting a uniformly distributed sampler through an equivalence stays uniform. -/
theorem evalDist_ofEquiv {α β : Type} [SampleableType α] [_root_.Finite β]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    [OracleSpec.IsUniformMeasureSpec unifSpec]
    (e : α ≃ β) (h : 𝒟[$ᵗ α] = uniformOn Set.univ) :
    𝒟[(SampleableType.ofEquiv e).selectElem] = uniformOn Set.univ := by
  change 𝒟[e <$> ($ᵗ α)] = _
  rw [evalDist_map_of_discrete, h]
  exact uniformOn_univ_map_equiv e

/-- Finite enumeration gives a native uniform sampler. -/
theorem evalDist_finEnum {α : Type} [h : FinEnum α] [_root_.Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [OracleSpec.IsUniformMeasureSpec unifSpec] :
    𝒟[(FinEnum.SampleableType α).selectElem] = uniformOn Set.univ := by
  have : NeZero (FinEnum.card α) := ⟨FinEnum.card_ne_zero⟩
  change 𝒟[(SampleableType.ofEquiv h.equiv.symm).selectElem] = _
  exact evalDist_ofEquiv h.equiv.symm (evalDist_fin_neZero (FinEnum.card α))

/-- Independent uniform samples give the uniform measure on a product type. -/
theorem evalDist_prod {α β : Type} [SampleableType α] [SampleableType β]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    [OracleSpec.IsUniformMeasureSpec unifSpec]
    (hα : 𝒟[$ᵗ α] = uniformOn Set.univ)
    (hβ : 𝒟[$ᵗ β] = uniformOn Set.univ) :
    𝒟[$ᵗ (α × β)] = uniformOn Set.univ := by
  change 𝒟[(·, ·) <$> ($ᵗ α) <*> ($ᵗ β)] = _
  have hseq : ((·, ·) <$> ($ᵗ α) <*> ($ᵗ β) : ProbComp (α × β)) =
      (do let a ← $ᵗ α; let b ← $ᵗ β; return (a, b)) := by
    simp [monad_norm]
  rw [hseq, evalDist_pair, hα, hβ]
  exact uniformOn_univ_prod.symm

/-- A sampled bit vector has the native uniform measure. -/
@[simp]
theorem evalDist_bitVec [OracleSpec.IsUniformMeasureSpec unifSpec] (n : ℕ) :
    𝒟[$ᵗ BitVec n] = uniformOn Set.univ :=
  evalDist_finEnum

end SampleableType

namespace ProbComp

open OracleComp OracleSpec ENNReal

/-- A fair hidden bit is guessed with probability one half when the guess distribution does not
depend on that bit. -/
theorem evalDist_decide_eq_uniformBool_half [OracleSpec.IsUniformMeasureSpec unifSpec]
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
    SampleableType.evalDist_finEnum
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
