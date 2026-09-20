/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.OracleComp.Constructions.SampleableType.Basic
public import VCVio.OracleComp.EvalDist.Measure
public import ToMathlib.MeasureTheory.DiscreteInstances
import VCVio.EvalDist.Monad.Measure
import Mathlib.Logic.Equiv.Bool

/-!
# Native measure laws for uniform sampling constructions

Finite-range sampling and transport through an equivalence preserve the native
uniform output measure certified by `SampleableType`. Events of a uniform sample are counting
statements: comparisons with fractions of the sample space reduce to comparisons of counts,
probability one and zero are universal and empty events, and independent uniform draws combined
by a bijection are a single uniform draw. Every uniform sampler of a type denotes the same
measure, so statements about `$ᵗ α` do not depend on the chosen sampler.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SampleableType

/-- Every singleton of a uniform finite sample has the reciprocal cardinality mass. -/
@[simp↓ high, grind norm↓]
theorem evalDist_uniformSample_singleton {α : Type} [SampleableType α] [_root_.Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (x : α) :
    𝒟[($ᵗ α : ProbComp α)] {x} = (Fintype.card α : ENNReal)⁻¹ := by
  rw [evalDist_uniformSample, uniformOn_univ_apply_singleton]

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

/-! ## Counting events of a uniform sample -/

/-- A uniform sample satisfies an event with probability one exactly when every element does. -/
theorem prEvent_uniformSample_eq_one_iff {α : Type} [SampleableType α] (p : α → Prop) :
    Pr{let x ← $ᵗ α}[p x] = 1 ↔ ∀ x, p x := by
  rw [OracleComp.prEvent_eq_one_iff, support_uniformSample]
  simp

/-- A uniform sample satisfies an event with probability zero exactly when no element does. -/
theorem prEvent_uniformSample_eq_zero_iff {α : Type} [SampleableType α] (p : α → Prop) :
    Pr{let x ← $ᵗ α}[p x] = 0 ↔ ∀ x, ¬ p x := by
  rw [OracleComp.prEvent_eq_zero_iff, support_uniformSample]
  simp

/-- A uniform sample satisfies an event with positive probability exactly when some element
does. -/
theorem prEvent_uniformSample_pos_iff {α : Type} [SampleableType α] (p : α → Prop) :
    0 < Pr{let x ← $ᵗ α}[p x] ↔ ∃ x, p x := by
  rw [OracleComp.prEvent_pos_iff, support_uniformSample]
  simp

/-- The probability of drawing one particular element uniformly. -/
theorem prEvent_uniformSample_eq_singleton {α : Type} [SampleableType α] [_root_.Fintype α]
    (a : α) : Pr{let x ← $ᵗ α}[x = a] = (Fintype.card α : ℝ≥0∞)⁻¹ := by
  let : MeasurableSpace α := ⊤
  rw [prEvent_eq_evalDist_singleton, evalDist_uniformSample_singleton]

section counting

variable {α : Type} [SampleableType α] [_root_.Fintype α] (p : α → Prop) [DecidablePred p]

/-- A uniform event is below a fraction of the sample space exactly when the count is. -/
theorem prEvent_uniformSample_lt_div_iff {c : ℕ} :
    Pr{let x ← $ᵗ α}[p x] < c / (Fintype.card α : ℝ≥0∞) ↔
      (Finset.univ.filter p).card < c := by
  rw [prEvent_uniformSample, ENNReal.div_lt_div_iff_left (by simp) (by simp)]
  exact Nat.cast_lt

/-- A uniform event is at most a fraction of the sample space exactly when the count is. -/
theorem prEvent_uniformSample_le_div_iff {c : ℕ} :
    Pr{let x ← $ᵗ α}[p x] ≤ c / (Fintype.card α : ℝ≥0∞) ↔
      (Finset.univ.filter p).card ≤ c := by
  rw [← not_lt, prEvent_uniformSample, ENNReal.div_lt_div_iff_left (by simp) (by simp),
    Nat.cast_lt, not_lt]

/-- A fraction of the sample space is below a uniform event exactly when the count is. -/
theorem div_lt_prEvent_uniformSample_iff {c : ℕ} :
    c / (Fintype.card α : ℝ≥0∞) < Pr{let x ← $ᵗ α}[p x] ↔
      c < (Finset.univ.filter p).card := by
  rw [prEvent_uniformSample, ENNReal.div_lt_div_iff_left (by simp) (by simp)]
  exact Nat.cast_lt

/-- A fraction of the sample space is at most a uniform event exactly when the count is. -/
theorem div_le_prEvent_uniformSample_iff {c : ℕ} :
    c / (Fintype.card α : ℝ≥0∞) ≤ Pr{let x ← $ᵗ α}[p x] ↔
      c ≤ (Finset.univ.filter p).card := by
  rw [← not_lt, prEvent_uniformSample, ENNReal.div_lt_div_iff_left (by simp) (by simp),
    Nat.cast_lt, not_lt]

/-- A uniform event equals a fraction of the sample space exactly when the count does. -/
theorem prEvent_uniformSample_eq_div_iff {c : ℕ} :
    Pr{let x ← $ᵗ α}[p x] = c / (Fintype.card α : ℝ≥0∞) ↔
      (Finset.univ.filter p).card = c := by
  rw [le_antisymm_iff, prEvent_uniformSample_le_div_iff, div_le_prEvent_uniformSample_iff,
    le_antisymm_iff]

/-- A uniform event as a real-valued fraction. -/
theorem prEvent_uniformSample_eq_ofReal :
    Pr{let x ← $ᵗ α}[p x] =
      ENNReal.ofReal ((Finset.univ.filter p).card / Fintype.card α : ℝ) := by
  rw [prEvent_uniformSample, ENNReal.ofReal_div_of_pos (by exact_mod_cast Fintype.card_pos)]
  simp

end counting

/-! ## Transport between uniform samples -/

section transport

variable {α β γ : Type} [SampleableType α] [SampleableType β]

/-- Transport a uniform event along a bijection of sample spaces. -/
theorem prEvent_uniformSample_comp_of_bijective {f : α → β} (hf : Function.Bijective f)
    (p : β → Prop) :
    Pr{let x ← $ᵗ α}[p (f x)] = Pr{let y ← $ᵗ β}[p y] := by
  rw [← prEvent_map]
  refine prEvent_congr_of_evalDist_eq _ _ ?_ p
  let : MeasurableSpace α := ⊤
  let : MeasurableSpace β := ⊤
  rw [evalDist_map_of_discrete, evalDist_uniformSample, evalDist_uniformSample]
  exact map_uniformOn_univ_of_bijective Measurable.of_discrete hf

/-- Transport a uniform event along an equivalence of sample spaces. -/
theorem prEvent_uniformSample_equiv (e : α ≃ β) (p : β → Prop) :
    Pr{let x ← $ᵗ α}[p (e x)] = Pr{let y ← $ᵗ β}[p y] :=
  prEvent_uniformSample_comp_of_bijective e.bijective p

/-- Two independent uniform draws combined by a bijection are one uniform draw. -/
theorem prEvent_uniformSample_pair_of_bijective [SampleableType γ] {g : α → β → γ}
    (hg : Function.Bijective (Function.uncurry g)) (p : γ → Prop) :
    Pr{let x ← $ᵗ α; let y ← $ᵗ β}[p (g x y)] = Pr{let z ← $ᵗ γ}[p z] := by
  calc Pr{let x ← $ᵗ α; let y ← $ᵗ β}[p (g x y)]
      = Pr{let xy ← (do let x ← $ᵗ α; let y ← $ᵗ β; return (x, y))}[
          p (Function.uncurry g xy)] := by
        simp only [bind_assoc, pure_bind, Function.uncurry_apply_pair]
    _ = Pr{let z ← $ᵗ γ}[p z] := by
        rw [← prEvent_map]
        refine prEvent_congr_of_evalDist_eq _ _ ?_ p
        let : MeasurableSpace α := ⊤
        let : MeasurableSpace β := ⊤
        let : MeasurableSpace γ := ⊤
        rw [evalDist_map_of_discrete, evalDist_pair, evalDist_uniformSample,
          evalDist_uniformSample, evalDist_uniformSample, ← uniformOn_univ_prod]
        exact map_uniformOn_univ_of_bijective Measurable.of_discrete hg

/-- A uniform draw from a product is two independent uniform draws. -/
theorem prEvent_uniformSample_prod (p : α × β → Prop) :
    Pr{let z ← $ᵗ (α × β)}[p z] = Pr{let x ← $ᵗ α; let y ← $ᵗ β}[p (x, y)] :=
  (prEvent_uniformSample_pair_of_bijective (g := Prod.mk) Function.bijective_id p).symm

/-- The first coordinate of a uniform product draw is a uniform draw. -/
theorem prEvent_uniformSample_fst (p : α → Prop) :
    Pr{let z ← $ᵗ (α × β)}[p z.1] = Pr{let x ← $ᵗ α}[p x] := by
  rw [prEvent_uniformSample_prod]
  have h := prEvent_bind_bind_and ($ᵗ α) ($ᵗ β) p (fun _ ↦ True)
  simp only [and_true] at h
  rw [h, (prEvent_uniformSample_eq_one_iff (fun _ ↦ True)).mpr (fun _ ↦ trivial), mul_one]

/-- A uniform draw of a successor-indexed tuple is a uniform tuple followed by a uniform last
entry. -/
theorem prEvent_uniformSample_finSnoc {n : ℕ} (p : (_root_.Fin (n + 1) → α) → Prop) :
    Pr{let v ← $ᵗ (_root_.Fin (n + 1) → α)}[p v] =
      Pr{let w ← $ᵗ (_root_.Fin n → α); let x ← $ᵗ α}[p (Fin.snoc w x)] := by
  refine (prEvent_uniformSample_pair_of_bijective (g := fun w x ↦ Fin.snoc w x) ?_ p).symm
  refine ⟨fun a b hab ↦ ?_, fun v ↦ ⟨(Fin.init v, v (Fin.last n)), Fin.snoc_init_self v⟩⟩
  obtain ⟨w₁, x₁⟩ := a
  obtain ⟨w₂, x₂⟩ := b
  simp only [Function.uncurry_apply_pair] at hab
  have hw : w₁ = w₂ := by simpa using congrArg Fin.init hab
  have hx : x₁ = x₂ := by simpa using congrArg (fun v ↦ v (Fin.last n)) hab
  rw [hw, hx]

end transport

/-! ## Independence of the chosen sampler -/

section samplerIrrelevance

variable {α : Type}

/-- Every uniform sampler of a type denotes the same measure. -/
theorem evalDist_uniformSample_inst_irrel (i₁ i₂ : SampleableType α)
    [MeasurableSpace α] [MeasurableSingletonClass α] :
    𝒟[@uniformSample α i₁] = 𝒟[@uniformSample α i₂] := by
  rw [@evalDist_uniformSample α i₁, @evalDist_uniformSample α i₂]

/-- Every uniform sampler of a type assigns the same probability to every event. -/
theorem prEvent_uniformSample_inst_irrel (i₁ i₂ : SampleableType α) (p : α → Prop) :
    Pr{let x ← @uniformSample α i₁}[p x] = Pr{let x ← @uniformSample α i₂}[p x] := by
  let : MeasurableSpace α := ⊤
  rw [prEvent_eq_evalDist_of_discrete, prEvent_eq_evalDist_of_discrete,
    evalDist_uniformSample_inst_irrel]

end samplerIrrelevance

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
