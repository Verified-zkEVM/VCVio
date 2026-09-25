/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.EvalDist.ProbabilityNotation

/-!
# Measure semantics for applicative sequencing

Independent applicative pairs denote Mathlib product measures on arbitrary measurable spaces.
Discarding either output retains the successful mass of its computation as a scaling factor.
No operational support, discrete evaluator, or measurable structure on a function space is needed.
-/

public section

open MeasureTheory

universe u v

variable {m : Type u → Type v} [Monad m] [LawfulMonad m]
  [EvalDistSemantics m] [LawfulEvalDistSemantics m] {α β γ : Type u}

section
variable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

/-- Independently sampled applicative pairs have the product of their output measures. -/
@[simp high, grind norm]
theorem evalDist_seq_map_prod_mk (mx : m α) (my : m β) :
    𝒟[Prod.mk <$> mx <*> my] = 𝒟[mx].prod 𝒟[my] := by
  simpa only [seq_eq_bind_map, map_eq_bind_pure_comp, bind_assoc, Function.comp_def,
    pure_bind] using evalDist_pair mx my

/-- An applicative binary operation pushes its product law forward along the uncurried operation.
Only that operation's joint measurability is needed, without a measurable function space. -/
theorem evalDist_seq_map (mx : m α) (my : m β) (f : α → β → γ)
    (hf : Measurable (Function.uncurry f)) :
    𝒟[f <$> mx <*> my] = (𝒟[mx].prod 𝒟[my]).map (Function.uncurry f) := by
  have h : f <$> mx <*> my = Function.uncurry f <$> (Prod.mk <$> mx <*> my) := by
    simp [map_seq, Functor.map_map, Function.comp_def, Function.uncurry]
  rw [h, evalDist_map _ hf, evalDist_seq_map_prod_mk]

/-- Keeping the first result scales its measure by the second computation's successful mass. -/
@[simp high, grind norm]
theorem evalDist_seqLeft (mx : m α) (my : m β) :
    𝒟[mx <* my] = 𝒟[my] Set.univ • 𝒟[mx] := by
  have h : mx <* my = (Prod.fst : α × β → α) <$> (Prod.mk <$> mx <*> my) := by
    simp only [seqLeft_eq_bind, seq_eq_bind_map, map_eq_bind_pure_comp, Function.comp_def,
      bind_assoc, pure_bind]
  rw [h, evalDist_map _ measurable_fst, evalDist_seq_map_prod_mk, Measure.map_fst_prod]

/-- Keeping the second result scales its measure by the first computation's successful mass. -/
@[simp high, grind norm]
theorem evalDist_seqRight (mx : m α) (my : m β) :
    𝒟[mx *> my] = 𝒟[mx] Set.univ • 𝒟[my] := by
  rw [seqRight_eq_bind, evalDist_bind_const]

end

section
variable [MeasurableSpace β] [MeasurableSpace γ]

/-- Mapping the retained first output commutes with discarding the second output.
No measurable space or measurability obligation is needed for the intermediate first output. -/
@[simp high, grind norm]
theorem evalDist_map_seqLeft (mx : m α) (my : m β) (f : α → γ) :
    𝒟[f <$> (mx <* my)] = 𝒟[my] Set.univ • 𝒟[f <$> mx] := by
  have h : f <$> (mx <* my) = (f <$> mx) <* my := by
    simp only [seqLeft_eq_bind, map_eq_bind_pure_comp, Function.comp_def,
      bind_assoc, pure_bind]
  rw [h, evalDist_seqLeft]

end

section
variable [MeasurableSpace α] [MeasurableSpace γ]

/-- Mapping the retained second output commutes with discarding the first output.
No measurable space or measurability obligation is needed for the intermediate second output. -/
@[simp high, grind norm]
theorem evalDist_map_seqRight (mx : m α) (my : m β) (f : β → γ) :
    𝒟[f <$> (mx *> my)] = 𝒟[mx] Set.univ • 𝒟[f <$> my] := by
  have h : f <$> (mx *> my) = mx *> (f <$> my) := by
    simp only [seqRight_eq_bind, map_eq_bind_pure_comp, Function.comp_def, bind_assoc]
  rw [h, evalDist_seqRight]

end

section
variable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

/-- An independent applicative pair inherits losslessness from its factors. -/
instance evalDist.instIsProbabilityMeasureSeqMapProdMk (mx : m α) (my : m β)
    [IsProbabilityMeasure 𝒟[mx]] [IsProbabilityMeasure 𝒟[my]] :
    IsProbabilityMeasure 𝒟[Prod.mk <$> mx <*> my] := by
  rw [evalDist_seq_map_prod_mk]
  infer_instance

/-- Keeping the first of two lossless computations preserves its probability certificate. -/
instance evalDist.instIsProbabilityMeasureSeqLeft (mx : m α) (my : m β)
    [IsProbabilityMeasure 𝒟[mx]] [IsProbabilityMeasure 𝒟[my]] :
    IsProbabilityMeasure 𝒟[mx <* my] := by
  rw [evalDist_seqLeft, measure_univ, one_smul]
  infer_instance

/-- Keeping the second of two lossless computations preserves its probability certificate. -/
instance evalDist.instIsProbabilityMeasureSeqRight (mx : m α) (my : m β)
    [IsProbabilityMeasure 𝒟[mx]] [IsProbabilityMeasure 𝒟[my]] :
    IsProbabilityMeasure 𝒟[mx *> my] := by
  rw [evalDist_seqRight, measure_univ, one_smul]
  infer_instance

end

section events

universe v'

variable {m : Type → Type v'} [Monad m] [LawfulMonad m]
  [EvalDistSemantics m] [LawfulEvalDistSemantics m] {α β : Type}

/-- A final event about the first result retains the second computation's successful mass.
The retained result type needs no measurable-space argument. -/
@[grind norm]
theorem prEvent_seqLeft [MeasurableSpace β] (mx : m α) (my : m β) (p : α → Prop) :
    Pr{let x ← mx <* my}[p x] = 𝒟[my] Set.univ * Pr{let x ← mx}[p x] := by
  have h : (do let x ← mx <* my; return p x) = (do let x ← mx; return p x) <* my := by
    simp [seqLeft_eq_bind]
  rw [h, evalDist_seqLeft, Measure.smul_apply, smul_eq_mul]

/-- A final event about the second result retains the first computation's successful mass.
The retained result type needs no measurable-space argument. -/
@[grind norm]
theorem prEvent_seqRight [MeasurableSpace α] (mx : m α) (my : m β) (p : β → Prop) :
    Pr{let y ← mx *> my}[p y] = 𝒟[mx] Set.univ * Pr{let y ← my}[p y] := by
  rw [seqRight_eq_bind, bind_assoc, evalDist_bind_const, Measure.smul_apply, smul_eq_mul]

end events
