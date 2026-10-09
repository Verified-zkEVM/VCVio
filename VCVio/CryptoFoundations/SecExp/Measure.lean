/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module

public import ToMathlib.MeasureTheory.Measure.Bool
public import VCVio.EvalDist.Defs.Semantics.Core
public import VCVio.EvalDist.MeasureTVDist.Basic
public import VCVio.EvalDist.Monad.Measure
public import VCVio.EvalDist.Monad.Bool
public import VCVio.OracleComp.Constructions.SampleableType.NativeMeasure

/-!
# Boolean hidden-bit experiments

A hidden-bit experiment over a uniform bit has the Boolean bias of `𝒟` equal to the Boolean
distance of its two branches. Advantages of `ProbComp Bool` experiments are
`Measure.boolBias` and `Measure.boolDist` of their `𝒟` measures.
-/

public section

open MeasureTheory OracleComp

/-- Hidden-bit guessing over a uniform bit has the Boolean distance of its two branches. -/
lemma evalDist_boolBias_bind_uniformBool (real rand : ProbComp Bool) :
    𝒟[do
      let b ← ($ᵗ Bool)
      let z ← if b then real else rand
      pure (b == z)].boolBias = 𝒟[real].boolDist 𝒟[rand] :=
  evalDist_boolBias_bind_coin ($ᵗ Bool : ProbComp Bool) real rand (by simp) (by simp)
