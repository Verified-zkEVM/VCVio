/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.OracleComp.EvalDist.UniformCompatibility
public import VCVio.OracleComp.OracleComp
public import VCVio.EvalDist.ProbabilityNotation
public import VCVio.EvalDist.BitVec.Measure
public import VCVio.EvalDist.IndepProductMeasure
public import VCVio.OracleComp.Constructions.UniformFinMeasure
public import VCVio.OracleComp.Constructions.ReplicateMeasure
public import VCVio.OracleComp.Constructions.SampleableType.NativeMeasure
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.GRewrite

/-!
# Measure-valued uniform oracle canaries

The canonical concrete uniform response certificates are resolved by typeclass synthesis.
Coin, finite-range, and bit-vector samplers exercise direct measure semantics.
-/

public section

open MeasureTheory ProbabilityTheory

namespace VCVioTest.UniformMeasureSpec

section DerivedMeasureSpec

variable {ι : Type} {spec : OracleSpec ι}
  [∀ t, MeasurableSpace (spec.Range t)]
  [∀ t, DiscreteMeasurableSpace (spec.Range t)] [OracleSpec.IsUniformSpec spec]

noncomputable example : OracleSpec.IsUniformMeasureSpec spec := inferInstance

end DerivedMeasureSpec

example : OracleSpec.IsMeasureSpec.toMeasure (spec := coinSpec) () =
    (uniformOn Set.univ : Measure Bool) :=
  OracleSpec.IsUniformMeasureSpec.toMeasure_eq_uniform ()

example : 𝒟[(pure true : OracleComp coinSpec Bool)] = Measure.dirac true := by
  simp

example : 𝒟[(HasQuery.query (spec := coinSpec) (m := OracleComp coinSpec) ())] =
    (uniformOn Set.univ : Measure Bool) := by
  simp

example (mx : OracleComp coinSpec Bool) :
    Pr{let b ← mx}[b] = 𝒟[mx] {true} := by
  rw [prEvent_eq_evalDist_of_discrete]
  simp

example (mx : OracleComp coinSpec Bool) (p q : Bool → Prop)
    (hpq : ∀ b, p b → q b) :
    Pr{let b ← mx}[p b] ≤ Pr{let b ← mx}[q b] := by
  rw [prEvent_eq_evalDist_of_discrete,
    prEvent_eq_evalDist_of_discrete]
  gcongr
  exact hpq _

example (mx : OracleComp coinSpec Bool) (p q : Bool → Prop)
    (hpq : ∀ b, p b → q b) :
    Pr{let b ← mx}[p b] ≤ Pr{let b ← mx}[q b] := by
  rw [prEvent_eq_evalDist_of_discrete,
    prEvent_eq_evalDist_of_discrete]
  have hset : {b | p b} ⊆ {b | q b} := Set.ofPred_subset_ofPred.mpr hpq
  grw [hset]

example : Pr{let b ← (pure true : OracleComp coinSpec Bool)}[b] = 1 := by
  simp

example (mx : OracleComp coinSpec (BitVec 1)) (msg : BitVec 1)
    (huniform : 𝒟[mx] = uniformOn Set.univ) :
    𝒟[(fun key : BitVec 1 => key ^^^ msg) <$> mx] = uniformOn Set.univ :=
  evalDist_xor_uniform_right mx msg huniform

example (n : ℕ) :
    𝒟[ProbComp.uniformFin n] = uniformOn Set.univ := by
  simp

example (n : ℕ) :
    𝒟[$ᵗ BitVec n] = uniformOn Set.univ := by
  exact SampleableType.evalDist_finEnum

example (n m : ℕ) :
    𝒟[$ᵗ (BitVec n × BitVec m)] = uniformOn Set.univ :=
  SampleableType.evalDist_prod

example (n : ℕ) (p : Fin (n + 1) → Prop) [DecidablePred p] :
    Pr{let x ← ProbComp.uniformFin n}[p x] =
      ((Finset.univ.filter p).card : ENNReal) / (n + 1) :=
  ProbComp.prEvent_uniformFin n p

example (g : Fin 3 → ProbComp Bool) :
    𝒟[Fin.mOfFn 3 g] = Measure.pi fun i => 𝒟[g i] :=
  evalDist_mOfFn 3 g

example (g : Fin 3 → ProbComp Bool) : 𝒟[Fin.mOfFn 3 g] Set.univ = 1 := by
  simp

section repeatedSampling

local instance : MeasurableSpace (List Bool) := ⊤

example (mx : OracleComp coinSpec Bool) (n : ℕ) :
    𝒟[mx.replicate n] Set.univ = (𝒟[mx] Set.univ) ^ n := by simp

end repeatedSampling

example (g : Bool → ProbComp Bool) (i : Bool) :
    (𝒟[Fintype.mPi g]).map (Function.eval i) = 𝒟[g i] :=
  evalDist_map_eval_mPi g (fun j => OracleComp.evalDist_apply_univ_eq_one (g j)) i

end VCVioTest.UniformMeasureSpec
