/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.OracleComp.EvalDist.Measure
public import VCVio.OracleComp.EvalDist.AnswerMeasure
public import VCVio.OracleComp.OracleComp
public import VCVio.EvalDist.ProbabilityNotation
public import VCVio.EvalDist.BitVec.Measure
public import VCVio.EvalDist.IndepProductMeasure
public import VCVio.OracleComp.Constructions.UniformFinMeasure
public import VCVio.OracleComp.Constructions.ReplicateMeasure
public import VCVio.OracleComp.Constructions.SampleableType.Measure
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.GRewrite

/-!
# Measure-valued uniform oracle canaries

The canonical concrete uniform response certificates are resolved by typeclass synthesis.
Coin, finite-range, and bit-vector samplers exercise direct measure semantics. Two injections of
a uniform draw give one distribution to a continuation that ignores the points they do not both
cover, and not otherwise.
-/

public section

open MeasureTheory ProbabilityTheory

namespace VCVioTest.UniformAnswerMeasure

/-! ### One measure semantics per specification

Every instance path to the measure semantics of `ProbComp`, and to the answer measures of a sum
of the built-in specifications, agrees at instance transparency, so `rw` and `simp` never meet two
spellings of one instance. -/

example : (inferInstance : EvalDistSemantics ProbComp) =
    @OracleComp.instEvalDistSemantics ℕ unifSpec
      OracleSpec.UniformAnswerMeasure.unifSpec.toAnswerMeasure := by
  with_reducible_and_instances rfl

example : (inferInstance : OracleSpec.AnswerMeasure (unifSpec + coinSpec)) =
    OracleSpec.AnswerMeasure.add (spec := unifSpec) coinSpec := by
  with_reducible_and_instances rfl

example : (inferInstance : OracleSpec.AnswerMeasure (unifSpec + coinSpec)) =
    (OracleSpec.UniformAnswerMeasure.add (spec := unifSpec) coinSpec).toAnswerMeasure := by
  with_reducible_and_instances rfl

example : OracleSpec.AnswerMeasure.toMeasure (spec := coinSpec) () =
    (uniformOn Set.univ : Measure Bool) :=
  OracleSpec.UniformAnswerMeasure.toMeasure_eq_uniform ()

example : 𝒟[(pure true : OracleComp coinSpec Bool)] = Measure.dirac true := by
  simp

example : 𝒟[(HasQuery.query (spec := coinSpec) (m := OracleComp coinSpec) ())] =
    (uniformOn Set.univ : Measure Bool) :=
  OracleComp.evalDist_query_uniform (spec := coinSpec) ()

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

/-! ### Coupling uniform draws through two injections -/

/-- The identity and negation on `Bool` both cover every point, so a continuation sees the same
distribution through either. -/
example (k : Bool → ProbComp Bool) :
    (do let a ← $ᵗ Bool; k (id a)) =ᵈ (do let a ← $ᵗ Bool; k (!a)) :=
  SampleableType.uniformSample_bind_evalDistEq_of_cover (S := Set.univ)
    Function.injective_id (fun a b h => by simpa using h)
    (fun b _ => ⟨b, rfl⟩) (fun b _ => ⟨!b, Bool.not_not b⟩) k (pure true)
    (fun b hb => absurd (Set.mem_univ b) hb)

/-- `SampleableType.uniformSample_bind_evalDistEq_of_cover` needs the continuation to ignore its
argument outside the covered set. Both injections below, `a ↦ a.toNat` and `a ↦ a.toNat + 1`,
cover `{1}`, but the continuation tests for `0`, which only the first reaches, and the two
distributions differ. -/
example :
    Pr{let x ← (do let a ← $ᵗ Bool; pure (decide (a.toNat = 0)) : ProbComp Bool)}[x = true] ≠
      Pr{let x ← (do
        let a ← $ᵗ Bool
        pure (decide (a.toNat + 1 = 0)) : ProbComp Bool)}[x = true] := by
  simp [SampleableType.prEvent_uniformSample]

end VCVioTest.UniformAnswerMeasure
