/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import VCVio

/-!
# The measure gate

Goal families about the output measure `𝒟[…]`, each closed by one terminal tactic, following the
conventions of `docs/agents/probability.md` (*Normal forms and the tactic contract*). The contract
it pins is that `simp` keeps the measure side in measure normal form: singleton, event and total
masses stay `𝒟[mx] s`, and integrals against `𝒟[mx]` keep their measure-theoretic normal form. The
Giry laws for `bind`/`map` stay out of default `simp`, and the integral form of a bind is an
intermediate, not a target.

The entries run on `ProbComp`, whose uniform answer measures are built in, and on
`OptionT ProbComp`, where failure is missing mass. The total-mass entries use `Fin 3` rather than
`Bool` because Mathlib's `simp` rewrites `(Set.univ : Set Bool)` to the literal `{false, true}`
before any `𝒟`-keyed lemma can see it.
-/

public section

open MeasureTheory OracleComp OracleSpec
open scoped ENNReal

namespace VCVioTest.MeasureBridge

/-! ## Successful-output measure normalization -/

example {α : Type} [MeasurableSpace α] (μ : Measure α) :
    (μ.map some).dropNone = μ := by simp

/-! ## Operational optional failure -/

example {r : Type → Type} [Monad r] [LawfulMonad r] [MonadAttach r]
    [ExactMonadAttach r] : HasEvalSet.LawfulFailure (OptionT r) := inferInstance

example {r : Type → Type} [Monad r] [LawfulMonad r] [MonadAttach r]
    [ExactMonadAttach r] {α : Type} : support (failure : OptionT r α) = ∅ := by simp

/-! ## `ProbComp` -/

example (x : Bool) : 𝒟[(pure x : ProbComp Bool)] = Measure.dirac x := by simp
example (x : Bool) : 𝒟[(pure x : ProbComp Bool)] {x} = 1 := by simp

example (mx : ProbComp (Fin 2)) (my : ProbComp (Fin 3)) (y : Fin 3) :
    𝒟[mx >>= fun _ => my] {y} = 𝒟[my] {y} := by simp
example (mx : ProbComp Bool) (my : ProbComp (Fin 3)) :
    𝒟[mx >>= fun _ => my] = 𝒟[mx] Set.univ • 𝒟[my] := by simp

/-- The ladder's finite rung: expanding a bind on a `Fintype` lands on a finite sum through
Mathlib's `lintegral_fintype`. -/
example (mx : ProbComp Bool) (f : Bool → ProbComp (Fin 3)) (y : Fin 3) :
    𝒟[mx >>= f] {y} = ∑ x, 𝒟[mx] {x} * 𝒟[f x] {y} := by
  rw [evalDist_bind_of_discrete,
    Measure.bind_apply MeasurableSet.of_discrete Measurable.of_discrete.aemeasurable,
    lintegral_fintype]
  simp [mul_comm]

/-- The Giry bind law is a `rw`/`exact` target, not a simp rule. -/
example (mx : ProbComp Bool) (f : Bool → ProbComp (Fin 3)) :
    𝒟[mx >>= f] = 𝒟[mx].bind fun x => 𝒟[f x] := by
  fail_if_success simp  -- by design: bind expansion is not default simp
  exact evalDist_bind_of_discrete mx f

/-- The integral form of a bind is an intermediate, not a target: `simp` neither produces nor
closes it. -/
example (mx : ProbComp Bool) (f : Bool → ProbComp (Fin 3)) (s : Set (Fin 3)) :
    𝒟[mx >>= f] s = ∫⁻ x, 𝒟[f x] s ∂𝒟[mx] := by
  fail_if_success simp  -- by design: the integral form is not a normal form
  rw [evalDist_bind_of_discrete,
    Measure.bind_apply MeasurableSet.of_discrete Measurable.of_discrete.aemeasurable]

/-! ## `OptionT ProbComp`: failure mass is visible -/

example (mx : OptionT ProbComp Bool) (my : OptionT ProbComp (Fin 3)) :
    𝒟[mx >>= fun _ => my] = 𝒟[mx] Set.univ • 𝒟[my] := by simp

/-! ## Independent products are product measures -/

section repeatedSampling

local instance : MeasurableSpace (List Bool) := ⊤

/-- Repeated sampling computes its mass through Mathlib's measure bind. -/
example (oa : ProbComp Bool) (n : ℕ) :
    𝒟[oa.replicate n] Set.univ = (𝒟[oa] Set.univ) ^ n := by simp
example (oa : ProbComp Bool) (n : ℕ) :
    𝒟[oa.replicate n] Set.univ = (𝒟[oa] Set.univ) ^ n := by grind

end repeatedSampling

example (g : Fin 3 → ProbComp Bool) : 𝒟[Fin.mOfFn 3 g] = Measure.pi fun i => 𝒟[g i] :=
  evalDist_mOfFn 3 g
example (f : Bool → ProbComp (Fin 3)) : 𝒟[Fintype.mPi f] = Measure.pi fun i => 𝒟[f i] :=
  evalDist_mPi f
example (n : ℕ) :
    𝒟[Fin.mOfFn n (fun _ => ($ᵗ Bool : ProbComp Bool))] =
      ProbabilityTheory.uniformOn Set.univ :=
  evalDist_mOfFn_const_uniform n ($ᵗ Bool : ProbComp Bool)
    (SampleableType.evalDist_finEnum (α := Bool))
example :
    𝒟[Fintype.mPi (fun _ : Fin 3 => ($ᵗ Bool : ProbComp Bool))] =
      ProbabilityTheory.uniformOn Set.univ :=
  evalDist_mPi_const_uniform ($ᵗ Bool : ProbComp Bool)
    (SampleableType.evalDist_finEnum (α := Bool))
example (f : Bool → ProbComp (Fin 3)) (v : Bool → Fin 3) :
    𝒟[Fintype.mPi f] {v} = ∏ i, 𝒟[f i] {v i} := by
  simp [evalDist_mPi]

/-- A coordinate marginal of a lossless independent family recovers its factor. -/
example (f : Bool → ProbComp (Fin 3)) (i : Bool) :
    (𝒟[Fintype.mPi f]).map (Function.eval i) = 𝒟[f i] :=
  evalDist_map_eval_mPi f (fun _ => by simp) i
example (f : Bool → ProbComp (Fin 3)) (i : Bool) :
    (𝒟[Fintype.mPi f]).map (Function.eval i) = 𝒟[f i] := by
  simp [evalDist_mPi, Measure.pi_map_eval]

/-- The empty product carries unit mass. -/
def emptyFamily : Fin 0 → ProbComp Bool := fun i => i.elim0

example : 𝒟[Fin.mOfFn 0 emptyFamily] Set.univ = 1 := by
  simp [evalDist_mOfFn]

/-- A product family with one successful coordinate and one failing coordinate. -/
def familyWithFailure : Bool → OptionT ProbComp Bool
  | false => pure false
  | true => failure

example : 𝒟[Fintype.mPi familyWithFailure] Set.univ = 0 := by
  have hfail : 𝒟[familyWithFailure true] Set.univ = 0 := by
    simp [familyWithFailure]
  rw [evalDist_mPi, Measure.pi_univ, Fintype.prod_bool, hfail, zero_mul]

example : (𝒟[Fintype.mPi familyWithFailure]).map (Function.eval false) = 0 := by
  have hfail : 𝒟[familyWithFailure true] Set.univ = 0 := by
    simp [familyWithFailure]
  have hmem : true ∈ (Finset.univ.erase false : Finset Bool) := by simp
  have hprod : ∏ j ∈ Finset.univ.erase false, 𝒟[familyWithFailure j] Set.univ = 0 :=
    Finset.prod_eq_zero hmem hfail
  rw [evalDist_mPi, Measure.pi_map_eval, hprod, zero_smul]

example : 𝒟[familyWithFailure false] ≠ 0 := by
  simp [familyWithFailure]

/-! ## Failure is missing mass -/

example : 𝒟[(failure : OptionT ProbComp Bool)] = 0 := by simp
example (mx : OptionT ProbComp Bool) : evalDistWithFailure mx {none} = 1 - 𝒟[mx] Set.univ :=
  evalDistWithFailure_none mx
example (mx : ProbComp Bool) : IsProbabilityMeasure 𝒟[mx] := inferInstance
example (mx : ProbComp (Fin 3)) (f : Fin 3 → ProbComp (Fin 2)) : 𝒟[mx >>= f] Set.univ = 1 := by
  simp

/-- A lossy computation that succeeds exactly on the `true` outcome of a fair coin. -/
def lossyCoin : OptionT ProbComp Bool := do
  let b ← $ᵗ Bool
  if b then pure true else failure

example : Pr{lossyCoin}[= true] = 2⁻¹ := by
  rw [lossyCoin, prEvent_bind_eq_lintegral_of_discrete]
  simp [lintegral_fintype]
example : Pr{lossyCoin}[= false] = 0 := by
  rw [lossyCoin, prEvent_bind_eq_lintegral_of_discrete]
  simp [lintegral_fintype]
example : Pr{_ ← lossyCoin}[True] = 2⁻¹ := by
  rw [lossyCoin, prEvent_bind_eq_lintegral_of_discrete]
  simp [lintegral_fintype]

/-! ## A unit-test program

A coin and a die drawn independently. The point probability is the product of the two uniform
masses (the closed form `simp` reaches; merging `2⁻¹ * 6⁻¹` into `12⁻¹` is `ℝ≥0∞` arithmetic, not a
probability rule), and the failure-side facts need nothing beyond the program never failing. -/

/-- A coin and a die, drawn independently. -/
def coinDie : ProbComp (Bool × Fin 6) := do
  let b ← $ᵗ Bool
  let d ← $ᵗ (Fin 6)
  pure (b, d)

example : Pr{coinDie}[= (true, 0)] = 2⁻¹ * 6⁻¹ := by simp [coinDie, Finset.filter_eq']
example : 𝒟[coinDie] Set.univ = 1 := by simp
example : evalDistWithFailure coinDie {none} = 0 := by simp [evalDistWithFailure_none]
example : IsProbabilityMeasure 𝒟[coinDie] := inferInstance

end VCVioTest.MeasureBridge
