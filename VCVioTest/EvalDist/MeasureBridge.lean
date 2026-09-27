/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import VCVio
public import VCVio.OracleComp.Constructions.SampleableType.MeasureCompatibility

/-!
# The measure gate

The measure-side counterpart of `VCVioTest/ProbabilityTactics.lean`: goal families about the
primary measure `𝒟[…]`, each closed by one terminal tactic, following the conventions of
`CONTRIBUTING.md` (*Tactic Gate Files*). The contract it pins is that on a discrete carrier the
measure side reduces *into* the discrete façade: singleton, event and total masses become
`Pr[…]`, and an integral against `𝒟[mx]` becomes `expectedValue mx g`, after which the façade's
own `simp`/`grind` contract applies inside `ProbComp.DiscreteCompatibility`. Native integrals
retain their measure-theoretic normal form; their calibration equations are explicit.
The Giry laws for `bind`/`map` stay out of default `simp`
on both sides, and the integral form of a bind is an intermediate, not a target.

The adapter checks open `ProbComp.DiscreteCompatibility` explicitly. Other entries exercise the
native free-monad fold, a local `IsProbabilitySpec.toMeasureSpec`, and `OptionT ProbComp`,
where failure mass is visible; these interpretations satisfy `DiscreteEvalDistCompatible` at
their compatibility boundaries. The total-mass
entries use `Fin 3` rather than `Bool` because Mathlib's `simp` rewrites `(Set.univ : Set Bool)`
to the literal `{false, true}` before any `𝒟`-keyed lemma can see it.
-/

public section

open MeasureTheory OracleComp OracleSpec OracleComp.EvalDist
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

/-! ## Adapter side: `ProbComp` with no measure specification -/

section adapter
open scoped ProbComp.DiscreteCompatibility

example (mx : ProbComp Bool) (x : Bool) : 𝒟[mx] {x} = Pr[= x | mx] := by simp
example (mx : ProbComp Bool) (p : Bool → Prop) : 𝒟[mx] {b | p b} = Pr[p | mx] := by simp
example (mx : ProbComp (Fin 3)) : 𝒟[mx] Set.univ = 1 - Pr[⊥ | mx] := by simp
example (mx : ProbComp Bool) (g : Bool → ℝ≥0∞) :
    ∫⁻ x, g x ∂𝒟[mx] = expectedValue mx g := by simp
example (mx : ProbComp Bool) (c : ℝ≥0∞) :
    ∫⁻ _, c ∂𝒟[mx] = expectedValue mx fun _ => c := by simp

example (x : Bool) : 𝒟[(pure x : ProbComp Bool)] = Measure.dirac x := by simp
example (x : Bool) : 𝒟[(pure x : ProbComp Bool)] {x} = 1 := by simp
example : 𝒟[$ᵗ Bool] {true} = 2⁻¹ := by simp

example (mx : ProbComp (Fin 2)) (my : ProbComp (Fin 3)) (y : Fin 3) :
    𝒟[mx >>= fun _ => my] {y} = (1 - Pr[⊥ | mx]) * Pr[= y | my] := by simp
example (mx : ProbComp Bool) (my : ProbComp (Fin 3)) :
    𝒟[mx >>= fun _ => my] = 𝒟[mx] Set.univ • 𝒟[my] := by simp

/-- The ladder's finite rung: expanding a bind on a `Fintype` lands on a finite sum through
Mathlib's `tsum_fintype`, with no library lemma involved. -/
example (mx : ProbComp Bool) (f : Bool → ProbComp (Fin 3)) (y : Fin 3) :
    Pr[= y | mx >>= f] = ∑ x, Pr[= x | mx] * Pr[= y | f x] := by
  simp [probOutput_bind_eq_tsum]

/-- The Giry bind law is a `rw`/`exact` target, not a simp rule, on either side. -/
example (mx : ProbComp Bool) (f : Bool → ProbComp (Fin 3)) :
    𝒟[mx >>= f] = 𝒟[mx].bind fun x => 𝒟[f x] := by
  fail_if_success simp  -- by design: bind expansion is not default simp
  exact evalDist_bind_of_discrete mx f

/-- The integral form of a bind is an intermediate, not a target: `simp` takes the right-hand
side into the façade instead of meeting it. -/
example (mx : ProbComp Bool) (f : Bool → ProbComp (Fin 3)) (s : Set (Fin 3)) :
    𝒟[mx >>= f] s = ∫⁻ x, 𝒟[f x] s ∂𝒟[mx] := by
  fail_if_success (simp; done)  -- by design: the integral form is not a normal form
  rw [evalDist_bind_of_discrete,
    Measure.bind_apply MeasurableSet.of_discrete Measurable.of_discrete.aemeasurable]

end adapter

/-! ## Free-monad fold: `ProbComp` with a local measure specification -/

section measureSpec

/-- A local measure specification for `unifSpec`, so nothing leaks through the test umbrella. -/
@[instance_reducible]
noncomputable def unifMeasureSpec : unifSpec.toPFunctor.IsMeasureSpec :=
  PFunctor.IsProbabilitySpec.toMeasureSpec _

attribute [local instance] unifMeasureSpec

example (mx : ProbComp Bool) (x : Bool) : 𝒟[mx] {x} = Pr[= x | mx] := by simp
example (mx : ProbComp Bool) (p : Bool → Prop) : 𝒟[mx] {b | p b} = Pr[p | mx] := by simp
example (mx : ProbComp (Fin 3)) : 𝒟[mx] Set.univ = 1 - Pr[⊥ | mx] := by simp
example (mx : ProbComp Bool) (g : Bool → ℝ≥0∞) :
    ∫⁻ x, g x ∂𝒟[mx] = expectedValue mx g := by simp only [lintegral_evalDist]
example (x : Bool) : 𝒟[(pure x : ProbComp Bool)] = Measure.dirac x := by simp
example (mx : ProbComp Bool) (my : ProbComp (Fin 3)) :
    𝒟[mx >>= fun _ => my] = 𝒟[mx] Set.univ • 𝒟[my] := by simp
example (mx : ProbComp Bool) (f : Bool → ProbComp (Fin 3)) :
    𝒟[mx >>= f] = 𝒟[mx].bind fun x => 𝒟[f x] :=
  evalDist_bind_of_discrete mx f

end measureSpec

/-! ## `OptionT ProbComp`: failure mass is visible -/

section optionCompatibility
open scoped ProbComp.DiscreteCompatibility

example (mx : OptionT ProbComp Bool) (x : Bool) : 𝒟[mx] {x} = Pr[= x | mx] := by simp
example (mx : OptionT ProbComp (Fin 3)) : 𝒟[mx] Set.univ = 1 - Pr[⊥ | mx] := by simp
example (mx : OptionT ProbComp Bool) (g : Bool → ℝ≥0∞) :
    ∫⁻ x, g x ∂𝒟[mx] = expectedValue mx g := by simp
example (mx : OptionT ProbComp Bool) (my : OptionT ProbComp (Fin 3)) :
    𝒟[mx >>= fun _ => my] = 𝒟[mx] Set.univ • 𝒟[my] := by simp

end optionCompatibility

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
    𝒟[Fintype.mPi f] {v} = ∏ i, Pr[= v i | f i] := by
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

section failureCompatibility
open scoped ProbComp.DiscreteCompatibility

example : 𝒟[(failure : OptionT ProbComp Bool)] = 0 := by simp
example (mx : OptionT ProbComp Bool) : (𝒟[mx]).withFailure {none} = Pr[⊥ | mx] := by simp
example (mx : OptionT ProbComp Bool) (x : Bool) :
    (𝒟[mx]).withFailure {some x} = Pr[= x | mx] := by simp
example (mx : ProbComp Bool) : IsProbabilityMeasure 𝒟[mx] := inferInstance
example (mx : ProbComp (Fin 3)) (f : Fin 3 → ProbComp (Fin 2)) : 𝒟[mx >>= f] Set.univ = 1 := by
  simp

/-- A lossy computation that succeeds exactly on the `true` outcome of a fair coin. -/
def lossyCoin : OptionT ProbComp Bool := do
  let b ← $ᵗ Bool
  if b then pure true else failure

example : 𝒟[lossyCoin] {true} = 2⁻¹ := by
  simp [lossyCoin, OptionT.probOutput_eq, probOutput_bind_eq_tsum]
example : 𝒟[lossyCoin] {false} = 0 := by
  simp [lossyCoin, OptionT.probOutput_eq, probOutput_bind_eq_tsum]
example : (𝒟[lossyCoin]).withFailure {none} = 2⁻¹ := by
  simp [lossyCoin, OptionT.probFailure_eq, probOutput_bind_eq_tsum]
example : (𝒟[lossyCoin]).withFailure {some true} = 2⁻¹ := by
  simp [lossyCoin, OptionT.probOutput_eq, probOutput_bind_eq_tsum]
example : (MeasureSemanticsVia.optionT ProbComp).evalDist lossyCoin =
    (𝒟[lossyCoin.run]).dropNone := by
  simp

end failureCompatibility

/-! ## A unit-test program

A coin and a die drawn independently, closed on the measure side by the same calls as the
façade: the point mass is the product of the two uniform masses (the closed form `simp` reaches;
merging `2⁻¹ * 6⁻¹` into `12⁻¹` is `ℝ≥0∞` arithmetic, not a probability rule), an event on one
coordinate needs the bind expanded under `Pr[…]` and `ENNReal.div_self` for the total factor, and
the failure-side facts need nothing beyond the program never failing. -/

/-- A coin and a die, drawn independently. -/
def coinDie : ProbComp (Bool × Fin 6) := do
  let b ← $ᵗ Bool
  let d ← $ᵗ (Fin 6)
  pure (b, d)

example : 𝒟[coinDie] {(true, 0)} = 2⁻¹ * 6⁻¹ := by simp [coinDie]
example : 𝒟[coinDie] {z | z.1 = true} = 2⁻¹ := by
  simp [coinDie, probEvent_bind_eq_tsum, ENNReal.div_self]
example (g : Bool × Fin 6 → ℝ≥0∞) :
    ∫⁻ z, g z ∂𝒟[coinDie] = expectedValue coinDie g := by simp only [lintegral_evalDist]
example : 𝒟[coinDie] Set.univ = 1 := by simp
example : (𝒟[coinDie]).withFailure {none} = 0 := by simp
example : IsProbabilityMeasure 𝒟[coinDie] := inferInstance

/-! ## Continuous carriers are untouched -/

/-- Without a discrete carrier the bridge does not fire: `lintegral_evalDist` needs
`DiscreteMeasurableSpace`, which `ℝ` does not have. -/
example (mx : ProbComp ℝ) (g : ℝ → ℝ≥0∞) (h : ∫⁻ x, g x ∂𝒟[mx] = 0) :
    ∫⁻ x, g x ∂𝒟[mx] = 0 := by
  fail_if_success simp only [lintegral_evalDist] at h
  exact h

end VCVioTest.MeasureBridge
