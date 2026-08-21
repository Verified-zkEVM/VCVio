/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import VCVio.EvalDist.PFunctorMeasure
public import Mathlib.Probability.Distributions.Gaussian.Real
public import ToMathlib.MeasureTheory.DiscreteInstances
public import Examples.OneTimePad.Basic

/-!
# Canaries for the measure denotation

Two checks on `VCVio.EvalDist.PFunctorMeasure`, kept in the test library so they stay out of
the timed build.

`continuousOracle` is the capability check. It exhibits an oracle whose answers are drawn from
a continuous distribution, which `PFunctor.IsProbabilitySpec` cannot express at all: that class
carries a `Handler PMF P`, and `PMF.support_countable` makes every `PMF` countably supported,
whereas `ProbabilityTheory.gaussianReal` is not. The measure denotation gives it a meaning.

`discreteAgreement` is the compatibility check: on an interface carrying both interpretations,
the measure denotation is the measure of the `PMF` denotation, so existing probability
statements transport rather than needing reproof.
-/

public section

open MeasureTheory ProbabilityTheory PFunctor OracleSpec OracleComp ENNReal

namespace VCVioTest.MeasureSemantics

/-! ## A continuous oracle -/

/-- An interface with a single operation, answered by a real number. -/
@[expose, reducible] def gaussSpec : PFunctor.{0, 0} := ⟨PUnit, fun _ => ℝ⟩

/-- The operation is answered by a standard Gaussian.

There is no `PFunctor.IsProbabilitySpec gaussSpec`: its `toPMF` field would have to be a
`PMF ℝ`, and a `PMF` has countable support. -/
noncomputable instance : gaussSpec.IsMeasureSpec where
  toMeasure _ := gaussianReal 0 1
  isProbabilityMeasure _ := instIsProbabilityMeasureGaussianReal 0 1

/-- Sampling the oracle once denotes the standard Gaussian on `ℝ`.

This is the statement the conversion buys: it does not typecheck against a `PMF`-valued
semantics, because its subject is not a `PMF`. -/
theorem denote_gauss_lift :
    FreeM.denote (P := gaussSpec) (FreeM.lift PUnit.unit) = gaussianReal 0 1 := by
  change Measure.bind (gaussianReal 0 1)
      (fun b => FreeM.denote (P := gaussSpec) (Pure.pure b)) = _
  simp

/-- The denoted measure really is a Gaussian law: its mass on a half-line is the Gaussian's,
so Mathlib's distribution API applies to the denotation directly rather than through a
translation layer. -/
example (s : Set ℝ) :
    FreeM.denote (P := gaussSpec) (FreeM.lift PUnit.unit) s = gaussianReal 0 1 s := by
  rw [denote_gauss_lift]

/-! ## Agreement with the `PMF` denotation on a discrete interface -/

/-- An interface with a single operation, answered by a coin flip. -/
@[expose, reducible] def coinSpec : PFunctor.{0, 0} := ⟨PUnit, fun _ => Bool⟩

noncomputable instance : coinSpec.IsProbabilitySpec where
  toPMF _ := PMF.uniformOfFintype Bool

noncomputable instance : coinSpec.IsMeasureSpec where
  toMeasure _ := (PMF.uniformOfFintype Bool).toMeasure
  isProbabilityMeasure _ := PMF.toMeasure.isProbabilityMeasure _

/-- On a discrete interface the two denotations agree, so a `Pr[…]` result proved against the
`PMF` semantics can be read off the measure semantics. -/
theorem denote_eq_toMeasure_coin {α : Type} [MeasurableSpace α]
    (program : FreeM coinSpec α) :
    FreeM.denote program = (program.liftM IsProbabilitySpec.toPMF).toMeasure :=
  FreeM.denote_eq_toMeasure (fun _ => rfl) program

/-! ## Transporting an existing `Pr[…]` result

`unifSpec` is discrete, so it induces a measure interpretation and the singleton bridge
applies. Any probability already proved about a `ProbComp` is then a fact about its measure
denotation, with no reproof. -/

noncomputable instance : unifSpec.toPFunctor.IsMeasureSpec :=
  PFunctor.IsProbabilitySpec.toMeasureSpec _

theorem denote_probComp_apply_singleton {α : Type} [MeasurableSpace α]
    [MeasurableSingletonClass α] (program : ProbComp α) (x : α) :
    FreeM.denote program {x} = Pr[= x | program] :=
  FreeM.denote_apply_singleton (fun _ => rfl) program x

/-- The one-time-pad ciphertext is uniform, read off the measure denotation.

The statement is about a Mathlib `Measure`; the proof is the existing `Pr[…]` result. This is
the compatibility gate: converting the semantics does not cost the crypto proofs. -/
example (sp : ℕ) (mgen : ProbComp (BitVec sp)) (σ : BitVec sp) :
    FreeM.denote ((oneTimePad sp).PerfectSecrecyCipherExp mgen) {σ}
      = (Fintype.card (BitVec sp) : ℝ≥0∞)⁻¹ := by
  rw [denote_probComp_apply_singleton]
  exact oneTimePad.probOutput_cipher_uniform sp mgen σ

end VCVioTest.MeasureSemantics
