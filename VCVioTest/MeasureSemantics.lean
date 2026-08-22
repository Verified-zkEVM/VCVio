/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import VCVio.EvalDist.ResumptionMeasure
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

/-- A genuinely continuous continuation composes through the Giry bind once its measurability is
made explicit. -/
@[expose] noncomputable def shiftedGaussian : FreeM gaussSpec ℝ :=
  FreeM.liftBind PUnit.unit fun sample => pure (sample + 1)

theorem denote_shiftedGaussian :
    FreeM.denote shiftedGaussian =
      Measure.bind (gaussianReal 0 1) fun sample => Measure.dirac (sample + 1) :=
  rfl

/-- The continuous composition remains a probability measure. This proof is the canary for the
measurable-continuation boundary that a `PMF` semantics cannot state. -/
theorem isProbabilityMeasure_denote_shiftedGaussian :
    IsProbabilityMeasure (FreeM.denote shiftedGaussian) := by
  apply FreeM.isProbabilityMeasure_denote_liftBind
  · change AEMeasurable (fun sample : ℝ => Measure.dirac (sample + 1)) (gaussianReal 0 1)
    fun_prop
  · exact Filter.Eventually.of_forall fun _ => ⟨by simp⟩

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

/-- Predicate notation transports to arbitrary measurable events, not just singletons. -/
theorem denote_event_coin {α : Type} [MeasurableSpace α] [DiscreteMeasurableSpace α]
    (program : FreeM coinSpec α) (event : α → Prop) :
    FreeM.denote program {x | event x} = Pr[event | program] :=
  FreeM.denote_apply_setOf (fun _ => rfl) program event MeasurableSet.of_discrete

/-! ## Transformer stacks retain their effects -/

/-- The reusable total semantics for the discrete coin interface. -/
noncomputable def coinMeasureSemantics : MeasureSemantics (FreeM coinSpec) :=
  MeasureSemantics.freeM

/-- `OptionT` keeps `none` as an observable outcome until a proof explicitly discards it. -/
example (computation : OptionT (FreeM coinSpec) Bool) :
    IsProbabilityMeasure (coinMeasureSemantics.optionT computation) :=
  coinMeasureSemantics.isProbabilityMeasure_optionT computation

/-- `ExceptT` likewise retains the error branch as part of the total outcome space. -/
example (computation : ExceptT Bool (FreeM coinSpec) Bool) :
    IsProbabilityMeasure (coinMeasureSemantics.exceptT computation) :=
  coinMeasureSemantics.isProbabilityMeasure_exceptT computation

/-- `WriterT` retains the produced log alongside the result. -/
example (computation : WriterT Bool (FreeM coinSpec) Bool) :
    IsProbabilityMeasure (coinMeasureSemantics.writerT computation) :=
  coinMeasureSemantics.isProbabilityMeasure_writerT computation

/-- A reader computation exposes its environment as the input of a Markov kernel. -/
@[expose] def echoEnvironment : ReaderT Bool (FreeM coinSpec) Bool :=
  fun environment => pure environment

noncomputable def echoEnvironmentKernel : Kernel Bool Bool :=
  coinMeasureSemantics.readerTKernel echoEnvironment Measurable.of_discrete

example : IsMarkovKernel echoEnvironmentKernel := by
  unfold echoEnvironmentKernel
  infer_instance

example (environment : Bool) :
    echoEnvironmentKernel environment = Measure.dirac environment := rfl

/-- A stateful computation denotes a Markov kernel from initial states to result/final-state
pairs. Discreteness makes the kernel's measurability obligation immediate. -/
@[expose] def rememberState : StateT Bool (FreeM coinSpec) Bool :=
  fun state => pure (state, !state)

noncomputable def rememberStateKernel : Kernel Bool (Bool × Bool) :=
  coinMeasureSemantics.stateTKernel rememberState Measurable.of_discrete

example : IsMarkovKernel rememberStateKernel := by
  unfold rememberStateKernel
  infer_instance

example (state : Bool) :
    rememberStateKernel state = Measure.dirac (state, !state) := rfl

/-! ## Finite observations of possible nontermination -/

/-- A resumption that needs one visible query before returning. -/
@[expose] def delayedTrue : Resumption coinSpec Bool :=
  Resumption.query PUnit.unit fun _ => pure true

/-- At zero fuel the computation has no returned-output mass. -/
example : Resumption.outputMeasure 0 delayedTrue = 0 := by
  simp [delayedTrue]

/-- At one unit of fuel it has returned `true`; the cutoff marker has not been conflated with a
failure result. -/
theorem outputMeasure_one_delayedTrue :
    Resumption.outputMeasure 1 delayedTrue = Measure.dirac true := by
  change (Measure.bind (IsMeasureSpec.toMeasure (P := coinSpec) PUnit.unit)
    (fun _ => Measure.dirac (some true))).dropNone = Measure.dirac true
  rw [Measure.bind_const,
    (IsMeasureSpec.isProbabilityMeasure (P := coinSpec) PUnit.unit).measure_univ, one_smul]
  simp

/-- The fuel-free returned-output semantics sees the delayed return with total mass one. -/
example : Resumption.returnedMeasure delayedTrue Set.univ = 1 := by
  apply le_antisymm (Resumption.returnedMeasure_apply_univ_le_one delayedTrue)
  calc
    1 = Resumption.outputMeasure 1 delayedTrue Set.univ := by
      rw [outputMeasure_one_delayedTrue]
      simp
    _ ≤ Resumption.returnedMeasure delayedTrue Set.univ :=
      (Resumption.outputMeasure_le_returnedMeasure 1 delayedTrue) Set.univ

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
