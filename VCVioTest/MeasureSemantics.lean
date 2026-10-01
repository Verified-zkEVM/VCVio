/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import VCVio.EvalDist.ResumptionMeasure
public import VCVio.EvalDist.Divergence.KLDivergence
public import VCVio.EvalDist.MeasureTVDist.Basic
public import VCVio.OracleComp.EvalDist.Measure
public import VCVio.ProgramLogic.Relational.Measure
public import ToMathlib.Probability.Divergence.RenyiTotalVariation
public import Mathlib.Probability.Distributions.Gaussian.Real
public import ToMathlib.MeasureTheory.DiscreteInstances
public import Examples.OneTimePad.Basic

/-!
# Canaries for the measure denotation

Checks on the measure denotation of `VCVio.EvalDist.PFunctorMeasure.Core`, kept in the test
library so they stay out of the timed build.

The continuous oracle is the capability check. Its answers are drawn from
`ProbabilityTheory.gaussianReal`, which has no atoms, so no countably supported distribution can
express it; the measure denotation gives it a meaning. The discrete coin interface then checks
the composition laws, transformer stacks, fuelled resumptions and divergences on a finite
interface.
-/

public section

open MeasureTheory ProbabilityTheory PFunctor OracleSpec OracleComp ENNReal

namespace VCVioTest.MeasureSemantics

/-! ## Optional measure kernels -/

example {α : Type*} [MeasurableSpace α] :
    Measurable (fun value : Option α => value.elim (0 : Measure α) Measure.dirac) := by
  fun_prop

example {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (f : β → Option α) (hf : Measurable f) :
    Measurable (fun b => (f b).elim (0 : Measure α) Measure.dirac) := by
  fun_prop

/-! ## A continuous oracle -/

/-- An interface with a single operation, answered by a real number. -/
@[expose, reducible] def gaussSpec : PFunctor.{0, 0} := ⟨PUnit, fun _ => ℝ⟩

/-- The operation is answered by a standard Gaussian, a law with no atoms. -/
noncomputable instance : gaussSpec.AnswerMeasure where
  toMeasure _ := gaussianReal 0 1
  isProbabilityMeasure _ := instIsProbabilityMeasureGaussianReal 0 1

/-- Sampling the oracle once denotes the standard Gaussian on `ℝ`.

Its subject is not countably supported, so no discrete semantics can state it. -/
theorem denote_gauss_lift :
    FreeM.denote (P := gaussSpec) (FreeM.lift PUnit.unit) = gaussianReal 0 1 :=
  FreeM.denote_lift (P := gaussSpec) PUnit.unit

/-- The `𝒟[…]` notation selects the direct measure fold. -/
example : 𝒟[(FreeM.lift PUnit.unit : FreeM gaussSpec ℝ)] = gaussianReal 0 1 :=
  denote_gauss_lift

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
      Measure.bind (gaussianReal 0 1) fun sample => Measure.dirac (sample + 1) := by
  apply FreeM.denote_liftBind (P := gaussSpec)
  change AEMeasurable (fun sample : ℝ => Measure.dirac (sample + 1)) (gaussianReal 0 1)
  fun_prop

/-- The continuous composition remains a probability measure. This proof is the canary for the
measurable-continuation boundary that a discrete semantics cannot state. -/
theorem isProbabilityMeasure_denote_shiftedGaussian :
    IsProbabilityMeasure (FreeM.denote shiftedGaussian) := by
  apply FreeM.isProbabilityMeasure_denote_liftBind
  · change AEMeasurable (fun sample : ℝ => Measure.dirac (sample + 1)) (gaussianReal 0 1)
    fun_prop
  · exact Filter.Eventually.of_forall fun _ => ⟨by simp⟩

/-! ## Uniform semantics and composition laws -/

/-- A finite, inhabited interface whose measure interpretation is chosen explicitly. -/
@[expose, reducible] def explicitCoinSpec : PFunctor.{0, 0} := ⟨PUnit, fun _ => Bool⟩

/-- The uniform measure interpretation is an explicit value, not a global instance. -/
@[instance_reducible]
noncomputable def explicitCoinMeasureSpec : explicitCoinSpec.AnswerMeasure :=
  AnswerMeasure.uniformOfFiniteNonempty _

attribute [local instance] explicitCoinMeasureSpec

/-- A uniform operation denotes `uniformOn univ` directly. -/
theorem denote_explicitCoin_lift :
    FreeM.denote (FreeM.lift (P := explicitCoinSpec) PUnit.unit) =
      (uniformOn Set.univ : Measure Bool) := by
  rw [FreeM.denote_lift (P := explicitCoinSpec) PUnit.unit]
  rfl

/-! ## Distance and relational semantics -/

/-- Total variation is available directly on a continuous computation. -/
example : measureTVDist shiftedGaussian shiftedGaussian = 0 :=
  measureTVDist_self shiftedGaussian

/-- The diagonal construction couples a Gaussian measure with itself. -/
example : Measure.IsCoupling (Measure.Coupling.refl (gaussianReal 0 1)).joint
    (gaussianReal 0 1) (gaussianReal 0 1) :=
  (Measure.Coupling.refl (gaussianReal 0 1)).property

/-- Relational reasoning applies directly to a continuous denotation. -/
example : ExpectationWP.RelWP shiftedGaussian shiftedGaussian (· = ·) :=
  ExpectationWP.relWP_refl shiftedGaussian

/-! ## A discrete interface -/

/-- An interface with a single operation, answered by a coin flip. -/
@[expose, reducible] def coinSpec : PFunctor.{0, 0} := ⟨PUnit, fun _ => Bool⟩

noncomputable instance : coinSpec.AnswerMeasure := AnswerMeasure.uniformOfFiniteNonempty _

/-- A nonzero, branch-sensitive lower bound rules out a vacuous quantitative semantics. -/
example : (1 : ℝ≥0∞) ≤
    ExpectationWP.eRelWP (pure true : FreeM coinSpec Bool)
      (pure false : FreeM coinSpec Bool)
      (fun a b => if a && !b then 1 else 0) := by
  exact ExpectationWP.le_eRelWP_pure_pure
    (m₁ := FreeM coinSpec) (m₂ := FreeM coinSpec) true false
    (fun a b => if a && !b then 1 else 0) (by fun_prop)

/-! ## Output-measure notation -/

/-- The `𝒟[…]` notation is a subprobability measure. -/
example (program : FreeM coinSpec Bool) : 𝒟[program] Set.univ ≤ 1 :=
  evalDist_apply_univ_le_one program

/-- On a discrete `FreeM` program, `𝒟[…]` agrees with the direct measure fold. -/
example (program : FreeM coinSpec Bool) : 𝒟[program] = FreeM.denote program :=
  FreeM.evalDist_eq_denote program

/-- Point notation is singleton mass in the output measure. -/
example (program : FreeM coinSpec Bool) (x : Bool) :
    Pr{let y ← program}[y = x] = 𝒟[program] {x} :=
  prEvent_eq_evalDist_singleton program x

/-- Mapping a discrete program pushes its denoted measure forward. -/
example (program : FreeM coinSpec Bool) :
    FreeM.denote ((fun bit => !bit) <$> program) =
      (FreeM.denote program).map fun bit => !bit :=
  FreeM.denote_map_of_discrete program _

/-- Two answer-independent executions denote the Mathlib product measure. -/
example (first second : FreeM coinSpec Bool) :
    FreeM.denote (do
      let x ← first
      let y ← second
      pure (x, y)) = (FreeM.denote first).prod (FreeM.denote second) :=
  FreeM.denote_bind_bind_prod_mk_eq_prod first second

/-! ## Transformer stacks retain their effects -/

/-- The reusable total semantics for the discrete coin interface. -/
noncomputable def coinMeasureSemantics : ProbabilitySemantics (FreeM coinSpec) :=
  ProbabilitySemantics.freeM

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
  rw [delayedTrue, Resumption.outputMeasure_query_succ (P := coinSpec)]
  rw [Measure.bind_const,
    (AnswerMeasure.isProbabilityMeasure (P := coinSpec) PUnit.unit).measure_univ, one_smul]
  exact Resumption.outputMeasure_pure (P := coinSpec) 0 true

/-- The fuel-free returned-output semantics sees the delayed return with total mass one. -/
example : Resumption.returnedMeasure delayedTrue Set.univ = 1 := by
  apply le_antisymm (Resumption.returnedMeasure_apply_univ_le_one delayedTrue)
  calc
    1 = Resumption.outputMeasure 1 delayedTrue Set.univ := by
      rw [outputMeasure_one_delayedTrue]
      simp
    _ ≤ Resumption.returnedMeasure delayedTrue Set.univ :=
      (Resumption.outputMeasure_le_returnedMeasure 1 delayedTrue) Set.univ

/-! ## Divergence

The point of denoting into `Measure` is that Mathlib's probability library then applies to
VCVio programs directly. Kullback-Leibler is the check: it arrives with its data-processing
inequalities already proved. -/

open InformationTheory

/-- Post-processing two computations by the same continuation cannot increase their divergence.

This is the game-hopping shape, and it is Mathlib's `klDiv_comp_right_le` — `Measure.bind` and
kernel composition are the same operation, so no transport is involved. -/
example {α β : Type} [MeasurableSpace α] [DiscreteMeasurableSpace α] [MeasurableSpace β]
    (mx my : FreeM coinSpec α) (f : α → FreeM coinSpec β) :
    klDiv (FreeM.denote (mx >>= f)) (FreeM.denote (my >>= f))
      ≤ klDiv (FreeM.denote mx) (FreeM.denote my) :=
  FreeM.klDiv_denote_bind_le mx my f

/-- The same for post-processing by a function. -/
example {α β : Type} [MeasurableSpace α] [DiscreteMeasurableSpace α] [MeasurableSpace β]
    (g : α → β) (mx my : FreeM coinSpec α) :
    klDiv (FreeM.denote (g <$> mx)) (FreeM.denote (g <$> my))
      ≤ klDiv (FreeM.denote mx) (FreeM.denote my) :=
  FreeM.klDiv_denote_map_le g mx my

/-- Divergence between *continuous* denotations is expressible at all.

`klDiv` here is applied to two measures on `ℝ` that no countably supported distribution can
carry. -/
example : klDiv (FreeM.denote (P := gaussSpec) (FreeM.lift PUnit.unit))
    (FreeM.denote (P := gaussSpec) (FreeM.lift PUnit.unit)) = 0 := by
  rw [denote_gauss_lift]
  exact klDiv_self _

/-! ## Expectation as an integral

An expectation is a `∫⁻` against the denoted measure, so Mathlib's integration theory applies to
it. Monotone convergence is the payoff. -/

/-- **Monotone convergence** for an expectation over a VCVio program, from `lintegral_iSup`. -/
example (n : ℕ) (mx : ProbComp (BitVec n)) (g : ℕ → BitVec n → ℝ≥0∞) (hg : Monotone g) :
    ∫⁻ x, ⨆ k, g k x ∂𝒟[mx] = ⨆ k, ∫⁻ x, g k x ∂𝒟[mx] :=
  lintegral_iSup (fun _ => Measurable.of_discrete) hg

/-! ## Renyi divergence

The Renyi divergence is stated for arbitrary measures, so it covers laws no countably supported
distribution can carry, and its security-facing bounds apply to program denotations directly. -/

/-- Renyi between two continuous laws. -/
example (a : ℝ) : renyiMGF a (gaussianReal 0 1) (gaussianReal 0 1) = 1 := renyiMGF_self a _

/-- **The Rényi → total-variation bound** between the output laws of two programs: both halves,
Cauchy-Schwarz against the Hellinger affinity and log-convexity of the Rényi MGF, reduce to the
same Mathlib inequality, `ENNReal.lintegral_mul_norm_pow_le`. -/
example (n : ℕ) (a : ℝ) (ha : 1 < a) (mx my : ProbComp (BitVec n)) :
    𝒟[mx].etvDist 𝒟[my] ^ (2 : ℝ) ≤ 1 - (renyiDiv a 𝒟[mx] 𝒟[my])⁻¹ :=
  etvDist_rpow_two_le_one_sub_inv_renyiDiv ha _ _

/-- **Probability preservation**, the form security reductions consume: an event of one program
keeps probability under a program at bounded Rényi divergence. -/
example (n : ℕ) (a : ℝ) (ha : 1 < a) (mx my : ProbComp (BitVec n)) (s : Set (BitVec n)) :
    𝒟[mx] s ^ (a / (a - 1)) / renyiDiv a 𝒟[mx] 𝒟[my] ≤ 𝒟[my] s :=
  measure_rpow_div_renyiDiv_le ha _ _ MeasurableSet.of_discrete

end VCVioTest.MeasureSemantics
