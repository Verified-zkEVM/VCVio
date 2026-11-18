/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.CryptoFoundations.TimeLockPuzzle.Quantum
import VCVio.Quantum.Comp.Finisher

/-!
# Classical generators in quantum delay experiments

A classical generator may retain arbitrary classical challenger data alongside its puzzle and key.
`ofClassicalGenerator` embeds it in the quantum experiment without exposing those hidden outputs to
the online adversary. For one fixed function, its framed generation branches are scalar identities
on adversary memory. This gives an exact weighted online-family law for adversaries with no
preprocessing, including observers of the key and hidden generator data jointly with the output.

The generic instrument factorization keeps the same runtime-private register across generation and
online execution. The scalar identity and weighted-law specialization apply to a fixed-function
runtime, whose private register is trivial. They do not discard a compressed or purified database.
-/

public section

open MeasureTheory Matrix OracleSpec OracleComp
open scoped ENNReal Kronecker

namespace Quantum.TimeLockPuzzle

variable {X Y Puzzle Key Secret Out : Type} [Fintype X] [DecidableEq X]
  [Fintype Y] [DecidableEq Y] [AddCommGroup Y]

/-- Embed a classical batch generator while retaining all hidden classical generator data.
The online adversary receives only the first component, the public puzzle. -/
@[expose, reducible]
noncomputable def ofClassicalGenerator
    (gen : OracleComp (unifSpec + (X →ₒ Y).batch) (Puzzle × Key × Secret))
    (solve : Puzzle → QComp (qromBatchSpec X Y) (QReg.of Unit) (QReg.of Unit) (Option Key)) :
    Quantum.TimeLockPuzzle (qromBatchSpec X Y) Puzzle Key where
  Secret := Secret
  gen := gen.toQuantumBatch
  solve := solve

/-- For a fixed function, honest classical generation multiplies every adversary-memory matrix
by the classical output probability. It neither observes nor changes the adversary register. -/
theorem generationInstrument_ofClassicalGenerator_branch (H : X → Y)
    (gen : OracleComp (unifSpec + (X →ₒ Y).batch) (Puzzle × Key × Secret))
    (solve : Puzzle → QComp (qromBatchSpec X Y) (QReg.of Unit) (QReg.of Unit) (Option Key))
    (M : QReg) (z : Puzzle × Key × Secret)
    (ρ : Matrix (M × (parallelOracleRuntime H).D) (M × (parallelOracleRuntime H).D) ℂ) :
    (generationInstrument (parallelOracleRuntime H)
      (ofClassicalGenerator gen solve) M).branch z ρ =
      ((Pr{let a ← simulateQ (unifFwdAnswerImpl (QueryImpl.ofFn H)).batch' gen}[a = z]).toReal :
        ℂ) • ρ := by
  have h : ((parallelOracleRuntime H).run₂ .instruments gen.toQuantumBatch).branch z =
      ((Pr{let a ← simulateQ (unifFwdAnswerImpl (QueryImpl.ofFn H)).batch' gen}[a = z]).toReal :
        ℂ) • LinearMap.id := by
    rw [run_toQuantumBatch, branch_run₂_toQuantumAt_coinImpl]
  change ((((parallelOracleRuntime H).run₂ .instruments gen.toQuantumBatch).frame M).reindex
    (generationEquiv M (parallelOracleRuntime H).D).symm
    (generationEquiv M (parallelOracleRuntime H).D).symm).branch z ρ = _
  rw [SubInstrument.branch_reindex_apply, DSubInstrument.branch_frame_apply]
  rw [h]
  ext a b
  simp [MatrixMap.amplify_apply, LinearMap.smul_apply, LinearMap.id_apply, generationEquiv]

section General

variable {spec : QuantumOracleSpec.{0, 0}}

/-- The retained-register witness for an adversary that starts its online phase immediately. -/
@[expose]
def TwoPhaseAdversary.withoutPreprocessingState (A : QReg) (ρ : SubState A)
    (online : Puzzle → QuantumComp LocalSig.instruments spec (fun _ ↦ Out) A) :
    (TwoPhaseAdversary.withoutPreprocessing A ρ online).State A := ⟨rfl⟩

/-- Joint transcript obtained from honest generation and an online leaf, with an empty
preprocessing phase. The hidden key and auxiliary secret remain in the observer transcript. -/
@[expose, reducible]
def withoutPreprocessingTranscript
    (tlp : Quantum.TimeLockPuzzle spec Puzzle Key) (A : QReg) (ρ : SubState A)
    (online : Puzzle → QuantumComp LocalSig.instruments spec (fun _ ↦ Out) A)
    (z : Puzzle × Key × tlp.Secret) (out : Σ _B : QReg, Out) :
    DelayTranscript tlp (TwoPhaseAdversary.withoutPreprocessing A ρ online) :=
  ⟨A, TwoPhaseAdversary.withoutPreprocessingState A ρ online,
    z.1, z.2.1, z.2.2, out.1, out.2⟩

/-- An empty preprocessing phase leaves the honest generation and online instruments composed
on the same adversary/oracle register, without initializing or discarding private runtime state. -/
theorem delayInstrument_withoutPreprocessing (R : QuantumRuntime spec)
    (tlp : Quantum.TimeLockPuzzle spec Puzzle Key) (A : QReg) (ρ : SubState A)
    (online : Puzzle → QuantumComp LocalSig.instruments spec (fun _ ↦ Out) A) :
    delayInstrument R tlp (TwoPhaseAdversary.withoutPreprocessing A ρ online) =
      DSubInstrument.bind (generationInstrument R tlp A) fun z ↦
        DSubInstrument.bind (R.run .instruments (online z.1)) fun out ↦
          DSubInstrument.ret (fun t : DelayTranscript tlp
            (TwoPhaseAdversary.withoutPreprocessing A ρ online) ↦ t.finalReg × R.D)
              (withoutPreprocessingTranscript tlp A ρ online z out) := by
  unfold delayInstrument TwoPhaseAdversary.withoutPreprocessing
  rw [QuantumRuntime.run_pure, DSubInstrument.ret_bind]
  rfl

end General

/-- The joint transcript assembled from a preprocessing leaf, hidden generator output and online
leaf. The online program receives only its preprocessing information and the public puzzle. -/
@[expose, reducible]
def phaseTranscript {spec : QuantumOracleSpec.{0, 0}}
    (tlp : Quantum.TimeLockPuzzle spec Puzzle Key) (adv : TwoPhaseAdversary spec Puzzle Out)
    (pre : Σ M, adv.State M) (z : Puzzle × Key × tlp.Secret) (out : Σ _B : QReg, Out) :
    DelayTranscript tlp adv :=
  ⟨pre.1, pre.2, z.1, z.2.1, z.2.2, out.1, out.2⟩

private theorem generation_onlineLaw {β : Type*} [MeasurableSpace β] (H : X → Y)
    (gen : OracleComp (unifSpec + (X →ₒ Y).batch) (Puzzle × Key × Secret))
    (solve : Puzzle → QComp (qromBatchSpec X Y) (QReg.of Unit) (QReg.of Unit) (Option Key))
    (adv : TwoPhaseAdversary (qromBatchSpec X Y) Puzzle Out)
    (pre : Σ M, adv.State M) (σ : SubState (pre.1 × (parallelOracleRuntime H).D))
    (f : DelayTranscript (ofClassicalGenerator gen solve) adv → β) :
    (letI : MeasurableSpace (DelayTranscript (ofClassicalGenerator gen solve) adv) := ⊤
     ((DSubInstrument.bind
       (generationInstrument (parallelOracleRuntime H) (ofClassicalGenerator gen solve) pre.1)
       fun z ↦ DSubInstrument.bind
         ((parallelOracleRuntime H).run .instruments (adv.online pre.1 pre.2 z.1))
         fun out ↦ DSubInstrument.ret
           (fun t : DelayTranscript (ofClassicalGenerator gen solve) adv ↦
             t.finalReg × (parallelOracleRuntime H).D)
           (phaseTranscript (ofClassicalGenerator gen solve) adv pre z out)).outcomeMeasure σ).map
       f) =
      (letI : MeasurableSpace (Σ _B : QReg, Out) := ⊤
       Measure.sum fun z : Puzzle × Key × Secret ↦
         (Pr{let a ← simulateQ (unifFwdAnswerImpl (QueryImpl.ofFn H)).batch' gen}[a = z]) •
           (((parallelOracleRuntime H).run .instruments (adv.online pre.1 pre.2 z.1)).outcomeMeasure
             σ).map
             (fun out ↦
                 f (phaseTranscript (ofClassicalGenerator gen solve) adv pre z out))) := by
  classical
  let : MeasurableSpace (DelayTranscript (ofClassicalGenerator gen solve) adv) := ⊤
  let : MeasurableSpace (Σ _B : QReg, Out) := ⊤
  rw [DSubInstrument.outcomeMeasure_bind,
    Measure.map_sum Measurable.of_discrete.aemeasurable]
  refine congrArg Measure.sum (funext fun z ↦ ?_)
  have hmap := DSubInstrument.map_eq_bind_ret
    (C := fun t : DelayTranscript (ofClassicalGenerator gen solve) adv ↦
      t.finalReg × (parallelOracleRuntime H).D)
    (phaseTranscript (ofClassicalGenerator gen solve) adv pre z)
    ((parallelOracleRuntime H).run .instruments (adv.online pre.1 pre.2 z.1))
  have hsmul (c : ℝ≥0∞) (μ : (Σ _B : QReg, Out) → Measure β) :
      c • Measure.sum μ = Measure.sum (fun i ↦ c • μ i) := by
    ext s hs
    simp only [Measure.smul_apply, Measure.sum_apply _ hs, smul_eq_mul,
      ENNReal.tsum_mul_left]
  rw [← hmap, DSubInstrument.outcomeMeasure_map,
    Measure.map_sum Measurable.of_discrete.aemeasurable,
    DSubInstrument.outcomeMeasure, Measure.map_sum Measurable.of_discrete.aemeasurable,
    hsmul]
  refine congrArg Measure.sum (funext fun out ↦ ?_)
  rw [Measure.map_smul _ Measurable.of_discrete.aemeasurable,
    Measure.map_dirac' Measurable.of_discrete,
    Measure.map_smul _ Measurable.of_discrete.aemeasurable,
    Measure.map_dirac' Measurable.of_discrete, smul_smul]
  congr 1
  rw [DSubInstrument.matrix_post,
    generationInstrument_ofClassicalGenerator_branch H gen solve pre.1 z,
    map_smul, Matrix.trace_smul]
  simp only [smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (prEvent_ne_top _)]

/-- The full joint observation law for a classical generator and arbitrary preprocessing.
The same fixed function answers all phases. Each online execution starts from its actual joint
preprocessing post-state, and the observer retains the preprocessing branch and hidden generator
outputs together with the final leaf. No query bounds or losslessness assumptions are needed. -/
theorem delayLawWith_ofClassicalGenerator
    {β : Type*} [MeasurableSpace β] (H : X → Y)
    (gen : OracleComp (unifSpec + (X →ₒ Y).batch) (Puzzle × Key × Secret))
    (solve : Puzzle → QComp (qromBatchSpec X Y) (QReg.of Unit) (QReg.of Unit) (Option Key))
    (adv : TwoPhaseAdversary (qromBatchSpec X Y) Puzzle Out)
    (f : DelayTranscript (ofClassicalGenerator gen solve) adv → β) :
    delayLawWith (parallelOracleRuntime H) (ofClassicalGenerator gen solve) adv f =
      (letI : MeasurableSpace (Σ _B : QReg, Out) := ⊤
       Measure.sum fun pre : Σ M, adv.State M ↦
         Measure.sum fun z : Puzzle × Key × Secret ↦
           (Pr{let a ← simulateQ (unifFwdAnswerImpl (QueryImpl.ofFn H)).batch' gen}[a = z]) •
             (((parallelOracleRuntime H).run .instruments
               (adv.online pre.1 pre.2 z.1)).outcomeMeasure
               ((parallelOracleRuntime H).jointPost .instruments adv.preprocess
                 adv.initialState pre)).map
               (fun out ↦
                 f (phaseTranscript (ofClassicalGenerator gen solve) adv pre z out))) := by
  let : MeasurableSpace (DelayTranscript (ofClassicalGenerator gen solve) adv) := ⊤
  unfold delayLawWith delayInstrument
  rw [DSubInstrument.outcomeMeasure_bind,
    Measure.map_sum Measurable.of_discrete.aemeasurable]
  exact congrArg Measure.sum (funext fun pre ↦ generation_onlineLaw H gen solve adv pre _ f)

/-- A classical generator average of preprocessing followed by the corresponding online program.
This form applies when the observer uses the hidden generator outputs and final leaf; the retained
preprocessing branch remains internal to the program. -/
theorem delayLawWith_ofClassicalGenerator_eq_sum
    {β : Type*} [MeasurableSpace β] (H : X → Y)
    (gen : OracleComp (unifSpec + (X →ₒ Y).batch) (Puzzle × Key × Secret))
    (solve : Puzzle → QComp (qromBatchSpec X Y) (QReg.of Unit) (QReg.of Unit) (Option Key))
    (adv : TwoPhaseAdversary (qromBatchSpec X Y) Puzzle Out)
    (f : (Puzzle × Key × Secret) → (Σ _B : QReg, Out) → β) :
    delayLawWith (parallelOracleRuntime H) (ofClassicalGenerator gen solve) adv
        (fun t ↦ f (t.puzzle, t.key, t.secret) ⟨t.finalReg, t.output⟩) =
      Measure.sum fun z : Puzzle × Key × Secret ↦
        (Pr{let a ← simulateQ (unifFwdAnswerImpl (QueryImpl.ofFn H)).batch' gen}[a = z]) •
          (parallelOracleRuntime H).evalDistMap .instruments
            (adv.preprocess.bind fun M state ↦ adv.online M state z.1)
            adv.initialState (f z) := by
  let : MeasurableSpace (Σ _B : QReg, Out) := ⊤
  rw [delayLawWith_ofClassicalGenerator, Measure.sum_comm]
  refine congrArg Measure.sum (funext fun z ↦ ?_)
  rw [QuantumRuntime.evalDistMap_bind]
  ext s hs
  simp only [Measure.sum_apply _ hs, Measure.smul_apply, smul_eq_mul,
    ENNReal.tsum_mul_left]

/-- Key-only recovery with arbitrary preprocessing is an average of complete preprocessing/online
runs. The complete hidden generator output remains in the averaging index and is used only by the
verifier. Honest generation is not counted as an adversary query. -/
theorem delayAdvantage_ofClassicalGenerator [DecidableEq Key]
    (H : X → Y)
    (gen : OracleComp (unifSpec + (X →ₒ Y).batch) (Puzzle × Key × Secret))
    (solve : Puzzle → QComp (qromBatchSpec X Y) (QReg.of Unit) (QReg.of Unit) (Option Key))
    (adv : Adversary (qromBatchSpec X Y) Puzzle Key) :
    delayAdvantage (parallelOracleRuntime H) (ofClassicalGenerator gen solve) adv =
      ∑' z : Puzzle × Key × Secret,
        (Pr{let a ← simulateQ (unifFwdAnswerImpl (QueryImpl.ofFn H)).batch' gen}[a = z]) *
          (parallelOracleRuntime H).evalDistMap .instruments
            (adv.preprocess.bind fun M state ↦ adv.online M state z.1) adv.initialState
            (fun out ↦ out.2 = z.2.1) {True} := by
  unfold delayAdvantage
  rw [delayLawWith_ofClassicalGenerator_eq_sum (f := fun z out ↦ decide (out.2 = z.2.1))]
  rw [Measure.sum_apply _ (MeasurableSet.singleton true)]
  simp only [Measure.smul_apply, smul_eq_mul]
  simp_rw [QuantumRuntime.evalDistMap_decide_apply_true]

/-- Exact fixed-function observation law for a classical generator and no preprocessing.
The observer may compare the output with the hidden key or any auxiliary generator data. -/
theorem delayLawWith_withoutPreprocessing_ofClassicalGenerator
    {β : Type*} [MeasurableSpace β] (H : X → Y)
    (gen : OracleComp (unifSpec + (X →ₒ Y).batch) (Puzzle × Key × Secret))
    (solve : Puzzle → QComp (qromBatchSpec X Y) (QReg.of Unit) (QReg.of Unit) (Option Key))
    (A : QReg) (ρ : SubState A)
    (online : Puzzle → QuantumComp LocalSig.instruments (qromBatchSpec X Y) (fun _ ↦ Out) A)
    (f : (Puzzle × Key × Secret) → (Σ _B : QReg, Out) → β) :
    delayLawWith (parallelOracleRuntime H) (ofClassicalGenerator gen solve)
      (TwoPhaseAdversary.withoutPreprocessing A ρ online)
      (fun t ↦ f (t.puzzle, t.key, t.secret) ⟨t.finalReg, t.output⟩) =
      Measure.sum fun z : Puzzle × Key × Secret ↦
        (Pr{let a ← simulateQ (unifFwdAnswerImpl (QueryImpl.ofFn H)).batch' gen}[a = z]) •
          (parallelOracleRuntime H).evalDistMap .instruments (online z.1) ρ (f z) := by
  let : MeasurableSpace (DelayTranscript (ofClassicalGenerator gen solve)
    (TwoPhaseAdversary.withoutPreprocessing A ρ online)) := ⊤
  let : MeasurableSpace (Σ _B : QReg, Out) := ⊤
  unfold delayLawWith
  rw [delayInstrument_withoutPreprocessing]
  simp_rw [QuantumRuntime.evalDistMap_eq_map_evalDist
    _ _ _ _ _ Measurable.of_discrete]
  exact generation_onlineLaw H gen solve
    (TwoPhaseAdversary.withoutPreprocessing A ρ online)
    ⟨A, TwoPhaseAdversary.withoutPreprocessingState A ρ online⟩
    (ρ.prod (parallelOracleRuntime H).init)
    (fun t ↦ f (t.puzzle, t.key, t.secret) ⟨t.finalReg, t.output⟩)

/-- Key-only recovery is the classical generator average of the online success probabilities.
No complete-tuple recovery event or conditioning on successful termination is introduced. -/
theorem delayAdvantage_withoutPreprocessing_ofClassicalGenerator [DecidableEq Key]
    (H : X → Y)
    (gen : OracleComp (unifSpec + (X →ₒ Y).batch) (Puzzle × Key × Secret))
    (solve : Puzzle → QComp (qromBatchSpec X Y) (QReg.of Unit) (QReg.of Unit) (Option Key))
    (A : QReg) (ρ : SubState A)
    (online : Puzzle → QuantumComp LocalSig.instruments (qromBatchSpec X Y) (fun _ ↦ Key) A) :
    delayAdvantage (parallelOracleRuntime H) (ofClassicalGenerator gen solve)
      (TwoPhaseAdversary.withoutPreprocessing A ρ online) =
      ∑' z : Puzzle × Key × Secret,
        (Pr{let a ← simulateQ (unifFwdAnswerImpl (QueryImpl.ofFn H)).batch' gen}[a = z]) *
          (parallelOracleRuntime H).evalDistMap .instruments (online z.1) ρ
            (fun out ↦ decide (out.2 = z.2.1)) {true} := by
  unfold delayAdvantage
  rw [delayLawWith_withoutPreprocessing_ofClassicalGenerator
    (f := fun z out ↦ decide (out.2 = z.2.1))]
  rw [Measure.sum_apply _ (MeasurableSet.singleton true)]
  simp only [Measure.smul_apply, smul_eq_mul]

end Quantum.TimeLockPuzzle
