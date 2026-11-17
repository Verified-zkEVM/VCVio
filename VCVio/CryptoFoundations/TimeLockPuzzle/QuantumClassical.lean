/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.CryptoFoundations.TimeLockPuzzle.Quantum

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
  classical
  let : MeasurableSpace (DelayTranscript (ofClassicalGenerator gen solve)
    (TwoPhaseAdversary.withoutPreprocessing A ρ online)) := ⊤
  unfold delayLawWith
  rw [delayInstrument_withoutPreprocessing]
  change Measure.map
    (fun t : DelayTranscript (ofClassicalGenerator gen solve)
      (TwoPhaseAdversary.withoutPreprocessing A ρ online) ↦
        f (t.puzzle, t.key, t.secret) ⟨t.finalReg, t.output⟩)
    ((DSubInstrument.bind
      (generationInstrument (parallelOracleRuntime H) (ofClassicalGenerator gen solve) A)
      fun z ↦ DSubInstrument.bind ((parallelOracleRuntime H).run .instruments (online z.1))
        fun out ↦ DSubInstrument.ret
          (fun t : DelayTranscript (ofClassicalGenerator gen solve)
            (TwoPhaseAdversary.withoutPreprocessing A ρ online) ↦
              t.finalReg × (parallelOracleRuntime H).D)
          (withoutPreprocessingTranscript (ofClassicalGenerator gen solve)
            A ρ online z out)).outcomeMeasure (ρ.prod (parallelOracleRuntime H).init)) = _
  rw [DSubInstrument.outcomeMeasure_bind,
    Measure.map_sum Measurable.of_discrete.aemeasurable]
  refine congrArg Measure.sum (funext fun z ↦ ?_)
  have hmap := DSubInstrument.map_eq_bind_ret
    (C := fun t : DelayTranscript (ofClassicalGenerator gen solve)
      (TwoPhaseAdversary.withoutPreprocessing A ρ online) ↦
        t.finalReg × (parallelOracleRuntime H).D)
    (withoutPreprocessingTranscript (ofClassicalGenerator gen solve) A ρ online z)
    ((parallelOracleRuntime H).run .instruments (online z.1))
  have hsmul (c : ℝ≥0∞) (μ : (Σ _B : QReg, Out) → Measure β) :
      c • Measure.sum μ = Measure.sum (fun i ↦ c • μ i) := by
    ext s hs
    simp only [Measure.smul_apply, Measure.sum_apply _ hs, smul_eq_mul,
      ENNReal.tsum_mul_left]
  rw [← hmap, DSubInstrument.outcomeMeasure_map,
    Measure.map_sum Measurable.of_discrete.aemeasurable,
    QuantumRuntime.evalDistMap, hsmul]
  refine congrArg Measure.sum (funext fun out ↦ ?_)
  rw [Measure.map_smul _ Measurable.of_discrete.aemeasurable,
    Measure.map_dirac' Measurable.of_discrete, smul_smul]
  congr 1
  rw [DSubInstrument.matrix_post,
    generationInstrument_ofClassicalGenerator_branch H gen solve A z,
    map_smul, Matrix.trace_smul]
  simp only [smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (prEvent_ne_top _)]
  rfl

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
