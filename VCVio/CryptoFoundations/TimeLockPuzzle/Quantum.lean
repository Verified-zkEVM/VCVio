/-
Copyright (c) 2026 Quang Dao, Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Alexander Hicks
-/

module
public import VCVio.CryptoFoundations.TimeLockPuzzle
public import VCVio.Quantum.Oracle.ClassicalParallel
public import QuantumFoundations.SubInstrument.Relabel

/-!
# Quantum two-phase time-lock puzzle experiments

A generator publishes a classical puzzle and retains a classical key and auxiliary secret data.
The adversary first preprocesses the oracle, retains an outcome-dependent quantum register and
classical state, and receives only the published puzzle during its online phase. Recovery means
outputting the key; the auxiliary secret is available to analysis observers, not to the adversary.
The honest generator starts and ends on the trivial register: its internal quantum workspace is
discarded, while adversary memory and the runtime's private oracle register persist.

`delayInstrument` composes the three phases as dependent subinstruments. `delayLawWith` initializes
the joint adversary/oracle state once. Generation operates on the oracle register with adversary
memory framed around it. No private state is discarded or initialized between phases, so
preprocessing may correlate retained adversary memory with a compressed or
purified oracle database. The joint transcript retains the preprocessing branch, published puzzle,
key, auxiliary secret and output. Lost mass remains failure, without postselection normalization.

`DelayBudget` charges preprocessing points and online rounds, points and maximum width. The
adversary's clock starts after generation publishes the puzzle. Honest generation queries and
preprocessing calls are outside this online clock; local operations cost no oracle rounds.

`sampledDelayLawWith` averages complete three-phase runs over one hidden runtime parameter.
`qromDelayAdvantage` specializes it to one uniformly sampled function shared across all phases.
The adversary, its initial state and the puzzle algorithms are fixed before this sampling.

## References

* V. Buterin, Q. Dao and J. Drake, *leanSeal: A Committee-Free Encrypted Mempool from Hashes
  Alone*, October 2026, §4.2. The classical two-phase delay experiment supplies the phase and
  clock conventions; the adversary interface here permits quantum preprocessing and memory.
-/

public section

open MeasureTheory Matrix
open scoped ENNReal Kronecker

namespace Quantum

/-- A puzzle with classical public, key and auxiliary-secret outputs. Honest algorithms discard
all internal quantum workspace; the solver may report a malformed puzzle by returning `none`. -/
structure TimeLockPuzzle (spec : QuantumOracleSpec.{0, 0}) (Puzzle Key : Type) where
  /-- Hidden classical generator data retained for analysis, beyond the recovery key. -/
  Secret : Type
  /-- Generate the public puzzle, recovery key and auxiliary secret. -/
  gen : QComp spec (QReg.of Unit) (QReg.of Unit) (Puzzle × Key × Secret)
  /-- Recover the key, or report a malformed puzzle. -/
  solve : Puzzle → QComp spec (QReg.of Unit) (QReg.of Unit) (Option Key)

namespace TimeLockPuzzle

variable {spec : QuantumOracleSpec.{0, 0}} {Puzzle Key Out : Type}

/-- A two-phase quantum adversary. Every preprocessing branch retains its own quantum register
and classical state. The online phase receives the state and public puzzle, without the key or
auxiliary generator secret; its final quantum register may also depend on outcomes. -/
structure TwoPhaseAdversary (spec : QuantumOracleSpec.{0, 0}) (Puzzle Out : Type) where
  /-- The register present before preprocessing. -/
  initialReg : QReg
  /-- Oracle-independent initial adversary state, allowing missing mass. -/
  initialState : SubState initialReg
  /-- Classical preprocessing information on each possible retained register. -/
  State : QReg → Type
  /-- Quantum preprocessing before the puzzle exists. -/
  preprocess : QuantumComp LocalSig.instruments spec State initialReg
  /-- Online key recovery using the retained memory and published puzzle. -/
  online : (M : QReg) → State M → Puzzle → QuantumComp LocalSig.instruments spec
    (fun _ ↦ Out) M

/-- A key-recovery adversary outputs only a candidate key. -/
abbrev Adversary (spec : QuantumOracleSpec.{0, 0}) (Puzzle Key : Type) :=
  TwoPhaseAdversary spec Puzzle Key

/-- Phase-local query resources. Honest generation consumes none of the online budget. -/
structure DelayBudget where
  /-- Total points queried before the puzzle exists. -/
  preprocessingPoints : ℕ
  /-- Total online oracle rounds after publication. -/
  onlineRounds : ℕ
  /-- Total points across all online rounds. -/
  onlinePoints : ℕ
  /-- Maximum width of each online round. -/
  onlineWidth : ℕ

/-- Syntactic preprocessing and online bounds on every branch, including zero-weight branches.
The online bounds hold for every retained register, classical state and public puzzle. -/
@[expose]
def TwoPhaseAdversary.IsQueryBound {P : Type} {In : P → QReg}
    (adv : TwoPhaseAdversary (uBatchSpec P In) Puzzle Out) (b : DelayBudget) : Prop :=
  adv.preprocess.IsPointBound b.preprocessingPoints ∧
    ∀ M state puzzle,
      (adv.online M state puzzle).IsTotalQueryBound b.onlineRounds ∧
        (adv.online M state puzzle).IsPointBound b.onlinePoints ∧
          (adv.online M state puzzle).IsWidthBound b.onlineWidth

/-- An adversary that starts its online algorithm immediately, retaining its initial register. -/
@[expose]
noncomputable def TwoPhaseAdversary.withoutPreprocessing (A : QReg) (ρ : SubState A)
    (online : Puzzle → QuantumComp LocalSig.instruments spec (fun _ ↦ Out) A) :
    TwoPhaseAdversary spec Puzzle Out where
  initialReg := A
  initialState := ρ
  State M := PLift (M = A)
  preprocess := QuantumComp.pure ⟨rfl⟩
  online _ h puzzle := by rcases h with ⟨h⟩; cases h; exact online puzzle

/-- The complete classical transcript available to an analysis observer. Neither the recovery
key nor the auxiliary secret is an input to the online adversary. -/
structure DelayTranscript (tlp : TimeLockPuzzle spec Puzzle Key)
    (adv : TwoPhaseAdversary spec Puzzle Out) where
  /-- The quantum register left after preprocessing. -/
  preprocessingReg : QReg
  /-- The retained classical preprocessing state. -/
  preprocessingState : adv.State preprocessingReg
  /-- The published puzzle. -/
  puzzle : Puzzle
  /-- The actual recovery key. -/
  key : Key
  /-- Hidden generator data retained jointly with the event being checked. -/
  secret : tlp.Secret
  /-- The register left after online execution. -/
  finalReg : QReg
  /-- The adversary's output. -/
  output : Out

/-- Expose the trivial honest-generator register and runtime memory while retaining the
adversary's register as a spectator. -/
@[expose]
def generationEquiv (M D : Type*) : M × D ≃ (Unit × D) × M where
  toFun md := (((), md.2), md.1)
  invFun d := (d.2, d.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Run honest generation on the same private oracle register, leaving the retained adversary
register as a spectator. Inputs may be correlated across the two registers. -/
@[expose]
noncomputable def generationInstrument (R : QuantumRuntime spec)
    (tlp : TimeLockPuzzle spec Puzzle Key) (M : QReg) :
    SubInstrument (M × R.D) (M × R.D) (Puzzle × Key × tlp.Secret) :=
  ((R.run₂ .instruments tlp.gen).frame M).reindex
    (generationEquiv M R.D).symm (generationEquiv M R.D).symm

/-- Framing honest generation preserves its losslessness on the full joint state. -/
theorem generationInstrument_lossless (R : QuantumRuntime spec)
    (tlp : TimeLockPuzzle spec Puzzle Key) (M : QReg)
    (hgen : (R.run₂ .instruments tlp.gen).Lossless) :
    (generationInstrument R tlp M).Lossless :=
  (hgen.frame M).reindex _ _

/-- The complete three-phase instrument on adversary memory and one shared private oracle
register. Every online continuation sees its actual preprocessing state and published puzzle. -/
@[expose]
noncomputable def delayInstrument (R : QuantumRuntime spec)
    (tlp : TimeLockPuzzle spec Puzzle Key) (adv : TwoPhaseAdversary spec Puzzle Out) :
    DSubInstrument (adv.initialReg × R.D) (DelayTranscript tlp adv)
      (fun t ↦ t.finalReg × R.D) :=
  DSubInstrument.bind (R.run .instruments adv.preprocess) fun pre ↦
    DSubInstrument.bind (generationInstrument R tlp pre.1) fun pk ↦
      DSubInstrument.bind (R.run .instruments (adv.online pre.1 pre.2 pk.1)) fun out ↦
        DSubInstrument.ret (fun t : DelayTranscript tlp adv ↦ t.finalReg × R.D)
          ⟨pre.1, pre.2, pk.1, pk.2.1, pk.2.2, out.1, out.2⟩

/-- Composing three lossless phases gives a lossless instrument without initializing another
oracle state between phases. -/
theorem delayInstrument_lossless (R : QuantumRuntime spec)
    (tlp : TimeLockPuzzle spec Puzzle Key) (adv : TwoPhaseAdversary spec Puzzle Out)
    (hpre : (R.run .instruments adv.preprocess).Lossless)
    (hgen : (R.run₂ .instruments tlp.gen).Lossless)
    (honline : ∀ M state puzzle, (R.run .instruments (adv.online M state puzzle)).Lossless) :
    (delayInstrument R tlp adv).Lossless := by
  unfold delayInstrument
  refine DSubInstrument.Lossless.bind hpre (fun pre ↦ ?_)
  refine DSubInstrument.Lossless.bind (generationInstrument_lossless R tlp pre.1 hgen)
    (fun pk ↦ ?_)
  refine DSubInstrument.Lossless.bind (honline pre.1 pre.2 pk.1) (fun out ↦ ?_)
  exact DSubInstrument.lossless_ret _ _

/-- Observe the complete execution from the single initial product state. Observers may use
all retained challenger data, while lost mass remains failure. -/
@[expose]
noncomputable def delayLawWith {β : Type*} [MeasurableSpace β]
    (R : QuantumRuntime spec) (tlp : TimeLockPuzzle spec Puzzle Key)
    (adv : TwoPhaseAdversary spec Puzzle Out) (f : DelayTranscript tlp adv → β) : Measure β :=
  letI : MeasurableSpace (DelayTranscript tlp adv) := ⊤
  ((delayInstrument R tlp adv).outcomeMeasure (adv.initialState.prod R.init)).map f

/-- Observed delay laws are subprobability measures, without renormalizing successful branches. -/
instance delayLawWith.instIsSubprobabilityMeasure {β : Type*} [MeasurableSpace β]
    (R : QuantumRuntime spec) (tlp : TimeLockPuzzle spec Puzzle Key)
    (adv : TwoPhaseAdversary spec Puzzle Out) (f : DelayTranscript tlp adv → β) :
    IsSubprobabilityMeasure (delayLawWith R tlp adv f) := by
  dsimp [delayLawWith]
  infer_instance

/-- Every event sums the weights of the joint transcripts on which it occurs. -/
theorem delayLawWith_apply {β : Type*} [MeasurableSpace β]
    (R : QuantumRuntime spec) (tlp : TimeLockPuzzle spec Puzzle Key)
    (adv : TwoPhaseAdversary spec Puzzle Out) (f : DelayTranscript tlp adv → β)
    {s : Set β} (hs : MeasurableSet s) :
    delayLawWith R tlp adv f s =
      ∑' t, ENNReal.ofReal ((delayInstrument R tlp adv).branch t
        (adv.initialState.prod R.init).matrix).trace.re * s.indicator 1 (f t) := by
  let : MeasurableSpace (DelayTranscript tlp adv) := ⊤
  rw [delayLawWith, Measure.map_apply Measurable.of_discrete hs,
    DSubInstrument.outcomeMeasure_apply _ _ MeasurableSet.of_discrete]
  rfl

/-- A lossless execution has exactly its initial joint mass, with both initial traces used once. -/
theorem delayLawWith_apply_univ_of_lossless {β : Type*} [MeasurableSpace β]
    (R : QuantumRuntime spec) (tlp : TimeLockPuzzle spec Puzzle Key)
    (adv : TwoPhaseAdversary spec Puzzle Out) (f : DelayTranscript tlp adv → β)
    (h : (delayInstrument R tlp adv).Lossless) :
    delayLawWith R tlp adv f Set.univ =
      ENNReal.ofReal (adv.initialState.matrix.trace.re * R.init.matrix.trace.re) := by
  let : MeasurableSpace (DelayTranscript tlp adv) := ⊤
  rw [delayLawWith, Measure.map_apply Measurable.of_discrete MeasurableSet.univ,
    Set.preimage_univ, h.outcomeMeasure_apply_univ, SubState.trace_re_prod]

/-- Unconditional recovery probability: only the output and actual key are compared. -/
@[expose]
noncomputable def delayAdvantage [DecidableEq Key] (R : QuantumRuntime spec)
    (tlp : TimeLockPuzzle spec Puzzle Key) (adv : Adversary spec Puzzle Key) : ℝ≥0∞ :=
  delayLawWith R tlp adv (fun t ↦ decide (t.output = t.key)) {true}

/-- Key-recovery advantage is at most one, including subnormalized initial states. -/
theorem delayAdvantage_le_one [DecidableEq Key] (R : QuantumRuntime spec)
    (tlp : TimeLockPuzzle spec Puzzle Key) (adv : Adversary spec Puzzle Key) :
    delayAdvantage R tlp adv ≤ 1 :=
  measure_le_one _ _

/-- Average complete executions over one uniformly hidden runtime parameter. The observer sees
that same parameter and the joint transcript; no phase samples an independent parameter. -/
@[expose]
noncomputable def sampledDelayLawWith {Ω β : Type*} [Fintype Ω] [MeasurableSpace β]
    (R : Ω → QuantumRuntime spec) (tlp : TimeLockPuzzle spec Puzzle Key)
    (adv : TwoPhaseAdversary spec Puzzle Out) (f : Ω → DelayTranscript tlp adv → β) :
    Measure β :=
  (Fintype.card Ω : ℝ≥0∞)⁻¹ • ∑ ω, delayLawWith (R ω) tlp adv (f ω)

/-- A finite sampled law is the uniform average of its fixed-parameter laws. -/
theorem sampledDelayLawWith_apply {Ω β : Type*} [Fintype Ω] [MeasurableSpace β]
    (R : Ω → QuantumRuntime spec) (tlp : TimeLockPuzzle spec Puzzle Key)
    (adv : TwoPhaseAdversary spec Puzzle Out) (f : Ω → DelayTranscript tlp adv → β)
    (s : Set β) :
    sampledDelayLawWith R tlp adv f s =
      ∑ ω, (Fintype.card Ω : ℝ≥0∞)⁻¹ * delayLawWith (R ω) tlp adv (f ω) s := by
  rw [sampledDelayLawWith, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply,
    smul_eq_mul, Finset.mul_sum]

/-- Recovery against one uniformly chosen runtime, with the adversary fixed before sampling. -/
@[expose]
noncomputable def sampledDelayAdvantage {Ω : Type*} [Fintype Ω] [DecidableEq Key]
    (R : Ω → QuantumRuntime spec) (tlp : TimeLockPuzzle spec Puzzle Key)
    (adv : Adversary spec Puzzle Key) : ℝ≥0∞ :=
  sampledDelayLawWith R tlp adv (fun _ t ↦ decide (t.output = t.key)) {true}

/-- Sampling a runtime outside the whole experiment averages the complete recovery probabilities. -/
theorem sampledDelayAdvantage_eq_sum {Ω : Type*} [Fintype Ω] [DecidableEq Key]
    (R : Ω → QuantumRuntime spec) (tlp : TimeLockPuzzle spec Puzzle Key)
    (adv : Adversary spec Puzzle Key) :
    sampledDelayAdvantage R tlp adv =
      ∑ ω, (Fintype.card Ω : ℝ≥0∞)⁻¹ * delayAdvantage (R ω) tlp adv := by
  rw [sampledDelayAdvantage, sampledDelayLawWith_apply]
  rfl

/-- Uniformly sampling a runtime preserves the unconditional probability bound. -/
theorem sampledDelayAdvantage_le_one {Ω : Type*} [Fintype Ω] [Nonempty Ω] [DecidableEq Key]
    (R : Ω → QuantumRuntime spec) (tlp : TimeLockPuzzle spec Puzzle Key)
    (adv : Adversary spec Puzzle Key) : sampledDelayAdvantage R tlp adv ≤ 1 := by
  rw [sampledDelayAdvantage_eq_sum]
  calc
    _ ≤ ∑ _ω : Ω, (Fintype.card Ω : ℝ≥0∞)⁻¹ * 1 := by
      gcongr with ω
      exact delayAdvantage_le_one _ _ _
    _ = 1 := by
      simp only [mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      exact ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
        (ENNReal.natCast_ne_top _)

section QROM

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]

/-- Recovery probability against one uniformly sampled function shared by preprocessing,
honest generation and online execution. -/
@[expose]
noncomputable def qromDelayAdvantage (tlp : TimeLockPuzzle (qromBatchSpec X Y) Puzzle Key)
    (adv : Adversary (qromBatchSpec X Y) Puzzle Key) [DecidableEq Key] : ℝ≥0∞ :=
  sampledDelayAdvantage parallelOracleRuntime tlp adv

/-- Quantum delay security in the QROM under separate preprocessing and online resources.
The adversary and its initial state are chosen independently of the sampled function.
This predicate is a security target to establish by an oracle argument. A bound for a named
adversary adapter yields it only with a coverage proof for all budget-bounded adversaries. -/
@[expose]
def QROMDelaySecure [DecidableEq Key] (tlp : TimeLockPuzzle (qromBatchSpec X Y) Puzzle Key)
    (b : DelayBudget) (ε : ℝ≥0∞) : Prop :=
  ∀ adv : Adversary (qromBatchSpec X Y) Puzzle Key,
    adv.IsQueryBound b → qromDelayAdvantage tlp adv ≤ ε

end QROM

end TimeLockPuzzle
end Quantum

namespace TimeLockPuzzle

open Quantum

variable {X Y Puzzle Key : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [AddCommGroup Y]

/-- Embed an honest classical puzzle into quantum basis calls and local private coins. The
auxiliary analysis secret is trivial; only the generated key is retained as hidden output. -/
@[expose]
noncomputable def toQuantum (tlp : _root_.TimeLockPuzzle (X →ₒ Y) Puzzle Key) :
    Quantum.TimeLockPuzzle (qromBatchSpec X Y) Puzzle Key where
  Secret := Unit
  gen := ((fun pk : Puzzle × Key ↦ (pk.1, pk.2, ())) <$> tlp.gen).toQuantumBatch
  solve puzzle := (tlp.solve puzzle).toQuantumBatch

/-- The honest quantum generator preserves the classical round and point budgets. -/
theorem IsGenQueryBound.toQuantum {tlp : _root_.TimeLockPuzzle (X →ₒ Y) Puzzle Key}
    {b : ℕ × ℕ} (h : tlp.IsGenQueryBound b) :
    tlp.toQuantum.gen.IsTotalQueryBound b.1 ∧ tlp.toQuantum.gen.IsPointBound b.2 := by
  have hg : OracleComp.IsOnlineQueryBound
      ((fun pk : Puzzle × Key ↦ (pk.1, pk.2, ())) <$> tlp.gen) b := by
    simpa only [IsGenQueryBound, OracleComp.IsOnlineQueryBound,
      OracleComp.isQueryBound_map_iff] using h
  exact ⟨hg.isTotalQueryBound_toQuantumBatch, hg.isPointBound_toQuantumBatch⟩

end TimeLockPuzzle
