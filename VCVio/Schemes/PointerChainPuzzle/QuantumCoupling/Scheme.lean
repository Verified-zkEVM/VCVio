/-
Copyright (c) 2026 Quang Dao, Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Alexander Hicks
-/

module
public import VCVio.Schemes.PointerChainPuzzle.QuantumCoupling
import VCVio.OracleComp.EvalDist.Sum

/-!
# Quantum recovery in the programmed pointer-chain experiment

For each fixed raw oracle, the preprocessing and online programs compose on the adversary's
actual retained register. Honest classical generation is an average of these complete runs,
with one oracle throughout and the recovery key retained in the final event. No query bounds
or losslessness assumptions are needed for this representation.

The rank-programmed comparison charges path-input collisions once, with allowance
`solvePoints n m ^ 2 / |Bytes 32|`, where `|Bytes 32| = 2^256`. In the programmed experiment,
preprocessing already queries the fully programmed oracle, and the same oracle answers the
online phase. The path responses are sampled without conditioning on collision-freedom.
-/

public section

open OracleSpec OracleComp Quantum MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PointerChainPuzzle.LeanSeal

variable {b n B : ℕ}

/-- A quantum key-recovery adversary over the full finite raw-byte window. -/
abbrev WindowAdversary (b n B : ℕ) :=
  Quantum.TimeLockPuzzle.Adversary (qromBatchSpec (ByteArray.Bounded B) (Bytes 32))
    (Puzzle b n) (Bytes 32)

/-- The complete preprocessing and online program for a fixed public puzzle. Only the online
continuation receives the puzzle; it retains its actual preprocessing register and state. -/
@[expose]
noncomputable def windowRecoveryProgram (adv : WindowAdversary b n B) (puzzle : Puzzle b n) :
    QuantumComp LocalSig.instruments (qromBatchSpec (ByteArray.Bounded B) (Bytes 32))
      (fun _ ↦ Bytes 32) adv.initialReg :=
  adv.preprocess.bind fun M state ↦ adv.online M state puzzle

/-- Unconditional key recovery under one fixed raw oracle. The initial state is supplied once,
and failed preprocessing or online branches retain their missing mass. -/
@[expose]
noncomputable def windowRecoveryAt (adv : WindowAdversary b n B)
    (H : ByteArray.Bounded B → Bytes 32) (puzzle : Puzzle b n) (key : Bytes 32) : ℝ≥0∞ :=
  (parallelOracleRuntime H).evalDistMap .instruments (windowRecoveryProgram adv puzzle)
    adv.initialState (fun leaf ↦ leaf.2 = key) {True}

/-- Fixed-oracle recovery is a subprobability event, including subnormalized initial states. -/
theorem windowRecoveryAt_le_one (adv : WindowAdversary b n B)
    (H : ByteArray.Bounded B → Bytes 32) (puzzle : Puzzle b n) (key : Bytes 32) :
    windowRecoveryAt adv H puzzle key ≤ 1 :=
  measure_le_one _ _

section Fixed

variable (saltSpace : MeasurableSpace (Bytes 16))
  [@MeasurableSingletonClass (Bytes 16) saltSpace]
  [MeasurableSpace (Bytes b)] [MeasurableSingletonClass (Bytes b)]

/-- At a fixed raw oracle, the actual three-phase experiment averages complete recovery runs
over the honest salt and links. Generation does not reset or normalize preprocessing memory. -/
theorem delayAdvantage_quantumWindowScheme_eq_lintegral {m : ℕ} [NeZero n]
    (hB : hashInputBound b ≤ B) (adv : WindowAdversary b n B)
    (H : ByteArray.Bounded B → Bytes 32) :
    letI := saltSpace
    Quantum.TimeLockPuzzle.delayAdvantage (parallelOracleRuntime H)
        (quantumWindowScheme (n := n) hB m) adv =
      ∫⁻ salt, ∫⁻ xs : Fin n → Bytes b,
        windowRecoveryAt adv H
          (honestPuzzle m (ctx b n m) id (oracles (extendWindowOracle H)) salt xs)
          (honestKey m (ctx b n m) id (oracles (extendWindowOracle H)) salt xs)
        ∂(uniformOn Set.univ : Measure (Fin n → Bytes b))
        ∂(uniformOn Set.univ : Measure (Bytes 16)) := by
  let : MeasurableSpace (Bytes 16) := saltSpace
  let : MeasurableSpace (Puzzle b n × Bytes 32) := ⊤
  let : MeasurableSpace (Puzzle b n × Bytes 32 × Unit) := ⊤
  rw [quantumWindowScheme, Quantum.TimeLockPuzzle.delayAdvantage_ofClassicalGenerator,
    simulateQ_map, simulateQ_windowScheme_gen, tsum_prEvent_map_mul]
  change (∑' pk : Puzzle b n × Bytes 32,
    (Pr{let y ← gen (extendWindowOracle H) m}[y = pk]) *
      windowRecoveryAt adv H pk.1 pk.2) = _
  rw [gen, tsum_prEvent_bind_mul]
  simp_rw [tsum_prEvent_bind_mul, tsum_prEvent_pure_mul]
  rw [← lintegral_evalDist_eq_tsum]
  simp_rw [← lintegral_evalDist_eq_tsum, SampleableType.evalDist_uniformSample]
  apply lintegral_congr
  intro salt
  apply lintegral_congr
  intro xs
  rw [honestPuzzle_oracles, honestKey_oracles]

variable (keySpace : MeasurableSpace (Bytes 32))
  [@MeasurableSingletonClass (Bytes 32) keySpace]

/-- The actual QROM experiment is one raw-oracle average of honest salt/link averages.
The same raw function answers preprocessing, honest generation and online recovery. -/
theorem qromDelayAdvantage_quantumWindowScheme_eq_lintegral {m : ℕ} [NeZero n]
    (hB : hashInputBound b ≤ B) (adv : WindowAdversary b n B) :
    letI := saltSpace
    letI := keySpace
    Quantum.TimeLockPuzzle.qromDelayAdvantage (quantumWindowScheme (n := n) hB m) adv =
      ∫⁻ H, ∫⁻ salt, ∫⁻ xs : Fin n → Bytes b,
        windowRecoveryAt adv H
          (honestPuzzle m (ctx b n m) id (oracles (extendWindowOracle H)) salt xs)
          (honestKey m (ctx b n m) id (oracles (extendWindowOracle H)) salt xs)
        ∂(uniformOn Set.univ : Measure (Fin n → Bytes b))
        ∂(uniformOn Set.univ : Measure (Bytes 16))
        ∂(uniformOn Set.univ : Measure (ByteArray.Bounded B → Bytes 32)) := by
  let : MeasurableSpace (Bytes 16) := saltSpace
  let : MeasurableSpace (Bytes 32) := keySpace
  rw [Quantum.TimeLockPuzzle.qromDelayAdvantage,
    Quantum.TimeLockPuzzle.sampledDelayAdvantage_eq_sum, lintegral_uniformOn_univ,
    div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro H _
  rw [delayAdvantage_quantumWindowScheme_eq_lintegral saltSpace]
  exact mul_comm _ _

end Fixed

/-- Recovery in the unconditioned programmed experiment. A full raw response is sampled for
every path value, including every mask tail. One programmed oracle serves both adversary phases,
and the online continuation retains its actual preprocessing memory. -/
@[expose]
noncomputable def programmedWindowRecoveryAdvantage {m : ℕ} [NeZero n]
    (hb : b ≤ 32) (hB : hashInputBound b ≤ B) (adv : WindowAdversary b n B) : ℝ≥0∞ :=
  letI : MeasurableSpace (Bytes 32) := ⊤
  letI : MeasurableSpace (Bytes 16) := ⊤
  letI : MeasurableSpace (Bytes b) := ⊤
  ∫⁻ salt, ∫⁻ p : Bytes b × (Fin (n - 1) → Bytes b),
    ∫⁻ H, ∫⁻ W : PathValue n m → Bytes 32,
      windowRecoveryAt adv (programPath hb hB salt p.1 p.2 H W)
        (labelPuzzle salt p.1 p.2 (pathLabels hb W)) ((pathLabels hb W) .key)
      ∂(uniformOn Set.univ : Measure (PathValue n m → Bytes 32))
      ∂(uniformOn Set.univ : Measure (ByteArray.Bounded B → Bytes 32))
      ∂(uniformOn Set.univ : Measure (Bytes b × (Fin (n - 1) → Bytes b)))
      ∂(uniformOn Set.univ : Measure (Bytes 16))

/-- The unconditioned programmed recovery game retains its subprobability mass. -/
theorem programmedWindowRecoveryAdvantage_le_one {m : ℕ} [NeZero n]
    (hb : b ≤ 32) (hB : hashInputBound b ≤ B) (adv : WindowAdversary b n B) :
    programmedWindowRecoveryAdvantage (m := m) hb hB adv ≤ 1 := by
  let : MeasurableSpace (Bytes 32) := ⊤
  let : MeasurableSpace (Bytes 16) := ⊤
  let : MeasurableSpace (Bytes b) := ⊤
  unfold programmedWindowRecoveryAdvantage
  calc
    _ ≤ ∫⁻ _salt, ∫⁻ _p : Bytes b × (Fin (n - 1) → Bytes b),
        ∫⁻ _H : ByteArray.Bounded B → Bytes 32,
          ∫⁻ _W : PathValue n m → Bytes 32, (1 : ℝ≥0∞)
          ∂(uniformOn Set.univ : Measure (PathValue n m → Bytes 32))
          ∂(uniformOn Set.univ : Measure (ByteArray.Bounded B → Bytes 32))
          ∂(uniformOn Set.univ : Measure (Bytes b × (Fin (n - 1) → Bytes b)))
          ∂(uniformOn Set.univ : Measure (Bytes 16)) := by
      apply lintegral_mono
      intro salt
      apply lintegral_mono
      intro p
      apply lintegral_mono
      intro H
      apply lintegral_mono
      intro W
      exact windowRecoveryAt_le_one adv _ _ _
    _ = 1 := by simp

/-- Compare actual quantum recovery with the unconditioned rank-programmed game, charging
path-input collisions once. This holds for every two-phase adversary, with unrestricted
retained memory and no query-budget assumption. Both phases use one programmed oracle;
the hidden path responses are not conditioned on collision-freedom. -/
theorem qromDelayAdvantage_quantumWindowScheme_le_programmed {m : ℕ} [NeZero n]
    (hb : b ≤ 32) (hn : n < 2 ^ 32) (hB : hashInputBound b ≤ B)
    (adv : WindowAdversary b n B) :
    Quantum.TimeLockPuzzle.qromDelayAdvantage (quantumWindowScheme (n := n) hB m) adv ≤
      programmedWindowRecoveryAdvantage (m := m) hb hB adv +
        (solvePoints n m : ℝ≥0∞) ^ 2 / Fintype.card (Bytes 32) := by
  let : MeasurableSpace (Bytes 32) := ⊤
  let : MeasurableSpace (Bytes 16) := ⊤
  let : MeasurableSpace (Bytes b) := ⊤
  have h := real_le_programmed_add_collision (m := m)
    (keySpace := inferInstance) (saltSpace := inferInstance) hb hn hB
    (windowRecoveryAt adv) (windowRecoveryAt_le_one adv)
  rw [← qromDelayAdvantage_quantumWindowScheme_eq_lintegral
    (saltSpace := inferInstance) (keySpace := inferInstance) hB adv] at h
  exact h

/-- Compare actual key recovery with programmed recovery and its collision allowance, capped
by the subprobability bound of one. In the programmed experiment, both adversary phases query
the same programmed oracle. -/
theorem qromDelayAdvantage_quantumWindowScheme_le_min_programmed {m : ℕ} [NeZero n]
    (hb : b ≤ 32) (hn : n < 2 ^ 32) (hB : hashInputBound b ≤ B)
    (adv : WindowAdversary b n B) :
    Quantum.TimeLockPuzzle.qromDelayAdvantage (quantumWindowScheme (n := n) hB m) adv ≤
      min 1 (programmedWindowRecoveryAdvantage (m := m) hb hB adv +
        (solvePoints n m : ℝ≥0∞) ^ 2 / Fintype.card (Bytes 32)) := by
  refine le_min ?_ (qromDelayAdvantage_quantumWindowScheme_le_programmed hb hn hB adv)
  exact Quantum.TimeLockPuzzle.sampledDelayAdvantage_le_one
    parallelOracleRuntime (quantumWindowScheme hB m) adv

end PointerChainPuzzle.LeanSeal
