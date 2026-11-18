/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.CryptoFoundations.TimeLockPuzzle.QuantumClassical
public import VCVio.Quantum.Oracle.MaskedChain.Bounds
import VCVio.OracleComp.EvalDist.Sum

/-!
# The idealized masked-chain time-lock puzzle

Generation samples a tuple of independent uniform vertices, queries all but the last in one
parallel round and publishes their oracle values masked by the following vertices. The solver
recovers the endpoint by successive single-point rounds. The quantum experiment retains the
complete tuple as hidden challenger data and exposes only the public puzzle to its adversary.

For a chain with `q + 1` links, generation uses one round and `q + 1` points; the honest
solver uses `q + 1` sequential rounds and points. The named no-preprocessing adversary adapter
has exactly the idealized endpoint experiment's recovery probability. Its delay bound permits
at most `q` online rounds and bounds each round's width. Oracle preprocessing and the exact
`PointerChainPuzzle` encoding are separate security obligations.

## Main statements

* `evalDist_scheme_solve_publicPuzzle`: the honest quantum solver recovers the sampled endpoint.
* `scheme_gen_queryBound` and `scheme_solve_queryBound`: the honest round and point budgets.
* `qromDelayAdvantage_eq_recoveryAdvantage`: exact agreement of the named puzzle experiment
  with the idealized endpoint game.
* `qromDelayAdvantage_le`: the depth bound for an online adversary without preprocessing.

## References

* Afshar et al., *On the (Im)possibility of Time-Lock Puzzles in the Quantum Random Oracle
  Model*, Asiacrypt 2023, §5, Definition 5.1.
-/

public section

open OracleComp OracleSpec Quantum MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MaskedChainPuzzle

variable {G : Type} [AddCommGroup G]

/-- Classical local coins and parallel calls to the chain oracle. -/
abbrev RoundComp (G : Type) := OracleComp (unifSpec + (G →ₒ G).batch)

/-- One generation round from an already sampled complete hidden vertex tuple. -/
@[expose]
def genWith {q : ℕ} (vertices : Fin (q + 2) → G) :
    RoundComp G (Quantum.MaskedChain.Puzzle G q × G × (Fin (q + 2) → G)) := do
  let answers ← queryRound (fun i : Fin (q + 1) ↦ vertices i.castSucc)
  pure ((vertices 0, fun i ↦ answers i + vertices i.succ),
    vertices (Fin.last (q + 1)), vertices)

/-- Uniformly sample the complete hidden tuple, then query its chain inputs in one round. -/
@[expose]
noncomputable def gen [Fintype G] (q : ℕ) :
    RoundComp G (Quantum.MaskedChain.Puzzle G q × G × (Fin (q + 2) → G)) :=
  letI := SampleableType.ofFintype (Fin (q + 2) → G)
  do
    let vertices ← $ᵗ (Fin (q + 2) → G)
    genWith vertices

/-- Follow the masked links in order, making one width-one call for every link. -/
@[expose]
def solveFrom : {n : ℕ} → (Fin n → G) → G → RoundComp G G
  | 0, _, x => pure x
  | _ + 1, masks, x => do
      let answer ← queryPoint x
      solveFrom (Fin.tail masks) (masks 0 - answer)

/-- Recover the last vertex by sequentially unmasking every link. -/
@[expose]
def solve {q : ℕ} (puzzle : Quantum.MaskedChain.Puzzle G q) : RoundComp G (Option G) :=
  some <$> solveFrom puzzle.2 puzzle.1

/-- The honest idealized puzzle as a quantum two-phase experiment. The hidden secret is the
complete sampled tuple; recovery asks only for its final vertex. -/
@[expose, reducible]
noncomputable def scheme [Fintype G] [DecidableEq G] (q : ℕ) :
    Quantum.TimeLockPuzzle (qromBatchSpec G G) (Quantum.MaskedChain.Puzzle G q) G :=
  Quantum.TimeLockPuzzle.ofClassicalGenerator (gen q) (fun puzzle ↦ (solve puzzle).toQuantumBatch)

/-- Fixed-function generation retains the real public masks, endpoint and complete tuple. -/
theorem simulateQ_genWith {q : ℕ} (H : G → G) (vertices : Fin (q + 2) → G) :
    simulateQ (unifFwdAnswerImpl (QueryImpl.ofFn H)).batch' (genWith vertices) =
      pure (Quantum.MaskedChain.publicPuzzle H vertices,
        vertices (Fin.last (q + 1)), vertices) := by
  rw [genWith, simulateQ_bind, simulateQ_queryRound, pure_bind, simulateQ_pure]
  rfl

/-- Under its generating oracle, every masked link unmasks to its sampled successor. -/
theorem simulateQ_solveFrom (H : G → G) (n : ℕ) (vertices : Fin (n + 1) → G) :
    simulateQ (unifFwdAnswerImpl (QueryImpl.ofFn H)).batch'
      (solveFrom (fun i : Fin n ↦ H (vertices i.castSucc) + vertices i.succ) (vertices 0)) =
        pure (vertices (Fin.last n)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [solveFrom, simulateQ_bind, simulateQ_queryPoint, pure_bind]
    have he : H (vertices 0) + vertices 1 - H (vertices 0) = vertices 1 := by abel
    change simulateQ (unifFwdAnswerImpl (QueryImpl.ofFn H)).batch'
      (solveFrom (Fin.tail (fun i : Fin (n + 1) ↦ H (vertices i.castSucc) + vertices i.succ))
        (H (vertices 0) + vertices 1 - H (vertices 0))) = _
    rw [he]
    exact ih (Fin.tail vertices)

/-- The honest solver recovers the generated endpoint for every fixed function and tuple. -/
theorem simulateQ_solve_publicPuzzle {q : ℕ} (H : G → G) (vertices : Fin (q + 2) → G) :
    simulateQ (unifFwdAnswerImpl (QueryImpl.ofFn H)).batch'
      (solve (Quantum.MaskedChain.publicPuzzle H vertices)) =
        pure (some (vertices (Fin.last (q + 1)))) := by
  rw [solve, simulateQ_map]
  rw [Quantum.MaskedChain.publicPuzzle, simulateQ_solveFrom, map_pure]

/-! ## Honest query budgets -/

/-- Honest generation from a fixed tuple uses one round and `q + 1` points. -/
theorem isOnlineQueryBound_genWith {q : ℕ} (vertices : Fin (q + 2) → G) :
    IsOnlineQueryBound (genWith vertices) (1, q + 1) := by
  rw [genWith]
  exact isOnlineQueryBound_bind_le (1, q + 1) (0, 0)
    (isOnlineQueryBound_queryRound _) (fun _ ↦ isOnlineQueryBound_pure _ _)
    ⟨by omega, by omega⟩

/-- Local uniform sampling adds no oracle calls to the generator's single round. -/
theorem isOnlineQueryBound_gen [Fintype G] (q : ℕ) :
    IsOnlineQueryBound (gen (G := G) q) (1, q + 1) := by
  let _ := SampleableType.ofFintype (Fin (q + 2) → G)
  rw [gen]
  exact isOnlineQueryBound_bind_le (0, 0) (1, q + 1)
    (isOnlineQueryBound_liftComp ($ᵗ (Fin (q + 2) → G)) (0, 0))
    (fun vertices ↦ isOnlineQueryBound_genWith vertices) ⟨by omega, by omega⟩

/-- Following `n` masked links uses `n` rounds and `n` points. -/
theorem isOnlineQueryBound_solveFrom (n : ℕ) (masks : Fin n → G) (x : G) :
    IsOnlineQueryBound (solveFrom masks x) (n, n) := by
  induction n generalizing x with
  | zero => exact isOnlineQueryBound_pure _ _
  | succ n ih =>
    rw [solveFrom]
    exact isOnlineQueryBound_bind_le (1, 1) (n, n) (isOnlineQueryBound_queryPoint _)
      (fun answer ↦ ih (Fin.tail masks) (masks 0 - answer)) ⟨by omega, by omega⟩

/-- Returning the recovered endpoint adds no oracle work to the sequential link traversal. -/
theorem isOnlineQueryBound_solve {q : ℕ} (puzzle : Quantum.MaskedChain.Puzzle G q) :
    IsOnlineQueryBound (solve puzzle) (q + 1, q + 1) := by
  simpa only [solve, IsOnlineQueryBound, isQueryBound_map_iff] using
    isOnlineQueryBound_solveFrom (q + 1) puzzle.2 puzzle.1

section Experiment

variable [Fintype G]

omit [AddCommGroup G] [Fintype G] in
private theorem simulateQ_liftProb {α : Type} (H : G → G) (oa : ProbComp α) :
    simulateQ (unifFwdAnswerImpl (QueryImpl.ofFn H)).batch'
      (liftM oa : RoundComp G α) = oa := by
  rw [QueryImpl.simulateQ_liftM_eq_of_query
    (unifFwdAnswerImpl (QueryImpl.ofFn H)).batch' (QueryImpl.id' unifSpec)
    (fun _ ↦ rfl), simulateQ_id']

/-- Weighted generation observations are uniform averages of the actual oracle-derived
challenge, endpoint and complete hidden tuple. -/
theorem tsum_gen_mul (q : ℕ) (H : G → G)
    (f : (Quantum.MaskedChain.Puzzle G q × G × (Fin (q + 2) → G)) → ℝ≥0∞) :
    (∑' z,
      Pr{let a ← simulateQ (unifFwdAnswerImpl (QueryImpl.ofFn H)).batch' (gen q)}[a = z] * f z) =
      ∑ vertices : Fin (q + 2) → G, (Fintype.card (Fin (q + 2) → G) : ℝ≥0∞)⁻¹ *
        f (Quantum.MaskedChain.publicPuzzle H vertices,
          vertices (Fin.last (q + 1)), vertices) := by
  let _ := SampleableType.ofFintype (Fin (q + 2) → G)
  rw [gen, simulateQ_bind, simulateQ_liftProb]
  simp_rw [simulateQ_genWith]
  rw [tsum_prEvent_bind_mul]
  simp_rw [tsum_prEvent_pure_mul, SampleableType.prEvent_uniformSample_eq_singleton]
  exact tsum_fintype _

variable [DecidableEq G]

/-- Use a no-preprocessing online family in the two-phase experiment, with its initial
quantum register and substate unchanged. -/
@[expose, reducible]
noncomputable def adversary {q : ℕ}
    (adv : Quantum.MaskedChain.OnlineAdversary LocalSig.instruments G q) :
    Quantum.TimeLockPuzzle.Adversary (qromBatchSpec G G) (Quantum.MaskedChain.Puzzle G q) G :=
  Quantum.TimeLockPuzzle.TwoPhaseAdversary.withoutPreprocessing
    adv.initialReg adv.initialState adv.run

/-- The embedded quantum generator preserves the one-round and `q + 1`-point budgets. -/
theorem scheme_gen_queryBound (q : ℕ) :
    (scheme (G := G) q).gen.IsTotalQueryBound 1 ∧
      (scheme (G := G) q).gen.IsPointBound (q + 1) :=
  ⟨(isOnlineQueryBound_gen q).isTotalQueryBound_toQuantumBatch,
    (isOnlineQueryBound_gen q).isPointBound_toQuantumBatch⟩

/-- The embedded quantum solver preserves the sequential `q + 1`-round and point budgets. -/
theorem scheme_solve_queryBound {q : ℕ} (puzzle : Quantum.MaskedChain.Puzzle G q) :
    ((scheme q).solve puzzle).IsTotalQueryBound (q + 1) ∧
      ((scheme q).solve puzzle).IsPointBound (q + 1) :=
  ⟨(isOnlineQueryBound_solve puzzle).isTotalQueryBound_toQuantumBatch,
    (isOnlineQueryBound_solve puzzle).isPointBound_toQuantumBatch⟩

/-- The honest quantum solver returns the generated endpoint with certainty for every fixed
function and hidden tuple, for any chosen measurable structure on its classical output. -/
theorem evalDist_scheme_solve_publicPuzzle [MeasurableSpace (Option G)] {q : ℕ}
    (H : G → G) (vertices : Fin (q + 2) → G) :
    (parallelOracleRuntime H).evalDist₂ .instruments
        ((scheme q).solve (Quantum.MaskedChain.publicPuzzle H vertices)) (SubState.basis ()) =
      Measure.dirac (some (vertices (Fin.last (q + 1)))) := by
  change (parallelOracleRuntime H).evalDist₂ .instruments
    (solve (Quantum.MaskedChain.publicPuzzle H vertices)).toQuantumBatch (SubState.basis ()) = _
  rw [evalDist_parallelOracleRuntime_toQuantumBatch, simulateQ_solve_publicPuzzle, evalDist_pure]

omit [AddCommGroup G] in
/-- The no-preprocessing adapter meets the two-phase budget obtained from its online rounds
and width. All preprocessing points are zero. -/
theorem adversary_isQueryBound {q k : ℕ}
    (adv : Quantum.MaskedChain.OnlineAdversary LocalSig.instruments G q)
    (hbound : adv.IsQueryBound q k) :
    (adversary adv).IsQueryBound ⟨0, q, k * q, k⟩ := by
  constructor
  · simp [adversary, Quantum.TimeLockPuzzle.TwoPhaseAdversary.withoutPreprocessing]
  · intro M state puzzle
    rcases state with ⟨h⟩
    subst M
    exact ⟨(hbound puzzle).1, (hbound puzzle).1.isPointBound (hbound puzzle).2,
      (hbound puzzle).2⟩

private theorem evalDistMap_endpoint_decide (H : G → G) {A : QReg}
    (x : QuantumComp LocalSig.instruments (qromBatchSpec G G) (fun _ ↦ G) A)
    (ρ : SubState A) (key : G) :
    (parallelOracleRuntime H).evalDistMap .instruments x ρ
        (fun out ↦ decide (out.2 = key)) {true} =
      (parallelOracleRuntime H).evalDistMap .instruments x ρ
        (fun out ↦ out.2 = key) {True} := by
  classical
  rw [(parallelOracleRuntime H).evalDistMap_apply .instruments x ρ _
      (MeasurableSet.singleton true),
    (parallelOracleRuntime H).evalDistMap_apply .instruments x ρ _
      (MeasurableSet.singleton True)]
  apply tsum_congr
  intro out
  by_cases h : out.2 = key <;> simp [h]

/-- The honest puzzle's quantum no-preprocessing experiment is exactly the endpoint game.
The same function supplies generation and online calls, and the complete tuple stays jointly
sampled with the public masks and endpoint check. No resource bound is needed for this equality. -/
theorem qromDelayAdvantage_eq_recoveryAdvantage {q : ℕ}
    (adv : Quantum.MaskedChain.OnlineAdversary LocalSig.instruments G q) :
    Quantum.TimeLockPuzzle.qromDelayAdvantage (scheme q) (adversary adv) =
      Quantum.MaskedChain.recoveryAdvantage .instruments adv := by
  rw [Quantum.TimeLockPuzzle.qromDelayAdvantage,
    Quantum.TimeLockPuzzle.sampledDelayAdvantage_eq_sum,
    Quantum.MaskedChain.recoveryAdvantage_eq_sum]
  apply Finset.sum_congr rfl
  intro H _
  congr 1
  change Quantum.TimeLockPuzzle.delayAdvantage (parallelOracleRuntime H)
    (Quantum.TimeLockPuzzle.ofClassicalGenerator (gen q) (fun p ↦ (solve p).toQuantumBatch))
    (Quantum.TimeLockPuzzle.TwoPhaseAdversary.withoutPreprocessing
      adv.initialReg adv.initialState adv.run) = _
  rw [Quantum.TimeLockPuzzle.delayAdvantage_withoutPreprocessing_ofClassicalGenerator,
    tsum_gen_mul]
  apply Finset.sum_congr rfl
  intro vertices _
  congr 1
  exact evalDistMap_endpoint_decide H _ adv.initialState _

/-- Quantum delay for the named idealized puzzle against an online family without
preprocessing. Honest generation is outside the online clock, and missing mass counts as
failure. This does not assert security for adversaries with oracle preprocessing. -/
theorem qromDelayAdvantage_le {q k : ℕ}
    (adv : Quantum.MaskedChain.OnlineAdversary LocalSig.instruments G q)
    (hbound : adv.IsQueryBound q k) :
    Quantum.TimeLockPuzzle.qromDelayAdvantage (scheme q) (adversary adv) ≤
      min 1 (Quantum.MaskedChain.recoveryBound G q k) := by
  rw [qromDelayAdvantage_eq_recoveryAdvantage]
  exact Quantum.MaskedChain.recoveryAdvantage_le .instruments adv hbound

end Experiment

end MaskedChainPuzzle
