/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.TimeLockPuzzle
public import VCVio.OracleComp.QueryTracking.QueryBound.Truncate

/-!
# Delay security within a round bound

The delay theorem of a time-lock puzzle bounds the probability of the per-run event "the online
phase outputs the key within `r` completed rounds", for every adversary within a point budget and
with no bound on its rounds. This file reduces that event to delay security at the round budget
`r`: the adversary truncated at `r` rounds (`TwoPhaseAdversary.truncate`) keeps the preprocessing
phase and its budget, runs the online phase until it would submit round `r + 1` and outputs a
fallback key there, and wins the delay experiment at least as often as the original adversary
achieves the per-run event. The comparison runs on the random-oracle cache shared by the three
phases. The truncation and its budgets hold for every two-phase adversary, whatever its free
oracles and outputs.

## Main definitions

* `TimeLockPuzzle.TwoPhaseAdversary.truncate`: the two-phase adversary whose online phase is
  truncated at `r` rounds.
* `TimeLockPuzzle.delayExperimentWithin`, `TimeLockPuzzle.delayAdvantageWithin`: the delay
  experiment won only by a key output within `r` completed rounds, and its success probability.

## Main statements

* `TimeLockPuzzle.TwoPhaseAdversary.isQueryBound_truncate`: the truncation of an adversary within
  a preprocessing budget `Q` and a point budget `q` is within `Q` and the online budget `(r, q)`.
* `TimeLockPuzzle.TwoPhaseAdversary.truncate_eq_self`: an adversary within `r` online rounds is its
  own truncation.
* `TimeLockPuzzle.delayAdvantageWithin_le_delayAdvantage_truncate`: the probability of the
  per-run event is at most the delay advantage of the truncated adversary.
* `TimeLockPuzzle.delayAdvantageWithin_le_delayAdvantage`,
  `TimeLockPuzzle.delayAdvantageWithin_eq_delayAdvantage`: the per-run event is at most the delay
  advantage, with equality for an adversary within `r` online rounds.
* `TimeLockPuzzle.delayAdvantageWithin_le_of_delaySecure`: delay security at `(r, q)` bounds the
  per-run event for every adversary within the point budget `q`.
-/

public section

open OracleSpec OracleComp ENNReal

namespace TimeLockPuzzle

variable {ι : Type} {spec : OracleSpec.{0, 0} ι} {Puzzle Key : Type}

/-! ## The truncated adversary -/

section TwoPhaseAdversary

variable {τ : Type} {free : OracleSpec.{0, 0} τ} {Out : Type}

/-- The adversary with the preprocessing phase and state of `adv`, whose online phase runs that of
`adv` until it would submit round `r + 1` and outputs `k₀` there (`OracleComp.truncate`). -/
@[expose]
def TwoPhaseAdversary.truncate (adv : TwoPhaseAdversary free spec Puzzle Out) (r : ℕ) (k₀ : Out) :
    TwoPhaseAdversary free spec Puzzle Out where
  State := adv.State
  preprocess := adv.preprocess
  online σ puzzle := OracleComp.truncate r k₀ (adv.online σ puzzle)

/-- The truncation at `r` rounds of an adversary with at most `Q` preprocessing queries whose
online phase holds at most `q` points on every path makes at most `Q` preprocessing queries and
submits at most `r` rounds holding at most `q` points. -/
theorem TwoPhaseAdversary.isQueryBound_truncate {adv : TwoPhaseAdversary free spec Puzzle Out}
    {Q q : ℕ} (hpre : IsPreprocessingQueryBound adv.preprocess Q)
    (honline : ∀ σ puzzle, IsPointQueryBound (adv.online σ puzzle) q) (r : ℕ) (k₀ : Out) :
    (adv.truncate r k₀).IsQueryBound Q (r, q) :=
  ⟨hpre, fun σ puzzle => (honline σ puzzle).isOnlineQueryBound_truncate⟩

/-- An adversary within `r` online rounds is its own truncation at `r` rounds. -/
theorem TwoPhaseAdversary.truncate_eq_self {adv : TwoPhaseAdversary free spec Puzzle Out}
    {Q r q : ℕ} (h : adv.IsQueryBound Q (r, q)) (k₀ : Out) : adv.truncate r k₀ = adv := by
  obtain ⟨State, preprocess, online⟩ := adv
  simp only [TwoPhaseAdversary.truncate, TwoPhaseAdversary.mk.injEq, heq_eq_eq, true_and]
  funext σ puzzle
  exact truncate_eq_self_of_isOnlineQueryBound (h.2 σ puzzle)

end TwoPhaseAdversary

/-! ## The delay experiment within a round bound -/

/-- The delay experiment won only within `r` rounds: run the preprocessing phase, generate a
puzzle with its key, run the online phase on the state and the puzzle while counting the rounds
it submits (`OracleComp.runCountingRounds`, before the rounds are rewritten as single queries),
and return whether its output is the key and it completed at most `r` rounds. As in
`delayExperiment`, one oracle serves the three phases. -/
@[expose]
def delayExperimentWithin [DecidableEq Key] (tlp : TimeLockPuzzle spec Puzzle Key)
    (adv : Adversary spec Puzzle Key) (r : ℕ) : OracleComp (unifSpec + spec) Bool := do
  let σ ← adv.preprocess
  let (puzzle, key) ← simulateQ spec.unbatch tlp.gen
  let (key', n) ← runCountingRounds spec.unbatch (adv.online σ puzzle)
  return decide (key' = key ∧ n ≤ r)

/-- The probability of the paper's event "A_1 outputs K within `r` completed rounds": the success
probability of `adv` in `delayExperimentWithin` against one lazily sampled random oracle, starting
from the empty cache. -/
noncomputable def delayAdvantageWithin [DecidableEq ι] [∀ t, SampleableType (spec.Range t)]
    [DecidableEq Key] (tlp : TimeLockPuzzle spec Puzzle Key) (adv : Adversary spec Puzzle Key)
    (r : ℕ) : ℝ≥0∞ :=
  (ProbCompRuntime.rom spec).evalDist (tlp.delayExperimentWithin adv r) {true}

section rom

variable [DecidableEq ι] [∀ t, SampleableType (spec.Range t)] [DecidableEq Key]

/-- The probability that `adv` outputs the key within `r` completed rounds is the probability that
`delayExperimentWithin` returns `true` against one lazily sampled random oracle. -/
theorem delayAdvantageWithin_eq (tlp : TimeLockPuzzle spec Puzzle Key)
    (adv : Adversary spec Puzzle Key) (r : ℕ) :
    delayAdvantageWithin tlp adv r =
      (ProbCompRuntime.rom spec).evalDist (tlp.delayExperimentWithin adv r) {true} := by
  unfold delayAdvantageWithin; rfl

/-- The per-run event of `adv` is at most the delay advantage of an adversary with the same
preprocessing phase whose online phase `online'` wins at least as often, on every state, puzzle,
key and random-oracle cache, as the online phase of `adv` outputs the key within `r` rounds. -/
private theorem delayAdvantageWithin_le_of_online (tlp : TimeLockPuzzle spec Puzzle Key)
    (adv : Adversary spec Puzzle Key) (r : ℕ)
    (online' : adv.State → Puzzle → OracleComp (unifSpec + spec.batch) Key)
    (h : ∀ σ puzzle key s,
      Pr{let z ← (runCountingRounds spec.romImpl.batch'
          (adv.online σ puzzle)).run s}[z.1.1 = key ∧ z.1.2 ≤ r] ≤
        Pr{let z ← (simulateQ spec.romImpl.batch' (online' σ puzzle)).run s}[z.1 = key]) :
    delayAdvantageWithin tlp adv r ≤
      delayAdvantage tlp ⟨adv.State, adv.preprocess, online'⟩ := by
  rw [delayAdvantageWithin, delayAdvantage_eq, ProbCompRuntime.rom_evalDist,
    ProbCompRuntime.rom_evalDist, ← prEvent_eq_evalDist_singleton,
    ← prEvent_eq_evalDist_singleton, StateT.run'_eq, StateT.run'_eq, prEvent_map, prEvent_map]
  simp only [delayExperimentWithin, delayExperiment, simulateQ_bind, StateT.run_bind]
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun z => ?_
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun w => ?_
  obtain ⟨⟨puzzle, key⟩, s⟩ := w
  simpa only [simulateQ_runCountingRounds_unbatch, QueryImpl.simulateQ_simulateQ_unbatch,
    simulateQ_pure, StateT.run_pure, bind_pure_comp, prEvent_map, decide_eq_true_eq]
    using h z.1 puzzle key s

/-- The probability that `adv` outputs the key within `r` completed rounds is at most the delay
advantage of its truncation at `r` rounds, for every fallback key `k₀`. The two experiments are
compared on the random-oracle cache left by the preprocessing phase and the generator. -/
theorem delayAdvantageWithin_le_delayAdvantage_truncate (tlp : TimeLockPuzzle spec Puzzle Key)
    (adv : Adversary spec Puzzle Key) (r : ℕ) (k₀ : Key) :
    delayAdvantageWithin tlp adv r ≤ delayAdvantage tlp (adv.truncate r k₀) :=
  delayAdvantageWithin_le_of_online tlp adv r _ fun _ _ key s =>
    (prEvent_congr _ _ _ fun _ => and_comm).trans_le
      (prEvent_run_runCountingRounds_le_truncate _ _ (fun x _ => x = key) s)

/-- The probability that `adv` outputs the key within `r` completed rounds is at most its delay
advantage. -/
theorem delayAdvantageWithin_le_delayAdvantage (tlp : TimeLockPuzzle spec Puzzle Key)
    (adv : Adversary spec Puzzle Key) (r : ℕ) :
    delayAdvantageWithin tlp adv r ≤ delayAdvantage tlp adv :=
  delayAdvantageWithin_le_of_online tlp adv r adv.online fun σ puzzle _ s => by
    rw [← fst_map_runCountingRounds, StateT.run_map, prEvent_map]
    exact prEvent_and_le_left _ _ _

/-- For an adversary within `r` online rounds, the probability that it outputs the key within `r`
completed rounds is its delay advantage. -/
theorem delayAdvantageWithin_eq_delayAdvantage (tlp : TimeLockPuzzle spec Puzzle Key)
    {adv : Adversary spec Puzzle Key} {Q r q : ℕ} (h : adv.IsQueryBound Q (r, q)) :
    delayAdvantageWithin tlp adv r = delayAdvantage tlp adv := by
  refine le_antisymm (delayAdvantageWithin_le_delayAdvantage tlp adv r) ?_
  rw [delayAdvantageWithin, delayAdvantage_eq, ProbCompRuntime.rom_evalDist,
    ProbCompRuntime.rom_evalDist, ← prEvent_eq_evalDist_singleton,
    ← prEvent_eq_evalDist_singleton, StateT.run'_eq, StateT.run'_eq, prEvent_map, prEvent_map]
  simp only [delayExperimentWithin, delayExperiment, simulateQ_bind, StateT.run_bind]
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun z => ?_
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun w => ?_
  obtain ⟨⟨puzzle, key⟩, s⟩ := w
  simp only [simulateQ_runCountingRounds_unbatch, QueryImpl.simulateQ_simulateQ_unbatch,
    simulateQ_pure, StateT.run_pure, bind_pure_comp, prEvent_map, decide_eq_true_eq]
  rw [← fst_map_runCountingRounds, StateT.run_map, prEvent_map]
  exact (prEvent_run_runCountingRounds_le_of_isOnlineQueryBound _ (h.2 z.1 puzzle)
    (fun x _ => x = key) s).trans_eq (prEvent_congr _ _ _ fun _ => and_comm)

/-- Delay security at the budget `(r, q)` bounds by `ε` the probability that an adversary outputs
the key within `r` completed rounds, for every adversary with at most `Q` preprocessing queries
whose online phase holds at most `q` points on every path, with no bound on its rounds. -/
theorem delayAdvantageWithin_le_of_delaySecure [Inhabited Key]
    {tlp : TimeLockPuzzle spec Puzzle Key} {Q r q : ℕ} {ε : ℝ≥0∞}
    (hsec : DelaySecure tlp Q (r, q) ε) {adv : Adversary spec Puzzle Key}
    (hpre : IsPreprocessingQueryBound adv.preprocess Q)
    (honline : ∀ σ puzzle, IsPointQueryBound (adv.online σ puzzle) q) :
    delayAdvantageWithin tlp adv r ≤ ε :=
  (delayAdvantageWithin_le_delayAdvantage_truncate tlp adv r default).trans
    (hsec _ (TwoPhaseAdversary.isQueryBound_truncate hpre honline r default))

end rom

end TimeLockPuzzle
