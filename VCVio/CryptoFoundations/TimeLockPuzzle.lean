/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.OracleComp.QueryTracking.QueryBound.Batch

/-!
# Time-lock puzzles in the random oracle model

A time-lock puzzle (Rivest, Shamir and Wagner; in the random oracle model, Mahmoody, Moran and
Vadhan, CRYPTO 2011) is a pair of algorithms over oracles `spec`, both submitting rounds of
parallel queries (`OracleSpec.batch`): a generator `gen` that outputs a puzzle with its key, and a
solver `solve` that recovers the key from the puzzle, or reports a malformed puzzle with `none`.
Time is counted in oracle rounds, measured by the online budget `OracleComp.IsOnlineQueryBound`.

Security is a two-phase delay experiment against one lazily sampled random oracle. The
preprocessing phase of the adversary queries the oracle one point at a time before the puzzle
exists and hands its state to the online phase, which receives the puzzle, submits rounds of
parallel queries, and wins if it outputs the key. All three of preprocessing, generation and the
online phase run on one cache, so an answer obtained in one phase is the answer in every later
phase.

## Main definitions

* `TimeLockPuzzle spec Puzzle Key`: the generator and the solver.
* `TimeLockPuzzle.correctnessExperiment`, `TimeLockPuzzle.Correct`: the solver returns the
  generated key with probability one in the random oracle model.
* `TimeLockPuzzle.IsGenQueryBound`, `TimeLockPuzzle.IsSolveQueryBound`: honest round and point
  budgets.
* `TimeLockPuzzle.TwoPhaseAdversary`, `TimeLockPuzzle.TwoPhaseAdversary.IsQueryBound`: a
  two-phase adversary whose online phase also queries oracles `free` at no cost, and its
  preprocessing and online budgets.
* `TimeLockPuzzle.Adversary`: the delay adversary, the two-phase adversary whose free oracles are
  local coins and whose output is a key.
* `TimeLockPuzzle.TwoPhaseAdversary.mapOutput`: the adversary with its output mapped by a
  function, within the same budgets (`TimeLockPuzzle.TwoPhaseAdversary.isQueryBound_mapOutput`).
* `TimeLockPuzzle.delayExperiment`, `TimeLockPuzzle.delayAdvantage`,
  `TimeLockPuzzle.DelaySecure`: the delay experiment, its success probability, and the security
  statement for bounded adversaries.
* `TimeLockPuzzle.guessExperiment`: the delay experiment for an online phase with outputs of any
  type, returning the output together with the key.

## Main statements

* `TimeLockPuzzle.delayAdvantage_eq`: the delay advantage is the probability that the delay
  experiment returns `true` in the random oracle model.
* `TimeLockPuzzle.delayExperiment_eq_map_guessExperiment`,
  `TimeLockPuzzle.delayAdvantage_eq_prEvent_guessExperiment`: the delay experiment decides whether
  the output of `guessExperiment` is the key, so the delay advantage is the probability of that
  event.
* `TimeLockPuzzle.guessExperiment_mapOutput`: mapping the output of the adversary maps the output
  of `guessExperiment`.
-/

public section

open OracleSpec OracleComp ENNReal

/-- A time-lock puzzle with puzzles `Puzzle` and keys `Key` over the oracles `spec`. Both
algorithms sample local coins from `unifSpec` and submit rounds of parallel queries to `spec`. -/
structure TimeLockPuzzle {ι : Type} (spec : OracleSpec.{0, 0} ι) (Puzzle Key : Type) where
  /-- The generator: a puzzle together with its key. -/
  gen : OracleComp (unifSpec + spec.batch) (Puzzle × Key)
  /-- The solver: the key of a puzzle, or `none` for a malformed puzzle. -/
  solve : Puzzle → OracleComp (unifSpec + spec.batch) (Option Key)

namespace TimeLockPuzzle

variable {ι : Type} {spec : OracleSpec.{0, 0} ι} {Puzzle Key : Type}

/-! ## Correctness -/

/-- Generate a puzzle, solve it, and return whether the solver returned the generated key. Rounds
are rewritten as single queries (`OracleSpec.unbatch`), so that one oracle answers the generator
and the solver. -/
@[expose]
def correctnessExperiment [DecidableEq Key] (tlp : TimeLockPuzzle spec Puzzle Key) :
    OracleComp (unifSpec + spec) Bool :=
  simulateQ spec.unbatch do
    let (puzzle, key) ← tlp.gen
    let key' ← tlp.solve puzzle
    return decide (key' = some key)

/-- Perfect correctness in the random oracle model: when the generator and the solver run against
one lazily sampled random oracle, the solver returns the generated key with probability one. -/
@[expose]
def Correct [DecidableEq ι] [∀ t, SampleableType (spec.Range t)] [DecidableEq Key]
    (tlp : TimeLockPuzzle spec Puzzle Key) : Prop :=
  (ProbCompRuntime.rom spec).evalDist tlp.correctnessExperiment {true} = 1

/-! ## Honest budgets -/

/-- The generator submits at most `b.1` rounds holding at most `b.2` points, on every path. -/
@[expose]
def IsGenQueryBound (tlp : TimeLockPuzzle spec Puzzle Key) (b : ℕ × ℕ) : Prop :=
  IsOnlineQueryBound tlp.gen b

/-- On every puzzle, the solver submits at most `b.1` rounds holding at most `b.2` points. -/
@[expose]
def IsSolveQueryBound (tlp : TimeLockPuzzle spec Puzzle Key) (b : ℕ × ℕ) : Prop :=
  ∀ puzzle, IsOnlineQueryBound (tlp.solve puzzle) b

/-! ## The delay experiment -/

/-- A two-phase adversary against a time-lock puzzle over the oracles `spec`, with outputs `Out`.
The preprocessing phase samples local coins and queries `spec` one point at a time before the
puzzle exists, and outputs a state of any type; the online phase receives that state and the
puzzle, submits rounds of parallel queries to `spec`, and outputs a value of `Out`. Beside its
rounds, the online phase queries the oracles `free`, which cost no round: local coins `unifSpec`
in the delay game, and local coins together with the challenger's encryption oracle in a hiding
game. -/
structure TwoPhaseAdversary {τ : Type} (free : OracleSpec.{0, 0} τ) (spec : OracleSpec.{0, 0} ι)
    (Puzzle Out : Type) where
  /-- The state passed from the preprocessing phase to the online phase. -/
  State : Type
  /-- The preprocessing phase, run before the puzzle is generated. -/
  preprocess : OracleComp (unifSpec + spec) State
  /-- The online phase, run on the preprocessing state and the puzzle. -/
  online : State → Puzzle → OracleComp (free + spec.batch) Out

/-- The adversary makes at most `Q` preprocessing queries to `spec`, and its online phase submits
at most `b.1` rounds holding at most `b.2` points on every state and puzzle. Local coins and the
oracles `free` cost nothing. -/
@[expose]
def TwoPhaseAdversary.IsQueryBound {τ : Type} {free : OracleSpec.{0, 0} τ} {Out : Type}
    (adv : TwoPhaseAdversary free spec Puzzle Out) (Q : ℕ) (b : ℕ × ℕ) : Prop :=
  IsPreprocessingQueryBound adv.preprocess Q ∧
    ∀ σ puzzle, IsOnlineQueryBound (adv.online σ puzzle) b

/-- The adversary whose online phase applies `f` to the output of `adv`, with the same state,
preprocessing phase and rounds. -/
@[expose]
def TwoPhaseAdversary.mapOutput {τ : Type} {free : OracleSpec.{0, 0} τ} {Out Out' : Type}
    (f : Out → Out') (adv : TwoPhaseAdversary free spec Puzzle Out) :
    TwoPhaseAdversary free spec Puzzle Out' where
  State := adv.State
  preprocess := adv.preprocess
  online σ puzzle := f <$> adv.online σ puzzle

/-- Mapping the output keeps the preprocessing and online budgets. -/
theorem TwoPhaseAdversary.isQueryBound_mapOutput {τ : Type} {free : OracleSpec.{0, 0} τ}
    {Out Out' : Type} (f : Out → Out') {adv : TwoPhaseAdversary free spec Puzzle Out} {Q : ℕ}
    {b : ℕ × ℕ} (h : adv.IsQueryBound Q b) : (adv.mapOutput f).IsQueryBound Q b :=
  ⟨h.1, fun σ puzzle => (isQueryBound_map_iff _ _ _ _ _).2 (h.2 σ puzzle)⟩

/-- An adversary in the delay experiment: a two-phase adversary whose online phase queries only
local coins beside its rounds, and outputs a key. -/
abbrev Adversary (spec : OracleSpec.{0, 0} ι) (Puzzle Key : Type) : Type 1 :=
  TwoPhaseAdversary unifSpec spec Puzzle Key

/-- The delay experiment: run the preprocessing phase, generate a puzzle with its key, run the
online phase on the state and the puzzle, and return whether its output is the key. Rounds are
rewritten as single queries (`OracleSpec.unbatch`), so that one oracle, and in the random oracle
model one cache, serves the three phases. -/
@[expose]
def delayExperiment [DecidableEq Key] (tlp : TimeLockPuzzle spec Puzzle Key)
    (adv : Adversary spec Puzzle Key) : OracleComp (unifSpec + spec) Bool := do
  let σ ← adv.preprocess
  let (puzzle, key) ← simulateQ spec.unbatch tlp.gen
  let key' ← simulateQ spec.unbatch (adv.online σ puzzle)
  return decide (key' = key)

/-- The delay experiment for an online phase with outputs of any type `Out`: run the
preprocessing phase, generate a puzzle with its key, run the online phase on the state and the
puzzle, and return its output together with the key. Rounds are rewritten as single queries
(`OracleSpec.unbatch`), as in `delayExperiment`, which decides whether the two agree
(`delayExperiment_eq_map_guessExperiment`). -/
@[expose]
def guessExperiment {Out : Type} (tlp : TimeLockPuzzle spec Puzzle Key)
    (adv : TwoPhaseAdversary unifSpec spec Puzzle Out) :
    OracleComp (unifSpec + spec) (Out × Key) := do
  let σ ← adv.preprocess
  let (puzzle, key) ← simulateQ spec.unbatch tlp.gen
  let out ← simulateQ spec.unbatch (adv.online σ puzzle)
  return (out, key)

/-- The delay experiment decides whether the output of the online phase in `guessExperiment` is
the key. -/
theorem delayExperiment_eq_map_guessExperiment [DecidableEq Key]
    (tlp : TimeLockPuzzle spec Puzzle Key) (adv : Adversary spec Puzzle Key) :
    tlp.delayExperiment adv = (fun z => decide (z.1 = z.2)) <$> tlp.guessExperiment adv := by
  simp [delayExperiment, guessExperiment]

/-- Mapping the output of the adversary maps the output of `guessExperiment` and keeps the key. -/
theorem guessExperiment_mapOutput {Out Out' : Type} (tlp : TimeLockPuzzle spec Puzzle Key)
    (f : Out → Out') (adv : TwoPhaseAdversary unifSpec spec Puzzle Out) :
    tlp.guessExperiment (adv.mapOutput f) =
      (fun z => (f z.1, z.2)) <$> tlp.guessExperiment adv := by
  simp [guessExperiment, TwoPhaseAdversary.mapOutput]

/-- The success probability of `adv` in the delay experiment against one lazily sampled random
oracle, starting from the empty cache. -/
noncomputable def delayAdvantage [DecidableEq ι] [∀ t, SampleableType (spec.Range t)]
    [DecidableEq Key] (tlp : TimeLockPuzzle spec Puzzle Key) (adv : Adversary spec Puzzle Key) :
    ℝ≥0∞ :=
  (ProbCompRuntime.rom spec).evalDist (tlp.delayExperiment adv) {true}

/-- The delay advantage is the probability that the delay experiment returns `true` against one
lazily sampled random oracle. -/
theorem delayAdvantage_eq [DecidableEq ι] [∀ t, SampleableType (spec.Range t)]
    [DecidableEq Key] (tlp : TimeLockPuzzle spec Puzzle Key) (adv : Adversary spec Puzzle Key) :
    delayAdvantage tlp adv =
      (ProbCompRuntime.rom spec).evalDist (tlp.delayExperiment adv) {true} := by
  unfold delayAdvantage; rfl

/-- The delay advantage is the probability, in the lazy random oracle model from the empty cache,
that the online phase in `guessExperiment` outputs the key. -/
theorem delayAdvantage_eq_prEvent_guessExperiment [DecidableEq ι]
    [∀ t, SampleableType (spec.Range t)] [DecidableEq Key] (tlp : TimeLockPuzzle spec Puzzle Key)
    (adv : Adversary spec Puzzle Key) :
    delayAdvantage tlp adv =
      Pr{let z ← (simulateQ spec.romImpl (tlp.guessExperiment adv)).run' ∅}[z.1 = z.2] := by
  rw [delayAdvantage_eq, ProbCompRuntime.rom_evalDist, delayExperiment_eq_map_guessExperiment,
    simulateQ_map, prEvent_eq_evalDist_decide]
  congr 2
  simp [StateT.run'_eq, map_eq_bind_pure_comp]

/-- Delay security: every adversary with at most `Q` preprocessing queries and an online budget
of `b.1` rounds and `b.2` points wins the delay experiment with probability at most `ε`. For a
puzzle whose honest solver derives the key in round `T`, the meaningful budgets are
`b = (T - 1, q)`. -/
@[expose]
def DelaySecure [DecidableEq ι] [∀ t, SampleableType (spec.Range t)] [DecidableEq Key]
    (tlp : TimeLockPuzzle spec Puzzle Key) (Q : ℕ) (b : ℕ × ℕ) (ε : ℝ≥0∞) : Prop :=
  ∀ adv : Adversary spec Puzzle Key, adv.IsQueryBound Q b → delayAdvantage tlp adv ≤ ε

end TimeLockPuzzle
