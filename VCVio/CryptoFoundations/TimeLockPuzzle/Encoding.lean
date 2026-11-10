/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.TimeLockPuzzle
public import VCVio.OracleComp.QueryTracking.RandomOracle.Encoded.Batch
import VCVio.OracleComp.SimSemantics.StateT.Measure

/-!
# Time-lock puzzles over a random-oracle encoding

A time-lock puzzle written against typed random oracles `spec` can be run against one raw random
oracle `D →ₒ M` through a `RandomOracleEncoding`: each typed round is sent as the raw round of the
encodings of its points, and every answer is truncated (`RandomOracleEncoding.roundImpl`). This
file transfers delay security from the typed puzzle to the raw one. Every raw adversary is
adapted to a typed adversary within the same budgets that wins the typed delay experiment at least
as often as the raw adversary wins the raw one, provided the encoding never clashes.

The adapted adversary `adaptAdversary` runs the raw adversary against the typed oracles through
the routing handlers of `VCVio/OracleComp/QueryTracking/RandomOracle/Encoded/Batch.lean`: a raw
input that encodes a typed point is answered through the typed oracle, and every other raw input by
a private lazy random oracle whose cache passes from the preprocessing phase to the online phase.
The adapter needs no knowledge of the puzzle, and it spends no more queries or rounds than the raw
adversary (`isQueryBound_adaptAdversary`), so the typed delay bound applies to it as stated.

The comparison runs through `combinedExperiment`, the delay experiment on the combined interface
`unifSpec + (spec + (D →ₒ M))`, where the adversary queries raw inputs and the generator queries
typed points. Encoded into the raw oracle, it is the raw delay experiment
(`simulateQ_encodeImpl_combinedExperiment`); in the typed world it is the typed delay experiment
of the adapted adversary (`typedImpl_combinedExperiment_evalDistEq`); and the two worlds differ
only on a clash of the encoding
(`RandomOracleEncoding.prEvent_simulateQ_romImpl_encodeImpl_run_le`).

## Main definitions

* `OracleComp.RandomOracleEncoding.adaptAdversary`: the typed adversary of a raw adversary.
* `OracleComp.RandomOracleEncoding.combinedExperiment`: the delay experiment of a typed puzzle
  against a raw adversary, on the combined interface.

## Main statements

* `OracleComp.RandomOracleEncoding.isQueryBound_adaptAdversary`: the adapter preserves the
  preprocessing budget and the online budget of rounds and points.
* `OracleComp.RandomOracleEncoding.delayAdvantage_le_delayAdvantage_adaptAdversary`: for an
  encoding without clashes and a raw puzzle whose generator is the typed generator with encoded
  rounds, the raw delay advantage of a raw adversary is at most the typed delay advantage of its
  adapted adversary.
-/

public section

open OracleSpec OracleComp

namespace OracleComp.RandomOracleEncoding

open TimeLockPuzzle

variable {ι D M : Type} {spec : OracleSpec.{0, 0} ι} [SampleableType M]
  [∀ t, SampleableType (spec.Range t)] (E : RandomOracleEncoding spec D M)

section adapter

variable [DecidableEq D]

/-! ## The adapter -/

/-- The typed adversary of a raw adversary: both phases run the raw adversary, answering raw
inputs at encodings through the typed oracles and other raw inputs from a private lazy random
oracle, whose cache passes from the preprocessing phase to the online phase. -/
@[expose]
def adaptAdversary {Puzzle Key : Type} (adv : Adversary (D →ₒ M) Puzzle Key) :
    Adversary spec Puzzle Key where
  State := adv.State × (D →ₒ M).QueryCache
  preprocess := (simulateQ E.preprocessImpl adv.preprocess).run ∅
  online σ puzzle := (simulateQ E.onlineImpl (adv.online σ.1 puzzle)).run' σ.2

/-- **The adapter preserves the budgets.** If a raw adversary makes at most `Q` preprocessing
queries and its online phase submits at most `b.1` rounds holding at most `b.2` points, so does
its typed adversary: each raw query or round becomes at most one typed query or round with at
most as many points, and raw inputs that encode no typed point cost nothing. -/
theorem isQueryBound_adaptAdversary {Puzzle Key : Type} {adv : Adversary (D →ₒ M) Puzzle Key}
    {Q : ℕ} {b : ℕ × ℕ} (h : adv.IsQueryBound Q b) : (E.adaptAdversary adv).IsQueryBound Q b := by
  refine ⟨h.1.simulateQ_run_StateT_of_step (E.isQueryBoundP_preprocessImpl) ∅, fun σ puzzle => ?_⟩
  have hrun : IsOnlineQueryBound ((simulateQ E.onlineImpl (adv.online σ.1 puzzle)).run σ.2) b :=
    IsQueryBound.simulateQ_run_of_step (combine := (· + ·)) (mapBudget := id)
      (stepBudget := fun t _ => onlineStep t) (h.2 σ.1 puzzle) isOnlineQueryBound_bind
      (fun t _ s _ => E.isOnlineQueryBound_onlineImpl t s)
      (fun t b hb => by
        rcases t with k | xs
        · simp
        · simp only [onlineCanQuery_inr] at hb
          refine Prod.ext ?_ ?_ <;> simp <;> omega) σ.2
  exact (isQueryBound_map_iff _ _ _ _ _).2 hrun

end adapter

/-! ## Comparing the delay experiments -/

/-- The delay experiment of a typed puzzle against a raw adversary, on the combined interface:
the adversary queries raw inputs and the generator queries typed points. Its encoding is the raw
delay experiment of the encoded puzzle, and in the typed world it is the typed delay experiment
of the adapted adversary. -/
@[expose]
def combinedExperiment {Puzzle Key : Type} [DecidableEq Key] (tlp : TimeLockPuzzle spec Puzzle Key)
    (adv : Adversary (D →ₒ M) Puzzle Key) : OracleComp (unifSpec + (spec + (D →ₒ M))) Bool := do
  let σ ← simulateQ rawLift adv.preprocess
  let (puzzle, key) ← simulateQ typedLift (simulateQ spec.unbatch tlp.gen)
  let key' ← simulateQ rawLift (simulateQ (D →ₒ M).unbatch (adv.online σ puzzle))
  return decide (key' = key)

/-- The combined experiment encoded into the single raw oracle is the raw delay experiment of a raw
puzzle whose generator is the typed generator translated by `roundImpl`. -/
lemma simulateQ_encodeImpl_combinedExperiment {Puzzle Key : Type} [DecidableEq Key]
    {tlpRaw : TimeLockPuzzle (D →ₒ M) Puzzle Key} {tlp : TimeLockPuzzle spec Puzzle Key}
    (hgen : tlpRaw.gen = simulateQ E.roundImpl tlp.gen) (adv : Adversary (D →ₒ M) Puzzle Key) :
    simulateQ E.encodeImpl (combinedExperiment tlp adv) = tlpRaw.delayExperiment adv := by
  have hg : simulateQ E.encodeImpl (simulateQ typedLift (simulateQ spec.unbatch tlp.gen)) =
      simulateQ (D →ₒ M).unbatch tlpRaw.gen := by
    rw [← QueryImpl.simulateQ_compose, QueryImpl.simulateQ_simulateQ_unbatch,
      encodeImpl_compose_typedLift_batch', QueryImpl.simulateQ_compose, hgen]
  simp only [combinedExperiment, delayExperiment, simulateQ_bind, simulateQ_encodeImpl_rawLift, hg,
    simulateQ_pure]

section typedWorld

variable [DecidableEq ι] [DecidableEq D]

/-- In the typed world, the combined experiment wins with the probability of the typed delay
experiment against the adapted adversary. -/
lemma typedImpl_combinedExperiment_evalDistEq {Puzzle Key : Type} [DecidableEq Key]
    (tlp : TimeLockPuzzle spec Puzzle Key) (adv : Adversary (D →ₒ M) Puzzle Key) :
    Prod.fst <$> (simulateQ E.typedImpl (combinedExperiment tlp adv)).run (∅, ∅) =ᵈ
      (simulateQ spec.romImpl (tlp.delayExperiment (E.adaptAdversary adv))).run' ∅ := by
  have hpre := simulateQ_run_simulateQ_run_evalDistEq spec.romImpl E.preprocessImpl
    (E.typedImpl ∘ₛ rawLift) (fun t s q => by rw [E.preprocessImpl_run_step]) adv.preprocess ∅ ∅
  simp only [combinedExperiment, delayExperiment, adaptAdversary, simulateQ_bind, StateT.run_bind,
    StateT.run'_eq, map_bind]
  refine EvalDistEq.trans ?_ (hpre.bind_left _).symm
  rw [← QueryImpl.simulateQ_compose, bind_map_left]
  refine EvalDistEq.bind_right _ fun z => ?_
  obtain ⟨st, c, pv⟩ := z
  simp only [simulateQ_typedImpl_typedLift_run, bind_map_left, simulateQ_pure, StateT.run_pure,
    map_pure]
  refine EvalDistEq.bind_right _ fun w => ?_
  rw [← QueryImpl.simulateQ_compose, QueryImpl.simulateQ_simulateQ_unbatch, simulateQ_map,
    simulateQ_map, OracleSpec.simulateQ_romImpl_simulateQ_unbatch, StateT.run_map, bind_map_left]
  refine EvalDistEq.trans ?_ ((simulateQ_run_simulateQ_run_evalDistEq _ E.onlineImpl
    (E.typedImpl ∘ₛ rawLift).batch' E.onlineImpl_run_step (adv.online st w.1.1) pv w.2).bind_left
      _).symm
  rw [bind_map_left]

/-- **The raw delay experiment against the typed one.** If the generator of a raw puzzle is the
typed generator with every round translated by `roundImpl`, and the encoding never clashes, a raw
adversary wins the raw delay experiment with probability at most that of its adapted typed
adversary in the typed delay experiment. -/
theorem delayAdvantage_le_delayAdvantage_adaptAdversary {Puzzle Key : Type} [DecidableEq Key]
    {tlpRaw : TimeLockPuzzle (D →ₒ M) Puzzle Key} {tlp : TimeLockPuzzle spec Puzzle Key}
    (hgen : tlpRaw.gen = simulateQ E.roundImpl tlp.gen) (hclash : ∀ c, ¬ E.Clash c)
    (adv : Adversary (D →ₒ M) Puzzle Key) :
    delayAdvantage tlpRaw adv ≤ delayAdvantage tlp (E.adaptAdversary adv) := by
  rw [delayAdvantage_eq, delayAdvantage_eq, ProbCompRuntime.rom_evalDist,
    ProbCompRuntime.rom_evalDist, ← prEvent_eq_evalDist_singleton,
    ← prEvent_eq_evalDist_singleton,
    ← (E.typedImpl_combinedExperiment_evalDistEq tlp adv).prEvent_eq,
    ← E.simulateQ_encodeImpl_combinedExperiment hgen adv, StateT.run'_eq, prEvent_map, prEvent_map]
  refine (E.prEvent_simulateQ_romImpl_encodeImpl_run_le _ (· = true)).trans (le_of_eq ?_)
  simp [hclash]

end typedWorld

end OracleComp.RandomOracleEncoding
