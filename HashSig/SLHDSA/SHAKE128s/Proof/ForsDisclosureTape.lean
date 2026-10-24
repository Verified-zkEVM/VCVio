/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.ForsCoverage
public import HashSig.SLHDSA.SHAKE128s.Proof.ForsConcentrationExtended
public import HashSig.SLHDSA.SHAKE128s.Proof.ForsPrefixCapacity
public import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# Disclosures from an independent digest-view tape

The experiment samples a uniform finite tape of full parsed digest views. These lemmas connect
its actual disclosure sets to the occupancy and prefix-cap probability bounds: every disclosure
set is bounded by the load of its instance (`disclosures_card_le_loads`), and the law of the
loads of a uniform tape is exactly `ForsConcentration.uniformLoads` (`loads_probability`).
Coupling this experiment to an adaptive shared random oracle is a separate obligation.
-/

public section

open OracleComp OracleSpec MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace SlhDsaSecurity.ForsDisclosureTape

/-- The parsed FORS view of a message digest. -/
abbrev View := ForsCoverage.View
/-- The FORS instance selected by a message digest. -/
abbrev Instance := ForsCoverage.Instance
/-- The index of one of the fourteen FORS trees. -/
abbrev Tree := ForsCoverage.Tree
/-- A leaf index inside one FORS tree. -/
abbrev Leaf := ForsCoverage.Leaf
/-- A tape of one digest view per signing request. -/
abbrev Tape (requests : Nat) := Fin requests → View
/-- The instances selected by each request. -/
abbrev InstanceWord (requests : Nat) := Fin requests → Instance
/-- The leaves selected by each request in every tree. -/
abbrev LeafWord (requests : Nat) := Fin requests → Tree → Leaf

/-- The instance word of a tape. -/
@[expose] def instanceWord {requests : Nat} (tape : Tape requests) : InstanceWord requests :=
  fun j => (tape j).1

/-- The number of requests on a tape that select instance `i`. -/
@[expose] def loads {requests : Nat} (tape : Tape requests) (i : Instance) : Nat :=
  (Finset.univ.filter (fun j => (tape j).1 = i)).card

/-- The leaves a tape discloses in each tree of each instance. -/
@[expose] def disclosures {requests : Nat} (tape : Tape requests) : ForsCoverage.Disclosures :=
  fun i tree => (Finset.univ.filter (fun j => (tape j).1 = i)).image
    (fun j => (tape j).2 tree)

/-- An instance discloses at most as many leaves per tree as it has requests. -/
theorem disclosures_card_le_loads {requests : Nat} (tape : Tape requests)
    (i : Instance) (tree : Tree) : (disclosures tape i tree).card ≤ loads tape i :=
  Finset.card_image_le

/-- The loads of a tape are the word loads of its instance word. -/
theorem loads_eq_wordLoads {requests : Nat} (tape : Tape requests) :
    loads tape = ForsConcentration.wordLoads (instanceWord tape) := by
  funext i
  simp only [loads, ForsConcentration.wordLoads, ForsConcentration.wordCounts,
    Finsupp.finsetSum_apply, Finsupp.single_apply, Finset.card_eq_sum_ones,
    Finset.sum_filter, instanceWord]

/-- A tape splits into its instance word and its leaf word. -/
@[expose]
def splitTape (requests : Nat) : Tape requests ≃ InstanceWord requests × LeafWord requests where
  toFun tape := (instanceWord tape, fun j => (tape j).2)
  invFun pair j := (pair.1 j, pair.2 j)
  left_inv := by intro tape; rfl
  right_inv := by intro pair; rfl

/-- The instance word of a uniform tape is a uniform instance word. -/
theorem evalDist_instanceWord_uniform (requests : Nat) :
    (instanceWord <$> ($ᵗ Tape requests : ProbComp (Tape requests))) =ᵈ
      ($ᵗ InstanceWord requests : ProbComp (InstanceWord requests)) := by
  refine EvalDistEq.of_forall_prEvent_eq fun p => ?_
  rw [prEvent_map]
  calc Pr{let tape ← ($ᵗ Tape requests : ProbComp (Tape requests))}[p (instanceWord tape)]
      = Pr{let tape ← ($ᵗ Tape requests : ProbComp (Tape requests))}[
          p (splitTape requests tape).1] := rfl
    _ = Pr{let z ← ($ᵗ (InstanceWord requests × LeafWord requests) :
          ProbComp (InstanceWord requests × LeafWord requests))}[p z.1] :=
        SampleableType.prEvent_uniformSample_equiv (splitTape requests) (fun z => p z.1)
    _ = _ := SampleableType.prEvent_uniformSample_fst p

/-- VCVio's uniform sampler and the finite uniform probability measure agree on all events. -/
theorem uniform_prob_eq_measure {α : Type}
    [SampleableType α] [MeasurableSpace α] [DiscreteMeasurableSpace α]
    (event : α → Prop) :
    Pr{let x ← ($ᵗ α : ProbComp α)}[event x] = uniformOn (Set.univ : Set α) {x | event x} := by
  classical
  have : Fintype α := Fintype.ofFinite α
  rw [SampleableType.prEvent_uniformSample, uniformOn_univ]
  have hset : {x | event x} = ((Finset.univ.filter event : Finset α) : Set α) := by
    ext x; simp
  rw [hset, Measure.count_apply_finset]

/-- Exact identification of the full-view tape's load law with the proved occupancy law. -/
theorem loads_probability {requests : Nat} (event : (Instance → Nat) → Prop) :
    Pr{let tape ← ($ᵗ Tape requests : ProbComp (Tape requests))}[event (loads tape)] =
      ForsConcentration.uniformLoads (2 ^ 63) requests {counts | event counts} := by
  calc Pr{let tape ← ($ᵗ Tape requests : ProbComp (Tape requests))}[event (loads tape)]
      = Pr{let w ← instanceWord <$> ($ᵗ Tape requests : ProbComp (Tape requests))}[
          event (ForsConcentration.wordLoads w)] := by
        rw [prEvent_map]; simp_rw [loads_eq_wordLoads]
    _ = Pr{let w ← ($ᵗ InstanceWord requests : ProbComp (InstanceWord requests))}[
          event (ForsConcentration.wordLoads w)] :=
        (evalDist_instanceWord_uniform requests).prEvent_eq _
    _ = uniformOn (Set.univ : Set (InstanceWord requests))
          {w | event (ForsConcentration.wordLoads w)} := uniform_prob_eq_measure _
    _ = _ := by
        rw [ForsConcentration.uniformLoads,
          Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete]
        rfl

end SlhDsaSecurity.ForsDisclosureTape
