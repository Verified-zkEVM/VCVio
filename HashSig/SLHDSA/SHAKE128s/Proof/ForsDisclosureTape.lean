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

The experiment samples a uniform finite tape of full parsed digest views. These
lemmas connect its actual disclosure sets to the occupancy and prefix-cap
probability bounds. Coupling this experiment to an adaptive shared random oracle
is a separate obligation.
-/

@[expose] public section

open OracleComp OracleSpec MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

noncomputable section

namespace SlhDsaSecurity.ForsDisclosureTape

abbrev View := ForsCoverage.View
abbrev Instance := ForsCoverage.Instance
abbrev Tree := ForsCoverage.Tree
abbrev Leaf := ForsCoverage.Leaf
abbrev Tape (requests : Nat) := Fin requests → View
abbrev InstanceWord (requests : Nat) := Fin requests → Instance
abbrev LeafWord (requests : Nat) := Fin requests → Tree → Leaf

def instanceWord {requests : Nat} (tape : Tape requests) : InstanceWord requests :=
  fun j => (tape j).1

def loads {requests : Nat} (tape : Tape requests) (i : Instance) : Nat :=
  (Finset.univ.filter (fun j => (tape j).1 = i)).card

def disclosures {requests : Nat} (tape : Tape requests) : ForsCoverage.Disclosures :=
  fun i tree => (Finset.univ.filter (fun j => (tape j).1 = i)).image
    (fun j => (tape j).2 tree)

theorem disclosures_card_le_loads {requests : Nat} (tape : Tape requests)
    (i : Instance) (tree : Tree) : (disclosures tape i tree).card ≤ loads tape i :=
  Finset.card_image_le

theorem loads_eq_wordLoads {requests : Nat} (tape : Tape requests) :
    loads tape = ForsConcentration.wordLoads (instanceWord tape) := by
  funext i
  simp only [loads, ForsConcentration.wordLoads, ForsConcentration.wordCounts,
    Finsupp.finsetSum_apply, Finsupp.single_apply, Finset.card_eq_sum_ones,
    Finset.sum_filter, instanceWord]

def splitTape (requests : Nat) : Tape requests ≃ InstanceWord requests × LeafWord requests where
  toFun tape := (instanceWord tape, fun j => (tape j).2)
  invFun pair j := (pair.1 j, pair.2 j)
  left_inv := by intro tape; rfl
  right_inv := by intro pair; rfl

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
theorem uniform_prob_eq_measure {α : Type} [Fintype α] [Nonempty α]
    [SampleableType α] [MeasurableSpace α] [DiscreteMeasurableSpace α]
    (event : α → Prop) :
    Pr{let x ← ($ᵗ α : ProbComp α)}[event x] = uniformOn (Set.univ : Set α) {x | event x} := by
  classical
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
