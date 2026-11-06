/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Interval.Merkle
import all HashSig.GXMSS.Interval.Merkle
public import VCVio.EvalDist.IndepProductMeasure
public import VCVio.EvalDist.Monad.Measure
public import VCVio.EvalDist.Monad.Seq.Uniform

/-!
# Inactive frontier input families and independent filler tables

The maximal inactive frontier splits into endpoint-vector and ordered-child-pair inputs.
Each family carries its exact capacity; independent table samplers assemble the complete frontier.
-/

public section

namespace GXMSS.Interval.Filler

open GXMSS.IntervalMerkle OracleSpec OracleComp TweakableHash

variable {PP T X H M R : Type} {h w v : ℕ}

/-- The two original-input domains used at an inactive frontier. -/
inductive Family
  /-- A leaf hashes its complete endpoint vector. -/
  | endpointVector
  /-- An internal node hashes its ordered left and right children. -/
  | childPair
  deriving DecidableEq, Repr

/-- Original input payload at a frontier of the selected family. -/
@[expose] def Input (f : Family) (H : Type) (v : ℕ) : Type :=
  match f with
  | .endpointVector => Fin v → H
  | .childPair => H × H

instance (f : Family) [SampleableType H] : SampleableType (Input f H v) := by
  cases f <;> unfold Input <;> infer_instance

/-- Family membership depends only on the address height. -/
@[expose] def HasFamily (f : Family) {I : Interval h} (node : Subtree.FrontierNode I) : Prop :=
  let (height, _) := node.val
  match f with
  | .endpointVector => height.val = 0
  | .childPair => 0 < height.val

instance (f : Family) (I : Interval h) (node : Subtree.FrontierNode I) :
    Decidable (HasFamily f node) := by
  cases f <;> unfold HasFamily <;> infer_instance

/-- Exact finite target subtype; no frontier-size estimate is used. -/
@[expose] def Target (f : Family) (I : Interval h) :=
  { node : Subtree.FrontierNode I // HasFamily f node }

instance (f : Family) (I : Interval h) : Fintype (Target f I) :=
  inferInstanceAs (Fintype { node : Subtree.FrontierNode I // HasFamily f node })

instance (f : Family) (I : Interval h) : DecidableEq (Target f I) :=
  inferInstanceAs (DecidableEq { node : Subtree.FrontierNode I // HasFamily f node })

/-- The finite Merkle address associated to a target. -/
@[expose] def address {f : Family} {I : Interval h} (n : Target f I) :
    Fin (h + 1) × Fin (2 ^ h) :=
  let node := n.val
  node.val

/-- Distinct targets have distinct original tree addresses. -/
theorem address_injective (f : Family) (I : Interval h) :
    Function.Injective (address (f := f) (I := I)) := by
  intro a b hab
  exact Subtype.ext (Subtype.ext hab)

/-- Number of nodes in the selected inactive frontier family. -/
@[expose] def targetCapacity (f : Family) (I : Interval h) : ℕ := Fintype.card (Target f I)

/-- The vector and pair target families partition the inactive frontier by height. -/
theorem targetCapacity_sum_eq_frontier_card (I : Interval h) :
    GXMSS.Interval.Filler.targetCapacity .endpointVector I +
      GXMSS.Interval.Filler.targetCapacity .childPair I = Fintype.card (Subtree.FrontierNode I) :=
          by
  let split : GXMSS.Interval.Filler.Target .endpointVector I ⊕
      GXMSS.Interval.Filler.Target .childPair I ≃ Subtree.FrontierNode I :=
    { toFun := Sum.elim Subtype.val Subtype.val
      invFun := fun node =>
        if hz : GXMSS.Interval.Filler.HasFamily .endpointVector node then Sum.inl ⟨node, hz⟩
        else Sum.inr ⟨node, by
          obtain ⟨⟨height, index⟩, hf⟩ := node
          change ¬ height.val = 0 at hz
          change 0 < height.val
          omega⟩
      left_inv := by
        rintro (⟨node, hn⟩ | ⟨node, hn⟩)
        · change (if hz : GXMSS.Interval.Filler.HasFamily .endpointVector node then
              (Sum.inl ⟨node, hz⟩ : GXMSS.Interval.Filler.Target .endpointVector I ⊕
                GXMSS.Interval.Filler.Target .childPair I) else Sum.inr ⟨node, _⟩) = Sum.inl ⟨node,
                    hn⟩
          rw [dite_eq_left hn]
        · have hz : ¬ GXMSS.Interval.Filler.HasFamily .endpointVector node := by
            obtain ⟨⟨height, index⟩, hf⟩ := node
            change 0 < height.val at hn
            change ¬ height.val = 0
            omega
          change (if hz : GXMSS.Interval.Filler.HasFamily .endpointVector node then
              (Sum.inl ⟨node, hz⟩ : GXMSS.Interval.Filler.Target .endpointVector I ⊕
                GXMSS.Interval.Filler.Target .childPair I) else Sum.inr ⟨node, _⟩) = Sum.inr ⟨node,
                    hn⟩
          rw [dite_eq_right hz]
      right_inv := by intro node; dsimp; split <;> rfl }
  simpa only [Fintype.card_sum, GXMSS.Interval.Filler.targetCapacity] using Fintype.card_congr split

/-- Embedding of the selected original input domain into the common THF domain. -/
@[expose] def embed (P : HashInstance PP T X H h w v) (f : Family) : Input f H v ↪ X :=
  match f with
  | .endpointVector => P.vectorInput
  | .childPair => P.pairInput

/-- The target's original addressed-tree tweak. -/
@[expose] def tweak (P : HashInstance PP T X H h w v) {f : Family} {I : Interval h}
    (n : Target f I) : T := P.treeTweak (address n)

instance (f : Family) (h : ℕ) : IsEmpty (Target f (Interval.full h)) where
  false n := isEmptyElim n.val

/-- A full interval has no target of either family. -/
@[simp] theorem targetCapacity_full (f : Family) (h : ℕ) :
    targetCapacity f (Interval.full h) = 0 := Fintype.card_eq_zero

/-- The family whose fillers remain independently uniform in a one-family hybrid. -/
@[expose] def Family.other : Family → Family
  | .endpointVector => .childPair
  | .childPair => .endpointVector

/-- Uniform digest table on one exact target family. -/
@[expose] noncomputable def sampleTable [SampleableType H] (f : Family) (I : Interval h) :
    ProbComp (Target f I → H) := Fintype.mPi (fun _ : Target f I => $ᵗ H)

/-- Combine the two disjoint family tables into one cached complete frontier table. -/
@[expose] def assemble (f : Family) (I : Interval h)
    (selected : Target f I → H) (other : Target f.other I → H) : Fillers I H :=
  fun node =>
    if hf : HasFamily f node then selected ⟨node, hf⟩
    else other ⟨node, by
      cases f with
      | endpointVector => exact Nat.pos_of_ne_zero hf
      | childPair => exact Nat.eq_zero_of_not_pos hf⟩

/-- Reading a selected-family coordinate from the complete table recovers its retained answer. -/
@[simp] theorem assemble_selected (f : Family) (I : Interval h)
    (selected : Target f I → H) (other : Target f.other I → H) (n : Target f I) :
    assemble f I selected other n.val = selected n := by
  obtain ⟨node, hf⟩ := n
  simp [assemble, hf]

/-- Reading an other-family coordinate recovers its independently sampled digest. -/
@[simp] theorem assemble_other (f : Family) (I : Interval h)
    (selected : Target f I → H) (other : Target f.other I → H) (n : Target f.other I) :
    assemble f I selected other n.val = other n := by
  obtain ⟨node, hf⟩ := n
  have hnot : ¬ HasFamily f node := by
    cases f <;> simp_all [HasFamily, Family.other]
    omega
  simp [assemble, hnot]

/-- Splitting and assembling family tables recovers the complete cached frontier table. -/
theorem assemble_restrict (f : Family) (I : Interval h) (fillers : Fillers I H) :
    assemble f I (fun n => fillers n.val) (fun n => fillers n.val) = fillers := by
  funext node
  simp only [assemble]
  split <;> rfl

/-- The partition into the selected and other family is a bijection of complete tables. -/
@[expose] def tableEquiv (f : Family) (I : Interval h) (H : Type) :
    ((Target f I → H) × (Target f.other I → H)) ≃ Fillers I H where
  toFun tables := assemble f I tables.1 tables.2
  invFun fillers := (fun n => fillers n.val, fun n => fillers n.val)
  left_inv tables := by
    obtain ⟨selected, other⟩ := tables
    apply Prod.ext <;> funext n
    · exact assemble_selected f I selected other n
    · exact assemble_other f I selected other n
  right_inv fillers := assemble_restrict f I fillers

/-- Ordered independent draws can be retained as a finite function without changing the program. -/
theorem replicate_eq_ofFn_mOfFn (n : ℕ) (draw : ProbComp H) :
    OracleComp.replicate n draw = List.ofFn <$> Fin.mOfFn n (fun _ => draw) := by
  induction n with
  | zero => simp [OracleComp.replicate_zero, Fin.mOfFn]
  | succ n ih =>
    simp [OracleComp.replicate_succ_bind, Fin.mOfFn, ih, List.ofFn_succ, monad_norm]

/-- The ordered family sampler has the whole uniform finite-function measure. -/
theorem orderedTable_uniform [SampleableType H] (n : ℕ) :
    letI : MeasurableSpace H := ⊤
    𝒟[Fin.mOfFn n (fun _ => ($ᵗ H : ProbComp H))] =
      ProbabilityTheory.uniformOn Set.univ := by
  let : MeasurableSpace H := ⊤
  rw [evalDist_mOfFn]
  simp_rw [SampleableType.evalDist_uniformSample]
  simpa using (ProbabilityTheory.uniformOn_pi (f := fun _ : Fin n => (Set.univ : Set H))).symm

/-- Each family's canonical table sampler denotes the whole uniform table measure. -/
theorem sampleTable_uniform [SampleableType H] (f : Family) (I : Interval h) :
    letI : MeasurableSpace H := ⊤
    𝒟[(sampleTable f I : ProbComp (Target f I → H))] =
      ProbabilityTheory.uniformOn Set.univ := by
  let : MeasurableSpace H := ⊤
  exact evalDist_mPi_const_uniform ($ᵗ H) SampleableType.evalDist_uniformSample

private theorem mOfFn_zero_exists (n : ℕ) (hn : n = 0) (draw : ProbComp H) :
    ∃ values : Fin n → H, Fin.mOfFn n (fun _ => draw) = pure values := by
  subst n
  exact ⟨Fin.elim0, rfl⟩

/-- The source filler sampler is the full independent product, including the empty frontier. -/
theorem sampleFillers_eq_mPi [SampleableType H] (I : Interval h) :
    sampleFillers I H = Fintype.mPi (fun _ : Subtree.FrontierNode I => $ᵗ H) := by
  by_cases hc : Fintype.card (Subtree.FrontierNode I) = 0
  · let empty : IsEmpty (Subtree.FrontierNode I) := Fintype.card_eq_zero_iff.mp hc
    simp only [sampleFillers, dite_eq_left hc, Fintype.mPi]
    have hvalues := mOfFn_zero_exists (Fintype.card (Subtree.FrontierNode I)) hc ($ᵗ H)
    obtain ⟨values, hv⟩ := hvalues
    rw [hv, map_pure]
    congr 1
    funext node
    exact (empty.false node).elim
  · simp [sampleFillers, hc]

/-- The source sampler's entire complete-table measure is uniform. -/
theorem sampleFillers_uniform [SampleableType H] (I : Interval h) :
    letI : MeasurableSpace H := ⊤
    𝒟[(sampleFillers I H)] = ProbabilityTheory.uniformOn Set.univ := by
  let : MeasurableSpace H := ⊤
  rw [sampleFillers_eq_mPi]
  exact evalDist_mPi_const_uniform ($ᵗ H) SampleableType.evalDist_uniformSample

/-- Independently sampling the two family tables yields the whole source filler-table law. -/
theorem assemble_tables_measure [SampleableType H] (f : Family) (I : Interval h) :
    letI : MeasurableSpace H := ⊤
    𝒟[(do
      let selected ← (sampleTable f I : ProbComp (Target f I → H))
      let other ← sampleTable f.other I
      pure (assemble f I selected other))] = 𝒟[sampleFillers I H] := by
  let : MeasurableSpace H := ⊤
  rw [sampleFillers_uniform]
  have h := evalDist_seq_map_eq_uniformOn (sampleTable f I : ProbComp (Target f I → H))
    (sampleTable f.other I) (assemble f I)
    (sampleTable_uniform f I) (sampleTable_uniform f.other I)
    Measurable.of_discrete (tableEquiv f I H).bijective
  simpa only [map_eq_bind_pure_comp, seq_eq_bind_map, bind_assoc, pure_bind,
    Function.comp_def] using h

/-- Every frontier table has the product mass of its independent uniform coordinates. -/
theorem sampleFillers_probability [SampleableType H]
    (I : Interval h) (fillers : Fillers I H) :
    Pr{let sampled ← GXMSS.IntervalMerkle.sampleFillers I H}[sampled = fillers] =
      ∏ node : Subtree.FrontierNode I, Pr{let digest ← $ᵗ H}[digest = fillers node] := by
  let : MeasurableSpace H := ⊤
  rw [sampleFillers_eq_mPi, prEvent_eq_evalDist_singleton, evalDist_mPi]
  simp_rw [prEvent_eq_evalDist_singleton]
  exact MeasureTheory.Measure.pi_singleton _ fillers

/-- Each frontier coordinate has uniform inverse-cardinality mass, independently. -/
theorem sampleFillers_uniform_probability [SampleableType H] [Fintype H]
    (I : Interval h) (fillers : Fillers I H) :
    Pr{let sampled ← GXMSS.IntervalMerkle.sampleFillers I H}[sampled = fillers] =
      ∏ _node : Subtree.FrontierNode I, (Fintype.card H : ENNReal)⁻¹ := by
  rw [sampleFillers_probability]
  simp_rw [SampleableType.prEvent_uniformSample_eq_singleton]

end GXMSS.Interval.Filler
