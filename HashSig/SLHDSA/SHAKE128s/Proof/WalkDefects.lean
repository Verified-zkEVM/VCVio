/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.RandomizerGate
public import HashSig.SLHDSA.SHAKE128s.Proof.WarmedGame

/-!
# The seeds' own coincidences, charged rather than assumed

Two of the charges carry a hypothesis about the key that is not a budget: that the PRF seed and
the public seed differ, which is what keeps the `PRF_msg` and canonical classes apart. Carried
as a hypothesis it is an assumption about the key; discharged it is a defect, and the defect is
one unit of `2 ^ -128` because the two seeds are drawn independently and uniformly before
anything else happens.

Discharging it is averaging over the walk, and the walk is where the seeds are drawn, so the
event is settled before the graph is traversed and before the adversary runs. That is the whole
argument: an event that reads only the walk's prefix is bounded by its probability in that
prefix, whatever happens afterwards.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.WalkDefects

variable {α β : Type}

open Security CanonicalGraph WarmedGame

/-! ## Averaging -/

/-- **A bound that holds after every prefix holds over the bind.** -/
theorem probEvent_bind_le {α β : Type} (run : ProbComp α) (next : α → ProbComp β)
    (event : β → Prop) (bound : ℝ≥0∞) (hnext : ∀ value, Pr{let x ← next value}[event x] ≤ bound) :
    Pr{let x ← run >>= next}[event x] ≤ bound :=
  prEvent_bind_le_of_forall_le run next event hnext

open scoped Classical in
/-- **An event settled by the prefix costs what it costs there.** Whatever the continuation
does, an outcome in the event comes from a prefix in the prefix's event. -/
theorem probEvent_bind_le_of_prefix {α β : Type} (run : ProbComp α) (next : α → ProbComp β)
    (event : β → Prop) (prefixEvent : α → Prop)
    (hprefix : ∀ value, ∀ result ∈ support (next value), event result → prefixEvent value) :
    Pr{let x ← run >>= next}[event x] ≤ Pr{let x ← run}[prefixEvent x] :=
  prEvent_bind_le_prEvent_of_forall_eq_zero run next prefixEvent event fun value hvalue =>
    prEvent_eq_zero_of_forall_mem_support _ _ fun result hresult hevent =>
      hvalue (hprefix value result hresult hevent)

open scoped Classical in
/-- **A bound that holds after every good prefix holds over the pair, at the cost of the bad
ones.** -/
theorem probEvent_bind_pair_split_le {α β : Type} (first : ProbComp α) (rest : α → ProbComp β)
    (event : α → β → Prop) (bad : α → Prop) (bound : ℝ≥0∞)
    (hrest : ∀ value ∈ support first, ¬ bad value →
      Pr{let x ← rest value}[(event value) x] ≤ bound) :
    Pr{let pair ← (do let value ← first; let result ← rest value; pure (value, result))}[
        event pair.1 pair.2] ≤
      bound + Pr{let x ← first}[bad x] := by
  rw [add_comm]
  refine prEvent_bind_le_prEvent_add_of_support first _ bad _ fun value hmem hbad => ?_
  rw [bind_pure_comp, prEvent_map]
  exact hrest value hmem hbad

/-! ## The seeds differ -/

/-- **The PRF seed and the public seed coincide with probability `2 ^ -128`.** -/
theorem prob_prf_eq_publicSeed_seeds :
    Pr{let sds ← seeds}[sds.2.1 = sds.2.2] ≤
      1 / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  rw [seeds]
  refine probEvent_bind_le _ _ _ _ fun secretSeed => ?_
  refine probEvent_bind_le _ _ _ _ fun prfSeed => ?_
  rw [bind_pure_comp, prEvent_map]
  exact le_of_eq (SecretGuessCharge.prob_single_guess prfSeed)

/-- **The same at the walk**, the seeds being drawn before it traverses anything. -/
theorem prob_prf_eq_publicSeed_walk :
    Pr{let walk ← graphWalk}[walk.1.1.2.1 = walk.1.1.2.2] ≤ 1 / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  rw [graphWalk_eq]
  refine le_trans (probEvent_bind_le_of_prefix seeds _ _
    (fun sds : Digest × Digest × Digest => sds.2.1 = sds.2.2) ?_) prob_prf_eq_publicSeed_seeds
  intro sds walk hwalk hevent
  rw [mem_support_bind_iff] at hwalk
  obtain ⟨step, -, hpure⟩ := hwalk
  rw [support_pure, Set.mem_singleton_iff] at hpure
  rw [hpure] at hevent
  exact hevent

/-! ## The public root is one of the walk's cells

The public key is the public seed and the top subtree's root, and that root is the graph's own
cell at the top `tree` node. So the pair the separation hypothesis is about is read off the
walk: one of its seeds and one of its cells.

What makes the defect `2 ^ -165` rather than the far weaker bound a fixed seed would give is
that the two are **jointly** uniform. The seed is drawn in the walk's prefix, the cell is one
coordinate of the uniform output table the traversal draws afterwards, and a coordinate of a
uniform table, truncated, is a uniform digest. Fixing the seed first and bounding the cell alone
would cost a factor of the number of address prefixes. -/

/-- The graph node whose cell is the public root: the top subtree's root. -/
def topNode : StructuralNode :=
  .tree ⟨⟨layers - 1, by decide⟩, ⟨0, by decide⟩⟩ ⟨subtreeHeight - 1, by decide⟩
    ⟨0, by decide⟩

variable [HasQuery HashSpec Id]

/-- **The public root is that cell.** -/
theorem value_topNode (secretSeed publicSeed : Digest) :
    value secretSeed publicSeed (.structural topNode) =
      Extraction.HypertreeChain.honestNode secretSeed publicSeed (layers - 1) 0 := rfl

omit [HasQuery HashSpec Id] in
/-- **A coordinate of the walk's output table, truncated, is a uniform digest.** -/
theorem outputs_coordinate_uniform (parent : StructuralNode) :
    ((fun outputs : Programming.Outputs => Hashing.truncate (outputs parent)) <$>
        ($ᵗ Programming.Outputs : ProbComp Programming.Outputs)) =ᵈ
      ($ᵗ Digest : ProbComp Digest) := by
  classical
  have hcoordinate : ((fun outputs : Programming.Outputs => outputs parent) <$>
      ($ᵗ Programming.Outputs : ProbComp Programming.Outputs)) =ᵈ
      ($ᵗ HashOutput : ProbComp HashOutput) := by
    let split : Programming.Outputs ≃ HashOutput × ({other // other ≠ parent} → HashOutput) :=
      Equiv.funSplitAt parent HashOutput
    have hmap : (fun outputs : Programming.Outputs => outputs parent) <$>
          ($ᵗ Programming.Outputs : ProbComp Programming.Outputs) =
        Prod.fst <$> (split <$> ($ᵗ Programming.Outputs : ProbComp Programming.Outputs)) := by
      rw [Functor.map_map]
      congr 1
    rw [hmap]
    refine ((SampleableType.map_uniformSample_evalDistEq_of_bijective
      split.bijective).map Prod.fst).trans ?_
    refine EvalDistEq.of_forall_prEvent_eq fun p => ?_
    rw [prEvent_map]
    exact SampleableType.prEvent_uniformSample_fst p
  have hcomp : (fun outputs : Programming.Outputs => Hashing.truncate (outputs parent)) <$>
        ($ᵗ Programming.Outputs : ProbComp Programming.Outputs) =
      Hashing.truncate <$> ((fun outputs : Programming.Outputs => outputs parent) <$>
        ($ᵗ Programming.Outputs : ProbComp Programming.Outputs)) := by
    rw [Functor.map_map]
  rw [hcomp]
  exact (hcoordinate.map Hashing.truncate).trans KeygenUniform.truncate_uniform

omit [HasQuery HashSpec Id] in
/-- **The two halves of the public key form an address prefix with probability `2 ^ -165`.**
The seed is the walk's own and the root is one of its cells, drawn afterwards and
independently. -/
theorem prob_possible_walk :
    Pr{let walk ← graphWalk}[
        HashSeparation.Possible (walk.1.1.2.2, walk.1.2 (.structural topNode))] ≤
      1 / ((2 ^ 165 : Nat) : ℝ≥0∞) := by
  classical
  have hroot : ∀ publicSeed : Digest,
      Pr{let outputs ← ($ᵗ Programming.Outputs : ProbComp Programming.Outputs)}[
          HashSeparation.Possible (publicSeed, Hashing.truncate (outputs topNode))] =
        Pr{let root ← ($ᵗ Digest : ProbComp Digest)}[
          HashSeparation.Possible (publicSeed, root)] := by
    intro publicSeed
    have h := (outputs_coordinate_uniform topNode).prEvent_eq
      (fun root => HashSeparation.Possible (publicSeed, root))
    rwa [prEvent_map] at h
  rw [graphWalk_eq, seeds]
  simp only [bind_assoc, pure_bind]
  refine prEvent_bind_le_of_forall_le _ _ _ fun secretSeed => ?_
  refine prEvent_bind_le_of_forall_le _ _ _ fun prfSeed => ?_
  have hwarm := EvalDistEq.bind_right ($ᵗ Digest : ProbComp Digest) fun publicSeed =>
    (Programming.warmup_uniform publicSeed secretSeed).bind_left
      (fun result => (pure (((secretSeed, prfSeed, publicSeed), result.1), result.2) :
        ProbComp (((Digest × Digest × Digest) × Cells) × QueryCache HashSpec)))
  rw [hwarm.prEvent_eq]
  simp only [prEvent_norm]
  refine le_trans (le_of_eq ?_) HashSeparation.prob_possible_le
  rw [SampleableType.prEvent_uniformSample_prod]
  let _ : MeasurableSpace Digest := ⊤
  rw [prEvent_bind_of_discrete, prEvent_bind_of_discrete]
  exact MeasureTheory.lintegral_congr fun publicSeed => hroot publicSeed

end SlhDsaSecurity.WalkDefects
