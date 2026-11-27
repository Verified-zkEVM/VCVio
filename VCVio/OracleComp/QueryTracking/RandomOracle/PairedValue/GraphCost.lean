/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.PairedValue
public import VCVio.OracleComp.QueryTracking.RandomOracle.Defer
public import VCVio.OracleComp.QueryTracking.WriterCost.StateT
import VCVio.OracleComp.QueryTracking.RandomOracle.CachePartial.Cost

/-!
# The physical query count of a paired graph caller

The caller pays for its original full queries.
Each full query reads at most two ordinary rows at the same physical input.
Private sampling leaves the ordinary cache unchanged.
-/

public section

open OracleComp OracleSpec
namespace CanonicalGraph.PairedQueries

/-- The public oracle has two rows at each physical input. -/
abbrev PairedSpec (L H : Type) := (L ⊕ L) →ₒ H

/-- The caller can draw private coins and ask for full words. -/
abbrev FullWorld (L F : Type) := unifSpec + (L →ₒ F)

/-- The deferred interpreter records the cells that await a final draw. -/
abbrev DeferredState (L H X K : Type) := RelabelState (PairedSpec L H) X K H × List (X ⊕ K)

variable {L H F X K : Type} (G : CanonicalGraph (PairedSpec L H) X K H) (e : F ≃ H × H)
  [DecidableEq L] [DecidableEq X] [DecidableEq K] [SampleableType H]

/-- A physical input is present if either ordinary row has a reply. -/
@[expose] def physicalInputs (c : (PairedSpec L H).QueryCache) : Set L :=
  {b | (c (.inl b)).isSome ∨ (c (.inr b)).isSome}

/-- Each original full query costs one and private randomness costs zero. -/
abbrev rawCost : ℕ ⊕ L → Nat := Sum.elim (fun _ => 0) (fun _ => 1)

/-- Forward private and public queries to the public part of the graph interpreter. -/
@[expose] def liftPublic :
    QueryImpl (unifSpec + PairedSpec L H) (OracleComp ((PairedSpec L H).withLabels X K H)) :=
  Sum.rec (fun n => query (spec := (PairedSpec L H).withLabels X K H) (.inl (.inl (.inl n))))
    (fun row => query (spec := (PairedSpec L H).withLabels X K H) (.inl (.inl (.inr row))))

/-- Answer a full query by reading its paired rows in the deferred graph. -/
@[expose] noncomputable def callerImpl :
    QueryImpl (FullWorld L F) (StateT (DeferredState L H X K) ProbComp) :=
  QueryImpl.compose G.deferredImpl
    (QueryImpl.compose liftPublic (RandomOraclePairedValue.readHalves e))

private theorem public_frame (key : L ⊕ L) (st : DeferredState L H X K)
    {z} (hz : z ∈ support ((G.deferredImpl (.inl (.inl (.inr key)))).run st))
    (other : L ⊕ L) (different : other ≠ key) :
    z.2.1.1 other = st.1.1 other := by
  rw [G.deferredImpl_run_inl, support_map] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  by_cases ready : ∃ k vs, G.childVals st.1 k = some vs ∧ G.pt k vs = key
  · obtain ⟨k, vs, children, rfl⟩ := ready
    rw [G.relabelImpl_run_pt children, support_map] at hw
    obtain ⟨u, hu, rfl⟩ := hw
    rw [RelabelState.drawCell_run, support_map] at hu
    obtain ⟨_, _, rfl⟩ := hu
    rfl
  · rw [G.relabelImpl_run_pub_of_not_exists ready, support_map] at hw
    obtain ⟨u, hu, rfl⟩ := hw
    exact (congrArg (fun c : (PairedSpec L H).QueryCache => c other)
      (QueryImpl.withCaching_run_eq_cacheQuery uniformSampleImpl hu)).trans
        (QueryCache.cacheQuery_of_ne _ _ different)

private theorem public_footprint (key : L ⊕ L)
    (st : DeferredState L H X K) {z}
    (hz : z ∈ support ((G.deferredImpl (.inl (.inl (.inr key)))).run st)) :
    physicalInputs z.2.1.1 ⊆ insert (key.elim id id) (physicalInputs st.1.1) := by
  intro b present
  by_cases same : b = key.elim id id
  · exact Or.inl same
  · refine Or.inr ?_
    have left : Sum.inl b ≠ key := fun h => same (congrArg (Sum.elim id id) h)
    have right : Sum.inr b ≠ key := fun h => same (congrArg (Sum.elim id id) h)
    simpa only [physicalInputs, Set.mem_ofPred_eq, public_frame G key st hz _ left,
      public_frame G key st hz _ right] using present

/-- Reading both halves may add their shared physical input and leaves every other input alone. -/
private theorem full_step (b : L) (st : DeferredState L H X K) {z}
    (hz : z ∈ support (((callerImpl G e) (.inr b)).run st)) :
    physicalInputs z.2.1.1 ⊆ insert b (physicalInputs st.1.1) := by
  simp only [callerImpl, QueryImpl.compose,
    RandomOraclePairedValue.readHalves, simulateQ_bind, simulateQ_pure,
    simulateQ_spec_query, liftPublic, simulateQ_HasQuery_query, StateT.run_bind, StateT.run_pure,
    mem_support_bind_iff, mem_support_pure_iff] at hz
  obtain ⟨low, hl, high, hh, rfl⟩ := hz
  have afterLow := public_footprint G (.inl b) st hl
  have afterHigh := public_footprint G (.inr b) low.2 hh
  -- Both steps insert b, so a repeat or an already populated sibling costs no extra row.
  exact afterHigh.trans (by simpa using Set.insert_subset_insert (a := b) afterLow)

/-- Repeating a full query preserves the set of physical public inputs.
It suffices that either tagged row for the input was already in the ordinary public cache. -/
theorem fullWord_repeat (b : L) (st : DeferredState L H X K)
    (present : b ∈ physicalInputs st.1.1) {z}
    (supported : z ∈ support ((simulateQ G.deferredImpl
      (simulateQ liftPublic (RandomOraclePairedValue.readHalves e (.inr b)))).run st)) :
    physicalInputs z.2.1.1 = physicalInputs st.1.1 := by
  have subset := full_step G e b st supported
  refine Set.Subset.antisymm (by simpa only [Set.insert_eq_of_mem present] using subset) ?_
  have extension := (G.le_of_mem_support_simulateQ_deferredImpl _ supported).1
  rintro input (left | right)
  · exact Or.inl (QueryCache.isSome_mono extension left)
  · exact Or.inr (QueryCache.isSome_mono extension right)

/-- The growth of the physical footprint is bounded by the charge of the raw query. -/
theorem caller_step_cost (t : (FullWorld L F).Domain) (st : DeferredState L H X K) {z}
    (hz : z ∈ support (((callerImpl G e) t).run st)) :
    (physicalInputs z.2.1.1).encard ≤ (physicalInputs st.1.1).encard + rawCost t := by
  cases t with
  | inr b => exact (Set.encard_le_encard (full_step G e b st hz)).trans (Set.encard_insert_le _ _)
  | inl n =>
    simp only [callerImpl, QueryImpl.compose,
      RandomOraclePairedValue.readHalves, simulateQ_spec_query, liftPublic,
      simulateQ_HasQuery_query, G.deferredImpl_run_inl, CanonicalGraph.relabelImpl_run_unif,
      Functor.map_map, support_map] at hz
    obtain ⟨_, _, rfl⟩ := hz
    simp [rawCost]

/-- The distinct public inputs that the actual run adds consume at most its recorded cost.
This also holds from a warm state in which exactly one of the two rows is populated. -/
theorem metered_footprint {α : Type} (caller : OracleComp (FullWorld L F) α)
    (st : DeferredState L H X K)
    (z : (α × Nat) × DeferredState L H X K)
    (hz : z ∈ support
      (((simulateQ ((callerImpl G e).withAddCost rawCost) caller).runAdd).run st)) :
    (physicalInputs z.2.1.1).encard ≤ (physicalInputs st.1.1).encard + z.1.2 :=
  QueryImpl.resource_le_runAdd (callerImpl G e) (fun s => (physicalInputs s.1.1).encard) rawCost
    (fun t s _ h => caller_step_cost G e t s h) caller st z hz

/-- Mark queries on the original free caller, then expand each public read into its two rows. -/
@[expose] def meteredCaller {α : Type} (caller : OracleComp (FullWorld L F) α) :
    OracleComp ((PairedSpec L H).withLabels X K H) (α × Nat) :=
  simulateQ liftPublic (simulateQ (RandomOraclePairedValue.readHalves e)
    (simulateQ ((QueryImpl.id' (FullWorld L F)).withAddCost rawCost) caller).runAdd)

/-- The deferred interpreter keeps the original caller's observed charge. -/
theorem run_meteredCaller {α : Type} (caller : OracleComp (FullWorld L F) α) :
    simulateQ G.deferredImpl (meteredCaller e caller) =
      (simulateQ ((callerImpl G e).withAddCost rawCost) caller).runAdd := by
  unfold meteredCaller callerImpl
  rw [← QueryImpl.simulateQ_compose liftPublic (RandomOraclePairedValue.readHalves e),
    ← QueryImpl.simulateQ_compose, QueryImpl.simulateQ_withAddCost_runAdd_fusion]

/-- A caller may follow a graph program and depend on its result.
The combined cost adds the setup's recorded charge to the caller's actual charge. -/
@[expose] def afterSetup {α β : Type}
    (setup : OracleComp ((PairedSpec L H).withLabels X K H) (β × Nat))
    (caller : β → OracleComp (FullWorld L F) α) :
    OracleComp ((PairedSpec L H).withLabels X K H) (α × Nat) := do
  let (b, startCost) ← setup
  let (a, cost) ← meteredCaller e (caller b)
  return (a, startCost + cost)

/-- A paid setup and its raw caller share one bound on distinct physical public inputs. -/
theorem afterSetup_footprint {α β : Type}
    (setup : OracleComp ((PairedSpec L H).withLabels X K H) (β × Nat))
    (caller : β → OracleComp (FullWorld L F) α)
    (paid : ∀ z ∈ support ((simulateQ G.deferredImpl setup).run ((∅, ∅), [])),
      (physicalInputs z.2.1.1).encard ≤ z.1.2)
    (z)
    (hz : z ∈ support ((simulateQ G.deferredImpl (afterSetup e setup caller)).run ((∅, ∅), []))) :
    (physicalInputs z.2.1.1).encard ≤ z.1.2 := by
  simp only [afterSetup, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    mem_support_bind_iff, mem_support_pure_iff] at hz
  obtain ⟨s, before, t, tail, rfl⟩ := hz
  rw [run_meteredCaller] at tail
  apply (metered_footprint G e _ _ _ tail).trans
  simpa using add_le_add_left (paid s before) (t.1.2 : ℕ∞)

end CanonicalGraph.PairedQueries
