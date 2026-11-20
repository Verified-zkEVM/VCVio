/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module

public import VCVio.OracleComp.SimSemantics.StateT.PreservesInv
public import VCVio.OracleComp.QueryTracking.RandomOracle.PairedValue.GraphCost

/-!
# Occupied rows under paired public queries

Each query reads the low row before the high row.
If a low row is canonical, the high row is already canonical.
If the low row is ordinary, it is present before the high query runs.
-/

public section

open OracleComp OracleSpec
namespace CanonicalGraph.PairedQueries

variable {L H F X K : Type} (G : CanonicalGraph (PairedSpec L H) X K H) (e : F ≃ H × H)
  [DecidableEq L] [DecidableEq X] [DecidableEq K] [SampleableType H]

/-- A high ordinary row is occupied only together with the corresponding low ordinary row. -/
@[expose] def PresentTogether (st : DeferredState L H X K) : Prop :=
  ∀ b : L, (st.1.1 (.inr b)).isSome → (st.1.1 (.inl b)).isSome

/-- The same query values enable both halves of the public point. -/
@[expose] def Ready (st : RelabelState (PairedSpec L H) X K H) (key : L ⊕ L) : Prop :=
  ∃ k vs, G.childVals st k = some vs ∧ G.pt k vs = key

private theorem ready_frame (st : DeferredState L H X K) (key : L ⊕ L) (ready : Ready G st.1 key)
    {z} (hz : z ∈ support ((G.deferredImpl (.inl (.inl (.inr key)))).run st)) :
    z.2.1.1 = st.1.1 := by
  obtain ⟨k, vs, children, rfl⟩ := ready
  rw [G.deferredImpl_run_inl, support_map] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  rw [G.relabelImpl_run_pt children, support_map] at hw
  obtain ⟨v, hv, rfl⟩ := hw
  rw [RelabelState.drawCell_run, support_map] at hv
  obtain ⟨u, hu, rfl⟩ := hv
  rfl

private theorem off_update (st : DeferredState L H X K) (key : L ⊕ L) (off : ¬ Ready G st.1 key)
    {z} (hz : z ∈ support ((G.deferredImpl (.inl (.inl (.inr key)))).run st)) :
    z.2.1.1 = st.1.1.cacheQuery key z.1 := by
  rw [G.deferredImpl_run_inl, support_map] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  rw [G.relabelImpl_run_pub_of_not_exists off, support_map] at hw
  obtain ⟨v, hv, rfl⟩ := hw
  exact QueryImpl.withCaching_run_eq_cacheQuery _ hv

/-- A paired read preserves joint presence even when its first draw enables further nodes. -/
private theorem read_preserves (paired : ∀ st b, Ready G st (.inl b) → Ready G st (.inr b))
    (st : DeferredState L H X K) (old : PresentTogether st) (b : L)
    {low} (hl : low ∈ support ((G.deferredImpl (.inl (.inl (.inr (.inl b))))).run st))
    {high} (hh : high ∈ support ((G.deferredImpl (.inl (.inl (.inr (.inr b))))).run low.2)) :
    PresentTogether high.2 := by
  by_cases ready : Ready G st.1 (.inl b)
  · obtain ⟨k, vs, kids, eqn⟩ := paired _ _ ready
    have later := G.childVals_mono (G.le_of_mem_support_deferredImpl hl) kids
    have r := ready_frame G low.2 (.inr b) ⟨k, vs, later, eqn⟩ hh
    simpa only [PresentTogether, r, ready_frame G st _ ready hl] using old
  · have update := off_update G st _ ready hl
    have preserved := (G.le_of_mem_support_deferredImpl hh).1
    intro x present
    by_cases same : x = b
    · subst x
      apply QueryCache.isSome_mono preserved
      rw [update]
      simp
    · have before : (low.2.1.1 (.inr x)).isSome := by
        by_cases hiReady : Ready G low.2.1 (.inr b)
        · rwa [ready_frame G _ _ hiReady hh] at present
        · rwa [off_update G _ _ hiReady hh, QueryCache.cacheQuery_of_ne _ _ (by simpa using same :
              (Sum.inr x : L ⊕ L) ≠ .inr b)] at present
      have orig : (st.1.1 (.inr x)).isSome := by
        simpa [update, QueryCache.cacheQuery_of_ne] using before
      exact QueryCache.isSome_mono
        ((G.le_of_mem_support_deferredImpl hl).1.trans preserved) (old _ orig)

/-- A single full call, or a private draw, preserves joint occupancy. -/
theorem caller_preserves_presence (paired : ∀ st b, Ready G st (.inl b) → Ready G st (.inr b)) :
    (callerImpl G e).PreservesInv PresentTogether := by
  intro t s inv w hw
  change w ∈ support (((QueryImpl.compose G.deferredImpl
    (QueryImpl.compose liftPublic (RandomOraclePairedValue.readHalves e))) t).run s) at hw
  cases t with
  | inr b =>
    simp only [QueryImpl.compose, RandomOraclePairedValue.readHalves, simulateQ_bind,
      simulateQ_pure,
      simulateQ_spec_query, liftPublic, simulateQ_HasQuery_query, StateT.run_bind, StateT.run_pure,
      mem_support_bind_iff, mem_support_pure_iff] at hw
    obtain ⟨low, hl, high, hh, rfl⟩ := hw
    exact read_preserves G paired _ inv _ hl hh
  | inl n =>
    simp only [QueryImpl.compose, RandomOraclePairedValue.readHalves, simulateQ_spec_query,
      liftPublic, simulateQ_HasQuery_query, G.deferredImpl_run_inl,
      CanonicalGraph.relabelImpl_run_unif,
      Functor.map_map, support_map] at hw
    obtain ⟨_, _, rfl⟩ := hw
    exact inv

/-- Forwarded private sampling and paired public queries preserve the occupied low rows. -/
theorem meteredCaller_present {α : Type} (p : OracleComp (FullWorld L F) α)
    (paired : ∀ st b, Ready G st (.inl b) → Ready G st (.inr b))
    (st : DeferredState L H X K) (old : PresentTogether st)
    (z) (hz : z ∈ support ((simulateQ G.deferredImpl (meteredCaller e p)).run st)) :
    PresentTogether z.2 := by
  unfold meteredCaller at hz
  rw [← QueryImpl.simulateQ_compose liftPublic (RandomOraclePairedValue.readHalves e),
    ← QueryImpl.simulateQ_compose] at hz
  exact simulateQ_run_preservesInv _ _ (caller_preserves_presence G e paired) _ st old _ hz

end CanonicalGraph.PairedQueries
