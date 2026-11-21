/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/
module

public import VCVio.OracleComp.QueryTracking.RandomOracle.PairedValue.GraphCost
import VCVio.OracleComp.QueryTracking.RandomOracle.PublicReplay
public import VCVio.OracleComp.QueryTracking.LoggingOracle.Core
public import VCVio.OracleComp.QueryTracking.QueryLog

/-!
# Reading back the full replies of a deferred graph caller

Each original public request observes both tagged rows.
A ready graph point gets its reply from a canonical label.
Other public rows get their reply from the ordinary cache.
A conflict is the case in which a stored ordinary row becomes a ready graph point.
-/

public section
open OracleComp OracleSpec

namespace CanonicalGraph.PairedQueries

variable {L H F X K : Type} (G : CanonicalGraph (PairedSpec L H) X K H) (e : F ≃ H × H)
  [DecidableEq L] [DecidableEq X] [DecidableEq K] [SampleableType H]

/-- A public row read in the deferred game retains its reply in every conflict-free extension. -/
theorem deferred_public_readback (row : L ⊕ L) (s : DeferredState L H X K) {z}
    (read : z ∈ support ((G.deferredImpl (.inl (.inl (.inr row)))).run s))
    (later : RelabelState (PairedSpec L H) X K H) (extendsState : z.2.1 ≤ later)
    (clean : ¬G.Conflict later) : G.merge later row = some z.1 :=
  G.merged_public_reply row s read extendsState clean

/-- Both tagged requests survive at the original key, with their order and full reply intact. -/
theorem deferred_full_readback (b : L) (s : DeferredState L H X K) {z}
    (read : z ∈ support ((simulateQ G.deferredImpl
      (simulateQ liftPublic (RandomOraclePairedValue.readHalves e (.inr b)))).run s))
    (later : RelabelState (PairedSpec L H) X K H) (extendsState : z.2.1 ≤ later)
    (clean : ¬G.Conflict later) :
    RandomOraclePairedValue.joinCache e (G.merge later) b = some z.1 := by
  simp only [RandomOraclePairedValue.readHalves, simulateQ_bind, simulateQ_pure,
    simulateQ_spec_query, liftPublic, simulateQ_HasQuery_query, StateT.run_bind, StateT.run_pure,
    mem_support_bind_iff, mem_support_pure_iff] at read
  obtain ⟨lo, hlo, hi, hhi, rfl⟩ := read
  apply (RandomOraclePairedValue.joinCache_eq_some_iff e _ _ _).2
  simp only [Equiv.apply_symm_apply]
  exact ⟨deferred_public_readback G (.inl b) s hlo later
    ((G.le_of_mem_support_deferredImpl hhi).trans extendsState) clean,
    deferred_public_readback G (.inr b) lo.2 hhi later extendsState clean⟩

/-- Every full public reply in an adaptive caller's actual log is present in a later clean merge.
The log may contain private draws and repeated calls to the same input. -/
theorem deferred_log_readback {α : Type} (caller : OracleComp (FullWorld L F) α)
    (s : DeferredState L H X K) {z}
    (logged : z ∈ support ((simulateQ G.deferredImpl
      (simulateQ (QueryImpl.compose liftPublic (RandomOraclePairedValue.readHalves e))
        (simulateQ loggingOracle caller).run)).run s))
    (later : RelabelState (PairedSpec L H) X K H) (extendsState : z.2.1 ≤ later)
    (clean : ¬G.Conflict later) :
    ∀ (entry : (t : (FullWorld L F).Domain) × (FullWorld L F).Range t), entry ∈ z.1.2 →
      match entry with
      | ⟨.inl _, _⟩ => True
      | ⟨.inr key, v⟩ => RandomOraclePairedValue.joinCache e (G.merge later) key = some v := by
  induction caller using OracleComp.inductionOn generalizing s z with
  | pure x =>
    simp only [simulateQ_pure, WriterT.run_pure, StateT.run_pure, mem_support_pure_iff] at logged
    subst z
    simp
  | query_bind t next ih =>
    rw [run_simulateQ_loggingOracle_query_bind] at logged
    simp only [simulateQ_bind, simulateQ_map, StateT.run_bind,
      StateT.run_map, mem_support_bind_iff, support_map] at logged
    obtain ⟨first, headRun, tail, tailRun, rfl⟩ := logged
    intro entry mem
    rcases mem with _ | ⟨_, occurs⟩
    · cases t with
      | inl n => trivial
      | inr key =>
        exact deferred_full_readback G e key s headRun later
          ((G.le_of_mem_support_simulateQ_deferredImpl _ tailRun).trans extendsState) clean
    · exact ih first.1 first.2 tailRun extendsState _ occurs

/-- The full words observed by the raw caller split into rows of the later graph merge. -/
theorem deferred_logged_cache_le {α : Type} (caller : OracleComp (FullWorld L F) α)
    (s : DeferredState L H X K) {z}
    (logged : z ∈ support ((simulateQ G.deferredImpl
      (simulateQ (QueryImpl.compose liftPublic (RandomOraclePairedValue.readHalves e))
        (simulateQ loggingOracle caller).run)).run s))
    (later : RelabelState (PairedSpec L H) X K H) (extendsState : z.2.1 ≤ later)
    (clean : ¬G.Conflict later) :
    RandomOraclePairedValue.splitCache e (.ofFn fun key => z.1.2.lookup? (.inr key)) ≤
      G.merge later := by
  apply (RandomOraclePairedValue.gc_splitCache_joinCache e _ _).2
  intro key word found
  have entry := z.1.2.mem_of_lookup?_eq_some (.inr key) word found
  exact deferred_log_readback G e caller s logged later extendsState clean _ entry

end CanonicalGraph.PairedQueries
