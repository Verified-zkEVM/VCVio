/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.MarkedReplies.Registration
public import VCVio.OracleComp.QueryTracking.RandomOracle.CachePartial.Cost
public import VCVio.OracleComp.QueryTracking.WriterCost.StateT
public import VCVio.OracleComp.SimSemantics.StateT.PreservesInv

/-!
# Charging active-target queries to the original public hash calls

Every public operation counts once, including a repeated lookup in a warm cache.
Private sampling and target registrations have zero cost.
-/

public section

open OracleSpec OracleComp
open scoped ENNReal

namespace randomOracle.Targets

variable {ι K V Notice α : Type} {pub : OracleSpec ι}

/-- Count an original public query when it is issued. -/
@[expose] def publicCost : (Queries pub Notice).Domain → Nat
  | .inl (.inr _) => 1
  | _ => 0

variable [DecidableEq ι] [DecidableEq V] [∀ t, SampleableType (pub.Range t)]
  (register : Register pub Notice K V) (role : ι → Option K) (project : ∀ t, pub.Range t → V)

/-- Count all original public queries alongside the fresh queries that have a target. -/
@[expose] noncomputable def counted :
    QueryImpl (Queries pub Notice) (StateT (State pub K V × Nat) ProbComp) :=
  (impl register role project).extendState fun t _ _ _ n => n + publicCost t

private theorem paid_step (t : (Queries pub Notice).Domain) (s : State pub K V)
    {z : (Queries pub Notice).Range t × State pub K V}
    (hz : z ∈ support ((impl register role project t).run s)) :
    z.2.paid ≤ s.paid + publicCost t := by
  rcases t with (i | t) | n
  · change z ∈ support ((fun w => (w, s)) <$> _) at hz
    rw [support_map] at hz
    obtain ⟨_, _, rfl⟩ := hz
    exact Nat.le_refl _
  · rw [public_run, support_map] at hz
    obtain ⟨w, _, rfl⟩ := hz
    unfold update
    split
    · exact Nat.le_succ _
    · split
      · exact Nat.le_succ _
      · exact le_rfl
  · change z ∈ support (pure _) at hz
    rw [mem_support_pure_iff] at hz
    subst z
    exact Nat.le_refl _

/-- On every supported execution, fresh watched queries consume at most the total physical calls. -/
theorem paid_le_count (caller : OracleComp (Queries pub Notice) α) (s : State pub K V) (n : Nat)
    (initial : s.paid ≤ n) {z} (hz : z ∈ support ((simulateQ
      (counted register role project) caller).run (s, n))) : z.2.1.paid ≤ z.2.2 := by
  apply simulateQ_run_preservesInv _ (fun st : State pub K V × Nat => st.1.paid ≤ st.2) _ caller
    (s, n) initial z hz
  intro t st hst y hy
  obtain ⟨base, cost⟩ := (QueryImpl.mem_support_extendState_run_iff _ _ _ _ _).mp hy
  rw [cost]
  exact (paid_step register role project t st.1 base).trans (Nat.add_le_add_right hst _)

/-- Charge each public call once, including a warm query. -/
@[expose] def hashCost : (unifSpec + pub).Domain → Nat
  | .inl _ => 0
  | .inr _ => 1

/-- The ordinary random oracle, with one unit charged for each public operation. -/
@[expose] noncomputable def publicMeter :
    QueryImpl (unifSpec + pub) (StateT (pub.QueryCache × Nat) ProbComp) :=
  (unifFwdImpl pub + pub.randomOracle).extendState fun t _ _ _ n => n + hashCost (pub := pub) t

/-- The ordinary public meter agrees with charging the original lazy oracle before cache lookup. -/
theorem publicMeter_run (body : OracleComp (unifSpec + pub) α) (c : pub.QueryCache) (n : Nat) :
    (simulateQ publicMeter body).run (c, n) =
      (fun z => (z.1.1, (z.2, n + z.1.2))) <$>
        (simulateQ ((unifFwdImpl pub + pub.randomOracle).withAddCost
          (hashCost (pub := pub))) body).runAdd.run c := by
  unfold publicMeter
  simpa only [QueryImpl.simulateQ_withAddCost_runAdd_fusion] using
    (run_withAddCost_eq_extendState (hashCost (pub := pub)) body
      (unifFwdImpl pub + pub.randomOracle) c n).symm

/-- Erasing notices preserves the caller's value, final cache and full public query count. -/
theorem counted_forget_run (caller : OracleComp (Queries pub Notice) α) (s : State pub K V)
    (n : Nat) :
    (fun z => (z.1, (z.2.1.cache, z.2.2))) <$>
        (simulateQ (counted register role project) caller).run (s, n) =
      (simulateQ publicMeter (simulateQ forget caller)).run (s.cache, n) := by
  rw [← QueryImpl.simulateQ_compose]
  apply map_run_simulateQ_eq_of_query_map_eq (proj := fun st : State pub K V × Nat =>
    (st.1.cache, st.2))
  intro input st
  rcases st with ⟨s, n⟩
  cases input with
  | inr notice =>
    rw [counted, QueryImpl.extendState_apply]
    simp [impl, publicCost, QueryImpl.compose, forget, StateT.run]
    rfl
  | inl t =>
    have base := forget_run register role project
      (caller := (query (spec := Queries pub Notice) (.inl t))) s
    simp only [simulateQ_HasQuery_query, forget, simulateQ_spec_query, QueryImpl.id'_apply] at base
    rw [QueryImpl.apply_compose]
    simp only [forget, QueryImpl.id'_apply, simulateQ_spec_query]
    change _ = (publicMeter t).run (s.cache, n)
    rw [publicMeter, QueryImpl.extendState_apply, counted, QueryImpl.extendState_apply]
    simp only [bind_pure_comp, Functor.map_map, ← base]
    cases t <;> rfl

/-- The target-match bound holds when the run is capped by all its physical public calls. -/
theorem prEvent_hit_and_count (ε : ℝ≥0∞) (finite : ε ≠ ⊤) (rate : ∀ t k, role t = some k →
    ∀ v, Pr{let w ← $ᵗ (pub.Range t)}[project t w = v] ≤ ε)
    (caller : OracleComp (Queries pub Notice) α) (s : State pub K V) (clean : s.hit = false)
    (n : Nat) (initial : s.paid ≤ n) (q : Nat) :
    Pr{let z ← (simulateQ (counted register role project) caller).run (s, n)}[
      z.2.1.hit = true ∧ z.2.2 ≤ q] ≤ (q : ℝ≥0∞) * ε := by
  have bound := prEvent_hit_and_paid register role project ε finite rate caller s clean q
  have same := extendState_run_proj_eq (impl register role project)
    (fun t _ _ _ (k : Nat) => k + publicCost t) caller s n
  rw [← same, prEvent_map] at bound
  apply (prEvent_mono_of_support _ _ _ ?_).trans bound
  rintro z hz ⟨hit, cost⟩
  exact ⟨hit, (paid_le_count register role project caller s n initial hz).trans cost⟩

end randomOracle.Targets
