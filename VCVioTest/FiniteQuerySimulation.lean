/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import VCVio.OracleComp.QueryTracking.QueryBound.FinMOfFn
public import VCVio.OracleComp.QueryTracking.QueryBound.Simulation
public import VCVio.OracleComp.QueryTracking.RandomOracle.CachePartial
public import VCVio.OracleComp.QueryTracking.RandomOracle.FinMOfFn
public import VCVio.ProgramLogic.Relational.Basic

/-!
# Finite sequencing, simulation costs and cache observations

These controls distinguish issued prefixes from completed paths, charge two target calls per
charged source call while retaining state changes on free calls, and retain both cached values
and the state relation in projected observations.
-/

public section

open OracleComp OracleSpec OracleComp.ProgramLogic.Relational

namespace VCVioTest.FiniteQuerySimulation

/-- Boolean source indices have a unique answer. -/
abbrev sourceSpec : OracleSpec Bool := fun _ => Unit
/-- Every target query has a unique index and answer. -/
abbrev targetSpec : OracleSpec Unit := fun _ => Unit
/-- The sole source query has no answer. -/
abbrev unansweredSpec : OracleSpec Unit := fun _ => Empty

/-- Charged steps issue two target queries; every step advances the state. -/
@[expose] def weightedStep : QueryImpl sourceSpec (StateT ℕ (OracleComp targetSpec)) :=
  fun charged => StateT.mk fun state =>
    if charged then do
      let _ ← liftM (targetSpec.query ())
      let _ ← liftM (targetSpec.query ())
      pure ((), state + 1)
    else pure ((), state + 1)

/-- Two charged source calls enclose a free source call. -/
@[expose] def chargedFreeCharged : OracleComp sourceSpec Unit := do
  let _ ← liftM (sourceSpec.query true)
  let _ ← liftM (sourceSpec.query false)
  liftM (sourceSpec.query true)

/-- A free source step can still change state; the two charged steps cost four target calls. -/
theorem weighted_cost (state : ℕ) :
    IsQueryBoundP ((simulateQ weightedStep chargedFreeCharged).run state) (fun _ => True) 4 := by
  apply IsQueryBoundP.simulateQ_run_of_step_le (n := 2) (cost := 2)
    (p := (· = true))
  · simp [chargedFreeCharged]
  · intro t ht s
    subst t
    simp [weightedStep]
  · intro t ht s
    cases t <;> simp_all [weightedStep]

/-- The free middle call advances state as well, despite consuming no target query budget. -/
theorem weighted_state (state : ℕ) (z : Unit × ℕ)
    (hz : z ∈ support ((simulateQ weightedStep chargedFreeCharged).run state)) :
    z.2 = state + 3 := by
  have heq : z = ((), state + 3) := by
    simpa [weightedStep, chargedFreeCharged, StateT.run_bind, Nat.add_assoc] using hz
  exact congrArg Prod.snd heq

/-- The empty family makes no query, independently of the requested component bound. -/
theorem empty_family (f : Fin 0 → OracleComp sourceSpec Unit) :
    IsTotalQueryBound (Fin.mOfFn 0 f) 0 := by
  simpa using isTotalQueryBound_fin_mOfFn (k := 7) f (fun i => i.elim0)

/-- An unanswerable issued query still consumes its structural prefix budget. -/
theorem empty_answer_prefix : IsTotalQueryBound
    (Fin.mOfFn 1 fun _ =>
      (liftM (unansweredSpec.query ()) : OracleComp unansweredSpec Empty)) 1 := by
  simpa using isTotalQueryBound_fin_mOfFn (n := 1) (k := 1)
    (fun _ => (liftM (unansweredSpec.query ()) : OracleComp unansweredSpec Empty))
    (by simp [IsTotalQueryBound])

/-- Empty successful support cannot justify a zero budget for an issued query. -/
theorem empty_answer_not_zero : ¬ IsTotalQueryBound
    (Fin.mOfFn 1 fun _ =>
      (liftM (unansweredSpec.query ()) : OracleComp unansweredSpec Empty)) 0 := by
  simp [Fin.mOfFn, IsTotalQueryBound]

/-- A fresh pair of distinct keys has the exact ordered two-draw program. -/
theorem fresh_pair :
    (simulateQ (randomOracle (spec := Bool →ₒ Bool))
      (Fin.mOfFn 2 fun i => (liftM ((Bool →ₒ Bool).query (decide (i = 1))) :
        OracleComp (Bool →ₒ Bool) Bool))).run' ∅ =
      Fin.mOfFn 2 (fun _ => ($ᵗ Bool)) := by
  apply run'_fin_mOfFn_randomOracle_of_fresh
  · decide
  · simp

/-- Repeated queries at another key and private draws preserve an already populated cell. -/
theorem populated_cache_frame {oa : OracleComp (unifSpec + (Bool →ₒ Bool)) Unit}
    (havoid : AllQueriesSatisfy oa (Sum.elim (fun _ => True) (· ≠ false)))
    {cache : (Bool →ₒ Bool).QueryCache} (hcache : cache false = some true)
    {z : Unit × (Bool →ₒ Bool).QueryCache}
    (hz : z ∈ support ((simulateQ (Bool →ₒ Bool).romImpl oa).run cache)) :
    z.2 false = some true :=
  (snd_apply_eq_of_mem_support_run_romImpl false havoid hz).trans hcache

/-- Projecting away bookkeeping retains the support invariant and every optional output,
including a returned `none`, in the coupling of the original distributions. -/
theorem projected_coupling (source : ProbComp (Option Bool × (ℕ × ℕ)))
    (hinv : ∀ result ∈ support source, result.2.1 ≤ result.2.2) :
    RelTriple source (Prod.map id Prod.fst <$> source)
      (fun left right => left.1 = right.1 ∧ right.2 ≤ left.2.2) := by
  exact relTriple_of_projected_eq source _ Prod.fst (fun full projected => projected ≤ full.2)
    EvalDistEq.rfl hinv

end VCVioTest.FiniteQuerySimulation
