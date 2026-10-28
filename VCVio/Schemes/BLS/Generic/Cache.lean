/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.Schemes.BLS.Generic.ReductionPrograms
public import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
public import VCVio.OracleComp.SimSemantics.StateT.StateProjection
import all VCVio.Schemes.BLS.Generic.ReductionPrograms

/-! # Commuting the private scalar cache with real group interpretation

The group table and private scalar cache are disjoint state. Interpreting group queries before
or after closing the scalar oracle yields the same program, with the same cache and group table.
-/

public section

open OracleComp OracleSpec GroupModel

namespace BLS.Generic

variable {F M R α : Type} {V U : PSort → Type}

attribute [local implicit_reducible] spec

/-- The real group interpreter with ordinary private coins. -/
@[expose] def realImpl [CommSemiring F]
    [∀ s, AddCommMonoid (V s)] [∀ s, Module F (V s)] [∀ s, DecidableEq (U s)]
    (model : Model F pairingSig V) (obs : (s : PSort) → V s → U s) :
    QueryImpl (genSpec F pairingSig) (StateT (Tbl V) ProbComp) :=
  impl model obs ProbComp +
    (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (Tbl V) ProbComp)

/-- Interpret group queries while forwarding coins and private scalar lookups. -/
@[expose] def openImpl [CommSemiring F]
    [∀ s, AddCommMonoid (V s)] [∀ s, Module F (V s)] [∀ s, DecidableEq (U s)]
    (model : Model F pairingSig V) (obs : (s : PSort) → V s → U s) :
    QueryImpl (reductionSpec F M R) (StateT (Tbl V) (OracleComp (unifSpec + (M →ₒ R)))) :=
  impl model obs (OracleComp (unifSpec + (M →ₒ R))) +
    (QueryImpl.ofLift (unifSpec + (M →ₒ R)) (OracleComp (unifSpec + (M →ₒ R)))).liftTarget
      (StateT (Tbl V) (OracleComp (unifSpec + (M →ₒ R))))

private theorem realImpl_liftM [CommSemiring F]
    [∀ s, AddCommMonoid (V s)] [∀ s, Module F (V s)] [∀ s, DecidableEq (U s)]
    (model : Model F pairingSig V) (obs : (s : PSort) → V s → U s)
    (oa : ProbComp α) (tbl : Tbl V) :
    (simulateQ (realImpl model obs) (liftM oa : OracleComp (genSpec F pairingSig) α)).run tbl =
      (fun a => (a, tbl)) <$> oa := by
  simp only [realImpl, QueryImpl.simulateQ_add_liftM_right, simulateQ_liftTarget]
  simp

private theorem openImpl_reductionLift_step [CommSemiring F]
    [∀ s, AddCommMonoid (V s)] [∀ s, Module F (V s)] [∀ s, DecidableEq (U s)]
    (model : Model F pairingSig V) (obs : (s : PSort) → V s → U s)
    (q : (genSpec F pairingSig).Domain) (tbl : Tbl V) :
    (simulateQ (openImpl (M := M) (R := R) model obs) (reductionLift q)).run tbl =
      liftM ((realImpl model obs q).run tbl) := by
  rcases q with q | n
  · cases q <;> simp [reductionLift, openImpl, realImpl, impl, push] <;> rfl
  · simp [reductionLift, openImpl, realImpl]
    rfl

/-- Interpreting a lifted generic program forwards its coins to the scalar interface. -/
theorem openImpl_reductionLift [CommSemiring F]
    [∀ s, AddCommMonoid (V s)] [∀ s, Module F (V s)] [∀ s, DecidableEq (U s)]
    (model : Model F pairingSig V) (obs : (s : PSort) → V s → U s)
    (program : OracleComp (genSpec F pairingSig) α) (tbl : Tbl V) :
    (simulateQ (openImpl (M := M) (R := R) model obs)
      (simulateQ reductionLift program)).run tbl =
      liftM (runGen model obs program tbl) := by
  induction program using OracleComp.inductionOn generalizing tbl with
  | pure a => simp [runGen, run]
  | query_bind q next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, runGen_bind, liftM_bind]
    rw [openImpl_reductionLift_step]
    have hq : runGen model obs (liftM ((genSpec F pairingSig).query q)) tbl =
        (realImpl model obs q).run tbl := by simp [runGen, run, realImpl]
    rw [hq]
    apply bind_congr
    intro z
    exact ih z.1 z.2

/-- Interpreting a private scalar computation only threads the group table unchanged. -/
theorem openImpl_scalar [CommSemiring F]
    [∀ s, AddCommMonoid (V s)] [∀ s, Module F (V s)] [∀ s, DecidableEq (U s)]
    (model : Model F pairingSig V) (obs : (s : PSort) → V s → U s)
    (program : OracleComp (unifSpec + (M →ₒ R)) α) (tbl : Tbl V) :
    (simulateQ (openImpl model obs)
      (simulateQ (fun q => ((reductionSpec F M R).query (.inr q) :
        OracleComp (reductionSpec F M R) _)) program)).run tbl =
      (fun a => (a, tbl)) <$> program := by
  induction program using OracleComp.inductionOn generalizing tbl with
  | pure a => simp
  | query_bind q next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
      simp only [openImpl, QueryImpl.add_apply_inr, QueryImpl.liftTarget_apply,
        QueryImpl.ofLift_apply, liftM_run_StateT, bind_assoc, pure_bind]
      apply bind_congr
      intro a
      exact ih a tbl

/-- Private randomness passes through the open interpreter without changing the group table. -/
theorem openImpl_liftM [CommSemiring F]
    [∀ s, AddCommMonoid (V s)] [∀ s, Module F (V s)] [∀ s, DecidableEq (U s)]
    (model : Model F pairingSig V) (obs : (s : PSort) → V s → U s)
    (program : ProbComp α) (tbl : Tbl V) :
    (simulateQ (openImpl (M := M) (R := R) model obs)
      (liftM program : OracleComp (reductionSpec F M R) α)).run tbl =
      (fun a => (a, tbl)) <$> (liftM program : OracleComp (unifSpec + (M →ₒ R)) α) := by
  rw [QueryImpl.simulateQ_liftM_eq_of_query _
    ((QueryImpl.ofLift unifSpec (OracleComp (unifSpec + (M →ₒ R)))).liftTarget _)
    (by intro n; simp [openImpl]; rfl)]
  simp only [simulateQ_liftTarget, liftM_run_StateT, bind_pure_comp]
  congr 1

/-- The open interpreter allocates a scalar multiple at the next handle of its sort. -/
theorem openImpl_smul [CommSemiring F]
    [∀ s, AddCommMonoid (V s)] [∀ s, Module F (V s)] [∀ s, DecidableEq (U s)]
    (model : Model F pairingSig V) (obs : (s : PSort) → V s → U s)
    (s : PSort) (c : F) (h : Handle) (tbl : Tbl V) :
    (simulateQ (openImpl (M := M) (R := R) model obs)
      (liftM ((reductionSpec F M R).query (.inl (.smul s c h))))).run tbl =
      pure ((tbl s).length, append tbl s (c • lookup tbl s h)) := by
  simp [openImpl, impl, push, StateT.run, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet]

private theorem cache_step [CommSemiring F] [DecidableEq M] [SampleableType R]
    [∀ s, AddCommMonoid (V s)] [∀ s, Module F (V s)] [∀ s, DecidableEq (U s)]
    (model : Model F pairingSig V) (obs : (s : PSort) → V s → U s)
    (q : (reductionSpec F M R).Domain) (c : (M →ₒ R).QueryCache) (tbl : Tbl V) :
    Prod.map id Prod.swap <$>
      (((realImpl model obs).mapStateTBase reductionCache).flattenStateT q).run (c, tbl) =
    (QueryImpl.parallelStateT (impl model obs ProbComp) (M →ₒ R).romImpl q).run (tbl, c) := by
  simp only [QueryImpl.flattenStateT_mapStateTBase_apply_run]
  rcases q with q | n | m
  · cases q <;>
      simp [reductionCache, realImpl,
        QueryImpl.parallelStateT, impl, push, Prod.map, Prod.swap] <;> rfl
  · simp [reductionCache, realImpl,
      QueryImpl.parallelStateT, Prod.map, Prod.swap, unifFwdImpl]
    rfl
  · change Prod.map id Prod.swap <$> ((fun y => (y.1.1, y.1.2, y.2)) <$>
        (simulateQ (realImpl model obs)
          (liftM (((M →ₒ R).randomOracle m).run c))).run tbl) = _
    rw [realImpl_liftM]
    simp only [Functor.map_map, QueryImpl.parallelStateT, StateT.run_mk,
      OracleSpec.romImpl_apply_inr]
    rfl

private theorem open_step [CommSemiring F] [DecidableEq M] [SampleableType R]
    [∀ s, AddCommMonoid (V s)] [∀ s, Module F (V s)] [∀ s, DecidableEq (U s)]
    (model : Model F pairingSig V) (obs : (s : PSort) → V s → U s)
    (q : (reductionSpec F M R).Domain) (tbl : Tbl V) (c : (M →ₒ R).QueryCache) :
    (((M →ₒ R).romImpl.mapStateTBase (openImpl model obs)).flattenStateT q).run (tbl, c) =
      (QueryImpl.parallelStateT (impl model obs ProbComp) (M →ₒ R).romImpl q).run (tbl, c) := by
  simp only [QueryImpl.flattenStateT_mapStateTBase_apply_run]
  rcases q with q | q
  · cases q <;>
      simp [openImpl,
        QueryImpl.parallelStateT, impl, push] <;> rfl
  · simp [openImpl,
      QueryImpl.parallelStateT]
    rfl

/-- Closing the scalar oracle commutes with real group interpretation, retaining both states. -/
theorem run_reductionCache [CommSemiring F] [DecidableEq M] [SampleableType R]
    [∀ s, AddCommMonoid (V s)] [∀ s, Module F (V s)] [∀ s, DecidableEq (U s)]
    (model : Model F pairingSig V) (obs : (s : PSort) → V s → U s)
    (program : OracleComp (reductionSpec F M R) α)
    (c : (M →ₒ R).QueryCache) (tbl : Tbl V) :
    (fun z => (z.1.1, z.2, z.1.2)) <$>
        runGen model obs ((simulateQ reductionCache program).run c) tbl =
      (fun z => (z.1.1, z.1.2, z.2)) <$>
        (simulateQ (M →ₒ R).romImpl
          ((simulateQ (openImpl model obs) program).run tbl)).run c := by
  have h := map_run_simulateQ_eq_of_query_map_eq
    ((realImpl model obs).mapStateTBase reductionCache).flattenStateT
    (QueryImpl.parallelStateT (impl model obs ProbComp) (M →ₒ R).romImpl)
    Prod.swap (fun q st => cache_step model obs q st.1 st.2) program (c, tbl)
  have hopen : ((M →ₒ R).romImpl.mapStateTBase (openImpl model obs)).flattenStateT =
      QueryImpl.parallelStateT (impl model obs ProbComp) (M →ₒ R).romImpl := by
    funext q st
    exact open_step model obs q st.1 st.2
  rw [← hopen] at h
  simpa only [simulateQ_flattenStateT_run, ← QueryImpl.simulateQ_mapStateTBase_run,
    bind_pure_comp, Functor.map_map, Function.comp_def, Prod.map, id_eq, Prod.swap,
    runGen, run, realImpl] using h

/-- Real interpretation of a closed program equals the ROM interpretation of its open run. -/
theorem run_closeReduction [CommSemiring F] [DecidableEq M] [SampleableType R]
    [∀ s, AddCommMonoid (V s)] [∀ s, Module F (V s)] [∀ s, DecidableEq (U s)]
    (model : Model F pairingSig V) (obs : (s : PSort) → V s → U s)
    (program : OracleComp (reductionSpec F M R) α) (tbl : Tbl V) :
    Prod.fst <$> runGen model obs (closeReduction program) tbl =
      (simulateQ (M →ₒ R).romImpl
        ((simulateQ (openImpl model obs) program).run' tbl)).run' ∅ := by
  have h := congrArg (fun p => Prod.fst <$> p) (run_reductionCache model obs program ∅ tbl)
  simpa only [closeReduction, StateT.run'_eq, runGen, run, simulateQ_map,
    StateT.run_map, Functor.map_map, Function.comp_def] using h

end BLS.Generic
