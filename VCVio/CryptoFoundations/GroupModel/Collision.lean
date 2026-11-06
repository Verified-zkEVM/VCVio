/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.Projection
public import VCVio.ProgramLogic.Relational.SimulateQ.UntilBad

/-!
Identical until a collision

Observation-based and exact equality runs differ in total variation by at most the probability
that the exact run queries distinct values with equal observations. Collision monitoring includes
zero defaults for out-of-range handles and preserves arbitrary shared game-oracle effects.
-/

public section

open OracleComp OracleSpec MeasureTheory
open OracleComp.ProgramLogic.Relational
open scoped ENNReal

namespace GroupModel

variable {F S : Type} {σ : Sig S} {V U W : S → Type}

/-- An equality query compares distinct values with equal observations. -/
@[expose] def IsCollision [∀ s, Zero (V s)] (obs : (s : S) → V s → U s)
    (tbl : Tbl V) : Query F σ → Prop
  | .eq s a b => lookup tbl s a ≠ lookup tbl s b ∧
      obs s (lookup tbl s a) = obs s (lookup tbl s b)
  | _ => False

/-- Collision detection is decidable from value and observation equality. -/
instance instDecidableIsCollision [∀ s, Zero (V s)] [∀ s, DecidableEq (V s)]
    [∀ s, DecidableEq (U s)] (obs : (s : S) → V s → U s) (tbl : Tbl V)
    (q : Query F σ) : Decidable (IsCollision obs tbl q) := by
  cases q <;> unfold IsCollision <;> infer_instance

/-- Monitor a group handler, retaining any collision detected in its input table. -/
@[expose] def flagHandler [∀ s, Zero (V s)] [∀ s, DecidableEq (V s)]
    [∀ s, DecidableEq (U s)] (obs : (s : S) → V s → U s)
    {m : Type → Type} [Monad m] (handler : QueryImpl (spec F σ) (StateT (Tbl V) m)) :
    QueryImpl (spec F σ) (StateT (Tbl V × Bool) m) :=
  handler.extendState fun q tbl _ _ flag => flag || decide (IsCollision obs tbl q)

/-- Lift a game handler to the flagged table, preserving the flag. -/
@[expose] def liftGameFlag {m : Type → Type} [Monad m] {ι : Type} {Γ : OracleSpec ι}
    (game : QueryImpl Γ (StateT (Tbl V) m)) : QueryImpl Γ (StateT (Tbl V × Bool) m) :=
  game.extendState fun _ _ _ _ flag => flag

private theorem flagHandler_mono [∀ s, Zero (V s)] [∀ s, DecidableEq (V s)]
    [∀ s, DecidableEq (U s)] {ι' : Type} {spec' : OracleSpec ι'}
    (obs : (s : S) → V s → U s)
    (handler : QueryImpl (spec F σ) (StateT (Tbl V) (OracleComp spec')))
    (q : Query F σ) (st : Tbl V × Bool) (h : st.2 = true)
    (z : (spec F σ).Range q × Tbl V × Bool)
    (hz : z ∈ support ((flagHandler obs handler q).run st)) : z.2.2 = true := by
  rw [flagHandler, QueryImpl.mem_support_extendState_run_iff] at hz
  simp_all

section Model

variable [CommSemiring F] [DecidableEq S]
  [∀ s, AddCommMonoid (V s)] [∀ s, Module F (V s)]
  [∀ s, DecidableEq (V s)] [∀ s, DecidableEq (U s)]

/-- The observation-based group handler with a persistent collision flag. -/
@[expose] def implFlag (M : Model F σ V) (obs : (s : S) → V s → U s)
    (m : Type → Type) [Monad m] : QueryImpl (spec F σ) (StateT (Tbl V × Bool) m) :=
  flagHandler obs (impl M obs m)

/-- Forgetting the collision flag recovers the observation-based handler. -/
theorem implFlag_project (M : Model F σ V) (obs : (s : S) → V s → U s)
    (m : Type → Type) [Monad m] [LawfulMonad m] (q : Query F σ) (st : Tbl V × Bool) :
    Prod.map id Prod.fst <$> (implFlag M obs m q).run st = (impl M obs m q).run st.1 := by
  simp [implFlag, flagHandler]

/-- Run with equality determined by `cmp`, monitoring collisions under `obs`.
The shared game handler acts on the table and preserves the collision flag. -/
@[expose] def runFlag [∀ s, DecidableEq (W s)]
    (M : Model F σ V) (obs : (s : S) → V s → U s) (cmp : (s : S) → V s → W s)
    {m : Type → Type} [Monad m] {ι : Type} {Γ : OracleSpec ι}
    (game : QueryImpl Γ (StateT (Tbl V) m)) {α : Type}
    (oa : OracleComp (spec F σ + Γ) α) (st : Tbl V × Bool) : m (α × Tbl V × Bool) :=
  (simulateQ (flagHandler obs (impl M cmp m) + liftGameFlag game) oa).run st

/-- Forgetting the flag in a monitored run recovers its underlying table run. -/
theorem runFlag_project [∀ s, DecidableEq (W s)]
    (M : Model F σ V) (obs : (s : S) → V s → U s) (cmp : (s : S) → V s → W s)
    {m : Type → Type} [Monad m] [LawfulMonad m] {ι : Type} {Γ : OracleSpec ι}
    (game : QueryImpl Γ (StateT (Tbl V) m)) {α : Type}
    (oa : OracleComp (spec F σ + Γ) α) (st : Tbl V × Bool) :
    Prod.map id Prod.fst <$> runFlag M obs cmp game oa st = run M cmp game oa st.1 := by
  apply map_run_simulateQ_eq_of_query_map_eq
  intro q st
  cases q <;> simp [flagHandler, liftGameFlag]

/-- Probability that the exact-comparison run encounters an observation collision. -/
@[expose] noncomputable def collisionProb (M : Model F σ V) (obs : (s : S) → V s → U s)
    {ι ι' : Type} {Γ : OracleSpec ι} {spec' : OracleSpec ι'} [AnswerMeasure spec']
    (game : QueryImpl Γ (StateT (Tbl V) (OracleComp spec'))) {α : Type}
    (oa : OracleComp (spec F σ + Γ) α) (tbl : Tbl V) : ℝ≥0∞ :=
  Pr{let z ← runFlag M obs (fun _ => id) game oa (tbl, false)}[z.2.2 = true]

private theorem flagHandler_agree {ι' : Type} {spec' : OracleSpec ι'} [AnswerMeasure spec']
    (M : Model F σ V) (obs : (s : S) → V s → U s) (q : Query F σ)
    (st : Tbl V × Bool) (p : (spec F σ).Range q × Tbl V × Bool → Prop) :
    Pr{let z ← (flagHandler obs (impl M (fun _ => id) (OracleComp spec')) q).run st}[
        p z ∧ ¬z.2.2 = true] =
    Pr{let z ← (implFlag M obs (OracleComp spec') q).run st}[p z ∧ ¬z.2.2 = true] := by
  cases q with
  | eq s a b =>
    by_cases he : lookup st.1 s a = lookup st.1 s b
    · simp [implFlag, flagHandler, impl, IsCollision, he]
    · by_cases ho : obs s (lookup st.1 s a) = obs s (lookup st.1 s b)
      · simp [implFlag, flagHandler, impl, IsCollision, he, ho]
      · simp [implFlag, flagHandler, impl, IsCollision, he, ho]
  | _ => rfl

/-- **Identical until a collision (L2).** The total variation of observation-based and exact
runs is bounded by the collision probability in the exact run, with the same game handler. -/
theorem measureETVDist_run_le_collisionProb
    (M : Model F σ V) (obs : (s : S) → V s → U s)
    {ι ι' : Type} {Γ : OracleSpec ι} {spec' : OracleSpec ι'} [AnswerMeasure spec']
    (game : QueryImpl Γ (StateT (Tbl V) (OracleComp spec'))) {α : Type}
    [MeasurableSpace (α × Tbl V)] (oa : OracleComp (spec F σ + Γ) α) (tbl : Tbl V) :
    measureETVDist (run M obs game oa tbl) (run M (fun _ => id) game oa tbl) ≤
      collisionProb M obs game oa tbl := by
  let h₁ := flagHandler obs (impl M (fun _ => id) (OracleComp spec')) + liftGameFlag game
  let h₂ := implFlag M obs (OracleComp spec') + liftGameFlag game
  have hmono {W : S → Type} [∀ s, DecidableEq (W s)] (cmp : (s : S) → V s → W s) :
      ∀ q st, st.2 = true → ∀ z ∈ support
        (((flagHandler obs (impl M cmp (OracleComp spec')) + liftGameFlag game) q).run st),
        z.2.2 = true := by
    intro q st hs z hz
    cases q with
    | inl q => exact flagHandler_mono obs _ q st hs z hz
    | inr q =>
      simp only [QueryImpl.add_apply_inr, liftGameFlag,
        QueryImpl.mem_support_extendState_run_iff] at hz
      exact hz.2.trans hs
  have hagree : ∀ q st, ¬st.2 = true →
      ∀ p : (spec F σ + Γ).Range q × Tbl V × Bool → Prop,
      Pr{let z ← (h₁ q).run st}[p z ∧ ¬z.2.2 = true] =
      Pr{let z ← (h₂ q).run st}[p z ∧ ¬z.2.2 = true] := by
    intro q st _ p
    cases q with
    | inl q => exact flagHandler_agree M obs q st p
    | inr q => rfl
  have h := measureETVDist_map_le_prEvent_of_agree
    ((simulateQ h₁ oa).run (tbl, false)) ((simulateQ h₂ oa).run (tbl, false))
    (Prod.map id Prod.fst) (fun z => z.2.2 = true)
    (prEvent_simulateQ_run_and_not_bad_eq h₁ h₂ (fun st => st.2 = true) hagree
      (hmono (fun _ => id)) (hmono obs) oa (tbl, false))
    (prEvent_simulateQ_run_bad_eq h₁ h₂ (fun st => st.2 = true) hagree
      (hmono (fun _ => id)) (hmono obs) oa (tbl, false)).ge
  change measureETVDist (Prod.map id Prod.fst <$> runFlag M obs (fun _ => id) game oa _)
    (Prod.map id Prod.fst <$> runFlag M obs obs game oa _) ≤ _ at h
  rw [runFlag_project, runFlag_project, measureETVDist_comm] at h
  exact h

/-- Each measurable event differs in probability by at most the exact-run collision
probability, in both directions. -/
theorem prEvent_run_le_add_collisionProb
    (M : Model F σ V) (obs : (s : S) → V s → U s)
    {ι ι' : Type} {Γ : OracleSpec ι} {spec' : OracleSpec ι'} [AnswerMeasure spec']
    (game : QueryImpl Γ (StateT (Tbl V) (OracleComp spec'))) {α : Type}
    [MeasurableSpace (α × Tbl V)] (oa : OracleComp (spec F σ + Γ) α) (tbl : Tbl V)
    (E : Set (α × Tbl V)) (hE : MeasurableSet E) :
    (Pr{let z ← run M obs game oa tbl}[z ∈ E] ≤
      Pr{let z ← run M (fun _ => id) game oa tbl}[z ∈ E] + collisionProb M obs game oa tbl) ∧
    (Pr{let z ← run M (fun _ => id) game oa tbl}[z ∈ E] ≤
      Pr{let z ← run M obs game oa tbl}[z ∈ E] + collisionProb M obs game oa tbl) := by
  have h := measureETVDist_run_le_collisionProb M obs game oa tbl
  constructor
  · exact (prEvent_le_prEvent_add_measureETVDist
      (run M obs game oa tbl) (run M (fun _ => id) game oa tbl) (· ∈ E) hE.mem).trans
      (add_le_add le_rfl h)
  · have h' := h
    rw [measureETVDist_comm] at h'
    exact (prEvent_le_prEvent_add_measureETVDist
      (run M (fun _ => id) game oa tbl) (run M obs game oa tbl) (· ∈ E) hE.mem).trans
      (add_le_add le_rfl h')

/-- Collision probability for a generic run with uniform sampling. -/
@[expose] noncomputable def collisionProbGen
    (M : Model F σ V) (obs : (s : S) → V s → U s) {α : Type}
    (oa : OracleComp (genSpec F σ) α) (tbl : Tbl V) : ℝ≥0∞ :=
  collisionProb M obs
    ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (Tbl V) ProbComp)) oa tbl

/-- The generic observation run is within the exact generic run's collision probability
in total variation. -/
theorem measureETVDist_runGen_le_collisionProbGen
    (M : Model F σ V) (obs : (s : S) → V s → U s) {α : Type}
    [MeasurableSpace (α × Tbl V)] (oa : OracleComp (genSpec F σ) α) (tbl : Tbl V) :
    measureETVDist (runGen M obs oa tbl) (runGen M (fun _ => id) oa tbl) ≤
      collisionProbGen M obs oa tbl :=
  measureETVDist_run_le_collisionProb M obs _ oa tbl

end Model

end GroupModel
