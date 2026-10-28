/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.Rewinding.Basic
public import VCVio.OracleComp.QueryTracking.RandomOracle.Commute

/-!
# Reset policies for persistent and stateless oracles

A persistent oracle has no execution-local cursor: its entire state records already frozen
answers. Lazy random-oracle tables give a persistent policy, while deterministic stateless
oracles give the trivial policy.
-/

public section

open OracleComp OracleSpec

namespace Rewinding.ResetPolicy

variable {ι W : Type} {spec : OracleSpec ι}

/-- Add a unit cursor to a persistent oracle implementation. -/
@[expose] def persistentAnswer (impl : QueryImpl spec (StateT W ProbComp)) :
    QueryImpl spec (StateT (W × Unit) ProbComp) :=
  fun q => StateT.mk fun s => (fun z => (z.1, (z.2, ()))) <$> (impl q).run s.1

/-- A persistent oracle whose answers are stable under extension defines a reset policy with
no execution-local state. -/
@[expose] def persistent [Preorder W] (empty : W)
    (impl : QueryImpl spec (StateT W ProbComp))
    (grows : ∀ q w z, z ∈ support ((impl q).run w) → w ≤ z.2)
    (frozen : ∀ q w w' z, z ∈ support ((impl q).run w) → z.2 ≤ w' →
      (impl q).run w' = pure (z.1, w'))
    (commute : ∀ q₁ q₂ w,
      (do
        let z₁ ← (impl q₁).run w
        let z₂ ← (impl q₂).run z₁.2
        pure (z₁.1, z₂.1, z₂.2)) =ᵈ
      (do
        let z₂ ← (impl q₂).run w
        let z₁ ← (impl q₁).run z₂.2
        pure (z₁.1, z₂.1, z₁.2))) :
    ResetPolicy (pure empty) impl where
  World := W
  empty := empty
  Cursor := Unit
  begin := ()
  answer := persistentAnswer impl
  faithful oa := by
    have h := OracleComp.run'_simulateQ_eq_of_query_map_eq
      (persistentAnswer impl) impl Prod.fst (by
        intro q s
        simp [persistentAnswer, Functor.map_map, Prod.map]) oa (empty, ())
    simp only [pure_bind]
    rw [h]
  faithful_coins oa := by
    have h := OracleComp.run'_simulateQ_eq_of_query_map_eq
      (coins (S := W × Unit) + persistentAnswer impl) (coins (S := W) + impl) Prod.fst (by
        intro q s
        cases q with
        | inl q => simp [QueryImpl.add_apply_inl, coins, Functor.map_map, Prod.map]
        | inr q =>
            simp [QueryImpl.add_apply_inr, persistentAnswer, Functor.map_map, Prod.map])
      oa (empty, ())
    simp only [pure_bind]
    rw [h]
  grows q w c z hz := by
    simp only [persistentAnswer, StateT.run_mk, support_map] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    exact grows q w y hy
  frozen q w w' c z hz hw := by
    simp only [persistentAnswer, StateT.run_mk, support_map] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    simp [persistentAnswer, frozen q w w' y hy hw]
  commute q₁ q₂ c₁ c₂ w := by
    simpa [persistentAnswer, bind_map_left, map_bind, Function.comp_def] using
      (commute q₁ q₂ w).map (fun z => ((z.1, ()), (z.2.1, ()), z.2.2))

/-- The reset policy for a lazily sampled random-oracle table. Repeated queries read the same
entry, and extensions only install previously missing entries. -/
@[expose] def randomOracle [DecidableEq ι]
    [∀ q : spec.Domain, SampleableType (spec.Range q)] :
    ResetPolicy (pure (∅ : spec.QueryCache)) spec.randomOracle :=
  persistent ∅ spec.randomOracle
    (fun q w z hz => QueryImpl.withCaching_cache_le _ q w z hz)
    (fun q w w' z hz hw => QueryImpl.withCaching_run_some _
      (hw (QueryImpl.withCaching_run_caches _ q w z hz)))
    (fun q₁ q₂ w => by
      let : MeasurableSpace (spec.Range q₁ × spec.Range q₂ × spec.QueryCache) := ⊤
      apply EvalDistEq.of_evalDist_eq
      exact _root_.randomOracle.evalDist_run_bind_run_swap q₁ q₂ w
        (fun a b c => pure (a, b, c)))

/-- A deterministic query handler carries no oracle state. -/
@[expose] def statelessImpl (answer : (q : spec.Domain) → spec.Range q) :
    QueryImpl spec (StateT Unit ProbComp) := fun q => pure (answer q)

/-- A deterministic stateless oracle has a trivial frozen world and cursor. -/
@[expose] def stateless (answer : (q : spec.Domain) → spec.Range q) :
    ResetPolicy (pure ()) (statelessImpl answer) :=
  persistent () (statelessImpl answer)
    (fun _ _ _ _ => le_rfl)
    (fun _ _ _ z hz _ => by
      simp only [statelessImpl, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      rfl)
    (fun _ _ _ => by simp [statelessImpl])

/-- The empty oracle signature has a reset policy with no effects. -/
@[expose] def trivial :
    ResetPolicy (pure ()) (statelessImpl (spec := emptySpec) (fun q => PEmpty.elim q)) :=
  stateless (spec := emptySpec) (fun q => PEmpty.elim q)

private def uniformInl : QueryImpl unifSpec (OracleComp (unifSpec + spec)) :=
  fun q => query (spec := unifSpec + spec) (.inl q)

private theorem simulateQ_uniformInl {σ α : Type}
    (handler : QueryImpl spec (StateT σ ProbComp)) (mx : ProbComp α) :
    simulateQ (coins (S := σ) + handler) (simulateQ (uniformInl (spec := spec)) mx) =
      (liftM mx : StateT σ ProbComp α) := by
  rw [QueryImpl.simulateQ_simulateQ_eq_of_apply
    (impl := coins (S := σ)) (by
      intro q
      simp [uniformInl, QueryImpl.add_apply_inl])]
  simp [coins]

private def stageRight {κ T : Type} {ctxSpec : OracleSpec κ}
    (ctx : QueryImpl ctxSpec (StateT T ProbComp)) :
    QueryImpl (ctxSpec + spec) (StateT T (OracleComp (unifSpec + spec)))
  | .inl q => StateT.mk fun t => simulateQ uniformInl ((ctx q).run t)
  | .inr q => StateT.mk fun t => (fun a => (a, t)) <$> query (spec := unifSpec + spec) (.inr q)

private theorem stageRight_run {κ T σ α : Type} {ctxSpec : OracleSpec κ}
    (ctx : QueryImpl ctxSpec (StateT T ProbComp))
    (handler : QueryImpl spec (StateT σ ProbComp))
    (oa : OracleComp (ctxSpec + spec) α) (t : T) (s : σ) :
    (simulateQ (coins (S := σ) + handler) ((simulateQ (stageRight ctx) oa).run t)).run s =
      (fun z : α × T × σ => ((z.1, z.2.1), z.2.2)) <$>
        (simulateQ (QueryImpl.parallelStateT ctx handler) oa).run (t, s) := by
  apply simulateQ_StateT_StateT_compose
  intro q t s
  change (simulateQ (coins (S := σ) + handler) ((stageRight ctx q).run t)).run s =
    (fun z : (ctxSpec + spec).Range q × T × σ => ((z.1, z.2.1), z.2.2)) <$>
      ((QueryImpl.parallelStateT ctx handler) q).run (t, s)
  cases q with
  | inl q =>
      simp [stageRight, simulateQ_uniformInl, QueryImpl.parallelStateT,
        StateT.run_monadLift, Functor.map_map, Prod.map]
  | inr q =>
      simp [stageRight, QueryImpl.add_apply_inr, QueryImpl.parallelStateT,
        Functor.map_map, Prod.map]

private theorem stageRight_run' {κ T σ α : Type} {ctxSpec : OracleSpec κ}
    (ctx : QueryImpl ctxSpec (StateT T ProbComp))
    (handler : QueryImpl spec (StateT σ ProbComp))
    (oa : OracleComp (ctxSpec + spec) α) (t : T) (s : σ) :
    (simulateQ (coins (S := σ) + handler)
      (Prod.fst <$> (simulateQ (stageRight ctx) oa).run t)).run' s =
        (simulateQ (QueryImpl.parallelStateT ctx handler) oa).run' (t, s) := by
  simp [StateT.run'_eq, stageRight_run, Functor.map_map]

private theorem replaceRight {κ T σ α : Type} {ctxSpec : OracleSpec κ}
    {init : ProbComp σ} {impl : QueryImpl spec (StateT σ ProbComp)}
    (P : ResetPolicy init impl) (ctx : QueryImpl ctxSpec (StateT T ProbComp))
    (oa : OracleComp (ctxSpec + spec) α) (t : T) :
    (simulateQ (QueryImpl.parallelStateT ctx P.answer) oa).run' (t, (P.empty, P.begin)) =ᵈ
      (do
        let s ← init
        (simulateQ (QueryImpl.parallelStateT ctx impl) oa).run' (t, s)) := by
  simpa only [stageRight_run', map_bind] using
    P.faithful_coins (Prod.fst <$> (simulateQ (stageRight ctx) oa).run t)

private def swapQueries {κ : Type} {ctxSpec : OracleSpec κ} :
    QueryImpl (spec + ctxSpec) (OracleComp (ctxSpec + spec))
  | .inl q => query (spec := ctxSpec + spec) (.inr q)
  | .inr q => query (spec := ctxSpec + spec) (.inl q)

private theorem parallel_swap_run' {κ T σ α : Type} {ctxSpec : OracleSpec κ}
    (handler : QueryImpl spec (StateT σ ProbComp))
    (ctx : QueryImpl ctxSpec (StateT T ProbComp))
    (oa : OracleComp (spec + ctxSpec) α) (s : σ) (t : T) :
    (simulateQ (QueryImpl.parallelStateT handler ctx) oa).run' (s, t) =
      (simulateQ (QueryImpl.parallelStateT ctx handler)
        (simulateQ swapQueries oa)).run' (t, s) := by
  rw [← QueryImpl.simulateQ_compose]
  apply OracleComp.run'_simulateQ_eq_of_query_map_eq
    (proj := Prod.swap)
  intro q z
  cases q <;>
    simp [QueryImpl.compose, swapQueries, QueryImpl.parallelStateT, Functor.map_map,
      Prod.map, Prod.swap] <;> rfl

private theorem replaceLeft {κ T σ α : Type} {ctxSpec : OracleSpec κ}
    {init : ProbComp σ} {impl : QueryImpl spec (StateT σ ProbComp)}
    (P : ResetPolicy init impl) (ctx : QueryImpl ctxSpec (StateT T ProbComp))
    (oa : OracleComp (spec + ctxSpec) α) (t : T) :
    (simulateQ (QueryImpl.parallelStateT P.answer ctx) oa).run' ((P.empty, P.begin), t) =ᵈ
      (do
        let s ← init
        (simulateQ (QueryImpl.parallelStateT impl ctx) oa).run' (s, t)) := by
  rw [parallel_swap_run' P.answer ctx oa (P.empty, P.begin) t]
  exact (replaceRight P ctx (simulateQ swapQueries oa) t).trans
    (EvalDistEq.bind_right init fun s => by
      rw [← parallel_swap_run' impl ctx oa s t])

private def reassocQueries {κ : Type} {ctxSpec : OracleSpec κ} :
    QueryImpl (unifSpec + (ctxSpec + spec)) (OracleComp ((unifSpec + ctxSpec) + spec))
  | .inl q => query (spec := (unifSpec + ctxSpec) + spec) (.inl (.inl q))
  | .inr (.inl q) => query (spec := (unifSpec + ctxSpec) + spec) (.inl (.inr q))
  | .inr (.inr q) => query (spec := (unifSpec + ctxSpec) + spec) (.inr q)

private theorem reassoc_run' {κ T σ α : Type} {ctxSpec : OracleSpec κ}
    (ctx : QueryImpl ctxSpec (StateT T ProbComp))
    (handler : QueryImpl spec (StateT σ ProbComp))
    (oa : OracleComp (unifSpec + (ctxSpec + spec)) α) (t : T) (s : σ) :
    (simulateQ (coins (S := T × σ) + QueryImpl.parallelStateT ctx handler) oa).run' (t, s) =
      (simulateQ (QueryImpl.parallelStateT (coins (S := T) + ctx) handler)
        (simulateQ reassocQueries oa)).run' (t, s) := by
  have h : ∀ q, simulateQ (QueryImpl.parallelStateT (coins (S := T) + ctx) handler)
      (reassocQueries q) = (coins (S := T × σ) + QueryImpl.parallelStateT ctx handler) q := by
    intro q
    rcases q with q | (q | q) <;>
      apply StateT.ext <;> intro z <;>
        simp [reassocQueries, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
          QueryImpl.parallelStateT, coins, Functor.map_map, Prod.map]
  exact congrArg (fun x => x.run' (t, s))
    (QueryImpl.simulateQ_simulateQ_eq_of_apply h oa).symm

private theorem replaceRightCoins {κ T σ α : Type} {ctxSpec : OracleSpec κ}
    {init : ProbComp σ} {impl : QueryImpl spec (StateT σ ProbComp)}
    (P : ResetPolicy init impl) (ctx : QueryImpl ctxSpec (StateT T ProbComp))
    (oa : OracleComp (unifSpec + (ctxSpec + spec)) α) (t : T) :
    (simulateQ
      (coins (S := T × (P.World × P.Cursor)) + QueryImpl.parallelStateT ctx P.answer) oa).run'
      (t, (P.empty, P.begin)) =ᵈ
      (do
        let s ← init
        (simulateQ (coins (S := T × σ) + QueryImpl.parallelStateT ctx impl) oa).run' (t, s)) := by
  simpa only [← reassoc_run'] using
    replaceRight P (coins (S := T) + ctx) (simulateQ reassocQueries oa) t

private def swapInnerQueries {κ : Type} {ctxSpec : OracleSpec κ} :
    QueryImpl (unifSpec + (spec + ctxSpec)) (OracleComp (unifSpec + (ctxSpec + spec)))
  | .inl q => query (spec := unifSpec + (ctxSpec + spec)) (.inl q)
  | .inr (.inl q) => query (spec := unifSpec + (ctxSpec + spec)) (.inr (.inr q))
  | .inr (.inr q) => query (spec := unifSpec + (ctxSpec + spec)) (.inr (.inl q))

private theorem parallel_swap_coins_run' {κ T σ α : Type} {ctxSpec : OracleSpec κ}
    (handler : QueryImpl spec (StateT σ ProbComp))
    (ctx : QueryImpl ctxSpec (StateT T ProbComp))
    (oa : OracleComp (unifSpec + (spec + ctxSpec)) α) (s : σ) (t : T) :
    (simulateQ (coins (S := σ × T) + QueryImpl.parallelStateT handler ctx) oa).run' (s, t) =
      (simulateQ (coins (S := T × σ) + QueryImpl.parallelStateT ctx handler)
        (simulateQ swapInnerQueries oa)).run' (t, s) := by
  rw [← QueryImpl.simulateQ_compose]
  apply OracleComp.run'_simulateQ_eq_of_query_map_eq
    (proj := Prod.swap)
  intro q z
  rcases q with q | (q | q) <;>
    simp [QueryImpl.compose, swapInnerQueries, QueryImpl.parallelStateT,
      QueryImpl.add_apply_inl, QueryImpl.add_apply_inr, coins,
      Functor.map_map, Prod.map, Prod.swap] <;> rfl

private theorem replaceLeftCoins {κ T σ α : Type} {ctxSpec : OracleSpec κ}
    {init : ProbComp σ} {impl : QueryImpl spec (StateT σ ProbComp)}
    (P : ResetPolicy init impl) (ctx : QueryImpl ctxSpec (StateT T ProbComp))
    (oa : OracleComp (unifSpec + (spec + ctxSpec)) α) (t : T) :
    (simulateQ
      (coins (S := (P.World × P.Cursor) × T) + QueryImpl.parallelStateT P.answer ctx) oa).run'
      ((P.empty, P.begin), t) =ᵈ
      (do
        let s ← init
        (simulateQ (coins (S := σ × T) + QueryImpl.parallelStateT impl ctx) oa).run' (s, t)) := by
  rw [parallel_swap_coins_run' P.answer ctx oa (P.empty, P.begin) t]
  exact (replaceRightCoins P ctx (simulateQ swapInnerQueries oa) t).trans
    (EvalDistEq.bind_right init fun s => by
      rw [← parallel_swap_coins_run' impl ctx oa s t])

section Product

variable {ι₁ ι₂ σ₁ σ₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
  {init₁ : ProbComp σ₁} {init₂ : ProbComp σ₂}
  {impl₁ : QueryImpl spec₁ (StateT σ₁ ProbComp)}
  {impl₂ : QueryImpl spec₂ (StateT σ₂ ProbComp)}
  (P₁ : ResetPolicy init₁ impl₁) (P₂ : ResetPolicy init₂ impl₂)

/-- Run two frozen handlers on separate persistent worlds and separate local cursors. -/
@[expose] def productAnswer : QueryImpl (spec₁ + spec₂)
    (StateT ((P₁.World × P₂.World) × (P₁.Cursor × P₂.Cursor)) ProbComp)
  | .inl q => StateT.mk fun s =>
      (fun z => (z.1, ((z.2.1, s.1.2), (z.2.2, s.2.2)))) <$>
        (P₁.answer q).run (s.1.1, s.2.1)
  | .inr q => StateT.mk fun s =>
      (fun z => (z.1, ((s.1.1, z.2.1), (s.2.1, z.2.2)))) <$>
        (P₂.answer q).run (s.1.2, s.2.2)

/-- Answering on a sum signature only extends the component world that was queried. -/
theorem productAnswer_grows (q : (spec₁ + spec₂).Domain) (w) (c) (z)
    (hz : z ∈ support ((productAnswer P₁ P₂ q).run (w, c))) : w ≤ z.2.1 := by
  cases q with
  | inl q =>
      simp only [productAnswer, StateT.run_mk, support_map] at hz
      obtain ⟨y, hy, rfl⟩ := hz
      exact ⟨P₁.grows q _ _ _ hy, le_rfl⟩
  | inr q =>
      simp only [productAnswer, StateT.run_mk, support_map] at hz
      obtain ⟨y, hy, rfl⟩ := hz
      exact ⟨le_rfl, P₂.grows q _ _ _ hy⟩

/-- An answered query on either summand remains frozen in every extension of both worlds. -/
theorem productAnswer_frozen (q : (spec₁ + spec₂).Domain) (w w') (c) (z)
    (hz : z ∈ support ((productAnswer P₁ P₂ q).run (w, c))) (hw : z.2.1 ≤ w') :
    (productAnswer P₁ P₂ q).run (w', c) = pure (z.1, (w', z.2.2)) := by
  cases q with
  | inl q =>
      simp only [productAnswer, StateT.run_mk, support_map] at hz
      obtain ⟨y, hy, rfl⟩ := hz
      simp [productAnswer, P₁.frozen q _ _ _ y hy hw.1]
  | inr q =>
      simp only [productAnswer, StateT.run_mk, support_map] at hz
      obtain ⟨y, hy, rfl⟩ := hz
      simp [productAnswer, P₂.frozen q _ _ _ y hy hw.2]

/-- Queries on a product policy commute, including their separate local cursor updates. -/
theorem productAnswer_commute (q₁ q₂ : (spec₁ + spec₂).Domain) (c₁ c₂) (w) :
    (do
      let z₁ ← (productAnswer P₁ P₂ q₁).run (w, c₁)
      let z₂ ← (productAnswer P₁ P₂ q₂).run (z₁.2.1, c₂)
      pure ((z₁.1, z₁.2.2), (z₂.1, z₂.2.2), z₂.2.1)) =ᵈ
    (do
      let z₂ ← (productAnswer P₁ P₂ q₂).run (w, c₂)
      let z₁ ← (productAnswer P₁ P₂ q₁).run (z₂.2.1, c₁)
      pure ((z₁.1, z₁.2.2), (z₂.1, z₂.2.2), z₁.2.1)) := by
  cases q₁ with
  | inl q₁ =>
      cases q₂ with
      | inl q₂ =>
          simpa [productAnswer, bind_map_left, map_bind, Function.comp_def] using
            (P₁.commute q₁ q₂ c₁.1 c₂.1 w.1).map
              (fun z => ((z.1.1, (z.1.2, c₁.2)),
                (z.2.1.1, (z.2.1.2, c₂.2)), (z.2.2, w.2)))
      | inr q₂ =>
          let : MeasurableSpace
              (((spec₁ + spec₂).Range (.inl q₁) × (P₁.Cursor × P₂.Cursor)) ×
                ((spec₁ + spec₂).Range (.inr q₂) × (P₁.Cursor × P₂.Cursor)) ×
                (P₁.World × P₂.World)) := ⊤
          apply EvalDistEq.of_evalDist_eq
          simp only [productAnswer, StateT.run_mk, bind_map_left]
          exact OracleComp.evalDist_bind_bind_swap _ _ _
  | inr q₁ =>
      cases q₂ with
      | inl q₂ =>
          let : MeasurableSpace
              (((spec₁ + spec₂).Range (.inr q₁) × (P₁.Cursor × P₂.Cursor)) ×
                ((spec₁ + spec₂).Range (.inl q₂) × (P₁.Cursor × P₂.Cursor)) ×
                (P₁.World × P₂.World)) := ⊤
          apply EvalDistEq.of_evalDist_eq
          simp only [productAnswer, StateT.run_mk, bind_map_left]
          exact OracleComp.evalDist_bind_bind_swap _ _ _
      | inr q₂ =>
          simpa [productAnswer, bind_map_left, map_bind, Function.comp_def] using
            (P₂.commute q₁ q₂ c₁.2 c₂.2 w.2).map
              (fun z => ((z.1.1, (c₁.1, z.1.2)),
                (z.2.1.1, (c₂.1, z.2.1.2)), (w.1, z.2.2)))

private theorem productAnswer_run' {α : Type}
    (oa : OracleComp (spec₁ + spec₂) α) (w : P₁.World × P₂.World)
    (c : P₁.Cursor × P₂.Cursor) :
    (simulateQ (productAnswer P₁ P₂) oa).run' (w, c) =
      (simulateQ (QueryImpl.parallelStateT P₁.answer P₂.answer) oa).run'
        ((w.1, c.1), (w.2, c.2)) := by
  apply OracleComp.run'_simulateQ_eq_of_query_map_eq
    (proj := fun s : (P₁.World × P₂.World) × (P₁.Cursor × P₂.Cursor) =>
      ((s.1.1, s.2.1), (s.1.2, s.2.2)))
  intro q s
  cases q <;> simp [productAnswer, QueryImpl.parallelStateT, Functor.map_map, Prod.map] <;> rfl

private theorem productAnswer_coins_run' {α : Type}
    (oa : OracleComp (unifSpec + (spec₁ + spec₂)) α) (w : P₁.World × P₂.World)
    (c : P₁.Cursor × P₂.Cursor) :
    (simulateQ (coins (S := (P₁.World × P₂.World) × (P₁.Cursor × P₂.Cursor)) +
      productAnswer P₁ P₂) oa).run' (w, c) =
      (simulateQ (coins (S := (P₁.World × P₁.Cursor) × (P₂.World × P₂.Cursor)) +
        QueryImpl.parallelStateT P₁.answer P₂.answer) oa).run'
        ((w.1, c.1), (w.2, c.2)) := by
  apply OracleComp.run'_simulateQ_eq_of_query_map_eq
    (proj := fun s : (P₁.World × P₂.World) × (P₁.Cursor × P₂.Cursor) =>
      ((s.1.1, s.2.1), (s.1.2, s.2.2)))
  intro q s
  rcases q with q | (q | q) <;>
    simp [productAnswer, QueryImpl.parallelStateT, QueryImpl.add_apply_inl,
      QueryImpl.add_apply_inr, coins, Functor.map_map, Prod.map] <;> rfl

/-- The product of independent reset policies freezes each summand in its own world and resets
both local cursors at the start of every run. -/
@[expose] def product :
    ResetPolicy (do return (← init₁, ← init₂)) (QueryImpl.parallelStateT impl₁ impl₂) where
  World := P₁.World × P₂.World
  empty := (P₁.empty, P₂.empty)
  Cursor := P₁.Cursor × P₂.Cursor
  begin := (P₁.begin, P₂.begin)
  answer := productAnswer P₁ P₂
  faithful oa := by
    rw [productAnswer_run']
    simp only [bind_assoc, pure_bind]
    exact (replaceRight P₂ P₁.answer oa (P₁.empty, P₁.begin)).trans
      ((EvalDistEq.bind_right init₂ fun s₂ => replaceLeft P₁ impl₂ oa s₂).trans
        (OracleComp.EvalDistEq.bind_bind_swap init₂ init₁ _))
  faithful_coins oa := by
    rw [productAnswer_coins_run']
    simp only [bind_assoc, pure_bind]
    exact (replaceRightCoins P₂ P₁.answer oa (P₁.empty, P₁.begin)).trans
      ((EvalDistEq.bind_right init₂ fun s₂ => replaceLeftCoins P₁ impl₂ oa s₂).trans
        (OracleComp.EvalDistEq.bind_bind_swap init₂ init₁ _))
  grows := productAnswer_grows P₁ P₂
  frozen := productAnswer_frozen P₁ P₂
  commute := productAnswer_commute P₁ P₂

end Product

end Rewinding.ResetPolicy
