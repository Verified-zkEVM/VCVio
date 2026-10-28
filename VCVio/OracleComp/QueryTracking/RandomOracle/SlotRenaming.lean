/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.OracleComp.QueryTracking.RandomOracle.ExpectedFreshQuery
public import VCVio.OracleComp.QueryTracking.QueryBound.Counter
public import VCVio.OracleComp.SimSemantics.StateT.StateProjection

/-! # Assigning fresh random-oracle queries to finite slots

Labels acquire slots in first-query order. Repeated labels reuse their slots. Private coins
leave the assignment and chronological label log unchanged. A uniform fallback makes the
handler total; a hash-query budget rules out its use.
-/

public section

namespace OracleComp.SlotRenaming

open OracleSpec

variable {D R α : Type} {q : ℕ}

/-- Finite-slot assignments, with a cache for overflow and a chronological hash-query log. -/
structure State (D R : Type) (q : ℕ) where
  /-- The slot assigned to each label. -/
  slotOf : D → Option (Fin q)
  /-- The number of fresh labels encountered, including overflow. -/
  next : ℕ
  /-- Responses for labels first encountered after all finite slots have been used. -/
  overflow : (D →ₒ R).QueryCache
  /-- Every queried label in chronological order, including repetitions. -/
  log : List (D × R)

/-- The initial assignment has no occupied slots and no receipts. -/
@[expose] def initial : State D R q := ⟨fun _ => none, 0, ∅, []⟩

/-- Add one receipt without changing the assignment. -/
@[expose] def record (s : State D R q) (l : D) (r : R) : State D R q :=
  { s with log := s.log ++ [(l, r)] }

/-- Assign the next unused slot to a new label and record its receipt. -/
@[expose] def assign [DecidableEq D] (s : State D R q) (l : D)
    (h : s.next < q) (r : R) : State D R q :=
  { s with
    slotOf := Function.update s.slotOf l (some ⟨s.next, h⟩)
    next := s.next + 1
    log := s.log ++ [(l, r)] }

/-- Cache a fresh overflow response and record its receipt. -/
@[expose] def spill [DecidableEq D] (s : State D R q) (l : D) (r : R) : State D R q :=
  { s with
    next := s.next + 1
    overflow := s.overflow.cacheQuery l r
    log := s.log ++ [(l, r)] }

/-- Route labels to finite slots, using independent private sampling only on overflow. -/
@[expose] def routeHash [DecidableEq D] [SampleableType R] :
    QueryImpl (D →ₒ R) (StateT (State D R q) (OracleComp (unifSpec + (Fin q →ₒ R)))) :=
  fun l s => match s.slotOf l with
  | some i => (fun r => (r, record s l r)) <$> (unifSpec + (Fin q →ₒ R)).query (.inr i)
  | none => match s.overflow l with
    | some r => pure (r, record s l r)
    | none => if h : s.next < q then
        (fun r => (r, assign s l h r)) <$> (unifSpec + (Fin q →ₒ R)).query (.inr ⟨s.next, h⟩)
      else (fun r => (r, spill s l r)) <$> (liftM ($ᵗ R) : OracleComp _ R)

/-- Interleave private coins with finite-slot hash routing. -/
@[expose] def route [DecidableEq D] [SampleableType R] :
    QueryImpl (unifSpec + (D →ₒ R))
      (StateT (State D R q) (OracleComp (unifSpec + (Fin q →ₒ R)))) :=
  QueryImpl.add (fun n s => (fun x => (x, s)) <$>
    (liftM ((unifSpec + (Fin q →ₒ R)).query (.inl n)) : OracleComp _ _)) routeHash

/-- The actual slot oracle runs routing above a lazy random oracle on the finite slot domain. -/
@[expose] def lazy [DecidableEq D] [SampleableType R] :
    QueryImpl (unifSpec + (D →ₒ R))
      (StateT (State D R q × (Fin q →ₒ R).QueryCache) ProbComp) :=
  ((Fin q →ₒ R).romImpl.mapStateTBase route).flattenStateT

/-- Read the label-indexed cache represented by the finite slots and the overflow cache. -/
@[expose] def cache (s : State D R q) (c : (Fin q →ₒ R).QueryCache) : (D →ₒ R).QueryCache :=
  QueryCache.ofFn fun l => match s.slotOf l with
    | some i => c i
    | none => s.overflow l

/-- Forget the slot assignment but keep the full label cache and receipt provenance. -/
@[expose] def project (s : State D R q × (Fin q →ₒ R).QueryCache) :
    (D →ₒ R).QueryCache × List (D × R) := (cache s.1 s.2, s.1.log)

/-- Honest lazy hashing with a chronological label log and independent private coins. -/
@[expose] def honest [DecidableEq D] [SampleableType R] :
    QueryImpl (unifSpec + (D →ₒ R))
      (StateT ((D →ₒ R).QueryCache × List (D × R)) ProbComp) :=
  QueryImpl.add
    (fun n s => (fun x => (x, s)) <$> (liftM (unifSpec.query n) : ProbComp _))
    (fun l s => (fun z => (z.1, z.2, s.2 ++ [(l, z.1)])) <$> ((D →ₒ R).randomOracle l).run s.1)

/-- Slot-cache invariant: assigned slots are occupied, and all slots at or beyond `next`
are unused. These are the facts needed for exact lazy-oracle simulation. -/
structure Valid (s : State D R q) (c : (Fin q →ₒ R).QueryCache) : Prop where
  /-- Each assigned slot precedes the next fresh index. -/
  below : ∀ l i, s.slotOf l = some i → i.val < s.next
  /-- Assigned slots contain cached responses. -/
  occupied : ∀ l i, s.slotOf l = some i → c i ≠ none
  /-- Future slots have not been queried. -/
  unused : ∀ i, s.next ≤ i.val → c i = none

/-- The empty assignment and slot cache satisfy the simulation invariant. -/
theorem valid_initial : Valid (initial : State D R q) ∅ := by
  constructor <;> simp [initial]

private theorem lazy_coin [DecidableEq D] [SampleableType R] (n : ℕ)
    (s : State D R q) (c : (Fin q →ₒ R).QueryCache) :
    (lazy (.inl n)).run (s, c) =
      (fun x => (x, s, c)) <$> (liftM (unifSpec.query n) : ProbComp _) := by
  rw [lazy, QueryImpl.flattenStateT_mapStateTBase_apply_run]
  change (fun y => (y.1.1, y.1.2, y.2)) <$>
    (simulateQ (Fin q →ₒ R).romImpl
      ((fun x => (x, s)) <$> (liftM ((unifSpec + (Fin q →ₒ R)).query (.inl n)) :
        OracleComp _ _))).run c = _
  simp [OracleSpec.romImpl, unifFwdImpl, Functor.map_map]

private theorem lazy_hash [DecidableEq D] [SampleableType R] (l : D)
    (s : State D R q) (c : (Fin q →ₒ R).QueryCache) :
    (lazy (.inr l)).run (s, c) = match s.slotOf l with
    | some i => (fun z => (z.1, record s l z.1, z.2)) <$>
        ((Fin q →ₒ R).randomOracle i).run c
    | none => match s.overflow l with
      | some r => pure (r, record s l r, c)
      | none => if h : s.next < q then
          (fun z => (z.1, assign s l h z.1, z.2)) <$>
            ((Fin q →ₒ R).randomOracle ⟨s.next, h⟩).run c
        else (fun r => (r, spill s l r, c)) <$> ($ᵗ R : ProbComp R) := by
  rw [lazy, QueryImpl.flattenStateT_mapStateTBase_apply_run]
  change (fun y => (y.1.1, y.1.2, y.2)) <$>
    (simulateQ (Fin q →ₒ R).romImpl ((routeHash l).run s)).run c = _
  have hr : (routeHash l).run s =
      (match s.slotOf l with
      | some i => (fun r => (r, record s l r)) <$>
          (liftM ((unifSpec + (Fin q →ₒ R)).query (.inr i)) : OracleComp _ _)
      | none => match s.overflow l with
        | some r => pure (r, record s l r)
        | none => if h : s.next < q then
            (fun r => (r, assign s l h r)) <$>
              (liftM ((unifSpec + (Fin q →ₒ R)).query (.inr ⟨s.next, h⟩)) : OracleComp _ _)
          else (fun r => (r, spill s l r)) <$> (liftM ($ᵗ R) : OracleComp _ R)) := rfl
  rw [hr]
  cases hs : s.slotOf l with
  | some i => simp [OracleSpec.romImpl, Functor.map_map]
  | none =>
    cases hc : s.overflow l with
    | some r => simp
    | none =>
      by_cases hn : s.next < q
      · simp [hn, OracleSpec.romImpl, Functor.map_map]
      · simp [hn, OracleSpec.romImpl, roSim.run_liftM, Functor.map_map]

private theorem cache_record (s : State D R q) (c : (Fin q →ₒ R).QueryCache) (l : D) (r : R) :
    cache (record s l r) c = cache s c := rfl

private theorem cache_assign [DecidableEq D] (s : State D R q)
    (c : (Fin q →ₒ R).QueryCache) (hv : Valid s c) (l : D) (h : s.next < q) (r : R) :
    cache (assign s l h r) (c.cacheQuery ⟨s.next, h⟩ r) = (cache s c).cacheQuery l r := by
  apply QueryCache.ext
  intro k
  by_cases hk : k = l
  · subst k
    simp [cache, assign]
  · simp only [cache, assign, QueryCache.ofFn_apply, Function.update_of_ne hk,
      QueryCache.cacheQuery_of_ne _ _ hk]
    cases he : s.slotOf k with
    | none => rfl
    | some j =>
      have hj : j ≠ ⟨s.next, h⟩ := by
        intro hj
        have := hv.below k j he
        subst j
        exact (Nat.lt_irrefl _ this)
      exact QueryCache.cacheQuery_of_ne _ _ hj

private theorem cache_spill [DecidableEq D] (s : State D R q)
    (c : (Fin q →ₒ R).QueryCache) (l : D) (hl : s.slotOf l = none) (r : R) :
    cache (spill s l r) c = (cache s c).cacheQuery l r := by
  apply QueryCache.ext
  intro k
  by_cases hk : k = l
  · subst k
    simp [cache, spill, hl]
  · simp only [cache, spill, QueryCache.ofFn_apply, QueryCache.cacheQuery_of_ne _ _ hk]

private theorem valid_record (s : State D R q) (c : (Fin q →ₒ R).QueryCache)
    (hv : Valid s c) (l : D) (r : R) : Valid (record s l r) c := ⟨hv.below, hv.occupied, hv.unused⟩

private theorem valid_assign [DecidableEq D] (s : State D R q)
    (c : (Fin q →ₒ R).QueryCache) (hv : Valid s c) (l : D) (h : s.next < q) (r : R) :
    Valid (assign s l h r) (c.cacheQuery ⟨s.next, h⟩ r) := by
  constructor
  · intro k j hj
    by_cases hk : k = l
    · subst k
      simp only [assign, Function.update_self, Option.some.injEq] at hj
      subst j
      exact Nat.lt_succ_self _
    · simp only [assign, Function.update_of_ne hk] at hj
      exact (hv.below k j hj).trans (Nat.lt_succ_self _)
  · intro k j hj
    by_cases hk : k = l
    · subst k
      simp only [assign, Function.update_self, Option.some.injEq] at hj
      subst j
      simp
    · simp only [assign, Function.update_of_ne hk] at hj
      have hne : j ≠ ⟨s.next, h⟩ := by
        intro he
        have := hv.below k j hj
        subst j
        exact (Nat.lt_irrefl _ this)
      simpa only [QueryCache.cacheQuery_of_ne _ _ hne] using hv.occupied k j hj
  · intro j hj
    have hne : j ≠ ⟨s.next, h⟩ := by
      intro he
      subst j
      simp [assign] at hj
    rw [QueryCache.cacheQuery_of_ne _ _ hne]
    exact hv.unused j (Nat.le_trans (Nat.le_succ _) hj)

private theorem valid_spill [DecidableEq D] (s : State D R q)
    (c : (Fin q →ₒ R).QueryCache) (hv : Valid s c) (l : D) (r : R) :
    Valid (spill s l r) c := by
  refine ⟨fun k j hj => (hv.below k j hj).trans (Nat.lt_succ_self _), hv.occupied, ?_⟩
  exact fun j hj => hv.unused j (Nat.le_trans (Nat.le_succ _) hj)

private theorem lazy_preserves [DecidableEq D] [SampleableType R]
    (t : (unifSpec + (D →ₒ R)).Domain) (st : State D R q × (Fin q →ₒ R).QueryCache)
    (hv : Valid st.1 st.2) (z) (hz : z ∈ support ((lazy t).run st)) : Valid z.2.1 z.2.2 := by
  rcases st with ⟨s, c⟩
  cases t with
  | inl n =>
    rw [lazy_coin, support_map] at hz
    obtain ⟨x, _, rfl⟩ := hz
    exact hv
  | inr l =>
    rw [lazy_hash] at hz
    cases hs : s.slotOf l with
    | some i =>
      cases hc : c i with
      | none => exact (hv.occupied l i hs hc).elim
      | some r =>
        simp only [hs, randomOracle.run_eq, hc, map_pure, support_pure,
          Set.mem_singleton_iff] at hz
        subst z
        exact valid_record s c hv l r
    | none =>
      cases hc : s.overflow l with
      | some r =>
        simp only [hs, hc, support_pure, Set.mem_singleton_iff] at hz
        subst z
        exact valid_record s c hv l r
      | none =>
        by_cases hn : s.next < q
        · have hu : c ⟨s.next, hn⟩ = none := hv.unused ⟨s.next, hn⟩ (le_refl _)
          simp only [hs, hc, dite_eq_left hn, randomOracle.run_eq, hu, bind_pure_comp,
            Functor.map_map, support_map] at hz
          obtain ⟨r, _, rfl⟩ := hz
          exact valid_assign s c hv l hn r
        · simp only [hs, hc, dite_eq_right hn, support_map] at hz
          obtain ⟨r, _, rfl⟩ := hz
          exact valid_spill s c hv l r

private theorem lazy_project [DecidableEq D] [SampleableType R]
    (t : (unifSpec + (D →ₒ R)).Domain) (st : State D R q × (Fin q →ₒ R).QueryCache)
    (hv : Valid st.1 st.2) :
    Prod.map id project <$> (lazy t).run st = (honest t).run (project st) := by
  rcases st with ⟨s, c⟩
  cases t with
  | inl n =>
    rw [lazy_coin]
    change Prod.map id project <$> ((fun x => (x, s, c)) <$>
      (liftM (unifSpec.query n) : ProbComp _)) =
        (fun x => (x, cache s c, s.log)) <$> (liftM (unifSpec.query n) : ProbComp _)
    simp [Functor.map_map, project]
  | inr l =>
    rw [lazy_hash]
    change _ = (fun z => (z.1, z.2, s.log ++ [(l, z.1)])) <$>
      ((D →ₒ R).randomOracle l).run (cache s c)
    cases hs : s.slotOf l with
    | some i =>
      cases hc : c i with
      | none => exact (hv.occupied l i hs hc).elim
      | some r =>
        have hl : cache s c l = some r := by simp [cache, hs, hc]
        simp only [randomOracle.run_eq, hc, hl, map_pure]
        rfl
    | none =>
      cases hc : s.overflow l with
      | some r =>
        have hl : cache s c l = some r := by simp [cache, hs, hc]
        simp only [randomOracle.run_eq, hl, map_pure]
        rfl
      | none =>
        have hl : cache s c l = none := by simp [cache, hs, hc]
        by_cases hn : s.next < q
        · have hu : c ⟨s.next, hn⟩ = none := hv.unused ⟨s.next, hn⟩ (le_refl _)
          simp only [dite_eq_left hn, randomOracle.run_eq, hu, hl, bind_pure_comp,
            Functor.map_map]
          congr 1
          funext r
          change (_, cache (assign s l hn r) (c.cacheQuery ⟨s.next, hn⟩ r), _) = _
          rw [cache_assign s c hv]
          rfl
        · simp only [dite_eq_right hn, randomOracle.run_eq, hl, bind_pure_comp,
            Functor.map_map]
          congr 1
          funext r
          change (_, cache (spill s l r) c, _) = _
          rw [cache_spill s c l hs]
          rfl

/-- Projecting slot execution recovers the honest lazy oracle, including the label cache
and the chronological receipt log. The equality allows adaptive queries and private coins. -/
theorem simulateQ_lazy_project [DecidableEq D] [SampleableType R]
    (oa : OracleComp (unifSpec + (D →ₒ R)) α)
    (st : State D R q × (Fin q →ₒ R).QueryCache) (hv : Valid st.1 st.2) :
    Prod.map id project <$> (simulateQ lazy oa).run st =
      (simulateQ honest oa).run (project st) :=
  map_run_simulateQ_eq_of_query_map_eq_inv' lazy honest
    (fun st => Valid st.1 st.2) project lazy_preserves lazy_project oa st hv

/-! ## Finite-table execution -/

private theorem lift_id (r : R) : (liftM (m := Id) r : ProbComp R) = pure r := by
  change (liftM (pure r : Id R) : ProbComp R) = _
  rw [liftM_pure]

private theorem fixedTable_project [DecidableEq D]
    (oa : OracleComp (unifSpec + (D →ₒ R)) α) (g : D → R)
    (c : (D →ₒ R).QueryCache) (hc : c.AgreesWithFn g) :
    (fun z => z.1.1) <$> fixedTableLoggedRun oa g c =
      simulateQ (unifFwdAnswerImpl g) oa := by
  induction oa using OracleComp.inductionOn generalizing c with
  | pure a => simp [fixedTableLoggedRun]
  | query_bind t k ih =>
    rw [fixedTableLoggedRun_bind]
    cases t with
    | inl n =>
      rw [fixedTableLoggedRun_uniformQuery]
      simp only [map_bind, bind_map_left, Functor.map_map]
      simp [simulateQ_bind, unifFwdAnswerImpl, fun u => ih u c hc]
    | inr l =>
      rw [fixedTableLoggedRun_hashQuery]
      cases hl : c l with
      | some r =>
        have hgr : g l = r := hc hl
        rw [QueryImpl.withCaching_run_some _ hl]
        simp [simulateQ_bind, unifFwdAnswerImpl, hgr, lift_id, ih r c hc]
      | none =>
        rw [QueryImpl.withCaching_run_none _ hl]
        have hc' : (c.cacheQuery l (g l)).AgreesWithFn g :=
          (QueryCache.agreesWithFn_cacheQuery_iff _ _ _ _ hl).mpr ⟨hc, rfl⟩
        simp [simulateQ_bind, unifFwdAnswerImpl, lift_id, ih _ _ hc']

/-- A finite-domain lazy random oracle has the same output distribution as an independently
uniform complete table. Both sides forward the computation's private coins. -/
theorem simulateQ_romImpl_run'_eq_uniform_table [DecidableEq D] [Finite D]
    [SampleableType R] [SampleableType (D → R)]
    (oa : OracleComp (unifSpec + (D →ₒ R)) α) :
    (simulateQ (D →ₒ R).romImpl oa).run' ∅ =ᵈ
      (($ᵗ (D → R)) >>= fun g => simulateQ (unifFwdAnswerImpl g) oa) := by
  let : MeasurableSpace ((α × QueryLog (D →ₒ R)) × (D →ₒ R).QueryCache) := ⊤
  have hd := evalDist_randomOracleLoggedRun_eq_fixedTable_finite oa ∅
  have he : randomOracleLoggedRun oa ∅ =ᵈ
      (($ᵗ (D → R)) >>= fun g => fixedTableLoggedRun oa g ∅) := by
    apply evalDistEq_iff_evalDist_eq.mpr
    simpa only [completeTable_empty] using hd
  have hm := he.map (fun z => z.1.1)
  have hp : (fun z => z.1.1) <$> randomOracleLoggedRun oa ∅ =
      (simulateQ (D →ₒ R).romImpl oa).run' ∅ := by
    rw [StateT.run'_eq, ← randomOracleLoggedRun_project]
    simp only [Functor.map_map]
  rw [hp] at hm
  simpa only [map_bind, fixedTable_project oa _ ∅ (by simp [QueryCache.AgreesWithFn])] using hm

/-- Execute a label computation with first-use slot allocation and a fixed table of slot
responses. The uniform overflow fallback is unreachable under a sufficient hash-query budget. -/
@[expose] def tableRun [DecidableEq D] [SampleableType R]
    (oa : OracleComp (unifSpec + (D →ₒ R)) α) (g : Fin q → R) : ProbComp (α × State D R q) :=
  simulateQ (unifFwdAnswerImpl g) ((simulateQ route oa).run initial)

/-- Forgetting the slot cache, lazy slot execution equals uniform presampling of the finite
slot table. The remaining state retains the slot assignment and all receipt labels. -/
theorem simulateQ_lazy_eq_uniform_table [DecidableEq D] [SampleableType R]
    [SampleableType (Fin q → R)] (oa : OracleComp (unifSpec + (D →ₒ R)) α) :
    (fun z => (z.1, z.2.1)) <$> (simulateQ lazy oa).run (initial, ∅) =ᵈ
      (($ᵗ (Fin q → R)) >>= fun g => tableRun oa g) := by
  have h := simulateQ_romImpl_run'_eq_uniform_table
    ((simulateQ (route (q := q)) oa).run initial)
  simpa only [tableRun, StateT.run'_eq,
    simulateQ_mapStateTBase_run_eq_map_flattenStateT, Functor.map_map,
    Function.comp_def, lazy] using h

/-- Honest lazy hashing over arbitrary labels has the same joint distribution of output and
receipt provenance as first-use routing through a uniform finite table. The fallback retains
this equality without a query bound; `tableRun_no_overflow` excludes it for bounded programs. -/
theorem simulateQ_honest_eq_uniform_table [DecidableEq D] [SampleableType R]
    [SampleableType (Fin q → R)] (oa : OracleComp (unifSpec + (D →ₒ R)) α) :
    (fun z => (z.1, z.2.2)) <$> (simulateQ honest oa).run (∅, []) =ᵈ
      (($ᵗ (Fin q → R)) >>= fun g => (fun z => (z.1, z.2.log)) <$> tableRun oa g) := by
  have hp := congrArg (Functor.map (fun z => (z.1, z.2.2)))
    (simulateQ_lazy_project oa ((initial : State D R q), ∅) valid_initial)
  have he := (simulateQ_lazy_eq_uniform_table (q := q) oa).map (fun z => (z.1, z.2.log))
  have hi : project ((initial : State D R q), ∅) = (∅, []) := rfl
  rw [hi] at hp
  rw [← hp]
  simpa only [Functor.map_map, Function.comp_def, Prod.map, id_eq, project, map_bind] using he

/-! ## Hash-query budgets and provenance -/

/-- Reachable slot assignments are injective; every receipt has either a finite slot or an
overflow response. The fresh-label counter never exceeds the number of hash receipts. -/
structure Assigned (s : State D R q) : Prop where
  /-- All allocated slots precede the next fresh index. -/
  below : ∀ l i, s.slotOf l = some i → i.val < s.next
  /-- Distinct labels cannot share a slot. -/
  injective : ∀ l k i, s.slotOf l = some i → s.slotOf k = some i → l = k
  /-- Every logged label has a response location. -/
  logged : ∀ l ∈ s.log.map Prod.fst, s.slotOf l ≠ none ∨ s.overflow l ≠ none
  /-- Any overflow response witnesses exhaustion of all finite slots. -/
  overflow : ∀ l, s.overflow l ≠ none → q < s.next
  /-- Each fresh label has at least one receipt. -/
  count : s.next ≤ s.log.length

private theorem assigned_initial : Assigned (initial : State D R q) := by
  constructor <;> simp [initial]

private theorem assigned_record (s : State D R q) (hv : Assigned s) (l : D) (r : R)
    (hl : s.slotOf l ≠ none ∨ s.overflow l ≠ none) : Assigned (record s l r) := by
  refine ⟨hv.below, hv.injective, ?_, hv.overflow, ?_⟩
  · intro k hk
    simp only [record, List.map_append, List.map_cons, List.map_nil,
      List.mem_append, List.mem_singleton] at hk
    rcases hk with hk | rfl
    · exact hv.logged k hk
    · exact hl
  · simpa only [record, List.length_append, List.length_singleton] using
      hv.count.trans (Nat.le_succ _)

private theorem assigned_assign [DecidableEq D] (s : State D R q) (hv : Assigned s)
    (l : D) (h : s.next < q) (r : R) : Assigned (assign s l h r) := by
  constructor
  · intro k i hi
    by_cases hk : k = l
    · subst k
      simp only [assign, Function.update_self, Option.some.injEq] at hi
      subst i
      exact Nat.lt_succ_self _
    · simp only [assign, Function.update_of_ne hk] at hi
      exact (hv.below k i hi).trans (Nat.lt_succ_self _)
  · intro k m i hk hm
    by_cases hkl : k = l
    · subst k
      simp only [assign, Function.update_self, Option.some.injEq] at hk
      subst i
      by_contra hml
      have hml' : m ≠ l := Ne.symm hml
      simp only [assign, Function.update_of_ne hml'] at hm
      exact (Nat.lt_irrefl _ (hv.below m _ hm))
    · simp only [assign, Function.update_of_ne hkl] at hk
      by_cases hml : m = l
      · subst m
        simp only [assign, Function.update_self, Option.some.injEq] at hm
        subst i
        exact (Nat.lt_irrefl _ (hv.below k _ hk)).elim
      · simp only [assign, Function.update_of_ne hml] at hm
        exact hv.injective k m i hk hm
  · intro k hk
    by_cases hkl : k = l
    · subst k
      simp [assign]
    · simp only [assign, Function.update_of_ne hkl]
      apply hv.logged k
      simpa only [assign, List.map_append, List.map_cons, List.map_nil,
        List.mem_append, List.mem_singleton, hkl, or_false] using hk
  · intro k hk
    exact (hv.overflow k hk).trans (Nat.lt_succ_self _)
  · simpa only [assign, List.length_append, List.length_singleton] using Nat.succ_le_succ hv.count

private theorem assigned_spill [DecidableEq D] (s : State D R q) (hv : Assigned s)
    (l : D) (hn : ¬s.next < q) (r : R) : Assigned (spill s l r) := by
  refine ⟨fun k i hi => (hv.below k i hi).trans (Nat.lt_succ_self _), hv.injective, ?_, ?_, ?_⟩
  · intro k hk
    by_cases hkl : k = l
    · subst k
      simp [spill]
    · simp only [spill, QueryCache.cacheQuery_of_ne _ _ hkl]
      apply hv.logged k
      simpa only [spill, List.map_append, List.map_cons, List.map_nil,
        List.mem_append, List.mem_singleton, hkl, or_false] using hk
  · intro k hk
    exact Nat.lt_succ_of_le (Nat.le_of_not_gt hn)
  · simpa only [spill, List.length_append, List.length_singleton] using Nat.succ_le_succ hv.count

private theorem route_step [DecidableEq D] [SampleableType R]
    (t : (unifSpec + (D →ₒ R)).Domain) (s : State D R q) (z)
    (hz : z ∈ support ((route t).run s)) :
    (Assigned s → Assigned z.2) ∧
      z.2.log.length = s.log.length + if t.isRight then 1 else 0 := by
  cases t with
  | inl n =>
    change z ∈ support ((fun x => (x, s)) <$>
      (liftM ((unifSpec + (Fin q →ₒ R)).query (.inl n)) : OracleComp _ _)) at hz
    rw [support_map] at hz
    obtain ⟨r, _, rfl⟩ := hz
    simp
  | inr l =>
    change z ∈ support ((routeHash l).run s) at hz
    dsimp only [routeHash, StateT.run] at hz
    cases hs : s.slotOf l with
    | some i =>
      simp only [hs, support_map] at hz
      obtain ⟨r, _, rfl⟩ := hz
      exact ⟨fun hv => assigned_record s hv l r (Or.inl (by simp [hs])), by simp [record]⟩
    | none =>
      cases hc : s.overflow l with
      | some r =>
        simp only [hs, hc, support_pure, Set.mem_singleton_iff] at hz
        subst z
        exact ⟨fun hv => assigned_record s hv l r (Or.inr (by simp [hc])), by simp [record]⟩
      | none =>
        by_cases hn : s.next < q
        · simp only [hs, hc, dite_eq_left hn, support_map] at hz
          obtain ⟨r, _, rfl⟩ := hz
          exact ⟨fun hv => assigned_assign s hv l hn r, by simp [assign]⟩
        · simp only [hs, hc, dite_eq_right hn, support_map] at hz
          obtain ⟨r, _, rfl⟩ := hz
          exact ⟨fun hv => assigned_spill s hv l hn r, by simp [spill]⟩

private theorem support_simulate_subset {ι : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec ProbComp) (oa : OracleComp spec α) :
    support (simulateQ impl oa) ⊆ support oa := by
  simpa using support_simulateQ_run'_subset
    (impl.liftTarget (StateT Unit ProbComp)) oa ()

/-- Every fixed-table run has an injective slot assignment and a chronological receipt log
whose length bounds the number of fresh labels. -/
theorem tableRun_assigned [DecidableEq D] [SampleableType R]
    (oa : OracleComp (unifSpec + (D →ₒ R)) α) (g : Fin q → R) (z)
    (hz : z ∈ support (tableRun oa g)) : Assigned z.2 := by
  apply simulateQ_run_preserves_inv_of_query route Assigned
    (fun t s hs z hz => (route_step t s z hz).1 hs) oa initial assigned_initial z
  exact support_simulate_subset _ _ hz

/-- A syntactic hash-query budget bounds the chronological receipt log in every supported
fixed-table run. Private coin queries do not contribute to this count. -/
theorem tableRun_log_length_le [DecidableEq D] [SampleableType R]
    (oa : OracleComp (unifSpec + (D →ₒ R)) α) (g : Fin q → R)
    (hbound : IsQueryBoundP oa (fun t => t.isRight) q) (z)
    (hz : z ∈ support (tableRun oa g)) : z.2.log.length ≤ q := by
  have h := hbound.cost_le_of_mem_support_run_simulateQ (impl := route)
    (fun s => s.log.length)
    (fun t ht s z hz => by simp [(route_step t s z hz).2, ht])
    (fun t ht s z hz => by simp [(route_step t s z hz).2, ht])
    initial z (support_simulate_subset _ _ hz)
  simpa only [initial, List.length_nil, zero_add] using h

/-- With at most `q` hash queries, every receipt is assigned a finite slot. No overflow
response can occur, even when labels depend on earlier hash replies or private coins. -/
theorem tableRun_no_overflow [DecidableEq D] [SampleableType R]
    (oa : OracleComp (unifSpec + (D →ₒ R)) α) (g : Fin q → R)
    (hbound : IsQueryBoundP oa (fun t => t.isRight) q) (z)
    (hz : z ∈ support (tableRun oa g)) :
    z.2.overflow = ∅ ∧ ∀ l ∈ z.2.log.map Prod.fst, ∃ i, z.2.slotOf l = some i := by
  have hv := tableRun_assigned oa g z hz
  have hn := hv.count.trans (tableRun_log_length_le oa g hbound z hz)
  have he (l : D) : z.2.overflow l = none := by
    by_contra hl
    exact (Nat.not_lt_of_ge hn) (hv.overflow l hl)
  refine ⟨QueryCache.ext he, ?_⟩
  intro l hl
  have hs := hv.logged l hl
  rcases hs with hs | hs
  · exact Option.ne_none_iff_exists'.mp hs
  · exact (hs (he l)).elim

/-! ## Fixed-table receipt values -/

/-- Interpret the allocated slots through a complete response table, retaining overflow entries. -/
@[expose] def tableCache (g : Fin q → R) (s : State D R q) : (D →ₒ R).QueryCache :=
  cache s (QueryCache.ofFn fun i => some (g i))

private theorem tableCache_assign [DecidableEq D] (g : Fin q → R) (s : State D R q)
    (l : D) (h : s.next < q) (r : R) :
    tableCache g (assign s l h r) = (tableCache g s).cacheQuery l (g ⟨s.next, h⟩) := by
  apply QueryCache.ext
  intro k
  by_cases hk : k = l
  · subst k
    simp [tableCache, cache, assign]
  · simp [tableCache, cache, assign, Function.update_of_ne hk,
      QueryCache.cacheQuery_of_ne _ _ hk]

private theorem tableCache_spill [DecidableEq D] (g : Fin q → R) (s : State D R q)
    (l : D) (hl : s.slotOf l = none) (r : R) :
    tableCache g (spill s l r) = (tableCache g s).cacheQuery l r :=
  cache_spill s _ l hl r

/-- One step of finite-table routing forwards coins, reuses assigned slots, and allocates a
fresh slot before using the overflow sampler. -/
theorem tableHandler_apply [DecidableEq D] [SampleableType R]
    (g : Fin q → R) (t : (unifSpec + (D →ₒ R)).Domain) (s : State D R q) :
    (((unifFwdAnswerImpl g).mapStateTBase route) t).run s =
      match t with
      | .inl n => (fun r => (r, s)) <$> (liftM (unifSpec.query n) : ProbComp _)
      | .inr l => match s.slotOf l with
        | some i => pure (g i, record s l (g i))
        | none => match s.overflow l with
          | some r => pure (r, record s l r)
          | none => if h : s.next < q then
              pure (g ⟨s.next, h⟩, assign s l h (g ⟨s.next, h⟩))
            else (fun r => (r, spill s l r)) <$> ($ᵗ R : ProbComp R) := by
  cases t with
  | inl n =>
    change simulateQ (unifFwdAnswerImpl g)
      ((fun r => (r, s)) <$> (liftM ((unifSpec + (Fin q →ₒ R)).query (.inl n)) :
        OracleComp _ _)) = _
    simp [unifFwdAnswerImpl]
  | inr l =>
    change simulateQ (unifFwdAnswerImpl g) ((routeHash l).run s) = _
    dsimp only [routeHash, StateT.run]
    cases hs : s.slotOf l with
    | some i => simp [unifFwdAnswerImpl, lift_id]
    | none =>
      cases hc : s.overflow l with
      | some r => simp
      | none =>
        by_cases hn : s.next < q
        · simp [hn, unifFwdAnswerImpl, lift_id]
        · have he : simulateQ (unifFwdAnswerImpl g)
              (liftM ($ᵗ R) : OracleComp (unifSpec + (Fin q →ₒ R)) R) = $ᵗ R := by
            change simulateQ (QueryImpl.id' unifSpec + ((QueryImpl.ofFn g).liftTarget ProbComp))
              (OracleComp.liftComp ($ᵗ R) _) = _
            rw [QueryImpl.simulateQ_add_liftComp_left]
            simp
          simp [hn, he]

private theorem table_receipts_preserves [DecidableEq D] [SampleableType R]
    (g : Fin q → R) (t : (unifSpec + (D →ₒ R)).Domain) (s : State D R q)
    (hs : ∀ p ∈ s.log, tableCache g s p.1 = some p.2) (z)
    (hz : z ∈ support ((((unifFwdAnswerImpl g).mapStateTBase route) t).run s)) :
    ∀ p ∈ z.2.log, tableCache g z.2 p.1 = some p.2 := by
  rw [tableHandler_apply] at hz
  cases t with
  | inl n =>
    rw [support_map] at hz
    obtain ⟨r, _, rfl⟩ := hz
    exact hs
  | inr l =>
    cases hl : s.slotOf l with
    | some i =>
      simp only [hl, support_pure, Set.mem_singleton_iff] at hz
      subst z
      intro p hp
      simp only [record, List.mem_append, List.mem_singleton] at hp
      rcases hp with hp | rfl
      · exact hs p hp
      · simp [tableCache, cache, record, hl]
    | none =>
      cases hc : s.overflow l with
      | some r =>
        simp only [hl, hc, support_pure, Set.mem_singleton_iff] at hz
        subst z
        intro p hp
        simp only [record, List.mem_append, List.mem_singleton] at hp
        rcases hp with hp | rfl
        · exact hs p hp
        · simp [tableCache, cache, record, hl, hc]
      | none =>
        have hold (p : D × R) (hp : p ∈ s.log) : p.1 ≠ l := by
          intro he
          have hv := hs p hp
          change (match s.slotOf p.1 with
            | some i => some (g i) | none => s.overflow p.1) = some p.2 at hv
          rw [he, hl, hc] at hv
          contradiction
        by_cases hn : s.next < q
        · simp only [hl, hc, dite_eq_left hn, support_pure, Set.mem_singleton_iff] at hz
          subst z
          intro p hp
          rw [tableCache_assign]
          simp only [assign, List.mem_append, List.mem_singleton] at hp
          rcases hp with hp | rfl
          · rw [QueryCache.cacheQuery_of_ne _ _ (hold p hp)]
            exact hs p hp
          · simp
        · simp only [hl, hc, dite_eq_right hn, support_map] at hz
          obtain ⟨r, _, rfl⟩ := hz
          intro p hp
          rw [tableCache_spill g s l hl]
          simp only [spill, List.mem_append, List.mem_singleton] at hp
          rcases hp with hp | rfl
          · rw [QueryCache.cacheQuery_of_ne _ _ (hold p hp)]
            exact hs p hp
          · simp

/-- Every chronological receipt agrees with the fixed table at its assigned slot, or with
its overflow-cache entry. Repeated receipts retain the same label origin. -/
theorem tableRun_receipts [DecidableEq D] [SampleableType R]
    (oa : OracleComp (unifSpec + (D →ₒ R)) α) (g : Fin q → R) (z)
    (hz : z ∈ support (tableRun oa g)) :
    ∀ p ∈ z.2.log, tableCache g z.2 p.1 = some p.2 := by
  have he : (simulateQ ((unifFwdAnswerImpl g).mapStateTBase route) oa).run initial =
      tableRun oa g := (QueryImpl.simulateQ_mapStateTBase_run _ _ _ _).symm
  rw [← he] at hz
  exact simulateQ_run_preserves_inv_of_query _
    (fun s => ∀ p ∈ s.log, tableCache g s p.1 = some p.2)
    (table_receipts_preserves g) oa initial (by simp [initial]) z hz

end OracleComp.SlotRenaming
