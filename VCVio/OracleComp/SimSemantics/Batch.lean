/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.OracleComp.Coercions.SubSpec.Basic
public import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
public import VCVio.OracleComp.SimSemantics.QueryImpl.Compose

/-!
# Rounds of parallel oracle queries

A round of parallel queries to `spec` is a list of points `ts : List ι`, submitted at once and
answered by one answer per point. `OracleSpec.batch spec` is the oracle specification whose
queries are such rounds: its answer to `ts` is a dependent tuple
`(j : Fin ts.length) → spec.Range ts[j]`, so points of oracles with different answer types share
one round. A round-structured computation is an ordinary `OracleComp` over `free + spec.batch`,
where the summand `free` holds the oracles that cost no round (local coins `unifSpec`, or a
challenger's oracle), and counting its rounds is an ordinary path-wise query bound
(`VCVio/OracleComp/QueryTracking/QueryBound/Batch.lean`).

## Main definitions

* `OracleSpec.batch`: rounds of parallel queries to `spec`.
* `QueryImpl.batch`: answer a round point by point, in order.
* `QueryImpl.batch'`: extend a handler of `free + spec` to `free + spec.batch`, answering queries
  to `free` as before and rounds point by point.
* `OracleSpec.unbatch`: rewrite each round as the sequence of its single queries.
* `OracleSpec.SubSpec.batch`: a `SubSpec` inclusion lifted through `batch`.
* `OracleComp.queryRound₂`, `OracleComp.queryRound`, `OracleComp.queryPoint`: rounds whose
  points are given by functions on `Fin k`, with their answers returned as dependent families
  (`OracleSpec.splitAnswers`).

## Main statements

* `QueryImpl.simulateQ_simulateQ_unbatch`: running a program with rounds through `unbatch` and
  then a handler is running it through the batched handler.
* `OracleSpec.simulateQ_romImpl_simulateQ_unbatch`: the corollary for the lazy random oracle.
* `QueryImpl.run_simulateQ_add_parallelStateT_batch_liftComp`: a program with rounds of `spec`,
  lifted to rounds of `spec + side` and answered by two handlers side by side, runs against the
  first handler alone and leaves the state of the second unchanged.
* `QueryImpl.withCaching_batch_le_and_isSome_iff`: answering a round with a caching handler caches
  exactly its points, beside the points cached before.
* `OracleComp.simulateQ_queryRound₂`, `OracleComp.simulateQ_queryRound`,
  `OracleComp.simulateQ_queryPoint`: against a fixed answer table, a round returns the table's
  answers at its points.
-/

public section

open OracleSpec OracleComp

universe u v w

open scoped OracleSpec.PrimitiveQuery

namespace OracleSpec

variable {ι : Type u}

/-- One round of parallel queries to `spec`: a list of points `ts`, answered by one answer per
point, the answer at position `j` lying in `spec.Range ts[j]`. -/
@[expose]
def batch (spec : OracleSpec.{u, v} ι) : OracleSpec.{u, v} (List ι) :=
  fun ts => (j : Fin ts.length) → spec.Range ts[j]

variable {spec : OracleSpec.{u, v} ι}

lemma batch_apply (ts : List ι) :
    spec.batch ts = ((j : Fin ts.length) → spec.Range ts[j]) := rfl

lemma batch_range (ts : List ι) :
    spec.batch.Range ts = ((j : Fin ts.length) → spec.Range ts[j]) := rfl

/-! ## Answers to a round

These instances are indexed on the `batch` head, so they apply only to answers of rounds. -/

instance [∀ t, DecidableEq (spec.Range t)] (ts : List ι) :
    DecidableEq (spec.batch.Range ts) :=
  inferInstanceAs (DecidableEq ((j : Fin ts.length) → spec.Range ts[j]))

instance [∀ t, Fintype (spec.Range t)] (ts : List ι) :
    Fintype (spec.batch.Range ts) :=
  inferInstanceAs (Fintype ((j : Fin ts.length) → spec.Range ts[j]))

instance [∀ t, Inhabited (spec.Range t)] (ts : List ι) :
    Inhabited (spec.batch.Range ts) :=
  inferInstanceAs (Inhabited ((j : Fin ts.length) → spec.Range ts[j]))

/-- The answer to the empty round. -/
@[expose]
def batchNil : spec.batch.Range [] := fun j => j.elim0

/-- The answer to the round `t :: ts` made of an answer `u` at `t` and an answer `us` to `ts`. -/
@[expose]
def batchCons {t : ι} {ts : List ι} (u : spec.Range t) (us : spec.batch.Range ts) :
    spec.batch.Range (t :: ts) :=
  Fin.cons (α := fun j : Fin (ts.length + 1) => spec.Range (t :: ts)[j]) u us

@[simp] lemma batchCons_zero {t : ι} {ts : List ι} (u : spec.Range t)
    (us : spec.batch.Range ts) :
    batchCons u us (0 : Fin (ts.length + 1)) = u := rfl

@[simp] lemma batchCons_succ {t : ι} {ts : List ι} (u : spec.Range t)
    (us : spec.batch.Range ts) (j : Fin ts.length) :
    batchCons u us j.succ = us j := rfl

@[simp] lemma batchCons_mk_succ {t : ι} {ts : List ι} (u : spec.Range t)
    (us : spec.batch.Range ts) (j : ℕ) (hj : j + 1 < (t :: ts).length) :
    batchCons u us ⟨j + 1, hj⟩ = us ⟨j, Nat.lt_of_succ_lt_succ hj⟩ := rfl

/-- Every answer to the empty round is `batchNil`. -/
lemma eq_batchNil (us : spec.batch.Range []) : us = batchNil :=
  funext fun j => j.elim0

/-- Every answer to a nonempty round is `batchCons` of its head and its tail. -/
lemma eq_batchCons {t : ι} {ts : List ι} (us : spec.batch.Range (t :: ts)) :
    us = batchCons (us ⟨0, Nat.zero_lt_succ _⟩) (fun j => us j.succ) :=
  funext fun j => Fin.cases rfl (fun _ => rfl) j

end OracleSpec

namespace QueryImpl

variable {ι : Type u} {spec : OracleSpec.{u, v} ι} {m : Type v → Type w}

/-- Answer a round point by point, in the order of its list. -/
@[expose]
def batch [Monad m] (impl : QueryImpl spec m) : QueryImpl spec.batch m
  | [] => pure batchNil
  | t :: ts => do
      let u ← impl t
      let us ← impl.batch ts
      pure (batchCons u us)

@[simp] lemma batch_nil [Monad m] (impl : QueryImpl spec m) :
    impl.batch [] = pure batchNil := rfl

@[simp] lemma batch_cons [Monad m] (impl : QueryImpl spec m) (t : ι) (ts : List ι) :
    impl.batch (t :: ts) = (do
      let u ← impl t
      let us ← impl.batch ts
      pure (batchCons u us)) := rfl

/-- A deterministic handler answers each point of a round by itself. -/
@[simp] lemma batch_id_apply (impl : QueryImpl spec Id) (ts : List ι) (j : Fin ts.length) :
    (impl.batch ts).run j = (impl ts[j]).run := by
  induction ts with
  | nil => exact j.elim0
  | cons t ts ih => cases j using Fin.cases with
    | zero => rfl
    | succ j => exact ih j

/-- Running the programs of `so` under `so'`, round by round, is batching the composite. -/
lemma compose_batch {ι' : Type*} {spec' : OracleSpec ι'} {m : Type v → Type w} [Monad m]
    [LawfulMonad m] (so' : QueryImpl spec' m) (so : QueryImpl spec (OracleComp spec')) :
    so' ∘ₛ so.batch = (so' ∘ₛ so).batch := by
  funext ts
  induction ts with
  | nil => simp
  | cons t ts ih => simp [← ih]

/-- A handler lifted into `StateT σ m` answers a round without touching the state: the round is
answered by `impl`, and the initial state is returned unchanged. -/
lemma run_batch_liftTarget [Monad m] [LawfulMonad m] {σ : Type v} (impl : QueryImpl spec m)
    (ts : List ι) (s : σ) :
    ((impl.liftTarget (StateT σ m)).batch ts).run s = (·, s) <$> impl.batch ts := by
  induction ts with
  | nil => simp
  | cons t ts ih => simp [StateT.run_bind, ih, map_eq_bind_pure_comp]

section batch'

variable {τ ι : Type} {free : OracleSpec.{0, 0} τ} {spec : OracleSpec.{0, 0} ι}
  {m : Type → Type w} [Monad m]

/-- Extend a handler of `free + spec` to rounds: queries to `free` are answered as `impl` answers
them, and a round is answered point by point by `impl`. -/
@[expose]
def batch' (impl : QueryImpl (free + spec) m) : QueryImpl (free + spec.batch) m :=
  QueryImpl.add (fun n => impl (.inl n)) (QueryImpl.batch fun t => impl (.inr t))

@[simp] lemma batch'_apply_inl (impl : QueryImpl (free + spec) m) (n : τ) :
    impl.batch' (.inl n) = impl (.inl n) := rfl

@[simp] lemma batch'_apply_inr (impl : QueryImpl (free + spec) m) (ts : List ι) :
    impl.batch' (.inr ts) = QueryImpl.batch (fun t => impl (.inr t)) ts := rfl

/-- The batched form of a sum handler batches its right summand. -/
@[simp] lemma batch'_add (impl₁ : QueryImpl free m) (impl₂ : QueryImpl spec m) :
    (impl₁ + impl₂).batch' = impl₁ + impl₂.batch := rfl

end batch'

end QueryImpl

namespace OracleSpec

variable {τ ι : Type} (spec : OracleSpec.{0, 0} ι) {free : OracleSpec.{0, 0} τ}

/-- Rewrite each round as the sequence of its single queries, in order; queries to the summand
`free` pass through unchanged. -/
@[expose]
def unbatch : QueryImpl (free + spec.batch) (OracleComp (free + spec)) :=
  QueryImpl.batch' fun t => liftM ((free + spec).query t)

variable {spec}

@[simp] lemma unbatch_apply_inl (n : τ) :
    spec.unbatch (.inl n) = liftM ((free + spec).query (.inl n)) := rfl

@[simp] lemma unbatch_apply_inr (ts : List ι) :
    spec.unbatch (free := free) (.inr ts) =
      QueryImpl.batch (fun t => liftM ((free + spec).query (.inr t))) ts := rfl

end OracleSpec

namespace QueryImpl

variable {τ ι : Type} {free : OracleSpec.{0, 0} τ} {spec : OracleSpec.{0, 0} ι}
  {m : Type → Type w} [Monad m] [LawfulMonad m]

/-- Running a program with rounds through `unbatch` and then `impl` is running it through the
batched handler `impl.batch'`. -/
theorem simulateQ_simulateQ_unbatch (impl : QueryImpl (free + spec) m) {α : Type}
    (oa : OracleComp (free + spec.batch) α) :
    simulateQ impl (simulateQ spec.unbatch oa) = simulateQ impl.batch' oa := by
  refine simulateQ_simulateQ_eq_of_apply (fun t => ?_) oa
  rcases t with n | ts
  · exact simulateQ_spec_query impl (.inl n)
  · change (impl ∘ₛ QueryImpl.batch _) ts = _
    rw [compose_batch]
    congr 1
    funext t
    exact simulateQ_spec_query impl (.inr t)

end QueryImpl

namespace OracleSpec

variable {ι : Type} {hashSpec : OracleSpec.{0, 0} ι} [DecidableEq ι]
  [∀ t : hashSpec.Domain, SampleableType (hashSpec.Range t)]

/-- In the random oracle model, running a program with rounds through `unbatch` is answering
uniform queries by sampling and each round point by point by the lazy random oracle, on one
shared cache. -/
theorem simulateQ_romImpl_simulateQ_unbatch {α : Type}
    (oa : OracleComp (unifSpec + hashSpec.batch) α) :
    simulateQ hashSpec.romImpl (simulateQ hashSpec.unbatch oa) =
      simulateQ (unifFwdImpl hashSpec + hashSpec.randomOracle.batch) oa :=
  QueryImpl.simulateQ_simulateQ_unbatch _ oa

end OracleSpec

namespace QueryImpl

variable {ι : Type} [DecidableEq ι] {spec : OracleSpec.{0, 0} ι} {m : Type → Type w} [Monad m]
  [LawfulMonad m] [MonadAttach m] [ExactMonadAttach m]

/-- Answering a round `ts` point by point with `so.withCaching` only extends the cache, and caches
exactly the points cached before or listed in `ts`. -/
lemma withCaching_batch_le_and_isSome_iff (so : QueryImpl spec m) {ts : List ι}
    {cache₀ : spec.QueryCache} {z : spec.batch.Range ts × spec.QueryCache}
    (hz : z ∈ support ((so.withCaching.batch ts).run cache₀)) :
    cache₀ ≤ z.2 ∧ ∀ t, (z.2 t).isSome ↔ (cache₀ t).isSome ∨ t ∈ ts := by
  induction ts generalizing cache₀ with
  | nil =>
    simp only [batch_nil, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    simp
  | cons t ts ih =>
    simp only [batch_cons, StateT.run_bind, StateT.run_pure, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at hz
    obtain ⟨y, hy, w, hw, rfl⟩ := hz
    obtain ⟨hle, hiff⟩ := ih hw
    refine ⟨(withCaching_cache_le so _ _ _ hy).trans hle, fun t' => ?_⟩
    rw [hiff, withCaching_run_isSome_apply_iff so hy, List.mem_cons]
    tauto

end QueryImpl

namespace OracleSpec.SubSpec

variable {ι : Type u} {τ : Type v} {spec : OracleSpec.{u, w} ι} {superSpec : OracleSpec.{v, w} τ}

/-- The answer translation of `SubSpec.batch`: translate the answer at each point by
`h.onResponse`. -/
@[expose]
def batchOnResponse (h : spec ⊂ₒ superSpec) :
    (ts : List ι) → superSpec.batch.Range (ts.map h.onQuery) → spec.batch.Range ts
  | [], _ => batchNil
  | t :: ts, us =>
      batchCons (h.onResponse t (us ⟨0, Nat.zero_lt_succ _⟩))
        (batchOnResponse h ts fun j => us j.succ)

/-- The translated answer at position `j` is `h.onResponse` of the answer at the matching
position of the translated round. -/
lemma batchOnResponse_apply (h : spec ⊂ₒ superSpec) (ts : List ι)
    (us : superSpec.batch.Range (ts.map h.onQuery)) (j : Fin ts.length) :
    batchOnResponse h ts us j =
      h.onResponse ts[j] (cast (by simp) (us ⟨j, by simp⟩)) := by
  induction ts with
  | nil => exact j.elim0
  | cons t ts ih => cases j using Fin.cases with
    | zero => rfl
    | succ j => exact ih _ j

/-- A `SubSpec` inclusion lifted through `batch`: a round `ts` becomes the round of translated
points `ts.map h.onQuery`, and its answer is translated point by point. -/
@[expose, reducible]
def batch (h : spec ⊂ₒ superSpec) : spec.batch ⊂ₒ superSpec.batch where
  monadLift q := ⟨q.input.map h.onQuery, q.cont ∘ batchOnResponse h q.input⟩
  onQuery ts := ts.map h.onQuery
  onResponse := batchOnResponse h

instance [h : spec ⊂ₒ superSpec] : spec.batch ⊂ₒ superSpec.batch := SubSpec.batch h

@[simp] lemma batch_onQuery (h : spec ⊂ₒ superSpec) (ts : List ι) :
    (SubSpec.batch h).onQuery ts = ts.map h.onQuery := rfl

@[simp] lemma batch_onResponse (h : spec ⊂ₒ superSpec) :
    (SubSpec.batch h).onResponse = batchOnResponse h := rfl

/-- Lifting through `batch` keeps response translations bijective. -/
instance [h : spec ⊂ₒ superSpec] [LawfulSubSpec spec superSpec] :
    LawfulSubSpec spec.batch superSpec.batch where
  onResponse_bijective ts := by
    induction ts with
    | nil =>
        refine ⟨fun _ _ _ => funext fun j => j.elim0, fun us => ⟨batchNil, ?_⟩⟩
        exact funext fun j => j.elim0
    | cons t ts ih =>
        obtain ⟨hinj, hsurj⟩ := LawfulSubSpec.onResponse_bijective (spec := spec)
          (superSpec := superSpec) t
        refine ⟨fun us vs huv => ?_, fun ws => ?_⟩
        · rw [eq_batchCons us, eq_batchCons vs]
          have h0 := congrFun huv ⟨0, Nat.zero_lt_succ _⟩
          have hs := fun j : Fin ts.length => congrFun huv j.succ
          change h.onResponse t _ = h.onResponse t _ at h0
          rw [hinj h0]
          congr 1
          funext j
          exact congrFun (ih.1 (funext hs)) j
        · obtain ⟨u, hu⟩ := hsurj (ws ⟨0, Nat.zero_lt_succ _⟩)
          obtain ⟨us, hus⟩ := ih.2 fun j => ws j.succ
          refine ⟨batchCons u us, funext fun j => Fin.cases ?_ (fun j => ?_) j⟩
          · exact hu
          · exact congrFun hus j

end OracleSpec.SubSpec

/-! ### Lifted rounds against handlers side by side -/

namespace QueryImpl

variable {ι ι' σ₁ σ₂ : Type} {spec : OracleSpec.{0, 0} ι} {side : OracleSpec.{0, 0} ι'}
  {m : Type → Type w} [Monad m] [LawfulMonad m]

/-- A round of `spec`, lifted to the round of `spec + side` at its translated points and answered
point by point by `impl₁` and `impl₂` side by side, is answered by `impl₁` and leaves the state of
`impl₂` unchanged. -/
lemma run_batchOnResponse_map_batch_parallelStateT (impl₁ : QueryImpl spec (StateT σ₁ m))
    (impl₂ : QueryImpl side (StateT σ₂ m)) (ts : List ι) (s₁ : σ₁) (s₂ : σ₂) :
    (SubSpec.batchOnResponse (inferInstance : spec ⊂ₒ (spec + side)) ts <$>
        (parallelStateT impl₁ impl₂).batch (ts.map Sum.inl)).run (s₁, s₂) =
      Prod.map id (·, s₂) <$> (impl₁.batch ts).run s₁ := by
  induction ts generalizing s₁ with
  | nil =>
    change (SubSpec.batchOnResponse (inferInstance : spec ⊂ₒ (spec + side)) [] <$>
      (pure batchNil : StateT (σ₁ × σ₂) m ((spec + side).batch.Range []))).run (s₁, s₂) = _
    simp [SubSpec.batchOnResponse, eq_batchNil]
  | cons t ts ih =>
    have ih' := fun s₁ => (StateT.run_map _ _ _).symm.trans (ih s₁)
    change (SubSpec.batchOnResponse (inferInstance : spec ⊂ₒ (spec + side)) (t :: ts) <$> (do
      let u ← parallelStateT impl₁ impl₂ (.inl t)
      let us ← (parallelStateT impl₁ impl₂).batch (ts.map Sum.inl)
      pure (batchCons (spec := spec + side) (t := Sum.inl t) (ts := ts.map Sum.inl) u us))).run
        (s₁, s₂) = _
    simp only [map_bind, StateT.run_bind, QueryImpl.batch_cons, map_pure, StateT.run_pure]
    rw [show (parallelStateT impl₁ impl₂ (.inl t)).run (s₁, s₂) =
      Prod.map id (·, s₂) <$> (impl₁ t).run s₁ from rfl, bind_map_left]
    refine bind_congr fun a => ?_
    simp only [bind_pure_comp]
    have h := congrArg ((fun q => (batchCons (spec := spec) (t := t) a.1 q.1, q.2)) <$> ·)
      (ih' a.2)
    simp only [Functor.map_map] at h
    exact h

/-- **A lifted program against handlers side by side.** A program with rounds of `spec`, lifted to
rounds of `spec + side` and run with queries to `free` answered by `base` and rounds answered
point by point by `impl₁` and `impl₂` side by side, runs as against `base` and `impl₁` alone and
leaves the state of `impl₂` unchanged. -/
theorem run_simulateQ_add_parallelStateT_batch_liftComp {τ : Type} {free : OracleSpec.{0, 0} τ}
    (base : QueryImpl free m) (impl₁ : QueryImpl spec (StateT σ₁ m))
    (impl₂ : QueryImpl side (StateT σ₂ m)) {α : Type} (oa : OracleComp (free + spec.batch) α)
    (s₁ : σ₁) (s₂ : σ₂) :
    (simulateQ (base.liftTarget (StateT (σ₁ × σ₂) m) + (parallelStateT impl₁ impl₂).batch)
        (liftComp oa (free + (spec + side).batch))).run (s₁, s₂) =
      Prod.map id (·, s₂) <$>
        (simulateQ (base.liftTarget (StateT σ₁ m) + impl₁.batch) oa).run s₁ := by
  rw [liftComp_def, ← QueryImpl.simulateQ_compose]
  refine (map_run_simulateQ_eq_of_query_map_eq _ _ (·, s₂) (fun t s₁ => ?_) oa s₁).symm
  rcases t with n | ts
  · simp only [QueryImpl.apply_compose]
    rw [liftM_eq_liftM_liftM, OracleQuery.liftM_right_add_right_add_query]
    simp
  · simp only [QueryImpl.apply_compose]
    rw [liftM_eq_liftM_liftM, OracleQuery.liftM_right_add_right_add_query]
    simp only [simulateQ_query]
    change _ = (SubSpec.batchOnResponse (inferInstance : spec ⊂ₒ (spec + side)) ts <$>
      (parallelStateT impl₁ impl₂).batch (ts.map Sum.inl)).run (s₁, s₂)
    rw [run_batchOnResponse_map_batch_parallelStateT]
    rfl

end QueryImpl

/-! ## Rounds with typed answers

A round whose points are given by functions `p : Fin k → ι` and `q : Fin l → ι` returns its
answers as two dependent families, so that the answer at `p j` has type `spec.Range (p j)`, which
reduces when `p j` is a constructor application. -/

namespace OracleSpec

variable {ι : Type u} {spec : OracleSpec.{u, v} ι}

/-- Split the answer to the round `List.ofFn p ++ List.ofFn q` into the answers at the points
`p j` and the answers at the points `q j`. -/
@[expose]
def splitAnswers {k l : ℕ} (p : Fin k → ι) (q : Fin l → ι)
    (us : spec.batch.Range (List.ofFn p ++ List.ofFn q)) :
    ((j : Fin k) → spec.Range (p j)) × ((j : Fin l) → spec.Range (q j)) :=
  (fun j => cast (by simp) (us ⟨j, by simp; omega⟩),
    fun j => cast (by simp) (us ⟨k + j, by simp⟩))

end OracleSpec

namespace OracleComp

variable {τ ι : Type} {free : OracleSpec.{0, 0} τ} {spec : OracleSpec.{0, 0} ι}

/-- One round holding the points `p j`, then the points `q j`; the answers are returned as two
families. The oracles `free` beside the rounds are not queried. -/
@[expose]
def queryRound₂ {k l : ℕ} (p : Fin k → ι) (q : Fin l → ι) :
    OracleComp (free + spec.batch)
      (((j : Fin k) → spec.Range (p j)) × ((j : Fin l) → spec.Range (q j))) :=
  splitAnswers p q <$>
    liftM ((free + spec.batch).query (.inr (List.ofFn p ++ List.ofFn q)))

/-- One round holding the points `p j`. -/
@[expose]
def queryRound {k : ℕ} (p : Fin k → ι) :
    OracleComp (free + spec.batch) ((j : Fin k) → spec.Range (p j)) :=
  Prod.fst <$> queryRound₂ p (Fin.elim0 : Fin 0 → ι)

/-- One round holding the single point `t`. -/
@[expose]
def queryPoint (t : ι) : OracleComp (free + spec.batch) (spec.Range t) :=
  (fun us => us 0) <$> queryRound (fun _ : Fin 1 => t)

end OracleComp

/-! ### Rounds against a fixed answer table -/

namespace QueryImpl

variable {ι : Type} {spec : OracleSpec.{0, 0} ι}

/-- Answering each point of a round from the table `f` answers the round with `f` pointwise. -/
lemma batch_unifFwdAnswerImpl (f : QueryImpl spec Id) (ts : List ι) :
    QueryImpl.batch (fun t => unifFwdAnswerImpl f (.inr t)) ts =
      (pure (fun j => (f ts[j]).run) : ProbComp (spec.batch.Range ts)) := by
  induction ts with
  | nil =>
      rw [QueryImpl.batch_nil]
      exact congrArg (pure : _ → ProbComp _) (funext fun j => j.elim0)
  | cons t ts ih =>
      rw [QueryImpl.batch_cons, ih]
      change (pure (f t).run >>= fun u => pure (batchCons u _) : ProbComp _) = _
      rw [pure_bind]
      exact congrArg (pure : _ → ProbComp _) (funext fun j => Fin.cases rfl (fun _ => rfl) j)

end QueryImpl

namespace OracleComp

variable {ι : Type} {spec : OracleSpec.{0, 0} ι}

private lemma cast_run_of_eq (f : QueryImpl spec Id) {a b : ι} (hab : a = b)
    (h : spec.Range a = spec.Range b) : cast h (f a).run = (f b).run := by
  subst hab
  rfl

private lemma splitAnswers_table (f : QueryImpl spec Id) {k l : ℕ} (p : Fin k → ι)
    (q : Fin l → ι) :
    splitAnswers p q (fun j => (f (List.ofFn p ++ List.ofFn q)[j]).run) =
      (fun j => (f (p j)).run, fun j => (f (q j)).run) := by
  simp only [splitAnswers]
  congr 1 <;> funext j <;> exact cast_run_of_eq f (by simp) _

/-- Against the fixed table `f`, the round `queryRound₂ p q` returns the table's answers at the
points `p j` and `q j`. -/
@[simp] lemma simulateQ_queryRound₂ (f : QueryImpl spec Id) {k l : ℕ} (p : Fin k → ι)
    (q : Fin l → ι) :
    simulateQ (unifFwdAnswerImpl f).batch' (queryRound₂ p q) =
      pure (fun j => (f (p j)).run, fun j => (f (q j)).run) := by
  rw [queryRound₂, simulateQ_map, simulateQ_spec_query, QueryImpl.batch'_apply_inr,
    QueryImpl.batch_unifFwdAnswerImpl]
  exact (map_pure _ _).trans (congrArg pure (splitAnswers_table f p q))

/-- Against the fixed table `f`, the round `queryRound p` returns the table's answers at the points
`p j`. -/
@[simp] lemma simulateQ_queryRound (f : QueryImpl spec Id) {k : ℕ} (p : Fin k → ι) :
    simulateQ (unifFwdAnswerImpl f).batch' (queryRound p) = pure (fun j => (f (p j)).run) := by
  rw [queryRound, simulateQ_map, simulateQ_queryRound₂, map_pure]

/-- Against the fixed table `f`, the single-point round `queryPoint t` returns the table's answer
at `t`. -/
@[simp] lemma simulateQ_queryPoint (f : QueryImpl spec Id) (t : ι) :
    simulateQ (unifFwdAnswerImpl f).batch' (queryPoint t) = pure (f t).run := by
  rw [queryPoint, simulateQ_map, simulateQ_queryRound, map_pure]

end OracleComp

namespace QueryImpl

variable {ι : Type} [DecidableEq ι] {spec : OracleSpec.{0, 0} ι} {m : Type → Type w} [Monad m]
  [LawfulMonad m]

/-- A map `g` of caches that, at every point satisfying `P`, leaves the entry unchanged and
commutes with caching an answer commutes with answering a round `ts` of points satisfying `P` with
`so.withCaching`: running the round and mapping the final cache through `g` is running the round
from the mapped cache. -/
lemma map_withCaching_batch_run_of_commute (so : QueryImpl spec m) {P : ι → Prop}
    (g : spec.QueryCache → spec.QueryCache) (h₁ : ∀ cache t, P t → g cache t = cache t)
    (h₂ : ∀ cache t u, P t → g (cache.cacheQuery t u) = (g cache).cacheQuery t u)
    {ts : List ι} (hts : ∀ t ∈ ts, P t) (cache : spec.QueryCache) :
    Prod.map id g <$> (so.withCaching.batch ts).run cache =
      (so.withCaching.batch ts).run (g cache) := by
  induction ts generalizing cache with
  | nil => simp
  | cons t ts ih =>
    have ht := hts t List.mem_cons_self
    simp only [batch_cons, StateT.run_bind, StateT.run_pure, map_bind, map_pure]
    rw [← map_withCaching_run_of_commute so g (h₁ cache t ht) (fun u => h₂ cache t u ht),
      bind_map_left]
    refine bind_congr fun z => ?_
    simp only [Prod.map_fst, Prod.map_snd, id_eq]
    rw [← ih (fun t' ht' => hts t' (List.mem_cons_of_mem _ ht')), bind_map_left]
    rfl

end QueryImpl
