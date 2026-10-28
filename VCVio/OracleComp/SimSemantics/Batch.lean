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
one round. A round-structured computation is an ordinary `OracleComp` over `unifSpec + spec.batch`,
and counting its rounds is an ordinary path-wise query bound
(`VCVio/OracleComp/QueryTracking/QueryBound/Batch.lean`).

## Main definitions

* `OracleSpec.batch`: rounds of parallel queries to `spec`.
* `QueryImpl.batch`: answer a round point by point, in order.
* `QueryImpl.batch'`: extend a handler of `unifSpec + spec` to `unifSpec + spec.batch`, answering
  uniform queries as before and rounds point by point.
* `OracleSpec.unbatch`: rewrite each round as the sequence of its single queries.
* `OracleSpec.SubSpec.batch`: a `SubSpec` inclusion lifted through `batch`.

## Main statements

* `QueryImpl.simulateQ_simulateQ_unbatch`: running a program with rounds through `unbatch` and
  then a handler is running it through the batched handler.
* `OracleSpec.simulateQ_romImpl_simulateQ_unbatch`: the corollary for the lazy random oracle.
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

/-- Extend a handler of `unifSpec + spec` to rounds: uniform queries are answered as `impl`
answers them, and a round is answered point by point by `impl`. -/
@[expose]
def batch' {ι : Type} {spec : OracleSpec.{0, 0} ι} {m : Type → Type w} [Monad m]
    (impl : QueryImpl (unifSpec + spec) m) : QueryImpl (unifSpec + spec.batch) m :=
  QueryImpl.add (fun n => impl (.inl n)) (QueryImpl.batch fun t => impl (.inr t))

@[simp] lemma batch'_apply_inl {ι : Type} {spec : OracleSpec.{0, 0} ι} {m : Type → Type w}
    [Monad m] (impl : QueryImpl (unifSpec + spec) m) (n : ℕ) :
    impl.batch' (.inl n) = impl (.inl n) := rfl

@[simp] lemma batch'_apply_inr {ι : Type} {spec : OracleSpec.{0, 0} ι} {m : Type → Type w}
    [Monad m] (impl : QueryImpl (unifSpec + spec) m) (ts : List ι) :
    impl.batch' (.inr ts) = QueryImpl.batch (fun t => impl (.inr t)) ts := rfl

/-- The batched form of a sum handler batches its right summand. -/
@[simp] lemma batch'_add {ι : Type} {spec : OracleSpec.{0, 0} ι} {m : Type → Type w}
    [Monad m] (impl₁ : QueryImpl unifSpec m) (impl₂ : QueryImpl spec m) :
    (impl₁ + impl₂).batch' = impl₁ + impl₂.batch := rfl

end QueryImpl

namespace OracleSpec

variable {ι : Type} (spec : OracleSpec.{0, 0} ι)

/-- Rewrite each round as the sequence of its single queries, in order; uniform queries pass
through unchanged. -/
@[expose]
def unbatch : QueryImpl (unifSpec + spec.batch) (OracleComp (unifSpec + spec)) :=
  QueryImpl.batch' fun t => liftM ((unifSpec + spec).query t)

variable {spec}

@[simp] lemma unbatch_apply_inl (n : ℕ) :
    spec.unbatch (.inl n) = liftM ((unifSpec + spec).query (.inl n)) := rfl

@[simp] lemma unbatch_apply_inr (ts : List ι) :
    spec.unbatch (.inr ts) =
      QueryImpl.batch (fun t => liftM ((unifSpec + spec).query (.inr t))) ts := rfl

end OracleSpec

namespace QueryImpl

variable {ι : Type} {spec : OracleSpec.{0, 0} ι} {m : Type → Type w} [Monad m] [LawfulMonad m]

/-- Running a program with rounds through `unbatch` and then `impl` is running it through the
batched handler `impl.batch'`. -/
theorem simulateQ_simulateQ_unbatch (impl : QueryImpl (unifSpec + spec) m) {α : Type}
    (oa : OracleComp (unifSpec + spec.batch) α) :
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
