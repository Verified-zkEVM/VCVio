/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.Encoded
public import VCVio.OracleComp.QueryTracking.QueryBound.Batch

/-!
# Rounds through a random-oracle encoding

A `RandomOracleEncoding spec D M` answers the typed oracles `spec` by one raw oracle `D →ₒ M`
(`VCVio/OracleComp/QueryTracking/RandomOracle/Encoded.lean`). This file carries the encoding over
to rounds of parallel queries, in both directions.

* From typed to raw, `roundImpl` sends a typed round to the raw round of the encodings of its
  points and truncates every answer (`truncRound`). A puzzle written against the typed oracles
  runs against the raw oracle this way.
* From raw to typed, a raw program runs against the typed oracles by routing each raw input.
  `preprocessImpl` answers one raw query and `onlineImpl` one raw round. Every raw input first draws
  a private value from a lazy random oracle whose cache is the handler's state. The inputs that
  encode a typed point are then submitted to the typed oracles, in the online phase as one typed
  round, and `assemble` completes each typed answer with the private value at its input. A raw
  input that encodes no typed point is answered by its private value. A raw round therefore costs
  at most one typed round, of at most as many points.

`rawLift` and `typedLift` place the raw and the typed interfaces inside the combined interface
`unifSpec + (spec + (D →ₒ M))`, where `RandomOracleEncoding.encodeImpl` gives the single-oracle
world and `RandomOracleEncoding.typedImpl` the typed world.

## Main statements

* `isQueryBoundP_preprocessImpl`, `isOnlineQueryBound_onlineImpl`: a raw query costs at most one
  typed query, and a raw round at most one typed round with at most as many points.
* `encodeImpl_compose_typedLift_batch'`: the typed interface encoded into the raw oracle, round by
  round, is `roundImpl` followed by unbatching.
* `preprocessImpl_run_step`, `onlineImpl_run_step`: in the typed world, a step of the routing
  handler is the typed world's answer to the raw query or round, with the private cache as the
  state of the raw inputs.
* `batch_typedHashImpl_run`: a raw round answered input by input in the typed world is equal in
  distribution to drawing all private values first, then the typed round of the encoded points,
  and reassembling.
-/

public section

open OracleSpec OracleComp

namespace OracleComp.RandomOracleEncoding

variable {ι D M : Type} {spec : OracleSpec.{0, 0} ι} [SampleableType M]
  [∀ t, SampleableType (spec.Range t)] (E : RandomOracleEncoding spec D M)

/-! ## Reassembling a raw round -/

/-- The answers to a raw round reassembled from the private values `ps` at its inputs and the
answers `us` to the round of the typed points they encode: at an encoding, the typed answer
completed from the private value, and elsewhere the private value. -/
@[expose]
def assemble : (xs : List D) → (D →ₒ M).batch.Range xs →
    spec.batch.Range (xs.filterMap E.route) → (D →ₒ M).batch.Range xs
  | [], _, _ => batchNil
  | x :: xs, ps, us =>
      match hx : E.route x with
      | none =>
          batchCons (ps ⟨0, by simp⟩) (assemble xs (fun j => ps j.succ)
            (cast (by rw [List.filterMap_cons_none hx]) us))
      | some q =>
          let us' : spec.batch.Range (q :: xs.filterMap E.route) :=
            cast (by rw [List.filterMap_cons_some hx]) us
          batchCons (E.complete q (us' ⟨0, by simp⟩) (ps ⟨0, by simp⟩))
            (assemble xs (fun j => ps j.succ) (fun j => us' j.succ))

lemma assemble_cons_none {x : D} {xs : List D} (hx : E.route x = none)
    (ps : (D →ₒ M).batch.Range (x :: xs)) (us : spec.batch.Range ((x :: xs).filterMap E.route)) :
    E.assemble (x :: xs) ps us = batchCons (ps ⟨0, by simp⟩)
      (E.assemble xs (fun j => ps j.succ) (cast (by rw [List.filterMap_cons_none hx]) us)) := by
  rw [assemble]
  split
  · rfl
  · rename_i heq
    simp [hx] at heq

lemma assemble_cons_some {x : D} {xs : List D} {q : ι} (hx : E.route x = some q)
    (ps : (D →ₒ M).batch.Range (x :: xs)) (us : spec.batch.Range (q :: xs.filterMap E.route)) :
    E.assemble (x :: xs) ps (cast (by rw [List.filterMap_cons_some hx]) us) =
      batchCons (E.complete q (us ⟨0, by simp⟩) (ps ⟨0, by simp⟩))
        (E.assemble xs (fun j => ps j.succ) (fun j => us j.succ)) := by
  rw [assemble]
  split
  · rename_i heq
    simp [hx] at heq
  · rename_i q' hx'
    obtain rfl : q' = q := Option.some_injective _ (hx'.symm.trans hx)
    simp

section adapter

variable [DecidableEq D]

/-! ## Routing raw queries to the typed oracles -/

/-- The private lazy random oracle of the adapter at a raw input, flipping local coins of the
typed program. -/
@[expose]
def privateDraw {τ : Type} {spec' : OracleSpec.{0, 0} τ} [MonadLiftT ProbComp (OracleComp spec')]
    (x : D) : StateT (D →ₒ M).QueryCache (OracleComp spec') M :=
  StateT.mk fun pv => liftM (((D →ₒ M).randomOracle x).run pv)

/-- The private lazy random oracle of the adapter at every raw input of a round, in order. -/
@[expose]
def privateDraws {τ : Type} {spec' : OracleSpec.{0, 0} τ} [MonadLiftT ProbComp (OracleComp spec')]
    (xs : List D) : StateT (D →ₒ M).QueryCache (OracleComp spec') ((D →ₒ M).batch.Range xs) :=
  StateT.mk fun pv => liftM (((D →ₒ M).randomOracle.batch xs).run pv)

/-- The preprocessing step of the adapter: a raw input draws its private value; if it is the
encoding of a typed point, the answer is the typed answer there completed from the private value,
and otherwise it is the private value. Uniform queries pass through. -/
@[expose]
def preprocessImpl :
    QueryImpl (unifSpec + (D →ₒ M)) (StateT (D →ₒ M).QueryCache (OracleComp (unifSpec + spec)))
  | .inl k => StateT.lift (liftM ((unifSpec + spec).query (.inl k)))
  | .inr x => do
      let p ← privateDraw x
      match E.route x with
      | some q => (E.complete q · p) <$> StateT.lift (liftM ((unifSpec + spec).query (.inr q)))
      | none => pure p

/-- The online step of the adapter on a raw round: draw the private values of all its inputs,
submit the encoded typed points as one typed round, and reassemble the answers. Uniform queries
pass through. -/
@[expose]
def onlineImpl : QueryImpl (unifSpec + (D →ₒ M).batch)
    (StateT (D →ₒ M).QueryCache (OracleComp (unifSpec + spec.batch)))
  | .inl k => StateT.lift (liftM ((unifSpec + spec.batch).query (.inl k)))
  | .inr xs => do
      let ps ← privateDraws xs
      let us ← StateT.lift (liftM ((unifSpec + spec.batch).query (.inr (xs.filterMap E.route))))
      return E.assemble xs ps us

/-! ### Budgets -/

omit [∀ t, SampleableType (spec.Range t)] in
lemma isQueryBoundP_liftM_probComp {α : Type} (oa : ProbComp α) :
    IsQueryBoundP (liftM oa : OracleComp (unifSpec + spec) α) (·.isRight) 0 := by
  induction oa using OracleComp.inductionOn with
  | pure x => exact isQueryBoundP_pure _ _ _
  | query_bind t k ih =>
      change IsQueryBoundP (liftComp (liftM (unifSpec.query t) >>= k) (unifSpec + spec))
        (·.isRight) 0
      rw [liftComp_bind, liftComp_query]
      exact (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨by simp, fun u => by simpa using ih u⟩

lemma isQueryBoundP_preprocessImpl (t : (unifSpec + (D →ₒ M)).Domain)
    (s : (D →ₒ M).QueryCache) :
    IsQueryBoundP ((E.preprocessImpl t).run s) (·.isRight) (if t.isRight then 1 else 0) := by
  rcases t with k | x
  · simp only [preprocessImpl, Sum.isRight_inl, Bool.false_eq_true, ↓reduceIte]
    exact isQueryBoundP_bind_zero _ _ (by simp) fun _ => isQueryBoundP_pure _ _ _
  · simp only [preprocessImpl, Sum.isRight_inr, ↓reduceIte, StateT.run_bind]
    rw [← Nat.zero_add 1]
    refine isQueryBoundP_bind (isQueryBoundP_liftM_probComp _) fun z _ => ?_
    rcases E.route x with _ | q
    · exact (isQueryBoundP_pure _ _ _)
    · simp only [StateT.run_map, StateT.run_lift, isQueryBoundP_map_iff]
      rw [← Nat.add_zero 1]
      exact isQueryBoundP_bind (by simp) fun _ _ => isQueryBoundP_pure _ _ _

lemma isOnlineQueryBound_onlineImpl (t : (unifSpec + (D →ₒ M).batch).Domain)
    (s : (D →ₒ M).QueryCache) :
    IsOnlineQueryBound ((E.onlineImpl t).run s) (onlineStep t) := by
  rcases t with k | xs
  · simp only [onlineImpl, onlineStep_inl, StateT.run_lift]
    exact (isOnlineQueryBound_query_bind_inl_iff _ _ _).2 fun _ => isOnlineQueryBound_pure _ _
  · simp only [onlineImpl, onlineStep_inr, StateT.run_bind]
    refine isOnlineQueryBound_bind_le (0, 0) (1, xs.length) (isOnlineQueryBound_liftComp _ _)
      (fun z => ?_) ⟨by omega, by omega⟩
    rw [StateT.run_lift, bind_assoc]
    refine isOnlineQueryBound_bind_le (1, xs.length) (0, 0) ?_ (fun _ => ?_) ⟨le_rfl, le_rfl⟩
    · rw [IsOnlineQueryBound, isQueryBound_query_iff]
      simp [List.length_filterMap_le]
    · simp only [pure_bind, StateT.run_pure]
      exact isOnlineQueryBound_pure _ _

end adapter

/-! ## The combined interface and encoded rounds -/

/-- The raw interface as part of the combined interface of typed points and raw inputs. -/
@[expose]
def rawLift : QueryImpl (unifSpec + (D →ₒ M)) (OracleComp (unifSpec + (spec + (D →ₒ M))))
  | .inl n => liftM ((unifSpec + (spec + (D →ₒ M))).query (.inl n))
  | .inr x => liftM ((unifSpec + (spec + (D →ₒ M))).query (.inr (.inr x)))

/-- The typed interface as part of the combined interface of typed points and raw inputs. -/
@[expose]
def typedLift : QueryImpl (unifSpec + spec) (OracleComp (unifSpec + (spec + (D →ₒ M))))
  | .inl n => liftM ((unifSpec + (spec + (D →ₒ M))).query (.inl n))
  | .inr t => liftM ((unifSpec + (spec + (D →ₒ M))).query (.inr (.inl t)))

/-- The typed answers to a round read off the raw answers at the encodings of its points. -/
@[expose]
def truncRound (ts : List ι) (us : (D →ₒ M).batch.Range (ts.map E.encode)) :
    spec.batch.Range ts :=
  fun j => E.trunc ts[j] (us ⟨j, by simp⟩)

lemma truncRound_cons (t : ι) (ts : List ι) (u : M)
    (us : (D →ₒ M).batch.Range (ts.map E.encode)) :
    E.truncRound (t :: ts) (batchCons (t := E.encode t) u us) =
      batchCons (E.trunc t u) (E.truncRound ts us) := by
  funext j
  cases j using Fin.cases <;> rfl

/-- The encoding as a translation of rounds: a typed round is the raw round of the encodings of
its points, with every answer truncated. Uniform queries pass through. -/
@[expose]
def roundImpl : QueryImpl (unifSpec + spec.batch) (OracleComp (unifSpec + (D →ₒ M).batch))
  | .inl n => liftM ((unifSpec + (D →ₒ M).batch).query (.inl n))
  | .inr ts => E.truncRound ts <$>
      liftM ((unifSpec + (D →ₒ M).batch).query (.inr (ts.map E.encode)))

lemma simulateQ_encodeImpl_rawLift {α : Type} (oa : OracleComp (unifSpec + (D →ₒ M)) α) :
    simulateQ E.encodeImpl (simulateQ rawLift oa) = oa := by
  rw [QueryImpl.simulateQ_simulateQ_eq_of_apply (impl := QueryImpl.id' _) (fun t => ?_),
    simulateQ_id']
  rcases t with n | x <;> simp [rawLift, encodeImpl]

lemma batch_encodeImpl_typedLift (ts : List ι) :
    QueryImpl.batch (fun t => simulateQ E.encodeImpl (typedLift (.inr t))) ts =
      E.truncRound ts <$> QueryImpl.batch (spec := D →ₒ M)
        (fun x => liftM ((unifSpec + (D →ₒ M)).query (.inr x))) (ts.map E.encode) := by
  induction ts with
  | nil =>
    change _ = E.truncRound [] <$> QueryImpl.batch _ []
    rw [QueryImpl.batch_nil, QueryImpl.batch_nil, map_pure, eq_batchNil (E.truncRound [] batchNil)]
  | cons t ts ih =>
    change _ = E.truncRound (t :: ts) <$> QueryImpl.batch _ (E.encode t :: ts.map E.encode)
    rw [QueryImpl.batch_cons, QueryImpl.batch_cons, ih]
    simp only [typedLift, simulateQ_spec_query, encodeImpl, map_bind, bind_map_left, map_pure,
      truncRound_cons]
    rfl

lemma encodeImpl_compose_typedLift_batch' :
    (E.encodeImpl ∘ₛ typedLift).batch' = (D →ₒ M).unbatch ∘ₛ E.roundImpl := by
  funext t
  rcases t with n | ts
  · simp [typedLift, encodeImpl, roundImpl]
  · simp only [QueryImpl.batch'_apply_inr, QueryImpl.apply_compose, roundImpl, simulateQ_map,
      simulateQ_spec_query, OracleSpec.unbatch_apply_inr]
    exact E.batch_encodeImpl_typedLift ts

section typedWorld

variable [DecidableEq ι] [DecidableEq D]

lemma preprocessImpl_run_step (t : (unifSpec + (D →ₒ M)).Domain) (pv : (D →ₒ M).QueryCache)
    (c : spec.QueryCache) :
    (simulateQ spec.romImpl ((E.preprocessImpl t).run pv)).run c =
      (fun z => ((z.1, z.2.2), z.2.1)) <$> ((E.typedImpl ∘ₛ rawLift) t).run (c, pv) := by
  rcases t with n | x
  · simp only [preprocessImpl, rawLift, QueryImpl.apply_compose, simulateQ_spec_query]
    rw [typedImpl_inl_run]
    simp [OracleSpec.romImpl]
  · simp only [preprocessImpl, rawLift, QueryImpl.apply_compose, simulateQ_spec_query,
      typedImpl, QueryImpl.add_apply_inr]
    rw [typedHashImpl_inr_run]
    simp only [privateDraw, StateT.run_bind, StateT.run_mk, simulateQ_bind, StateT.run_bind,
      OracleSpec.simulateQ_romImpl_liftM_run, bind_map_left, map_bind]
    refine bind_congr fun z => ?_
    rcases E.route x with _ | q
    · simp
    · simp [OracleSpec.romImpl]

/-- A raw round answered input by input in the typed world is equal in distribution to drawing
all private values first, then the typed round of the encoded points, and reassembling. -/
lemma batch_typedHashImpl_run (xs : List D) (c : spec.QueryCache) (pv : (D →ₒ M).QueryCache) :
    (QueryImpl.batch (spec := D →ₒ M) (fun x => E.typedHashImpl (.inr x)) xs).run (c, pv) =ᵈ
      ((D →ₒ M).randomOracle.batch xs).run pv >>= fun z =>
        (spec.randomOracle.batch (xs.filterMap E.route)).run c >>= fun y =>
          pure (E.assemble xs z.1 y.1, (y.2, z.2)) := by
  induction xs generalizing c pv with
  | nil => simp [assemble]
  | cons x xs ih =>
    rcases hx : E.route x with _ | q
    · simp only [QueryImpl.batch_cons, StateT.run_bind]
      rw [typedHashImpl_inr_run]
      simp only [hx, bind_assoc, StateT.run_pure, pure_bind]
      refine (EvalDistEq.bind_right _ fun (z : M × (D →ₒ M).QueryCache) =>
        (ih c z.2).bind_left _).trans ?_
      simp only [batch_randomOracle_run_bind_cast (List.filterMap_cons_none hx),
        assemble_cons_none _ hx, bind_assoc, pure_bind, cast_cast, cast_eq, batchCons_mk_zero,
        batchCons_succ]
      exact EvalDistEq.rfl
    · simp only [QueryImpl.batch_cons, StateT.run_bind]
      rw [typedHashImpl_inr_run]
      simp only [hx, bind_assoc, map_eq_bind_pure_comp, Function.comp_apply, StateT.run_pure,
        pure_bind]
      refine (EvalDistEq.bind_right _ fun (z : M × (D →ₒ M).QueryCache) =>
        EvalDistEq.bind_right _ fun (y : spec.Range q × spec.QueryCache) =>
          (ih y.2 z.2).bind_left _).trans ?_
      simp only [batch_randomOracle_run_bind_cast (List.filterMap_cons_some hx),
        assemble_cons_some _ hx, QueryImpl.batch_cons, StateT.run_bind, StateT.run_pure,
        bind_assoc, pure_bind, batchCons_mk_zero, batchCons_succ]
      refine EvalDistEq.bind_right _ fun z => ?_
      exact EvalDistEq.bind_bind_swap _ _ _

lemma typedImpl_compose_rawLift_inr (x : D) :
    (E.typedImpl ∘ₛ rawLift) (.inr x) = E.typedHashImpl (.inr x) := by
  simp only [QueryImpl.apply_compose, rawLift, simulateQ_spec_query, typedImpl,
    QueryImpl.add_apply_inr]

lemma onlineImpl_run_step (t : (unifSpec + (D →ₒ M).batch).Domain) (pv : (D →ₒ M).QueryCache)
    (c : spec.QueryCache) :
    (simulateQ (unifFwdImpl spec + spec.randomOracle.batch) ((E.onlineImpl t).run pv)).run c =ᵈ
      (fun z => ((z.1, z.2.2), z.2.1)) <$> ((E.typedImpl ∘ₛ rawLift).batch' t).run (c, pv) := by
  rcases t with n | xs
  · simp only [onlineImpl, QueryImpl.batch'_apply_inl, QueryImpl.apply_compose, rawLift,
      simulateQ_spec_query]
    rw [typedImpl_inl_run]
    simp [OracleSpec.romImpl]
  · rw [QueryImpl.batch'_apply_inr, show (fun x => (E.typedImpl ∘ₛ rawLift) (.inr x)) =
      fun x => E.typedHashImpl (.inr x) from funext E.typedImpl_compose_rawLift_inr]
    refine EvalDistEq.trans ?_ ((E.batch_typedHashImpl_run xs c pv).map _).symm
    simp [onlineImpl, privateDraws, run_simulateQ_unifFwdImpl_add_liftM]

lemma simulateQ_typedImpl_typedLift_run {α : Type} (oa : OracleComp (unifSpec + spec) α)
    (c : spec.QueryCache) (pv : (D →ₒ M).QueryCache) :
    (simulateQ E.typedImpl (simulateQ typedLift oa)).run (c, pv) =
      (fun z => (z.1, (z.2, pv))) <$> (simulateQ spec.romImpl oa).run c := by
  induction oa using OracleComp.inductionOn generalizing c with
  | pure a => simp
  | query_bind t k ih =>
    have ht : (simulateQ E.typedImpl (typedLift t)).run (c, pv) =
        (fun z => (z.1, (z.2, pv))) <$> (spec.romImpl t).run c := by
      rcases t with n | t
      · simp only [typedLift, simulateQ_spec_query]
        exact typedImpl_inl_run n c pv
      · simp only [typedLift, simulateQ_spec_query]
        exact typedImpl_inr_inl_run t c pv
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, ht, bind_map_left, ih,
      map_bind]

end typedWorld

end OracleComp.RandomOracleEncoding
