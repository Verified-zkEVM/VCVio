/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.OracleComp.QueryTracking.CountingOracle.Core
public import VCVio.OracleComp.QueryTracking.QueryBound.Basic
public import VCVio.OracleComp.QueryTracking.WriterCost
public import VCVio.ProgramLogic.Library.T1.Lifts
public import VCVio.ProgramLogic.Library.T1.RunNF

/-!
# Specifications for counting and cost handlers

Specifications for the cost instrumentation `QueryImpl.withCost` and its instances
`QueryImpl.withCounting`, `QueryImpl.withAddCost`, `costOracle` and `countingOracle`, which
charge each query in a `WriterT` log read as accumulated state by `WriterT.MonoidWP`
(`open scoped WriterT.MonoidWP`). `OracleComp`-based statements use the necessary reading
(`open scoped OracleComp.Necessary`). Counts live in `Multiplicative (QueryCount ι)`: a query at
`t` multiplies the log by `Multiplicative.ofAdd (QueryCount.single t)`.

* *One query.* `withCost_wp`, `withCounting_wp` and `withAddCost_wp` read an instrumented step
  through the underlying handler under any reading; `costOracle_wp` and `countingOracle_wp`
  (`spec high`) charge the query and allow any answer.
* *Whole runs.* An instrumented run returns a possible result of the plain program and multiplies
  the log by its cost (`simulateQ_withCost_wp`, `spec low`); a cost function into a submonoid keeps
  the total cost there (`simulateQ_withCost_wp_of_mem`).
* *Query bounds.* A per-index query bound bounds the count of every reachable counted run
  (`toAdd_le_of_mem_support_run_simulateQ_withCounting`, and the triple
  `simulateQ_withCounting_wp_of_isPerIndexQueryBound`).
-/

@[expose] public section

open OracleSpec OracleComp Std.WP

open scoped OracleComp.Necessary WriterT.MonoidWP

universe u v w w' u' v'

namespace QueryImpl

variable {ι : Type u} {spec : OracleSpec.{u, u} ι}

section anyBase

variable {m : Type u → Type v} [Monad m] {ω : Type u} [Monoid ω]

/-- A cost-instrumented step runs the handler and writes the query's cost. -/
@[simulateQ_nf]
theorem run_withCost_apply_eq_map [LawfulMonad m] (so : QueryImpl spec m)
    (costFn : spec.Domain → ω) (t : spec.Domain) :
    (so.withCost costFn t).run = (·, costFn t) <$> so t := by
  simp [map_eq_bind_pure_comp]

variable {Pred : Type w} {EPred : Type w'} [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]

/-- A cost-instrumented step under any reading: the handler answers and the log is multiplied by
the query's cost. -/
@[spec]
theorem withCost_wp (so : QueryImpl spec m) (costFn : spec.Domain → ω) (t : spec.Domain)
    (post : spec.Range t → ω → Pred) (epost : EPred) :
    ⦃ fun c => wp (so t) (fun v => post v (c * costFn t)) epost ⦄ so.withCost costFn t
      ⦃ post; epost ⦄ := by
  refine ⟨fun c => ?_⟩
  rw [WriterT.wp_apply_eq, run_withCost_apply_eq_map]
  exact WPMonad.map_le_wp_map (m := m) (·, costFn t) (so t)
    (fun p : spec.Range t × ω => post p.1 (c * p.2)) epost

/-- A counted step under any reading: the handler answers and the count gains the query. -/
@[spec]
theorem withCounting_wp [DecidableEq ι] (so : QueryImpl spec m) (t : spec.Domain)
    (post : spec.Range t → Multiplicative (QueryCount ι) → Pred) (epost : EPred) :
    ⦃ fun c => wp (so t) (fun v => post v (c * Multiplicative.ofAdd (QueryCount.single t)))
        epost ⦄
      so.withCounting t ⦃ post; epost ⦄ :=
  withCost_wp so _ t post epost

end anyBase

/-- An additively cost-instrumented step under any reading: the handler answers and the cost
gains the query's cost. -/
@[spec]
theorem withAddCost_wp {ι : Type} {spec : OracleSpec ι} {m : Type → Type v} [Monad m]
    {Pred : Type w} {EPred : Type w'} [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    {ω : Type} [AddMonoid ω] (so : QueryImpl spec m) (costFn : spec.Domain → ω) (t : spec.Domain)
    (post : spec.Range t → Multiplicative ω → Pred) (epost : EPred) :
    ⦃ fun c => wp (so t) (fun v => post v (c * Multiplicative.ofAdd (costFn t))) epost ⦄
      so.withAddCost costFn t ⦃ post; epost ⦄ :=
  withCost_wp so _ t post epost

section oracleCompBase

variable {ι' : Type u'} {spec' : OracleSpec.{u', v'} ι'} {ω : Type u} [Monoid ω]

/-- A reachable cost-instrumented step is a reachable step of the handler charged its cost. -/
theorem mem_support_run_withCost_iff (so : QueryImpl spec (OracleComp spec'))
    (costFn : spec.Domain → ω) {t : spec.Domain} {v : spec.Range t} {w : ω} :
    (v, w) ∈ support (so.withCost costFn t).run ↔ v ∈ support (so t) ∧ w = costFn t := by
  rw [run_withCost_apply_eq_map, support_map]
  constructor
  · rintro ⟨u, hu, h⟩
    rw [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hu, rfl⟩
  · rintro ⟨hv, rfl⟩
    exact ⟨v, hv, rfl⟩

/-- A cost-instrumented run of a query followed by a continuation runs the handler, then the
continuation, charging the query's cost first. -/
theorem run_simulateQ_withCost_query_bind {α : Type u} (so : QueryImpl spec (OracleComp spec'))
    (costFn : spec.Domain → ω) (t : spec.Domain) (oa : spec.Range t → OracleComp spec α) :
    (simulateQ (so.withCost costFn) ((spec.query t : OracleComp spec _) >>= oa)).run =
      so t >>= fun u =>
        (fun z => (z.1, costFn t * z.2)) <$> (simulateQ (so.withCost costFn) (oa u)).run := by
  simp only [simulateQ_bind, simulateQ_spec_query, WriterT.run_bind, QueryImpl.withCost_apply]
  simp [map_eq_bind_pure_comp]

/-- A cost function into a submonoid keeps the total cost of every reachable instrumented run in
the submonoid, and the result is a possible result of the plain run. -/
theorem mem_of_mem_support_run_simulateQ_withCost {α : Type u}
    (so : QueryImpl spec (OracleComp spec')) (costFn : spec.Domain → ω) (S : Submonoid ω)
    (hS : ∀ t, costFn t ∈ S) (oa : OracleComp spec α) {z : α × ω}
    (hz : z ∈ support (simulateQ (so.withCost costFn) oa).run) :
    z.1 ∈ support (simulateQ so oa) ∧ z.2 ∈ S := by
  induction oa using OracleComp.inductionOn generalizing z with
  | pure a =>
    rw [simulateQ_pure, WriterT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨by simp, S.one_mem⟩
  | query_bind t oa ih =>
    rw [run_simulateQ_withCost_query_bind, mem_support_bind_iff] at hz
    obtain ⟨u, hu, hz⟩ := hz
    rw [support_map] at hz
    obtain ⟨z', hz', rfl⟩ := hz
    obtain ⟨ha, hw⟩ := ih u hz'
    refine ⟨?_, S.mul_mem (hS t) hw⟩
    simp only [simulateQ_bind, simulateQ_spec_query, mem_support_bind_iff]
    exact ⟨u, hu, ha⟩

/-- The frame of a whole cost-instrumented run, for an opaque program: the result is a possible
result of the plain run and the log is multiplied by the run's cost. -/
@[spec low]
theorem simulateQ_withCost_wp {α : Type u} (so : QueryImpl spec (OracleComp spec'))
    (costFn : spec.Domain → ω) (oa : OracleComp spec α) (post : α → ω → Prop)
    {epost : EStack⟨⟩} :
    ⦃ fun c => ∀ a w, a ∈ support (simulateQ so oa) → post a (c * w) ⦄
      (simulateQ (so.withCost costFn) oa) ⦃ post; epost ⦄ :=
  (OracleComp.ProgramLogic.triple_writerT_iff_forall_mem_support _ _ _ _).2 fun _ h a w hz =>
    h a w (mem_of_mem_support_run_simulateQ_withCost so costFn ⊤ (fun _ => trivial) oa hz).1

/-- A whole cost-instrumented run with costs in a submonoid multiplies the log by an element of
the submonoid. -/
theorem simulateQ_withCost_wp_of_mem {α : Type u} (so : QueryImpl spec (OracleComp spec'))
    (costFn : spec.Domain → ω) (S : Submonoid ω) (hS : ∀ t, costFn t ∈ S)
    (oa : OracleComp spec α) (post : α → ω → Prop) {epost : EStack⟨⟩} :
    ⦃ fun c => ∀ a w, a ∈ support (simulateQ so oa) → w ∈ S → post a (c * w) ⦄
      (simulateQ (so.withCost costFn) oa) ⦃ post; epost ⦄ :=
  (OracleComp.ProgramLogic.triple_writerT_iff_forall_mem_support _ _ _ _).2 fun _ h a w hz =>
    (mem_of_mem_support_run_simulateQ_withCost so costFn S hS oa hz).elim (h a w)

variable [DecidableEq ι]

/-- A per-index query bound on `oa` bounds the count of every reachable counted run. -/
theorem toAdd_le_of_mem_support_run_simulateQ_withCounting {α : Type u}
    (so : QueryImpl spec (OracleComp spec')) {oa : OracleComp spec α} {qb : ι → ℕ}
    (h : IsPerIndexQueryBound oa qb) {z : α × Multiplicative (QueryCount ι)}
    (hz : z ∈ support (simulateQ so.withCounting oa).run) : Multiplicative.toAdd z.2 ≤ qb := by
  induction oa using OracleComp.inductionOn generalizing qb z with
  | pure a =>
    rw [simulateQ_pure, WriterT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact fun i => Nat.zero_le _
  | query_bind t oa ih =>
    rw [isPerIndexQueryBound_query_bind_iff] at h
    rw [withCounting, run_simulateQ_withCost_query_bind, mem_support_bind_iff] at hz
    obtain ⟨u, -, hz⟩ := hz
    rw [support_map] at hz
    obtain ⟨⟨a, w₂⟩, h₂, rfl⟩ := hz
    have hw := ih u (h.2 u) h₂
    intro i
    have hi := hw i
    simp only [toAdd_mul, toAdd_ofAdd, Pi.add_apply] at hi ⊢
    rcases eq_or_ne i t with rfl | hne
    · rw [Function.update_self] at hi
      rw [QueryCount.single, Pi.single_eq_same]
      have := h.1
      omega
    · rw [Function.update_of_ne hne] at hi
      rw [QueryCount.single, Pi.single_eq_of_ne hne, zero_add]
      exact hi

/-- A counted run of a program with a per-index query bound multiplies the count by at most the
bound. -/
theorem simulateQ_withCounting_wp_of_isPerIndexQueryBound {α : Type u}
    (so : QueryImpl spec (OracleComp spec')) {oa : OracleComp spec α} {qb : ι → ℕ}
    (h : IsPerIndexQueryBound oa qb) (post : α → Multiplicative (QueryCount ι) → Prop)
    {epost : EStack⟨⟩} :
    ⦃ fun c => ∀ a w, a ∈ support (simulateQ so oa) → Multiplicative.toAdd w ≤ qb →
        post a (c * w) ⦄
      (simulateQ so.withCounting oa) ⦃ post; epost ⦄ :=
  (OracleComp.ProgramLogic.triple_writerT_iff_forall_mem_support _ _ _ _).2 fun _ hpre a w hz =>
    hpre a w (mem_of_mem_support_run_simulateQ_withCost so _ ⊤ (fun _ => trivial) oa hz).1
      (toAdd_le_of_mem_support_run_simulateQ_withCounting so h hz)

end oracleCompBase

end QueryImpl

namespace costOracle

variable {ι : Type u} {spec : OracleSpec.{u, u} ι} {ω : Type u} [Monoid ω]

/-- A `costOracle` step queries and writes the query's cost. -/
@[simulateQ_nf]
theorem run_apply (costFn : spec.Domain → ω) (t : spec.Domain) :
    (costOracle costFn t).run =
      (·, costFn t) <$> (liftM (spec.query t) : OracleComp spec (spec.Range t)) :=
  QueryImpl.run_withCost_apply_eq_map _ costFn t

end costOracle

namespace countingOracle

variable {ι : Type u} [DecidableEq ι] {spec : OracleSpec.{u, u} ι}

/-- A `countingOracle` step queries and counts the query. -/
@[simulateQ_nf]
theorem run_apply (t : spec.Domain) :
    (spec.countingOracle t).run = (·, Multiplicative.ofAdd (QueryCount.single t)) <$>
      (liftM (spec.query t) : OracleComp spec (spec.Range t)) :=
  QueryImpl.run_withCost_apply_eq_map _ _ t

end countingOracle

namespace OracleComp.ProgramLogic

variable {ι : Type u} {spec : OracleSpec.{u, u} ι}

/-- One `costOracle` query: any answer, with the log multiplied by its cost. The default rule of
`vcgen` for `costOracle`. -/
@[spec high]
theorem costOracle_wp {ω : Type u} [Monoid ω] (costFn : spec.Domain → ω) (t : spec.Domain)
    (post : spec.Range t → ω → Prop) {epost : EStack⟨⟩} :
    ⦃ fun c => ∀ v, post v (c * costFn t) ⦄ (costOracle costFn t) ⦃ post; epost ⦄ :=
  (triple_writerT_iff_forall_mem_support _ _ _ _).2 fun c h v w hz => by
    rw [((QueryImpl.mem_support_run_withCost_iff _ costFn).1 hz).2]
    exact h v

/-- One `countingOracle` query: any answer, with the count gaining the query. The default rule
of `vcgen` for `countingOracle`. -/
@[spec high]
theorem countingOracle_wp [DecidableEq ι] (t : spec.Domain)
    (post : spec.Range t → Multiplicative (QueryCount ι) → Prop) {epost : EStack⟨⟩} :
    ⦃ fun c => ∀ v, post v (c * Multiplicative.ofAdd (QueryCount.single t)) ⦄
      (spec.countingOracle t) ⦃ post; epost ⦄ :=
  costOracle_wp _ t post

/-- The frame of a whole `costOracle` run, for an opaque program: the result is a possible result
of the program and the log is multiplied by the run's cost. -/
@[spec low]
theorem simulateQ_costOracle_wp {ω : Type u} [Monoid ω] (costFn : spec.Domain → ω) {α : Type u}
    (oa : OracleComp spec α) (post : α → ω → Prop) {epost : EStack⟨⟩} :
    ⦃ fun c => ∀ a w, a ∈ support oa → post a (c * w) ⦄ (simulateQ (costOracle costFn) oa)
      ⦃ post; epost ⦄ := by
  have h := QueryImpl.simulateQ_withCost_wp (QueryImpl.ofLift spec (OracleComp spec)) costFn oa
    post (epost := epost)
  simp only [simulateQ_ofLift_eq_self] at h
  exact h

/-- A `countingOracle` run of a program with a per-index query bound multiplies the count by at
most the bound. -/
theorem simulateQ_countingOracle_wp_of_isPerIndexQueryBound [DecidableEq ι] {α : Type u}
    {oa : OracleComp spec α} {qb : ι → ℕ} (h : IsPerIndexQueryBound oa qb)
    (post : α → Multiplicative (QueryCount ι) → Prop) {epost : EStack⟨⟩} :
    ⦃ fun c => ∀ a w, a ∈ support oa → Multiplicative.toAdd w ≤ qb → post a (c * w) ⦄
      (simulateQ spec.countingOracle oa) ⦃ post; epost ⦄ := by
  have h' := QueryImpl.simulateQ_withCounting_wp_of_isPerIndexQueryBound
    (QueryImpl.ofLift spec (OracleComp spec)) h post (epost := epost)
  simp only [simulateQ_ofLift_eq_self] at h'
  exact h'

/-- A per-index query bound on `oa` bounds the count of every reachable `countingOracle` run. -/
theorem toAdd_le_of_mem_support_run_simulateQ_countingOracle [DecidableEq ι] {α : Type u}
    {oa : OracleComp spec α} {qb : ι → ℕ} (h : IsPerIndexQueryBound oa qb)
    {z : α × Multiplicative (QueryCount ι)}
    (hz : z ∈ support (simulateQ spec.countingOracle oa).run) : Multiplicative.toAdd z.2 ≤ qb :=
  QueryImpl.toAdd_le_of_mem_support_run_simulateQ_withCounting _ h hz

end OracleComp.ProgramLogic
