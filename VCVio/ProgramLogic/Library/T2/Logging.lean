/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.OracleComp.QueryTracking.LoggingOracle.Core
public import VCVio.ProgramLogic.Library.T1.Lifts
public import VCVio.ProgramLogic.Library.T1.RunNF

/-!
# Specifications for logging handlers

Specifications for `QueryImpl.withLogging` and `loggingOracle`, which append each query and its
answer to a `WriterT` log. The log is read as accumulated state by `WriterT.AppendWP`
(`open scoped WriterT.AppendWP`); `OracleComp`-based statements use the necessary reading
(`open scoped OracleComp.Necessary`).

* *One query.* `withLogging_wp` reads a logged step through the underlying handler under any
  reading; `loggingOracle_wp` (`spec high`) is `fun log => ∀ v, post v (log ++ [⟨t, v⟩])`.
* *Whole runs.* A logged run returns a possible result of the unlogged program and only appends
  to the log (`simulateQ_loggingOracle_wp`, `spec low`). Query bounds transport to the log:
  `countQ_le_of_mem_support_run_simulateQ` bounds the entries satisfying a predicate by an
  `IsQueryBoundP` budget, and `simulateQ_loggingOracle_wp_of_isQueryBoundP` states it as a triple;
  `simulateQ_loggingOracle_wp_of_allQueriesSatisfy` records the inputs' predicate.
* *Support.* `mem_support_run_withLogging_iff` and `loggingOracle.mem_support_run_iff` read a
  reachable logged step.
-/

@[expose] public section

open OracleSpec OracleComp Std.WP

open scoped OracleComp.Necessary WriterT.AppendWP

universe u v w w' u' v'

namespace OracleSpec.QueryLog

/-- The empty log has no entries satisfying any predicate. -/
@[simp]
theorem countQ_nil {ι : Type u} {spec : OracleSpec.{u, v} ι} (p : spec.Domain → Prop)
    [DecidablePred p] : countQ ([] : QueryLog spec) p = 0 := rfl

end OracleSpec.QueryLog

namespace QueryImpl

variable {ι : Type u} {spec : OracleSpec.{u, u} ι}

section anyBase

variable {m : Type u → Type v} [Monad m]

/-- A logged step runs the handler and writes the query with its answer. -/
@[simulateQ_nf]
theorem run_withLogging_apply_eq_map [LawfulMonad m] (so : QueryImpl spec m) (t : spec.Domain) :
    (so.withLogging t).run = (fun u => (u, [⟨t, u⟩])) <$> so t := by
  simp [map_eq_bind_pure_comp]

variable {Pred : Type w} {EPred : Type w'} [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]

/-- A logged step under any reading: the underlying handler answers and the log gains the query
with its answer. -/
@[spec]
theorem withLogging_wp (so : QueryImpl spec m) (t : spec.Domain)
    (post : spec.Range t → QueryLog spec → Pred) (epost : EPred) :
    ⦃ fun log => wp (so t) (fun v => post v (log ++ [⟨t, v⟩])) epost ⦄ so.withLogging t
      ⦃ post; epost ⦄ := by
  refine ⟨fun log => ?_⟩
  rw [WriterT.AppendWP.wp_apply_eq, run_withLogging_apply_eq_map]
  exact WPMonad.map_le_wp_map (m := m) (fun u => (u, [⟨t, u⟩])) (so t)
    (fun p : spec.Range t × QueryLog spec => post p.1 (log ++ p.2)) epost

end anyBase

variable {ι' : Type u'} {spec' : OracleSpec.{u', v'} ι'}

/-- A reachable logged step is a reachable step of the handler with a one-entry log. -/
theorem mem_support_run_withLogging_iff (so : QueryImpl spec (OracleComp spec')) {t : spec.Domain}
    {v : spec.Range t} {w : QueryLog spec} :
    (v, w) ∈ support (so.withLogging t).run ↔ v ∈ support (so t) ∧ w = [⟨t, v⟩] := by
  rw [run_withLogging_apply_eq_map, support_map]
  constructor
  · rintro ⟨u, hu, h⟩
    rw [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hu, rfl⟩
  · rintro ⟨hv, rfl⟩
    exact ⟨v, hv, rfl⟩

end QueryImpl

namespace loggingOracle

variable {ι : Type u} {spec : OracleSpec.{u, u} ι}

/-- A `loggingOracle` step queries and logs the query with its answer. -/
@[simulateQ_nf]
theorem run_apply (t : spec.Domain) :
    (spec.loggingOracle t).run =
      (fun u => (u, [⟨t, u⟩])) <$> (liftM (spec.query t) : OracleComp spec (spec.Range t)) :=
  QueryImpl.run_withLogging_apply_eq_map _ t

/-- A reachable `loggingOracle` step logs exactly its query and answer. -/
@[simulateQ_nf]
theorem mem_support_run_iff {t : spec.Domain} {v : spec.Range t} {w : QueryLog spec} :
    (v, w) ∈ support (spec.loggingOracle t).run ↔ w = [⟨t, v⟩] := by
  rw [loggingOracle, QueryImpl.mem_support_run_withLogging_iff]
  simp

end loggingOracle

namespace OracleComp.ProgramLogic

section step

variable {ι : Type u} {spec : OracleSpec.{u, u} ι}

/-- One `loggingOracle` query: any answer, appended with its query to the log. The default rule
of `vcgen` for `loggingOracle`. -/
@[spec high]
theorem loggingOracle_wp (t : spec.Domain) (post : spec.Range t → QueryLog spec → Prop)
    {epost : EStack⟨⟩} :
    ⦃ fun log => ∀ v, post v (log ++ [⟨t, v⟩]) ⦄ (spec.loggingOracle t) ⦃ post; epost ⦄ :=
  (triple_writerT_iff_forall_mem_support_append _ _ _ _).2 fun log h v w hz => by
    rw [loggingOracle.mem_support_run_iff.1 hz]
    exact h v

end step

section run

variable {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}

/-- A query bound on `oa` bounds, in every reachable logged run, the number of log entries whose
input satisfies the bounded predicate. -/
theorem countQ_le_of_mem_support_run_simulateQ {p : ι → Prop} [DecidablePred p] {n : ℕ}
    {oa : OracleComp spec α} (h : IsQueryBoundP oa p n) {z : α × QueryLog spec}
    (hz : z ∈ support (simulateQ spec.loggingOracle oa).run) : z.2.countQ p ≤ n := by
  induction oa using OracleComp.inductionOn generalizing n z with
  | pure a =>
    simp only [simulateQ_pure] at hz
    rw [show z = (a, []) from hz]
    exact Nat.zero_le n
  | query_bind t oa ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    rw [run_simulateQ_loggingOracle_query_bind, mem_support_bind_iff] at hz
    obtain ⟨u, -, hz⟩ := hz
    rw [support_map] at hz
    obtain ⟨z', hz', rfl⟩ := hz
    have := ih u (h.2 u) hz'
    rw [QueryLog.countQ_cons]
    split_ifs at this ⊢ with hp
    · have := h.1.resolve_left (not_not.2 hp)
      omega
    · exact this

/-- The result of a reachable logged run is a possible result of the unlogged program. -/
theorem mem_support_of_mem_support_run_simulateQ_loggingOracle {oa : OracleComp spec α}
    {z : α × QueryLog spec} (hz : z ∈ support (simulateQ spec.loggingOracle oa).run) :
    z.1 ∈ support oa := by
  rw [← loggingOracle.support_fst_map_run_simulateQ, support_map]
  exact ⟨z, hz, rfl⟩

/-- The frame of a whole logged run, for an opaque program: the result is a possible one of the
program and the log is only appended to. -/
@[spec low]
theorem simulateQ_loggingOracle_wp (oa : OracleComp spec α) (post : α → QueryLog spec → Prop)
    {epost : EStack⟨⟩} :
    ⦃ fun log => ∀ a w, a ∈ support oa → post a (log ++ w) ⦄
      (simulateQ spec.loggingOracle oa) ⦃ post; epost ⦄ :=
  (triple_writerT_iff_forall_mem_support_append _ _ _ _).2 fun _ h a w hz =>
    h a w (mem_support_of_mem_support_run_simulateQ_loggingOracle hz)

/-- A logged run of a program with an `IsQueryBoundP` budget appends at most that many entries
satisfying the predicate. -/
theorem simulateQ_loggingOracle_wp_of_isQueryBoundP {p : ι → Prop} [DecidablePred p] {n : ℕ}
    {oa : OracleComp spec α} (h : IsQueryBoundP oa p n) (post : α → QueryLog spec → Prop)
    {epost : EStack⟨⟩} :
    ⦃ fun log => ∀ a w, a ∈ support oa → w.countQ p ≤ n → post a (log ++ w) ⦄
      (simulateQ spec.loggingOracle oa) ⦃ post; epost ⦄ :=
  (triple_writerT_iff_forall_mem_support_append _ _ _ _).2 fun _ hpre a w hz =>
    hpre a w (mem_support_of_mem_support_run_simulateQ_loggingOracle hz)
      (countQ_le_of_mem_support_run_simulateQ h hz)

/-- A logged run of a program whose queries all satisfy `P` appends only entries with inputs
satisfying `P`. -/
theorem simulateQ_loggingOracle_wp_of_allQueriesSatisfy {P : ι → Prop} {oa : OracleComp spec α}
    (h : AllQueriesSatisfy oa P) (post : α → QueryLog spec → Prop) {epost : EStack⟨⟩} :
    ⦃ fun log => ∀ a w, a ∈ support oa → (∀ e ∈ w, P e.1) → post a (log ++ w) ⦄
      (simulateQ spec.loggingOracle oa) ⦃ post; epost ⦄ :=
  (triple_writerT_iff_forall_mem_support_append _ _ _ _).2 fun _ hpre a w hz =>
    hpre a w (mem_support_of_mem_support_run_simulateQ_loggingOracle hz)
      (holds_of_mem_log_of_mem_support_run_simulateQ h hz)

end run

end OracleComp.ProgramLogic
