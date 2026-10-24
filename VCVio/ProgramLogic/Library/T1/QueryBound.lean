/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.OracleComp.QueryTracking.QueryBound.Basic
public import VCVio.OracleComp.Constructions.Replicate.Basic
public import VCVio.OracleComp.Coercions.SubSpec.Basic

/-!
# Structural rules for query bounds

Rules that make `IsTotalQueryBound` and `IsQueryBoundP` goals for concrete programs mechanical,
one per program former:

* `simp` normal forms for `pure`, a primitive query, a lifted query and `<$>`
  (`isTotalQueryBound_pure`, `isTotalQueryBound_query_iff`, `isTotalQueryBound_liftM_iff`,
  `isTotalQueryBound_map_iff`), which `IsTotalQueryBound` hides from `IsQueryBound`'s simp set;
* `isTotalQueryBound_bind_le` and `isQueryBoundP_bind_le`: a bind against any goal bound at
  least the sum, with the continuation bounded only on the support, so they apply with `refine`
  to a goal whose bound is not syntactically a sum;
* `ite` (`isTotalQueryBound_ite`, `isQueryBoundP_ite`);
* traversals with per-element bounds: `List.mapM`, `List.foldlM` and `List.forM`, as a sum of
  per-element counts (`*_sum`) or a uniform product (`xs.length * n`), and `replicate`;
* lifts and simulations: `isTotalQueryBound_liftComp`, and
  `IsTotalQueryBound.simulateQ_run_of_step_le` for a stateful handler making at most `step`
  queries per source query (the bound is `n * step`).

The budget reading of `VCVio.ProgramLogic.Library.T1.QueryBoundBudget` states the same bounds as
core triples, for `vcgen`.
-/

@[expose] public section

open OracleSpec

universe u

open scoped OracleSpec.PrimitiveQuery

namespace OracleComp

variable {ι : Type u} {spec : OracleSpec.{u, u} ι} {α β γ : Type u}

/-! ## Total query bounds -/

/-- A `pure` computation makes no queries. -/
@[simp]
theorem isTotalQueryBound_pure (x : α) (n : ℕ) :
    IsTotalQueryBound (pure x : OracleComp spec α) n :=
  trivial

/-- A primitive query needs a positive budget. -/
@[simp]
theorem isTotalQueryBound_query_iff (t : spec.Domain) (n : ℕ) :
    IsTotalQueryBound (liftM (spec.query t) : OracleComp spec (spec.Range t)) n ↔ 0 < n :=
  isQueryBound_query_iff t n _ _

/-- A query bound is invariant under mapping the output. -/
@[simp]
theorem isTotalQueryBound_map_iff (oa : OracleComp spec α) (f : α → β) (n : ℕ) :
    IsTotalQueryBound (f <$> oa) n ↔ IsTotalQueryBound oa n :=
  isQueryBound_map_iff oa f n _ _

/-- A lifted oracle query needs a positive budget. -/
@[simp]
theorem isTotalQueryBound_liftM_iff (q : OracleQuery spec α) (n : ℕ) :
    IsTotalQueryBound (liftM q : OracleComp spec α) n ↔ 0 < n := by
  rw [liftM_eq_map_query, isTotalQueryBound_map_iff, isTotalQueryBound_query_iff]

/-- **Bind rule against any larger bound.** Budgets add under sequencing, with the
continuation bounded on the support of the first computation. -/
theorem isTotalQueryBound_bind_le {oa : OracleComp spec α} {ob : α → OracleComp spec β}
    {n₁ n₂ n : ℕ} (h₁ : IsTotalQueryBound oa n₁)
    (h₂ : ∀ x ∈ support oa, IsTotalQueryBound (ob x) n₂) (h : n₁ + n₂ ≤ n) :
    IsTotalQueryBound (oa >>= ob) n :=
  (isTotalQueryBound_bind_of_mem_support h₁ h₂).mono h

/-- A conditional is bounded by a bound of both branches. -/
theorem isTotalQueryBound_ite {c : Prop} [Decidable c] {oa ob : OracleComp spec α} {n : ℕ}
    (h₁ : c → IsTotalQueryBound oa n) (h₂ : ¬c → IsTotalQueryBound ob n) :
    IsTotalQueryBound (if c then oa else ob) n := by
  split_ifs with hc
  exacts [h₁ hc, h₂ hc]

/-- `List.mapM` makes at most the sum of the per-element bounds. -/
theorem isTotalQueryBound_list_mapM_sum (xs : List α) {f : α → OracleComp spec β}
    (g : α → ℕ) (h : ∀ x ∈ xs, IsTotalQueryBound (f x) (g x)) :
    IsTotalQueryBound (xs.mapM f) (xs.map g).sum := by
  induction xs with
  | nil => exact isTotalQueryBound_pure _ _
  | cons x xs ih =>
    rw [List.mapM_cons, List.map_cons, List.sum_cons]
    refine isTotalQueryBound_bind_le (h x List.mem_cons_self) (n₂ := (xs.map g).sum)
      (fun _ _ => ?_) le_rfl
    exact isTotalQueryBound_bind_le (ih fun y hy => h y (List.mem_cons_of_mem x hy))
      (fun _ _ => isTotalQueryBound_pure _ 0) le_rfl

/-- `List.mapM` with a uniform per-element bound. -/
theorem isTotalQueryBound_list_mapM (xs : List α) {f : α → OracleComp spec β} {n : ℕ}
    (h : ∀ x ∈ xs, IsTotalQueryBound (f x) n) :
    IsTotalQueryBound (xs.mapM f) (xs.length * n) := by
  simpa using isTotalQueryBound_list_mapM_sum xs (fun _ => n) h

/-- `List.foldlM` makes at most the sum of the per-element bounds, from every accumulator. -/
theorem isTotalQueryBound_list_foldlM_sum (xs : List α) {f : β → α → OracleComp spec β}
    (g : α → ℕ) (h : ∀ b, ∀ x ∈ xs, IsTotalQueryBound (f b x) (g x)) (init : β) :
    IsTotalQueryBound (xs.foldlM f init) (xs.map g).sum := by
  induction xs generalizing init with
  | nil => exact isTotalQueryBound_pure _ _
  | cons x xs ih =>
    rw [List.foldlM_cons, List.map_cons, List.sum_cons]
    exact isTotalQueryBound_bind_le (h init x List.mem_cons_self)
      (fun b _ => ih (fun b y hy => h b y (List.mem_cons_of_mem x hy)) b) le_rfl

/-- `List.foldlM` with a uniform per-element bound. -/
theorem isTotalQueryBound_list_foldlM (xs : List α) {f : β → α → OracleComp spec β} {n : ℕ}
    (h : ∀ b, ∀ x ∈ xs, IsTotalQueryBound (f b x) n) (init : β) :
    IsTotalQueryBound (xs.foldlM f init) (xs.length * n) := by
  simpa using isTotalQueryBound_list_foldlM_sum xs (fun _ => n) h init

/-- `List.forM` makes at most the sum of the per-element bounds. -/
theorem isTotalQueryBound_list_forM_sum (xs : List α) {f : α → OracleComp spec PUnit}
    (g : α → ℕ) (h : ∀ x ∈ xs, IsTotalQueryBound (f x) (g x)) :
    IsTotalQueryBound (xs.forM f) (xs.map g).sum := by
  induction xs with
  | nil => exact isTotalQueryBound_pure _ _
  | cons x xs ih =>
    rw [List.map_cons, List.sum_cons]
    exact isTotalQueryBound_bind_le (ob := fun _ => xs.forM f) (h x List.mem_cons_self)
      (fun _ _ => ih fun y hy => h y (List.mem_cons_of_mem x hy)) le_rfl

/-- `replicate k oa` makes at most `k` times the bound of `oa`. -/
theorem isTotalQueryBound_replicate {oa : OracleComp spec α} {n : ℕ}
    (h : IsTotalQueryBound oa n) (k : ℕ) :
    IsTotalQueryBound (oa.replicate k) (k * n) := by
  induction k with
  | zero => exact isTotalQueryBound_pure _ _
  | succ k ih =>
    rw [replicate_succ_bind]
    exact isTotalQueryBound_bind_le h (fun _ _ => isTotalQueryBound_bind_le ih
      (fun _ _ => isTotalQueryBound_pure _ 0) le_rfl) (by rw [Nat.succ_mul]; omega)

/-- Lifting into a larger specification keeps a total query bound. -/
theorem isTotalQueryBound_liftComp {τ : Type u} {superSpec : OracleSpec.{u, u} τ}
    [MonadLiftT (OracleQuery spec) (OracleQuery superSpec)]
    {oa : OracleComp spec α} {n : ℕ} (h : IsTotalQueryBound oa n) :
    IsTotalQueryBound (liftComp oa superSpec) n := by
  rw [liftComp_def]
  exact h.simulateQ_of_step fun t => (isTotalQueryBound_liftM_iff _ 1).2 Nat.one_pos

/-- A stateful handler making at most `step` queries per source query runs a computation within
`n` queries in at most `n * step` queries. -/
theorem IsTotalQueryBound.simulateQ_run_of_step_le {ι' : Type u}
    {spec' : OracleSpec.{u, u} ι'} {σ : Type u}
    {impl : QueryImpl spec (StateT σ (OracleComp spec'))} {oa : OracleComp spec α} {n step : ℕ}
    (h : IsTotalQueryBound oa n) (hstep : ∀ t s, IsTotalQueryBound ((impl t).run s) step)
    (s : σ) :
    IsTotalQueryBound ((simulateQ impl oa).run s) (n * step) := by
  induction oa using OracleComp.inductionOn generalizing n s with
  | pure x => exact isTotalQueryBound_pure _ _
  | query_bind t mx ih =>
    rw [isTotalQueryBound_query_bind_iff] at h
    rw [simulateQ_query_bind, StateT.run_bind]
    have hstep' : IsTotalQueryBound
        ((liftM (impl t) : StateT σ (OracleComp spec') (spec.Range t)).run s) step := by
      simpa [OracleComp.liftM_run_StateT, MonadLift.monadLift] using hstep t s
    refine isTotalQueryBound_bind_le hstep' (fun p _ => ih p.1 (h.2 p.1) p.2) ?_
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
    rw [Nat.add_sub_cancel, Nat.succ_mul, Nat.add_comm]

/-- `IsTotalQueryBound.simulateQ_run_of_step_le` with the final state discarded. -/
theorem IsTotalQueryBound.simulateQ_run'_of_step_le {ι' : Type u}
    {spec' : OracleSpec.{u, u} ι'} {σ : Type u}
    {impl : QueryImpl spec (StateT σ (OracleComp spec'))} {oa : OracleComp spec α} {n step : ℕ}
    (h : IsTotalQueryBound oa n) (hstep : ∀ t s, IsTotalQueryBound ((impl t).run s) step)
    (s : σ) :
    IsTotalQueryBound ((simulateQ impl oa).run' s) (n * step) := by
  rw [StateT.run'_eq, isTotalQueryBound_map_iff]
  exact h.simulateQ_run_of_step_le hstep s

/-! ## Predicate-targeted query bounds -/

variable {p : ι → Prop} [DecidablePred p]

/-- **Bind rule against any larger bound**, for queries satisfying `p`. -/
theorem isQueryBoundP_bind_le {oa : OracleComp spec α} {ob : α → OracleComp spec β}
    {n₁ n₂ n : ℕ} (h₁ : IsQueryBoundP oa p n₁)
    (h₂ : ∀ x ∈ support oa, IsQueryBoundP (ob x) p n₂) (h : n₁ + n₂ ≤ n) :
    IsQueryBoundP (oa >>= ob) p n :=
  (isQueryBoundP_bind h₁ h₂).mono h

/-- A conditional is `p`-bounded by a bound of both branches. -/
theorem isQueryBoundP_ite {c : Prop} [Decidable c] {oa ob : OracleComp spec α} {n : ℕ}
    (h₁ : c → IsQueryBoundP oa p n) (h₂ : ¬c → IsQueryBoundP ob p n) :
    IsQueryBoundP (if c then oa else ob) p n := by
  split_ifs with hc
  exacts [h₁ hc, h₂ hc]

/-- `List.mapM` makes at most the sum of the per-element `p`-bounds. -/
theorem isQueryBoundP_list_mapM_sum (xs : List α) {f : α → OracleComp spec β}
    (g : α → ℕ) (h : ∀ x ∈ xs, IsQueryBoundP (f x) p (g x)) :
    IsQueryBoundP (xs.mapM f) p (xs.map g).sum := by
  induction xs with
  | nil => exact isQueryBoundP_pure p _ _
  | cons x xs ih =>
    rw [List.mapM_cons, List.map_cons, List.sum_cons]
    refine isQueryBoundP_bind_le (h x List.mem_cons_self) (n₂ := (xs.map g).sum)
      (fun _ _ => ?_) le_rfl
    exact isQueryBoundP_bind_le (ih fun y hy => h y (List.mem_cons_of_mem x hy))
      (fun _ _ => isQueryBoundP_pure p _ 0) le_rfl

/-- `List.mapM` with a uniform per-element `p`-bound. -/
theorem isQueryBoundP_list_mapM (xs : List α) {f : α → OracleComp spec β} {n : ℕ}
    (h : ∀ x ∈ xs, IsQueryBoundP (f x) p n) :
    IsQueryBoundP (xs.mapM f) p (xs.length * n) := by
  simpa using isQueryBoundP_list_mapM_sum xs (fun _ => n) h

/-- `List.foldlM` makes at most the sum of the per-element `p`-bounds. -/
theorem isQueryBoundP_list_foldlM_sum (xs : List α) {f : β → α → OracleComp spec β}
    (g : α → ℕ) (h : ∀ b, ∀ x ∈ xs, IsQueryBoundP (f b x) p (g x)) (init : β) :
    IsQueryBoundP (xs.foldlM f init) p (xs.map g).sum := by
  induction xs generalizing init with
  | nil => exact isQueryBoundP_pure p _ _
  | cons x xs ih =>
    rw [List.foldlM_cons, List.map_cons, List.sum_cons]
    exact isQueryBoundP_bind_le (h init x List.mem_cons_self)
      (fun b _ => ih (fun b y hy => h b y (List.mem_cons_of_mem x hy)) b) le_rfl

/-- `replicate k oa` makes at most `k` times the `p`-bound of `oa`. -/
theorem isQueryBoundP_replicate {oa : OracleComp spec α} {n : ℕ}
    (h : IsQueryBoundP oa p n) (k : ℕ) :
    IsQueryBoundP (oa.replicate k) p (k * n) := by
  induction k with
  | zero => exact isQueryBoundP_pure p _ _
  | succ k ih =>
    rw [replicate_succ_bind]
    exact isQueryBoundP_bind_le h (fun _ _ => isQueryBoundP_bind_le ih
      (fun _ _ => isQueryBoundP_pure p _ 0) le_rfl) (by rw [Nat.succ_mul]; omega)

end OracleComp
