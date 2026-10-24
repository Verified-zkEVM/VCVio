/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.CryptoFoundations.PRF
public import VCVio.ProgramLogic.Library

/-!
# Specifications for the PRF experiment handlers

Specifications for `PRFScheme.prfRealQueryImpl` (the keyed function, stateless) and
`PRFScheme.prfIdealQueryImpl` (the lazy random oracle `romImpl`, over a cache), under the
necessary reading (`open scoped OracleComp.Necessary`).

* *One query.* `Spec.simulateQ_functionQuery` exposes `functionQuery` to `vcgen`, and
  `@[spec high]` rules cover both branches of both handlers: the real function query
  returns `prf.eval k d`; the ideal one is exact and in one branch, `fun c => ∀ v, (c d = none ∨
  c d = some v) → post v (c.cacheQuery d v)`; uniform queries return any answer and keep the
  state. Posts are typed at `PRFOracleSpec`'s answer type.
* *Support.* `mem_support_*_iff` (in `simulateQ_nf`).
* *Whole runs.* The ideal handler is `QueryImpl.MonotoneState` for the cache order (it is
  `romImpl`), so `vcgen` frames an opaque distinguisher. A real run is deterministic on function
  queries: `simulateQ_prfRealQueryImpl_bind_functionQuery_self` collapses a repeated query, and
  `prfRealQueryImpl_eq_ideal_of_agree` identifies a real run with an ideal run from a cache that
  agrees with the key on every point.
* *Fresh points.* An ideal function query at an uncached point is uniform
  (`prEvent_prfIdealQueryImpl_run'_eq_of_eq_none`).
-/

@[expose] public section

open OracleSpec OracleComp OracleComp.ProgramLogic Std.WP ENNReal

open scoped OracleComp.Necessary

universe v w w'

namespace PRFScheme

variable {K D R : Type}

/-- A simulated function query runs the handler at `Sum.inr d`, under any reading of the handler's
monad. `functionQuery` is not reducible, so `vcgen` needs this rule to see the query; the post
is re-typed at the sum's answer type, where the handler rules are stated. -/
@[spec high]
theorem Spec.simulateQ_functionQuery {m : Type → Type v} [Monad m] {Pred : Type w}
    {EPred : Type w'} [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    (impl : QueryImpl (PRFOracleSpec D R) m) (d : D) {post : R → Pred} {epost : EPred} :
    Triple (simulateQ impl (functionQuery d))
      (wp (impl (.inr d)) (fun u : (PRFOracleSpec D R).Range (.inr d) => post u) epost)
      post epost :=
  Spec.simulateQ_spec_query impl (.inr d)

/-! ## The real handler -/

section real

variable (prf : PRFScheme K D R) (k : K)

/-- A real function query returns the keyed function's value. -/
@[simulateQ_nf]
theorem mem_support_prfRealQueryImpl_inr_iff {d : D} {r : (PRFOracleSpec D R).Range (.inr d)} :
    r ∈ support (prf.prfRealQueryImpl k (.inr d)) ↔ r = prf.eval k d := by
  rw [prfRealQueryImpl_apply_inr, support_pure, Set.mem_singleton_iff]

/-- One real function query: the answer is `prf.eval k d`. -/
@[spec high]
theorem prfRealQueryImpl_wp_inr (d : D) (post : (PRFOracleSpec D R).Range (.inr d) → Prop)
    {epost : EStack⟨⟩} :
    ⦃ post (prf.eval k d) ⦄ prf.prfRealQueryImpl k (.inr d) ⦃ post; epost ⦄ :=
  (triple_iff_forall_mem_support _ _ _ _).2 fun h _ hr =>
    (mem_support_prfRealQueryImpl_inr_iff prf k).1 hr ▸ h

/-- One real uniform query: any answer. -/
@[spec high]
theorem prfRealQueryImpl_wp_inl (n : ℕ) (post : (PRFOracleSpec D R).Range (.inl n) → Prop)
    {epost : EStack⟨⟩} :
    ⦃ ∀ u, post u ⦄ prf.prfRealQueryImpl k (.inl n) ⦃ post; epost ⦄ :=
  (triple_iff_forall_mem_support _ _ _ _).2 fun h r _ => h r

/-- A repeated real function query at the same point returns the same answer. -/
theorem simulateQ_prfRealQueryImpl_bind_functionQuery_self {β : Type} (d : D)
    (f : R → R → OracleComp (PRFOracleSpec D R) β) :
    simulateQ (prf.prfRealQueryImpl k) (functionQuery d >>= fun a => functionQuery d >>= f a) =
      simulateQ (prf.prfRealQueryImpl k) (f (prf.eval k d) (prf.eval k d)) := by
  simp

end real

/-! ## The ideal handler -/

section ideal

variable [DecidableEq D] [SampleableType R]

/-- An ideal function query is a lazy random-oracle step. -/
@[simulateQ_nf]
theorem mem_support_prfIdealQueryImpl_inr_iff {d : D} {c c' : (D →ₒ R).QueryCache}
    {v : (PRFOracleSpec D R).Range (.inr d)} :
    (v, c') ∈ support ((prfIdealQueryImpl (D := D) (R := R) (.inr d)).run c) ↔
      (c d = some v ∧ c' = c) ∨ (c d = none ∧ c' = c.cacheQuery d v) := by
  rw [prfIdealQueryImpl_apply_inr]
  exact randomOracle.mem_support_run_iff

/-- An ideal uniform query keeps the cache. -/
@[simulateQ_nf]
theorem mem_support_prfIdealQueryImpl_inl_iff {n : ℕ} {c c' : (D →ₒ R).QueryCache}
    {u : (PRFOracleSpec D R).Range (.inl n)} :
    (u, c') ∈ support ((prfIdealQueryImpl (D := D) (R := R) (.inl n)).run c) ↔ c' = c := by
  change (u, c') ∈ support ((unifFwdImpl (D →ₒ R) n).run c) ↔ _
  rw [unifFwdImpl_run_apply, support_map]
  simp [eq_comm]

/-- One ideal function query, exactly: the stored answer on a hit, any answer on a miss, cached. -/
@[spec high]
theorem prfIdealQueryImpl_wp_inr (d : D)
    (post : (PRFOracleSpec D R).Range (.inr d) → (D →ₒ R).QueryCache → Prop) {epost : EStack⟨⟩} :
    ⦃ fun c => ∀ v, (c d = none ∨ c d = some v) → post v (c.cacheQuery d v) ⦄
      prfIdealQueryImpl (D := D) (R := R) (.inr d) ⦃ post; epost ⦄ :=
  (triple_stateT_iff_forall_mem_support _ _ _ _).2 fun c h v c' hz => by
    rcases (mem_support_prfIdealQueryImpl_inr_iff (D := D) (R := R)).1 hz with
      ⟨hc, rfl⟩ | ⟨hc, rfl⟩
    · simpa [QueryCache.cacheQuery_eq_self_of_eq_some hc] using h v (.inr hc)
    · exact h v (.inl hc)

/-- One ideal uniform query: any answer, the cache unchanged. -/
@[spec high]
theorem prfIdealQueryImpl_wp_inl (n : ℕ)
    (post : (PRFOracleSpec D R).Range (.inl n) → (D →ₒ R).QueryCache → Prop) {epost : EStack⟨⟩} :
    ⦃ fun c => ∀ u, post u c ⦄ prfIdealQueryImpl (D := D) (R := R) (.inl n) ⦃ post; epost ⦄ :=
  (triple_stateT_iff_forall_mem_support _ _ _ _).2 fun _ h u _ hz =>
    (mem_support_prfIdealQueryImpl_inl_iff (D := D) (R := R)).1 hz ▸ h u

/-- The ideal handler only grows its cache. -/
instance monotoneState_prfIdealQueryImpl :
    (prfIdealQueryImpl (D := D) (R := R)).MonotoneState (· ≤ ·) :=
  inferInstanceAs ((D →ₒ R).romImpl.MonotoneState (· ≤ ·))

/-- An ideal function query at an uncached point answers each value with probability
`1 / |R|`. -/
theorem prEvent_prfIdealQueryImpl_run'_eq_of_eq_none [Fintype R] {d : D}
    {c : (D →ₒ R).QueryCache} (h : c d = none) (r : R) :
    Pr{let v ← (prfIdealQueryImpl (D := D) (R := R) (.inr d)).run' c}[v = r] =
      (Fintype.card R : ℝ≥0∞)⁻¹ := by
  rw [prfIdealQueryImpl_apply_inr]
  exact randomOracle.prEvent_run'_eq_of_eq_none h r

/-- On a cache that agrees with the key everywhere, the ideal handler answers like the real one
and keeps the cache. -/
theorem prfIdealQueryImpl_run_eq_of_agree (prf : PRFScheme K D R) (k : K)
    {c : (D →ₒ R).QueryCache} (hc : ∀ d, c d = some (prf.eval k d))
    (t : (PRFOracleSpec D R).Domain) :
    (prfIdealQueryImpl (D := D) (R := R) t).run c = (·, c) <$> prf.prfRealQueryImpl k t := by
  rcases t with n | d
  · change (unifFwdImpl (D →ₒ R) n).run c = _
    rw [unifFwdImpl_run_apply]
    rfl
  · rw [prfIdealQueryImpl_apply_inr, prfRealQueryImpl_apply_inr, map_pure]
    exact randomOracle.run_of_eq_some (hc d)

/-- A real run is an ideal run from a cache agreeing with the key on every point. -/
theorem prfRealQueryImpl_eq_ideal_of_agree (prf : PRFScheme K D R) (k : K)
    {c : (D →ₒ R).QueryCache} (hc : ∀ d, c d = some (prf.eval k d)) {α : Type}
    (oa : OracleComp (PRFOracleSpec D R) α) :
    (simulateQ (prfIdealQueryImpl (D := D) (R := R)) oa).run' c =
      simulateQ (prf.prfRealQueryImpl k) oa := by
  induction oa using OracleComp.inductionOn generalizing c with
  | pure a => simp
  | query_bind t f ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run'_eq, StateT.run_bind,
      prfIdealQueryImpl_run_eq_of_agree prf k hc t, bind_map_left, map_bind]
    exact bind_congr fun a => by rw [← StateT.run'_eq, ih a hc]

end ideal

end PRFScheme
