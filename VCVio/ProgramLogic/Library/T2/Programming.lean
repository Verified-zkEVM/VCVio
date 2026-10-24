/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.OracleComp.QueryTracking.ProgrammingOracle
public import VCVio.ProgramLogic.Library.T2.Caching

/-!
# Specifications for the programming handler

Specifications for `QueryImpl.withProgramming so policy`, which caches answers and, on a cache
miss at an input the policy programs, answers with the programmed value and raises a bad flag.
Statements use the necessary reading of `OracleComp` (`open scoped OracleComp.Necessary`).

* *One query.* `withProgramming_wp` is exact and has one branch: the answer is the cached one on
  a hit, the programmed one on a programmed miss, and a possible answer of `so` otherwise; the
  cache gains the answer, and the flag is raised exactly on a programmed miss.
* *Whole runs.* `withProgramming` is `QueryImpl.MonotoneState` for "the cache grows and the flag
  is never lowered", so T1's frame steps over an opaque programmed run.
* *Support.* `mem_support_withProgramming_run_iff` splits a reachable step into hit, programmed
  miss and forwarded miss.
-/

@[expose] public section

open OracleSpec OracleComp Std.WP

open scoped OracleComp.Necessary

universe u u' v'

namespace QueryImpl

variable {ι : Type u} [DecidableEq ι] {spec : OracleSpec.{u, u} ι} {ι' : Type u'}
  {spec' : OracleSpec.{u', v'} ι'} (so : QueryImpl spec (OracleComp spec'))
  (policy : ProgrammingPolicy spec)

/-- A reachable programming step is a hit, a programmed miss raising the flag, or a forwarded
miss keeping it; a miss caches its answer. -/
@[simulateQ_nf]
theorem mem_support_withProgramming_run_iff {t : spec.Domain}
    {s s' : spec.QueryCache × Bool} {v : spec.Range t} :
    (v, s') ∈ support ((so.withProgramming policy t).run s) ↔
      (s.1 t = some v ∧ s' = s) ∨ (s.1 t = none ∧
        ((policy t = some v ∧ s' = (s.1.cacheQuery t v, true)) ∨
          (policy t = none ∧ v ∈ support (so t) ∧ s' = (s.1.cacheQuery t v, s.2)))) := by
  rw [withProgramming_apply, StateT.run_mk]
  cases h : s.1 t with
  | some u => simp [eq_comm]
  | none =>
    cases hp : policy t with
    | some u => simp +contextual [eq_comm]
    | none => simp [eq_comm]

/-- A reachable programming step grows the cache, stores the answer, and never lowers the
flag. -/
theorem withProgramming_run_step {t : spec.Domain} {s : spec.QueryCache × Bool}
    {z : spec.Range t × spec.QueryCache × Bool}
    (hz : z ∈ support ((so.withProgramming policy t).run s)) :
    s.1 ≤ z.2.1 ∧ z.2.1 t = some z.1 ∧ (s.2 = true → z.2.2 = true) := by
  obtain ⟨v, c', b'⟩ := z
  obtain ⟨c, b⟩ := s
  rcases (mem_support_withProgramming_run_iff so policy).1 hz with
    ⟨hc, h⟩ | ⟨hc, ⟨-, h⟩ | ⟨-, -, h⟩⟩ <;> simp only [Prod.mk.injEq] at h <;>
    obtain ⟨rfl, rfl⟩ := h
  · exact ⟨le_rfl, hc, id⟩
  · exact ⟨QueryCache.le_cacheQuery _ hc, QueryCache.cacheQuery_self _ _ _, fun _ => rfl⟩
  · exact ⟨QueryCache.le_cacheQuery _ hc, QueryCache.cacheQuery_self _ _ _, id⟩

/-- One programming query over `OracleComp`, exactly and in one branch: the answer is the stored
one on a hit, the programmed one on a programmed miss and a possible answer of `so` on a
forwarded miss; the cache gains it, and the flag is raised exactly on a programmed miss. -/
@[spec]
theorem withProgramming_wp (t : spec.Domain) (post : spec.Range t → spec.QueryCache × Bool → Prop)
    {epost : EStack⟨⟩} :
    ⦃ fun s => ∀ v, (s.1 t = none ∨ s.1 t = some v) →
        (s.1 t = none → ∀ u, policy t = some u → v = u) →
        (s.1 t = none → policy t = none → v ∈ support (so t)) →
        post v (s.1.cacheQuery t v, s.2 || ((s.1 t).isNone && (policy t).isSome)) ⦄
      (so.withProgramming policy t) ⦃ post; epost ⦄ :=
  (OracleComp.ProgramLogic.triple_stateT_iff_forall_mem_support _ _ _ _).2 fun s h v s' hz => by
    rcases (mem_support_withProgramming_run_iff so policy).1 hz with
      ⟨hc, rfl⟩ | ⟨hc, ⟨hp, rfl⟩ | ⟨hp, hv, rfl⟩⟩
    · simpa [hc, QueryCache.cacheQuery_eq_self_of_eq_some hc] using
        h v (Or.inr hc) (by simp [hc]) (by simp [hc])
    · simpa [hc, hp] using h v (Or.inl hc) (fun _ u hu => by simp_all) (by simp [hp])
    · simpa [hc, hp] using h v (Or.inl hc) (by simp [hp]) fun _ _ => hv

/-- A programming handler only grows its cache and never lowers its flag. -/
instance monotoneState_withProgramming :
    (so.withProgramming policy).MonotoneState
      fun s s' => s.1 ≤ s'.1 ∧ (s.2 = true → s'.2 = true) where
  refl _ := ⟨le_rfl, id⟩
  trans _ _ _ h₁ h₂ := ⟨h₁.1.trans h₂.1, h₂.2 ∘ h₁.2⟩
  step _ _ _ hz :=
    let h := withProgramming_run_step so policy hz
    ⟨h.1, h.2.2⟩

/-- A programming run only grows its cache and never lowers its flag, whatever the program. -/
theorem simulateQ_withProgramming_le {α : Type u} (oa : OracleComp spec α)
    (s : spec.QueryCache × Bool) :
    ∀ z ∈ support ((simulateQ (so.withProgramming policy) oa).run s),
      s.1 ≤ z.2.1 ∧ (s.2 = true → z.2.2 = true) :=
  fun _ hz => MonotoneState.rel_of_mem_support hz

end QueryImpl
