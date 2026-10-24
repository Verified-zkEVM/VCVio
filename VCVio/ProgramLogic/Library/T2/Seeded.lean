/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.Eager
public import VCVio.OracleComp.QueryTracking.SeededOracle
public import VCVio.ProgramLogic.Library.T1.Lifts
public import VCVio.ProgramLogic.Library.T1.RunNF

/-!
# Specifications for seeded handlers

Specifications for `QueryImpl.withPregen`, `seededOracle` and `eagerRandomOracle`, which answer a
query from a pre-generated seed when one is left and fall back to the underlying handler
otherwise. `OracleComp`-based statements use the necessary reading
(`open scoped OracleComp.Necessary`).

* *One query.* `seededOracle_wp` and `eagerRandomOracle_wp` (`spec high`), and
  `withPregen_wp_frame` for any `OracleComp`-based fallback, read a step exactly in one branch:
  `fun s => ∀ v s', (s t = [] → s' = s) → (∀ u us, s t = u :: us → v = u ∧ s' = s.update t us) →
  post v s'`. A known seed (`s t = []` or `s t = u :: us`) resolves the hypotheses.
  `withPregen_wp` reads the step under any reading.
* *Whole runs.* A seeded run only consumes its seed: each final seed list is a suffix of the
  initial one. `withPregen` over `OracleComp`, `seededOracle` and `eagerRandomOracle` are
  `QueryImpl.MonotoneState` for this relation, so T1's frame `Spec.simulateQ_monotoneState` steps
  over an opaque seeded run; `simulateQ_withPregen_suffix` is the support form.
* *Erasure.* From the empty seed a seeded run is the unseeded one, paired with the empty seed
  (`simulateQ_withPregen_run_empty`); so `seededOracle` from `∅` is the program itself and
  `eagerRandomOracle` from `∅` is uniform sampling, as equalities of computations.
-/

@[expose] public section

open OracleSpec OracleComp Std.WP

open scoped OracleComp.Necessary

universe u v w w' u' v'

namespace QueryImpl

variable {ι : Type u} [DecidableEq ι] {spec : OracleSpec.{u, u} ι}

section anyBase

variable {m : Type u → Type v} [Monad m]

/-- With a seed left at `t`, a seeded step answers with its head. -/
@[simulateQ_nf]
theorem withPregen_run'_of_eq_cons [LawfulMonad m] (so : QueryImpl spec m) {t : spec.Domain}
    {s : QuerySeed spec} {u : spec.Range t} {us : List (spec.Range t)} (h : s t = u :: us) :
    (so.withPregen t).run' s = pure u := by
  rw [StateT.run'_eq, withPregen_run_cons so h, map_pure]

/-- With no seed left at `t`, a seeded step answers as the underlying handler. -/
@[simulateQ_nf]
theorem withPregen_run'_of_eq_nil [LawfulMonad m] (so : QueryImpl spec m) {t : spec.Domain}
    {s : QuerySeed spec} (h : s t = []) : (so.withPregen t).run' s = so t := by
  rw [StateT.run'_eq, withPregen_run_nil so h, Functor.map_map]
  exact id_map (so t)

/-- From the empty seed, a seeded run is the unseeded run with the seed left empty. -/
theorem simulateQ_withPregen_run_empty [LawfulMonad m] {α : Type u} (so : QueryImpl spec m)
    (oa : OracleComp spec α) :
    (simulateQ so.withPregen oa).run ∅ = (·, ∅) <$> simulateQ so oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t oa ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
      withPregen_run_nil so (QuerySeed.empty_apply t), bind_map_left, map_bind]
    exact bind_congr fun u => ih u

variable {Pred : Type w} {EPred : Type w'} [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]

/-- A seeded step under any reading: the head of the seed is consumed, or the underlying handler
answers and the seed is kept. -/
@[spec low]
theorem withPregen_wp (so : QueryImpl spec m) (t : spec.Domain)
    (post : spec.Range t → QuerySeed spec → Pred) (epost : EPred) :
    ⦃ fun s => match s t with
        | u :: us => post u (s.update t us)
        | [] => wp (so t) (fun v => post v s) epost ⦄
      (so.withPregen t) ⦃ post; epost ⦄ := by
  refine ⟨fun s => ?_⟩
  cases h : s t with
  | cons u us =>
    rw [StateT.wp_apply_eq, withPregen_run_cons so h]
    exact WPMonad.pure_le_wp_pure (m := m) (u, s.update t us) (fun x => post x.1 x.2) epost
  | nil =>
    rw [StateT.wp_apply_eq, withPregen_run_nil so h]
    exact WPMonad.map_le_wp_map (m := m) (·, s) (so t) (fun x => post x.1 x.2) epost

end anyBase

section oracleCompBase

variable {ι' : Type u'} {spec' : OracleSpec.{u', v'} ι'}

/-- A reachable seeded step consumes the head of the seed, or, with no seed left, returns a
possible answer of the underlying handler and keeps the seed. -/
@[simulateQ_nf]
theorem mem_support_withPregen_run_iff (so : QueryImpl spec (OracleComp spec'))
    {t : spec.Domain} {s s' : QuerySeed spec} {v : spec.Range t} :
    (v, s') ∈ support ((so.withPregen t).run s) ↔
      (∃ us, s t = v :: us ∧ s' = s.update t us) ∨
        (s t = [] ∧ v ∈ support (so t) ∧ s' = s) := by
  cases h : s t with
  | cons u us =>
    rw [withPregen_run_cons so h, support_pure]
    simp [eq_comm]
  | nil =>
    rw [withPregen_run_nil so h, support_map]
    simp [eq_comm]

/-- A seeded step over `OracleComp`, exactly and in one branch: with no seed left the seed is kept
and the answer is a possible one of the underlying handler; otherwise the head is consumed. -/
@[spec]
theorem withPregen_wp_frame (so : QueryImpl spec (OracleComp spec')) (t : spec.Domain)
    (post : spec.Range t → QuerySeed spec → Prop) {epost : EStack⟨⟩} :
    ⦃ fun s => ∀ v s', (s t = [] → s' = s ∧ v ∈ support (so t)) →
        (∀ u us, s t = u :: us → v = u ∧ s' = s.update t us) → post v s' ⦄
      (so.withPregen t) ⦃ post; epost ⦄ :=
  (OracleComp.ProgramLogic.triple_stateT_iff_forall_mem_support _ _ _ _).2 fun s h v s' hz => by
    rcases (mem_support_withPregen_run_iff so).1 hz with ⟨us, hs, rfl⟩ | ⟨hs, hv, rfl⟩
    · exact h _ _ (fun h' => by simp [hs] at h') fun u us' h' => by simp_all
    · exact h _ _ (fun _ => ⟨rfl, hv⟩) fun u us h' => by simp [hs] at h'

/-- A seeded step only consumes its seed: every seed list ends in a suffix of the initial one. -/
theorem withPregen_run_suffix (so : QueryImpl spec (OracleComp spec')) {t : spec.Domain}
    {s : QuerySeed spec} {z : spec.Range t × QuerySeed spec}
    (hz : z ∈ support ((so.withPregen t).run s)) (i : ι) : z.2 i <:+ s i := by
  rcases (mem_support_withPregen_run_iff so).1 hz with ⟨us, hs, h⟩ | ⟨-, -, h⟩
  · rw [h]
    rcases eq_or_ne i t with rfl | hi
    · rw [QuerySeed.update_self, hs]
      exact List.suffix_cons _ _
    · rw [QuerySeed.update_of_ne _ _ _ _ hi]
  · rw [h]

/-- A seeded handler over `OracleComp` only consumes its seed, so whole runs are framed by "each
seed list ends in a suffix of the initial one". -/
instance monotoneState_withPregen (so : QueryImpl spec (OracleComp spec')) :
    so.withPregen.MonotoneState fun s s' => ∀ i, s' i <:+ s i where
  refl _ _ := List.suffix_refl _
  trans _ _ _ h₁₂ h₂₃ i := (h₂₃ i).trans (h₁₂ i)
  step _ _ _ hz := withPregen_run_suffix so hz

/-- A seeded run only consumes its seed, whatever the program: each final seed list is a suffix
of the initial one. -/
theorem simulateQ_withPregen_suffix {α : Type u} (so : QueryImpl spec (OracleComp spec'))
    (oa : OracleComp spec α) (s : QuerySeed spec) :
    ∀ z ∈ support ((simulateQ so.withPregen oa).run s), ∀ i, z.2 i <:+ s i :=
  fun _ hz => MonotoneState.rel_of_mem_support hz

end oracleCompBase

attribute [simulateQ_nf] withPregen_run_cons withPregen_run_nil

end QueryImpl

namespace seededOracle

variable {ι : Type u} [DecidableEq ι] {spec : OracleSpec.{u, u} ι}

/-- A reachable `seededOracle` step consumes the head of the seed, or keeps an exhausted seed. -/
@[simulateQ_nf]
theorem mem_support_run_iff {t : spec.Domain} {s s' : QuerySeed spec} {v : spec.Range t} :
    (v, s') ∈ support ((seededOracle t).run s) ↔
      (∃ us, s t = v :: us ∧ s' = s.update t us) ∨ (s t = [] ∧ s' = s) := by
  rw [eq_withPregen, QueryImpl.mem_support_withPregen_run_iff]
  simp

/-- `seededOracle` only consumes its seed. -/
instance monotoneState : (spec.seededOracle).MonotoneState fun s s' => ∀ i, s' i <:+ s i :=
  QueryImpl.monotoneState_withPregen _

/-- From the empty seed, a `seededOracle` run is the program itself. -/
theorem run'_simulateQ_empty {α : Type u} (oa : OracleComp spec α) :
    (simulateQ seededOracle oa).run' ∅ = oa := by
  rw [StateT.run'_eq, eq_withPregen, QueryImpl.simulateQ_withPregen_run_empty, Functor.map_map]
  simp

end seededOracle

namespace eagerRandomOracle

variable {ι : Type} [DecidableEq ι] {spec : OracleSpec.{0, 0} ι}
  [∀ t : spec.Domain, SampleableType (spec.Range t)]

/-- The eager random oracle is the seeded uniform sampler. -/
theorem eq_withPregen : (eagerRandomOracle (spec := spec)) = uniformSampleImpl.withPregen := rfl

/-- A reachable eager step consumes the head of the seed, or samples with the seed kept. -/
@[simulateQ_nf high]
theorem mem_support_run_iff {t : spec.Domain} {s s' : QuerySeed spec} {v : spec.Range t} :
    (v, s') ∈ support ((eagerRandomOracle t).run s) ↔
      (∃ us, s t = v :: us ∧ s' = s.update t us) ∨ (s t = [] ∧ s' = s) := by
  rw [eq_withPregen, QueryImpl.mem_support_withPregen_run_iff, uniformSampleImpl_apply]
  simp

/-- The eager random oracle only consumes its seed. -/
instance monotoneState :
    (eagerRandomOracle (spec := spec)).MonotoneState fun s s' => ∀ i, s' i <:+ s i :=
  QueryImpl.monotoneState_withPregen _

/-- From the empty seed, the eager random oracle is uniform sampling, as a computation. -/
theorem run'_simulateQ_empty {α : Type} (oa : OracleComp spec α) :
    (simulateQ eagerRandomOracle oa).run' ∅ = simulateQ uniformSampleImpl oa := by
  rw [StateT.run'_eq, eq_withPregen, QueryImpl.simulateQ_withPregen_run_empty, Functor.map_map]
  exact id_map _

end eagerRandomOracle

namespace OracleComp.ProgramLogic

section seeded

variable {ι : Type u} [DecidableEq ι] {spec : OracleSpec.{u, u} ι}

/-- One `seededOracle` query, exactly and in one branch. The default rule of `vcgen` for
`seededOracle`. -/
@[spec high]
theorem seededOracle_wp (t : spec.Domain) (post : spec.Range t → QuerySeed spec → Prop)
    {epost : EStack⟨⟩} :
    ⦃ fun s => ∀ v s', (s t = [] → s' = s) →
        (∀ u us, s t = u :: us → v = u ∧ s' = s.update t us) → post v s' ⦄
      (spec.seededOracle t) ⦃ post; epost ⦄ :=
  (triple_stateT_iff_forall_mem_support _ _ _ _).2 fun s h v s' hz => by
    rcases seededOracle.mem_support_run_iff.1 hz with ⟨us, hs, rfl⟩ | ⟨hs, rfl⟩
    · exact h _ _ (fun h' => by simp [hs] at h') fun u us' h' => by simp_all
    · exact h _ _ (fun _ => rfl) fun u us h' => by simp [hs] at h'

end seeded

section eager

variable {ι : Type} [DecidableEq ι] {spec : OracleSpec.{0, 0} ι}
  [∀ t : spec.Domain, SampleableType (spec.Range t)]

/-- One eager random-oracle query, exactly and in one branch. -/
@[spec high]
theorem eagerRandomOracle_wp (t : spec.Domain) (post : spec.Range t → QuerySeed spec → Prop)
    {epost : EStack⟨⟩} :
    ⦃ fun s => ∀ v s', (s t = [] → s' = s) →
        (∀ u us, s t = u :: us → v = u ∧ s' = s.update t us) → post v s' ⦄
      (eagerRandomOracle (spec := spec) t) ⦃ post; epost ⦄ :=
  (triple_stateT_iff_forall_mem_support _ _ _ _).2 fun s h v s' hz => by
    rcases eagerRandomOracle.mem_support_run_iff.1 hz with ⟨us, hs, rfl⟩ | ⟨hs, rfl⟩
    · exact h _ _ (fun h' => by simp [hs] at h') fun u us' h' => by simp_all
    · exact h _ _ (fun _ => rfl) fun u us h' => by simp [hs] at h'

end eager

end OracleComp.ProgramLogic
