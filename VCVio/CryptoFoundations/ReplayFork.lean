/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.CryptoFoundations.SeededFork
import VCVio.OracleComp.QueryTracking.LoggingOracle
import PolyFun.PFunctor.Free.Context

/-!
# Replay-Based Forking

This file proves a replay-style forking lemma using PolyFun's typed execution
paths and occurrence contexts. A first path selects an oracle occurrence; the
same context is then completed independently a second time. The shared prefix
and both suffixes are intrinsic in `PFunctor.FreeM.Path.ForkView`, leaving the
VCVio layer responsible only for probability and collision estimates.

The accompanying `QueryLog` view is an erasure interface for applications such
as Fiat--Shamir that state postconditions over transcripts.
-/

open OracleSpec OracleComp OracleComp.ProgramLogic ENNReal Function Finset

open scoped OracleSpec.PrimitiveQuery
open scoped PFunctor

-- Dependent path/zipper APIs must see that an oracle specification's
-- polynomial positions and directions are its domain and ranges. Keep this
-- transparency local: exporting it changes simplifier normal forms in
-- unrelated OracleComp proofs.
set_option allowUnsafeReducibility true in
attribute [local reducible] OracleSpec.toPFunctor PFunctor.Idx

namespace QueryLog

variable {ι : Type} {spec : OracleSpec ι}

/-- The `n`-th answer in the log for queries to oracle `t`, if it exists. -/
def getQueryValue? [spec.DecidableEq] (log : QueryLog spec) (t : ι) (n : Nat) :
    Option (spec.Range t) :=
  match (log.getQ (· = t))[n]? with
  | none => none
  | some ⟨t', u⟩ => if h : t' = t then some (h ▸ u) else none

/-- Decompose `getQ` across a `logQuery` step. -/
lemma getQ_logQuery (log : QueryLog spec) (t : ι) (u : spec.Range t)
    (p : ι → Prop) [DecidablePred p] :
    (log.logQuery t u).getQ p = log.getQ p ++ (if p t then [⟨t, u⟩] else []) := by
  simp [QueryLog.logQuery, QueryLog.singleton]

/-- If `getQueryValue? log t n = some u`, then the `n`-th `t`-filtered entry of
`log` is `⟨t, u⟩`. -/
lemma getQ_getElem?_eq_of_getQueryValue?_eq_some [spec.DecidableEq]
    (log : QueryLog spec) (t : ι) (n : Nat) (u : spec.Range t)
    (h : getQueryValue? log t n = some u) :
    (log.getQ (· = t))[n]? = some ⟨t, u⟩ := by
  rcases hopt : (log.getQ (· = t))[n]? with _ | ⟨t', u'⟩
  · simp [getQueryValue?, hopt] at h
  · obtain rfl : t' = t := by by_contra ht; simp [getQueryValue?, hopt, ht] at h
    simpa [getQueryValue?, hopt] using h

/-- Converse: if the `n`-th `t`-filtered entry is `⟨t, u⟩`, then
`getQueryValue? log t n = some u`. -/
lemma getQueryValue?_eq_some_of_getQ_getElem? [spec.DecidableEq]
    (log : QueryLog spec) (t : ι) (n : Nat) (u : spec.Range t)
    (h : (log.getQ (· = t))[n]? = some ⟨t, u⟩) :
    getQueryValue? log t n = some u := by
  simp [getQueryValue?, h]

/-- Every entry of `log.getQ (· = t)` has its first component equal to `t`. -/
lemma getQ_eq_mem [spec.DecidableEq] (log : QueryLog spec) (t : ι)
    {entry : (t' : ι) × spec.Range t'} (h : entry ∈ log.getQ (· = t)) :
    entry.1 = t := by
  induction log <;> grind [QueryLog.getQ_cons, QueryLog.getQ_nil]

/-- If the `t`-filtered log has at least `n + 1` entries, then `getQueryValue? log t n`
is `some _`. -/
lemma getQueryValue?_isSome_of_lt [spec.DecidableEq] (log : QueryLog spec) (t : ι) (n : Nat)
    (h : n < (log.getQ (· = t)).length) :
    (getQueryValue? log t n).isSome := by
  simp [getQueryValue?, List.getElem?_eq_getElem h, getQ_eq_mem log t (List.getElem_mem h)]

/-- Prepending an entry whose oracle index does not match `t` leaves the `t`-indexed
view of the log unchanged. -/
lemma getQueryValue?_cons_of_ne [spec.DecidableEq]
    (entry : (t' : ι) × spec.Range t') (log : QueryLog spec) (t : ι) (n : Nat)
    (h : entry.1 ≠ t) :
    getQueryValue? (entry :: log) t n = getQueryValue? log t n := by
  simp [getQueryValue?, QueryLog.getQ_cons, h]

/-- The first entry of `getQueryValue? (⟨t, u⟩ :: log) t 0` is the prepended value. -/
lemma getQueryValue?_cons_self_zero [spec.DecidableEq]
    (t : ι) (u : spec.Range t) (log : QueryLog spec) :
    getQueryValue? (⟨t, u⟩ :: log) t 0 = some u :=
  getQueryValue?_eq_some_of_getQ_getElem? _ _ _ _ (by simp [QueryLog.getQ_cons])

/-- Prepending a matching `⟨t, _⟩` entry shifts later `t`-indexed lookups by one. -/
lemma getQueryValue?_cons_self_succ [spec.DecidableEq]
    (t : ι) (u : spec.Range t) (log : QueryLog spec) (n : Nat) :
    getQueryValue? (⟨t, u⟩ :: log) t (n + 1) = getQueryValue? log t n := by
  simp [getQueryValue?, QueryLog.getQ_cons]

/-- The entry immediately following a prefix is the next occurrence of its
oracle index after all matching entries in that prefix. -/
lemma getQueryValue?_append_self_at_countQ [spec.DecidableEq]
    (before after : QueryLog spec) (t : ι) (u : spec.Range t) :
    getQueryValue? (before ++ ⟨t, u⟩ :: after) t (before.countQ (· = t)) = some u := by
  apply getQueryValue?_eq_some_of_getQ_getElem?
  simp [QueryLog.countQ]

/-- Query-log counting is the `OracleSpec` specialization of PolyFun's
generic occurrence count on erased polynomial traces. -/
lemma countQ_eq_occurrences [spec.DecidableEq] (log : QueryLog spec) (t : ι) :
    log.countQ (· = t) = PFunctor.FreeM.Path.occurrences (P := spec.toPFunctor) t
      (show PFunctor.TraceList spec.toPFunctor from log) := by
  induction log with
  | nil => rfl
  | cons entry log ih =>
      rcases entry with ⟨t', u⟩
      by_cases h : t' = t
      · subst t'
        simp only [QueryLog.countQ, QueryLog.getQ_cons, if_pos trivial,
          List.length_cons]
        rw [PFunctor.FreeM.Path.occurrences,
          List.countP_cons_of_pos (by simp)]
        rw [PFunctor.FreeM.Path.occurrences] at ih
        simpa [QueryLog.countQ] using ih
      · simp only [QueryLog.countQ, QueryLog.getQ_cons, if_neg h]
        rw [PFunctor.FreeM.Path.occurrences,
          List.countP_cons_of_neg (by simp [h])]
        rw [PFunctor.FreeM.Path.occurrences] at ih
        simpa [QueryLog.countQ] using ih

end QueryLog

namespace OracleComp

variable {ι : Type} {spec : OracleSpec ι} {α : Type}

/-- Run `main` with query logging. This is the first-run object for replay forks. -/
@[reducible]
def replayFirstRun (main : OracleComp spec α) : OracleComp spec (α × QueryLog spec) :=
  (simulateQ spec.loggingOracle main).run

/-- The first run represented intrinsically: executing `main` returns the
typed root-to-leaf path selected by its oracle answers. -/
def replayFirstPath (main : OracleComp spec α) :
    OracleComp spec (PFunctor.FreeM.Path main) :=
  PFunctor.FreeM.withPath main

/-- Forget an intrinsic first-run path into the output/transcript pair used by
the probability-facing replay API. -/
def replayPathResult (main : OracleComp spec α)
    (path : PFunctor.FreeM.Path main) : α × QueryLog spec :=
  ⟨PFunctor.FreeM.output main path, PFunctor.FreeM.Path.trace main path⟩

@[simp] theorem replayFirstPath_query_bind (t : spec.Domain)
    (next : spec.Range t → OracleComp spec α) :
    replayFirstPath (liftM (query t) >>= next) =
      OracleComp.queryBind t fun u =>
        PFunctor.FreeM.map
          (fun path : PFunctor.FreeM.Path (next u) =>
            (⟨u, path⟩ : PFunctor.FreeM.Path (OracleComp.queryBind t next)))
          (replayFirstPath (next u)) :=
  rfl

/-- Intrinsic path execution and writer-style query logging are the same first
run after erasing the path to its output and trace. This is the bridge that
lets replay proofs use typed paths without changing their probability API. -/
theorem map_replayPathResult_replayFirstPath (main : OracleComp spec α) :
    PFunctor.FreeM.map (replayPathResult main) (replayFirstPath main) =
      replayFirstRun main := by
  induction main using OracleComp.inductionOn with
  | pure x => rfl
  | query_bind t next ih =>
      rw [replayFirstRun, OracleComp.run_simulateQ_loggingOracle_query_bind]
      rw [replayFirstPath_query_bind]
      simp only [PFunctor.FreeM.map]
      change
        OracleComp.queryBind t (fun u =>
          PFunctor.FreeM.map
            (replayPathResult (OracleComp.queryBind t next))
            (PFunctor.FreeM.map
              (fun path : PFunctor.FreeM.Path (next u) =>
                (⟨u, path⟩ : PFunctor.FreeM.Path (OracleComp.queryBind t next)))
              (replayFirstPath (next u)))) =
          OracleComp.queryBind t (fun u =>
            PFunctor.FreeM.map
              (fun p : α × QueryLog spec => (p.1, ⟨t, u⟩ :: p.2))
              (replayFirstRun (next u)))
      apply congrArg (OracleComp.queryBind t)
      funext u
      rw [← ih u, ← PFunctor.FreeM.comp_map, ← PFunctor.FreeM.comp_map]
      rfl

/-- A supported intrinsic path erases to a supported legacy first-run result. -/
lemma replayPathResult_mem_support_replayFirstRun
    (main : OracleComp spec α) (path : PFunctor.FreeM.Path main)
    (hpath : path ∈ support (replayFirstPath main)) :
    replayPathResult main path ∈ support (replayFirstRun main) := by
  rw [← map_replayPathResult_replayFirstPath]
  change replayPathResult main path ∈ support
    ((replayPathResult main <$> replayFirstPath main) : OracleComp spec _)
  rw [support_map, Set.mem_image]
  exact ⟨path, hpath, rfl⟩

/-- Every well-typed path through an oracle computation is supported. Oracle
queries have universal symbolic support, so a `Path` already contains all the
evidence needed to select its successive branches. -/
lemma mem_support_replayFirstPath (main : OracleComp spec α)
    (path : PFunctor.FreeM.Path main) :
    path ∈ support (replayFirstPath main) := by
  induction main with
  | pure x =>
      cases path
      change PUnit.unit ∈ support (pure PUnit.unit : OracleComp spec PUnit)
      simp
  | queryBind t next ih =>
      rcases path with ⟨answer, tail⟩
      change (⟨answer, tail⟩ : PFunctor.FreeM.Path (OracleComp.queryBind t next)) ∈
        support ((spec.query t : OracleComp spec _) >>= fun u =>
          (((fun inner : PFunctor.FreeM.Path (next u) =>
              (⟨u, inner⟩ : PFunctor.FreeM.Path (OracleComp.queryBind t next))) <$>
            replayFirstPath (next u)) : OracleComp spec _))
      rw [mem_support_bind_iff]
      refine ⟨answer, by simp, ?_⟩
      simpa only [support_map, Set.mem_image] using
        (show ∃ inner ∈ support (replayFirstPath (next answer)),
          (⟨answer, inner⟩ : PFunctor.FreeM.Path (OracleComp.queryBind t next)) =
            (⟨answer, tail⟩ : PFunctor.FreeM.Path (OracleComp.queryBind t next)) from
          ⟨tail, ih answer tail, rfl⟩)

/-- Forgetting the path produced by the intrinsic first run recovers the
original oracle computation. -/
@[simp] theorem map_output_replayFirstPath (main : OracleComp spec α) :
    (PFunctor.FreeM.output main <$> replayFirstPath main : OracleComp spec α) = main := by
  exact PFunctor.FreeM.map_output_withPath main

/-- The selected entry of an occurrence completion's erased trace is exactly
its focused answer. -/
lemma getQueryValue?_completion_path_eq_answer [spec.DecidableEq]
    {main : OracleComp spec α} {i : ι} {n : Nat}
    (occurrence : PFunctor.FreeM.Path.Occurrence i main n)
    (completion : occurrence.Completion) :
    QueryLog.getQueryValue?
      (PFunctor.FreeM.Path.trace main completion.path) i n =
        some completion.answer := by
  change QueryLog.getQueryValue?
    (PFunctor.FreeM.Path.trace main
      (occurrence.plug completion.answer completion.suffix)) i n =
        some completion.answer
  rw [PFunctor.FreeM.Path.Occurrence.trace_plug]
  have hcount :
      (show QueryLog spec from occurrence.before).countQ (· = i) = n := by
    rw [QueryLog.countQ_eq_occurrences]
    exact occurrence.before_count
  change QueryLog.getQueryValue?
    ((show QueryLog spec from occurrence.before) ++
      (⟨i, completion.answer⟩ ::
        PFunctor.FreeM.Path.trace
          (occurrence.resume completion.answer) completion.suffix)) i n =
      some completion.answer
  simpa only [hcount] using QueryLog.getQueryValue?_append_self_at_countQ
    (show QueryLog spec from occurrence.before)
    (PFunctor.FreeM.Path.trace
      (occurrence.resume completion.answer) completion.suffix)
    i completion.answer

section quantitative

variable [spec.DecidableEq]

/-- Reachability hypothesis on the fork-index selector `cf`: whenever the first run
of `main` outputs `x` and the recorded log is `log`, every selected fork index
`s = cf x` actually corresponds to an `i`-query in `log` (i.e. the `s`-th
`i`-query exists in the log). In Fiat--Shamir applications `cf` extracts the
index of a recorded query, so this property holds by construction. -/
def CfReachable (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) : Prop :=
  ∀ {x : α} {log : QueryLog spec},
    (x, log) ∈ support (replayFirstRun main) →
    ∀ s : Fin (qb i + 1), cf x = some s →
      (QueryLog.getQueryValue? log i ↑s).isSome

/-- Intrinsic form of selector reachability: every selected ordinal is an
actual occurrence on the typed execution path. -/
def PathCfReachable (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) : Prop :=
  ∀ (path : PFunctor.FreeM.Path main) (s : Fin (qb i + 1)),
    cf (PFunctor.FreeM.output main path) = some s →
      (PFunctor.FreeM.Path.locateAt? (P := spec.toPFunctor) i main path s).isSome

/-- Transcript reachability implies the canonical path-level condition. -/
theorem CfReachable.toPathCfReachable
    {main : OracleComp spec α} {qb : ι → ℕ} {i : ι}
    {cf : α → Option (Fin (qb i + 1))} (hreach : CfReachable main qb i cf) :
    PathCfReachable main qb i cf := by
  intro path s hcf
  have hpath : path ∈ support (replayFirstPath main) :=
    mem_support_replayFirstPath main path
  have hrun := replayPathResult_mem_support_replayFirstRun main path hpath
  have hsome := hreach hrun s (by simpa [replayPathResult] using hcf)
  rcases hlookup : QueryLog.getQueryValue?
      (PFunctor.FreeM.Path.trace main path) i (s : Nat) with _ | answer
  · simp [hlookup] at hsome
  · have hget := QueryLog.getQ_getElem?_eq_of_getQueryValue?_eq_some
      (PFunctor.FreeM.Path.trace main path) i (s : Nat) answer hlookup
    have hlt : (s : Nat) <
        ((show QueryLog spec from PFunctor.FreeM.Path.trace main path).getQ
          (· = i)).length :=
      (List.getElem?_eq_some_iff.1 hget).1
    rw [PFunctor.FreeM.Path.locateAt?_isSome_iff_lt_occurrences]
    rw [← QueryLog.countQ_eq_occurrences]
    exact hlt

/-! ## Intrinsic quantitative games -/

/-- Two independent completions of occurrence `s`, represented entirely by
PolyFun's typed context machinery. -/
def contextForkView (main : OracleComp spec α) (i : ι) (s : Nat) :
    OracleComp spec (Option (PFunctor.FreeM.Path.ForkView i main s)) :=
  PFunctor.FreeM.Path.reforkAt (P := spec.toPFunctor) i main s

/-- Pure success classifier shared by fixed and dynamically selected context
experiments. All probabilistic structure remains in PolyFun's reforking
combinators. -/
private def classifyForkView
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) (s : Fin (qb i + 1))
    (view : PFunctor.FreeM.Path.ForkView i main s) : Option (α × α) :=
  let x₁ := PFunctor.FreeM.output main view.firstPath
  let x₂ := PFunctor.FreeM.output main view.secondPath
  if view.firstAnswer = view.secondAnswer then none
  else if cf x₁ = some s ∧ cf x₂ = some s then some (x₁, x₂)
  else none

@[simp] private theorem classifyForkView_isSome
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) (s : Fin (qb i + 1))
    (view : PFunctor.FreeM.Path.ForkView i main s) :
    (classifyForkView main qb i cf s view).isSome ↔
      view.firstAnswer ≠ view.secondAnswer ∧
        cf (PFunctor.FreeM.output main view.firstPath) = some s ∧
        cf (PFunctor.FreeM.output main view.secondPath) = some s := by
  simp only [classifyForkView]
  grind

private theorem classifyForkView_eq_some_iff
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) (s : Fin (qb i + 1))
    (view : PFunctor.FreeM.Path.ForkView i main s) (x₁ x₂ : α) :
    classifyForkView main qb i cf s view = some (x₁, x₂) ↔
      view.firstAnswer ≠ view.secondAnswer ∧
        cf (PFunctor.FreeM.output main view.firstPath) = some s ∧
        cf (PFunctor.FreeM.output main view.secondPath) = some s ∧
        x₁ = PFunctor.FreeM.output main view.firstPath ∧
        x₂ = PFunctor.FreeM.output main view.secondPath := by
  simp only [classifyForkView]
  grind

private theorem classifyForkView_component_iff
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) (s : Fin (qb i + 1))
    (view : PFunctor.FreeM.Path.ForkView i main s) :
    (classifyForkView main qb i cf s view).map (cf ∘ Prod.fst) =
        some (some s) ↔
      (classifyForkView main qb i cf s view).isSome := by
  simp only [classifyForkView]
  grind

private theorem classifyForkView_component_ne
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) (t s : Fin (qb i + 1))
    (view : PFunctor.FreeM.Path.ForkView i main t) (hne : t ≠ s) :
    (classifyForkView main qb i cf t view).map (cf ∘ Prod.fst) ≠
      some (some s) := by
  simp only [classifyForkView]
  grind

/-- Semantic result of a dynamically selected fork.  The selecting ordinal,
shared occurrence context, and both completions remain available to
reduction-facing proofs. -/
abbrev ContextForkWitness
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι) :=
  PFunctor.FreeM.Path.SelectedForkView i main (Fin (qb i + 1))
    (fun s => (s : Nat))

private def acceptContextForkWitness
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) (s : Fin (qb i + 1))
    (view : PFunctor.FreeM.Path.ForkView i main s) :
    Option (ContextForkWitness main qb i) :=
  if (classifyForkView main qb i cf s view).isSome then
    some ⟨s, view⟩
  else none

@[simp] private theorem acceptContextForkWitness_eq_some
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) (s : Fin (qb i + 1))
    (view : PFunctor.FreeM.Path.ForkView i main s) :
    acceptContextForkWitness main qb i cf s view = some ⟨s, view⟩ ↔
      view.firstAnswer ≠ view.secondAnswer ∧
        cf (PFunctor.FreeM.output main view.firstPath) = some s ∧
        cf (PFunctor.FreeM.output main view.secondPath) = some s := by
  simp [acceptContextForkWitness]

/-- Canonical rich forking experiment.  Probability statements may project
its output pair, while Fiat--Shamir reductions can consume the typed
occurrence and the two completions directly. -/
def contextForkWitness
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) :
    OracleComp spec (Option (ContextForkWitness main qb i)) :=
  PFunctor.FreeM.Path.filterMapReforkBy (P := spec.toPFunctor)
    i main cf (fun s => (s : Nat)) (acceptContextForkWitness main qb i cf)

omit [spec.DecidableEq] in
@[simp] theorem contextForkWitness_outputs
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (witness : ContextForkWitness main qb i) :
    (PFunctor.FreeM.Path.SelectedForkView.outputs witness) =
      (PFunctor.FreeM.output main witness.view.firstPath,
        PFunctor.FreeM.output main witness.view.secondPath) := by
  rfl

/-- Canonical dynamically selected fork. The first execution chooses an
ordinal through `cf`; PolyFun locates that occurrence and independently
completes the same typed context a second time. -/
def contextFork
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) :
    OracleComp spec (Option (α × α)) :=
  PFunctor.FreeM.Path.filterMapReforkBy (P := spec.toPFunctor)
    i main cf (fun s => (s : Nat)) (classifyForkView main qb i cf)


omit [spec.DecidableEq] in
private theorem mem_support_freeM_bind_iff
    {β γ : Type} (mx : OracleComp spec β) (next : β → OracleComp spec γ)
    (y : γ) :
    y ∈ support (OracleComp.ofFreeM (PFunctor.FreeM.bind mx next)) ↔
      ∃ x ∈ support mx, y ∈ support (next x) := by
  change y ∈ support (mx >>= next) ↔
    ∃ x ∈ support mx, y ∈ support (next x)
  exact mem_support_bind_iff mx next y

omit [spec.DecidableEq] in
private theorem mem_support_freeM_map_iff
    {β γ : Type} (mx : spec.toPFunctor.FreeM β) (f : β → γ) (y : γ) :
    y ∈ support (OracleComp.ofFreeM (PFunctor.FreeM.map f mx)) ↔
      ∃ x ∈ support (OracleComp.ofFreeM mx), f x = y := by
  rw [OracleComp.ofFreeM_map]
  rw [support_map, Set.mem_image]

omit [spec.DecidableEq] in
private theorem mem_support_freeM_pure_iff {β : Type} (x y : β) :
    y ∈ support (OracleComp.ofFreeM
      (pure x : spec.toPFunctor.FreeM β)) ↔ y = x := by
  change y ∈ support (pure x : OracleComp spec β) ↔ y = x
  simp


/-- Successful contextual forks expose the selected path, its certified
occurrence, and the independently sampled second completion. -/
theorem contextFork_success
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) {x₁ x₂ : α}
    (h : some (x₁, x₂) ∈ support (contextFork main qb i cf)) :
    ∃ (path : PFunctor.FreeM.Path main) (s : Fin (qb i + 1))
      (located : PFunctor.FreeM.Path.Located i main path s)
      (second : located.occurrence.Completion),
      path ∈ (_root_.support (show OracleComp spec _ from
        PFunctor.FreeM.withPath main)) ∧
      cf (PFunctor.FreeM.output main path) = some s ∧
      second ∈ (_root_.support (show OracleComp spec _ from
        located.occurrence.complete)) ∧
      located.completion.answer ≠ second.answer ∧
      cf (PFunctor.FreeM.output main second.path) = some s ∧
      x₁ = PFunctor.FreeM.output main path ∧
      x₂ = PFunctor.FreeM.output main second.path := by
  rw [contextFork,
    PFunctor.FreeM.Path.filterMapReforkBy_eq_bind_complete] at h
  rw [mem_support_freeM_bind_iff] at h
  obtain ⟨path, hpath, h⟩ := h
  rcases hcf : cf (PFunctor.FreeM.output main path) with _ | s
  · rw [hcf] at h
    rw [mem_support_freeM_pure_iff] at h
    simp at h
  · simp only [hcf] at h
    rcases hlocated : PFunctor.FreeM.Path.locateAt?
        (P := spec.toPFunctor) i main path s with _ | located
    · rw [hlocated] at h
      rw [mem_support_freeM_pure_iff] at h
      simp at h
    · simp only [hlocated] at h
      rw [mem_support_freeM_map_iff] at h
      obtain ⟨second, hsecond, hresult⟩ := h
      change classifyForkView main qb i cf s {
          occurrence := located.occurrence
          first := located.completion
          second := second } = some (x₁, x₂) at hresult
      rcases (classifyForkView_eq_some_iff main qb i cf s _ x₁ x₂).mp hresult with
        ⟨hne, _, hcf₂, hx₁, hx₂⟩
      exact ⟨path, s, located, second, hpath, hcf, hsecond, hne,
        by simpa only [PFunctor.FreeM.Path.ForkView.secondPath] using hcf₂,
        (by
          calc
            x₁ = PFunctor.FreeM.output main located.completion.path := by
              simpa only [PFunctor.FreeM.Path.ForkView.firstPath] using hx₁
            _ = PFunctor.FreeM.output main path :=
              congrArg (PFunctor.FreeM.output main) located.path_eq),
        by simpa only [PFunctor.FreeM.Path.ForkView.secondPath] using hx₂⟩

/-- Transfer first-run log invariants through a successful contextual fork.
The differing selected entries follow directly from the two completions of
the retained occurrence. -/
theorem contextFork_propertyTransfer [IsUniformSpec spec]
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1)))
    (P_out : α → QueryLog spec → Prop)
    (hP : ∀ {x log}, (x, log) ∈ support (replayFirstRun main) → P_out x log)
    {x₁ x₂ : α}
    (h : some (x₁, x₂) ∈ support (contextFork main qb i cf)) :
    ∃ (log₁ log₂ : QueryLog spec) (s : Fin (qb i + 1)),
      cf x₁ = some s ∧ cf x₂ = some s ∧
      P_out x₁ log₁ ∧ P_out x₂ log₂ ∧
      QueryLog.getQueryValue? log₁ i s ≠
        QueryLog.getQueryValue? log₂ i s := by
  obtain ⟨path, s, located, second, hpath, hcf₁, _hsecond,
      hne, hcf₂, hx₁, hx₂⟩ := contextFork_success main qb i cf h
  let log₁ : QueryLog spec := PFunctor.FreeM.Path.trace main path
  let log₂ : QueryLog spec := PFunctor.FreeM.Path.trace main second.path
  have hrun₁ : (x₁, log₁) ∈ support (replayFirstRun main) := by
    have hp := replayPathResult_mem_support_replayFirstRun main path hpath
    simpa [log₁, replayPathResult, hx₁] using hp
  have hrun₂ : (x₂, log₂) ∈ support (replayFirstRun main) := by
    have hp := replayPathResult_mem_support_replayFirstRun main second.path
      (mem_support_replayFirstPath main second.path)
    simpa [log₂, replayPathResult, hx₂] using hp
  have hlookup₁ : QueryLog.getQueryValue? log₁ i s =
      some located.completion.answer := by
    subst log₁
    have htrace := congrArg
      (fun path : PFunctor.FreeM.Path main =>
        (show QueryLog spec from PFunctor.FreeM.Path.trace main path))
      located.path_eq
    change QueryLog.getQueryValue?
      (show QueryLog spec from PFunctor.FreeM.Path.trace main path) i s =
        some located.completion.answer
    rw [← htrace]
    exact getQueryValue?_completion_path_eq_answer
      located.occurrence located.completion
  have hlookup₂ : QueryLog.getQueryValue? log₂ i s = some second.answer := by
    exact getQueryValue?_completion_path_eq_answer located.occurrence second
  refine ⟨log₁, log₂, s, ?_, ?_, hP hrun₁, hP hrun₂, ?_⟩
  · simpa only [hx₁] using hcf₁
  · simpa only [hx₂] using hcf₂
  · rw [hlookup₁, hlookup₂]
    exact fun heq => hne (Option.some.inj heq)

/-- The fixed-index guarded context experiment. It succeeds exactly when both
outputs select `s` and the two focused oracle answers differ. -/
def guardedContextFork
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) (s : Fin (qb i + 1)) :
    OracleComp spec (Option (α × α)) :=
  PFunctor.FreeM.Path.filterMapReforkAt (P := spec.toPFunctor)
    i main s (classifyForkView main qb i cf s)

private def collideForkView
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) (s : Fin (qb i + 1)) :
    Option (PFunctor.FreeM.Path.ForkView i main (s : Nat)) →
      Option (Fin (qb i + 1))
  | none => none
  | some view =>
      if view.firstAnswer = view.secondAnswer ∧
          cf (PFunctor.FreeM.output main view.firstPath) = some s ∧
          cf (PFunctor.FreeM.output main view.secondPath) = some s then
        some s
      else none

@[simp] private theorem collideForkView_eq_some
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) (s : Fin (qb i + 1))
    (view : PFunctor.FreeM.Path.ForkView i main s) :
    collideForkView main qb i cf s (some view) = some s ↔
      view.firstAnswer = view.secondAnswer ∧
        cf (PFunctor.FreeM.output main view.firstPath) = some s ∧
        cf (PFunctor.FreeM.output main view.secondPath) = some s := by
  simp [collideForkView]

private def contextForkViewCollision
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) (s : Fin (qb i + 1)) :
    OracleComp spec (Option (Fin (qb i + 1))) :=
  PFunctor.FreeM.map (collideForkView main qb i cf s) (contextForkView main i s)

/-- Equal focused answers form the sole collision branch removed by
`guardedContextFork`. -/
noncomputable def contextForkCollision
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) (s : Fin (qb i + 1)) :
    OracleComp spec (Option (Fin (qb i + 1))) := do
  let path ← PFunctor.FreeM.withPath main
  match PFunctor.FreeM.Path.locateAt? (P := spec.toPFunctor) i main path s with
  | none => pure none
  | some located =>
      let secondAnswer ← (liftM (spec.query i) :
        OracleComp spec (spec.Range i))
      if located.completion.answer = secondAnswer ∧
          cf (PFunctor.FreeM.output main path) = some s then
        pure (some s)
      else pure none

/-- The generic certified factorization viewed through the `OracleComp` type
alias. This lemma contains only the boundary casts between the two APIs. -/
private theorem splitAtValid_bind_complete_oracleComp
    (main : OracleComp spec α) (i : ι) (n : Nat) :
    ((show OracleComp spec _ from
        PFunctor.FreeM.Path.splitAtValid (P := spec.toPFunctor) i main n) >>=
      fun certified => (show OracleComp spec (PFunctor.FreeM.Path main) from
        certified.1.complete)) = replayFirstPath main := by
  exact PFunctor.FreeM.Path.splitAtValid_bind_complete i main n

/-- Certified two-completion factorization through the `OracleComp` alias. -/
private theorem splitAtValid_bind_completeFork_oracleComp
    (main : OracleComp spec α) (i : ι) (n : Nat) :
    ((show OracleComp spec _ from
        PFunctor.FreeM.Path.splitAtValid (P := spec.toPFunctor) i main n) >>=
      fun certified => (show OracleComp spec _ from
        certified.1.completeFork)) = contextForkView main i n := by
  unfold contextForkView
  exact (PFunctor.FreeM.Path.splitAtValid_bind_completeFork i main n).trans
    (PFunctor.FreeM.Path.forkAt_eq_reforkAt i main n)

omit [spec.DecidableEq] in
/-- The generic found-fork observation law through the `OracleComp` alias. -/
private theorem map_completeFork_found_oracleComp
    {main : OracleComp spec α} {i : ι} {n : Nat}
    (occurrence : PFunctor.FreeM.Path.Occurrence i main n) {β : Type}
    (observe : PFunctor.FreeM.Path.ForkView i main n → β) :
    Option.map observe <$>
        (show OracleComp spec
            (Option (PFunctor.FreeM.Path.ForkView i main n)) from
          (PFunctor.FreeM.Path.Split.found occurrence :
            PFunctor.FreeM.Path.Split i main n).completeFork) =
      ((show OracleComp spec occurrence.Completion from occurrence.complete) >>= fun first =>
        (fun second => some (observe {
          occurrence := occurrence
          first := first
          second := second })) <$>
            (show OracleComp spec occurrence.Completion from occurrence.complete)) := by
  exact PFunctor.FreeM.Path.Split.map_completeFork_found occurrence observe

omit [spec.DecidableEq] in
/-- Event transport for a raw PolyFun map at the `OracleComp` probability
boundary. Keeping this cast in one lemma lets context proofs stay in
PolyFun normal form. -/
private theorem probEvent_freeM_map [IsProbabilitySpec spec]
    {β γ : Type} (f : β → γ) (mx : spec.toPFunctor.FreeM β)
    (event : γ → Prop) :
    Pr[event | OracleComp.ofFreeM (PFunctor.FreeM.map f mx)] =
      Pr[event ∘ f | OracleComp.ofFreeM mx] := by
  rw [OracleComp.ofFreeM_map]
  exact probEvent_map (OracleComp.ofFreeM mx) f event

omit [spec.DecidableEq] in
/-- Probability of a raw PolyFun return at the `OracleComp` boundary. -/
private theorem probEvent_freeM_pure [IsProbabilitySpec spec]
    {β : Type} (x : β) (event : β → Prop) [DecidablePred event] :
    Pr[event | OracleComp.ofFreeM
      (pure x : spec.toPFunctor.FreeM β)] = if event x then 1 else 0 := by
  change Pr[event | (pure x : OracleComp spec β)] = if event x then 1 else 0
  exact probEvent_pure x event

omit [spec.DecidableEq] in
private theorem probEvent_freeM_bind_eq_tsum [IsProbabilitySpec spec]
    {β γ : Type} (mx : spec.toPFunctor.FreeM β)
    (next : β → spec.toPFunctor.FreeM γ) (event : γ → Prop) :
    Pr[event | OracleComp.ofFreeM (PFunctor.FreeM.bind mx next)] =
      ∑' x, Pr[= x | OracleComp.ofFreeM mx] *
        Pr[event | OracleComp.ofFreeM (next x)] := by
  rw [OracleComp.ofFreeM_bind]
  exact probEvent_bind_eq_tsum (OracleComp.ofFreeM mx)
    (fun x => OracleComp.ofFreeM (next x)) event

private theorem probEvent_classifyForkView_isSome_eq_zero_of_first_ne
    [IsProbabilitySpec spec]
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) (s : Fin (qb i + 1))
    {path : PFunctor.FreeM.Path main}
    (located : PFunctor.FreeM.Path.Located i main path s)
    (hfirst : cf (PFunctor.FreeM.output main located.completion.path) ≠ some s) :
    Pr[fun result : Option (α × α) => result.isSome |
      OracleComp.ofFreeM (PFunctor.FreeM.map
        (fun second => classifyForkView main qb i cf s {
          occurrence := located.occurrence
          first := located.completion
          second := second }) located.occurrence.complete)] = 0 := by
  rw [probEvent_freeM_map]
  rw [show ((fun result : Option (α × α) => result.isSome = true) ∘
      fun second => classifyForkView main qb i cf s {
        occurrence := located.occurrence
        first := located.completion
        second := second }) = fun _ => False by
    funext second
    apply propext
    simp only [Function.comp_apply, iff_false]
    intro hisSome
    exact hfirst (by
      simpa only [PFunctor.FreeM.Path.ForkView.firstPath] using
        (classifyForkView_isSome main qb i cf s _).mp hisSome |>.2.1),
    probEvent_False]

private theorem probEvent_classifyForkView_component_ne_eq_zero
    [IsProbabilitySpec spec]
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) (t s : Fin (qb i + 1))
    {path : PFunctor.FreeM.Path main}
    (located : PFunctor.FreeM.Path.Located i main path t) (hne : t ≠ s) :
    Pr[fun result : Option (α × α) =>
        result.map (cf ∘ Prod.fst) = some (some s) |
      OracleComp.ofFreeM (PFunctor.FreeM.map
        (fun second => classifyForkView main qb i cf t {
          occurrence := located.occurrence
          first := located.completion
          second := second }) located.occurrence.complete)] = 0 := by
  rw [probEvent_freeM_map]
  rw [show ((fun result : Option (α × α) =>
      result.map (cf ∘ Prod.fst) = some (some s)) ∘
      fun second => classifyForkView main qb i cf t {
        occurrence := located.occurrence
        first := located.completion
        second := second }) = fun _ => False by
    funext second
    apply propext
    simpa only [Function.comp_apply, iff_false] using
      classifyForkView_component_ne main qb i cf t s {
        occurrence := located.occurrence
        first := located.completion
        second := second } hne,
    probEvent_False]


noncomputable def contextForkPair
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) (s : Fin (qb i + 1)) :
    OracleComp spec (Option (Option (Fin (qb i + 1)) × Option (Fin (qb i + 1)))) :=
  Option.map (fun view =>
    (cf (PFunctor.FreeM.output main view.firstPath),
      cf (PFunctor.FreeM.output main view.secondPath))) <$>
        contextForkView main i s

/-- A valid missing split cannot select its nominal occurrence. This is the
structural step that removes the missing branch from the certified pair game. -/
theorem not_cf_eq_of_valid_missing
    {main : OracleComp spec α} {qb : ι → ℕ} {i : ι}
    {cf : α → Option (Fin (qb i + 1))}
    (hreach : PathCfReachable main qb i cf) (s : Fin (qb i + 1))
    (path : PFunctor.FreeM.Path main)
    (hvalid : (PFunctor.FreeM.Path.Split.missing path :
      PFunctor.FreeM.Path.Split i main (s : Nat)).Valid) :
    cf (PFunctor.FreeM.output main path) ≠ some s := by
  intro hcf
  have hsome := hreach path s hcf
  rw [PFunctor.FreeM.Path.locateAt?_isSome_iff_lt_occurrences] at hsome
  exact (Nat.not_lt_of_ge hvalid) hsome

/- Fixed-index success squares under two independent completions of the
PolyFun occurrence context. This is the analytic core of replay forking and
does not use query logs, replay cursors, or a bespoke oracle interpreter. -/
theorem sq_probOutput_main_le_contextForkPair [IsUniformSpec spec]
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1)))
    (hreach : PathCfReachable main qb i cf) (s : Fin (qb i + 1)) :
    Pr[= s | cf <$> main] ^ 2 ≤
      Pr[= (some (some s, some s) : Option
            (Option (Fin (qb i + 1)) × Option (Fin (qb i + 1)))) |
          contextForkPair main qb i cf s] := by
  let domainDecEq : DecidableEq spec.Domain := inferInstance
  let rangeDecEq : ∀ j, DecidableEq (spec.Range j) := fun _ => inferInstance
  classical
  letI : DecidableEq spec.Domain := domainDecEq
  letI (j : spec.Domain) : DecidableEq (spec.Range j) := rangeDecEq j
  set y : Option (Fin (qb i + 1)) := some s
  let splitComp : OracleComp spec
      {split : PFunctor.FreeM.Path.Split i main (s : Nat) // split.Valid} :=
    PFunctor.FreeM.Path.splitAtValid (P := spec.toPFunctor) i main (s : Nat)
  let finish : PFunctor.FreeM.Path main → OracleComp spec (Option (Fin (qb i + 1))) :=
    fun path => pure (cf (PFunctor.FreeM.output main path))
  let Q : {split : PFunctor.FreeM.Path.Split i main (s : Nat) // split.Valid} →
      ℝ≥0∞ := fun certified =>
    Pr[= y | (show OracleComp spec (PFunctor.FreeM.Path main) from
      certified.1.complete) >>= finish]
  let w : {split : PFunctor.FreeM.Path.Split i main (s : Nat) // split.Valid} →
      ℝ≥0∞ := fun certified =>
    Pr[= certified | (splitComp : OracleComp spec _)]
  have hprogram : (cf <$> main : OracleComp spec (Option (Fin (qb i + 1)))) =
      splitComp >>= fun certified =>
        (show OracleComp spec (PFunctor.FreeM.Path main) from
          certified.1.complete) >>= finish := by
    simp only [splitComp]
    rw [← bind_assoc, splitAtValid_bind_complete_oracleComp]
    calc
      cf <$> main = cf <$> (PFunctor.FreeM.output main <$> replayFirstPath main) := by
        rw [map_output_replayFirstPath]
      _ = (cf ∘ PFunctor.FreeM.output main) <$> replayFirstPath main := by
        simp only [Functor.map_map, Function.comp_def]
      _ = replayFirstPath main >>= finish := by
        simp [finish, Function.comp_def]
  have hMain : (Pr[= y | cf <$> main] : ℝ≥0∞) = ∑' split, w split * Q split := by
    rw [hprogram, probOutput_bind_eq_tsum]
  have hw : ∑' split, w split ≤ 1 := tsum_probOutput_le_one
  have hJensen : (∑' split, w split * Q split) ^ 2 ≤
      ∑' split, w split * Q split ^ 2 :=
    ENNReal.sq_tsum_le_tsum_sq w Q hw
  have hFactor :
      Pr[= (some (y, y) : Option
            (Option (Fin (qb i + 1)) × Option (Fin (qb i + 1)))) |
          contextForkPair main qb i cf s] =
        ∑' split, w split * Q split ^ 2 := by
    let observeView : PFunctor.FreeM.Path.ForkView i main (s : Nat) →
        Option (Fin (qb i + 1)) × Option (Fin (qb i + 1)) := fun view =>
      (cf (PFunctor.FreeM.output main view.firstPath),
        cf (PFunctor.FreeM.output main view.secondPath))
    have hpair : contextForkPair main qb i cf s =
        splitComp >>= fun certified =>
          Option.map observeView <$>
            (show OracleComp spec _ from certified.1.completeFork) := by
      calc
        contextForkPair main qb i cf s =
            Option.map observeView <$> contextForkView main i s := rfl
        _ = Option.map observeView <$> (splitComp >>= fun certified =>
              (show OracleComp spec _ from certified.1.completeFork)) := by
            simp only [splitComp]
            rw [splitAtValid_bind_completeFork_oracleComp]
        _ = _ := by rw [map_bind]
    rw [hpair, probOutput_bind_eq_tsum]
    simp only [w, splitComp]
    refine tsum_congr fun split =>
      congrArg (fun z => Pr[= split |
        (show OracleComp spec _ from
          PFunctor.FreeM.Path.splitAtValid (P := spec.toPFunctor)
            i main (s : Nat))] * z) ?_
    rcases split with ⟨split, hvalid⟩
    cases split with
    | missing path =>
        have hcf := not_cf_eq_of_valid_missing hreach s path hvalid
        have hQ : Q ⟨.missing path, hvalid⟩ = 0 := by
          change Pr[= y | (pure (cf (PFunctor.FreeM.output main path)) :
            OracleComp spec _)] = 0
          simp [y, Ne.symm hcf]
        change Pr[= some (y, y) |
            (Option.map observeView <$> (pure none : OracleComp spec _))] =
          Q ⟨.missing path, hvalid⟩ ^ 2
        simp [hQ]
    | found occurrence =>
        let completion : OracleComp spec occurrence.Completion :=
          (show OracleComp spec occurrence.Completion from occurrence.complete)
        let observe : occurrence.Completion → Option (Fin (qb i + 1)) :=
          fun completed => cf (PFunctor.FreeM.output main completed.path)
        have hcomp : (do
            let first ← completion
            let second ← completion
            pure (some (observe first, observe second)) :
              OracleComp spec (Option
                (Option (Fin (qb i + 1)) × Option (Fin (qb i + 1))))) =
            some <$> (do
              let a ← observe <$> completion
              let b ← observe <$> completion
              pure (a, b) : OracleComp spec _) := by
          simp [completion, observe, monad_norm]
        change Pr[= some (y, y) | Option.map observeView <$>
            (show OracleComp spec
                (Option (PFunctor.FreeM.Path.ForkView i main (s : Nat))) from
              (PFunctor.FreeM.Path.Split.found occurrence :
                PFunctor.FreeM.Path.Split i main (s : Nat)).completeFork)] = _
        rw [map_completeFork_found_oracleComp]
        change Pr[= some (y, y) | (completion >>= fun first =>
            (fun second => some (observe first, observe second)) <$> completion)] = _
        rw [show (completion >>= fun first =>
              (fun second => some (observe first, observe second)) <$> completion) =
            (do
              let first ← completion
              let second ← completion
              pure (some (observe first, observe second)) : OracleComp spec _) by
            apply congrArg (fun k => completion >>= k)
            funext first
            rw [bind_pure_comp]]
        rw [hcomp, probOutput_some_map_some,
          probOutput_bind_bind_prod_mk_eq_mul']
        have hQeq : Pr[= y | observe <$> completion] =
            Q ⟨.found occurrence, hvalid⟩ := by
          have hprogramQ : (observe <$> completion : OracleComp spec _) =
              (cf ∘ PFunctor.FreeM.output main) <$>
                (show OracleComp spec _ from occurrence.completePath) := by
            change PFunctor.FreeM.map observe occurrence.complete =
              PFunctor.FreeM.map (cf ∘ PFunctor.FreeM.output main)
                (PFunctor.FreeM.map
                  PFunctor.FreeM.Path.Occurrence.Completion.path occurrence.complete)
            rw [← PFunctor.FreeM.comp_map]
            rfl
          rw [hprogramQ]
          change Pr[= y | (cf ∘ PFunctor.FreeM.output main) <$>
              (show OracleComp spec _ from occurrence.completePath)] =
            Pr[= y | (show OracleComp spec _ from occurrence.completePath) >>= finish]
          rw [show ((show OracleComp spec _ from occurrence.completePath) >>= finish) =
              (cf ∘ PFunctor.FreeM.output main) <$>
                (show OracleComp spec _ from occurrence.completePath) by
            rw [show finish = pure ∘ (cf ∘ PFunctor.FreeM.output main) by
              funext path
              rfl]
            exact bind_pure_comp _ _]
        simpa [sq] using congrArg (fun z : ℝ≥0∞ => z * z) hQeq
  rw [hMain]
  exact hJensen.trans_eq hFactor.symm

/-- Fixed-index pair success partitions into a genuine guarded fork or an
equal-answer collision, all as observations of the same `ForkView`. -/
theorem probOutput_contextForkPair_le_guarded_add_collision [IsUniformSpec spec]
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) (s : Fin (qb i + 1)) :
    Pr[= (some (some s, some s) : Option
          (Option (Fin (qb i + 1)) × Option (Fin (qb i + 1)))) |
        contextForkPair main qb i cf s] ≤
      Pr[fun result : Option (α × α) => result.isSome |
        guardedContextFork main qb i cf s] +
      Pr[= (some s : Option (Fin (qb i + 1))) |
        contextForkViewCollision main qb i cf s] := by
  classical
  let source := contextForkView main i s
  let pairGood : Option (PFunctor.FreeM.Path.ForkView i main (s : Nat)) → Prop
    | none => False
    | some view =>
        cf (PFunctor.FreeM.output main view.firstPath) = some s ∧
        cf (PFunctor.FreeM.output main view.secondPath) = some s
  let guardGood : Option (PFunctor.FreeM.Path.ForkView i main (s : Nat)) → Prop :=
    fun view? => (view?.bind (classifyForkView main qb i cf s)).isSome
  let collisionGood : Option (PFunctor.FreeM.Path.ForkView i main (s : Nat)) → Prop :=
    fun view? => collideForkView main qb i cf s view? = some s
  have hpoint : ∀ view?, pairGood view? → guardGood view? ∨ collisionGood view? := by
    intro view? hgood
    rcases view? with _ | view
    · simp [pairGood] at hgood
    · rcases hgood with ⟨hfirst, hsecond⟩
      by_cases heq : view.firstAnswer = view.secondAnswer
      · right
        simp [collisionGood, collideForkView, heq, hfirst, hsecond]
      · left
        simp [guardGood, classifyForkView, heq, hfirst, hsecond]
  have hpair :
      Pr[= (some (some s, some s) : Option
            (Option (Fin (qb i + 1)) × Option (Fin (qb i + 1)))) |
          contextForkPair main qb i cf s] = Pr[pairGood | source] := by
    rw [← probEvent_eq_eq_probOutput, contextForkPair, probEvent_map]
    congr 1
    funext view?
    apply propext
    rcases view? with _ | view <;> simp [pairGood]
  have hguard : Pr[guardGood | source] =
      Pr[fun result : Option (α × α) => result.isSome |
        guardedContextFork main qb i cf s] := by
    unfold guardedContextFork PFunctor.FreeM.Path.filterMapReforkAt
    rw [probEvent_freeM_map]
    unfold source contextForkView guardGood
    rfl
  have hcollision : Pr[collisionGood | source] =
      Pr[= (some s : Option (Fin (qb i + 1))) |
        contextForkViewCollision main qb i cf s] := by
    rw [← probEvent_eq_eq_probOutput, contextForkViewCollision]
    change Pr[collisionGood | source] =
      Pr[fun x => x = some s | collideForkView main qb i cf s <$> source]
    rw [probEvent_map]
    rfl
  rw [hpair]
  calc
    Pr[pairGood | source] ≤ Pr[fun view? => guardGood view? ∨ collisionGood view? |
        source] := probEvent_mono (mx := source) fun view? _ hgood => hpoint view? hgood
    _ ≤ Pr[guardGood | source] + Pr[collisionGood | source] :=
      probEvent_or_le source guardGood collisionGood
    _ = _ := by rw [hguard, hcollision]

/-- A fresh focused answer collides with the first completion's answer with
probability at most the inverse answer-space cardinality. -/
theorem probOutput_contextForkCollision_le_main_div [IsUniformSpec spec]
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) (s : Fin (qb i + 1)) :
    Pr[= (some s : Option (Fin (qb i + 1))) |
        contextForkCollision main qb i cf s] ≤
      Pr[= (some s : Option (Fin (qb i + 1))) | cf <$> main] /
        Fintype.card (spec.Range i) := by
  let paths : OracleComp spec (PFunctor.FreeM.Path main) :=
    PFunctor.FreeM.withPath main
  let good : PFunctor.FreeM.Path main → ℝ≥0∞ := fun path =>
    if cf (PFunctor.FreeM.output main path) = some s then 1 else 0
  let hcard : ℝ≥0∞ := Fintype.card (spec.Range i)
  let collision : PFunctor.FreeM.Path main →
      OracleComp spec (Option (Fin (qb i + 1))) := fun path =>
    match PFunctor.FreeM.Path.locateAt? (P := spec.toPFunctor)
        i main path s with
    | none => pure none
    | some located => do
        let secondAnswer ← (liftM (spec.query i) :
          OracleComp spec (spec.Range i))
        if located.completion.answer = secondAnswer ∧
            cf (PFunctor.FreeM.output main path) = some s then
          pure (some s)
        else pure none
  let domainDecEq : DecidableEq spec.Domain := inferInstance
  classical
  letI : DecidableEq spec.Domain := domainDecEq
  have hinner : ∀ path : PFunctor.FreeM.Path main,
      Pr[= (some s : Option (Fin (qb i + 1))) | collision path] ≤
        good path * hcard⁻¹ := by
    intro path
    simp only [collision]
    rcases hlocated : PFunctor.FreeM.Path.locateAt?
        (P := spec.toPFunctor) i main path s with _ | located
    · simp [good]
    · by_cases hcf : cf (PFunctor.FreeM.output main path) = some s
      · rw [probOutput_bind_eq_tsum]
        simp [hcf, good, hcard, probOutput_query]
      · simp [hcf, good]
  calc
    Pr[= (some s : Option (Fin (qb i + 1))) |
        contextForkCollision main qb i cf s]
        = ∑' path, Pr[= path | paths] *
            Pr[= (some s : Option (Fin (qb i + 1))) | collision path] := by
            simp only [contextForkCollision, paths, collision]
            rw [probOutput_bind_eq_tsum]
    _ ≤ ∑' path, Pr[= path | paths] * (good path * hcard⁻¹) := by
          exact ENNReal.tsum_le_tsum fun path => mul_le_mul' le_rfl (hinner path)
    _ = (∑' path, Pr[= path | paths] * good path) * hcard⁻¹ := by
          rw [← ENNReal.tsum_mul_right]
          exact tsum_congr fun path => by ring
    _ = Pr[= (some s : Option (Fin (qb i + 1))) | cf <$> main] * hcard⁻¹ := by
          congr 1
          rw [show (cf <$> main : OracleComp spec _) =
              (cf ∘ PFunctor.FreeM.output main) <$> paths by
            calc
              cf <$> main = cf <$> (PFunctor.FreeM.output main <$>
                  replayFirstPath main) := by rw [map_output_replayFirstPath]
              _ = (cf ∘ PFunctor.FreeM.output main) <$>
                  replayFirstPath main := by
                    simp only [Functor.map_map, Function.comp_def]
              _ = _ := rfl]
          rw [probOutput_map_eq_tsum]
          exact tsum_congr fun path => by
            by_cases hcf : cf (PFunctor.FreeM.output main path) = some s
            · simp [good, hcf]
            · have hcf' : some s ≠ cf (PFunctor.FreeM.output main path) :=
                Ne.symm hcf
              simp [good, hcf, hcf']
    _ = Pr[= (some s : Option (Fin (qb i + 1))) | cf <$> main] /
          Fintype.card (spec.Range i) := by
          simp [hcard, div_eq_mul_inv]

/-- Requiring the colliding second completion to finish successfully can only
decrease the path-first equal-answer collision probability. -/
theorem probOutput_contextForkViewCollision_le_collision [IsUniformSpec spec]
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) (s : Fin (qb i + 1)) :
    Pr[= (some s : Option (Fin (qb i + 1))) |
        contextForkViewCollision main qb i cf s] ≤
      Pr[= (some s : Option (Fin (qb i + 1))) |
        contextForkCollision main qb i cf s] := by
  let paths : OracleComp spec (PFunctor.FreeM.Path main) :=
    PFunctor.FreeM.withPath main
  let viewCollision : PFunctor.FreeM.Path main →
      OracleComp spec (Option (Fin (qb i + 1))) := fun path =>
    match PFunctor.FreeM.Path.locateAt? (P := spec.toPFunctor) i main path s with
    | none => pure none
    | some located =>
        PFunctor.FreeM.bind
          (PFunctor.FreeM.lift (P := spec.toPFunctor) i) fun secondAnswer =>
            (fun secondSuffix =>
              collideForkView main qb i cf s (some {
                occurrence := located.occurrence
                first := located.completion
                second := ⟨secondAnswer, secondSuffix⟩ })) <$>
              PFunctor.FreeM.withPath (located.occurrence.resume secondAnswer)
  let answerCollision : PFunctor.FreeM.Path main →
      OracleComp spec (Option (Fin (qb i + 1))) := fun path =>
    match PFunctor.FreeM.Path.locateAt? (P := spec.toPFunctor) i main path s with
    | none => pure none
    | some located => do
        let secondAnswer ← (liftM (spec.query i) : OracleComp spec (spec.Range i))
        if located.completion.answer = secondAnswer ∧
            cf (PFunctor.FreeM.output main path) = some s then
          pure (some s)
        else pure none
  have hsource : contextForkViewCollision main qb i cf s =
      paths >>= viewCollision := by
    letI : spec.toPFunctor.DecidableEq :=
      (inferInstance : spec.DecidableEq).toDecidableEq
    unfold contextForkViewCollision contextForkView
    rw [PFunctor.FreeM.Path.map_reforkAt]
    apply congrArg (fun k => paths >>= k)
    funext path
    simp only [viewCollision]
    rcases PFunctor.FreeM.Path.locateAt?
        (P := spec.toPFunctor) i main path s with _ | located
    · rfl
    · simp [PFunctor.FreeM.Path.Located.refork]
  have hlift : (PFunctor.FreeM.lift (P := spec.toPFunctor) i :
      OracleComp spec (spec.Range i)) = OracleComp.lift (spec.query i) := rfl
  have hinner : ∀ path : PFunctor.FreeM.Path main,
      Pr[= (some s : Option (Fin (qb i + 1))) | viewCollision path] ≤
        Pr[= (some s : Option (Fin (qb i + 1))) | answerCollision path] := by
    intro path
    simp only [viewCollision, answerCollision]
    rcases hlocated : PFunctor.FreeM.Path.locateAt?
        (P := spec.toPFunctor) i main path s with _ | located
    · simp
    · rw [hlift]
      let continuation : spec.Range i →
          OracleComp spec (Option (Fin (qb i + 1))) := fun secondAnswer =>
        (fun secondSuffix =>
          collideForkView main qb i cf s (some {
            occurrence := located.occurrence
            first := located.completion
            second := ⟨secondAnswer, secondSuffix⟩ })) <$>
          PFunctor.FreeM.withPath (located.occurrence.resume secondAnswer)
      change Pr[= (some s : Option (Fin (qb i + 1))) |
          OracleComp.lift (spec.query i) >>= continuation] ≤ _
      rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
      refine ENNReal.tsum_le_tsum fun secondAnswer => ?_
      let firstAnswer : spec.Range i := located.completion.answer
      by_cases heq : firstAnswer = secondAnswer
      · by_cases hcf : cf (PFunctor.FreeM.output main path) = some s
        · have hfirst : cf (PFunctor.FreeM.output main located.completion.path) =
              some s := by rw [located.path_eq]; exact hcf
          simp [continuation, firstAnswer, heq, hcf, collideForkView,
            probOutput_query]
        · have hfirst : cf (PFunctor.FreeM.output main located.completion.path) ≠
              some s := by rw [located.path_eq]; exact hcf
          have hcond : ¬(located.completion.answer = secondAnswer ∧
              cf (PFunctor.FreeM.output main path) = some s) :=
            fun h => hcf h.2
          rw [if_neg hcond]
          simp only [probOutput_pure, reduceCtorEq, if_false, mul_zero]
          rw [nonpos_iff_eq_zero]
          apply mul_eq_zero_of_right
          rw [probOutput_eq_zero_iff']
          intro hmem
          rw [mem_finSupport_iff_mem_support, support_map] at hmem
          rcases hmem with ⟨suffix, hsuffix, hsuccess⟩
          exact hfirst (by
            simpa only [PFunctor.FreeM.Path.ForkView.firstPath] using
              (collideForkView_eq_some main qb i cf s _).mp hsuccess |>.2.1)
      · have hcond : ¬(located.completion.answer = secondAnswer ∧
            cf (PFunctor.FreeM.output main path) = some s) :=
          fun h => heq h.1
        rw [if_neg hcond]
        simp only [probOutput_pure, reduceCtorEq, if_false, mul_zero]
        rw [nonpos_iff_eq_zero]
        apply mul_eq_zero_of_right
        rw [probOutput_eq_zero_iff']
        intro hmem
        rw [mem_finSupport_iff_mem_support, support_map] at hmem
        rcases hmem with ⟨suffix, hsuffix, hsuccess⟩
        exact heq (by
          simpa only [PFunctor.FreeM.Path.ForkView.firstAnswer,
            PFunctor.FreeM.Path.ForkView.secondAnswer] using
              (collideForkView_eq_some main qb i cf s _).mp hsuccess |>.1)
  calc
    Pr[= (some s : Option (Fin (qb i + 1))) |
        contextForkViewCollision main qb i cf s]
        = ∑' path, Pr[= path | paths] *
            Pr[= (some s : Option (Fin (qb i + 1))) | viewCollision path] := by
          rw [hsource, probOutput_bind_eq_tsum]
    _ ≤ ∑' path, Pr[= path | paths] *
          Pr[= (some s : Option (Fin (qb i + 1))) | answerCollision path] := by
        exact ENNReal.tsum_le_tsum fun path => mul_le_mul' le_rfl (hinner path)
    _ = Pr[= (some s : Option (Fin (qb i + 1))) |
          contextForkCollision main qb i cf s] := by
        simp only [contextForkCollision, paths, answerCollision]
        rw [probOutput_bind_eq_tsum]

/-- The successful equal-answer branch of the intrinsic context experiment is
bounded by one uniform-answer collision against the original success event. -/
theorem probOutput_contextForkViewCollision_le_main_div [IsUniformSpec spec]
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) (s : Fin (qb i + 1)) :
    Pr[= (some s : Option (Fin (qb i + 1))) |
        contextForkViewCollision main qb i cf s] ≤
      Pr[= (some s : Option (Fin (qb i + 1))) | cf <$> main] /
        Fintype.card (spec.Range i) :=
  (probOutput_contextForkViewCollision_le_collision main qb i cf s).trans
    (probOutput_contextForkCollision_le_main_div main qb i cf s)

/-- Fixed-occurrence forking succeeds with the usual square-minus-collision
lower bound, stated directly for the guarded PolyFun context experiment. -/
theorem sq_sub_div_le_probEvent_guardedContextFork [IsUniformSpec spec]
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1)))
    (hreach : PathCfReachable main qb i cf) (s : Fin (qb i + 1)) :
    let h : ℝ≥0∞ := ↑(Fintype.card (spec.Range i))
    Pr[= s | cf <$> main] ^ 2 - Pr[= s | cf <$> main] / h ≤
      Pr[fun result : Option (α × α) => result.isSome |
        guardedContextFork main qb i cf s] := by
  set h : ℝ≥0∞ := ↑(Fintype.card (spec.Range i))
  apply (tsub_le_iff_right).2
  have hsquare := sq_probOutput_main_le_contextForkPair
    main qb i cf hreach s
  have hpartition := probOutput_contextForkPair_le_guarded_add_collision
    main qb i cf s
  have hcollision := probOutput_contextForkViewCollision_le_main_div
    main qb i cf s
  have hsum :
      Pr[fun result : Option (α × α) => result.isSome |
          guardedContextFork main qb i cf s] +
          Pr[= (some s : Option (Fin (qb i + 1))) |
            contextForkViewCollision main qb i cf s] ≤
        Pr[fun result : Option (α × α) => result.isSome |
          guardedContextFork main qb i cf s] +
          Pr[= (some s : Option (Fin (qb i + 1))) | cf <$> main] / h := by
    exact add_le_add_right (by simpa [h] using hcollision) _
  exact hsquare.trans (hpartition.trans hsum)

/-- Finite aggregation of the fixed-occurrence bounds.  This is the
probability-facing interface consumed by the dynamic context fork. -/
theorem sum_sq_sub_div_le_probEvent_guardedContextFork
    [IsUniformSpec spec]
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1)))
    (hreach : PathCfReachable main qb i cf) :
    let h : ℝ≥0∞ := ↑(Fintype.card (spec.Range i))
    ∑ s : Fin (qb i + 1),
        (Pr[= s | cf <$> main] ^ 2 - Pr[= s | cf <$> main] / h) ≤
      ∑ s : Fin (qb i + 1),
        Pr[fun result : Option (α × α) => result.isSome |
          guardedContextFork main qb i cf s] := by
  classical
  dsimp
  refine Finset.sum_le_sum (fun s _ => ?_)
  exact sq_sub_div_le_probEvent_guardedContextFork main qb i cf hreach s

/-- A fixed guarded fork is the corresponding component of the dynamic
semantic fork. -/
theorem probEvent_guardedContextFork_eq_contextFork_component
    [IsProbabilitySpec spec]
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) (s : Fin (qb i + 1)) :
    Pr[fun result : Option (α × α) => result.isSome |
        guardedContextFork main qb i cf s] =
      Pr[fun result : Option (α × α) =>
          result.map (cf ∘ Prod.fst) = some (some s) |
        contextFork main qb i cf] := by
  letI : spec.toPFunctor.DecidableEq :=
    (inferInstance : spec.DecidableEq).toDecidableEq
  change Pr[fun result : Option (α × α) => result.isSome |
      OracleComp.ofFreeM (PFunctor.FreeM.Path.filterMapReforkAt
        (P := spec.toPFunctor) i main s (classifyForkView main qb i cf s))] =
    Pr[fun result : Option (α × α) =>
        result.map (cf ∘ Prod.fst) = some (some s) |
      OracleComp.ofFreeM (PFunctor.FreeM.Path.filterMapReforkBy
        (P := spec.toPFunctor) i main cf (fun t => (t : Nat))
          (classifyForkView main qb i cf))]
  rw [PFunctor.FreeM.Path.filterMapReforkAt_eq_bind_complete,
    PFunctor.FreeM.Path.filterMapReforkBy_eq_bind_complete,
    probEvent_freeM_bind_eq_tsum, probEvent_freeM_bind_eq_tsum]
  apply tsum_congr
  intro path
  congr 1
  rcases hcf : cf (PFunctor.FreeM.output main path) with _ | t
  · rcases hloc : PFunctor.FreeM.Path.locateAt?
        (P := spec.toPFunctor) i main path s with _ | located
    · rw [probEvent_freeM_pure, probEvent_freeM_pure]
      simp
    · have hfirst :
          cf (PFunctor.FreeM.output main located.completion.path) = none := by
        rw [located.path_eq]
        exact hcf
      rw [probEvent_classifyForkView_isSome_eq_zero_of_first_ne
          main qb i cf s located (by simp [hfirst]),
        probEvent_freeM_pure]
      simp
  · by_cases hts : t = s
    · subst t
      rcases hloc : PFunctor.FreeM.Path.locateAt?
          (P := spec.toPFunctor) i main path s with _ | located
      · simp only [hloc]
        rw [probEvent_freeM_pure, probEvent_freeM_pure]
        simp
      · simp only [hloc]
        rw [probEvent_freeM_map, probEvent_freeM_map]
        congr 1
        funext second
        apply propext
        change (classifyForkView main qb i cf s {
            occurrence := located.occurrence
            first := located.completion
            second := second }).isSome = true ↔
          (classifyForkView main qb i cf s {
            occurrence := located.occurrence
            first := located.completion
            second := second }).map (cf ∘ Prod.fst) = some (some s)
        simpa using
          (classifyForkView_component_iff main qb i cf s {
            occurrence := located.occurrence
            first := located.completion
            second := second }).symm
    · rcases hlocFixed : PFunctor.FreeM.Path.locateAt?
          (P := spec.toPFunctor) i main path s with _ | locatedFixed
      · rw [probEvent_freeM_pure]
        simp only [Option.isSome_none, Bool.false_eq_true, if_false]
        rcases hlocDynamic : PFunctor.FreeM.Path.locateAt?
            (P := spec.toPFunctor) i main path t with _ | locatedDynamic
        · dsimp only
          rw [probEvent_freeM_pure]
          simp
        · dsimp only
          rw [probEvent_classifyForkView_component_ne_eq_zero
            main qb i cf t s locatedDynamic hts]
      · dsimp only
        have hfirstFixed :
            cf (PFunctor.FreeM.output main locatedFixed.completion.path) =
              some t := by
          rw [locatedFixed.path_eq]
          exact hcf
        have hfirstNe :
            cf (PFunctor.FreeM.output main locatedFixed.completion.path) ≠
              some s := by
          intro heq
          exact hts (Option.some.inj (hfirstFixed.symm.trans heq))
        rw [probEvent_classifyForkView_isSome_eq_zero_of_first_ne
          main qb i cf s locatedFixed hfirstNe]
        rcases hlocDynamic : PFunctor.FreeM.Path.locateAt?
            (P := spec.toPFunctor) i main path t with _ | locatedDynamic
        · dsimp only
          rw [probEvent_freeM_pure]
          simp
        · dsimp only
          rw [probEvent_classifyForkView_component_ne_eq_zero
            main qb i cf t s locatedDynamic hts]
private lemma sum_probEvent_contextFork_component_le_tsum_some
    [IsUniformSpec spec]
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) :
    ∑ s : Fin (qb i + 1),
        Pr[fun r => r.map (cf ∘ Prod.fst) = some (some s) |
          contextFork main qb i cf] ≤
      ∑' (p : α × α), Pr[= some p | contextFork main qb i cf] := by
  classical
  simp_rw [probEvent_eq_tsum_ite]
  have hsplit : ∀ s : Fin (qb i + 1),
      (∑' (r : Option (α × α)),
        if r.map (cf ∘ Prod.fst) = some (some s) then
          Pr[= r | contextFork main qb i cf] else 0) =
        ∑' (p : α × α),
          if cf p.1 = some s then
            Pr[= some p | contextFork main qb i cf] else 0 := by
    intro s
    simpa only [Option.map, comp_apply, reduceCtorEq, ite_false, zero_add,
      Option.some.injEq] using tsum_option (fun r : Option (α × α) =>
        if r.map (cf ∘ Prod.fst) = some (some s) then
          Pr[= r | contextFork main qb i cf] else 0) ENNReal.summable
  simp_rw [hsplit]
  rw [← tsum_fintype (L := .unconditional _), ENNReal.tsum_comm]
  refine ENNReal.tsum_le_tsum fun p => ?_
  rw [tsum_fintype (L := .unconditional _)]
  rcases hcf : cf p.1 with _ | s₀
  · simp
  · rw [Finset.sum_eq_single s₀
      (by intro b _ hb; simp [Ne.symm hb]) (by simp)]
    simp

private lemma tsum_some_eq_probEvent_isSome_contextFork
    [IsUniformSpec spec]
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) :
    ∑' (p : α × α), Pr[= some p | contextFork main qb i cf] =
      Pr[fun r : Option (α × α) => r.isSome |
        contextFork main qb i cf] := by
  classical
  rw [probEvent_eq_tsum_ite]
  simpa only [Option.isSome, Bool.false_eq_true, eq_self,
    ite_false, ite_true, zero_add] using
      (tsum_option (fun r : Option (α × α) =>
        if r.isSome = true then
          Pr[= r | contextFork main qb i cf] else 0) ENNReal.summable).symm

/-- The fixed guarded components form disjoint selector events inside the
dynamic semantic fork. -/
theorem sum_probEvent_guardedContextFork_le_isSome
    [IsUniformSpec spec]
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) :
    ∑ s : Fin (qb i + 1),
        Pr[fun result : Option (α × α) => result.isSome |
          guardedContextFork main qb i cf s] ≤
      Pr[fun result : Option (α × α) => result.isSome |
        contextFork main qb i cf] := by
  classical
  calc
    _ = ∑ s : Fin (qb i + 1),
        Pr[fun result : Option (α × α) =>
            result.map (cf ∘ Prod.fst) = some (some s) |
          contextFork main qb i cf] := by
      apply Finset.sum_congr rfl
      intro s _
      exact probEvent_guardedContextFork_eq_contextFork_component
        main qb i cf s
    _ ≤ ∑' (p : α × α),
        Pr[= some p | contextFork main qb i cf] :=
      sum_probEvent_contextFork_component_le_tsum_some main qb i cf
    _ = _ := tsum_some_eq_probEvent_isSome_contextFork main qb i cf

/-- Direct probability bound for the canonical semantic context fork. The
program manipulation is discharged by PolyFun; this theorem contains only
the finite selector aggregation and the usual Cauchy--Schwarz estimate. -/
theorem le_probEvent_isSome_contextFork [IsUniformSpec spec]
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1)))
    (hreach : PathCfReachable main qb i cf) :
    (let acc : ℝ≥0∞ := ∑ s, Pr[= some s | cf <$> main]
     let h : ℝ≥0∞ := Fintype.card (spec.Range i)
     let q := qb i + 1
     acc * (acc / q - h⁻¹)) ≤
      Pr[fun r : Option (α × α) => r.isSome |
        contextFork main qb i cf] := by
  classical
  simp only
  set ps : Fin (qb i + 1) → ℝ≥0∞ :=
    fun s => Pr[= (some s : Option _) | cf <$> main]
  set acc : ℝ≥0∞ := ∑ s, ps s
  set h : ℝ≥0∞ := ↑(Fintype.card (spec.Range i))
  have hacc_ne_top : acc ≠ ⊤ :=
    ne_top_of_le_ne_top one_ne_top
      (sum_probOutput_some_le_one (mx := cf <$> main)
        (α := Fin (qb i + 1)))
  have halgebra :
      acc * (acc / ↑(qb i + 1) - h⁻¹) ≤
        ∑ s, (ps s ^ 2 - ps s / h) := by
    have hcs := ENNReal.sq_sum_le_card_mul_sum_sq
      (Finset.univ : Finset (Fin (qb i + 1))) ps
    simp only [Finset.card_univ, Fintype.card_fin] at hcs
    calc
      acc * (acc / ↑(qb i + 1) - h⁻¹)
          = acc * (acc / ↑(qb i + 1)) - acc * h⁻¹ :=
            ENNReal.mul_sub (fun _ _ => hacc_ne_top)
      _ = acc ^ 2 / ↑(qb i + 1) - acc / h := by
            rw [div_eq_mul_inv, div_eq_mul_inv, ← mul_assoc, sq,
              div_eq_mul_inv]
      _ ≤ (∑ s, ps s ^ 2) - acc / h := by
            gcongr
            rw [div_eq_mul_inv]
            have hn : ((qb i + 1 : ℕ) : ℝ≥0∞) ≠ 0 := by simp
            calc
              acc ^ 2 * (↑(qb i + 1))⁻¹
                  ≤ (↑(qb i + 1) * ∑ s, ps s ^ 2) *
                      (↑(qb i + 1))⁻¹ := by gcongr
              _ = ∑ s, ps s ^ 2 := by
                  rw [mul_assoc, mul_comm (∑ s, ps s ^ 2) _, ← mul_assoc,
                    ENNReal.mul_inv_cancel hn (by simp), one_mul]
      _ ≤ (∑ s, ps s ^ 2) - ∑ s, ps s / h := by
            gcongr
            simp_rw [div_eq_mul_inv]
            rw [← Finset.sum_mul]
      _ ≤ ∑ s, (ps s ^ 2 - ps s / h) := by
            rw [tsub_le_iff_right]
            calc
              ∑ s, ps s ^ 2
                  ≤ ∑ s, ((ps s ^ 2 - ps s / h) + ps s / h) :=
                    Finset.sum_le_sum fun s _ => le_tsub_add
              _ = ∑ s, (ps s ^ 2 - ps s / h) + ∑ s, ps s / h :=
                    Finset.sum_add_distrib
  refine halgebra.trans ?_
  calc
    ∑ s, (ps s ^ 2 - ps s / h) ≤
        ∑ s, Pr[fun result : Option (α × α) => result.isSome |
          guardedContextFork main qb i cf s] := by
      simpa only [ps, h] using
        sum_sq_sub_div_le_probEvent_guardedContextFork
          main qb i cf hreach
    _ ≤ _ := sum_probEvent_guardedContextFork_le_isSome main qb i cf

end quantitative

end OracleComp
