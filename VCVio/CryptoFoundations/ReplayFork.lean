/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import PolyFun.PFunctor.Free.Cursor.Fork
public import ToMathlib.Data.ENNReal.SumSquares
public import VCVio.OracleComp.Constructions.Fork.Basic
public import VCVio.OracleComp.QueryTracking.LoggingOracle.Core
public import VCVio.OracleComp.QueryTracking.Structures

import VCVio.OracleComp.EvalDist.Measure

/-!
# Replay-Based Forking

This file proves a replay-style forking lemma using PolyFun's typed execution
paths and occurrence contexts. A first path selects an oracle occurrence; the
same context is then completed independently a second time. The shared prefix
and both suffixes are intrinsic in `PFunctor.FreeM.Cursor.ForkView`, leaving the
VCVio layer responsible only for probability and collision estimates.

The accompanying `QueryLog` view is an erasure interface for applications such
as Fiat--Shamir that state postconditions over transcripts.

Dependent path and zipper APIs identify `QueryLog` entries with erased polynomial
trace events, so this file makes `PFunctor.Idx` locally reducible in order for
`simp` and `rw` to match through it. The attribute is scoped to this file because
`PFunctor.Idx` is a Mathlib definition.

## Main definitions

* `replayFirstRun`: the first run of the main computation, instrumented with a query log.
* `replayFirstPath`: the intrinsic execution path taken by that first run.
* `CfReachable` / `PathCfReachable`: reachability of a selected occurrence from an output.
* `contextFork`: two independent completions of the occurrence context chosen by the first path.
* `contextForkWitness`: the fork together with the transcript data witnessing success.
* `guardedContextFork`: `contextFork` restricted to forks whose focused answers differ.
* `contextForkCollision`: the event that both completions return the same focused answer.

## Main results

* `contextForkWitness_success`: a successful witness yields two accepting transcripts.
* `contextFork_success`: the analogous statement for `contextFork`.
* `contextFork_propertyTransfer`: postconditions of the main computation transfer to both branches.
* `sq_prEvent_main_le_contextForkPair`: the squaring step for two independent completions.
* `le_prEvent_isSome_contextFork`: the replay forking bound, stated with `Pr{…}` events of the
  native output measures.

## References

* M. Bellare and G. Neven, *Multi-Signatures in the Plain Public-Key Model and a General
  Forking Lemma*, CCS 2006. The seed-based presentation is mechanized in
  `VCVio.CryptoFoundations.SeededFork`.
-/

@[expose] public section

open OracleSpec OracleComp ENNReal Function Finset

open scoped OracleSpec.PrimitiveQuery
open scoped PFunctor

/- Replay logs and intrinsic paths meet through their list and dependent-pair
presentations; these two reducers are needed only while matching that seam. -/
attribute [local implicit_reducible] FreeMonoid PFunctor.Idx

namespace OracleComp

variable {ι : Type} {spec : OracleSpec ι} {α : Type}

/-- Run `main` with query logging. This is the first-run object for replay forks. -/
@[reducible]
def replayFirstRun (main : OracleComp spec α) : OracleComp spec (α × QueryLog spec) :=
  main.withQueryLog

/-- The first run represented intrinsically: executing `main` returns the
typed root-to-leaf path selected by its oracle answers. -/
def replayFirstPath (main : OracleComp spec α) : OracleComp spec (PFunctor.FreeM.Path main) :=
  PFunctor.FreeM.withPath main

/-- Forget an intrinsic first-run path into the output/transcript pair used by
the probability-facing replay API. -/
def replayPathResult (main : OracleComp spec α) (path : PFunctor.FreeM.Path main) :
    α × QueryLog spec :=
  pathLogResult main path

/-- The intrinsic first-run path of a query-bind: query `t`, then for each answer `u`
prepend that answer to the path taken by the continuation `next u`. -/
@[simp] theorem replayFirstPath_query_bind (t : spec.Domain)
    (next : spec.Range t → OracleComp spec α) :
    replayFirstPath (liftM (query t) >>= next) =
      OracleComp.queryBind t fun u => PFunctor.FreeM.map
          (fun path : PFunctor.FreeM.Path (next u) =>
            (⟨u, path⟩ : PFunctor.FreeM.Path (OracleComp.queryBind t next)))
          (replayFirstPath (next u)) :=
  rfl

/-- Intrinsic path execution and writer-style query logging are the same first
run after erasing the path to its output and trace. This is the bridge that
lets replay proofs use typed paths without changing their probability API. -/
theorem map_replayPathResult_replayFirstPath (main : OracleComp spec α) :
    PFunctor.FreeM.map (replayPathResult main) (replayFirstPath main) = replayFirstRun main :=
  map_pathLogResult_withPath main

/-- A supported intrinsic path erases to a supported legacy first-run result. -/
lemma replayPathResult_mem_support_replayFirstRun
    (main : OracleComp spec α) (path : PFunctor.FreeM.Path main)
    (hpath : path ∈ support (replayFirstPath main)) :
    replayPathResult main path ∈ support (replayFirstRun main) := by
  rw [← map_replayPathResult_replayFirstPath]
  exact (support_map (replayPathResult main) (replayFirstPath main)).symm ▸
    Set.mem_image_of_mem _ hpath

/-- Every well-typed path through an oracle computation is supported. Oracle
queries have universal symbolic support, so a `Path` already contains all the
evidence needed to select its successive branches. -/
lemma mem_support_replayFirstPath (main : OracleComp spec α) (path : PFunctor.FreeM.Path main) :
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
      rw [support_map]
      exact Set.mem_image_of_mem _ (ih answer tail)

/-- Forgetting the path produced by the intrinsic first run recovers the
original oracle computation. -/
@[simp] theorem map_output_replayFirstPath (main : OracleComp spec α) :
    PFunctor.FreeM.output main <$> replayFirstPath main = main :=
  PFunctor.FreeM.map_output_withPath main

/-- The selected entry of an occurrence completion's erased trace is exactly
its focused answer. -/
lemma getQueryValue?_completion_path_eq_answer [DecidableEq ι] {main : OracleComp spec α} {i : ι}
    {n : Nat} (occurrence : PFunctor.FreeM.Cursor.Occurrence i main n)
    (completion : occurrence.Completion) :
    QueryLog.getQueryValue? (PFunctor.FreeM.Path.trace main completion.path) i n =
      some completion.answer := by
  rw [QueryLog.getQueryValue?_eq_getAt?]
  exact occurrence.getAt?_trace_completion_path completion

section quantitative

/-- Reachability hypothesis on the fork-index selector `cf`: whenever the first run
of `main` outputs `x` and the recorded log is `log`, every selected fork index
`s = cf x` actually corresponds to an `i`-query in `log` (i.e. the `s`-th
`i`-query exists in the log). In Fiat--Shamir applications `cf` extracts the
index of a recorded query, so this property holds by construction. -/
def CfReachable [DecidableEq ι] (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) :
    Prop :=
  ∀ {x : α} {log : QueryLog spec},
    (x, log) ∈ support (replayFirstRun main) →
    ∀ s : Fin (qb i + 1), cf x = some s →
      (QueryLog.getQueryValue? log i ↑s).isSome

/-- Intrinsic form of selector reachability: every selected ordinal is an
actual occurrence on the typed execution path. -/
def PathCfReachable [DecidableEq ι] (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) : Prop :=
  ∀ (path : PFunctor.FreeM.Path main) (s : Fin (qb i + 1)),
    cf (PFunctor.FreeM.output main path) = some s →
      (PFunctor.FreeM.Cursor.locateAt? (P := spec.toPFunctor) i main path s).isSome

/-- Transcript reachability implies the canonical path-level condition. -/
theorem CfReachable.toPathCfReachable [DecidableEq ι] {main : OracleComp spec α} {qb : ι → ℕ}
    {i : ι} {cf : α → Option (Fin (qb i + 1))} (hreach : CfReachable main qb i cf) :
    PathCfReachable main qb i cf := by
  intro path s hcf
  rw [PFunctor.FreeM.Cursor.locateAt?_isSome_iff_lt_occurrences,
    ← PFunctor.TraceList.getAt?_isSome_iff_lt_occurrences, ← QueryLog.getQueryValue?_eq_getAt?]
  exact hreach (replayPathResult_mem_support_replayFirstRun main path
    (mem_support_replayFirstPath main path)) s (by simpa [replayPathResult] using hcf)

/-! ## Intrinsic quantitative games -/

/-- Two independent completions of occurrence `s`, represented entirely by
PolyFun's typed context machinery. -/
def contextForkView [DecidableEq ι] (main : OracleComp spec α) (i : ι) (s : Nat) :
    OracleComp spec (Option (PFunctor.FreeM.Cursor.ForkView i main s)) :=
  PFunctor.FreeM.Cursor.locateAndForkAt (P := spec.toPFunctor) i main s

-- Shared success classifier for the fixed and dynamically selected context-fork experiments.
def classifyForkView [∀ t, DecidableEq (spec.Range t)] (main : OracleComp spec α) (qb : ι → ℕ)
    (i : ι) (cf : α → Option (Fin (qb i + 1))) (s : Fin (qb i + 1))
    (view : PFunctor.FreeM.Cursor.ForkView i main s) : Option (α × α) :=
  let x₁ := PFunctor.FreeM.output main view.firstPath
  let x₂ := PFunctor.FreeM.output main view.secondPath
  if view.firstAnswer = view.secondAnswer then none
  else if cf x₁ = some s ∧ cf x₂ = some s then some (x₁, x₂)
  else none

@[simp] private theorem classifyForkView_isSome [∀ t, DecidableEq (spec.Range t)]
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι) (cf : α → Option (Fin (qb i + 1)))
    (s : Fin (qb i + 1)) (view : PFunctor.FreeM.Cursor.ForkView i main s) :
    (classifyForkView main qb i cf s view).isSome ↔
      view.firstAnswer ≠ view.secondAnswer ∧
        cf (PFunctor.FreeM.output main view.firstPath) = some s ∧
        cf (PFunctor.FreeM.output main view.secondPath) = some s := by
  grind [classifyForkView]

private theorem classifyForkView_component_iff [∀ t, DecidableEq (spec.Range t)]
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι) (cf : α → Option (Fin (qb i + 1)))
    (s : Fin (qb i + 1)) (view : PFunctor.FreeM.Cursor.ForkView i main s) :
    (classifyForkView main qb i cf s view).map (cf ∘ Prod.fst) = some (some s) ↔
      (classifyForkView main qb i cf s view).isSome := by
  grind [classifyForkView]

/-- Semantic result of a dynamically selected fork.  The selecting ordinal,
shared occurrence context, and both completions remain available to
reduction-facing proofs. -/
abbrev ContextForkWitness (main : OracleComp spec α) (qb : ι → ℕ) (i : ι) :=
  PFunctor.FreeM.Cursor.SelectedForkView i main (Fin (qb i + 1)) Fin.val

def acceptContextForkWitness [∀ t, DecidableEq (spec.Range t)] (main : OracleComp spec α)
    (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) (s : Fin (qb i + 1))
    (view : PFunctor.FreeM.Cursor.ForkView i main s) :
    Option (ContextForkWitness main qb i) :=
  if (classifyForkView main qb i cf s view).isSome then some ⟨s, view⟩ else none

@[simp] private theorem acceptContextForkWitness_eq_some [∀ t, DecidableEq (spec.Range t)]
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι) (cf : α → Option (Fin (qb i + 1)))
    (s : Fin (qb i + 1)) (view : PFunctor.FreeM.Cursor.ForkView i main s) :
    acceptContextForkWitness main qb i cf s view = some ⟨s, view⟩ ↔
      view.firstAnswer ≠ view.secondAnswer ∧
        cf (PFunctor.FreeM.output main view.firstPath) = some s ∧
        cf (PFunctor.FreeM.output main view.secondPath) = some s := by
  simp [acceptContextForkWitness]

/-- Canonical rich forking experiment. Probability statements may project
its output pair, while Fiat--Shamir reductions can consume the typed
occurrence and the two completions directly. -/
def contextForkWitness [DecidableEq ι] [∀ t, DecidableEq (spec.Range t)]
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) :
    OracleComp spec (Option (ContextForkWitness main qb i)) :=
  PFunctor.FreeM.Cursor.filterMapLocateAndForkSelected (P := spec.toPFunctor)
    i main cf Fin.val fun selected =>
      acceptContextForkWitness main qb i cf selected.label selected.view

/-- The `outputs` pair of a contextual-fork witness is the pair of oracle outputs read at its
first and second fork paths. -/
@[simp] theorem contextForkWitness_outputs (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (witness : ContextForkWitness main qb i) :
    (PFunctor.FreeM.Cursor.SelectedForkView.outputs witness) =
      (PFunctor.FreeM.output main witness.view.firstPath,
        PFunctor.FreeM.output main witness.view.secondPath) := rfl

def contextForkByClassify [DecidableEq ι] [∀ t, DecidableEq (spec.Range t)]
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) : OracleComp spec (Option (α × α)) :=
  PFunctor.FreeM.Cursor.filterMapLocateAndForkBy (P := spec.toPFunctor)
    i main cf Fin.val (classifyForkView main qb i cf)

private theorem map_contextForkWitness_outputs_eq_contextForkByClassify [DecidableEq ι]
    [∀ t, DecidableEq (spec.Range t)]
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) :
    PFunctor.FreeM.map
        (Option.map PFunctor.FreeM.Cursor.SelectedForkView.outputs)
        (contextForkWitness main qb i cf) = contextForkByClassify main qb i cf := by
  unfold contextForkWitness contextForkByClassify
  rw [PFunctor.FreeM.Cursor.filterMapLocateAndForkSelected_eq_filterMapLocateAndForkBy]
  unfold PFunctor.FreeM.Cursor.filterMapLocateAndForkBy
  rw [← PFunctor.FreeM.comp_map,
    PFunctor.FreeM.Cursor.map_locateAndForkBy,
    PFunctor.FreeM.Cursor.map_locateAndForkBy]
  apply congrArg (PFunctor.FreeM.bind (PFunctor.FreeM.withPath main))
  funext path
  rcases hcf : cf (PFunctor.FreeM.output main path) with _ | s
  · rfl
  · rcases hlocate : PFunctor.FreeM.Cursor.locateAt?
        (P := spec.toPFunctor) i main path s with _ | located
    · simp [hlocate]
    · simp only [hlocate]
      apply congrArg (fun f => PFunctor.FreeM.map f located.fork)
      funext view
      simp only [Function.comp_apply, Option.join, Option.map]
      unfold acceptContextForkWitness classifyForkView
      split <;> split <;> simp_all
      grind

/-- Canonical dynamically selected fork. The first execution chooses an
ordinal through `cf`; PolyFun locates that occurrence and independently
completes the same typed context a second time. -/
def contextFork [DecidableEq ι] [∀ t, DecidableEq (spec.Range t)] (main : OracleComp spec α)
    (qb : ι → ℕ) (i : ι) (cf : α → Option (Fin (qb i + 1))) :
    OracleComp spec (Option (α × α)) :=
  PFunctor.FreeM.map
    (Option.map PFunctor.FreeM.Cursor.SelectedForkView.outputs)
    (contextForkWitness main qb i cf)

private theorem contextFork_eq_contextForkByClassify [DecidableEq ι]
    [∀ t, DecidableEq (spec.Range t)] (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) :
    contextFork main qb i cf = contextForkByClassify main qb i cf :=
  map_contextForkWitness_outputs_eq_contextForkByClassify main qb i cf

/-- Every supported rich witness carries a supported second completion and
the pure success conditions checked by the contextual fork. -/
theorem contextForkWitness_success [DecidableEq ι] [∀ t, DecidableEq (spec.Range t)]
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1)))
    {witness : ContextForkWitness main qb i}
    (h : some witness ∈ support (contextForkWitness main qb i cf)) :
    witness.view.second ∈ support (Cursor.completeOccurrence witness.view.occurrence) ∧
      witness.view.firstAnswer ≠ witness.view.secondAnswer ∧
      cf (PFunctor.FreeM.output main witness.view.firstPath) = some witness.label ∧
      cf (PFunctor.FreeM.output main witness.view.secondPath) = some witness.label := by
  rw [contextForkWitness,
    PFunctor.FreeM.Cursor.filterMapLocateAndForkSelected_eq_filterMapLocateAndForkBy,
    PFunctor.FreeM.Cursor.filterMapLocateAndForkBy_eq_bind_complete] at h
  obtain ⟨path, _, h⟩ := mem_support_bind_peel _ _ h
  rcases hcf : cf (PFunctor.FreeM.output main path) with _ | s
  · simp only [hcf] at h
    cases eq_of_mem_support_pure none h
  rcases hlocated : PFunctor.FreeM.Cursor.locateAt?
      (P := spec.toPFunctor) i main path s with _ | located
  · simp only [hcf, hlocated] at h
    cases eq_of_mem_support_pure none h
  simp only [hcf, hlocated] at h
  obtain ⟨second, hsecond, hresult⟩ := mem_support_map_peel _ _ h
  by_cases haccept : (classifyForkView main qb i cf s
      { occurrence := located.occurrence, first := located.completion, second := second }).isSome
  · rw [acceptContextForkWitness, ite_eq_left haccept, Option.some.injEq] at hresult
    subst hresult
    exact ⟨hsecond, (classifyForkView_isSome main qb i cf s _).mp haccept⟩
  · rw [acceptContextForkWitness, ite_eq_right haccept] at hresult
    cases hresult

/-- Successful contextual forks expose the selected path, its certified
occurrence, and the independently sampled second completion. -/
theorem contextFork_success [DecidableEq ι] [∀ t, DecidableEq (spec.Range t)]
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) {x₁ x₂ : α}
    (h : some (x₁, x₂) ∈ support (contextFork main qb i cf)) :
    ∃ (path : PFunctor.FreeM.Path main) (s : Fin (qb i + 1))
      (located : PFunctor.FreeM.Cursor.Located i main path s)
      (second : located.occurrence.Completion),
      path ∈ support (Cursor.withPath main) ∧
      cf (PFunctor.FreeM.output main path) = some s ∧
      second ∈ support (Cursor.completeOccurrence located.occurrence) ∧
      located.completion.answer ≠ second.answer ∧
      cf (PFunctor.FreeM.output main second.path) = some s ∧
      x₁ = PFunctor.FreeM.output main path ∧
      x₂ = PFunctor.FreeM.output main second.path := by
  rw [contextFork] at h
  have hmap : some (x₁, x₂) ∈
      (Option.map PFunctor.FreeM.Cursor.SelectedForkView.outputs) ''
        support (contextForkWitness main qb i cf) := by
    exact (congrArg (some (x₁, x₂) ∈ ·)
      (PFunctor.FreeM.support_map
        (Option.map PFunctor.FreeM.Cursor.SelectedForkView.outputs)
        (contextForkWitness main qb i cf))).mp h
  obtain ⟨result, hresult, houtputs⟩ := hmap
  rcases result with _ | witness
  · simp at houtputs
  · simp only [Option.map, Option.some.injEq] at houtputs
    obtain ⟨hsecond, hne, hcf₁, hcf₂⟩ :=
      contextForkWitness_success main qb i cf hresult
    exact ⟨witness.view.firstPath, witness.label,
      .ofCompletion witness.view.first, witness.view.second,
      mem_support_replayFirstPath main witness.view.firstPath, hcf₁, hsecond, hne,
      hcf₂, (congrArg Prod.fst houtputs).symm, (congrArg Prod.snd houtputs).symm⟩

/-- Transfer first-run log invariants through a successful contextual fork.
The differing selected entries follow directly from the two completions of
the retained occurrence. -/
theorem contextFork_propertyTransfer [DecidableEq ι] [∀ t, DecidableEq (spec.Range t)]
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1)))
    (P_out : α → QueryLog spec → Prop)
    (hP : ∀ {x log}, (x, log) ∈ support (replayFirstRun main) → P_out x log)
    {x₁ x₂ : α} (h : some (x₁, x₂) ∈ support (contextFork main qb i cf)) :
    ∃ (log₁ log₂ : QueryLog spec) (s : Fin (qb i + 1)),
      cf x₁ = some s ∧ cf x₂ = some s ∧
      P_out x₁ log₁ ∧ P_out x₂ log₂ ∧
      QueryLog.getQueryValue? log₁ i s ≠
        QueryLog.getQueryValue? log₂ i s := by
  obtain ⟨path, s, located, second, hpath, hcf₁, _hsecond,
      hne, hcf₂, hx₁, hx₂⟩ := contextFork_success main qb i cf h
  let log₁ : QueryLog spec := PFunctor.FreeM.Path.trace main path
  let log₂ : QueryLog spec := PFunctor.FreeM.Path.trace main second.path
  have hlookup₁ : QueryLog.getQueryValue? log₁ i s = some located.completion.answer := by
    simpa [log₁] using congrArg (PFunctor.FreeM.Path.trace main) located.path_eq ▸
      getQueryValue?_completion_path_eq_answer located.occurrence located.completion
  refine ⟨log₁, log₂, s, hx₁ ▸ hcf₁, hx₂ ▸ hcf₂, hP ?_, hP ?_, ?_⟩
  · simpa [log₁, replayPathResult, hx₁] using
      replayPathResult_mem_support_replayFirstRun main path hpath
  · simpa [log₂, replayPathResult, hx₂] using
      replayPathResult_mem_support_replayFirstRun main second.path
        (mem_support_replayFirstPath main second.path)
  · rw [hlookup₁, getQueryValue?_completion_path_eq_answer located.occurrence second]
    exact fun heq => hne (Option.some.inj heq)

/-- The fixed-index guarded context experiment. It succeeds exactly when both
outputs select `s` and the two focused oracle answers differ. -/
def guardedContextFork [DecidableEq ι] [∀ t, DecidableEq (spec.Range t)]
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) (s : Fin (qb i + 1)) :
    OracleComp spec (Option (α × α)) :=
  PFunctor.FreeM.Cursor.filterMapLocateAndForkAt i main s (classifyForkView main qb i cf s)

def collideForkView [∀ t, DecidableEq (spec.Range t)] (main : OracleComp spec α) (qb : ι → ℕ)
    (i : ι) (cf : α → Option (Fin (qb i + 1))) (s : Fin (qb i + 1)) :
    Option (PFunctor.FreeM.Cursor.ForkView i main s) → Option (Fin (qb i + 1))
  | none => none
  | some view => if view.firstAnswer = view.secondAnswer ∧
      cf (PFunctor.FreeM.output main view.firstPath) = some s ∧
      cf (PFunctor.FreeM.output main view.secondPath) = some s
      then some s else none

@[simp] private theorem collideForkView_eq_some [∀ t, DecidableEq (spec.Range t)]
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι) (cf : α → Option (Fin (qb i + 1)))
    (s : Fin (qb i + 1)) (view : PFunctor.FreeM.Cursor.ForkView i main s) :
    collideForkView main qb i cf s (some view) = some s ↔
      view.firstAnswer = view.secondAnswer ∧
        cf (PFunctor.FreeM.output main view.firstPath) = some s ∧
        cf (PFunctor.FreeM.output main view.secondPath) = some s := by
  simp [collideForkView]

def contextForkViewCollision [DecidableEq ι] [∀ t, DecidableEq (spec.Range t)]
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) (s : Fin (qb i + 1)) :
    OracleComp spec (Option (Fin (qb i + 1))) :=
  PFunctor.FreeM.map (collideForkView main qb i cf s) (contextForkView main i s)

/-- Per-path continuation of `contextForkCollision`. Locate occurrence `s` on `path`; if it is
present, resample the focused answer and report `some s` exactly when the fresh answer collides
with the first completion's answer and the path already selected `s`. -/
def contextForkCollisionCont [DecidableEq ι] [∀ t, DecidableEq (spec.Range t)]
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) (s : Fin (qb i + 1)) (path : PFunctor.FreeM.Path main) :
    OracleComp spec (Option (Fin (qb i + 1))) :=
  match PFunctor.FreeM.Cursor.locateAt? (P := spec.toPFunctor) i main path s with
  | none => pure none
  | some located => do
      let secondAnswer ← spec.query i
      if located.completion.answer = secondAnswer ∧ cf (PFunctor.FreeM.output main path) = some s
        then pure (some s) else pure none

/-- Equal focused answers form the sole collision branch removed by
`guardedContextFork`. -/
def contextForkCollision [DecidableEq ι] [∀ t, DecidableEq (spec.Range t)]
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) (s : Fin (qb i + 1)) :
    OracleComp spec (Option (Fin (qb i + 1))) :=
  PFunctor.FreeM.withPath main >>= contextForkCollisionCont main qb i cf s

section nativeBounds

variable [∀ t, MeasurableSpace (spec.Range t)] [∀ t, DiscreteMeasurableSpace (spec.Range t)]

omit [∀ t, DiscreteMeasurableSpace (spec.Range t)] in
/-- An event of a mapped raw polynomial program is the pulled-back event. -/
private theorem prEvent_ofFreeM_map [OracleSpec.IsMeasureSpec spec] {β γ : Type}
    (mx : spec.toPFunctor.FreeM β) (f : β → γ) (p : γ → Prop) :
    Pr{let r ← OracleComp.ofFreeM (PFunctor.FreeM.map f mx)}[p r] =
      Pr{let x ← OracleComp.ofFreeM mx}[p (f x)] :=
  prEvent_map (OracleComp.ofFreeM mx) f p

/-- An event of a raw polynomial `pure` is its indicator. -/
private theorem prEvent_ofFreeM_pure [OracleSpec.IsMeasureSpec spec] {β : Type} (x : β)
    (p : β → Prop) [Decidable (p x)] :
    Pr{let r ← OracleComp.ofFreeM (pure x : spec.toPFunctor.FreeM β)}[p r] =
      if p x then 1 else 0 :=
  prEvent_pure (m := OracleComp spec) x p

/-- Raw polynomial binds with pointwise equal continuation events have equal events. -/
private theorem prEvent_ofFreeM_bind_congr [OracleSpec.IsMeasureSpec spec] {β γ δ : Type}
    (mx : spec.toPFunctor.FreeM β) (f : β → spec.toPFunctor.FreeM γ)
    (g : β → spec.toPFunctor.FreeM δ) (p : γ → Prop) (q : δ → Prop)
    (h : ∀ x, Pr{let r ← OracleComp.ofFreeM (f x)}[p r] =
      Pr{let r ← OracleComp.ofFreeM (g x)}[q r]) :
    Pr{let r ← OracleComp.ofFreeM (PFunctor.FreeM.bind mx f)}[p r] =
      Pr{let r ← OracleComp.ofFreeM (PFunctor.FreeM.bind mx g)}[q r] :=
  prEvent_bind_congr (OracleComp.ofFreeM mx) (fun x => OracleComp.ofFreeM (f x))
    (fun x => OracleComp.ofFreeM (g x)) p q h

/-- A classified fork whose first completion does not select `s` never succeeds. -/
private theorem prEvent_classifyForkView_isSome_eq_zero_of_first_ne
    [∀ t, DecidableEq (spec.Range t)] [OracleSpec.IsMeasureSpec spec]
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) (s : Fin (qb i + 1))
    {path : PFunctor.FreeM.Path main}
    (located : PFunctor.FreeM.Cursor.Located i main path s)
    (hfirst : cf (PFunctor.FreeM.output main located.completion.path) ≠ some s) :
    Pr{let result ← OracleComp.ofFreeM (PFunctor.FreeM.map
        (fun second => classifyForkView main qb i cf s {
          occurrence := located.occurrence
          first := located.completion
          second := second }) located.occurrence.complete)}[result.isSome] = 0 :=
  (prEvent_map (OracleComp.ofFreeM located.occurrence.complete) _ _).trans
    (prEvent_eq_zero_of_forall_not _ _ fun second h => by
      simp [PFunctor.FreeM.Cursor.ForkView.firstPath, hfirst] at h)

/-- A classified fork for index `t` never reports the component of a different index `s`. -/
private theorem prEvent_classifyForkView_component_eq_zero_of_ne
    [∀ t, DecidableEq (spec.Range t)] [OracleSpec.IsMeasureSpec spec]
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) (t s : Fin (qb i + 1))
    {path : PFunctor.FreeM.Path main}
    (located : PFunctor.FreeM.Cursor.Located i main path t) (hne : t ≠ s) :
    Pr{let result ← OracleComp.ofFreeM (PFunctor.FreeM.map
        (fun second => classifyForkView main qb i cf t {
          occurrence := located.occurrence
          first := located.completion
          second := second }) located.occurrence.complete)}[
        result.map (cf ∘ Prod.fst) = some (some s)] = 0 :=
  (prEvent_map (OracleComp.ofFreeM located.occurrence.complete) _ _).trans
    (prEvent_eq_zero_of_forall_not _ _ fun second h => by grind [classifyForkView])

/-- The pair of `cf`-classifications observed from the two completions of the fixed
occurrence at index `i` and position `s`: the `contextForkView`-family specialization of
`observedForkPair` over which the replay-forking squaring and partition bounds are stated. -/
def contextForkPair [DecidableEq ι] (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) (s : Fin (qb i + 1)) :
    OracleComp spec (Option (Option (Fin (qb i + 1)) × Option (Fin (qb i + 1)))) :=
  observedForkPair main i s cf

/-- Fixed-index success squares under two independent completions of the
PolyFun occurrence context. This is the analytic core of replay forking and
does not use query logs, replay cursors, or a bespoke oracle interpreter. -/
theorem sq_prEvent_main_le_contextForkPair [DecidableEq ι] [OracleSpec.IsMeasureSpec spec]
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1)))
    (hreach : PathCfReachable main qb i cf) (s : Fin (qb i + 1)) :
    Pr{let x ← main}[cf x = some s] ^ 2 ≤
      Pr{let r ← contextForkPair main qb i cf s}[r = some (some s, some s)] :=
  prEvent_sq_le_observedForkPair main i s cf s (fun path => hreach path s)

/-- Fixed-index pair success partitions into a genuine guarded fork or an
equal-answer collision, all as observations of the same `ForkView`. -/
theorem prEvent_contextForkPair_le_guarded_add_collision [DecidableEq ι]
    [∀ t, DecidableEq (spec.Range t)] [OracleSpec.IsMeasureSpec spec]
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) (s : Fin (qb i + 1)) :
    Pr{let r ← contextForkPair main qb i cf s}[r = some (some s, some s)] ≤
      Pr{let r ← guardedContextFork main qb i cf s}[r.isSome] +
        Pr{let r ← contextForkViewCollision main qb i cf s}[r = some s] := by
  let source := contextForkView main i s
  let pairGood : Option (PFunctor.FreeM.Cursor.ForkView i main (s : Nat)) → Prop
    | none => False
    | some view =>
        cf (PFunctor.FreeM.output main view.firstPath) = some s ∧
        cf (PFunctor.FreeM.output main view.secondPath) = some s
  let guardGood : Option (PFunctor.FreeM.Cursor.ForkView i main (s : Nat)) → Prop :=
    fun view? => (view?.bind (classifyForkView main qb i cf s)).isSome
  let collisionGood : Option (PFunctor.FreeM.Cursor.ForkView i main (s : Nat)) → Prop :=
    fun view? => collideForkView main qb i cf s view? = some s
  have hpoint : ∀ view?, pairGood view? → guardGood view? ∨ collisionGood view? := by
    rintro (_ | view) <;> simp only [pairGood] <;> grind [classifyForkView, collideForkView]
  have hpair : Pr{let r ← contextForkPair main qb i cf s}[r = some (some s, some s)] =
      Pr{let v ← source}[pairGood v] := by
    rw [contextForkPair, observedForkPair, prEvent_map]
    exact prEvent_congr _ _ _ fun view? => by rcases view? with _ | view <;> simp [pairGood]
  have hguard : Pr{let v ← source}[guardGood v] =
      Pr{let r ← guardedContextFork main qb i cf s}[r.isSome] :=
    (prEvent_map source (fun view? => view?.bind (classifyForkView main qb i cf s))
      (fun r => r.isSome)).symm
  have hcollision : Pr{let v ← source}[collisionGood v] =
      Pr{let r ← contextForkViewCollision main qb i cf s}[r = some s] :=
    (prEvent_map source (collideForkView main qb i cf s) (· = some s)).symm
  rw [hpair, ← hguard, ← hcollision]
  exact (prEvent_mono source _ _ fun view? => hpoint view?).trans
    (prEvent_or_le source guardGood collisionGood)

/-- A fresh focused answer collides with the first completion's answer with
probability at most the inverse answer-space cardinality. -/
theorem prEvent_contextForkCollision_le_main_div [DecidableEq ι]
    [∀ t, DecidableEq (spec.Range t)] [OracleSpec.IsUniformMeasureSpec spec]
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι) [Fintype (spec.Range i)]
    (cf : α → Option (Fin (qb i + 1))) (s : Fin (qb i + 1)) :
    Pr{let r ← contextForkCollision main qb i cf s}[r = some s] ≤
      Pr{let x ← main}[cf x = some s] / Fintype.card (spec.Range i) := by
  have hpaths : (PFunctor.FreeM.output main <$> PFunctor.FreeM.withPath main :
      OracleComp spec α) = main := PFunctor.FreeM.map_output_withPath main
  conv_rhs => rw [← hpaths, prEvent_map, div_eq_mul_inv]
  refine prEvent_bind_le_prEvent_mul_of_forall_le _ _ _ _ (fun path hcf => ?_)
    (fun path hcf => ?_)
  · simp only [contextForkCollisionCont]
    rcases PFunctor.FreeM.Cursor.locateAt? (P := spec.toPFunctor) i main path s
      with _ | located
    · simp
    · refine (prEvent_bind_mono_of_forall_le _ _ (fun second => pure second) _
        (fun second => located.completion.answer = second) fun second => ?_).trans ?_
      · by_cases heq : located.completion.answer = second <;> simp [hcf, heq]
      · rw [bind_pure, prEvent_liftM_query_eq_card_div]
        simp [Finset.filter_eq]
  · simp only [contextForkCollisionCont]
    rcases PFunctor.FreeM.Cursor.locateAt? (P := spec.toPFunctor) i main path s
      with _ | located
    · simp
    · refine prEvent_eq_zero_of_forall_mem_support _ _ fun r hr => ?_
      obtain ⟨second, -, hr⟩ := (mem_support_bind_iff _ _ _).mp hr
      simp only [hcf, and_false, ite_false, support_pure, Set.mem_singleton_iff] at hr
      subst hr
      simp

/-- Requiring the colliding second completion to finish successfully can only
decrease the path-first equal-answer collision probability. -/
theorem prEvent_contextForkViewCollision_le_collision [DecidableEq ι]
    [∀ t, DecidableEq (spec.Range t)] [OracleSpec.IsMeasureSpec spec]
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) (s : Fin (qb i + 1)) :
    Pr{let r ← contextForkViewCollision main qb i cf s}[r = some s] ≤
      Pr{let r ← contextForkCollision main qb i cf s}[r = some s] := by
  let paths : OracleComp spec (PFunctor.FreeM.Path main) := PFunctor.FreeM.withPath main
  let viewCollision : PFunctor.FreeM.Path main →
      OracleComp spec (Option (Fin (qb i + 1))) := fun path =>
    match PFunctor.FreeM.Cursor.locateAt? (P := spec.toPFunctor) i main path s with
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
  have hsource : contextForkViewCollision main qb i cf s =
      paths >>= viewCollision := by
    unfold contextForkViewCollision contextForkView
    rw [PFunctor.FreeM.Cursor.map_locateAndForkAt]
    apply congrArg (fun k => paths >>= k)
    funext path
    simp only [viewCollision]
    rcases PFunctor.FreeM.Cursor.locateAt?
        (P := spec.toPFunctor) i main path s with _ | located
    · rfl
    · simp [PFunctor.FreeM.Cursor.Located.fork]
  rw [hsource, contextForkCollision]
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun path => ?_
  simp only [viewCollision, contextForkCollisionCont]
  rcases hlocated : PFunctor.FreeM.Cursor.locateAt?
      (P := spec.toPFunctor) i main path s with _ | located
  · exact le_rfl
  · let continuation : spec.Range i → OracleComp spec (Option (Fin (qb i + 1))) :=
      fun secondAnswer =>
        (fun secondSuffix =>
          collideForkView main qb i cf s (some {
            occurrence := located.occurrence
            first := located.completion
            second := ⟨secondAnswer, secondSuffix⟩ })) <$>
          PFunctor.FreeM.withPath (located.occurrence.resume secondAnswer)
    change Pr{let r ← ((liftM (query i) : OracleComp spec (spec.Range i)) >>= continuation)}[
      r = some s] ≤ _
    refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun secondAnswer => ?_
    rw [prEvent_map]
    by_cases heq : located.completion.answer = secondAnswer
    · by_cases hcf : cf (PFunctor.FreeM.output main path) = some s
      · simp only [heq, hcf, and_self, ite_true]
        rw [prEvent_pure]
        simp only [ite_true]
        exact prEvent_le_one _
      · have hfirst : cf (PFunctor.FreeM.output main located.completion.path) ≠ some s := by
          rw [located.path_eq]; exact hcf
        refine (le_of_eq (prEvent_eq_zero_of_forall_not _ _ fun _ h => ?_)).trans zero_le
        simp [collideForkView, PFunctor.FreeM.Cursor.ForkView.firstPath, hfirst] at h
    · refine (le_of_eq (prEvent_eq_zero_of_forall_not _ _ fun _ h => ?_)).trans zero_le
      simp [collideForkView, PFunctor.FreeM.Cursor.ForkView.firstAnswer,
        PFunctor.FreeM.Cursor.ForkView.secondAnswer, heq] at h

/-- The successful equal-answer branch of the intrinsic context experiment is
bounded by one uniform-answer collision against the original success event. -/
theorem prEvent_contextForkViewCollision_le_main_div [DecidableEq ι]
    [∀ t, DecidableEq (spec.Range t)] [OracleSpec.IsUniformMeasureSpec spec]
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι) [Fintype (spec.Range i)]
    (cf : α → Option (Fin (qb i + 1))) (s : Fin (qb i + 1)) :
    Pr{let r ← contextForkViewCollision main qb i cf s}[r = some s] ≤
      Pr{let x ← main}[cf x = some s] / Fintype.card (spec.Range i) :=
  (prEvent_contextForkViewCollision_le_collision main qb i cf s).trans
    (prEvent_contextForkCollision_le_main_div main qb i cf s)

/-- Fixed-occurrence forking succeeds with the usual square-minus-collision
lower bound, stated directly for the guarded PolyFun context experiment. -/
theorem sq_sub_div_le_prEvent_guardedContextFork [DecidableEq ι]
    [∀ t, DecidableEq (spec.Range t)] [OracleSpec.IsUniformMeasureSpec spec]
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι) [Fintype (spec.Range i)]
    (cf : α → Option (Fin (qb i + 1)))
    (hreach : PathCfReachable main qb i cf) (s : Fin (qb i + 1)) :
    let h : ℝ≥0∞ := ↑(Fintype.card (spec.Range i))
    Pr{let x ← main}[cf x = some s] ^ 2 - Pr{let x ← main}[cf x = some s] / h ≤
      Pr{let r ← guardedContextFork main qb i cf s}[r.isSome] :=
  tsub_le_iff_right.2 <|
    (sq_prEvent_main_le_contextForkPair main qb i cf hreach s).trans <|
    (prEvent_contextForkPair_le_guarded_add_collision main qb i cf s).trans <|
      add_le_add le_rfl (prEvent_contextForkViewCollision_le_main_div main qb i cf s)

/-- A fixed guarded fork is the corresponding component of the dynamic
semantic fork. -/
theorem prEvent_guardedContextFork_eq_contextFork_component [DecidableEq ι]
    [∀ t, DecidableEq (spec.Range t)] [OracleSpec.IsMeasureSpec spec]
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) (s : Fin (qb i + 1)) :
    Pr{let r ← guardedContextFork main qb i cf s}[r.isSome] =
      Pr{let r ← contextFork main qb i cf}[r.map (cf ∘ Prod.fst) = some (some s)] := by
  rw [contextFork_eq_contextForkByClassify]
  unfold guardedContextFork contextForkByClassify
  rw [PFunctor.FreeM.Cursor.filterMapLocateAndForkAt_eq_bind_complete,
    PFunctor.FreeM.Cursor.filterMapLocateAndForkBy_eq_bind_complete]
  classical
  refine prEvent_ofFreeM_bind_congr _ _ _ _ _ fun path => ?_
  rcases hcf : cf (PFunctor.FreeM.output main path) with _ | t
  · dsimp only
    rcases hloc : PFunctor.FreeM.Cursor.locateAt?
        (P := spec.toPFunctor) i main path s with _ | located
    · dsimp only
      simp only [prEvent_ofFreeM_pure]
      simp
    · have hfirst :
          cf (PFunctor.FreeM.output main located.completion.path) = none := by
        simpa only [located.path_eq] using hcf
      dsimp only
      rw [prEvent_classifyForkView_isSome_eq_zero_of_first_ne
        main qb i cf s located (by simp [hfirst])]
      simp only [prEvent_ofFreeM_pure]
      simp
  · by_cases hts : t = s
    · subst t
      dsimp only
      rcases hloc : PFunctor.FreeM.Cursor.locateAt?
          (P := spec.toPFunctor) i main path s with _ | located
      · dsimp only
        simp only [prEvent_ofFreeM_pure]
        simp
      · dsimp only
        rw [prEvent_ofFreeM_map, prEvent_ofFreeM_map]
        exact prEvent_congr _ _ _ fun second => (classifyForkView_component_iff main qb i cf s {
            occurrence := located.occurrence
            first := located.completion
            second := second }).symm
    · dsimp only
      trans (0 : ℝ≥0∞)
      · rcases hlocFixed : PFunctor.FreeM.Cursor.locateAt?
            (P := spec.toPFunctor) i main path s with _ | locatedFixed
        · dsimp only
          simp only [prEvent_ofFreeM_pure]
          simp
        · have hfirstNe :
              cf (PFunctor.FreeM.output main locatedFixed.completion.path) ≠ some s := by
            simp only [locatedFixed.path_eq, hcf]
            grind
          exact prEvent_classifyForkView_isSome_eq_zero_of_first_ne
            main qb i cf s locatedFixed hfirstNe
      · rcases hlocDynamic : PFunctor.FreeM.Cursor.locateAt?
            (P := spec.toPFunctor) i main path t with _ | locatedDynamic
        · dsimp only
          simp only [prEvent_ofFreeM_pure]
          simp
        · exact (prEvent_classifyForkView_component_eq_zero_of_ne
            main qb i cf t s locatedDynamic hts).symm

/-- Direct probability bound for the canonical semantic context fork. The
program manipulation is discharged by PolyFun; this theorem contains only
the finite selector aggregation and the usual Cauchy--Schwarz estimate. -/
theorem le_prEvent_isSome_contextFork [DecidableEq ι] [∀ t, DecidableEq (spec.Range t)]
    [OracleSpec.IsUniformMeasureSpec spec]
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι) [Fintype (spec.Range i)]
    (cf : α → Option (Fin (qb i + 1)))
    (hreach : PathCfReachable main qb i cf) :
    (let acc : ℝ≥0∞ := ∑ s, Pr{let x ← main}[cf x = some s]
     let h : ℝ≥0∞ := Fintype.card (spec.Range i)
     let q := qb i + 1
     acc * (acc / q - h⁻¹)) ≤ Pr{let r ← contextFork main qb i cf}[r.isSome] := by
  dsimp only
  set ps : Fin (qb i + 1) → ℝ≥0∞ := fun s => Pr{let x ← main}[cf x = some s]
  set h : ℝ≥0∞ := ↑(Fintype.card (spec.Range i))
  have hsum : (∑ s, ps s) ≠ ⊤ :=
    ne_top_of_le_ne_top one_ne_top (sum_prEvent_eq_some_le_one main cf)
  have hcard : ((Finset.univ : Finset (Fin (qb i + 1))).card : ℝ≥0∞) =
      ((qb i + 1 : ℕ) : ℝ≥0∞) := by simp
  calc
    (∑ s, ps s) * ((∑ s, ps s) / ((qb i + 1 : ℕ) : ℝ≥0∞) - h⁻¹)
        ≤ ∑ s, (ps s ^ 2 - ps s / h) := by
          have hbound := ENNReal.mul_tsub_inv_le_sum_sq_sub_div univ ps h hsum
          rwa [hcard] at hbound
    _ ≤ ∑ s, Pr{let r ← guardedContextFork main qb i cf s}[r.isSome] :=
          Finset.sum_le_sum fun s _ =>
            sq_sub_div_le_prEvent_guardedContextFork main qb i cf hreach s
    _ = ∑ s, Pr{let r ← contextFork main qb i cf}[r.map (cf ∘ Prod.fst) = some (some s)] :=
          Finset.sum_congr rfl fun s _ =>
            prEvent_guardedContextFork_eq_contextFork_component main qb i cf s
    _ ≤ _ := sum_prEvent_option_map_eq_some_le_isSome _ _

end nativeBounds

end quantitative

end OracleComp
