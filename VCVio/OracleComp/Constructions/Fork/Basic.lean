/-
Copyright (c) 2026 Devon Tuma, Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module
public import PolyFun.PFunctor.Free.Cursor.Fork
public import ToMathlib.Probability.UniformOn
public import VCVio.EvalDist.ProbabilityBounds
public import VCVio.OracleComp.EvalDist.MeasureSpec

/-!
# Measure bounds for typed occurrence forks

Two independent completions of a selected occurrence bound the squared event probability of
one execution. The argument applies to arbitrary discrete response measures, and observations
need no measurable-space arguments on intermediate values. Completing an occurrence and
observing its answer recovers the query's configured measure. A located fork's second answer
has the same marginal, so its collision probability is the mass of the fixed first answer.
-/

public section

open OracleSpec ENNReal MeasureTheory
open scoped PFunctor

namespace OracleComp

variable {ι : Type} {spec : OracleSpec ι} {α β : Type}

namespace Cursor

/-- Execute an intrinsic path through the `OracleComp` abstraction boundary. -/
@[expose, reducible]
def withPath (main : OracleComp spec α) : OracleComp spec (PFunctor.FreeM.Path main) :=
  ofFreeM (PFunctor.FreeM.withPath (toFreeM main))

@[simp] private theorem map_output_withPath (main : OracleComp spec α) :
    (PFunctor.FreeM.output main <$> withPath main : OracleComp spec α) = main :=
  PFunctor.FreeM.map_output_withPath main

/-- Split at an occurrence through the `OracleComp` abstraction boundary. -/
@[expose, reducible]
def splitAtValid [spec.DecidableEq] (main : OracleComp spec α) (i : ι) (n : Nat) :
    OracleComp spec {split : PFunctor.FreeM.Cursor.Split i main n // split.Valid} :=
  ofFreeM (PFunctor.FreeM.Cursor.splitAtValid i (toFreeM main) n)

/-- Complete one occurrence split through the `OracleComp` abstraction boundary. -/
@[expose, reducible]
def complete {main : OracleComp spec α} {i : ι} {n : Nat}
    (split : PFunctor.FreeM.Cursor.Split i main n) : OracleComp spec (PFunctor.FreeM.Path main) :=
  ofFreeM split.complete

/-- Complete a fork through the `OracleComp` abstraction boundary. -/
@[expose, reducible]
def completeFork {main : OracleComp spec α} {i : ι} {n : Nat}
    (split : PFunctor.FreeM.Cursor.Split i main n) :
    OracleComp spec (Option (PFunctor.FreeM.Cursor.ForkView i main n)) :=
  ofFreeM split.completeFork

/-- Complete an occurrence through the `OracleComp` abstraction boundary. -/
@[expose, reducible]
def completeOccurrence {main : OracleComp spec α} {i : ι} {n : Nat}
    (occurrence : PFunctor.FreeM.Cursor.Occurrence i main n) :
    OracleComp spec occurrence.Completion :=
  ofFreeM occurrence.complete

end Cursor

section answer

variable [∀ t, MeasurableSpace (spec.Range t)]
  [∀ t, DiscreteMeasurableSpace (spec.Range t)] [IsMeasureSpec spec]

/-- The answer marginal of an occurrence completion is its configured query measure. -/
@[simp↓ high, grind norm↓]
theorem evalDist_map_answer_completeOccurrence {main : OracleComp spec α} {i : ι} {n : Nat}
    (occurrence : PFunctor.FreeM.Cursor.Occurrence i main n) :
    𝒟[(fun completion ↦ completion.answer) <$> Cursor.completeOccurrence occurrence] =
      IsMeasureSpec.toMeasure (spec := spec) i := by
  simp only [Cursor.completeOccurrence, PFunctor.FreeM.Cursor.Occurrence.complete,
    PFunctor.FreeM.liftBind_eq, ofFreeM_bind, ofFreeM_map, map_bind, Functor.map_map]
  calc
    _ = 𝒟[(ofFreeM (PFunctor.FreeM.lift (P := spec.toPFunctor) i) :
        OracleComp spec (spec.Range i)) >>= fun answer ↦ pure answer] := by
      apply evalDist_bind_congr
      intro answer
      simp only [OracleComp.evalDist_map_const, evalDist_pure]
    _ = _ := by
      simpa only [bind_pure] using PFunctor.FreeM.evalDist_lift (P := spec.toPFunctor) i

/-- Events on the answer of an occurrence completion are events of a fresh query. -/
@[simp↓ high, grind norm↓]
theorem prEvent_answer_completeOccurrence {main : OracleComp spec α} {i : ι} {n : Nat}
    (occurrence : PFunctor.FreeM.Cursor.Occurrence i main n) (p : spec.Range i → Prop) :
    Pr{let completion ← Cursor.completeOccurrence occurrence}[p completion.answer] =
      Pr{let answer ← (query i : OracleComp spec (spec.Range i))}[p answer] := by
  rw [← prEvent_map (Cursor.completeOccurrence occurrence) (fun c ↦ c.answer) p,
    prEvent_eq_evalDist_of_discrete, evalDist_map_answer_completeOccurrence,
    prEvent_eq_evalDist_of_discrete, evalDist_query]

/-- The second answer of a located fork has its configured query measure. -/
@[simp↓ high, grind norm↓]
theorem evalDist_map_secondAnswer_fork {main : OracleComp spec α} {i : ι} {n : Nat}
    {path : PFunctor.FreeM.Path main}
    (located : PFunctor.FreeM.Cursor.Located i main path n) :
    𝒟[(fun view ↦ view.secondAnswer) <$> ofFreeM located.fork] =
      IsMeasureSpec.toMeasure (spec := spec) i := by
  rw [PFunctor.FreeM.Cursor.Located.fork_eq_map_complete, ofFreeM_map, Functor.map_map]
  simpa only [Function.comp_def, PFunctor.FreeM.Cursor.ForkView.secondAnswer_mk,
    Cursor.completeOccurrence] using evalDist_map_answer_completeOccurrence located.occurrence

/-- A located fork collides exactly with the measure of its fixed first answer. -/
@[simp↓ high, grind norm↓]
theorem prEvent_focusCollision_fork {main : OracleComp spec α} {i : ι} {n : Nat}
    {path : PFunctor.FreeM.Path main}
    (located : PFunctor.FreeM.Cursor.Located i main path n) :
    Pr{let view ← ofFreeM located.fork}[view.firstAnswer = view.secondAnswer] =
      IsMeasureSpec.toMeasure (spec := spec) i {located.completion.answer} := by
  rw [PFunctor.FreeM.Cursor.Located.fork_eq_map_complete, ofFreeM_map, prEvent_map]
  simp only [PFunctor.FreeM.Cursor.ForkView.firstAnswer_mk,
    PFunctor.FreeM.Cursor.ForkView.secondAnswer_mk]
  rw [prEvent_answer_completeOccurrence, prEvent_eq_evalDist_of_discrete, evalDist_query]
  congr 1
  ext answer
  simp [eq_comm]

/-- Adding a guard to a located fork's collision event only decreases its probability. -/
theorem prEvent_focusCollision_fork_le {main : OracleComp spec α} {i : ι} {n : Nat}
    {path : PFunctor.FreeM.Path main}
    (located : PFunctor.FreeM.Cursor.Located i main path n) (accept : α → Prop) :
    Pr{let view ← ofFreeM located.fork}[view.firstAnswer = view.secondAnswer ∧
      accept (PFunctor.FreeM.output main view.firstPath)] ≤
      IsMeasureSpec.toMeasure (spec := spec) i {located.completion.answer} :=
  (prEvent_mono _ _ _ fun _ h ↦ h.1).trans_eq (prEvent_focusCollision_fork located)

end answer

/-- Under uniform answer measures, a guarded collision is bounded by inverse cardinality. -/
theorem prEvent_focusCollision_fork_le_of_uniform
    [∀ t, MeasurableSpace (spec.Range t)] [∀ t, DiscreteMeasurableSpace (spec.Range t)]
    [IsUniformMeasureSpec spec] {main : OracleComp spec α} {i : ι} {n : Nat}
    {path : PFunctor.FreeM.Path main}
    (located : PFunctor.FreeM.Cursor.Located i main path n) (accept : α → Prop) :
    Pr{let view ← ofFreeM located.fork}[view.firstAnswer = view.secondAnswer ∧
      accept (PFunctor.FreeM.output main view.firstPath)] ≤
      (Fintype.card (spec.Range i) : ℝ≥0∞)⁻¹ := by
  simpa only [IsMeasureSpec.toMeasure_eq_uniformOn,
    ProbabilityTheory.uniformOn_univ_apply_singleton] using
    prEvent_focusCollision_fork_le located accept

/-- Observe the outputs of both completions of a fixed typed occurrence. -/
@[expose] def observedForkPair [spec.DecidableEq]
    (main : OracleComp spec α) (i : ι) (n : Nat)
    (observe : α → β) : OracleComp spec (Option (β × β)) :=
  Option.map (fun view =>
    (observe (PFunctor.FreeM.output main view.firstPath),
      observe (PFunctor.FreeM.output main view.secondPath))) <$>
        PFunctor.FreeM.Cursor.locateAndForkAt (P := spec.toPFunctor) i main n

/-- An observed output selects an occurrence only if that occurrence exists on
the corresponding intrinsic execution path. -/
@[expose] def OutputSelectsOccurrence [spec.DecidableEq]
    (main : OracleComp spec α) (i : ι) (n : Nat)
    (observe : α → Option β) (value : β) : Prop :=
  ∀ path : PFunctor.FreeM.Path main,
    observe (PFunctor.FreeM.output main path) = some value →
      (PFunctor.FreeM.Cursor.locateAt? (P := spec.toPFunctor) i main path n).isSome

private theorem splitAtValid_bind_complete_oracleComp [spec.DecidableEq]
    (main : OracleComp spec α) (i : ι) (n : Nat) :
    (Cursor.splitAtValid main i n >>= fun certified => Cursor.complete certified.1) =
      Cursor.withPath main :=
  PFunctor.FreeM.Cursor.splitAtValid_bind_complete i main n

private theorem splitAtValid_bind_completeFork_oracleComp [spec.DecidableEq]
    (main : OracleComp spec α) (i : ι) (n : Nat) :
    (Cursor.splitAtValid main i n >>= fun certified => Cursor.completeFork certified.1) =
      PFunctor.FreeM.Cursor.locateAndForkAt (P := spec.toPFunctor) i main n :=
  (PFunctor.FreeM.Cursor.splitAtValid_bind_completeFork i main n).trans
    (PFunctor.FreeM.Cursor.forkAt_eq_locateAndForkAt i main n)

private theorem map_completeFork_found_oracleComp {main : OracleComp spec α} {i : ι} {n : Nat}
    (occurrence : PFunctor.FreeM.Cursor.Occurrence i main n) {γ : Type}
    (observe : PFunctor.FreeM.Cursor.ForkView i main n → γ) :
    Option.map observe <$> Cursor.completeFork (PFunctor.FreeM.Cursor.Split.found occurrence) =
      (Cursor.completeOccurrence occurrence >>= fun first =>
        (fun second => some (observe { occurrence, first, second })) <$>
          Cursor.completeOccurrence occurrence) :=
  PFunctor.FreeM.Cursor.Split.map_completeFork_found occurrence observe

/-- A certified missing split cannot produce an output selecting its nominal occurrence. -/
lemma ne_some_of_valid_missing [spec.DecidableEq]
    {main : OracleComp spec α} {i : ι} {n : Nat}
    {observe : α → Option β} {value : β}
    (hselect : OutputSelectsOccurrence main i n observe value)
    (path : PFunctor.FreeM.Path main)
    (hvalid : (PFunctor.FreeM.Cursor.Split.missing path :
      PFunctor.FreeM.Cursor.Split i main n).Valid) :
    observe (PFunctor.FreeM.output main path) ≠ some value :=
  fun hvalue => Nat.not_lt_of_ge hvalid
    ((PFunctor.FreeM.Cursor.locateAt?_isSome_iff_lt_occurrences _ _ _ _).mp
      (hselect path hvalue))

/-- Fixed-index observed success squares under two independent completions of the selected
occurrence context. Answer measures need not be uniform. -/
theorem prEvent_sq_le_observedForkPair [spec.DecidableEq]
    [∀ t, MeasurableSpace (spec.Range t)] [∀ t, DiscreteMeasurableSpace (spec.Range t)]
    [IsMeasureSpec spec]
    (main : OracleComp spec α) (i : ι) (n : Nat) (observe : α → Option β) (value : β)
    (hselect : OutputSelectsOccurrence main i n observe value) :
    Pr{let output ← main}[observe output = some value] ^ 2 ≤
      Pr{let pair ← observedForkPair main i n observe}[pair = some (some value, some value)] := by
  let source := Cursor.splitAtValid main i n
  let kernel := fun certified : {split : PFunctor.FreeM.Cursor.Split i main n // split.Valid} ↦
    (observe ∘ PFunctor.FreeM.output main) <$> Cursor.complete certified.1
  have hprogram : observe <$> main = source >>= kernel := by
    simp only [source, kernel, ← map_bind, splitAtValid_bind_complete_oracleComp]
    calc
      _ = observe <$> (PFunctor.FreeM.output main <$> Cursor.withPath main) := by
        rw [Cursor.map_output_withPath]
      _ = _ := by simp only [Functor.map_map, Function.comp_def]
  have hsuccess : Pr{let output ← main}[observe output = some value] =
      Pr{let output ← source >>= kernel}[output = some value] := by
    rw [← hprogram, prEvent_map]
  rw [hsuccess]
  refine (prEvent_bind_sq_le_bind_pair source kernel (· = some value)).trans_eq ?_
  let observeView := fun view : PFunctor.FreeM.Cursor.ForkView i main n ↦
    (observe (PFunctor.FreeM.output main view.firstPath),
      observe (PFunctor.FreeM.output main view.secondPath))
  have hfork : observedForkPair main i n observe =
      source >>= fun certified ↦ Option.map observeView <$> Cursor.completeFork certified.1 := by
    unfold observedForkPair
    rw [← splitAtValid_bind_completeFork_oracleComp, map_bind]
  rw [hfork]
  let pairKernel := fun certified ↦ (do
    let a ← kernel certified
    let b ← kernel certified
    return (a, b))
  have hpair :
      Pr{let x ← source; let a ← kernel x; let b ← kernel x}[a = some value ∧ b = some value] =
        Pr{let pair ← source >>= pairKernel}[pair.1 = some value ∧ pair.2 = some value] := by
    simp only [pairKernel, bind_assoc, pure_bind]
  rw [hpair]
  refine prEvent_bind_congr source pairKernel _ _ _ ?_
  rintro ⟨split, hvalid⟩
  cases split with
  | missing path =>
      have hne := ne_some_of_valid_missing hselect path hvalid
      simp [pairKernel, kernel, Cursor.complete, Cursor.completeFork,
        PFunctor.FreeM.Cursor.Split.complete_missing,
        PFunctor.FreeM.Cursor.Split.completeFork_missing, hne]
  | found occurrence =>
      rw [map_completeFork_found_oracleComp]
      simp only [pairKernel, kernel, Cursor.complete,
        PFunctor.FreeM.Cursor.Split.complete_found,
        PFunctor.FreeM.Cursor.Occurrence.completePath, Cursor.completeOccurrence,
        ofFreeM_map, bind_assoc, pure_bind, bind_map_left,
        Option.some.injEq, Prod.mk.injEq,
        PFunctor.FreeM.Cursor.ForkView.firstPath_mk,
        PFunctor.FreeM.Cursor.ForkView.secondPath_mk,
        observeView, Function.comp_def]

end OracleComp
