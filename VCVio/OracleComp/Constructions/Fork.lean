/-
Copyright (c) 2026 Devon Tuma, Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/
import VCVio.EvalDist.Prod
import VCVio.OracleComp.EvalDist
import PolyFun.PFunctor.Free.Cursor.Fork

/-!
# Probability Bounds for Forking Oracle Computations

This file connects PolyFun's typed occurrence forks to `OracleComp` probability.
It packages the conditional-square argument for two independent completions of
one occurrence context, leaving cryptographic reductions to supply only an
output observation and a reachability hypothesis.
-/

open OracleSpec ENNReal

open scoped PFunctor

set_option allowUnsafeReducibility true in
attribute [local reducible] OracleSpec.toPFunctor PFunctor.Idx

namespace OracleComp

variable {ι : Type} {spec : OracleSpec ι} {α β : Type}

namespace Cursor

/-- Execute an intrinsic path through the `OracleComp` abstraction boundary. -/
@[reducible] def withPath (main : OracleComp spec α) :
    OracleComp spec (PFunctor.FreeM.Path main) :=
  ofFreeM (PFunctor.FreeM.withPath (toFreeM main))

/-- Split at an occurrence through the `OracleComp` abstraction boundary. -/
@[reducible] def splitAtValid [spec.DecidableEq] (main : OracleComp spec α)
    (i : ι) (n : Nat) : OracleComp spec
      {split : PFunctor.FreeM.Cursor.Split i main n // split.Valid} :=
  ofFreeM (PFunctor.FreeM.Cursor.splitAtValid i (toFreeM main) n)

/-- Complete one occurrence split through the `OracleComp` abstraction boundary. -/
@[reducible] def complete {main : OracleComp spec α} {i : ι} {n : Nat}
    (split : PFunctor.FreeM.Cursor.Split i main n) :
    OracleComp spec (PFunctor.FreeM.Path main) :=
  ofFreeM split.complete

/-- Complete a fork through the `OracleComp` abstraction boundary. -/
@[reducible] def completeFork {main : OracleComp spec α} {i : ι} {n : Nat}
    (split : PFunctor.FreeM.Cursor.Split i main n) :
    OracleComp spec (Option (PFunctor.FreeM.Cursor.ForkView i main n)) :=
  ofFreeM split.completeFork

/-- Complete an occurrence through the `OracleComp` abstraction boundary. -/
@[reducible] def completeOccurrence {main : OracleComp spec α} {i : ι} {n : Nat}
    (occurrence : PFunctor.FreeM.Cursor.Occurrence i main n) :
    OracleComp spec occurrence.Completion :=
  ofFreeM occurrence.complete

end Cursor

private def pathRun (main : OracleComp spec α) :
    OracleComp spec (PFunctor.FreeM.Path main) :=
  Cursor.withPath main

@[simp] private theorem map_output_pathRun (main : OracleComp spec α) :
    (PFunctor.FreeM.output main <$> pathRun main : OracleComp spec α) = main :=
  PFunctor.FreeM.map_output_withPath main

/-- Observe the outputs of both completions of a fixed typed occurrence. -/
def observedForkPair [spec.DecidableEq] (main : OracleComp spec α) (i : ι) (n : Nat)
    (observe : α → β) : OracleComp spec (Option (β × β)) :=
  Option.map (fun view =>
    (observe (PFunctor.FreeM.output main view.firstPath),
      observe (PFunctor.FreeM.output main view.secondPath))) <$>
        PFunctor.FreeM.Cursor.locateAndForkAt (P := spec.toPFunctor) i main n

/-- An observed output selects an occurrence only if that occurrence exists on
the corresponding intrinsic execution path. -/
def OutputSelectsOccurrence [spec.DecidableEq] (main : OracleComp spec α) (i : ι)
    (n : Nat) (observe : α → Option β) (value : β) : Prop :=
  ∀ path : PFunctor.FreeM.Path main,
    observe (PFunctor.FreeM.output main path) = some value →
      (PFunctor.FreeM.Cursor.locateAt? (P := spec.toPFunctor) i main path n).isSome

private theorem splitAtValid_bind_complete_oracleComp [spec.DecidableEq]
    (main : OracleComp spec α) (i : ι) (n : Nat) :
    (Cursor.splitAtValid main i n >>= fun certified => Cursor.complete certified.1) =
      pathRun main := by
  exact PFunctor.FreeM.Cursor.splitAtValid_bind_complete i main n

private theorem splitAtValid_bind_completeFork_oracleComp [spec.DecidableEq]
    (main : OracleComp spec α) (i : ι) (n : Nat) :
    (Cursor.splitAtValid main i n >>= fun certified => Cursor.completeFork certified.1) =
        PFunctor.FreeM.Cursor.locateAndForkAt (P := spec.toPFunctor) i main n := by
  exact (PFunctor.FreeM.Cursor.splitAtValid_bind_completeFork i main n).trans
    (PFunctor.FreeM.Cursor.forkAt_eq_locateAndForkAt i main n)

private theorem map_completeFork_found_oracleComp
    {main : OracleComp spec α} {i : ι} {n : Nat}
    (occurrence : PFunctor.FreeM.Cursor.Occurrence i main n) {γ : Type}
    (observe : PFunctor.FreeM.Cursor.ForkView i main n → γ) :
    Option.map observe <$> Cursor.completeFork
        (PFunctor.FreeM.Cursor.Split.found occurrence) =
      (Cursor.completeOccurrence occurrence >>= fun first =>
        (fun second => some (observe {
          occurrence := occurrence
          first := first
          second := second })) <$>
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
    observe (PFunctor.FreeM.output main path) ≠ some value := by
  intro hvalue
  have hsome := hselect path hvalue
  rw [PFunctor.FreeM.Cursor.locateAt?_isSome_iff_lt_occurrences] at hsome
  exact (Nat.not_lt_of_ge hvalid) hsome

/-- Fixed-index observed success squares under two independent completions of
the selected occurrence context. -/
theorem sq_probOutput_map_le_observedForkPair [spec.DecidableEq] [IsUniformSpec spec]
    (main : OracleComp spec α) (i : ι) (n : Nat)
    (observe : α → Option β) (value : β)
    (hselect : OutputSelectsOccurrence main i n observe value) :
    Pr[= value | observe <$> main] ^ 2 ≤
      Pr[= (some (some value, some value) : Option (Option β × Option β)) |
        observedForkPair main i n observe] := by
  classical
  let domainDecEq : DecidableEq spec.Domain := inferInstance
  let rangeDecEq : ∀ j, DecidableEq (spec.Range j) := fun _ => inferInstance
  letI : DecidableEq spec.Domain := domainDecEq
  letI (j : spec.Domain) : DecidableEq (spec.Range j) := rangeDecEq j
  set y : Option β := some value
  let splitComp : OracleComp spec
      {split : PFunctor.FreeM.Cursor.Split i main n // split.Valid} :=
    Cursor.splitAtValid main i n
  let finish : PFunctor.FreeM.Path main → OracleComp spec (Option β) :=
    fun path => pure (observe (PFunctor.FreeM.output main path))
  let kernel : {split : PFunctor.FreeM.Cursor.Split i main n // split.Valid} →
      OracleComp spec (Option β) := fun certified =>
    Cursor.complete certified.1 >>= finish
  have hprogram : (observe <$> main : OracleComp spec (Option β)) = splitComp >>= kernel := by
    simp only [splitComp, kernel]
    rw [← bind_assoc, splitAtValid_bind_complete_oracleComp]
    calc
      observe <$> main = observe <$>
          (PFunctor.FreeM.output main <$> pathRun main) := by
        rw [map_output_pathRun]
      _ = (observe ∘ PFunctor.FreeM.output main) <$>
          pathRun main := by
        simp only [Functor.map_map, Function.comp_def]
      _ = pathRun main >>= finish := by
        simp [finish, Function.comp_def]
  rw [hprogram]
  refine (sq_probOutput_bind_le_probOutput_bind_prod splitComp kernel y).trans_eq ?_
  let observeView : PFunctor.FreeM.Cursor.ForkView i main n → Option β × Option β :=
    fun view =>
      (observe (PFunctor.FreeM.output main view.firstPath),
        observe (PFunctor.FreeM.output main view.secondPath))
  have hpair : observedForkPair main i n observe =
      splitComp >>= fun certified => Option.map observeView <$>
        Cursor.completeFork certified.1 := by
    unfold observedForkPair
    rw [← splitAtValid_bind_completeFork_oracleComp, map_bind]
  rw [hpair, probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
  refine tsum_congr fun certified => congrArg
    (fun z => Pr[= certified | splitComp] * z) ?_
  rcases certified with ⟨split, hvalid⟩
  cases split with
  | missing path =>
      have hne := ne_some_of_valid_missing hselect path hvalid
      have hne' : y ≠ observe (PFunctor.FreeM.output main path) := by
        simpa [y] using Ne.symm hne
      symm
      change Pr[= some (y, y) |
          Option.map observeView <$> (pure none : OracleComp spec _)] =
        Pr[= (y, y) | do
          let a ← kernel ⟨.missing path, hvalid⟩
          let b ← kernel ⟨.missing path, hvalid⟩
          pure (a, b)]
      have hkernelMissing : kernel ⟨.missing path, hvalid⟩ =
          (pure (observe (PFunctor.FreeM.output main path)) : OracleComp spec (Option β)) := by
        rfl
      rw [hkernelMissing]
      simp [hne']
  | found occurrence =>
      let completion : OracleComp spec occurrence.Completion :=
        Cursor.completeOccurrence occurrence
      let observeCompletion : occurrence.Completion → Option β := fun completed =>
        observe (PFunctor.FreeM.output main completed.path)
      symm
      change Pr[= some (y, y) | Option.map observeView <$>
          Cursor.completeFork (PFunctor.FreeM.Cursor.Split.found occurrence)] =
        Pr[= (y, y) | do
          let a ← kernel ⟨.found occurrence, hvalid⟩
          let b ← kernel ⟨.found occurrence, hvalid⟩
          pure (a, b)]
      rw [map_completeFork_found_oracleComp]
      change Pr[= some (y, y) | completion >>= fun first =>
          (fun second => some (observeCompletion first, observeCompletion second)) <$>
            completion] = _
      have hcompletionPair : (completion >>= fun first =>
          (fun second => some (observeCompletion first, observeCompletion second)) <$>
            completion) = some <$> (do
            let first ← completion
            let second ← completion
            pure (observeCompletion first, observeCompletion second) :
              OracleComp spec _) := by
        simp [monad_norm]
      rw [hcompletionPair]
      rw [probOutput_some_map_some, probOutput_bind_bind_prod_mk_eq_mul']
      rw [probOutput_bind_bind_prod_mk_eq_mul']
      have hkernel : (observeCompletion <$> completion : OracleComp spec _) =
          kernel ⟨.found occurrence, hvalid⟩ := by
        change PFunctor.FreeM.map observeCompletion occurrence.complete =
          occurrence.completePath >>= finish
        have hfinish : finish = pure ∘ (observe ∘ PFunctor.FreeM.output main) := by
          funext path
          rfl
        have hcomplete : occurrence.completePath >>= finish =
            (observe ∘ PFunctor.FreeM.output main) <$> occurrence.completePath := by
          rw [hfinish]
          exact bind_pure_comp _ _
        rw [hcomplete]
        change PFunctor.FreeM.map observeCompletion occurrence.complete =
          PFunctor.FreeM.map (observe ∘ PFunctor.FreeM.output main)
            (PFunctor.FreeM.map
              PFunctor.FreeM.Cursor.Occurrence.Completion.path occurrence.complete)
        rw [← PFunctor.FreeM.comp_map]
        rfl
      rw [hkernel]
      have hidFun : (fun a : Option β => a) = id := rfl
      have hid : (fun a : Option β => a) <$>
          kernel ⟨.found occurrence, hvalid⟩ = kernel ⟨.found occurrence, hvalid⟩ := by
        rw [hidFun, id_map]
      rw [hid]

end OracleComp
