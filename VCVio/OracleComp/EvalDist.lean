/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module
public import VCVio.OracleComp.ReachableWhen
public import VCVio.OracleComp.Support
public import VCVio.OracleComp.EvalDist.Measure
public import VCVio.EvalDist.Defs.Support.Failure
public import VCVio.EvalDist.Monad.Seq
public import VCVio.EvalDist.Instances.OptionT
public import VCVio.EvalDist.PFunctorSupport
public import PolyFun.PFunctor.Free.WP
public import VCVio.OracleComp.SimSemantics.SimulateQ
public import ToMathlib.Data.Set.Functor

/-!
# Evaluation of oracle computations

This module collects the measure semantics of oracle computations
(`VCVio.OracleComp.EvalDist.Measure`) with the support of optional oracle computations: the
support of `guard`, and peelers for the run of an `OptionT` bind.
-/

@[expose] public section

open OracleSpec Option ENNReal

universe u v w

namespace OracleComp

variable {ι ι'} {spec : OracleSpec ι} {spec' : OracleSpec ι'} {α β γ : Type w}

section guard

lemma support_guard {p : Prop} [Decidable p] :
    support (guard p : OptionT (OracleComp spec) Unit) = if p then {()} else ∅ := by
  by_cases hp : p
  · simp [OracleComp.guard_eq, hp]
  · simp only [OracleComp.guard_eq, hp, ↓reduceIte, OptionT.support_def]
    ext x
    simp

end guard

end OracleComp

namespace OptionT

variable {ι : Type} {spec : OracleSpec ι} {α β : Type}

/-- Support-level peeler for an `OptionT`-monadic bind, stated at the underlying
`OracleComp`-level `.run`: every element `y` of the support of the *run* of `mx >>= f` factors
through an intermediate `some a` in `mx`'s run support and a `y` in the run support of `f a`,
unless `mx`'s run can produce `none` (in which case `y` may be that `none`). Companion to
`OptionT.mem_support_bind_mk` for the case where the `OptionT.run` has already been stripped to
the bare underlying computation.

Applies to a hypothesis `y ∈ support oa` whenever `oa` is *definitionally* `(mx >>= f).run`
(the `OptionT.run` is identity), so callers need not respell the full bind term. -/
lemma mem_support_run_bind
    (mx : OptionT (OracleComp spec) α) (f : α → OptionT (OracleComp spec) β) {y : Option β}
    (hy : y ∈ support ((mx >>= f : OptionT (OracleComp spec) β).run)) :
    (none ∈ support mx.run ∧ y = none) ∨
      ∃ a, some a ∈ support mx.run ∧ y ∈ support ((f a).run) := by
  rw [OptionT.run_bind, Option.elimM, mem_support_bind_iff] at hy
  obtain ⟨o, ho, hy⟩ := hy
  cases o with
  | none => exact Or.inl ⟨ho, by simpa using hy⟩
  | some a => exact Or.inr ⟨a, ho, hy⟩

/-- `OptionT.lift`-headed specialization of `mem_support_run_bind`: a `lift`ed (hence
never-failing) first computation `oa` peels cleanly, with the intermediate value living in
`support oa` directly (no `none` branch). -/
lemma mem_support_run_lift_bind
    (oa : OracleComp spec α) (f : α → OptionT (OracleComp spec) β) {y : Option β}
    (hy : y ∈ support ((OptionT.lift oa >>= f : OptionT (OracleComp spec) β).run)) :
    ∃ a, a ∈ support oa ∧ y ∈ support ((f a).run) := by
  rwa [OptionT.run_bind, OptionT.run_lift, Option.elimM, bind_pure_comp, bind_map_left,
    mem_support_bind_iff] at hy

end OptionT
