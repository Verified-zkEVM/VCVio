/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import PolyFun.Control.Monad.Measure.OptionT
public import VCVio.EvalDist.Defs.Measure.Core
public import ToMathlib.MeasureTheory.Measure.GiryMonad
public import VCVio.EvalDist.ProbabilityBounds
public import PolyFun.Control.Monad.Measure.Failure
public import VCVio.EvalDist.ProbabilityNotation
public import ToMathlib.Control.OptionT

/-!
# Events of optional computations

Successful-output semantics turns a sampled guard into a condition on the sampled value.
The intermediate measurable space is internal to the observation law. Wrapped computations are
observed through their present values, and sequencing a lossless prefix with continuations that
succeed on its reachable outputs preserves probability-one events.
-/

public section

open MeasureTheory

universe v

namespace OptionT

section sequencing

variable {m : Type → Type v} [Monad m] [LawfulMonad m] {α β : Type}

/-- A wrapped bind is a lifted prefix followed by the wrapped continuations. -/
theorem mk_bind_eq_lift_bind (mx : m α) (f : α → m (Option β)) :
    OptionT.mk (mx >>= f) = (OptionT.lift mx >>= fun a ↦ OptionT.mk (f a) : OptionT m β) := by
  simp [OptionT.ext_iff]

variable [MonadAttach m] [ExactMonadAttach m]

/-- Reachable outputs of a lifted computation are reachable in the computation. -/
theorem mem_support_of_mem_support_lift {mx : m α} {a : α}
    (ha : a ∈ support (OptionT.lift mx)) : a ∈ support mx := by
  rw [MonadAttach.mem_support, MonadAttach.OptionT.canReturn_iff, OptionT.run_lift,
    MonadAttach.mem_support_bind] at ha
  obtain ⟨a', ha', h⟩ := ha
  rw [MonadAttach.mem_support_pure] at h
  exact Option.some_injective _ h ▸ ha'

variable [EvalDistSemantics m] [LawfulEvalDistSemantics m]

/-- A lossless prefix followed by continuations that each satisfy an event with probability one
on the prefix's reachable outputs satisfies the event with probability one. -/
theorem prEvent_mk_bind_eq_one_of_support (mx : m α) (hmx : Pr{let _ ← mx}[True] = 1)
    (f : α → m (Option β)) (p : β → Prop)
    (h : ∀ a ∈ support mx, Pr{let y ← OptionT.mk (f a)}[p y] = 1) :
    Pr{let y ← OptionT.mk (mx >>= f)}[p y] = 1 := by
  rw [mk_bind_eq_lift_bind]
  refine le_antisymm (prEvent_le_one _) ?_
  refine le_prEvent_bind_of_forall_le_of_support (OptionT.lift mx) ?_ _ p ?_
  · rwa [prEvent_lift]
  · exact fun a ha ↦ (h a (mem_support_of_mem_support_lift ha)).ge

/-- An upper bound on the wrapped continuation event over reachable prefixes. -/
theorem prEvent_mk_bind_le_of_forall_le (mx : m α) (f : α → m (Option β)) (q : β → Prop)
    {ε : ENNReal} (h : ∀ a ∈ support mx, Pr{let y ← OptionT.mk (f a)}[q y] ≤ ε) :
    Pr{let y ← OptionT.mk (mx >>= f)}[q y] ≤ ε := by
  rw [mk_bind_eq_lift_bind]
  exact prEvent_bind_le_of_forall_le_of_support (OptionT.lift mx) _ q fun a ha ↦
    h a (mem_support_of_mem_support_lift ha)

end sequencing

end OptionT
