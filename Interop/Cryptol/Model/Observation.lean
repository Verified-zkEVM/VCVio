/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Model.Adequacy

/-!
# Finite typed observations

Observations demand selected fields, stream positions, or function results.
Their interpretation is continuous and commutes with the syntax they build.
Adequacy therefore applies to finite demands on infinite or higher-order
values, as well as to evaluation of the outer constructor itself.
-/

public section

open OmegaCompletePartialOrder

namespace Interop.Cryptol

/-- A finite path of demands through a typed value. -/
inductive Observation : ClosedTy → ClosedTy → Type where
  | done {a} : Observation a a
  | fst {a b r} (rest : Observation a r) : Observation (.prod a b) r
  | snd {a b r} (rest : Observation b r) : Observation (.prod a b) r
  | index {l a r} (position : Int) (rest : Observation a r) : Observation (.seq l a) r
  | app {a b r} (argument : Expr [] a) (rest : Observation b r) :
      Observation (.arrow a b) r

/-- Build an observation as ordinary closed syntax. -/
@[expose] def Observation.apply {a b : ClosedTy} : Observation a b → Expr [] a → Expr [] b
  | .done, e => e
  | .fst rest, e => rest.apply (.fst e)
  | .snd rest, e => rest.apply (.snd e)
  | .index i rest, e => rest.apply (.index e (.integer i))
  | .app arg rest, e => rest.apply (.app e arg)

/-- Interpret a finite observation by the same continuous demand operations. -/
@[expose] noncomputable def Observation.denote {a b : ClosedTy} :
    Observation a b → (Computation a →𝒄 Computation b)
  | .done => .id
  | .fst rest => rest.denote.comp (Frame.denote .fst)
  | .snd rest => rest.denote.comp (Frame.denote .snd)
  | .index i rest => rest.denote.comp (Frame.denote (.index (.integer i)))
  | .app arg rest => rest.denote.comp (Frame.denote (.app arg))

/-- Demanding a value in syntax commutes with denotation. -/
theorem Observation.denote_apply {a b : ClosedTy} (obs : Observation a b) (e : Expr [] a) :
    (obs.apply e).denote Environment.empty = obs.denote (e.denote Environment.empty) := by
  induction obs with
  | done => rfl
  | fst rest ih => rw [Observation.apply, ih]; rfl
  | snd rest ih => rw [Observation.apply, ih]; rfl
  | index i rest ih => rw [Observation.apply, ih]; rfl
  | app arg rest ih => rw [Observation.apply, ih]; rfl

/-- Finite observations of semantic equals produce the same semantic result. -/
theorem Observation.congr {a b : ClosedTy} (obs : Observation a b) {e e' : Expr [] a}
    (h : e.denote Environment.empty = e'.denote Environment.empty) :
    (obs.apply e).denote Environment.empty = (obs.apply e').denote Environment.empty := by
  rw [obs.denote_apply, obs.denote_apply, h]

/-- Adequacy for errors from finite demands on a lazy value. -/
theorem Observation.adequacy_error {a b : ClosedTy} (obs : Observation a b)
    (e : Expr [] a) (err : EvalError) :
    obs.denote (e.denote Environment.empty) = .error err ↔
      Evaluates (obs.apply e) (.error err) := by
  rw [← obs.denote_apply]
  exact (obs.apply e).adequacy_error err

/-- A divergent observation has no terminating outcome, even if its input
already evaluates to a sequence, tuple, or function constructor. -/
theorem Observation.adequacy_bottom {a b : ClosedTy} (obs : Observation a b) (e : Expr [] a) :
    obs.denote (e.denote Environment.empty) = ⊥ ↔
      ∀ r, ¬ Evaluates (obs.apply e) r := by
  rw [← obs.denote_apply]
  exact (obs.apply e).adequacy_bottom

end Interop.Cryptol
