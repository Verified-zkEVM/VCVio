/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.Coinductive.DynSystem
import VCVio.OracleComp.SimSemantics.StateT.Basic
import PolyFun.PFunctor.Dynamical.Game

/-!
# Probabilistic Responders for Oracle Strategies

A `ProbResponder spec` bundles PolyFun's stateful-handler presentation of an effectful Mealy
machine, specialized to `SPMF` and the polynomial interface of an `OracleSpec`. Its wired strategy
runs are the `SPMF` specialization of PolyFun's generic `DynSystem.stepWith` and
`DynSystem.iterWith`.
-/

universe u

open OracleSpec

variable {ι : Type u} {spec : OracleSpec.{u, u} ι} {S : Type u}

/-- A stateful probabilistic responder for an oracle interface, as an existentially bundled
PolyFun handler in the `StateT State SPMF` Kleisli category. -/
structure ProbResponder (spec : OracleSpec.{u, u} ι) where
  /-- Private responder state. -/
  State : Type u
  /-- PolyFun handler jointly producing an answer and successor state. -/
  handler : PFunctor.Handler (StateT State SPMF) spec.toPFunctor

namespace ProbResponder

/-- Read a responder as a handler in the state monad. -/
def toQueryImpl (R : ProbResponder spec) : QueryImpl spec (StateT R.State SPMF) :=
  R.handler

/-- Run the responder's PolyFun handler at a state and query. -/
def answer (R : ProbResponder spec) (s : R.State) (t : spec.Domain) :
    SPMF (spec.Range t × R.State) :=
  R.handler t s

/-- Bundle a stateful `SPMF` handler as a responder. -/
def ofQueryImpl {σ : Type u} (impl : QueryImpl spec (StateT σ SPMF)) : ProbResponder spec where
  State := σ
  handler := impl

@[simp] theorem toQueryImpl_ofQueryImpl {σ : Type u}
    (impl : QueryImpl spec (StateT σ SPMF)) : (ofQueryImpl impl).toQueryImpl = impl := rfl

@[simp] theorem ofQueryImpl_toQueryImpl (R : ProbResponder spec) :
    ofQueryImpl R.toQueryImpl = R := rfl

/-- A family of memoryless handlers indexed by state that remains constant during a run. -/
noncomputable def ofHandlerFamily {Γ : Type u} (h : Γ → ProbHandler spec) :
    ProbResponder spec where
  State := Γ
  handler t γ := (fun r => (r, γ)) <$> h γ t

@[simp] theorem ofHandlerFamily_state {Γ : Type u} (h : Γ → ProbHandler spec) :
    (ofHandlerFamily h).State = Γ := rfl

/-- A memoryless handler as a trivial-state responder. -/
noncomputable def ofHandler (H : ProbHandler spec) : ProbResponder spec :=
  ofHandlerFamily fun _ : PUnit => H

/-- Lift a `ProbComp` stateful handler through evaluation semantics. -/
noncomputable def ofStateQueryImpl {ι₀ : Type} {spec₀ : OracleSpec.{0, 0} ι₀}
    {σ : Type} (impl : QueryImpl spec₀ (StateT σ ProbComp)) : ProbResponder spec₀ where
  State := σ
  handler t := StateT.mapHom (MonadHom.ofLift ProbComp SPMF) (impl t)

@[simp] theorem ofStateQueryImpl_state {ι₀ : Type} {spec₀ : OracleSpec.{0, 0} ι₀}
    {σ : Type} (impl : QueryImpl spec₀ (StateT σ ProbComp)) :
    (ofStateQueryImpl impl).State = σ := rfl

/-- Evaluation-distribution naturality for a stateful handler. This is PolyFun's stateful
naturality theorem for the universal fold, rather than a new induction on `OracleComp`. -/
theorem run_simulateQ_toQueryImpl_ofStateQueryImpl {ι₀ : Type}
    {spec₀ : OracleSpec.{0, 0} ι₀} {σ α : Type}
    (impl : QueryImpl spec₀ (StateT σ ProbComp)) (oa : OracleComp spec₀ α) (s : σ) :
    (simulateQ (ofStateQueryImpl impl).toQueryImpl oa).run s =
      𝒟[(simulateQ impl oa).run s] := by
  exact PFunctor.FreeM.run_liftM_mapHom (MonadHom.ofLift ProbComp SPMF) impl oa s

/-- Embed an actual PolyFun deterministic responder into the probabilistic Kleisli model. The
Mealy presentation comes from `Responder.toStateHandler`; only its effects are lifted to `SPMF`. -/
noncomputable def ofResponder {σ : Type u}
    (R : PFunctor.Responder σ spec.toPFunctor) : ProbResponder spec where
  State := σ
  handler t := StateT.mapHom (MonadHom.pure SPMF) (R.toStateHandler t)

@[simp] theorem ofResponder_state {σ : Type u}
    (R : PFunctor.Responder σ spec.toPFunctor) : (ofResponder R).State = σ := rfl

/-- Pull a responder back along an interface lens. -/
noncomputable def pullback {ι' : Type u} {spec' : OracleSpec.{u, u} ι'}
    (w : PFunctor.Lens spec.toPFunctor spec'.toPFunctor) (R : ProbResponder spec') :
    ProbResponder spec where
  State := R.State
  handler t s := (fun q => (w.toFunB t q.1, q.2)) <$> R.handler (w.toFunA t) s

@[simp] theorem toQueryImpl_pullback {ι' : Type u} {spec' : OracleSpec.{u, u} ι'}
    (w : PFunctor.Lens spec.toPFunctor spec'.toPFunctor) (R : ProbResponder spec')
    (t : spec.Domain) :
    (pullback w R).toQueryImpl t =
      (fun a => w.toFunB t a) <$> R.toQueryImpl (w.toFunA t) := by
  funext s
  rfl

end ProbResponder

namespace OracleStrategy

/-- One PolyFun-wired step against a stateful probabilistic responder. -/
noncomputable def wireKStep (A : OracleStrategy S spec) (R : ProbResponder spec) :
    R.State × S → SPMF (R.State × S) :=
  PFunctor.DynSystem.stepWith R.toQueryImpl A

@[simp] theorem wireKStep_apply (A : OracleStrategy S spec) (R : ProbResponder spec)
    (p : R.State × S) :
    wireKStep A R p =
      (fun q => (q.2, A.update p.2 q.1)) <$> R.handler (A.expose p.2) p.1 := rfl

/-- The PolyFun-wired finite run against a responder. -/
noncomputable def wireKIterate (A : OracleStrategy S spec) (R : ProbResponder spec) :
    ℕ → R.State × S → SPMF (R.State × S) :=
  PFunctor.DynSystem.iterWith R.toQueryImpl A

@[simp] theorem wireKIterate_zero (A : OracleStrategy S spec) (R : ProbResponder spec)
    (p : R.State × S) : wireKIterate A R 0 p = pure p := rfl

theorem wireKIterate_succ (A : OracleStrategy S spec) (R : ProbResponder spec)
    (n : ℕ) (p : R.State × S) :
    wireKIterate A R (n + 1) p = wireKStep A R p >>= wireKIterate A R n := rfl

/-- The probabilistic embedding of a PolyFun responder wires exactly as its deterministic closed
game, wrapped in `SPMF.pure`. -/
@[simp] theorem wireKStep_ofResponder {σ : Type u}
    (R : PFunctor.Responder σ spec.toPFunctor) (A : OracleStrategy S spec) (p : σ × S) :
    wireKStep A (ProbResponder.ofResponder R) p =
      pure ((PFunctor.DynSystem.closedGame R A).step p) := by
  change (fun dt : spec.Range (A.expose p.2) × σ => (dt.2, A.update p.2 dt.1)) <$>
      pure (R.answer p.1 (A.expose p.2), R.next p.1 (A.expose p.2)) = _
  rw [map_pure]
  rfl

@[simp] theorem wireKStep_ofHandlerFamily {Γ : Type u} (h : Γ → ProbHandler spec)
    (A : OracleStrategy S spec) (p : Γ × S) :
    wireKStep A (ProbResponder.ofHandlerFamily h) p =
      (fun s' => (p.1, s')) <$> kleisliStep (h p.1) A p.2 := by
  simp only [wireKStep_apply, ProbResponder.ofHandlerFamily, kleisliStep, Functor.map_map]

@[simp] theorem wireKIterate_ofHandlerFamily {Γ : Type u} (h : Γ → ProbHandler spec)
    (A : OracleStrategy S spec) (n : ℕ) (p : Γ × S) :
    wireKIterate A (ProbResponder.ofHandlerFamily h) n p =
      (fun s' => (p.1, s')) <$> kleisliIterate (h p.1) A n p.2 := by
  induction n generalizing p with
  | zero =>
    simp only [wireKIterate_zero, kleisliIterate, map_pure]
    rfl
  | succ n ih =>
    calc
      wireKIterate A (ProbResponder.ofHandlerFamily h) (n + 1) p =
          ((fun s' => (p.1, s')) <$> kleisliStep (h p.1) A p.2) >>=
            wireKIterate A (ProbResponder.ofHandlerFamily h) n := by
        rw [wireKIterate_succ, wireKStep_ofHandlerFamily]
        rfl
      _ = kleisliStep (h p.1) A p.2 >>= fun s' =>
          wireKIterate A (ProbResponder.ofHandlerFamily h) n (p.1, s') := by
        rw [map_eq_bind_pure_comp, bind_assoc]
        exact congrArg (kleisliStep (h p.1) A p.2 >>= ·)
          (funext fun s' => by rw [Function.comp_apply, pure_bind]; rfl)
      _ = kleisliStep (h p.1) A p.2 >>= fun s' =>
          (fun s'' => (p.1, s'')) <$> kleisliIterate (h p.1) A n s' :=
        congrArg (kleisliStep (h p.1) A p.2 >>= ·)
          (funext fun s' => ih (p.1, s'))
      _ = (fun s' => (p.1, s')) <$> kleisliIterate (h p.1) A (n + 1) p.2 := by
        rw [kleisliIterate]
        simp only [map_eq_bind_pure_comp, bind_assoc]

end OracleStrategy
