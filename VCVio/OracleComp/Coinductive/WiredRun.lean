/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.Coinductive.Machine
import VCVio.OracleComp.Coinductive.Responder

/-!
# Wired Runs of Oracle Machines

This file runs pointed oracle machines against stateful probabilistic responders and states the
adjunction between machine interface wrapping and responder pullback.
-/

universe u

open OracleSpec PFunctor

variable {ι : Type u} {spec : OracleSpec.{u, u} ι} {α β : Type u}

namespace OracleMachine

/-- Run a machine against a stateful responder for at most `k` rounds. -/
noncomputable def wireKRun (M : OracleMachine spec α β) (R : ProbResponder spec)
    (k : ℕ) (p : R.State × M.State) : SPMF (Option β × R.State) :=
  (M.runK R.toQueryImpl k p.2).run p.1

@[simp] theorem wireKRun_zero (M : OracleMachine spec α β) (R : ProbResponder spec)
    (r : R.State) (s : M.State) : M.wireKRun R 0 (r, s) = pure (M.output s, r) := rfl

/-- A halted machine does not query or advance the responder. -/
theorem wireKRun_of_output_eq_some (M : OracleMachine spec α β) (R : ProbResponder spec)
    {s : M.State} {b : β} (hb : M.output s = some b) (k : ℕ) (r : R.State) :
    M.wireKRun R k (r, s) = pure (some b, r) := by
  rw [wireKRun, M.runK_of_output_eq_some R.toQueryImpl hb]
  rfl

/-- One unresolved machine round is one PolyFun-wired strategy step. -/
theorem wireKRun_succ_of_output_eq_none (M : OracleMachine spec α β)
    (R : ProbResponder spec) {s : M.State} (hb : M.output s = none) (k : ℕ)
    (r : R.State) :
    M.wireKRun R (k + 1) (r, s) =
      OracleStrategy.wireKStep M.toDynSystem R (r, s) >>= fun p => M.wireKRun R k p :=
  PointedMachine.runWith_run_succ_of_output_eq_none M R.toQueryImpl hb k r

@[simp] theorem wireKRun_ofHandlerFamily {Γ : Type u} (h : Γ → ProbHandler spec)
    (M : OracleMachine spec α β) (k : ℕ) (s : M.State) (γ : Γ) :
    M.wireKRun (.ofHandlerFamily h) k (γ, s) =
      (fun ob => (ob, γ)) <$> M.runK (h γ) k s := by
  induction k generalizing s with
  | zero =>
    simp only [wireKRun_zero, runK_zero, map_pure]
    rfl
  | succ k ih =>
    cases hb : M.output s with
    | some b =>
      rw [M.wireKRun_of_output_eq_some _ hb, M.runK_of_output_eq_some (h γ) hb, map_pure]
      rfl
    | none =>
      calc
        M.wireKRun (.ofHandlerFamily h) (k + 1) (γ, s) =
            ((fun s' => (γ, s')) <$> OracleStrategy.kleisliStep (h γ) M.toDynSystem s) >>=
              fun p => M.wireKRun (.ofHandlerFamily h) k p := by
          rw [M.wireKRun_succ_of_output_eq_none _ hb,
            OracleStrategy.wireKStep_ofHandlerFamily]
          rfl
        _ = OracleStrategy.kleisliStep (h γ) M.toDynSystem s >>= fun s' =>
            (fun ob => (ob, γ)) <$> M.runK (h γ) k s' := by
          rw [bind_map_left]
          exact bind_congr fun s' => ih s'
        _ = (fun ob => (ob, γ)) <$> M.runK (h γ) (k + 1) s := by
          rw [M.runK_succ_of_output_eq_none' _ hb, map_bind]

variable {ι' : Type u} {spec' : OracleSpec.{u, u} ι'}

/-- Transport a machine along a lens, specialized back to the OracleSpec vocabulary. -/
def wrapIface (w : PFunctor.Lens spec.toPFunctor spec'.toPFunctor)
    (M : OracleMachine spec α β) : OracleMachine spec' α β where
  State := M.State
  expose s := w.toFunA (M.expose s)
  update s a := M.update s (w.toFunB (M.expose s) a)
  init := M.init
  output := M.output

/-- The OracleSpec wrapper is PolyFun's pointed-machine interface transport. -/
theorem wrapIface_eq_wrap (w : PFunctor.Lens spec.toPFunctor spec'.toPFunctor)
    (M : OracleMachine spec α β) : M.wrapIface w = M.wrap w := rfl

/-- Running a machine wrapped along a lens is running it against the pulled-back responder. -/
theorem runK_wrap (w : PFunctor.Lens spec.toPFunctor spec'.toPFunctor)
    (M : OracleMachine spec α β) (R : ProbResponder spec') (k : ℕ) (s : M.State) :
    (M.wrapIface w).runK R.toQueryImpl k s = M.runK (R.pullback w).toQueryImpl k s := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    cases hb : M.output s with
    | some b =>
      rw [M.runK_of_output_eq_some (R.pullback w).toQueryImpl hb]
      exact (M.wrapIface w).runK_of_output_eq_some R.toQueryImpl hb _
    | none =>
      rw [M.runK_succ_of_output_eq_none (R.pullback w).toQueryImpl hb,
        (M.wrapIface w).runK_succ_of_output_eq_none R.toQueryImpl hb]
      simp only [ih]
      simp only [wrapIface, ProbResponder.toQueryImpl_pullback]
      exact (bind_map_left (m := StateT R.State SPMF)
        (fun a => w.toFunB (M.expose s) a) (R.toQueryImpl (w.toFunA (M.expose s)))
        (fun r => M.runK (R.pullback w).toQueryImpl k (M.update s r))).symm

/-- Wired-run form of the machine-wrap/responder-pullback adjunction. -/
theorem wireKRun_wrap (w : PFunctor.Lens spec.toPFunctor spec'.toPFunctor)
    (M : OracleMachine spec α β) (R : ProbResponder spec') (k : ℕ)
    (r : R.State) (s : M.State) :
    (M.wrapIface w).wireKRun R k (r, s) = M.wireKRun (R.pullback w) k (r, s) := by
  rw [wireKRun, wireKRun, runK_wrap]
  rfl

end OracleMachine
