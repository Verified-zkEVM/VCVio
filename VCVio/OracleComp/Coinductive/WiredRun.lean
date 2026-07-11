/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.Coinductive.WireK
import VCVio.OracleComp.Coinductive.PolyTime

/-!
# Wired Machine Runs: Fuelled Machines Against Stateful Responders

`OracleMachine.wireKRun` runs a machine adversary against a stateful probabilistic
responder (`ProbResponder`): the eval-wired tensor system run in the Kleisli category
of `SPMF`, with the machine's pointed early-stopping readout. Definitionally it is
`OracleMachine.runK` at `m := StateT R.State SPMF` fed the responder's handler, `.run`
from the responder state (`wireKRun_eq_runK_run`). The responder state comes first in
the input pair, matching `OracleStrategy.wireKStep`; the output pair is
`(readout, final responder state)` in `StateT.run` order, value first.

The step theory is inherited from PolyFun's generic parents rather than re-proven: the
zero-fuel and halted-state laws come from `PFunctor.PointedMachine.runWith`
(`wireKRun_zero`, `wireKRun_of_output_eq_some`), and the unresolved-state unfolding
`wireKRun_succ_of_output_eq_none` is the machine-vs-responder step law
`PFunctor.PointedMachine.runWith_run_succ_of_output_eq_none` at `m := SPMF`, with the
step expressed through `OracleStrategy.wireKStep` of the machine's dynamical core.
VCVio contributes the `SPMF` semantics; the constant-state collapse
`wireKRun_ofHandlerFamily` recovers the memoryless run `OracleMachine.runK` against the
selected handler.

`wireKRun` is deliberately *not* an image of `OracleStrategy.wireKIterate` in general:
early stopping matters. Against a stateful responder, running past the readout would
keep advancing the responder's state — and, against lossy responders, shed mass — so
the early-stopping run and the fixed-fuel iterate genuinely differ on machines that
halt before the fuel is exhausted.

The bundled-adversary corollary `MachineAdversary.exec_run_eq_wireKRun` identifies the
security-game execution `MachineAdversary.exec` against a responder's handler with the
wired run at the adversary's round budget, definitionally: game statements about
machine adversaries against stateful challengers are statements about wired runs.
-/

universe u

open OracleSpec PFunctor

section WiredRun

variable {ι : Type u} {spec : OracleSpec.{u, u} ι} {α β : Type u}

namespace OracleMachine

/-! ## The wired run -/

/-- The fuelled run of a machine against a stateful responder: the machine's
monad-parametric run `runK` at `m := StateT R.State SPMF`, fed the responder's handler
and run from the responder state. Input pair is responder-state-first (matching
`OracleStrategy.wireKStep`); output pair is `(readout, final responder state)` in
`StateT.run` order. Early stopping at the first `some` readout is inherited from
`runK`. -/
noncomputable def wireKRun (M : OracleMachine spec α β) (R : ProbResponder spec)
    (k : ℕ) (p : R.State × M.State) : SPMF (Option β × R.State) :=
  (M.runK R.toQueryImpl k p.2).run p.1

/-- Regression canary: the wired run is definitionally the stateful `runK` in
`StateT.run` form. -/
theorem wireKRun_eq_runK_run (M : OracleMachine spec α β) (R : ProbResponder spec)
    (k : ℕ) (r : R.State) (s : M.State) :
    M.wireKRun R k (r, s) = (M.runK R.toQueryImpl k s).run r := rfl

@[simp] theorem wireKRun_zero (M : OracleMachine spec α β) (R : ProbResponder spec)
    (r : R.State) (s : M.State) : M.wireKRun R 0 (r, s) = pure (M.output s, r) := rfl

/-- A halted machine's wired run is Dirac on its readout and the unchanged responder
state, at every fuel. -/
theorem wireKRun_of_output_eq_some (M : OracleMachine spec α β) (R : ProbResponder spec)
    {s : M.State} {b : β} (hb : M.output s = some b) (k : ℕ) (r : R.State) :
    M.wireKRun R k (r, s) = pure (some b, r) := by
  rw [wireKRun_eq_runK_run, M.runK_of_output_eq_some R.toQueryImpl hb k]
  rfl

/-- **The wired step law**: on an unresolved state, one unit of fuel of the wired run
is one `OracleStrategy.wireKStep` of the machine's dynamical core, bound into the rest
of the run — the upstream machine-vs-responder step law
`PFunctor.PointedMachine.runWith_run_succ_of_output_eq_none` at `m := SPMF`. -/
theorem wireKRun_succ_of_output_eq_none (M : OracleMachine spec α β)
    (R : ProbResponder spec) {s : M.State} (hb : M.output s = none) (k : ℕ)
    (r : R.State) :
    M.wireKRun R (k + 1) (r, s) =
      OracleStrategy.wireKStep M.toDynSystem R (r, s) >>= fun p => M.wireKRun R k p :=
  PointedMachine.runWith_run_succ_of_output_eq_none M R.toQueryImpl hb k r

/-! ## Memoryless recovery -/

/-- Against a constant-state responder the wired run is the memoryless machine run
against the selected handler, with the setup carried along unchanged: the machine-run
form of `OracleStrategy.wireKIterate_ofHandlerFamily`. -/
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
      rw [M.wireKRun_of_output_eq_some _ hb, M.runK_of_output_eq_some (h γ) hb,
        map_pure]
      rfl
    | none =>
      calc M.wireKRun (.ofHandlerFamily h) (k + 1) (γ, s)
          = ((fun s' => (γ, s')) <$> OracleStrategy.kleisliStep (h γ) M.toDynSystem s) >>=
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

/-! ## Interface wrapping: reductions as lenses

Installing an interface translation on a machine adversary is literal lens composition,
and it is *adjoint* to pulling the responder back along the same lens: wrapping the
adversary forward equals pulling the challenger's responder back. This is the run-level
combinator behind same-interface security reductions (`OracleStrategy.reduce` is the
sub-spec special case). -/

variable {ι' : Type u} {spec' : OracleSpec.{u, u} ι'}

/-- Install an interface translation on a machine along a lens `w : spec ⇆ spec'`: the
machine speaks `spec` internally; the wrapper exposes each query forward through `w` and
feeds each answer back, so the result speaks `spec'`, with `init`/`output` threaded
unchanged. The pointed re-cut of `PFunctor.DynSystem.wrap w`, and the machine-level
generalization of `OracleStrategy.reduce` (the sub-spec inclusion special case). -/
def wrapIface (w : PFunctor.Lens spec.toPFunctor spec'.toPFunctor)
    (M : OracleMachine spec α β) : OracleMachine spec' α β where
  State := M.State
  expose s := w.toFunA (M.expose s)
  update s a := M.update s (w.toFunB (M.expose s) a)
  init := M.init
  output := M.output

@[simp] theorem wrapIface_output (w : PFunctor.Lens spec.toPFunctor spec'.toPFunctor)
    (M : OracleMachine spec α β) (s : M.State) : (M.wrapIface w).output s = M.output s :=
  rfl

@[simp] theorem wrapIface_init (w : PFunctor.Lens spec.toPFunctor spec'.toPFunctor)
    (M : OracleMachine spec α β) (x : α) : (M.wrapIface w).init x = M.init x := rfl

/-- **The run-level interface-wrapping adjunction**: running the wrapped machine against a
`spec'`-responder equals running the original machine against the responder pulled back
along `w`. Wrapping the adversary forward is pulling the responder back — proved by fuel
induction through the handler-level `ProbResponder.toQueryImpl_pullback`. -/
theorem runK_wrapIface (w : PFunctor.Lens spec.toPFunctor spec'.toPFunctor)
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
      have h0 : (M.wrapIface w).output s = none := hb
      rw [M.runK_succ_of_output_eq_none (R.pullback w).toQueryImpl hb,
        (M.wrapIface w).runK_succ_of_output_eq_none R.toQueryImpl h0]
      simp only [ih]
      simp only [wrapIface, ProbResponder.toQueryImpl_pullback]
      exact (bind_map_left (m := StateT R.State SPMF)
        (fun a => w.toFunB (M.expose s) a) (R.toQueryImpl (w.toFunA (M.expose s)))
        (fun r => M.runK (R.pullback w).toQueryImpl k (M.update s r))).symm

/-- **The wired-run interface-wrapping adjunction**: the `wireKRun` form of
`runK_wrapIface`. This is the workhorse of same-interface reductions at the game level. -/
theorem wireKRun_wrapIface (w : PFunctor.Lens spec.toPFunctor spec'.toPFunctor)
    (M : OracleMachine spec α β) (R : ProbResponder spec') (k : ℕ) (r : R.State)
    (s : M.State) :
    (M.wrapIface w).wireKRun R k (r, s) = M.wireKRun (R.pullback w) k (r, s) := by
  rw [wireKRun_eq_runK_run, wireKRun_eq_runK_run, runK_wrapIface]
  rfl

end OracleMachine

end WiredRun

/-! ## Bundled adversaries: game execution is the wired run -/

namespace MachineAdversary

variable {ι : ℕ → Type} [∀ n, DecidableEq (ι n)]
  {spec : (n : ℕ) → OracleSpec.{0, 0} (ι n)} {α β : ℕ → Type}
  {bd : BoundaryData spec α β}

/-- **Game-execution bridge**: a bundled polynomial-time adversary's security-game
execution against a responder's stateful handler is the machine's wired run at the
adversary's round budget — definitionally. Game statements phrased through
`MachineAdversary.exec` at `m := StateT R.State SPMF` are statements about
`OracleMachine.wireKRun`. -/
theorem exec_run_eq_wireKRun (D : MachineAdversary bd) (n : ℕ)
    (R : ProbResponder (spec n)) (x : α n) (r : R.State) :
    (D.exec n R.toQueryImpl x).run r =
      (D.M n).wireKRun R (D.steps.eval n) (r, (D.M n).init x) := rfl

end MachineAdversary
