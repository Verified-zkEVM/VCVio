/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.Coinductive.Machine
import VCVio.OracleComp.Coinductive.Responder
import PolyFun.PFunctor.Handler.Normalization

/-!
# Wired Machine Runs: Fuelled Machines Against Stateful Responders

`OracleMachine.runAgainst` runs a machine adversary against a stateful probabilistic
responder (`ProbResponder`): the machine's monad-parametric run `runWith` at
`m := StateT R.State SPMF`, fed the responder's handler and run from the responder
state (`runAgainst_eq_runWith_run` is the definitional canary). The responder state
comes first in the input pair, matching `OracleStrategy.stepAgainst`; the output pair
is `(readout, final responder state)` in `StateT.run` order, value first.

The step theory is inherited from PolyFun's `DynComputation` bounded-execution
lemmas rather than re-proven: a returned state is Dirac on its value at every fuel
(`runAgainst_of_view_return`, from `runWith_return`), zero fuel cuts an unresolved
query off (`runAgainst_zero_of_view_query`, from `runWith_query_zero`), and the wired
step law `runAgainst_succ_of_view_query` is `runWith_query_succ_stateT` read at
`m := SPMF`: one unit of fuel jointly samples the answer and next responder state,
then continues. VCVio contributes the `SPMF` semantics; the constant-state collapse
`runAgainst_ofHandlerFamily` recovers the memoryless run against the selected handler.

`runAgainst` is deliberately *not* an image of `OracleStrategy.iterateAgainst` in
general: early stopping matters. Against a stateful responder, running past the
readout would keep advancing the responder's state — and, against lossy responders,
shed mass — so the early-stopping run and the fixed-fuel iterate genuinely differ on
machines that halt before the fuel is exhausted.

Interface wrapping needs no bespoke machine transport: `DynComputation.wrap` moves a
machine along a lens, and the **interface-wrapping adjunction** `runWith_wrap` /
`runAgainst_wrap` states that wrapping the adversary forward equals pulling the
responder back (`ProbResponder.pullback`) along the same lens. This is the run-level
combinator behind same-interface security reductions (`OracleStrategy.reduce` is the
sub-spec special case).
-/

universe u

open OracleSpec PFunctor PFunctor.DynSystem

namespace OracleComp.OracleMachine

variable {ι : Type u} {spec : OracleSpec.{u, u} ι} {α β : Type u}

/-! ## The wired run -/

/-- The fuelled run of a machine against a stateful responder: the machine's
monad-parametric run `runWith` at `m := StateT R.State SPMF`, fed the responder's
handler and run from the responder state. Input pair is responder-state-first
(matching `OracleStrategy.stepAgainst`); output pair is `(readout, final responder
state)` in `StateT.run` order. Early stopping at the first returned value is
inherited from `runWith`. -/
noncomputable def runAgainst (M : OracleMachine spec α β) (R : ProbResponder spec)
    (k : ℕ) (p : R.State × M.State) : SPMF (Option β × R.State) :=
  (M.runWith R.toQueryImpl k p.2).run p.1

/-- Regression canary: the wired run is definitionally the stateful `runWith` in
`StateT.run` form. -/
theorem runAgainst_eq_runWith_run (M : OracleMachine spec α β) (R : ProbResponder spec)
    (k : ℕ) (r : R.State) (s : M.State) :
    M.runAgainst R k (r, s) = (M.runWith R.toQueryImpl k s).run r := rfl

/-- A returned machine state's wired run is Dirac on its value and the unchanged
responder state, at every fuel. -/
theorem runAgainst_of_view_return (M : OracleMachine spec α β) (R : ProbResponder spec)
    {s : M.State} {b : β} (hview : M.view s = Sum.inl b) (k : ℕ) (r : R.State) :
    M.runAgainst R k (r, s) = pure (some b, r) := by
  rw [runAgainst_eq_runWith_run, M.runWith_return R.toQueryImpl k s b hview]
  simp only [handler_nf]

/-- Zero fuel cuts an unresolved query off with `none`, leaving the responder state
unchanged. -/
theorem runAgainst_zero_of_view_query (M : OracleMachine spec α β)
    (R : ProbResponder spec) {s : M.State} {t : spec.Domain}
    {next : spec.Range t → M.State} (hview : M.view s = Sum.inr ⟨t, next⟩)
    (r : R.State) : M.runAgainst R 0 (r, s) = pure (none, r) := by
  rw [runAgainst_eq_runWith_run, M.runWith_query_zero R.toQueryImpl s t next hview]
  simp only [handler_nf]

/-- **The wired step law**: on a querying state, one unit of fuel of the wired run
jointly samples the responder's answer and next state, then continues — PolyFun's
`runWith_query_succ_stateT` read at `m := SPMF`. -/
theorem runAgainst_succ_of_view_query (M : OracleMachine spec α β)
    (R : ProbResponder spec) {s : M.State} {t : spec.Domain}
    {next : spec.Range t → M.State} (hview : M.view s = Sum.inr ⟨t, next⟩)
    (k : ℕ) (r : R.State) :
    M.runAgainst R (k + 1) (r, s) =
      R.answer r t >>= fun q => M.runAgainst R k (q.2, next q.1) :=
  M.runWith_query_succ_stateT R.toQueryImpl k s t next hview r

/-! ## Memoryless recovery -/

/-- Against a constant-state responder the wired run is the memoryless machine run
against the selected handler, with the setup carried along unchanged: the machine-run
form of `OracleStrategy.iterateAgainst_ofHandlerFamily`. -/
@[simp] theorem runAgainst_ofHandlerFamily {Γ : Type u} (h : Γ → ProbHandler spec)
    (M : OracleMachine spec α β) (k : ℕ) (s : M.State) (γ : Γ) :
    M.runAgainst (.ofHandlerFamily h) k (γ, s) =
      (fun ob => (ob, γ)) <$> M.runWith (h γ) k s := by
  induction k generalizing s with
  | zero =>
    cases hview : M.view s with
    | inl b =>
      rw [M.runAgainst_of_view_return _ hview, M.runWith_return (h γ) 0 s b hview,
        map_pure]
    | inr q =>
      rw [M.runAgainst_zero_of_view_query _ hview,
        M.runWith_query_zero (h γ) s q.1 q.2 hview, map_pure]
  | succ k ih =>
    cases hview : M.view s with
    | inl b =>
      rw [M.runAgainst_of_view_return _ hview, M.runWith_return (h γ) (k + 1) s b hview,
        map_pure]
    | inr q =>
      obtain ⟨t, next⟩ := q
      calc M.runAgainst (.ofHandlerFamily h) (k + 1) (γ, s)
          = (ProbResponder.ofHandlerFamily h).answer γ t >>= fun p =>
              M.runAgainst (.ofHandlerFamily h) k (p.2, next p.1) :=
            M.runAgainst_succ_of_view_query (.ofHandlerFamily h) hview k γ
        _ = h γ t >>= fun a =>
              (fun ob => (ob, γ)) <$> M.runWith (h γ) k (next a) := by
            simp only [ProbResponder.ofHandlerFamily, bind_map_left]
            exact bind_congr fun a => ih (next a)
        _ = (fun ob => (ob, γ)) <$> M.runWith (h γ) (k + 1) s := by
            rw [M.runWith_query_succ (h γ) k s t next hview, map_bind]

/-! ## Interface wrapping: reductions as lenses

Installing an interface translation on a machine adversary is PolyFun's
`DynComputation.wrap`, and it is *adjoint* to pulling the responder back along the
same lens: wrapping the adversary forward equals pulling the challenger's responder
back. -/

variable {ι' : Type u} {spec' : OracleSpec.{u, u} ι'}

/-- **The run-level interface-wrapping adjunction**: running the wrapped machine
against a `spec'`-responder equals running the original machine against the responder
pulled back along `w`. Pure factoring, no fuel induction: `unroll_wrap` translates the
unrolled query tree, and `ProbResponder.liftM_mapLens_pullback` re-reads the
translation through the pulled-back handler. -/
theorem runWith_wrap (w : PFunctor.Lens spec.toPFunctor spec'.toPFunctor)
    (M : OracleMachine spec α β) (R : ProbResponder spec') (k : ℕ) (s : M.State) :
    (M.wrap w).runWith R.toQueryImpl k s =
      M.runWith (R.pullback w).toQueryImpl k s := by
  simp only [DynComputation.runWith]
  rw [M.unroll_wrap w k s]
  exact ProbResponder.liftM_mapLens_pullback w R (M.unroll k s)

/-- **The wired-run interface-wrapping adjunction**: the `runAgainst` form of
`runWith_wrap`. This is the workhorse of same-interface reductions at the game
level. -/
theorem runAgainst_wrap (w : PFunctor.Lens spec.toPFunctor spec'.toPFunctor)
    (M : OracleMachine spec α β) (R : ProbResponder spec') (k : ℕ) (r : R.State)
    (s : M.State) :
    runAgainst (M.wrap w) R k (r, s) = M.runAgainst (R.pullback w) k (r, s) := by
  rw [runAgainst_eq_runWith_run, runAgainst_eq_runWith_run, runWith_wrap]

end OracleComp.OracleMachine
