/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public meta import VCVio.ProgramLogic.Tactics
public import VCVioFoxglove.Independence
public import VCVioFoxglove.Specs

/-!
# `vcgen` with Foxglove

Importing this module extends VCVio's `vcgen`. It is still one tactic, now with Foxglove's
rules available. Lean tries a syntax kind's elaborators in turn, so the elaborator added here
runs first, and gives way (`throwUnsupportedSyntax`) to VCVio's `vcgen`, and through it to core's,
on every goal it does not handle.

* **Foxglove goals** (`⊢ wp oa ⦃X, …⦄`) are decomposed by Foxglove's rules: leaf laws of
  VCVio's samplers, independence of a sample and an independent sampler, independent
  post-processing, and the semantic route `wp_of_prEvent` to VCVio's own event goals. Whatever
  is left is handed to VCVio's `vcgen`.
* **VCVio event goals** that independence decides (a decided event of two draws, a guess of a
  uniform draw, a conjunction of events of independent components, a product output measure) are
  tried through Foxglove all-or-nothing: if the attempt does not close the goal, the state is
  restored and VCVio's `vcgen` runs as before.

The routes are lemma applications (`Foxglove.*`). The only custom tooling is the routing itself.
-/

public meta section

open Lean Elab Tactic Meta

namespace Foxglove.VCGen

/-- Laws of leaf programs: VCVio's samplers, `pure`, and, when the law is still to be found,
the program's own tape law. Reducible transparency keeps a mismatch from unfolding `wp`. -/
macro "fox_leaf" : tactic => `(tactic| with_reducible first
  | exact Foxglove.wp_uniformSample _
  | exact Foxglove.wp_query_unifSpec _
  | exact Foxglove.wp_pure_law _
  | exact Foxglove.wp_lawPMF _)

/-- One step on an independence goal `⊢ wp oa ⦃X, (fst ∘ X) ~ μ ∗ (snd ∘ X) ~ ν⦄`. -/
macro "fox_indep" : tactic => `(tactic| with_reducible first
  | refine Foxglove.wp_bind_pair_sep_of_evalDist_eq ?_ fun _ ↦ ?_
  | refine Foxglove.wp_bind_pair_sep ?_ fun _ ↦ ?_
  | refine Foxglove.wp_bind_sep_bind ?_ (fun _ ↦ ?_) (fun _ ↦ ?_))

/-- Event goals that independence decides, reduced to independence goals. The laws of the
components are left as metavariables for the independence steps to find. -/
macro "fox_event" : tactic => `(tactic| first
  | rw [Foxglove.evalDist_decide_bind_bind]
  | apply Eq.trans (Foxglove.prEvent_eq_of_wp_sep_uniform ?_)
  | apply Foxglove.prEvent_and_of_wp_sep
  | apply Foxglove.evalDist_eq_product_of_wp_sep)

/-- Side conditions: equal output measures across a binder, and numerals. -/
macro "fox_close" : tactic => `(tactic| first
  | rfl
  | (simp_all; done)
  | (rename_i b; cases b <;> simp_all; done)
  | (norm_num [one_div]; done))

/-- One Foxglove step. -/
macro "fox_step" : tactic => `(tactic| first | fox_leaf | fox_indep | fox_event)

/-- Whether `e` mentions Foxglove's `wp`. -/
def mentionsFoxgloveWP (e : Expr) : Bool :=
  (e.find? fun e ↦ e.isConstOf ``Foxglove.wp).isSome

/-- The option that marks a `vcgen` call made from inside the Foxglove routes, which goes
straight to VCVio's `vcgen`. -/
def innerOption : Name := `foxglove.vcgen.inner

/-- Run the Foxglove routes to a fixpoint, close side conditions, and hand every goal that is
left to VCVio's `vcgen`. -/
def run : TacticM Unit := withOptions (·.setBool innerOption true) do
  evalTactic (← `(tactic| repeat' fox_step))
  evalTactic (← `(tactic| all_goals try fox_close))
  evalTactic (← `(tactic| all_goals try vcgen))

elab_rules (kind := OracleComp.ProgramLogic.vcgenBasic) : tactic
  | `(tactic| vcgen) => do
    if (← getOptions).getBool innerOption false then throwUnsupportedSyntax
    if (← getGoals).isEmpty then throwUnsupportedSyntax
    let target ← instantiateMVars (← getMainTarget)
    if mentionsFoxgloveWP target then
      run
    else
      -- an event goal: through Foxglove only if that closes it
      let saved ← saveState
      let closed ← try
          evalTactic (← `(tactic| fox_event))
          run
          pure (← getGoals).isEmpty
        catch _ => pure false
      unless closed do
        saved.restore
        throwUnsupportedSyntax

end Foxglove.VCGen
