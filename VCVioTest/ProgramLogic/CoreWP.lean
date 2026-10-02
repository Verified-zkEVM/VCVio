/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.ProgramLogic.Unary.WP.Coherence
public import PolyFun.Control.Do.Spec
public import ToMathlib.Control.WriterT

/-!
# Core WP carrier selection and transformer consumers

Oracle computations read `Prop` triples by default (the necessary reading); the expectation and
probability-bounded interpretations take precedence inside their scopes. State and append-based logs
retain their input and output information. The quantitative example uses core's tactic directly,
without VCVio's probability-tactic frontend.
-/

public section

open Std.WP
open scoped ENNReal

namespace VCVioTest.ProgramLogic.CoreWP

noncomputable example : WPMonad ProbComp Prop EStack⟨⟩ := inferInstance

example : True := by
  fail_if_success
    let _ := (inferInstance : WPMonad ProbComp ℝ≥0∞ EStack⟨⟩)
  trivial

section Qualitative

example {ι : Type} {spec : OracleSpec ι} {α : Type} (oa : OracleComp spec α)
    (post : α → Prop) :
    wp oa post estack⟨⟩ ↔ ∀ a ∈ support oa, post a :=
  OracleComp.Necessary.wp_iff_forall_support oa post

end Qualitative

section Quantitative
open scoped OracleComp.Lower

noncomputable example : WPMonad ProbComp ℝ≥0∞ EStack⟨⟩ := inferInstance

-- The package acknowledges `vcgen`'s experimental status once (`lakefile.lean`); this pins the
-- warning a file sees without that acknowledgment.
set_option experimental.vcgen false in
/--
warning: The `vcgen` tactic is an experimental drop-in replacement for `mvcgen` that will eventually replace it; `set_option experimental.vcgen true` acknowledges its experimental status and silences this warning.
-/
#guard_msgs in
example (post : Nat → Nat → ℝ≥0∞) :
    ⦃ fun n => post n (n + 1) ⦄
      (do
        let n ← get
        set (n + 1)
        pure n : StateT Nat ProbComp Nat)
    ⦃ post ⦄ := by
  vcgen

noncomputable local instance : WPMonad (WriterT (List Nat) ProbComp) (List Nat → ℝ≥0∞) EStack⟨⟩ :=
  WriterT.wpMonadOf [] (· ++ ·) List.append_nil List.append_assoc

example (post : PUnit.{1} → List Nat → ℝ≥0∞) :
    ⦃ fun log => post ⟨⟩ (log ++ [1, 2]) ⦄
      (do tell [1]; tell [2] : WriterT (List Nat) ProbComp PUnit)
    ⦃ post ⦄ := by
  refine Triple.intro ?_
  intro log
  simp [WriterT.run_bind, WriterT.run_tell]

end Quantitative

section Probabilistic
open scoped OracleComp.Probabilistic

example (oa : ProbComp Nat) (post : Nat → Prob) :
    (wp oa post estack⟨⟩).val =
      wp⟦oa⟧ (fun a => (post a).val) :=
  OracleComp.Probabilistic.wp_val_eq_wp oa post _

end Probabilistic

/-! ## What each reading means, against the others -/

section Coherence

open OrderDual

variable {α : Type}

/-- The lower-bound triple from `1` of an event's indicator is the necessary triple. -/
example (oa : ProbComp α) (p : α → Prop) (h : ⦃ True ⦄ oa ⦃ p ⦄) :
    @Triple ℝ≥0∞ EStack⟨⟩ (ProbComp α) α _ _ oa OracleComp.Lower.wpInst 1 (predInd p)
      Lean.Order.bot :=
  (OracleComp.Necessary.triple_one_iff_triple oa p).2 h

/-- The upper-bound triple from `0` of the indicator of an event's negation is the necessary
triple. -/
example (oa : ProbComp α) (p : α → Prop) (h : ⦃ True ⦄ oa ⦃ p ⦄) :
    @Triple ℝ≥0∞ᵒᵈ EStack⟨⟩ᵒᵈ (ProbComp α) α _ _ oa OracleComp.Upper.wpInst (toDual 0)
      (fun x => toDual (propInd (¬ p x))) Lean.Order.bot :=
  (OracleComp.Necessary.triple_zero_not_iff_triple oa p).2 h

/-- A necessary triple gives a possible one, since every oracle computation has a possible
outcome. -/
example (oa : ProbComp α) (p : α → Prop) (h : ⦃ True ⦄ oa ⦃ p ⦄) :
    @Triple Prop EStack⟨⟩ (ProbComp α) α _ _ oa OracleComp.Possible.wpInst True p
      Lean.Order.bot :=
  OracleComp.Possible.triple_of_necessary oa p (OracleComp.support_nonempty oa) h

/-- The necessary triple of an `OptionT` event forbids failure. -/
example (mx : OptionT ProbComp α) (p : α → Prop) (h : Pr{let x ← mx}[p x] = 1) :
    ⦃ True ⦄ mx ⦃ p; (fun _ => False, Lean.Order.bot) ⦄ :=
  (OracleComp.Necessary.OptionT.prEvent_eq_one_iff_triple mx p).1 h

open scoped OracleComp.Upper in
/-- The lifted upper-bound reading of an `OptionT` program, with a failure worth `0`, is the
dual of its expectation. -/
example (mx : OptionT ProbComp α) (g : α → ℝ≥0∞) :
    wp mx (fun a => toDual (g a)) (fun _ => toDual 0, Lean.Order.bot) = toDual (wp⟦mx⟧ g) :=
  OracleComp.Upper.OptionT.wp_eq mx _

end Coherence

end VCVioTest.ProgramLogic.CoreWP
