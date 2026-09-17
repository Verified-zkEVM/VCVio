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

Ordinary imports expose all three interpretations without selecting one globally.
State and append-based logs retain their input and output information. The quantitative
example uses core's tactic directly, without VCVio's probability-tactic frontend.
-/

public section

open Std.Internal.Do
open scoped ENNReal

namespace VCVioTest.ProgramLogic.CoreWP

example : True := by
  fail_if_success
    let _ := (inferInstance : WPMonad ProbComp ℝ≥0∞ EPost.Nil)
  trivial

section Qualitative
open scoped OracleComp.Qualitative

example {ι : Type} {spec : OracleSpec ι} {α : Type} (oa : OracleComp spec α)
    (post : α → Prop) :
    wp oa post EPost.Nil.mk ↔ ∀ a ∈ support oa, post a :=
  OracleComp.ProgramLogic.PropLogic.wp_iff_forall_support oa post

end Qualitative

section Quantitative
open scoped OracleComp.Quantitative

/--
warning: The `vcgen` tactic is an experimental drop-in replacement for `mvcgen` that will eventually replace it. Avoid using it in production projects.
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

noncomputable local instance : WPMonad (WriterT (List Nat) ProbComp) (List Nat → ℝ≥0∞) EPost.Nil :=
  WriterT.wpMonadOf [] (· ++ ·) List.append_nil List.append_assoc

example (post : PUnit.{1} → List Nat → ℝ≥0∞) :
    ⦃ fun log => post ⟨⟩ (log ++ [1, 2]) ⦄
      (do tell [1]; tell [2] : WriterT (List Nat) ProbComp PUnit)
    ⦃ post ⦄ := by
  refine Triple.intro ?_
  intro log
  simp [WriterT.run_bind, WriterT.run_tell, MAlgOrdered.wp_pure]

end Quantitative

section Probabilistic
open scoped OracleComp.Probabilistic

example (oa : ProbComp Nat) (post : Nat → Prob) :
    (wp oa post EPost.Nil.mk).val =
      MAlgOrdered.wp (l := ℝ≥0∞) oa (fun a => (post a).val) :=
  OracleComp.Probabilistic.wp_val_eq_mAlgOrdered_wp oa post

end Probabilistic

end VCVioTest.ProgramLogic.CoreWP
