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

Oracle computations read expectations by default; the structural and probability-bounded
interpretations take precedence inside their scopes. State and append-based logs retain their
input and output information. The quantitative example uses core's tactic directly, without
VCVio's probability-tactic frontend.
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

end VCVioTest.ProgramLogic.CoreWP
