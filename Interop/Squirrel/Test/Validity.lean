/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Squirrel.Global
import VCVio.OracleComp.EvalDist.Measure

/-!
# Satisfiability checks of the semantics

* `Model.trivial D` interprets every base type as the single empty bitstring, over empty tapes;
  it respects every label but `large` (`Model.trivial_respectsLabels`), so for a declaration with
  no `large` base type validity does not quantify over an empty class of models. A `large` base
  type has a carrier that grows with `η`, which a type labelled `finite` and `fixed` cannot have,
  so some declarations have no model.
* `Valid.not_box_ff`: `[false]` is not valid, whatever the classes of machines, so validity is
  not trivial.
* `Valid.not_equiv_tt_ff`: `true ∼ false` is not valid against `AdvClass.all`: the machine that
  returns its input (`Machine.input`) meets the read and query bounds and has advantage one. So
  an indistinguishability is not valid for want of admitted machines.
-/

public section

namespace Interop.Squirrel

open IPFunctor IPFunctor.ScopedSignature

variable {B : Type} {D : Decl B}

/-- Every base type is the single empty bitstring, the attacker tape and the names' bit blocks
are empty, and the samplers, honest and attacker symbols take arbitrary values. -/
noncomputable def Model.trivial (D : Decl B) : Model D where
  lenA _ := 0
  carrier _ _ := {[]}
  nonempty _ _ := Set.singleton_nonempty _
  coinLen _ _ := 0
  sample η b _ := Classical.choice (b.nonempty_value (fun _ _ => Set.singleton_nonempty _) η)
  finite_index η {a _} _ := a.finite_value_of_finite (fun _ _ => Set.finite_singleton _) η
  fn η {τ} _ := Classical.choice (τ.nonempty_value (fun _ _ => Set.singleton_nonempty _) η)
  att η f _ := Classical.choice ((D.attTy f).nonempty_value
    (fun _ _ => Set.singleton_nonempty _) η)

/-- The trivial model meets every label but `large`: its carriers are finite and constant. -/
theorem Model.trivial_respectsLabels (hD : ∀ b, ¬ D.labels b .large) :
    (Model.trivial D).RespectsLabels
  | _, .finite, _ => fun _ => Set.finite_singleton _
  | _, .fixed, _ => fun _ _ => rfl
  | b, .large, h => absurd h (hD b)

/-- `[false]` is not valid, whatever the classes of machines, for a declaration with no `large`
base type. -/
theorem Valid.not_box_ff (hD : ∀ b, ¬ D.labels b .large) (C : ∀ M : Model D, AdvClass M) :
    ¬ Valid (fun _ => True) C (Γ := []) [] (.box .ff) := fun h => by
  have hM := h (Model.trivial D) (Model.trivial_respectsLabels hD) trivial Env.empty (by simp)
  refine not_negligible_one (negligible_of_le (fun η => le_of_eq ?_) hM)
  exact (OracleComp.prEvent_eq_one_of_forall_mem_support _ _ fun _ _ => rfl).symm

/-- `true ∼ false` is not valid against `AdvClass.all`, for a declaration with no `large` base
type: the machine that returns its input has advantage one. -/
theorem Valid.not_equiv_tt_ff (hD : ∀ b, ¬ D.labels b .large) :
    ¬ Valid (D := D) (fun _ => True) AdvClass.all (Γ := []) []
      (.equiv (Env.cons .tt Env.empty) (Env.cons .ff Env.empty)) := fun h => by
  have hM := Form.holds_equiv.1 (h (Model.trivial D) (Model.trivial_respectsLabels hD) trivial
    Env.empty (by simp)) (Machine.input .zero Ty.isGround_bool)
    (AdvClass.all_mem_input _ _)
  refine not_negligible_one (negligible_of_le (fun η => le_of_eq ?_) hM)
  simp only [advantage, Machine.test, Machine.run_input, Vec.rv_cons, VecRV.cons, Env.cons_zero,
    FTerm.denote_tt, FTerm.denote_ff]
  rw [OracleComp.prEvent_true_eq_one,
    prEvent_eq_zero_of_forall_not _ _ fun _ h => Bool.noConfusion h, ENNReal.absDiff_zero_right]

end Interop.Squirrel
