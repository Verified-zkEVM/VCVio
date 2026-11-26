/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Squirrel.Derivation
public import Interop.Squirrel.Test.Validity
import VCVio.OracleComp.EvalDist.Measure

/-!
# Checks of the structural rules

Small derivations, one or two rules each; `Valid.all_inst` and `Valid.box_ff_of_hyp` read two of
them through `Derivation.sound`:

* `Derivation.hyp`: G.Axiom and G.Weak.
* `Derivation.allInst`, `Valid.all_inst`: G.L-∀̃, G.Cut and G.Axiom instantiate a global universal.
* `Derivation.allVacuous`: G.R-∀̃ quantifies a hypothesis over a variable it does not mention.
* `Derivation.boxRoundTrip`: L.ByGlob, then G.ByLoc.
* `Valid.box_all_eq_self`: L.R-∀ gives `[∀ x. x = x]` from the local validity of `x = x`.

Two checks show that premises are needed, for a declaration with no `large` base type. `[false]`
follows from the hypothesis `[false]` (`Valid.box_ff_of_hyp`) but not from no hypothesis
(`Valid.not_box_ff`), so G.Axiom reads its hypotheses. `[∀ (x : bool). x = true]` is not valid
(`Valid.not_box_all_eq_tt`), since the local quantifier ranges over the whole carrier, so L.R-∀
needs its premise, here the local validity of `x = true`.
-/

public section

namespace Interop.Squirrel

open IPFunctor IPFunctor.ScopedSignature

variable {B : Type} {D : Decl B} {Γ : List (Kind B)}

/-- G.Axiom and G.Weak: a hypothesis is derivable from any list holding it. -/
def Derivation.hyp (F G : Form D Γ) : Derivation D [G, F] F :=
  .weaken (Θ := [F]) (.ax List.mem_cons_self) (by simp)

/-- G.L-∀̃, G.Cut and G.Axiom: from the hypothesis `∀̃ x. G`, conclude `G{x ↦ t}`. -/
def Derivation.allInst {τ : Ty B} (G : Form D (.loc τ :: Γ)) (t : FTerm D Γ τ) :
    Derivation D [.all τ G] (G.substOne t) :=
  .allLeft t (.ax List.mem_cons_self)

/-- A valid global universal may be instantiated by any local term: G.Cut, G.L-∀̃, G.Axiom. -/
theorem Valid.all_inst {R : Model D → Prop} {C : ∀ M : Model D, AdvClass M}
    {Θ : List (Form D Γ)} {τ : Ty B} {G : Form D (.loc τ :: Γ)} (t : FTerm D Γ τ)
    (h : Valid R C Θ (.all τ G)) : Valid R C Θ (G.substOne t) :=
  h.cut (((Derivation.allInst G t).sound R C).weaken (by simp))

/-- G.R-∀̃: a hypothesis holds under a global quantifier over a variable it does not mention. -/
def Derivation.allVacuous (F : Form D Γ) (τ : Ty B) :
    Derivation D [F] (.all τ (F.weaken (.loc τ))) :=
  .allRight (.ax List.mem_cons_self)

/-- L.ByGlob, then G.ByLoc: `[φ]` gives `[∧[] ⇒ φ]`, and that gives `[φ]` back. -/
def Derivation.boxRoundTrip (φ : FTerm D Γ .bool) : Derivation D [.box φ] (.box φ) :=
  .byLoc (.byGlob [] (.ax List.mem_cons_self))

/-- G.Axiom: `[false]` follows from the hypothesis `[false]`, in every model. -/
theorem Valid.box_ff_of_hyp (R : Model D → Prop) (C : ∀ M : Model D, AdvClass M) :
    Valid R C (Γ := []) [.box .ff] (.box .ff) :=
  (Derivation.ax List.mem_cons_self).sound R C

/-- L.R-∀ (with G.ByLoc): `[∀ x. x = x]`, from the local validity of `x = x` for a free `x`. -/
theorem Valid.box_all_eq_self (R : Model D → Prop) (C : ∀ M : Model D, AdvClass M) (τ : Ty B) :
    Valid R C (Γ := []) [] (.box (FTerm.all (FTerm.eq (.var .zero) (.var .zero) :
      FTerm D [.loc τ] .bool))) := by
  refine Valid.byLoc (Valid.local_all [] fun M _ _ env _ => Form.holds_box.2 ?_)
  refine negligible_of_zero fun η => prEvent_eq_zero_of_forall_not _ _ fun ρ h => ?_
  simp [FTerm.imp, FTerm.conj] at h

/-- `[∀ (x : bool). x = true]` is not valid, whatever the classes of machines, for a declaration
with no `large` base type: the local quantifier ranges over `false` too. -/
theorem Valid.not_box_all_eq_tt (hD : ∀ b, ¬ D.labels b .large) (C : ∀ M : Model D, AdvClass M) :
    ¬ Valid (fun _ => True) C (Γ := []) []
      (.box (FTerm.all (FTerm.eq (.var .zero) .tt : FTerm D [.loc .bool] .bool))) := fun h => by
  have hM := Form.holds_box.1
    (h (Model.trivial D) (Model.trivial_respectsLabels hD) trivial Env.empty (by simp))
  refine not_negligible_one (negligible_of_le (fun η => le_of_eq ?_) hM)
  refine (OracleComp.prEvent_eq_one_of_forall_mem_support _ _ fun ρ _ => ?_).symm
  simp [FTerm.denote_all, FTerm.denote_eq]

end Interop.Squirrel
