/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Squirrel.Global

/-!
# Local universal introduction

LICS23's rule L.R-∀ (Fig. 7) introduces a local universal quantifier from a local sequent with
the variable in context: `E, x : τ; Θ; Γ ⊢ φ` gives `E; Θ; Γ ⊢ ∀ (x : τ). φ`. Its soundness is
Proposition 2's choice construction: the variable of the premise is instantiated by a random
variable that picks, at each parameter and tape, a counterexample to `φ` when one exists. The
premise then makes the counterexamples rare.

Locality (`eval_denote_fullInterp`) is what lets the chosen random variable stand for the
constant `RV.constAt η a` that the local quantifier binds.

## References

* [LICS23] Baelde, Koutsos, Lallemand, *A Higher-Order Indistinguishability Logic for
  Cryptographic Reasoning*, LICS 2023: Fig. 7 and Proposition 2.
-/

public section

namespace Interop.Squirrel

open IPFunctor IPFunctor.ScopedSignature

variable {B : Type} {D : Decl B} {M : Model D} {C : AdvClass M} {Γ : List (Kind B)}

/-- Weakening the local hypotheses past a binder does not change their conjunction. -/
private theorem FTerm.denote_conj_weaken {τ : Ty B} (Γl : List (FTerm D Γ .bool))
    (X : RV M τ) (env : Env (Kind.Value M) Γ) :
    (FTerm.conj (Γl.map (Term.weaken · (.loc τ)))).denote (fullInterp M C) (Env.cons X env) =
      (FTerm.conj Γl).denote (fullInterp M C) env := by
  induction Γl with
  | nil => rfl
  | cons φ Γl ih =>
    simp only [List.map_cons, FTerm.conj, FTerm.denote_ite, FTerm.denote_ff, ih,
      denote_weaken_cons]

/-- At `(η, ρ)`, a term depends on the random variable bound to its nearest variable only
through its value at `(η, ρ)`. -/
private theorem denote_cons_congr {τ : Ty B} {s : Kind B}
    (t : (fullSig D).Term (.loc τ :: Γ) s) (env : Env (Kind.Value M) Γ) {X Y : RV M τ} {η : ℕ}
    {ρ : M.Tape η} (h : X η ρ = Y η ρ) :
    s.eval M η ρ (t.denote (fullInterp M C) (Env.cons X env)) =
      s.eval M η ρ (t.denote (fullInterp M C) (Env.cons Y env)) := by
  rw [eval_denote_fullInterp, eval_denote_fullInterp]
  congr 1
  funext s x
  cases x
  · exact h
  · rfl

namespace Valid

variable {R : Model D → Prop} {C : ∀ M : Model D, AdvClass M} {Θ : List (Form D Γ)}

/-- **L.R-∀** (LICS23 Fig. 7, Proposition 2). -/
theorem local_all {τ : Ty B} {φ : FTerm D (.loc τ :: Γ) .bool} (Γl : List (FTerm D Γ .bool))
    (h : LValid R C (Θ.map (Term.weaken · (.loc τ))) (Γl.map (Term.weaken · (.loc τ))) φ) :
    LValid R C Θ Γl (FTerm.all φ) := by
  intro M hl hR env hΘ
  classical
  let ψ (η : ℕ) (ρ : M.Tape η) (a : τ.Value M.carrier η) : Bool :=
    φ.denote (fullInterp M (C M)) (Env.cons (RV.constAt η a) env) η ρ
  let X : RV M τ := fun η ρ => if hx : ∃ a, ψ η ρ a = false then hx.choose
    else Classical.choice (τ.nonempty_value M.nonempty η)
  refine Form.holds_box.2 <| (Form.holds_box.1 (h M hl hR (Env.cons X env) fun θ hθ => ?_)).mono
    fun η ρ hρ => ?_
  · obtain ⟨θ', hθ', rfl⟩ := List.mem_map.1 hθ
    rw [Form.Holds, denote_weaken_cons (fullInterp M (C M)) θ' (s' := .loc τ) X env]
    exact hΘ θ' hθ'
  · have hφ : φ.denote (fullInterp M (C M)) (Env.cons X env) η ρ = ψ η ρ (X η ρ) :=
      denote_cons_congr φ env (RV.constAt_apply_self η (X η ρ) ρ).symm
    simp only [FTerm.imp, FTerm.denote_ite, FTerm.denote_tt, FTerm.denote_all,
      FTerm.denote_conj_weaken, hφ] at hρ ⊢
    cases hc : (FTerm.conj Γl).denote (fullInterp M (C M)) env η ρ
    · simp only [hc, Bool.cond_false] at hρ
      exact Bool.noConfusion hρ
    simp only [hc, Bool.cond_true] at hρ ⊢
    have hx : ∃ a, ψ η ρ a = false := by
      by_contra hn
      have hall : ∀ a, ψ η ρ a = true := fun a => by simpa using fun h => hn ⟨a, h⟩
      exact Bool.noConfusion (hρ.symm.trans (@decide_eq_true _ (Classical.propDecidable _) hall))
    rw [show X η ρ = hx.choose by simp [X, hx]]
    exact hx.choose_spec

end Valid

end Interop.Squirrel
