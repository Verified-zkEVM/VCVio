/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Squirrel.Rules.Local

/-!
# Derivations of global sequents

Derivations of the structural rules of LICS23 (Fig. 7), as data: each constructor is one rule,
indexed by the context, the hypotheses and the conclusion. Local sequents are unfolded to the
global sequents `Θ ⊢ [∧Γl ⇒ φ]` that they stand for (`LValid`). `Derivation.sound` maps every
derivation to validity over every model restriction and every class of machines, one rule lemma
of `Interop.Squirrel.Global` and `Interop.Squirrel.Rules.Local` per constructor. No rule here
uses a property of the class of machines, so soundness holds for every class.

## References

* [LICS23] Baelde, Koutsos, Lallemand, *A Higher-Order Indistinguishability Logic for
  Cryptographic Reasoning*, LICS 2023: §III and Fig. 7.
-/

public section

namespace Interop.Squirrel

open IPFunctor IPFunctor.ScopedSignature

variable {B : Type}

/-- Derivations of `Θ ⊢ F` in the context `Γ` by the structural rules. -/
inductive Derivation (D : Decl B) : {Γ : List (Kind B)} → List (Form D Γ) → Form D Γ → Type
  /-- G.Axiom. -/
  | ax {Γ : List (Kind B)} {Θ : List (Form D Γ)} {F : Form D Γ} : F ∈ Θ → Derivation D Θ F
  /-- G.Weak. -/
  | weaken {Γ : List (Kind B)} {Θ Θ' : List (Form D Γ)} {F : Form D Γ} :
      Derivation D Θ F → Θ ⊆ Θ' → Derivation D Θ' F
  /-- G.Cut. -/
  | cut {Γ : List (Kind B)} {Θ : List (Form D Γ)} {F F' : Form D Γ} :
      Derivation D Θ F' → Derivation D (F' :: Θ) F → Derivation D Θ F
  /-- G.L-∀̃. -/
  | allLeft {Γ : List (Kind B)} {Θ : List (Form D Γ)} {F : Form D Γ} {τ : Ty B}
      {G : Form D (.loc τ :: Γ)} (t : FTerm D Γ τ) :
      Derivation D (G.substOne t :: Θ) F → Derivation D (.all τ G :: Θ) F
  /-- G.R-∀̃. -/
  | allRight {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τ : Ty B} {G : Form D (.loc τ :: Γ)} :
      Derivation D (Θ.map (Term.weaken · (.loc τ))) G → Derivation D Θ (.all τ G)
  /-- L.ByGlob, with the local sequent unfolded. -/
  | byGlob {Γ : List (Kind B)} {Θ : List (Form D Γ)} {φ : FTerm D Γ .bool}
      (Γl : List (FTerm D Γ .bool)) :
      Derivation D Θ (.box φ) → Derivation D Θ (.box (.imp (.conj Γl) φ))
  /-- G.ByLoc, with the local sequent unfolded. -/
  | byLoc {Γ : List (Kind B)} {Θ : List (Form D Γ)} {φ : FTerm D Γ .bool} :
      Derivation D Θ (.box (.imp (.conj []) φ)) → Derivation D Θ (.box φ)
  /-- L.R-∀, with the local sequents unfolded. -/
  | localAll {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τ : Ty B} {φ : FTerm D (.loc τ :: Γ) .bool}
      (Γl : List (FTerm D Γ .bool)) :
      Derivation D (Θ.map (Term.weaken · (.loc τ)))
        (.box (.imp (.conj (Γl.map (Term.weaken · (.loc τ)))) φ)) →
      Derivation D Θ (.box (.imp (.conj Γl) (FTerm.all φ)))

variable {D : Decl B}

/-- **Soundness.** Every derivation is valid over every model restriction `R` and against every
class of machines `C`. -/
theorem Derivation.sound (R : Model D → Prop) (C : ∀ M : Model D, AdvClass M) :
    {Γ : List (Kind B)} → {Θ : List (Form D Γ)} → {F : Form D Γ} → Derivation D Θ F →
      Valid R C Θ F
  | _, _, _, .ax h => Valid.ax h
  | _, _, _, .weaken d h => (d.sound R C).weaken h
  | _, _, _, .cut d₁ d₂ => (d₁.sound R C).cut (d₂.sound R C)
  | _, _, _, .allLeft t d => Valid.all_left t (d.sound R C)
  | _, _, _, .allRight d => Valid.all_right (d.sound R C)
  | _, _, _, .byGlob Γl d => Valid.byGlob Γl (d.sound R C)
  | _, _, _, .byLoc d => Valid.byLoc (d.sound R C)
  | _, _, _, .localAll Γl d => Valid.local_all Γl (d.sound R C)

end Interop.Squirrel
