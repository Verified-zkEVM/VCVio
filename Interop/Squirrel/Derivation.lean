/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Squirrel.Rules.Local
public import Interop.Squirrel.Rules.Equiv
public import Interop.Squirrel.Rules.Rename
public import Interop.Squirrel.Rules.Enc

/-!
# Derivations of global sequents

Derivations in the fragment of the logic proved sound here, as data: each constructor is one rule,
indexed by the context, the hypotheses and the conclusion. Local sequents are unfolded to the
global sequents `Θ ⊢ [∧Γl ⇒ φ]` that they stand for (`LValid`). `Derivation.sound` maps every
derivation to validity over every model restriction and every class of machines, one rule lemma
per constructor:

* the structural rules of LICS23 (Fig. 7), from `Interop.Squirrel.Global` and
  `Interop.Squirrel.Rules.Local`;
* the rules about `∼` that need no cryptographic assumption (`Interop.Squirrel.Rules.Equiv`).
  BC14's If1 (`equivIf1`) is sound by the case split (`equivCaseStudy`), but is a constructor of
  its own: deriving it would rewrite `if c' then z else z` to `z`, and the fragment has no rule
  proving that local equality;
* name renaming, for a bijection of names (`Valid.equiv_renameNames_of_equiv`), which holds in
  every model;
* the encryption rule (`Valid.equiv_enc`), at the instances that the parameter `enc` admits. Its
  syntactic side conditions (`EncInstance.Syntactic`: distinct key and coin names, which the
  messages and the context do not use) are a premise of the constructor, which `decide` discharges
  on concrete instances. `Derivation.sound` takes the semantic hypotheses of each admitted
  instance (`EncInstance.Holds`). With `enc` empty, derivations are those of the rest of the
  fragment.

The rules about `∼` hold for every class of machines, because the class is closed under their
reductions by its fields (`AdvClass`). Formulas carry the order bounds of CSF24 and CCS26
(`Ty.IndistOrder`, `Ty.AdvOrder`). A constructor's conclusion carries the bound derived from its
premises', and a constructor that adds an entry or starts from no premise takes the conclusion's
bound.

## References

* [LICS23] Baelde, Koutsos, Lallemand, *A Higher-Order Indistinguishability Logic for
  Cryptographic Reasoning*, LICS 2023: §III, Figs. 7 and 8, Prop. 19.
* [BC14] Bana, Comon-Lundh, *A Computationally Complete Symbolic Attacker for Equivalence
  Properties*, CCS 2014: Fig. 2, Props. 2 and 3.
* [CSF24] Baelde, Fontaine, Koutsos, Scerri, Vignon, *A Probabilistic Logic for Concrete
  Security*, CSF 2024: App. A.
* [CCS26] Hérouard, Jacomme, Koutsos, Lallemand, *Secrecy in Squirrel and the Post-Compromise
  Security of a Ratchet*, CCS 2026: §3.1.
-/

public section

namespace Interop.Squirrel

open IPFunctor IPFunctor.ScopedSignature

variable {B : Type}

/-- Derivations of `Θ ⊢ F` in the context `Γ`, using the encryption rule at the instances that
`enc` admits. -/
inductive Derivation (D : Decl B) (enc : EncInstance D → Prop) :
    {Γ : List (Kind B)} → List (Form D Γ) → Form D Γ → Type
  /-- G.Axiom. -/
  | ax {Γ : List (Kind B)} {Θ : List (Form D Γ)} {F : Form D Γ} : F ∈ Θ → Derivation D enc Θ F
  /-- G.Weak. -/
  | weaken {Γ : List (Kind B)} {Θ Θ' : List (Form D Γ)} {F : Form D Γ} :
      Derivation D enc Θ F → Θ ⊆ Θ' → Derivation D enc Θ' F
  /-- G.Cut. -/
  | cut {Γ : List (Kind B)} {Θ : List (Form D Γ)} {F F' : Form D Γ} :
      Derivation D enc Θ F' → Derivation D enc (F' :: Θ) F → Derivation D enc Θ F
  /-- G.L-∀̃. -/
  | allLeft {Γ : List (Kind B)} {Θ : List (Form D Γ)} {F : Form D Γ} {τ : Ty B}
      {G : Form D (.loc τ :: Γ)} (t : FTerm D Γ τ) :
      Derivation D enc (G.substOne t :: Θ) F → Derivation D enc (.all τ G :: Θ) F
  /-- G.R-∀̃. -/
  | allRight {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τ : Ty B} {G : Form D (.loc τ :: Γ)} :
      Derivation D enc (Θ.map (Term.weaken · (.loc τ))) G → Derivation D enc Θ (.all τ G)
  /-- L.ByGlob, with the local sequent unfolded. -/
  | byGlob {Γ : List (Kind B)} {Θ : List (Form D Γ)} {φ : FTerm D Γ .bool}
      (Γl : List (FTerm D Γ .bool)) :
      Derivation D enc Θ (.box φ) → Derivation D enc Θ (.box (.imp (.conj Γl) φ))
  /-- G.ByLoc, with the local sequent unfolded. -/
  | byLoc {Γ : List (Kind B)} {Θ : List (Form D Γ)} {φ : FTerm D Γ .bool} :
      Derivation D enc Θ (.box (.imp (.conj []) φ)) → Derivation D enc Θ (.box φ)
  /-- L.R-∀, with the local sequents unfolded. -/
  | localAll {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τ : Ty B} {φ : FTerm D (.loc τ :: Γ) .bool}
      (Γl : List (FTerm D Γ .bool)) :
      Derivation D enc (Θ.map (Term.weaken · (.loc τ)))
        (.box (.imp (.conj (Γl.map (Term.weaken · (.loc τ)))) φ)) →
      Derivation D enc Θ (.box (.imp (.conj Γl) (FTerm.all φ)))
  /-- Refl. -/
  | equivRefl {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} (u : Vec D Γ τs)
      (ho : Ty.IndistOrder τs) : Derivation D enc Θ (.equiv u u ho)
  /-- Sym. -/
  | equivSymm {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {u v : Vec D Γ τs}
      {ho : Ty.IndistOrder τs} :
      Derivation D enc Θ (.equiv u v ho) → Derivation D enc Θ (.equiv v u ho)
  /-- Trans. -/
  | equivTrans {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)}
      {u v w : Vec D Γ τs} {ho : Ty.IndistOrder τs} :
      Derivation D enc Θ (.equiv u v ho) → Derivation D enc Θ (.equiv v w ho) →
      Derivation D enc Θ (.equiv u w ho)
  /-- G.Equiv:FA-App. -/
  | equivApp {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {u v : Vec D Γ τs}
      {a b : Ty B} {t s : FTerm D Γ (.arrow a b)} {t' s' : FTerm D Γ a}
      {ho : Ty.IndistOrder (.arrow a b :: a :: τs)} :
      Derivation D enc Θ
        (.equiv (Env.cons t (Env.cons t' u)) (Env.cons s (Env.cons s' v)) ho) →
      Derivation D enc Θ
        (.equiv (Env.cons (FTerm.app t t') u) (Env.cons (FTerm.app s s') v) ho.app)
  /-- FA-Fn. -/
  | equivFn {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {u v : Vec D Γ τs}
      {τ : Ty B} (ho : Ty.IndistOrder (τ :: τs)) (f : D.Fn τ) :
      Derivation D enc Θ (.equiv u v ho.tail) →
      Derivation D enc Θ (.equiv (Env.cons (FTerm.fn f) u) (Env.cons (FTerm.fn f) v) ho)
  /-- G.Equiv:FA-Adv. -/
  | equivAdv {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {u v : Vec D Γ τs}
      {τs₀ : List (Ty B)} {β : Ty B} {t : FTerm D Γ (Ty.arrows τs₀ β)} {ha : Ty.AdvOrder τs₀ β}
      (ho : Ty.IndistOrder (Ty.arrows τs₀ β :: τs)) :
      Derivation D enc Θ (.adv t ha) → Derivation D enc Θ (.equiv u v ho.tail) →
      Derivation D enc Θ (.equiv (Env.cons t u) (Env.cons t v) ho)
  /-- Restr. -/
  | equivTail {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {u v : Vec D Γ τs}
      {τ : Ty B} {t s : FTerm D Γ τ} {ho : Ty.IndistOrder (τ :: τs)} :
      Derivation D enc Θ (.equiv (Env.cons t u) (Env.cons s v) ho) →
      Derivation D enc Θ (.equiv u v ho.tail)
  /-- Dup. -/
  | equivDup {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {u v : Vec D Γ τs}
      {τ : Ty B} {t s : FTerm D Γ τ} {ho : Ty.IndistOrder (τ :: τs)} :
      Derivation D enc Θ (.equiv (Env.cons t u) (Env.cons s v) ho) →
      Derivation D enc Θ
        (.equiv (Env.cons t (Env.cons t u)) (Env.cons s (Env.cons s v)) ho.dup)
  /-- If. -/
  | equivIte {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {u v : Vec D Γ τs}
      {a : Ty B} {c c' : FTerm D Γ .bool} {t t' s s' : FTerm D Γ a}
      {ho : Ty.IndistOrder (.bool :: a :: a :: τs)} :
      Derivation D enc Θ (.equiv (Env.cons c (Env.cons t (Env.cons t' u)))
        (Env.cons c' (Env.cons s (Env.cons s' v))) ho) →
      Derivation D enc Θ
        (.equiv (Env.cons (FTerm.ite c t t') u) (Env.cons (FTerm.ite c' s s') v) ho.ite)
  /-- G.Case-Study:ITE (LICS23 Fig. 8). -/
  | equivCaseStudy {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)}
      {u v : Vec D Γ τs} {a : Ty B} {c c' : FTerm D Γ .bool} {t t' s s' : FTerm D Γ a}
      {ho : Ty.IndistOrder (.bool :: a :: τs)} :
      Derivation D enc Θ
        (.equiv (Env.cons c (Env.cons t u)) (Env.cons c' (Env.cons s v)) ho) →
      Derivation D enc Θ
        (.equiv (Env.cons c (Env.cons t' u)) (Env.cons c' (Env.cons s' v)) ho) →
      Derivation D enc Θ
        (.equiv (Env.cons (FTerm.ite c t t') u) (Env.cons (FTerm.ite c' s s') v) ho.tail)
  /-- If1 (BC14 Fig. 2). -/
  | equivIf1 {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {u v : Vec D Γ τs}
      {a : Ty B} {c c' : FTerm D Γ .bool} {x y z : FTerm D Γ a}
      {ho : Ty.IndistOrder (.bool :: a :: τs)} :
      Derivation D enc Θ
        (.equiv (Env.cons c (Env.cons x u)) (Env.cons c' (Env.cons z v)) ho) →
      Derivation D enc Θ
        (.equiv (Env.cons c (Env.cons y u)) (Env.cons c' (Env.cons z v)) ho) →
      Derivation D enc Θ (.equiv (Env.cons (FTerm.ite c x y) u) (Env.cons z v) ho.tail)
  /-- Rewriting an entry under an overwhelming equality. -/
  | equivRewrite {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {u : Vec D Γ τs}
      {τ : Ty B} {t t' : FTerm D Γ τ} {w : Vec D Γ (τ :: τs)} {ho : Ty.IndistOrder (τ :: τs)} :
      Derivation D enc Θ (.box (FTerm.eq t t')) →
      Derivation D enc Θ (.equiv (Env.cons t' u) w ho) →
      Derivation D enc Θ (.equiv (Env.cons t u) w ho)
  /-- Eq1 (BC14 Fig. 2). -/
  | equivEqSelf {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {τ : Ty B}
      (t : FTerm D Γ τ) (u : Vec D Γ τs) (ho : Ty.IndistOrder (.bool :: τs)) :
      Derivation D enc Θ (.equiv (Env.cons (FTerm.eq t t) u) (Env.cons FTerm.tt u) ho)
  /-- Perm (BC14 Fig. 2): reindexing both vectors. -/
  | equivRename {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs τs' : List (Ty B)}
      {u v : Vec D Γ τs} {ho : Ty.IndistOrder τs} (r : Renaming τs' τs) :
      Derivation D enc Θ (.equiv u v ho) →
      Derivation D enc Θ (.equiv (Env.rename r u) (Env.rename r v) (ho.rename r))
  /-- Name renaming along a bijection of names, for a closed vector. -/
  | equivRenameNames {Θ : List (Form D [])} {τs : List (Ty B)}
      (π : ∀ {a b : Ty B}, D.Name a b ≃ D.Name a b) (u : Vec D [] τs) (ho : Ty.IndistOrder τs) :
      Derivation D enc Θ (.equiv u (u.renameNames fun n => π n) ho)
  /-- Encryption from one-time IND-CPA, at an admitted instance whose syntactic side conditions
  hold. -/
  | equivEnc {Θ : List (Form D [])} (e : EncInstance D) : enc e → e.Syntactic →
      Derivation D enc Θ (.equiv (e.E.challenge e.m₀ e.u) (e.E.challenge e.m₁ e.u) e.order)

variable {D : Decl B} {enc : EncInstance D → Prop}

/-- **Soundness.** Every derivation is valid over every model restriction `R` and against every
class of machines `C` under which the admitted encryption instances meet their semantic
hypotheses. -/
theorem Derivation.sound (R : Model D → Prop) (C : ∀ M : Model D, AdvClass M)
    (henc : ∀ e, enc e → e.Holds R C) :
    {Γ : List (Kind B)} → {Θ : List (Form D Γ)} → {F : Form D Γ} → Derivation D enc Θ F →
      Valid R C Θ F
  | _, _, _, .ax h => Valid.ax h
  | _, _, _, .weaken d h => (d.sound R C henc).weaken h
  | _, _, _, .cut d₁ d₂ => (d₁.sound R C henc).cut (d₂.sound R C henc)
  | _, _, _, .allLeft t d => Valid.all_left t (d.sound R C henc)
  | _, _, _, .allRight d => Valid.all_right (d.sound R C henc)
  | _, _, _, .byGlob Γl d => Valid.byGlob Γl (d.sound R C henc)
  | _, _, _, .byLoc d => Valid.byLoc (d.sound R C henc)
  | _, _, _, .localAll Γl d => Valid.local_all Γl (d.sound R C henc)
  | _, _, _, .equivRefl u _ => Valid.equiv_refl u
  | _, _, _, .equivSymm d => (d.sound R C henc).equiv_symm
  | _, _, _, .equivTrans d₁ d₂ => (d₁.sound R C henc).equiv_trans (d₂.sound R C henc)
  | _, _, _, .equivApp d => (d.sound R C henc).equiv_app
  | _, _, _, .equivFn ho f d => Valid.equiv_fn (ho := ho) f (d.sound R C henc)
  | _, _, _, .equivAdv ho d₁ d₂ =>
    Valid.equiv_adv (ho := ho) (d₁.sound R C henc) (d₂.sound R C henc)
  | _, _, _, .equivTail d => (d.sound R C henc).equiv_tail
  | _, _, _, .equivDup d => (d.sound R C henc).equiv_dup
  | _, _, _, .equivIte d => (d.sound R C henc).equiv_ite
  | _, _, _, .equivCaseStudy d₁ d₂ => (d₁.sound R C henc).equiv_caseStudy (d₂.sound R C henc)
  | _, _, _, .equivIf1 d₁ d₂ => (d₁.sound R C henc).equiv_if1 (d₂.sound R C henc)
  | _, _, _, .equivRewrite d₁ d₂ => Valid.equiv_rewrite (d₁.sound R C henc) (d₂.sound R C henc)
  | _, _, _, .equivEqSelf t u _ => Valid.equiv_eq_self t u
  | _, _, _, .equivRename r d => Valid.equiv_rename r (d.sound R C henc)
  | _, _, _, .equivRenameNames π u _ => Valid.equiv_renameNames_of_equiv π u
  | _, _, _, .equivEnc e he hs => e.valid hs (henc e he)

end Interop.Squirrel
