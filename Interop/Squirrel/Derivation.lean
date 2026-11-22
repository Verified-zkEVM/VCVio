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
public import Interop.Squirrel.Rules.Deduce
public import Interop.Squirrel.Rules.FreshL

/-!
# Derivations of global sequents

Derivations in the fragment of the logic proved sound here, as data: each constructor is one rule,
indexed by the context, the hypotheses and the conclusion. Local sequents are unfolded to the
global sequents `Θ ⊢ [∧Γl ⇒ φ]` that they stand for (`LValid`). `Derivation.sound` maps every
derivation to validity over the model restrictions it allows and every class of machines, one rule
lemma per constructor:

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
  fragment;
* the secrecy rules of CCS26 Fig. 3 (Neg1, Neg2, Ineq, Trans, WeakL, WeakR, Rw-Equiv) from
  `Interop.Squirrel.Rules.Secrecy`, with `▷` from `adv` (`dedApps`); Rw-Equiv takes the ground
  type of its right side as a premise;
* deductions from the entries of the vector (`dedInput`), honest symbols (`dedFn`), application
  (`dedApp`) and rewriting under an overwhelming equality (`dedRewrite`), and local reasoning read
  semantically: `boxValid` concludes `[φ]` for a local formula true at every tape of every model
  of `R₀`, which is how equations of honest symbols that `R₀` imposes are used, and `boxMP` is
  modus ponens under `[·]` (`Interop.Squirrel.Rules.Deduce`);
* FreshR and FreshL (CCS26 Fig. 11), for closed terms that do not use the name, a syntactic
  condition that `decide` discharges on concrete terms (`FTerm.AvoidsNames`). FreshR takes the
  label `large` of the name's type.

FreshL is sound only over models with long attacker tapes (`Model.LongTapes`); without them it
fails (`FreshLCountermodel.freshL_needs_longTapes`, in the tests). So derivations carry a
parameter `R₀`, the restriction on models that their rules assume: FreshL's constructor takes as
premises that `R₀` gives long tapes and polynomial bit blocks for the name's type, and that the
terms read the attacker tape below a polynomial in every model of `R₀` and of `Θ`.
`Derivation.sound` holds over every restriction `R` contained in `R₀`. Derivations that use
neither FreshL nor `boxValid` can take `R₀` to be every model.

The rules about `∼`, `⊬` and `▷` hold for every class of machines, because the class is closed
under their reductions by its fields (`AdvClass`). Formulas carry the order bounds of CSF24 and
CCS26 (`Ty.IndistOrder`, `Ty.AdvOrder`, `Ty.SecrecyOrder`). A constructor's conclusion carries the
bound derived from its premises', and a constructor that adds an entry or starts from no premise
takes the conclusion's bound.

## References

* [LICS23] Baelde, Koutsos, Lallemand, *A Higher-Order Indistinguishability Logic for
  Cryptographic Reasoning*, LICS 2023: §III, Figs. 7 and 8, Prop. 19.
* [BC14] Bana, Comon-Lundh, *A Computationally Complete Symbolic Attacker for Equivalence
  Properties*, CCS 2014: Fig. 2, Props. 2 and 3.
* [CSF24] Baelde, Fontaine, Koutsos, Scerri, Vignon, *A Probabilistic Logic for Concrete
  Security*, CSF 2024: App. A.
* [CCS26] Hérouard, Jacomme, Koutsos, Lallemand, *Secrecy in Squirrel and the Post-Compromise
  Security of a Ratchet*, CCS 2026: §3.1, Fig. 3 and Fig. 11.
-/

public section

namespace Interop.Squirrel

open IPFunctor IPFunctor.ScopedSignature

variable {B : Type}

/-- Derivations of `Θ ⊢ F` in the context `Γ`, using the encryption rule at the instances that
`enc` admits, over the models of `R₀`. -/
inductive Derivation (D : Decl B) (enc : EncInstance D → Prop) (R₀ : Model D → Prop) :
    {Γ : List (Kind B)} → List (Form D Γ) → Form D Γ → Type
  /-- G.Axiom. -/
  | ax {Γ : List (Kind B)} {Θ : List (Form D Γ)} {F : Form D Γ} : F ∈ Θ → Derivation D enc R₀ Θ F
  /-- G.Weak. -/
  | weaken {Γ : List (Kind B)} {Θ Θ' : List (Form D Γ)} {F : Form D Γ} :
      Derivation D enc R₀ Θ F → Θ ⊆ Θ' → Derivation D enc R₀ Θ' F
  /-- G.Cut. -/
  | cut {Γ : List (Kind B)} {Θ : List (Form D Γ)} {F F' : Form D Γ} :
      Derivation D enc R₀ Θ F' → Derivation D enc R₀ (F' :: Θ) F → Derivation D enc R₀ Θ F
  /-- G.L-∀̃. -/
  | allLeft {Γ : List (Kind B)} {Θ : List (Form D Γ)} {F : Form D Γ} {τ : Ty B}
      {G : Form D (.loc τ :: Γ)} (t : FTerm D Γ τ) :
      Derivation D enc R₀ (G.substOne t :: Θ) F → Derivation D enc R₀ (.all τ G :: Θ) F
  /-- G.R-∀̃. -/
  | allRight {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τ : Ty B} {G : Form D (.loc τ :: Γ)} :
      Derivation D enc R₀ (Θ.map (Term.weaken · (.loc τ))) G → Derivation D enc R₀ Θ (.all τ G)
  /-- L.ByGlob, with the local sequent unfolded. -/
  | byGlob {Γ : List (Kind B)} {Θ : List (Form D Γ)} {φ : FTerm D Γ .bool}
      (Γl : List (FTerm D Γ .bool)) :
      Derivation D enc R₀ Θ (.box φ) → Derivation D enc R₀ Θ (.box (.imp (.conj Γl) φ))
  /-- G.ByLoc, with the local sequent unfolded. -/
  | byLoc {Γ : List (Kind B)} {Θ : List (Form D Γ)} {φ : FTerm D Γ .bool} :
      Derivation D enc R₀ Θ (.box (.imp (.conj []) φ)) → Derivation D enc R₀ Θ (.box φ)
  /-- L.R-∀, with the local sequents unfolded. -/
  | localAll {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τ : Ty B} {φ : FTerm D (.loc τ :: Γ) .bool}
      (Γl : List (FTerm D Γ .bool)) :
      Derivation D enc R₀ (Θ.map (Term.weaken · (.loc τ)))
        (.box (.imp (.conj (Γl.map (Term.weaken · (.loc τ)))) φ)) →
      Derivation D enc R₀ Θ (.box (.imp (.conj Γl) (FTerm.all φ)))
  /-- Refl. -/
  | equivRefl {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} (u : Vec D Γ τs)
      (ho : Ty.IndistOrder τs) : Derivation D enc R₀ Θ (.equiv u u ho)
  /-- Sym. -/
  | equivSymm {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {u v : Vec D Γ τs}
      {ho : Ty.IndistOrder τs} :
      Derivation D enc R₀ Θ (.equiv u v ho) → Derivation D enc R₀ Θ (.equiv v u ho)
  /-- Trans. -/
  | equivTrans {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)}
      {u v w : Vec D Γ τs} {ho : Ty.IndistOrder τs} :
      Derivation D enc R₀ Θ (.equiv u v ho) → Derivation D enc R₀ Θ (.equiv v w ho) →
      Derivation D enc R₀ Θ (.equiv u w ho)
  /-- G.Equiv:FA-App. -/
  | equivApp {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {u v : Vec D Γ τs}
      {a b : Ty B} {t s : FTerm D Γ (.arrow a b)} {t' s' : FTerm D Γ a}
      {ho : Ty.IndistOrder (.arrow a b :: a :: τs)} :
      Derivation D enc R₀ Θ
        (.equiv (Env.cons t (Env.cons t' u)) (Env.cons s (Env.cons s' v)) ho) →
      Derivation D enc R₀ Θ
        (.equiv (Env.cons (FTerm.app t t') u) (Env.cons (FTerm.app s s') v) ho.app)
  /-- FA-Fn. -/
  | equivFn {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {u v : Vec D Γ τs}
      {τ : Ty B} (ho : Ty.IndistOrder (τ :: τs)) (f : D.Fn τ) :
      Derivation D enc R₀ Θ (.equiv u v ho.tail) →
      Derivation D enc R₀ Θ (.equiv (Env.cons (FTerm.fn f) u) (Env.cons (FTerm.fn f) v) ho)
  /-- G.Equiv:FA-Adv. -/
  | equivAdv {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {u v : Vec D Γ τs}
      {τs₀ : List (Ty B)} {β : Ty B} {t : FTerm D Γ (Ty.arrows τs₀ β)} {ha : Ty.AdvOrder τs₀ β}
      (ho : Ty.IndistOrder (Ty.arrows τs₀ β :: τs)) :
      Derivation D enc R₀ Θ (.adv t ha) → Derivation D enc R₀ Θ (.equiv u v ho.tail) →
      Derivation D enc R₀ Θ (.equiv (Env.cons t u) (Env.cons t v) ho)
  /-- Restr. -/
  | equivTail {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {u v : Vec D Γ τs}
      {τ : Ty B} {t s : FTerm D Γ τ} {ho : Ty.IndistOrder (τ :: τs)} :
      Derivation D enc R₀ Θ (.equiv (Env.cons t u) (Env.cons s v) ho) →
      Derivation D enc R₀ Θ (.equiv u v ho.tail)
  /-- Dup. -/
  | equivDup {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {u v : Vec D Γ τs}
      {τ : Ty B} {t s : FTerm D Γ τ} {ho : Ty.IndistOrder (τ :: τs)} :
      Derivation D enc R₀ Θ (.equiv (Env.cons t u) (Env.cons s v) ho) →
      Derivation D enc R₀ Θ
        (.equiv (Env.cons t (Env.cons t u)) (Env.cons s (Env.cons s v)) ho.dup)
  /-- If. -/
  | equivIte {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {u v : Vec D Γ τs}
      {a : Ty B} {c c' : FTerm D Γ .bool} {t t' s s' : FTerm D Γ a}
      {ho : Ty.IndistOrder (.bool :: a :: a :: τs)} :
      Derivation D enc R₀ Θ (.equiv (Env.cons c (Env.cons t (Env.cons t' u)))
        (Env.cons c' (Env.cons s (Env.cons s' v))) ho) →
      Derivation D enc R₀ Θ
        (.equiv (Env.cons (FTerm.ite c t t') u) (Env.cons (FTerm.ite c' s s') v) ho.ite)
  /-- G.Case-Study:ITE (LICS23 Fig. 8). -/
  | equivCaseStudy {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)}
      {u v : Vec D Γ τs} {a : Ty B} {c c' : FTerm D Γ .bool} {t t' s s' : FTerm D Γ a}
      {ho : Ty.IndistOrder (.bool :: a :: τs)} :
      Derivation D enc R₀ Θ
        (.equiv (Env.cons c (Env.cons t u)) (Env.cons c' (Env.cons s v)) ho) →
      Derivation D enc R₀ Θ
        (.equiv (Env.cons c (Env.cons t' u)) (Env.cons c' (Env.cons s' v)) ho) →
      Derivation D enc R₀ Θ
        (.equiv (Env.cons (FTerm.ite c t t') u) (Env.cons (FTerm.ite c' s s') v) ho.tail)
  /-- If1 (BC14 Fig. 2). -/
  | equivIf1 {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {u v : Vec D Γ τs}
      {a : Ty B} {c c' : FTerm D Γ .bool} {x y z : FTerm D Γ a}
      {ho : Ty.IndistOrder (.bool :: a :: τs)} :
      Derivation D enc R₀ Θ
        (.equiv (Env.cons c (Env.cons x u)) (Env.cons c' (Env.cons z v)) ho) →
      Derivation D enc R₀ Θ
        (.equiv (Env.cons c (Env.cons y u)) (Env.cons c' (Env.cons z v)) ho) →
      Derivation D enc R₀ Θ (.equiv (Env.cons (FTerm.ite c x y) u) (Env.cons z v) ho.tail)
  /-- Rewriting an entry under an overwhelming equality. -/
  | equivRewrite {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {u : Vec D Γ τs}
      {τ : Ty B} {t t' : FTerm D Γ τ} {w : Vec D Γ (τ :: τs)} {ho : Ty.IndistOrder (τ :: τs)} :
      Derivation D enc R₀ Θ (.box (FTerm.eq t t')) →
      Derivation D enc R₀ Θ (.equiv (Env.cons t' u) w ho) →
      Derivation D enc R₀ Θ (.equiv (Env.cons t u) w ho)
  /-- Eq1 (BC14 Fig. 2). -/
  | equivEqSelf {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {τ : Ty B}
      (t : FTerm D Γ τ) (u : Vec D Γ τs) (ho : Ty.IndistOrder (.bool :: τs)) :
      Derivation D enc R₀ Θ (.equiv (Env.cons (FTerm.eq t t) u) (Env.cons FTerm.tt u) ho)
  /-- Perm (BC14 Fig. 2): reindexing both vectors. -/
  | equivRename {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs τs' : List (Ty B)}
      {u v : Vec D Γ τs} {ho : Ty.IndistOrder τs} (r : Renaming τs' τs) :
      Derivation D enc R₀ Θ (.equiv u v ho) →
      Derivation D enc R₀ Θ (.equiv (Env.rename r u) (Env.rename r v) (ho.rename r))
  /-- Name renaming along a bijection of names, for a closed vector. -/
  | equivRenameNames {Θ : List (Form D [])} {τs : List (Ty B)}
      (π : ∀ {a b : Ty B}, D.Name a b ≃ D.Name a b) (u : Vec D [] τs) (ho : Ty.IndistOrder τs) :
      Derivation D enc R₀ Θ (.equiv u (u.renameNames fun n => π n) ho)
  /-- Encryption from one-time IND-CPA, at an admitted instance whose syntactic side conditions
  hold. -/
  | equivEnc {Θ : List (Form D [])} (e : EncInstance D) : enc e → e.Syntactic →
      Derivation D enc R₀ Θ (.equiv (e.E.challenge e.m₀ e.u) (e.E.challenge e.m₁ e.u) e.order)
  /-- Neg1 (CCS26 Fig. 3). -/
  | notDed {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {β : Ty B}
      {u : Vec D Γ τs} {v : FTerm D Γ β} {ho : Ty.SecrecyOrder τs β} :
      Derivation D enc R₀ Θ (.nonDed u v ho) → Derivation D enc R₀ Θ (.not (.ded u v ho))
  /-- Neg2 (CCS26 Fig. 3). -/
  | notNonDed {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {β : Ty B}
      {u : Vec D Γ τs} {v : FTerm D Γ β} {ho : Ty.SecrecyOrder τs β} :
      Derivation D enc R₀ Θ (.ded u v ho) → Derivation D enc R₀ Θ (.not (.nonDed u v ho))
  /-- Ineq (CCS26 Fig. 3). -/
  | boxNotEq {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {β : Ty B}
      {u : Vec D Γ τs} {v w : FTerm D Γ β} {ho : Ty.SecrecyOrder τs β} :
      Derivation D enc R₀ Θ (.nonDed u v ho) → Derivation D enc R₀ Θ (.ded u w ho) →
      Derivation D enc R₀ Θ (.box (FTerm.not (FTerm.eq v w)))
  /-- Trans (CCS26 Fig. 3). -/
  | dedTrans {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {β γ : Ty B}
      {u : Vec D Γ τs} {v : FTerm D Γ β} {w : FTerm D Γ γ} {ho₁ : Ty.SecrecyOrder τs β}
      {ho₂ : Ty.SecrecyOrder [β] γ} :
      Derivation D enc R₀ Θ (.ded u v ho₁) →
      Derivation D enc R₀ Θ (.ded (Env.cons v Env.empty) w ho₂) →
      Derivation D enc R₀ Θ (.ded u w ⟨ho₁.1, ho₂.2⟩)
  /-- WeakL (CCS26 Fig. 3). -/
  | nonDedWeakL {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {β γ : Ty B}
      {u : Vec D Γ τs} {v : FTerm D Γ β} {w : FTerm D Γ γ} {ho₁ : Ty.SecrecyOrder τs γ}
      {ho₂ : Ty.SecrecyOrder τs β} :
      Derivation D enc R₀ Θ (.nonDed u w ho₁) → Derivation D enc R₀ Θ (.ded u v ho₂) →
      Derivation D enc R₀ Θ (.nonDed (Env.cons v Env.empty) w ⟨.single ho₂.2, ho₁.2⟩)
  /-- WeakR (CCS26 Fig. 3). -/
  | nonDedWeakR {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {β γ : Ty B}
      {u : Vec D Γ τs} {v : FTerm D Γ β} {w : FTerm D Γ γ} {ho₁ : Ty.SecrecyOrder τs β}
      {ho₂ : Ty.SecrecyOrder [γ] β} :
      Derivation D enc R₀ Θ (.nonDed u v ho₁) →
      Derivation D enc R₀ Θ (.ded (Env.cons w Env.empty) v ho₂) →
      Derivation D enc R₀ Θ (.nonDed u w ⟨ho₁.1, ho₂.1.head⟩)
  /-- Rw-Equiv (CCS26 Fig. 3), for a right side of Boolean or base type. -/
  | nonDedRwEquiv {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {β : Ty B}
      {u₁ u₂ : Vec D Γ τs} {v₁ v₂ : FTerm D Γ β} {ho : Ty.SecrecyOrder τs β}
      {hoE : Ty.IndistOrder (τs ++ [β])} : β.IsGround →
      Derivation D enc R₀ Θ (.nonDed u₂ v₂ ho) →
      Derivation D enc R₀ Θ (.equiv (Vec.snoc u₁ v₁) (Vec.snoc u₂ v₂) hoE) →
      Derivation D enc R₀ Θ (.nonDed u₁ v₁ ho)
  /-- `u⃗ ▷ f(u⃗)` from `adv(f)`. -/
  | dedApps {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {β : Ty B}
      {u : Vec D Γ τs} {f : FTerm D Γ (Ty.arrows τs β)} {ha : Ty.AdvOrder τs β}
      (ho : Ty.SecrecyOrder τs β) :
      Derivation D enc R₀ Θ (.adv f ha) → Derivation D enc R₀ Θ (.ded u (FTerm.apps f u) ho)
  /-- `u⃗ ▷ uᵢ`: an entry of order at most one is deducible. -/
  | dedInput {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {τ : Ty B}
      (u : Vec D Γ τs) (y : ScopedVar τs τ) (ho : Ty.SecrecyOrder τs τ) :
      Derivation D enc R₀ Θ (.ded u (u τ y) ho)
  /-- `u⃗ ▷ f`: an honest symbol of order at most one is deducible. -/
  | dedFn {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {τ : Ty B}
      (u : Vec D Γ τs) (f : D.Fn τ) (ho : Ty.SecrecyOrder τs τ) :
      Derivation D enc R₀ Θ (.ded u (FTerm.fn f) ho)
  /-- From `u⃗ ▷ f` and `u⃗ ▷ t`, `u⃗ ▷ f t`. -/
  | dedApp {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {a b : Ty B}
      {u : Vec D Γ τs} {f : FTerm D Γ (.arrow a b)} {t : FTerm D Γ a}
      {hof : Ty.SecrecyOrder τs (.arrow a b)} {hot : Ty.SecrecyOrder τs a}
      (ho : Ty.SecrecyOrder τs b) :
      Derivation D enc R₀ Θ (.ded u f hof) → Derivation D enc R₀ Θ (.ded u t hot) →
      Derivation D enc R₀ Θ (.ded u (FTerm.app f t) ho)
  /-- From `u⃗ ▷ v` and `[v = v']`, `u⃗ ▷ v'`. -/
  | dedRewrite {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {β : Ty B}
      {u : Vec D Γ τs} {v v' : FTerm D Γ β} {ho : Ty.SecrecyOrder τs β} :
      Derivation D enc R₀ Θ (.ded u v ho) → Derivation D enc R₀ Θ (.box (FTerm.eq v v')) →
      Derivation D enc R₀ Θ (.ded u v' ho)
  /-- `[φ]` for a local formula true at every tape of every model of `R₀`: local reasoning, read
  semantically. -/
  | boxValid {Γ : List (Kind B)} {Θ : List (Form D Γ)} (φ : FTerm D Γ .bool) :
      (∀ M : Model D, M.RespectsLabels → R₀ M → ∀ (C : AdvClass M) env η ρ,
        φ.denote (fullInterp M C) env η ρ = true) →
      Derivation D enc R₀ Θ (.box φ)
  /-- Modus ponens under `[·]`: from `[φ]` and `[φ ⇒ ψ]`, `[ψ]`. -/
  | boxMP {Γ : List (Kind B)} {Θ : List (Form D Γ)} {φ ψ : FTerm D Γ .bool} :
      Derivation D enc R₀ Θ (.box φ) → Derivation D enc R₀ Θ (.box (FTerm.imp φ ψ)) →
      Derivation D enc R₀ Θ (.box ψ)
  /-- FreshR (CCS26 Fig. 11), for a closed vector that does not use the name. -/
  | nonDedFreshR {Θ : List (Form D [])} {τs : List (Ty B)} {a b : Ty B} (u : Vec D [] τs)
      (n : D.Name a b) (i : D.Fn a) (ho : Ty.SecrecyOrder τs b) : b.HasLabel D.labels .large →
      u.AvoidsNames (· = ⟨a, b, n⟩) →
      Derivation D enc R₀ Θ (.nonDed u (FTerm.name n (FTerm.fn i)) ho)
  /-- FreshL (CCS26 Fig. 11), for closed terms that do not use the name, over models where `R₀`
  gives long attacker tapes and polynomial bit blocks for names of type `b`: the terms read the
  attacker tape below a polynomial in every model of `R₀` and of `Θ`. -/
  | nonDedFreshL {Θ : List (Form D [])} {τs : List (Ty B)} {a b β : Ty B} {u : Vec D [] τs}
      {v : FTerm D [] β} {ho : Ty.SecrecyOrder τs β} (ho' : Ty.SecrecyOrder (τs ++ [b]) β)
      (n : D.Name a b) (i : D.Fn a) :
      (∀ M, R₀ M → M.LongTapes ∧ M.PolyCoins b) →
      (∀ M : Model D, M.RespectsLabels → R₀ M → ∀ (C : AdvClass M) env,
        (∀ θ ∈ Θ, θ.Holds M C env) → u.ReadsPoly M C env ∧ v.ReadsPoly M C env) →
      u.AvoidsNames (· = ⟨a, b, n⟩) → v.AvoidsNames (· = ⟨a, b, n⟩) →
      Derivation D enc R₀ Θ (.nonDed u v ho) →
      Derivation D enc R₀ Θ (.nonDed (Vec.snoc u (FTerm.name n (FTerm.fn i))) v ho')

variable {D : Decl B} {enc : EncInstance D → Prop} {R₀ : Model D → Prop}

/-- **Soundness.** Every derivation is valid over every model restriction `R` contained in `R₀`
and against every class of machines `C` under which the admitted encryption instances meet their
semantic hypotheses. -/
theorem Derivation.sound (R : Model D → Prop) (C : ∀ M : Model D, AdvClass M)
    (henc : ∀ e, enc e → e.Holds R C) (hR : ∀ M, R M → R₀ M) :
    {Γ : List (Kind B)} → {Θ : List (Form D Γ)} → {F : Form D Γ} → Derivation D enc R₀ Θ F →
      Valid R C Θ F
  | _, _, _, .ax h => Valid.ax h
  | _, _, _, .weaken d h => (d.sound R C henc hR).weaken h
  | _, _, _, .cut d₁ d₂ => (d₁.sound R C henc hR).cut (d₂.sound R C henc hR)
  | _, _, _, .allLeft t d => Valid.all_left t (d.sound R C henc hR)
  | _, _, _, .allRight d => Valid.all_right (d.sound R C henc hR)
  | _, _, _, .byGlob Γl d => Valid.byGlob Γl (d.sound R C henc hR)
  | _, _, _, .byLoc d => Valid.byLoc (d.sound R C henc hR)
  | _, _, _, .localAll Γl d => Valid.local_all Γl (d.sound R C henc hR)
  | _, _, _, .equivRefl u _ => Valid.equiv_refl u
  | _, _, _, .equivSymm d => (d.sound R C henc hR).equiv_symm
  | _, _, _, .equivTrans d₁ d₂ => (d₁.sound R C henc hR).equiv_trans (d₂.sound R C henc hR)
  | _, _, _, .equivApp d => (d.sound R C henc hR).equiv_app
  | _, _, _, .equivFn ho f d => Valid.equiv_fn (ho := ho) f (d.sound R C henc hR)
  | _, _, _, .equivAdv ho d₁ d₂ =>
    Valid.equiv_adv (ho := ho) (d₁.sound R C henc hR) (d₂.sound R C henc hR)
  | _, _, _, .equivTail d => (d.sound R C henc hR).equiv_tail
  | _, _, _, .equivDup d => (d.sound R C henc hR).equiv_dup
  | _, _, _, .equivIte d => (d.sound R C henc hR).equiv_ite
  | _, _, _, .equivCaseStudy d₁ d₂ =>
    (d₁.sound R C henc hR).equiv_caseStudy (d₂.sound R C henc hR)
  | _, _, _, .equivIf1 d₁ d₂ => (d₁.sound R C henc hR).equiv_if1 (d₂.sound R C henc hR)
  | _, _, _, .equivRewrite d₁ d₂ =>
    Valid.equiv_rewrite (d₁.sound R C henc hR) (d₂.sound R C henc hR)
  | _, _, _, .equivEqSelf t u _ => Valid.equiv_eq_self t u
  | _, _, _, .equivRename r d => Valid.equiv_rename r (d.sound R C henc hR)
  | _, _, _, .equivRenameNames π u _ => Valid.equiv_renameNames_of_equiv π u
  | _, _, _, .equivEnc e he hs => e.valid hs (henc e he)
  | _, _, _, .notDed d => Valid.not_ded (d.sound R C henc hR)
  | _, _, _, .notNonDed d => Valid.not_nonDed (d.sound R C henc hR)
  | _, _, _, .boxNotEq d₁ d₂ => Valid.box_not_eq (d₁.sound R C henc hR) (d₂.sound R C henc hR)
  | _, _, _, .dedTrans d₁ d₂ => Valid.ded_trans (d₁.sound R C henc hR) (d₂.sound R C henc hR)
  | _, _, _, .nonDedWeakL d₁ d₂ =>
    Valid.nonDed_weakL (d₁.sound R C henc hR) (d₂.sound R C henc hR)
  | _, _, _, .nonDedWeakR d₁ d₂ =>
    Valid.nonDed_weakR (d₁.sound R C henc hR) (d₂.sound R C henc hR)
  | _, _, _, .nonDedRwEquiv hβ d₁ d₂ =>
    Valid.nonDed_rwEquiv hβ (d₁.sound R C henc hR) (d₂.sound R C henc hR)
  | _, _, _, .dedApps _ d => Valid.ded_apps (d.sound R C henc hR)
  | _, _, _, .dedInput _ y _ => Valid.ded_input y
  | _, _, _, .dedFn _ f _ => Valid.ded_fn f
  | _, _, _, .dedApp _ d₁ d₂ => Valid.ded_app (d₁.sound R C henc hR) (d₂.sound R C henc hR)
  | _, _, _, .dedRewrite d₁ d₂ =>
    Valid.ded_rewrite (d₁.sound R C henc hR) (d₂.sound R C henc hR)
  | _, _, _, .boxValid _ h =>
    Valid.box_valid fun M hl hRM env η ρ => h M hl (hR M hRM) (C M) env η ρ
  | _, _, _, .boxMP d₁ d₂ => Valid.box_mp (d₁.sound R C henc hR) (d₂.sound R C henc hR)
  | _, _, _, .nonDedFreshR _ n i _ hl hf => Valid.nonDed_freshR n i hl hf
  | _, _, _, .nonDedFreshL _ n i hl hr hfu hfv d =>
    Valid.nonDed_freshL n i (fun M hRM => hl M (hR M hRM))
      (fun M hlM hRM env hΘ => hr M hlM (hR M hRM) (C M) env hΘ) hfu hfv (d.sound R C henc hR)

end Interop.Squirrel
