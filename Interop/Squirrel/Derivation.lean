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
public import Interop.Squirrel.Rules.Oracle
public import Interop.Squirrel.Rules.PRF
public import Interop.Squirrel.Rules.PRFLeft

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
  instance (`EncInstance.Holds`). With `enc` empty, derivations use the other rules only;
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
  label `large` of the name's type;
* Rw-Oracle as CCS26's double rule (`nonDedRwOracle`, App. C.1), whose agreement premise deduces
  from `u⃗, o_β` for `o_β` one of the two oracles, and Pc-Oracle (`nonDedPcOracle`), for oracles
  with a Boolean or base argument type and a right side of Boolean or base type. CCS26 derives
  Pc-Oracle from the double rule by concluding the agreement premise with Ineq under the
  hypothesis `u⃗, o′ ▷ m`, which the fragment has no rule to introduce, so it is a constructor of
  its own (`Valid.nonDed_pcOracle` is that derivation, read semantically);
* G.PRF without an oracle on the left (`equivPRF`), at the instances that the parameter `prf`
  admits (`PRFRule`), with its syntactic side conditions (`PRFInstance.Syntactic`: `ψ_key`,
  `⊢pptm`, first order, Boolean or base types, and a fresh name, which `decide` discharges on
  concrete instances) and `[ψ_msg]` as premises. `Derivation.sound` takes the semantic hypotheses
  of each admitted instance (`PRFRule.Holds`: uniform names of the hash type, and the PRF
  assumption for the named reductions of the admitted machines). PRF-Simple is derived from
  G.PRF, Perm, FreshL and Rw-Equiv as CCS26 derives it (`Derivation.nonDedPRF`), so it is not a
  constructor;
* PRF.R and PRF.L-sec (CCS26 Fig. 4 and §2.3), with the hash oracle on the left (`nonDedPRFR`,
  `nonDedPRFLSec`), at the instances that `prf` admits, with their syntactic side conditions
  (`PRFRInstance.Syntactic`, `PRFLInstance.Syntactic`) and their `[ψ_msg]` as premises.
  `Derivation.sound` takes the PRF assumption of each admitted instance for its named reductions
  (`PRFRule.Holds`: `PRFSymbols.rightReduction`, one per candidate; `PRFSymbols.leftReduction` and
  `PRFSymbols.leftFreshReduction`).

FreshL is sound only over models with long attacker tapes (`Model.LongTapes`); without them it
fails (`FreshLCountermodel.freshL_needs_longTapes`, in the tests). So derivations carry a
parameter `R₀`, the restriction on models that their rules assume: FreshL's constructor takes as
premises that `R₀` gives long tapes and polynomial bit blocks for the name's type, and that the
terms read the attacker tape below a polynomial in every model of `R₀` and of `Θ`. The guess of
Rw-Oracle and Pc-Oracle draws its position from the attacker tape as FreshL draws its name, so
their constructors take the same premises, with polynomial bit blocks for the oracles' argument
type, from which the guess draws its default. PRF.R and PRF.L-sec use the same guess against
their premises on the message, and PRF.L-sec reads its fresh draw from the attacker tape, so their
constructors take that `R₀` gives uniform names of the hash type, long tapes and polynomial bit
blocks for messages (and for hashes, PRF.L-sec), with the read bounds of their terms.
`Derivation.sound` holds over every restriction `R` contained in `R₀`. Derivations that use none
of FreshL, Rw-Oracle, Pc-Oracle, PRF.R, PRF.L-sec and `boxValid` can take `R₀` to be every
model.

The rules about `∼`, `⊬` and `▷` hold for every class of machines, because the class is closed
under their reductions by its fields (`AdvClass`). Formulas carry the order bounds of CSF24 and
CCS26 (`Ty.IndistOrder`, `Ty.AdvOrder`, `Ty.SecrecyOrder`). A constructor's conclusion carries the
bound derived from its premises', and a constructor that adds an entry or starts from no premise
takes the conclusion's bound.

## References

* [LICS23] Baelde, Koutsos, Lallemand, *A Higher-Order Indistinguishability Logic for
  Cryptographic Reasoning*, LICS 2023: §III, Figs. 7 and 8, Prop. 19, and the rule G.PRF.
* [BC14] Bana, Comon-Lundh, *A Computationally Complete Symbolic Attacker for Equivalence
  Properties*, CCS 2014: Fig. 2, Props. 2 and 3.
* [CSF24] Baelde, Fontaine, Koutsos, Scerri, Vignon, *A Probabilistic Logic for Concrete
  Security*, CSF 2024: App. A.
* [CCS26] Hérouard, Jacomme, Koutsos, Lallemand, *Secrecy in Squirrel and the Post-Compromise
  Security of a Ratchet*, CCS 2026: §2.3, §3.1, Fig. 3, Fig. 4, Fig. 11, p. 17 and App. C.
-/

public section

namespace Interop.Squirrel

open IPFunctor IPFunctor.ScopedSignature

variable {B : Type}

/-- The instances of the PRF rules that a derivation may use: G.PRF, PRF.R and PRF.L-sec. -/
inductive PRFRule (D : Decl B) where
  /-- An instance of G.PRF. -/
  | gprf (e : PRFInstance D)
  /-- An instance of PRF.R. -/
  | right (e : PRFRInstance D)
  /-- An instance of PRF.L-sec. -/
  | left (e : PRFLInstance D)

/-- The semantic hypotheses of an instance of a PRF rule. -/
@[expose] def PRFRule.Holds {D : Decl B} : PRFRule D → (Model D → Prop) →
    (∀ M : Model D, AdvClass M) → Prop
  | .gprf e, R, C => e.Holds R C
  | .right e, R, C => e.Holds R C
  | .left e, R, C => e.Holds R C

/-- Derivations of `Θ ⊢ F` in the context `Γ`, using the encryption rule at the instances that
`enc` admits and the PRF rules at the instances that `prf` admits, over the models of `R₀`. -/
inductive Derivation (D : Decl B) (enc : EncInstance D → Prop) (prf : PRFRule D → Prop)
    (R₀ : Model D → Prop) :
    {Γ : List (Kind B)} → List (Form D Γ) → Form D Γ → Type
  /-- G.Axiom. -/
  | ax {Γ : List (Kind B)} {Θ : List (Form D Γ)} {F : Form D Γ} :
      F ∈ Θ → Derivation D enc prf R₀ Θ F
  /-- G.Weak. -/
  | weaken {Γ : List (Kind B)} {Θ Θ' : List (Form D Γ)} {F : Form D Γ} :
      Derivation D enc prf R₀ Θ F → Θ ⊆ Θ' → Derivation D enc prf R₀ Θ' F
  /-- G.Cut. -/
  | cut {Γ : List (Kind B)} {Θ : List (Form D Γ)} {F F' : Form D Γ} :
      Derivation D enc prf R₀ Θ F' → Derivation D enc prf R₀ (F' :: Θ) F →
      Derivation D enc prf R₀ Θ F
  /-- G.L-∀̃. -/
  | allLeft {Γ : List (Kind B)} {Θ : List (Form D Γ)} {F : Form D Γ} {τ : Ty B}
      {G : Form D (.loc τ :: Γ)} (t : FTerm D Γ τ) :
      Derivation D enc prf R₀ (G.substOne t :: Θ) F → Derivation D enc prf R₀ (.all τ G :: Θ) F
  /-- G.R-∀̃. -/
  | allRight {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τ : Ty B} {G : Form D (.loc τ :: Γ)} :
      Derivation D enc prf R₀ (Θ.map (Term.weaken · (.loc τ))) G →
      Derivation D enc prf R₀ Θ (.all τ G)
  /-- L.ByGlob, with the local sequent unfolded. -/
  | byGlob {Γ : List (Kind B)} {Θ : List (Form D Γ)} {φ : FTerm D Γ .bool}
      (Γl : List (FTerm D Γ .bool)) :
      Derivation D enc prf R₀ Θ (.box φ) → Derivation D enc prf R₀ Θ (.box (.imp (.conj Γl) φ))
  /-- G.ByLoc, with the local sequent unfolded. -/
  | byLoc {Γ : List (Kind B)} {Θ : List (Form D Γ)} {φ : FTerm D Γ .bool} :
      Derivation D enc prf R₀ Θ (.box (.imp (.conj []) φ)) → Derivation D enc prf R₀ Θ (.box φ)
  /-- L.R-∀, with the local sequents unfolded. -/
  | localAll {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τ : Ty B} {φ : FTerm D (.loc τ :: Γ) .bool}
      (Γl : List (FTerm D Γ .bool)) :
      Derivation D enc prf R₀ (Θ.map (Term.weaken · (.loc τ)))
        (.box (.imp (.conj (Γl.map (Term.weaken · (.loc τ)))) φ)) →
      Derivation D enc prf R₀ Θ (.box (.imp (.conj Γl) (FTerm.all φ)))
  /-- Refl. -/
  | equivRefl {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} (u : Vec D Γ τs)
      (ho : Ty.IndistOrder τs) : Derivation D enc prf R₀ Θ (.equiv u u ho)
  /-- Sym. -/
  | equivSymm {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {u v : Vec D Γ τs}
      {ho : Ty.IndistOrder τs} :
      Derivation D enc prf R₀ Θ (.equiv u v ho) → Derivation D enc prf R₀ Θ (.equiv v u ho)
  /-- Trans. -/
  | equivTrans {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)}
      {u v w : Vec D Γ τs} {ho : Ty.IndistOrder τs} :
      Derivation D enc prf R₀ Θ (.equiv u v ho) → Derivation D enc prf R₀ Θ (.equiv v w ho) →
      Derivation D enc prf R₀ Θ (.equiv u w ho)
  /-- G.Equiv:FA-App. -/
  | equivApp {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {u v : Vec D Γ τs}
      {a b : Ty B} {t s : FTerm D Γ (.arrow a b)} {t' s' : FTerm D Γ a}
      {ho : Ty.IndistOrder (.arrow a b :: a :: τs)} :
      Derivation D enc prf R₀ Θ
        (.equiv (Env.cons t (Env.cons t' u)) (Env.cons s (Env.cons s' v)) ho) →
      Derivation D enc prf R₀ Θ
        (.equiv (Env.cons (FTerm.app t t') u) (Env.cons (FTerm.app s s') v) ho.app)
  /-- FA-Fn. -/
  | equivFn {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {u v : Vec D Γ τs}
      {τ : Ty B} (ho : Ty.IndistOrder (τ :: τs)) (f : D.Fn τ) :
      Derivation D enc prf R₀ Θ (.equiv u v ho.tail) →
      Derivation D enc prf R₀ Θ (.equiv (Env.cons (FTerm.fn f) u) (Env.cons (FTerm.fn f) v) ho)
  /-- G.Equiv:FA-Adv. -/
  | equivAdv {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {u v : Vec D Γ τs}
      {τs₀ : List (Ty B)} {β : Ty B} {t : FTerm D Γ (Ty.arrows τs₀ β)} {ha : Ty.AdvOrder τs₀ β}
      (ho : Ty.IndistOrder (Ty.arrows τs₀ β :: τs)) :
      Derivation D enc prf R₀ Θ (.adv t ha) → Derivation D enc prf R₀ Θ (.equiv u v ho.tail) →
      Derivation D enc prf R₀ Θ (.equiv (Env.cons t u) (Env.cons t v) ho)
  /-- Restr. -/
  | equivTail {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {u v : Vec D Γ τs}
      {τ : Ty B} {t s : FTerm D Γ τ} {ho : Ty.IndistOrder (τ :: τs)} :
      Derivation D enc prf R₀ Θ (.equiv (Env.cons t u) (Env.cons s v) ho) →
      Derivation D enc prf R₀ Θ (.equiv u v ho.tail)
  /-- Dup. -/
  | equivDup {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {u v : Vec D Γ τs}
      {τ : Ty B} {t s : FTerm D Γ τ} {ho : Ty.IndistOrder (τ :: τs)} :
      Derivation D enc prf R₀ Θ (.equiv (Env.cons t u) (Env.cons s v) ho) →
      Derivation D enc prf R₀ Θ
        (.equiv (Env.cons t (Env.cons t u)) (Env.cons s (Env.cons s v)) ho.dup)
  /-- If. -/
  | equivIte {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {u v : Vec D Γ τs}
      {a : Ty B} {c c' : FTerm D Γ .bool} {t t' s s' : FTerm D Γ a}
      {ho : Ty.IndistOrder (.bool :: a :: a :: τs)} :
      Derivation D enc prf R₀ Θ (.equiv (Env.cons c (Env.cons t (Env.cons t' u)))
        (Env.cons c' (Env.cons s (Env.cons s' v))) ho) →
      Derivation D enc prf R₀ Θ
        (.equiv (Env.cons (FTerm.ite c t t') u) (Env.cons (FTerm.ite c' s s') v) ho.ite)
  /-- G.Case-Study:ITE (LICS23 Fig. 8). -/
  | equivCaseStudy {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)}
      {u v : Vec D Γ τs} {a : Ty B} {c c' : FTerm D Γ .bool} {t t' s s' : FTerm D Γ a}
      {ho : Ty.IndistOrder (.bool :: a :: τs)} :
      Derivation D enc prf R₀ Θ
        (.equiv (Env.cons c (Env.cons t u)) (Env.cons c' (Env.cons s v)) ho) →
      Derivation D enc prf R₀ Θ
        (.equiv (Env.cons c (Env.cons t' u)) (Env.cons c' (Env.cons s' v)) ho) →
      Derivation D enc prf R₀ Θ
        (.equiv (Env.cons (FTerm.ite c t t') u) (Env.cons (FTerm.ite c' s s') v) ho.tail)
  /-- If1 (BC14 Fig. 2). -/
  | equivIf1 {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {u v : Vec D Γ τs}
      {a : Ty B} {c c' : FTerm D Γ .bool} {x y z : FTerm D Γ a}
      {ho : Ty.IndistOrder (.bool :: a :: τs)} :
      Derivation D enc prf R₀ Θ
        (.equiv (Env.cons c (Env.cons x u)) (Env.cons c' (Env.cons z v)) ho) →
      Derivation D enc prf R₀ Θ
        (.equiv (Env.cons c (Env.cons y u)) (Env.cons c' (Env.cons z v)) ho) →
      Derivation D enc prf R₀ Θ (.equiv (Env.cons (FTerm.ite c x y) u) (Env.cons z v) ho.tail)
  /-- Rewriting an entry under an overwhelming equality. -/
  | equivRewrite {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {u : Vec D Γ τs}
      {τ : Ty B} {t t' : FTerm D Γ τ} {w : Vec D Γ (τ :: τs)} {ho : Ty.IndistOrder (τ :: τs)} :
      Derivation D enc prf R₀ Θ (.box (FTerm.eq t t')) →
      Derivation D enc prf R₀ Θ (.equiv (Env.cons t' u) w ho) →
      Derivation D enc prf R₀ Θ (.equiv (Env.cons t u) w ho)
  /-- Eq1 (BC14 Fig. 2). -/
  | equivEqSelf {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {τ : Ty B}
      (t : FTerm D Γ τ) (u : Vec D Γ τs) (ho : Ty.IndistOrder (.bool :: τs)) :
      Derivation D enc prf R₀ Θ (.equiv (Env.cons (FTerm.eq t t) u) (Env.cons FTerm.tt u) ho)
  /-- Perm (BC14 Fig. 2): reindexing both vectors. -/
  | equivRename {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs τs' : List (Ty B)}
      {u v : Vec D Γ τs} {ho : Ty.IndistOrder τs} (r : Renaming τs' τs) :
      Derivation D enc prf R₀ Θ (.equiv u v ho) →
      Derivation D enc prf R₀ Θ (.equiv (Env.rename r u) (Env.rename r v) (ho.rename r))
  /-- Name renaming along a bijection of names, for a closed vector. -/
  | equivRenameNames {Θ : List (Form D [])} {τs : List (Ty B)}
      (π : ∀ {a b : Ty B}, D.Name a b ≃ D.Name a b) (u : Vec D [] τs) (ho : Ty.IndistOrder τs) :
      Derivation D enc prf R₀ Θ (.equiv u (u.renameNames fun n => π n) ho)
  /-- Encryption from one-time IND-CPA, at an admitted instance whose syntactic side conditions
  hold. -/
  | equivEnc {Θ : List (Form D [])} (e : EncInstance D) : enc e → e.Syntactic →
      Derivation D enc prf R₀ Θ (.equiv (e.E.challenge e.m₀ e.u) (e.E.challenge e.m₁ e.u) e.order)
  /-- Neg1 (CCS26 Fig. 3). -/
  | notDed {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {β : Ty B}
      {u : Vec D Γ τs} {v : FTerm D Γ β} {ho : Ty.SecrecyOrder τs β} :
      Derivation D enc prf R₀ Θ (.nonDed u v ho) → Derivation D enc prf R₀ Θ (.not (.ded u v ho))
  /-- Neg2 (CCS26 Fig. 3). -/
  | notNonDed {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {β : Ty B}
      {u : Vec D Γ τs} {v : FTerm D Γ β} {ho : Ty.SecrecyOrder τs β} :
      Derivation D enc prf R₀ Θ (.ded u v ho) → Derivation D enc prf R₀ Θ (.not (.nonDed u v ho))
  /-- Ineq (CCS26 Fig. 3). -/
  | boxNotEq {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {β : Ty B}
      {u : Vec D Γ τs} {v w : FTerm D Γ β} {ho : Ty.SecrecyOrder τs β} :
      Derivation D enc prf R₀ Θ (.nonDed u v ho) → Derivation D enc prf R₀ Θ (.ded u w ho) →
      Derivation D enc prf R₀ Θ (.box (FTerm.not (FTerm.eq v w)))
  /-- Trans (CCS26 Fig. 3). -/
  | dedTrans {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {β γ : Ty B}
      {u : Vec D Γ τs} {v : FTerm D Γ β} {w : FTerm D Γ γ} {ho₁ : Ty.SecrecyOrder τs β}
      {ho₂ : Ty.SecrecyOrder [β] γ} :
      Derivation D enc prf R₀ Θ (.ded u v ho₁) →
      Derivation D enc prf R₀ Θ (.ded (Env.cons v Env.empty) w ho₂) →
      Derivation D enc prf R₀ Θ (.ded u w ⟨ho₁.1, ho₂.2⟩)
  /-- WeakL (CCS26 Fig. 3). -/
  | nonDedWeakL {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {β γ : Ty B}
      {u : Vec D Γ τs} {v : FTerm D Γ β} {w : FTerm D Γ γ} {ho₁ : Ty.SecrecyOrder τs γ}
      {ho₂ : Ty.SecrecyOrder τs β} :
      Derivation D enc prf R₀ Θ (.nonDed u w ho₁) → Derivation D enc prf R₀ Θ (.ded u v ho₂) →
      Derivation D enc prf R₀ Θ (.nonDed (Env.cons v Env.empty) w ⟨.single ho₂.2, ho₁.2⟩)
  /-- WeakR (CCS26 Fig. 3). -/
  | nonDedWeakR {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {β γ : Ty B}
      {u : Vec D Γ τs} {v : FTerm D Γ β} {w : FTerm D Γ γ} {ho₁ : Ty.SecrecyOrder τs β}
      {ho₂ : Ty.SecrecyOrder [γ] β} :
      Derivation D enc prf R₀ Θ (.nonDed u v ho₁) →
      Derivation D enc prf R₀ Θ (.ded (Env.cons w Env.empty) v ho₂) →
      Derivation D enc prf R₀ Θ (.nonDed u w ⟨ho₁.1, ho₂.1.head⟩)
  /-- Rw-Equiv (CCS26 Fig. 3), for a right side of Boolean or base type. -/
  | nonDedRwEquiv {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {β : Ty B}
      {u₁ u₂ : Vec D Γ τs} {v₁ v₂ : FTerm D Γ β} {ho : Ty.SecrecyOrder τs β}
      {hoE : Ty.IndistOrder (τs ++ [β])} : β.IsGround →
      Derivation D enc prf R₀ Θ (.nonDed u₂ v₂ ho) →
      Derivation D enc prf R₀ Θ (.equiv (Vec.snoc u₁ v₁) (Vec.snoc u₂ v₂) hoE) →
      Derivation D enc prf R₀ Θ (.nonDed u₁ v₁ ho)
  /-- `u⃗ ▷ f(u⃗)` from `adv(f)`. -/
  | dedApps {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {β : Ty B}
      {u : Vec D Γ τs} {f : FTerm D Γ (Ty.arrows τs β)} {ha : Ty.AdvOrder τs β}
      (ho : Ty.SecrecyOrder τs β) :
      Derivation D enc prf R₀ Θ (.adv f ha) → Derivation D enc prf R₀ Θ (.ded u (FTerm.apps f u) ho)
  /-- `u⃗ ▷ uᵢ`: an entry of order at most one is deducible. -/
  | dedInput {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {τ : Ty B}
      (u : Vec D Γ τs) (y : ScopedVar τs τ) (ho : Ty.SecrecyOrder τs τ) :
      Derivation D enc prf R₀ Θ (.ded u (u τ y) ho)
  /-- `u⃗ ▷ f`: an honest symbol of order at most one is deducible. -/
  | dedFn {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {τ : Ty B}
      (u : Vec D Γ τs) (f : D.Fn τ) (ho : Ty.SecrecyOrder τs τ) :
      Derivation D enc prf R₀ Θ (.ded u (FTerm.fn f) ho)
  /-- From `u⃗ ▷ f` and `u⃗ ▷ t`, `u⃗ ▷ f t`. -/
  | dedApp {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {a b : Ty B}
      {u : Vec D Γ τs} {f : FTerm D Γ (.arrow a b)} {t : FTerm D Γ a}
      {hof : Ty.SecrecyOrder τs (.arrow a b)} {hot : Ty.SecrecyOrder τs a}
      (ho : Ty.SecrecyOrder τs b) :
      Derivation D enc prf R₀ Θ (.ded u f hof) → Derivation D enc prf R₀ Θ (.ded u t hot) →
      Derivation D enc prf R₀ Θ (.ded u (FTerm.app f t) ho)
  /-- From `u⃗ ▷ v` and `[v = v']`, `u⃗ ▷ v'`. -/
  | dedRewrite {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {β : Ty B}
      {u : Vec D Γ τs} {v v' : FTerm D Γ β} {ho : Ty.SecrecyOrder τs β} :
      Derivation D enc prf R₀ Θ (.ded u v ho) → Derivation D enc prf R₀ Θ (.box (FTerm.eq v v')) →
      Derivation D enc prf R₀ Θ (.ded u v' ho)
  /-- `[φ]` for a local formula true at every tape of every model of `R₀`: local reasoning, read
  semantically. -/
  | boxValid {Γ : List (Kind B)} {Θ : List (Form D Γ)} (φ : FTerm D Γ .bool) :
      (∀ M : Model D, M.RespectsLabels → R₀ M → ∀ (C : AdvClass M) env η ρ,
        φ.denote (fullInterp M C) env η ρ = true) →
      Derivation D enc prf R₀ Θ (.box φ)
  /-- Modus ponens under `[·]`: from `[φ]` and `[φ ⇒ ψ]`, `[ψ]`. -/
  | boxMP {Γ : List (Kind B)} {Θ : List (Form D Γ)} {φ ψ : FTerm D Γ .bool} :
      Derivation D enc prf R₀ Θ (.box φ) → Derivation D enc prf R₀ Θ (.box (FTerm.imp φ ψ)) →
      Derivation D enc prf R₀ Θ (.box ψ)
  /-- FreshR (CCS26 Fig. 11), for a closed vector that does not use the name. -/
  | nonDedFreshR {Θ : List (Form D [])} {τs : List (Ty B)} {a b : Ty B} (u : Vec D [] τs)
      (n : D.Name a b) (i : D.Fn a) (ho : Ty.SecrecyOrder τs b) : b.HasLabel D.labels .large →
      u.AvoidsNames (· = ⟨a, b, n⟩) →
      Derivation D enc prf R₀ Θ (.nonDed u (FTerm.name n (FTerm.fn i)) ho)
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
      Derivation D enc prf R₀ Θ (.nonDed u v ho) →
      Derivation D enc prf R₀ Θ (.nonDed (Vec.snoc u (FTerm.name n (FTerm.fn i))) v ho')
  /-- Rw-Oracle as CCS26's double rule (Fig. 3, App. C.1), for oracles with a Boolean or base
  argument type and a right side of Boolean or base type, over models where `R₀` gives long
  attacker tapes and polynomial bit blocks for the argument type: the terms read the attacker
  tape below a polynomial in every model of `R₀` and of `Θ`. -/
  | nonDedRwOracle {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {a b β : Ty B}
      {u : Vec D Γ τs} {o₁ o₂ oβ : FTerm D Γ (.arrow a b)} {v : FTerm D Γ β}
      {ho₂ : Ty.SecrecyOrder (τs ++ [.arrow a b]) β}
      {hd : Ty.SecrecyOrder (τs ++ [.arrow a b]) a} (ho₁ : Ty.SecrecyOrder (τs ++ [.arrow a b]) β)
      (ha : a.IsGround) (hβ : β.IsGround) (hoβ : oβ = o₁ ∨ oβ = o₂) :
      (∀ M, R₀ M → M.LongTapes ∧ M.PolyCoins a) →
      (∀ M : Model D, M.RespectsLabels → R₀ M → ∀ (C : AdvClass M) env,
        (∀ θ ∈ Θ, θ.Holds M C env) →
          u.ReadsPoly M C env ∧ o₁.ReadsPoly M C env ∧ o₂.ReadsPoly M C env) →
      Derivation D enc prf R₀ Θ (.nonDed (Vec.snoc u o₂) v ho₂) →
      Derivation D enc prf R₀ Θ (Form.oracleAgree u oβ o₁ o₂ hd) →
      Derivation D enc prf R₀ Θ (.nonDed (Vec.snoc u o₁) v ho₁)
  /-- Pc-Oracle (CCS26 Fig. 3), under the conditions of Rw-Oracle, with the read bounds of the
  oracle, the point and the new answer. -/
  | nonDedPcOracle {Γ : List (Kind B)} {Θ : List (Form D Γ)} {τs : List (Ty B)} {a b β : Ty B}
      {u : Vec D Γ τs} {o : FTerm D Γ (.arrow a b)} {m : FTerm D Γ a} {w : FTerm D Γ b}
      {v : FTerm D Γ β} {ho₂ : Ty.SecrecyOrder (τs ++ [.arrow a b]) β}
      {hom : Ty.SecrecyOrder (τs ++ [.arrow a b]) a} (ho₁ : Ty.SecrecyOrder (τs ++ [.arrow a b]) β)
      (ha : a.IsGround) (hβ : β.IsGround) :
      (∀ M, R₀ M → M.LongTapes ∧ M.PolyCoins a) →
      (∀ M : Model D, M.RespectsLabels → R₀ M → ∀ (C : AdvClass M) env,
        (∀ θ ∈ Θ, θ.Holds M C env) → u.ReadsPoly M C env ∧ o.ReadsPoly M C env ∧
          m.ReadsPoly M C env ∧ w.ReadsPoly M C env) →
      Derivation D enc prf R₀ Θ (.nonDed (Vec.snoc u (FTerm.puncture o m w)) v ho₂) →
      Derivation D enc prf R₀ Θ (.nonDed (Vec.snoc u (FTerm.puncture o m w)) m hom) →
      Derivation D enc prf R₀ Θ (.nonDed (Vec.snoc u o) v ho₁)
  /-- G.PRF (LICS23; CCS26 Fig. 11), at an admitted instance whose syntactic side conditions hold,
  from `[ψ_msg]`. -/
  | equivPRF {Θ : List (Form D [])} (e : PRFInstance D) : prf (.gprf e) → e.Syntactic →
      Derivation D enc prf R₀ Θ (.box (e.P.psiMsg e.u e.m)) →
      Derivation D enc prf R₀ Θ (.equiv e.lhs e.rhs e.order)
  /-- PRF.R (CCS26 Fig. 4), at an admitted instance whose syntactic side conditions hold, over
  models where `R₀` gives uniform names of the hash type, long attacker tapes and polynomial bit
  blocks for messages, with the read bounds of the terms in every model of `R₀` and of `Θ`, from
  `[ψ_msg^{m,k}(u⃗)]` and `u⃗, o_h^k ⊬ m`. -/
  | nonDedPRFR {Θ : List (Form D [])} (e : PRFRInstance D) : prf (.right e) → e.Syntactic →
      (∀ M, R₀ M → M.UniformSampler e.P.hTy ∧ M.LongTapes ∧ M.PolyCoins e.P.msgTy) →
      (∀ M : Model D, M.RespectsLabels → R₀ M → ∀ (C : AdvClass M) env,
        (∀ θ ∈ Θ, θ.Holds M C env) →
          Vec.ReadsPoly M C (e.P.closeVec e.u) env ∧ FTerm.ReadsPoly M C (e.P.close e.m) env) →
      Derivation D enc prf R₀ Θ (.box (e.P.psiMsgVec e.u e.m)) →
      Derivation D enc prf R₀ Θ (.nonDed e.lhs (e.P.close e.m) e.orderM) →
      Derivation D enc prf R₀ Θ (.nonDed e.lhs (e.P.hashTerm (e.P.close e.m)) e.order)
  /-- PRF.L-sec (CCS26 §2.3 and Fig. 4), at an admitted instance whose syntactic side conditions
  hold, over models where `R₀` gives uniform names of the hash type, long attacker tapes and
  polynomial bit blocks for messages and hashes, with the read bounds of the terms in every model
  of `R₀` and of `Θ`, from `[ψ_msg^{m,k}(u⃗, v, m)]`, `u⃗, o_h^k ⊬ v` and `u⃗, o_h^k ⊬ m`. -/
  | nonDedPRFLSec {Θ : List (Form D [])} (e : PRFLInstance D) : prf (.left e) → e.Syntactic →
      (∀ M, R₀ M → M.UniformSampler e.P.hTy ∧ M.LongTapes ∧ M.PolyCoins e.P.msgTy ∧
        M.PolyCoins e.P.hTy) →
      (∀ M : Model D, M.RespectsLabels → R₀ M → ∀ (C : AdvClass M) env,
        (∀ θ ∈ Θ, θ.Holds M C env) → Vec.ReadsPoly M C (e.P.closeVec e.u) env ∧
          FTerm.ReadsPoly M C (e.P.close e.v) env ∧ FTerm.ReadsPoly M C (e.P.close e.m) env) →
      Derivation D enc prf R₀ Θ (.box (e.P.psiMsg (Env.append e.u (Env.cons e.v Env.empty)) e.m)) →
      Derivation D enc prf R₀ Θ (.nonDed e.lhs (e.P.close e.v) e.order) →
      Derivation D enc prf R₀ Θ (.nonDed e.lhs (e.P.close e.m) e.orderM) →
      Derivation D enc prf R₀ Θ
        (.nonDed (Vec.snoc e.lhs (e.P.hashTerm (e.P.close e.m))) (e.P.close e.v) e.orderC)

variable {D : Decl B} {enc : EncInstance D → Prop} {prf : PRFRule D → Prop}
  {R₀ : Model D → Prop}

/-- **Soundness.** Every derivation is valid over every model restriction `R` contained in `R₀`
and against every class of machines `C` under which the admitted encryption and PRF instances
meet their semantic hypotheses. -/
theorem Derivation.sound (R : Model D → Prop) (C : ∀ M : Model D, AdvClass M)
    (henc : ∀ e, enc e → e.Holds R C) (hprf : ∀ e, prf e → e.Holds R C)
    (hR : ∀ M, R M → R₀ M) :
    {Γ : List (Kind B)} → {Θ : List (Form D Γ)} → {F : Form D Γ} → Derivation D enc prf R₀ Θ F →
      Valid R C Θ F
  | _, _, _, .ax h => Valid.ax h
  | _, _, _, .weaken d h => (d.sound R C henc hprf hR).weaken h
  | _, _, _, .cut d₁ d₂ => (d₁.sound R C henc hprf hR).cut (d₂.sound R C henc hprf hR)
  | _, _, _, .allLeft t d => Valid.all_left t (d.sound R C henc hprf hR)
  | _, _, _, .allRight d => Valid.all_right (d.sound R C henc hprf hR)
  | _, _, _, .byGlob Γl d => Valid.byGlob Γl (d.sound R C henc hprf hR)
  | _, _, _, .byLoc d => Valid.byLoc (d.sound R C henc hprf hR)
  | _, _, _, .localAll Γl d => Valid.local_all Γl (d.sound R C henc hprf hR)
  | _, _, _, .equivRefl u _ => Valid.equiv_refl u
  | _, _, _, .equivSymm d => (d.sound R C henc hprf hR).equiv_symm
  | _, _, _, .equivTrans d₁ d₂ =>
    (d₁.sound R C henc hprf hR).equiv_trans (d₂.sound R C henc hprf hR)
  | _, _, _, .equivApp d => (d.sound R C henc hprf hR).equiv_app
  | _, _, _, .equivFn ho f d => Valid.equiv_fn (ho := ho) f (d.sound R C henc hprf hR)
  | _, _, _, .equivAdv ho d₁ d₂ =>
    Valid.equiv_adv (ho := ho) (d₁.sound R C henc hprf hR) (d₂.sound R C henc hprf hR)
  | _, _, _, .equivTail d => (d.sound R C henc hprf hR).equiv_tail
  | _, _, _, .equivDup d => (d.sound R C henc hprf hR).equiv_dup
  | _, _, _, .equivIte d => (d.sound R C henc hprf hR).equiv_ite
  | _, _, _, .equivCaseStudy d₁ d₂ =>
    (d₁.sound R C henc hprf hR).equiv_caseStudy (d₂.sound R C henc hprf hR)
  | _, _, _, .equivIf1 d₁ d₂ => (d₁.sound R C henc hprf hR).equiv_if1 (d₂.sound R C henc hprf hR)
  | _, _, _, .equivRewrite d₁ d₂ =>
    Valid.equiv_rewrite (d₁.sound R C henc hprf hR) (d₂.sound R C henc hprf hR)
  | _, _, _, .equivEqSelf t u _ => Valid.equiv_eq_self t u
  | _, _, _, .equivRename r d => Valid.equiv_rename r (d.sound R C henc hprf hR)
  | _, _, _, .equivRenameNames π u _ => Valid.equiv_renameNames_of_equiv π u
  | _, _, _, .equivEnc e he hs => e.valid hs (henc e he)
  | _, _, _, .notDed d => Valid.not_ded (d.sound R C henc hprf hR)
  | _, _, _, .notNonDed d => Valid.not_nonDed (d.sound R C henc hprf hR)
  | _, _, _, .boxNotEq d₁ d₂ =>
    Valid.box_not_eq (d₁.sound R C henc hprf hR) (d₂.sound R C henc hprf hR)
  | _, _, _, .dedTrans d₁ d₂ =>
    Valid.ded_trans (d₁.sound R C henc hprf hR) (d₂.sound R C henc hprf hR)
  | _, _, _, .nonDedWeakL d₁ d₂ =>
    Valid.nonDed_weakL (d₁.sound R C henc hprf hR) (d₂.sound R C henc hprf hR)
  | _, _, _, .nonDedWeakR d₁ d₂ =>
    Valid.nonDed_weakR (d₁.sound R C henc hprf hR) (d₂.sound R C henc hprf hR)
  | _, _, _, .nonDedRwEquiv hβ d₁ d₂ =>
    Valid.nonDed_rwEquiv hβ (d₁.sound R C henc hprf hR) (d₂.sound R C henc hprf hR)
  | _, _, _, .dedApps _ d => Valid.ded_apps (d.sound R C henc hprf hR)
  | _, _, _, .dedInput _ y _ => Valid.ded_input y
  | _, _, _, .dedFn _ f _ => Valid.ded_fn f
  | _, _, _, .dedApp _ d₁ d₂ =>
    Valid.ded_app (d₁.sound R C henc hprf hR) (d₂.sound R C henc hprf hR)
  | _, _, _, .dedRewrite d₁ d₂ =>
    Valid.ded_rewrite (d₁.sound R C henc hprf hR) (d₂.sound R C henc hprf hR)
  | _, _, _, .boxValid _ h =>
    Valid.box_valid fun M hl hRM env η ρ => h M hl (hR M hRM) (C M) env η ρ
  | _, _, _, .boxMP d₁ d₂ => Valid.box_mp (d₁.sound R C henc hprf hR) (d₂.sound R C henc hprf hR)
  | _, _, _, .nonDedFreshR _ n i _ hl hf => Valid.nonDed_freshR n i hl hf
  | _, _, _, .nonDedFreshL _ n i hl hr hfu hfv d =>
    Valid.nonDed_freshL n i (fun M hRM => hl M (hR M hRM))
      (fun M hlM hRM env hΘ => hr M hlM (hR M hRM) (C M) env hΘ) hfu hfv (d.sound R C henc hprf hR)
  | _, _, _, .nonDedRwOracle _ ha hβ hoβ hl hr d₁ d₂ =>
    Valid.nonDed_rwOracle_of ha hβ hoβ (fun M hRM => hl M (hR M hRM))
      (fun M hlM hRM env hΘ => hr M hlM (hR M hRM) (C M) env hΘ) (d₁.sound R C henc hprf hR)
      (d₂.sound R C henc hprf hR)
  | _, _, _, .nonDedPcOracle _ ha hβ hl hr d₁ d₂ =>
    Valid.nonDed_pcOracle ha hβ (fun M hRM => hl M (hR M hRM))
      (fun M hlM hRM env hΘ => hr M hlM (hR M hRM) (C M) env hΘ) (d₁.sound R C henc hprf hR)
      (d₂.sound R C henc hprf hR)
  | _, _, _, .equivPRF e he hs d => e.valid hs (hprf _ he) (d.sound R C henc hprf hR)
  | _, _, _, .nonDedPRFR e he hs hl hr d₁ d₂ =>
    e.valid hs (hprf _ he) (fun M hRM => hl M (hR M hRM))
      (fun M hlM hRM env hΘ => hr M hlM (hR M hRM) (C M) env hΘ) (d₁.sound R C henc hprf hR)
      (d₂.sound R C henc hprf hR)
  | _, _, _, .nonDedPRFLSec e he hs hl hr d₁ d₂ d₃ =>
    e.valid hs (hprf _ he) (fun M hRM => hl M (hR M hRM))
      (fun M hlM hRM env hΘ => hr M hlM (hR M hRM) (C M) env hΘ) (d₁.sound R C henc hprf hR)
      (d₂.sound R C henc hprf hR) (d₃.sound R C henc hprf hR)

/-- **PRF-Simple, derived** (CCS26 Fig. 11, p. 17): from a derivation of `u⃗ ⊬ v`, a derivation of
`u⃗, h(m, k) ⊬ v`, through the constructors of G.PRF (at the vector `u⃗, v` and a name `n` of the
hash type), Perm, FreshL and Rw-Equiv, as CCS26 derives it. The side conditions are those of the
three constructors; `Valid.nonDed_prf` is the same derivation, read semantically. -/
def Derivation.nonDedPRF {Θ : List (Form D [])} (P : PRFSymbols D) {τs : List (Ty B)}
    {β : Ty B} (u : OVec P [] τs) (v : OTerm P [] β) (m : OTerm P [] P.msgTy) {a : Ty B}
    (nn : D.Name a P.hTy) (i : D.Fn a) {ho : Ty.SecrecyOrder τs β}
    (ho' : Ty.SecrecyOrder (τs ++ [P.hTy]) β) (hβ : β.IsGround)
    (horder : Ty.IndistOrder ((τs ++ [β]) ++ [P.hTy]))
    (hprf : prf (.gprf ⟨P, τs ++ [β], Env.append u (Env.cons v Env.empty), m, a, nn, i, horder⟩))
    (hs : PRFInstance.Syntactic ⟨P, τs ++ [β], Env.append u (Env.cons v Env.empty), m, a, nn, i,
      horder⟩)
    (hl : ∀ M, R₀ M → M.LongTapes ∧ M.PolyCoins P.hTy)
    (hread : ∀ M : Model D, M.RespectsLabels → R₀ M → ∀ (C : AdvClass M) env,
      (∀ θ ∈ Θ, θ.Holds M C env) →
        Vec.ReadsPoly M C (P.closeVec u) env ∧ FTerm.ReadsPoly M C (P.close v) env)
    (hnu : (P.closeVec u).AvoidsNames (· = ⟨a, P.hTy, nn⟩))
    (hnv : FTerm.AvoidsNames (· = ⟨a, P.hTy, nn⟩) (P.close v))
    (dmsg : Derivation D enc prf R₀ Θ (.box (P.psiMsg (Env.append u (Env.cons v Env.empty)) m)))
    (d : Derivation D enc prf R₀ Θ (.nonDed (P.closeVec u) (P.close v) ho)) :
    Derivation D enc prf R₀ Θ
      (.nonDed (Vec.snoc (P.closeVec u) (P.hashTerm (P.close m))) (P.close v) ho') :=
  let dprf := Derivation.equivPRF (Θ := Θ) _ hprf hs dmsg
  have hlhs : PRFInstance.lhs ⟨P, τs ++ [β], Env.append u (Env.cons v Env.empty), m, a, nn, i,
      horder⟩ = Vec.snoc (Vec.snoc (P.closeVec u) (P.close v)) (P.hashTerm (P.close m)) := by
    rw [PRFInstance.lhs, P.closeVec_append, P.closeVec_single]
    rfl
  have hrhs : PRFInstance.rhs ⟨P, τs ++ [β], Env.append u (Env.cons v Env.empty), m, a, nn, i,
      horder⟩ = Vec.snoc (Vec.snoc (P.closeVec u) (P.close v)) (FTerm.name nn (FTerm.fn i)) := by
    rw [PRFInstance.rhs, P.closeVec_append, P.closeVec_single]
    rfl
  let dperm := Derivation.equivRename (swapLast τs P.hTy β) (hlhs ▸ hrhs ▸ dprf)
  have hperm : ∀ w : FTerm D [] P.hTy,
      Env.rename (swapLast τs P.hTy β) (Vec.snoc (Vec.snoc (P.closeVec u) (P.close v)) w) =
        Vec.snoc (Vec.snoc (P.closeVec u) w) (P.close v) := fun w =>
    rename_swapLast (P.closeVec u) (P.close v) w
  Derivation.nonDedRwEquiv hβ (Derivation.nonDedFreshL ho' nn i hl hread hnu hnv d)
    (hperm _ ▸ hperm _ ▸ dperm)

end Interop.Squirrel
