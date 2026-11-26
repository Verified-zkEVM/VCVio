/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Squirrel.Indist
public import PolyFun.IPFunctor.Scoped.Sum

/-!
# Squirrel's global formulas and sequents

Global formulas (LICS23 §II-C) are first-order formulas whose atoms are about local terms and
whose variables range over random variables. Here they are the terms of sort `glob` of
`fullSig D`, the sum of the local signature and `globalSig B` over the same sorts. A global
quantifier binds a variable of a local sort, so local and global variables share one context, as
in LICS23's environments `E`. Substitution and renaming of global formulas are PolyFun's.

`fullInterp M C` reads local constructors as random variables (`rvInterp`) and global ones as
propositions:

* `[φ]` is `Overwhelming`: over uniform tapes, the probability that `φ` is false is negligible;
* `const t` is `RV.IsConst`;
* `adv t` and `u⃗ ∼ v⃗` are read through `C : AdvClass M` (`Interop.Squirrel.Indist`), a class
  of machines standing for LICS23's polynomial-time machines. The vectors of `∼` are
  environments of terms (`Vec`), so that they are extended by `Env.cons` and reindexed by
  PolyFun's renamings. As in CSF24 and CCS26 (§3.1, p. 6), `adv` applies to terms of order at most
  two and `∼` to vectors of order at most one: the constructors carry these bounds
  (`Ty.AdvOrder`, `Ty.IndistOrder`), which their default argument proves by evaluation for
  concrete types.

`Valid R C Θ F` is the validity of the global sequent `Θ ⊢ F` (LICS23 §III): `F` holds in every
model respecting the labels and the restriction `R`, at every value of the variables, wherever
every formula of `Θ` holds. A local sequent `Θ; Γl ⊢ φ` is `Θ ⊢ [∧Γl ⇒ φ]` (`LValid`).

## Main results

* The rules of LICS23 Fig. 7: `Valid.ax` (G.Axiom), `Valid.weaken` (G.Weak), `Valid.cut`
  (G.Cut), `Valid.all_left` (G.L-∀̃, instantiation by a local term), `Valid.all_right` (G.R-∀̃),
  `Valid.byGlob` (L.ByGlob) and `Valid.byLoc` (G.ByLoc).
* `eval_denote_fullInterp`: local terms inside global formulas, which substitution does not keep
  in the image of `Term.inl`, still mean their pointwise reading at each `(η, ρ)`.
* `FTerm.denote_substOne_apply`: a term with one free variable, closed by a closed term, means
  the open term read at the closed term's value (`FTerm.evalAt`).

## References

* [LICS23] Baelde, Koutsos, Lallemand, *A Higher-Order Indistinguishability Logic for
  Cryptographic Reasoning*, LICS 2023: §II-C, Fig. 2, §III and Fig. 7.
* [CSF24] Baelde, Fontaine, Koutsos, Scerri, Vignon, *A Probabilistic Logic for Concrete
  Security*, CSF 2024: App. A.
* [CCS26] Hérouard, Jacomme, Koutsos, Lallemand, *Secrecy in Squirrel and the Post-Compromise
  Security of a Ratchet*, CCS 2026: §3.1.
-/

public section

namespace Interop.Squirrel

open IPFunctor IPFunctor.ScopedSignature

variable {B : Type} {D : Decl B}

/-! ## Syntax -/

/-- The constructors of global formulas, all at the global sort. -/
inductive GlobalOp (B : Type) : Kind B → Type where
  /-- Truth. -/
  | top : GlobalOp B .glob
  /-- Falsity. -/
  | bot : GlobalOp B .glob
  /-- Conjunction. -/
  | and : GlobalOp B .glob
  /-- Disjunction. -/
  | or : GlobalOp B .glob
  /-- Implication. -/
  | imp : GlobalOp B .glob
  /-- Universal quantification over random variables of a type. -/
  | all (τ : Ty B) : GlobalOp B .glob
  /-- Existential quantification over random variables of a type. -/
  | ex (τ : Ty B) : GlobalOp B .glob
  /-- Overwhelming truth `[φ]` of a local formula. -/
  | box : GlobalOp B .glob
  /-- `const t`: the term is a constant. -/
  | const (τ : Ty B) : GlobalOp B .glob
  /-- `adv t` for a term of type `τ₁ → … → τₙ → β` of order at most two: the attacker computes
  the term. -/
  | adv (τs : List (Ty B)) (β : Ty B) (h : Ty.AdvOrder τs β) : GlobalOp B .glob
  /-- `u⃗ ∼ v⃗` for vectors of terms of the types `τs`, of order at most one. -/
  | equiv (τs : List (Ty B)) (h : Ty.IndistOrder τs) : GlobalOp B .glob

/-- The global constructors. Quantifiers bind one variable of a local sort; `[·]`, `const`,
`adv` and `∼` take local terms; the connectives take global formulas. The arguments of `∼` are
its two sides at each position of the vector. The constructors `adv` and `∼` carry the order
bounds of CSF24 and CCS26 (§3.1, p. 6), so that an atom outside the fragment cannot be written. -/
@[expose, reducible] def globalSig (B : Type) : ScopedSignature (Kind B) where
  Op := GlobalOp B
  Arg o := match o with
    | .top | .bot => Fin 0
    | .and | .or | .imp => Fin 2
    | .all _ | .ex _ | .box | .const _ | .adv _ _ _ => Fin 1
    | .equiv τs _ => Bool × (τ : Ty B) × ScopedVar τs τ
  binders o := match o with
    | .all τ | .ex τ => fun _ => [.loc τ]
    | _ => fun _ => []
  sort o := match o with
    | .top | .bot | .and | .or | .imp | .all _ | .ex _ => fun _ => .glob
    | .box => fun _ => .loc .bool
    | .const τ => fun _ => .loc τ
    | .adv τs β _ => fun _ => .loc (Ty.arrows τs β)
    | .equiv _ _ => fun p => .loc p.2.1

/-- Local and global constructors together. -/
@[expose, reducible] def fullSig (D : Decl B) : ScopedSignature (Kind B) :=
  (localSig D).sum (globalSig B)

/-- Local terms of type `τ` inside global formulas. -/
abbrev FTerm (D : Decl B) (Γ : List (Kind B)) (τ : Ty B) := (fullSig D).Term Γ (.loc τ)

/-- Global formulas. -/
abbrev Form (D : Decl B) (Γ : List (Kind B)) := (fullSig D).Term Γ .glob

namespace FTerm

variable {Γ : List (Kind B)} {a : Ty B}

/-- The conditional. -/
@[expose] def ite (c : FTerm D Γ .bool) (t e : FTerm D Γ a) : FTerm D Γ a :=
  .node (.inl (.ite a)) (Fin.cases c (Fin.cases t fun _ => e))

/-- The constant `true`. -/
@[expose] def tt : FTerm D Γ .bool := .node (.inl .tt) fun p => nomatch p

/-- The constant `false`. -/
@[expose] def ff : FTerm D Γ .bool := .node (.inl .ff) fun p => nomatch p

/-- Local implication. -/
@[expose] def imp (φ ψ : FTerm D Γ .bool) : FTerm D Γ .bool := ite φ ψ tt

/-- Local negation. -/
@[expose] def not (φ : FTerm D Γ .bool) : FTerm D Γ .bool := ite φ ff tt

/-- The conjunction of a list of local formulas; `true` for the empty list. -/
@[expose] def conj : List (FTerm D Γ .bool) → FTerm D Γ .bool
  | [] => tt
  | φ :: φs => ite φ (conj φs) ff

variable {b : Ty B}

/-- Application. -/
@[expose] def app (f : FTerm D Γ (.arrow a b)) (x : FTerm D Γ a) : FTerm D Γ b :=
  .node (.inl (.app a b)) (Fin.cases f fun _ => x)

/-- Abstraction over the nearest variable. -/
@[expose] def lam (body : FTerm D (.loc a :: Γ) b) : FTerm D Γ (.arrow a b) :=
  .node (.inl (.lam a b)) fun _ => body

/-- Local equality `t = u`. -/
@[expose] def eq (t u : FTerm D Γ a) : FTerm D Γ .bool :=
  app (app (.node (.inl (.eq a)) fun p => nomatch p) t) u

/-- Local universal quantification `∀ (x : a). φ`, as `∀_a (λ x. φ)`. -/
@[expose] def all (φ : FTerm D (.loc a :: Γ) .bool) : FTerm D Γ .bool :=
  app (.node (.inl (.all a)) fun p => nomatch p) (lam φ)

/-- An honest function symbol. -/
@[expose] def fn (f : D.Fn a) : FTerm D Γ a := .node (.inl (.fn f)) fun p => nomatch p

/-- A name applied to an index. -/
@[expose] def name (n : D.Name a b) (i : FTerm D Γ a) : FTerm D Γ b :=
  app (.node (.inl (.name n)) fun p => nomatch p) i

/-- An attacker function symbol. -/
@[expose] def att (f : D.Att) : FTerm D Γ (D.attTy f) := .node (.inl (.att f)) fun p => nomatch p

end FTerm

/-- Vectors of local terms of the types `τs`, as environments. -/
abbrev Vec (D : Decl B) (Γ : List (Kind B)) (τs : List (Ty B)) :=
  Env (fun τ => FTerm D Γ τ) τs

namespace Form

variable {Γ : List (Kind B)} {τ : Ty B}

/-- Overwhelming truth `[φ]`. -/
@[expose] def box (φ : FTerm D Γ .bool) : Form D Γ := .node (.inr .box) fun _ => φ

/-- Global implication. -/
@[expose] def imp (F G : Form D Γ) : Form D Γ := .node (.inr .imp) (Fin.cases F fun _ => G)

/-- Global universal quantification over random variables of type `τ`. -/
@[expose] def all (τ : Ty B) (F : Form D (.loc τ :: Γ)) : Form D Γ :=
  .node (.inr (.all τ)) fun _ => F

/-- Global conjunction. -/
@[expose] def and (F G : Form D Γ) : Form D Γ := .node (.inr .and) (Fin.cases F fun _ => G)

/-- Falsity. -/
@[expose] def bot : Form D Γ := .node (.inr .bot) fun p => nomatch p

/-- Global negation, `F ⇒ ⊥`. -/
@[expose] def not (F : Form D Γ) : Form D Γ := imp F bot

/-- Global existential quantification over random variables of type `τ`. -/
@[expose] def ex (τ : Ty B) (F : Form D (.loc τ :: Γ)) : Form D Γ :=
  .node (.inr (.ex τ)) fun _ => F

/-- `const t`. -/
@[expose] def const (t : FTerm D Γ τ) : Form D Γ := .node (.inr (.const τ)) fun _ => t

/-- `adv t`, for a term of type `τ₁ → … → τₙ → β` of order at most two. -/
@[expose] def adv {τs : List (Ty B)} {β : Ty B} (t : FTerm D Γ (Ty.arrows τs β))
    (h : Ty.AdvOrder τs β := by exact of_decide_eq_true rfl) : Form D Γ :=
  .node (.inr (.adv τs β h)) fun _ => t

/-- `u⃗ ∼ v⃗`, for vectors of order at most one. -/
@[expose] def equiv {τs : List (Ty B)} (u v : Vec D Γ τs)
    (h : Ty.IndistOrder τs := by exact of_decide_eq_true rfl) : Form D Γ :=
  .node (.inr (.equiv τs h)) fun p => bif p.1 then v _ p.2.2 else u _ p.2.2

end Form

/-! ## Atoms -/

/-- Overwhelming truth (LICS23 Fig. 2, `[φ]`): over uniform tapes, the probability that the
Boolean random variable `φ` is false is negligible in the security parameter. -/
@[expose] def Overwhelming (T : TapeModel) (φ : (η : ℕ) → T.Tape η → Bool) : Prop :=
  negligible fun η => Pr{let ρ ← $ᵗ (T.Tape η)}[φ η ρ = false]

/-- A Boolean random variable that is false only where an overwhelming one is false is
overwhelming. -/
theorem Overwhelming.mono {T : TapeModel} {φ ψ : (η : ℕ) → T.Tape η → Bool}
    (h : ∀ η ρ, ψ η ρ = false → φ η ρ = false) (hφ : Overwhelming T φ) : Overwhelming T ψ :=
  negligible_of_le (fun η => prEvent_mono _ _ _ (h η)) hφ

/-- Two values of a type, at two security parameters, are the same value. At base types this is
equality of bitstrings; at arrow types it is read as a logical relation. -/
@[expose] def Ty.Same (carrier : B → ℕ → Set (List Bool)) :
    (τ : Ty B) → {η η' : ℕ} → τ.Value carrier η → τ.Value carrier η' → Prop
  | .bool, _, _, x, y => x = y
  | .base _, _, _, x, y => x.1 = y.1
  | .arrow a b, _, _, f, g => ∀ x y, a.Same carrier x y → b.Same carrier (f x) (g y)

/-- `const t` (LICS23 Fig. 2): the same value at every parameter and tape. LICS23 asks for a
value in `⋂_η ⟦τ⟧_η`; `Ty.Same` agrees with that at base types and at arrows from fixed types. -/
@[expose] def RV.IsConst {M : Model D} {τ : Ty B} (X : RV M τ) : Prop :=
  ∀ η η' ρ ρ', τ.Same M.carrier (X η ρ) (X η' ρ')

/-! ## Semantics and validity -/

/-- Global constructors as propositions about random variables (LICS23 Fig. 2). -/
@[expose] noncomputable def globalInterp (M : Model D) (C : AdvClass M) :
    Interpretation (globalSig B) (Kind.Value M)
  | _, .top, _ => True
  | _, .bot, _ => False
  | _, .and, next => next 0 Env.empty ∧ next 1 Env.empty
  | _, .or, next => next 0 Env.empty ∨ next 1 Env.empty
  | _, .imp, next => next 0 Env.empty → next 1 Env.empty
  | _, .all τ, next => ∀ X : RV M τ, next 0 (Env.single X)
  | _, .ex τ, next => ∃ X : RV M τ, next 0 (Env.single X)
  | _, .box, next => Overwhelming M.toTapeModel (next 0 Env.empty)
  | _, .const _, next => RV.IsConst (next 0 Env.empty)
  | _, .adv _ _ _, next => C.Adv (next 0 Env.empty)
  | _, .equiv _ _, next => C.Indist (fun η ρ _ x => next (false, ⟨_, x⟩) Env.empty η ρ)
      (fun η ρ _ x => next (true, ⟨_, x⟩) Env.empty η ρ)

/-- Local constructors as random variables, global ones as propositions. -/
@[expose] noncomputable def fullInterp (M : Model D) (C : AdvClass M) :
    Interpretation (fullSig D) (Kind.Value M) :=
  Interpretation.sum (rvInterp M) (globalInterp M C)

/-- Global constructors have no pointwise meaning. -/
@[expose] def ptGlobal (M : Model D) (η : ℕ) : Interpretation (globalSig B) (Kind.PtValue M η)
  | .glob, _, _ => PUnit.unit
  | .loc _, o, _ => nomatch o

/-- **Locality**, for local terms inside global formulas: at `(η, ρ)` they mean their pointwise
reading. Proved by `IFreeM.fold_rel` as `eval_denote_rvInterp` is; at the global sort both sides
are trivial. -/
theorem eval_denote_fullInterp (M : Model D) (C : AdvClass M) (η : ℕ) (ρ : M.Tape η)
    {Γ : List (Kind B)} {s : Kind B} (t : (fullSig D).Term Γ s) (env : Env (Kind.Value M) Γ) :
    s.eval M η ρ (t.denote (fullInterp M C) env) =
      t.denote (Interpretation.sum (interp M η ρ) (ptGlobal M η)) (evalEnv M η ρ env) := by
  refine IFreeM.fold_rel (P := (fullSig D).polynomial)
    (D := fun j : Judgment (Kind B) => Env (Kind.Value M) j.1 → Kind.Value M j.2)
    (E := fun j : Judgment (Kind B) => Env (Kind.PtValue M η) j.1 → Kind.PtValue M η j.2)
    (fun j f g => ∀ env, j.2.eval M η ρ (f env) = g (evalEnv M η ρ env))
    (fun _ x env => env _ x) (fun _ x env => env _ x)
    (fun _ o next env => fullInterp M C o fun p ξ => next p (Env.append ξ env))
    (fun _ o next env => Interpretation.sum (interp M η ρ) (ptGlobal M η) o
      fun p ξ => next p (Env.append ξ env))
    (fun _ _ _ => rfl) ?_ t env
  rintro ⟨Γ, s⟩ (o | o) ds es h env <;> cases s
  · change interp M η ρ o _ = interp M η ρ o _
    congr 1
    funext p e
    rw [h p, evalEnv_append, evalEnv_embed]
  · exact nomatch o
  · exact nomatch o
  · rfl

/-- A global formula holds in a model at random-variable values of its variables. -/
@[expose] def Form.Holds (M : Model D) (C : AdvClass M) {Γ : List (Kind B)} (F : Form D Γ)
    (env : Env (Kind.Value M) Γ) : Prop :=
  F.denote (fullInterp M C) env

section Reading

variable {M : Model D} {C : AdvClass M} {Γ : List (Kind B)} {env : Env (Kind.Value M) Γ}

theorem Form.holds_box {φ : FTerm D Γ .bool} :
    (Form.box φ).Holds M C env ↔ Overwhelming M.toTapeModel (φ.denote (fullInterp M C) env) :=
  Iff.rfl

theorem Form.holds_imp {F G : Form D Γ} :
    (Form.imp F G).Holds M C env ↔ (F.Holds M C env → G.Holds M C env) := Iff.rfl

theorem Form.holds_and {F G : Form D Γ} :
    (Form.and F G).Holds M C env ↔ F.Holds M C env ∧ G.Holds M C env := Iff.rfl

theorem Form.not_holds_bot : ¬ (Form.bot : Form D Γ).Holds M C env := id

theorem Form.holds_not {F : Form D Γ} : (Form.not F).Holds M C env ↔ ¬ F.Holds M C env :=
  Iff.rfl

theorem Form.holds_all {τ : Ty B} {F : Form D (.loc τ :: Γ)} :
    (Form.all τ F).Holds M C env ↔ ∀ X : RV M τ, F.Holds M C (Env.cons X env) := Iff.rfl

theorem Form.holds_ex {τ : Ty B} {F : Form D (.loc τ :: Γ)} :
    (Form.ex τ F).Holds M C env ↔ ∃ X : RV M τ, F.Holds M C (Env.cons X env) := Iff.rfl

@[simp] theorem FTerm.denote_ite {a : Ty B} (c : FTerm D Γ .bool) (t e : FTerm D Γ a) :
    (FTerm.ite c t e).denote (fullInterp M C) env =
      fun η ρ => cond (c.denote (fullInterp M C) env η ρ) (t.denote (fullInterp M C) env η ρ)
        (e.denote (fullInterp M C) env η ρ) := rfl

@[simp] theorem FTerm.denote_tt :
    (FTerm.tt : FTerm D Γ .bool).denote (fullInterp M C) env = fun _ _ => true := rfl

@[simp] theorem FTerm.denote_ff :
    (FTerm.ff : FTerm D Γ .bool).denote (fullInterp M C) env = fun _ _ => false := rfl

@[simp] theorem FTerm.denote_app {a b : Ty B} (f : FTerm D Γ (.arrow a b)) (x : FTerm D Γ a) :
    (FTerm.app f x).denote (fullInterp M C) env =
      fun η ρ => f.denote (fullInterp M C) env η ρ (x.denote (fullInterp M C) env η ρ) := rfl

/-- Local equality is equality of the values at each parameter and tape. -/
@[simp] theorem FTerm.denote_eq {a : Ty B} (t u : FTerm D Γ a) :
    (FTerm.eq t u).denote (fullInterp M C) env = fun η ρ =>
      @decide (t.denote (fullInterp M C) env η ρ = u.denote (fullInterp M C) env η ρ)
        (Classical.propDecidable _) := rfl

/-- An abstraction at `(η, ρ)` maps a value `x` to the body's reading with the variable at the
constant random variable `RV.constAt η x`. -/
theorem FTerm.denote_lam {a b : Ty B} (body : FTerm D (.loc a :: Γ) b) :
    (FTerm.lam body).denote (fullInterp M C) env =
      fun η ρ x => body.denote (fullInterp M C) (Env.cons (RV.constAt η x) env) η ρ :=
  rfl

/-- Local universal quantification at `(η, ρ)` ranges over the carrier at `η`; the bound variable
is the constant random variable `RV.constAt η x`. -/
@[simp] theorem FTerm.denote_all {a : Ty B} (φ : FTerm D (.loc a :: Γ) .bool) :
    (FTerm.all φ).denote (fullInterp M C) env = fun η ρ =>
      @decide (∀ x, φ.denote (fullInterp M C) (Env.cons (RV.constAt η x) env) η ρ = true)
        (Classical.propDecidable _) := rfl

@[simp] theorem FTerm.denote_fn {τ : Ty B} (f : D.Fn τ) :
    (FTerm.fn f : FTerm D Γ τ).denote (fullInterp M C) env = fun η _ => M.fn η f := rfl

/-- An attacker symbol reads the attacker tape. -/
@[simp] theorem FTerm.denote_att (f : D.Att) :
    (FTerm.att f : FTerm D Γ (D.attTy f)).denote (fullInterp M C) env = fun η ρ => M.att η f ρ.1 :=
  rfl

/-- A name reads the coordinate of the honest tape at its index's value. -/
@[simp] theorem FTerm.denote_name {a b : Ty B} (n : D.Name a b) (i : FTerm D Γ a) :
    (FTerm.name n i).denote (fullInterp M C) env =
      fun η ρ => M.name η n (i.denote (fullInterp M C) env η ρ) ρ.2 := rfl

/-- A term weakened past a binder ignores the value bound there. -/
theorem denote_weaken_cons {V : Kind B → Type} (alg : Interpretation (fullSig D) V)
    {s s' : Kind B} (t : (fullSig D).Term Γ s) (x : V s') (ξ : Env V Γ) :
    (t.weaken s').denote alg (Env.cons x ξ) = t.denote alg ξ := by
  rw [Term.weaken, Term.denote_rename]
  rfl

/-- The random variables of a vector of terms. -/
@[expose] noncomputable def Vec.rv (M : Model D) (C : AdvClass M) {τs : List (Ty B)}
    (u : Vec D Γ τs) (env : Env (Kind.Value M) Γ) : VecRV M τs :=
  fun η ρ _ x => (u _ x).denote (fullInterp M C) env η ρ

@[simp] theorem Vec.rv_cons {τ : Ty B} {τs : List (Ty B)} (t : FTerm D Γ τ) (u : Vec D Γ τs) :
    Vec.rv M C (Env.cons t u : Vec D Γ (τ :: τs)) env =
      VecRV.cons (t.denote (fullInterp M C) env) (u.rv M C env) := by
  funext η ρ σ x
  cases x <;> rfl

theorem Form.holds_adv {τs : List (Ty B)} {β : Ty B} {t : FTerm D Γ (Ty.arrows τs β)}
    {h : Ty.AdvOrder τs β} :
    (Form.adv t h).Holds M C env ↔ C.Adv (t.denote (fullInterp M C) env) :=
  Iff.rfl

theorem Form.holds_equiv {τs : List (Ty B)} {u v : Vec D Γ τs} {h : Ty.IndistOrder τs} :
    (Form.equiv u v h).Holds M C env ↔ C.Indist (u.rv M C env) (v.rv M C env) :=
  Iff.rfl

end Reading

/-- A term with one free variable, read at `(η, ρ)` with the value `x` for the variable. -/
@[expose] noncomputable def FTerm.evalAt (M : Model D) (η : ℕ) (ρ : M.Tape η) {σ τ : Ty B}
    (t : FTerm D [.loc σ] τ) (x : σ.Value M.carrier η) : τ.Value M.carrier η :=
  t.denote (Interpretation.sum (interp M η ρ) (ptGlobal M η)) (Env.cons x Env.empty)

/-- A term with one free variable, closed by substituting a closed term, means at `(η, ρ)` the
open term read at the closed term's value there: `Term.denote_substOne` and locality. -/
theorem FTerm.denote_substOne_apply (M : Model D) (C : AdvClass M) {σ τ : Ty B}
    (t : FTerm D [.loc σ] τ) (s : FTerm D [] σ) (env : Env (Kind.Value M) []) (η : ℕ)
    (ρ : M.Tape η) :
    (t.substOne s).denote (fullInterp M C) env η ρ =
      FTerm.evalAt M η ρ t (s.denote (fullInterp M C) env η ρ) := by
  rw [Term.denote_substOne]
  refine (eval_denote_fullInterp M C η ρ t _).trans
    (congrArg _ (funext fun _ => funext fun x => ?_))
  cases x with
  | zero => rfl
  | succ x => exact nomatch x

/-- Validity of the global sequent `Θ ⊢ F` in the context `Γ` (LICS23 §III), over the models
respecting the labels and the restriction `R`, against the adversaries `C M`. -/
@[expose] def Valid (R : Model D → Prop) (C : ∀ M : Model D, AdvClass M) {Γ : List (Kind B)}
    (Θ : List (Form D Γ)) (F : Form D Γ) : Prop :=
  ∀ M : Model D, M.RespectsLabels → R M → ∀ env,
    (∀ θ ∈ Θ, θ.Holds M (C M) env) → F.Holds M (C M) env

/-- Validity of the local sequent `Θ; Γl ⊢ φ`, which is `Θ ⊢ [∧Γl ⇒ φ]` (LICS23 §III). -/
@[expose] def LValid (R : Model D → Prop) (C : ∀ M : Model D, AdvClass M) {Γ : List (Kind B)}
    (Θ : List (Form D Γ)) (Γl : List (FTerm D Γ .bool)) (φ : FTerm D Γ .bool) : Prop :=
  Valid R C Θ (.box (.imp (.conj Γl) φ))

/-! ## Rules (LICS23 Fig. 7) -/

namespace Valid

variable {R : Model D → Prop} {C : ∀ M : Model D, AdvClass M} {Γ : List (Kind B)}
  {Θ Θ' : List (Form D Γ)} {F F' : Form D Γ}

/-- **G.Axiom.** -/
theorem ax (h : F ∈ Θ) : Valid R C Θ F := fun _ _ _ _ hΘ => hΘ F h

/-- **G.Weak.** -/
theorem weaken (h : Valid R C Θ F) (hΘ : Θ ⊆ Θ') : Valid R C Θ' F :=
  fun M hl hR env hΘ' => h M hl hR env fun θ hθ => hΘ' θ (hΘ hθ)

/-- **G.Cut.** -/
theorem cut (h₁ : Valid R C Θ F') (h₂ : Valid R C (F' :: Θ) F) : Valid R C Θ F :=
  fun M hl hR env hΘ => h₂ M hl hR env (List.forall_mem_cons.2 ⟨h₁ M hl hR env hΘ, hΘ⟩)

/-- **G.L-∀̃.** A global universal hypothesis may be instantiated by any local term, whose random
variable is the instance; `Term.denote_substOne` is the whole proof. -/
theorem all_left {τ : Ty B} {G : Form D (.loc τ :: Γ)} (t : FTerm D Γ τ)
    (h : Valid R C (G.substOne t :: Θ) F) : Valid R C (.all τ G :: Θ) F := by
  intro M hl hR env hΘ
  rw [List.forall_mem_cons] at hΘ
  refine h M hl hR env (List.forall_mem_cons.2 ⟨?_, hΘ.2⟩)
  rw [Form.Holds, Term.denote_substOne]
  exact hΘ.1 _

/-- **G.R-∀̃.** The hypotheses are weakened into the extended context; `Term.denote_rename` reads
them back. -/
theorem all_right {τ : Ty B} {G : Form D (.loc τ :: Γ)}
    (h : Valid R C (Θ.map (Term.weaken · (.loc τ))) G) : Valid R C Θ (.all τ G) := by
  intro M hl hR env hΘ X
  refine h M hl hR (Env.cons X env) fun θ hθ => ?_
  obtain ⟨θ', hθ', rfl⟩ := List.mem_map.1 hθ
  rw [Form.Holds, Term.weaken, Term.denote_rename]
  exact hΘ θ' hθ'

/-- **L.ByGlob.** An overwhelming formula is a local consequence of any local hypotheses. -/
theorem byGlob {φ : FTerm D Γ .bool} (Γl : List (FTerm D Γ .bool))
    (h : Valid R C Θ (.box φ)) : LValid R C Θ Γl φ := fun M hl hR env hΘ =>
  Form.holds_box.2 <| (Form.holds_box.1 (h M hl hR env hΘ)).mono fun η ρ hρ => by
    simp only [FTerm.imp, FTerm.denote_ite, FTerm.denote_tt] at hρ
    cases hc : (FTerm.conj Γl).denote (fullInterp M (C M)) env η ρ <;> simp_all

/-- **G.ByLoc.** A local formula derived without local hypotheses is overwhelming: `∧∅ ⇒ φ` and
`φ` have the same random variable. -/
theorem byLoc {φ : FTerm D Γ .bool} (h : LValid R C Θ [] φ) : Valid R C Θ (.box φ) := h

end Valid

end Interop.Squirrel
