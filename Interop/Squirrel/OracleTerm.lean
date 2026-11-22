/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Squirrel.Avoids

/-!
# Terms with explicit calls to a keyed hash

The PRF rules of LICS23 (G.PRF) and CCS26 (Fig. 4 and Fig. 11) are about terms in which a key name
`k` occurs only as the key of a hash `h(·, k)`. Their reductions evaluate such terms without the
key, sending each `h(t, k)` to a hash oracle (CCS26 App. C.3). Here the hashes with key `k` are
explicit syntax:

* `PRFSymbols D` names the keyed hash in a declaration: a key name `nk` at an honest constant
  index `ik`, and an honest symbol `hOf : msg → key → hash`, applied as `h(m, k)`
  (`PRFSymbols.hashTerm`).
* `PRFSymbols.oSig P` is the local signature with one more constructor, `call t`, the oracle
  `o_h^k = λx. h(x, k)` of CCS26 applied to `t`, as a sum of PolyFun's binding signatures
  (`ScopedSignature.sum`). Its terms are `OTerm P Γ τ`.
* `PRFSymbols.close` replaces each `call t` by `h(t, k)`: a fold of the syntax, giving the term of
  the logic that an `OTerm` stands for. `PRFSymbols.denote_close`: it means the `OTerm` read with
  `call` as `h(·, k)` at the key's value (`PRFSymbols.ointerp`).

## The side conditions, on the heads of a term

Each side condition says that every head of the term (PolyFun's `Term.heads`, the constructors it
uses) lies in a set, so it is a fold of the syntax with no induction over terms, and it is
decidable on concrete terms.

* **ψ_key** (`PRFSymbols.KeyFree`): no head of the `OTerm` is the key name. In `close t` the key
  then occurs only where `close` puts it, as the key of `h`: this is CCS26's `ψ^k_PRF,key`
  (Fig. 11), and LICS23's condition that every key occurrence `k t₀` other than hash keys has
  `t₀ ≠ t`, for indices that are the same honest constant. `PRFSymbols.ointerp_eq_of_keyFree`
  shows what it gives: the term reads no coordinate of the honest tape that belongs to the key
  name.
* **⊢pptm** (`PRFSymbols.Pptm`): the heads that a machine evaluates by the compiled reading
  (`Interop.Squirrel.Compile`). It mirrors LICS23's rules for `⊢pptm` (Fig. 10): variables
  (PT.Input), application (PT.App), names at Boolean or base indices (PT.Name), abstraction
  (PT.Lambda), honest and attacker symbols (PT.Adv; here of order at most one, so that their
  values pass to and from Kleisli arrows), conditionals and Boolean constants, equality at Boolean
  and base types only, and hash calls on Boolean or base types. Local quantifiers are excluded:
  PT.Quant enumerates a polynomial type, which the compiled reading does not do.
* **First order** (`PRFSymbols.FirstOrder`): no abstraction. LICS23 generates `ψ_msg` over the
  generalised subterms, which quantify over the variables bound above an occurrence (Fig. 1);
  without binders every call argument lives in the term's own context, and `PRFSymbols.calls`
  collects them by a fold.
* **ψ_msg** (`PRFSymbols.psiMsg`): the conjunction, over the arguments `t′` of the calls of `u⃗`
  and `m`, of `t′ ≠ m`. LICS23's `ψ^k_msg` asks `∀α. ψ ⇒ (t = t₀) ⇒ (m ≠ m₀)` for each hash
  occurrence `(α, ψ, hash m₀ (k t₀))`, with `ψ` the conditions of the enclosing conditionals; here
  every call has the key `k(ik)`, there is no `α`, and the conditions are dropped, which makes the
  formula stronger and keeps the rule sound. The challenge `h(m, k)` itself is not a call of `u⃗`
  or `m`, so it is not among the conjuncts. `PRFSymbols.psiMsg_eq_true_iff` reads it at a tape.

## References

* [LICS23] Baelde, Koutsos, Lallemand, *A Higher-Order Indistinguishability Logic for
  Cryptographic Reasoning*, LICS 2023: Fig. 1, Fig. 10 and the rule G.PRF (p. 29).
* [CCS26] Hérouard, Jacomme, Koutsos, Lallemand, *Secrecy in Squirrel and the Post-Compromise
  Security of a Ratchet*, CCS 2026: Fig. 4, Fig. 11 and App. C.3.
-/

public section

namespace Interop.Squirrel

open IPFunctor IPFunctor.ScopedSignature

variable {B : Type} {D : Decl B}

/-! ## Deciding a property of every entry of a vector

A fact about PolyFun's environments, independent of Squirrel: the side conditions of a vector are
decided entry by entry. -/

/-- Whether a property holds of every entry of an environment, decided entry by entry. -/
@[expose, instance_reducible] def decidableForallEntries {S : Type} {V : S → Type}
    (p : ∀ a, V a → Prop) [∀ a v, Decidable (p a v)] :
    {Γ : List S} → (η : Env V Γ) → Decidable (∀ a x, p a (η a x))
  | [], _ => isTrue fun _ x => nomatch x
  | _ :: _, η =>
    haveI := decidableForallEntries p fun _ x => η _ (.succ x)
    decidable_of_iff (p _ (η _ .zero) ∧ ∀ a (x : ScopedVar _ a), p a (η a (.succ x)))
      ⟨fun h a x => by
        cases x with
        | zero => exact h.1
        | succ x => exact h.2 a x,
      fun h => ⟨h _ .zero, fun a x => h a (.succ x)⟩⟩

/-- The symbols of a keyed hash in a declaration: a key name `nk` read at an honest constant
index `ik`, and the hash `hOf : msg → key → hash`, applied to a message and the key. -/
structure PRFSymbols (D : Decl B) where
  /-- The index type of the key name. -/
  keyIdx : Ty B
  /-- The type of keys. -/
  keyTy : Ty B
  /-- The type of messages, the hash's domain. -/
  msgTy : Ty B
  /-- The type of hashes, the hash's range. -/
  hTy : Ty B
  /-- The key name `k`. -/
  nk : D.Name keyIdx keyTy
  /-- The index at which the key name is read. -/
  ik : D.Fn keyIdx
  /-- The keyed hash `h(m, k)`, curried. -/
  hOf : D.Fn (.arrow msgTy (.arrow keyTy hTy))

namespace PRFSymbols

variable (P : PRFSymbols D)

/-- The key name with its types. -/
abbrev keyName : (a : Ty B) × (b : Ty B) × D.Name a b := ⟨_, _, P.nk⟩

/-- The coordinate of the honest tape that the key reads at `η`. -/
abbrev keySlot (M : Model D) (η : ℕ) : M.Slot η := ⟨P.keyName, M.fn η P.ik⟩

/-- The key's value at `η` on the honest tape `ρh`. -/
abbrev keyVal (M : Model D) (η : ℕ) (ρh : M.TapeH η) : P.keyTy.Value M.carrier η :=
  M.name η P.nk (M.fn η P.ik) ρh

/-- The term `h(m, k)`. -/
@[expose] def hashTerm {Γ : List (Kind B)} (m : FTerm D Γ P.msgTy) : FTerm D Γ P.hTy :=
  FTerm.app (FTerm.app (FTerm.fn P.hOf) m) (FTerm.name P.nk (FTerm.fn P.ik))

/-- `h(m, k)` hashes the message's value under the key's value. -/
theorem denote_hashTerm {M : Model D} (C : AdvClass M) {Γ : List (Kind B)}
    (m : FTerm D Γ P.msgTy) (env : Env (Kind.Value M) Γ) :
    (P.hashTerm m).denote (fullInterp M C) env =
      fun η ρ => M.fn η P.hOf (m.denote (fullInterp M C) env η ρ) (P.keyVal M η ρ.2) :=
  rfl

/-- The oracle constructor: a call of `o_h^k = λx. h(x, k)`. -/
inductive CallOp : Kind B → Type where
  /-- `call t`, standing for `h(t, k)`. -/
  | call : CallOp (.loc P.hTy)

/-- The signature of the oracle call: one argument, a message, binding nothing. -/
@[expose, reducible] def callSig : ScopedSignature (Kind B) where
  Op := P.CallOp
  Arg _ := Unit
  binders _ _ := []
  sort _ _ := .loc P.msgTy

/-- Local terms with oracle calls: the sum of the local signature and the call. -/
@[expose, reducible] def oSig : ScopedSignature (Kind B) := (localSig D).sum P.callSig

end PRFSymbols

/-- Local terms of type `τ` with calls to the keyed hash. -/
abbrev OTerm (P : PRFSymbols D) (Γ : List (Kind B)) (τ : Ty B) := P.oSig.Term Γ (.loc τ)

/-- Vectors of terms with calls. -/
abbrev OVec (P : PRFSymbols D) (Γ : List (Kind B)) (τs : List (Ty B)) :=
  Env (fun τ => OTerm P Γ τ) τs

namespace OTerm

variable {P : PRFSymbols D} {Γ : List (Kind B)} {a b : Ty B}

/-- A call `o_h^k(t)`, standing for `h(t, k)`. -/
@[expose] def call (t : OTerm P Γ P.msgTy) : OTerm P Γ P.hTy := .node (.inr .call) fun _ => t

/-- Application. -/
@[expose] def app (f : OTerm P Γ (.arrow a b)) (x : OTerm P Γ a) : OTerm P Γ b :=
  .node (.inl (.app a b)) (Fin.cases f fun _ => x)

/-- The conditional. -/
@[expose] def ite (c : OTerm P Γ .bool) (t e : OTerm P Γ a) : OTerm P Γ a :=
  .node (.inl (.ite a)) (Fin.cases c (Fin.cases t fun _ => e))

/-- Local equality. -/
@[expose] def eq (t u : OTerm P Γ a) : OTerm P Γ .bool :=
  app (app (.node (.inl (.eq a)) fun p => nomatch p) t) u

/-- An honest function symbol. -/
@[expose] def fn (f : D.Fn a) : OTerm P Γ a := .node (.inl (.fn f)) fun p => nomatch p

/-- An attacker function symbol. -/
@[expose] def att (f : D.Att) : OTerm P Γ (D.attTy f) := .node (.inl (.att f)) fun p => nomatch p

/-- A name applied to an index. -/
@[expose] def name (n : D.Name a b) (i : OTerm P Γ a) : OTerm P Γ b :=
  app (.node (.inl (.name n)) fun p => nomatch p) i

/-- The local universal quantifier over `a`, applied to a predicate. -/
@[expose] def all (φ : OTerm P Γ (.arrow a .bool)) : OTerm P Γ .bool :=
  app (.node (.inl (.all a)) fun p => nomatch p) φ

end OTerm

namespace PRFSymbols

variable (P : PRFSymbols D)

/-! ## Closing calls into hashes -/

/-- Replace every call `o_h^k(t)` by `h(t, k)`: the term of the logic that a term with calls
stands for. -/
@[expose] def close {Γ : List (Kind B)} {s : Kind B} (t : P.oSig.Term Γ s) :
    (fullSig D).Term Γ s :=
  t.fold (D := fun j : Judgment (Kind B) => (fullSig D).Term j.1 j.2) (fun _ x => .pure x)
    fun ⟨_, s⟩ o next => match s, o, next with
      | _, .inl o, next => .liftBind (.inl o) next
      | _, .inr .call, next => P.hashTerm (next ())

variable {P} in
@[simp] theorem close_fn {Γ : List (Kind B)} {τ : Ty B} (f : D.Fn τ) :
    P.close (OTerm.fn (P := P) (Γ := Γ) f) = FTerm.fn f :=
  congrArg (IFreeM.liftBind _) (funext fun p => p.elim0)

variable {P} in
@[simp] theorem close_app {Γ : List (Kind B)} {a b : Ty B} (f : OTerm P Γ (.arrow a b))
    (x : OTerm P Γ a) : P.close (OTerm.app f x) = FTerm.app (P.close f) (P.close x) :=
  congrArg (IFreeM.liftBind _) (funext fun p => Fin.cases rfl (fun _ => rfl) p)

variable {P} in
@[simp] theorem close_name {Γ : List (Kind B)} {a b : Ty B} (n : D.Name a b) (i : OTerm P Γ a) :
    P.close (OTerm.name n i) = FTerm.name n (P.close i) := by
  rw [OTerm.name, close_app]
  exact congrArg (FTerm.app · _) (congrArg (IFreeM.liftBind _) (funext fun p => p.elim0))

variable {P} in
@[simp] theorem close_call {Γ : List (Kind B)} (t : OTerm P Γ P.msgTy) :
    P.close (OTerm.call t) = P.hashTerm (P.close t) :=
  rfl

/-- Close every entry of a vector. -/
@[expose] def closeVec {Γ : List (Kind B)} {τs : List (Ty B)} (u : OVec P Γ τs) : Vec D Γ τs :=
  fun _ x => P.close (u _ x)

theorem closeVec_append {Γ : List (Kind B)} {τs' : List (Ty B)} :
    ∀ {τs : List (Ty B)} (u : OVec P Γ τs) (w : OVec P Γ τs'),
      P.closeVec (Env.append u w) = Env.append (P.closeVec u) (P.closeVec w)
  | [], _, _ => rfl
  | _ :: _, u, w => by
    funext a x
    cases x with
    | zero => rfl
    | succ x => exact congrFun (congrFun (closeVec_append (fun _ y => u _ (.succ y)) w) a) x

theorem closeVec_single {Γ : List (Kind B)} {β : Ty B} (v : OTerm P Γ β) :
    P.closeVec (Env.cons v Env.empty : OVec P Γ [β]) =
      (Env.cons (P.close v) Env.empty : Vec D Γ [β]) := by
  funext a x
  cases x with
  | zero => rfl
  | succ x => exact nomatch x

/-- The meaning of a call at `η` with the key value `kv`: the hash of the argument. -/
@[expose] def callInterp (M : Model D) (η : ℕ) (kv : P.keyTy.Value M.carrier η) :
    Interpretation P.callSig (Kind.PtValue M η)
  | _, .call, next => M.fn η P.hOf (next () Env.empty) kv

/-- Terms with calls read at `η` and the tapes `ρ`, each call hashing with the key value `kv`. -/
@[expose, reducible] noncomputable def ointerp (M : Model D) (η : ℕ) (ρ : M.Tape η)
    (kv : P.keyTy.Value M.carrier η) : Interpretation P.oSig (Kind.PtValue M η) :=
  Interpretation.sum (interp M η ρ) (P.callInterp M η kv)

/-- A closed-up term means its calls read as hashes with the key of the honest tape. -/
theorem denote_close (M : Model D) (η : ℕ) (ρ : M.Tape η) {Γ : List (Kind B)} {s : Kind B}
    (t : P.oSig.Term Γ s) (e : Env (Kind.PtValue M η) Γ) :
    (P.close t).denote (Interpretation.sum (interp M η ρ) (ptGlobal M η)) e =
      t.denote (P.ointerp M η ρ (P.keyVal M η ρ.2)) e := by
  have h := IFreeM.fold_fusion (P := P.oSig.polynomial)
    (D := fun j : Judgment (Kind B) => (fullSig D).Term j.1 j.2)
    (E := fun j : Judgment (Kind B) => Env (Kind.PtValue M η) j.1 → Kind.PtValue M η j.2)
    (fun _ t e => t.denote (Interpretation.sum (interp M η ρ) (ptGlobal M η)) e)
    (fun _ x => .pure x) (fun _ x e => e _ x)
    (fun ⟨_, s⟩ o next => match s, o, next with
      | _, .inl o, next => .liftBind (.inl o) next
      | _, .inr .call, next => P.hashTerm (next ()))
    (fun _ o next e => P.ointerp M η ρ (P.keyVal M η ρ.2) o
      fun p ξ => next p (Env.append ξ e))
    (fun _ _ => rfl) ?_ t
  · exact congrFun h e
  rintro ⟨Γ, s⟩ (o | o) ds
  · rfl
  · cases o
    rfl

/-! ## The side conditions, on heads -/

/-- The head is not the key name. -/
@[expose] def KeyFreeAt : P.oSig.Head → Prop
  | ⟨_, .inl (.name n)⟩ => (⟨_, _, n⟩ : (a : Ty B) × (b : Ty B) × D.Name a b) ≠ P.keyName
  | _ => True

/-- **ψ_key** (CCS26 Fig. 11): the key name is not a head of the term with calls, so in its
closed-up term it occurs only as the key of `h`. -/
@[expose] def KeyFree {Γ : List (Kind B)} {s : Kind B} (t : P.oSig.Term Γ s) : Prop :=
  t.heads ⊆ {h | P.KeyFreeAt h}

instance KeyFreeAt.decidablePred [DecidableEq ((a : Ty B) × (b : Ty B) × D.Name a b)] :
    DecidablePred P.KeyFreeAt
  | ⟨_, .inl (.name _)⟩ => instDecidableNot
  | ⟨_, .inl (.app _ _)⟩ | ⟨_, .inl (.lam _ _)⟩ | ⟨_, .inl (.ite _)⟩ | ⟨_, .inl .tt⟩
  | ⟨_, .inl .ff⟩ | ⟨_, .inl (.eq _)⟩ | ⟨_, .inl (.all _)⟩ | ⟨_, .inl (.ex _)⟩
  | ⟨_, .inl (.fn _)⟩ | ⟨_, .inl (.att _)⟩ | ⟨_, .inr .call⟩ => instDecidableTrue

/-- `ψ_key` is decidable when names have decidable equality: PolyFun's decision procedure for
the heads of a term. -/
instance decidableKeyFree [DecidableEq ((a : Ty B) × (b : Ty B) × D.Name a b)]
    {Γ : List (Kind B)} {s : Kind B} (t : P.oSig.Term Γ s) : Decidable (P.KeyFree t) :=
  Term.decidableHeadsSubset _ t

/-- The heads that the compiled reading evaluates (LICS23 Fig. 10): names at Boolean or base
indices with results of order at most one, honest and attacker symbols of order at most one,
equality at Boolean and base types, no local quantifiers, and calls on a Boolean or base message
type with a Boolean or base hash type. -/
@[expose] def PptmAt : P.oSig.Head → Prop
  | ⟨_, .inl (.eq a)⟩ => a.IsGround
  | ⟨_, .inl (.all _)⟩ => False
  | ⟨_, .inl (.ex _)⟩ => False
  | ⟨_, .inl (@LocalOp.name _ _ a b _)⟩ => a.IsGround ∧ b.order ≤ 1
  | ⟨_, .inl (@LocalOp.fn _ _ τ _)⟩ => τ.order ≤ 1
  | ⟨_, .inl (.att f)⟩ => (D.attTy f).order ≤ 1
  | ⟨_, .inr .call⟩ => P.msgTy.IsGround ∧ P.hTy.IsGround
  | _ => True

/-- **⊢pptm**: every head of the term is evaluated by the compiled reading. -/
@[expose] def Pptm {Γ : List (Kind B)} {s : Kind B} (t : P.oSig.Term Γ s) : Prop :=
  t.heads ⊆ {h | P.PptmAt h}

instance PptmAt.decidablePred : DecidablePred P.PptmAt
  | ⟨_, .inl (.eq a)⟩ => inferInstanceAs (Decidable a.IsGround)
  | ⟨_, .inl (.all _)⟩ | ⟨_, .inl (.ex _)⟩ => instDecidableFalse
  | ⟨_, .inl (@LocalOp.name _ _ a b _)⟩ => inferInstanceAs (Decidable (a.IsGround ∧ b.order ≤ 1))
  | ⟨_, .inl (@LocalOp.fn _ _ τ _)⟩ => inferInstanceAs (Decidable (τ.order ≤ 1))
  | ⟨_, .inl (.att f)⟩ => inferInstanceAs (Decidable ((D.attTy f).order ≤ 1))
  | ⟨_, .inr .call⟩ => inferInstanceAs (Decidable (P.msgTy.IsGround ∧ P.hTy.IsGround))
  | ⟨_, .inl (.app _ _)⟩ | ⟨_, .inl (.lam _ _)⟩ | ⟨_, .inl (.ite _)⟩ | ⟨_, .inl .tt⟩
  | ⟨_, .inl .ff⟩ => instDecidableTrue

/-- `⊢pptm` is decidable: PolyFun's decision procedure for the heads of a term. -/
instance decidablePptm {Γ : List (Kind B)} {s : Kind B} (t : P.oSig.Term Γ s) :
    Decidable (P.Pptm t) :=
  Term.decidableHeadsSubset _ t

/-- The head is not an abstraction. -/
@[expose] def FirstOrderAt : P.oSig.Head → Prop
  | ⟨_, .inl (.lam _ _)⟩ => False
  | _ => True

/-- The term binds no variable: every call argument lives in the term's own context. -/
@[expose] def FirstOrder {Γ : List (Kind B)} {s : Kind B} (t : P.oSig.Term Γ s) : Prop :=
  t.heads ⊆ {h | P.FirstOrderAt h}

instance FirstOrderAt.decidablePred : DecidablePred P.FirstOrderAt
  | ⟨_, .inl (.lam _ _)⟩ => instDecidableFalse
  | ⟨_, .inl (.app _ _)⟩ | ⟨_, .inl (.ite _)⟩ | ⟨_, .inl .tt⟩ | ⟨_, .inl .ff⟩
  | ⟨_, .inl (.eq _)⟩ | ⟨_, .inl (.all _)⟩ | ⟨_, .inl (.ex _)⟩ | ⟨_, .inl (.name _)⟩
  | ⟨_, .inl (.fn _)⟩ | ⟨_, .inl (.att _)⟩ | ⟨_, .inr .call⟩ => instDecidableTrue

/-- Being first order is decidable: PolyFun's decision procedure for the heads of a term. -/
instance decidableFirstOrder {Γ : List (Kind B)} {s : Kind B} (t : P.oSig.Term Γ s) :
    Decidable (P.FirstOrder t) :=
  Term.decidableHeadsSubset _ t

/-! ## The arguments of the calls -/

/-- The term itself and the arguments of its calls, by a fold that also rebuilds the syntax.
Calls under an abstraction are in a larger context and are not collected; first-order terms have
none. -/
@[expose] def callsAux {Γ : List (Kind B)} {s : Kind B} (t : P.oSig.Term Γ s) :
    P.oSig.Term Γ s × List (OTerm P Γ P.msgTy) :=
  t.fold (D := fun j : Judgment (Kind B) => P.oSig.Term j.1 j.2 × List (OTerm P j.1 P.msgTy))
    (fun _ x => (.pure x, []))
    fun ⟨_, s⟩ o next => match s, o, next with
      | _, .inr .call, next => (.liftBind (.inr .call) fun p => (next p).1,
          (next ()).1 :: (next ()).2)
      | _, .inl (.app a b), next => (.liftBind (.inl (.app a b)) fun p => (next p).1,
          (next 0).2 ++ (next 1).2)
      | _, .inl (.ite a), next => (.liftBind (.inl (.ite a)) fun p => (next p).1,
          (next 0).2 ++ (next 1).2 ++ (next 2).2)
      | _, o, next => (.liftBind o fun p => (next p).1, [])

/-- The arguments of the calls of a term. -/
@[expose] def calls {Γ : List (Kind B)} {s : Kind B} (t : P.oSig.Term Γ s) :
    List (OTerm P Γ P.msgTy) :=
  (P.callsAux t).2

/-- The arguments of the calls of a vector. -/
@[expose] def vecCalls {Γ : List (Kind B)} : {τs : List (Ty B)} → OVec P Γ τs →
    List (OTerm P Γ P.msgTy)
  | [], _ => []
  | _ :: _, u => P.calls (u _ .zero) ++ vecCalls fun _ x => u _ (.succ x)

/-- **ψ_msg** (CCS26 Fig. 11; LICS23, G.PRF): over the calls `o_h^k(t′)` of `u⃗` and `m`, the
conjunction of `t′ ≠ m`, closed up. -/
@[expose] def psiMsg {Γ : List (Kind B)} {τs : List (Ty B)} (u : OVec P Γ τs)
    (m : OTerm P Γ P.msgTy) : FTerm D Γ .bool :=
  FTerm.conj ((P.vecCalls u ++ P.calls m).map fun t' =>
    FTerm.not (FTerm.eq (P.close t') (P.close m)))

/-! ## What the side conditions give -/

section Semantics

variable {P} {M : Model D} {η : ℕ}

/-- A local constructor other than the key name reads the same at two honest tapes that agree
on every coordinate not belonging to the key name. -/
theorem interp_eq_of_keyFreeAt {ρa : M.TapeA η} {ρh ρh' : M.TapeH η}
    (hρ : ∀ k : M.Slot η, k.1 ≠ P.keyName → ρh k = ρh' k) {s : Kind B} (o : (localSig D).Op s)
    (ho : P.KeyFreeAt ⟨s, .inl o⟩) :
    interp M η (ρa, ρh) o = interp M η (ρa, ρh') o := by
  funext next
  cases o with
  | name n => exact funext fun i => congrArg (M.sample η _) (hρ ⟨⟨_, _, n⟩, i⟩ ho)
  | _ => rfl

/-- **ψ_key, semantically.** A term with calls in which the key name does not occur reads no
coordinate of the honest tape that belongs to the key name: its reading is the same at two
honest tapes that agree on every other coordinate, whatever the key value of its calls. It is
PolyFun's `Term.denote_congr_of_heads_subset`: the two readings agree on every head of `t`. -/
theorem ointerp_eq_of_keyFree {ρa : M.TapeA η} {ρh ρh' : M.TapeH η}
    (hρ : ∀ k : M.Slot η, k.1 ≠ P.keyName → ρh k = ρh' k) (kv : P.keyTy.Value M.carrier η)
    {Γ : List (Kind B)} {s : Kind B} (t : P.oSig.Term Γ s) (ht : P.KeyFree t) :
    t.denote (P.ointerp M η (ρa, ρh) kv) = t.denote (P.ointerp M η (ρa, ρh') kv) := by
  refine Term.denote_congr_of_heads_subset t ht ?_
  rintro ⟨s, o | o⟩ ho
  · exact interp_eq_of_keyFreeAt hρ o ho
  · cases o
    rfl

/-- The first component of `callsAux` rebuilds the term. -/
theorem fst_callsAux {Γ : List (Kind B)} {s : Kind B} (t : P.oSig.Term Γ s) :
    (P.callsAux t).1 = t := by
  induction t using Term.inductionOn with
  | hvar Γ s x => rfl
  | hnode Γ s op args ih =>
    rcases op with o | o
    · cases o <;> exact congrArg (IFreeM.liftBind _) (funext ih)
    · cases o
      exact congrArg (IFreeM.liftBind _) (funext ih)

@[simp] theorem calls_fn {Γ : List (Kind B)} {τ : Ty B} (f : D.Fn τ) :
    P.calls (OTerm.fn (P := P) (Γ := Γ) f) = [] :=
  rfl

@[simp] theorem calls_app {Γ : List (Kind B)} {a b : Ty B} (f : OTerm P Γ (.arrow a b))
    (x : OTerm P Γ a) : P.calls (OTerm.app f x) = P.calls f ++ P.calls x :=
  rfl

@[simp] theorem calls_name {Γ : List (Kind B)} {a b : Ty B} (n : D.Name a b) (i : OTerm P Γ a) :
    P.calls (OTerm.name n i) = P.calls i :=
  rfl

@[simp] theorem calls_call {Γ : List (Kind B)} (t : OTerm P Γ P.msgTy) :
    P.calls (OTerm.call t) = t :: P.calls t := by
  change (P.callsAux t).1 :: P.calls t = _
  rw [fst_callsAux]

@[simp] theorem vecCalls_cons {Γ : List (Kind B)} {τ : Ty B} {τs : List (Ty B)}
    (t : OTerm P Γ τ) (u : OVec P Γ τs) :
    P.vecCalls (Env.cons t u : OVec P Γ (τ :: τs)) = P.calls t ++ P.vecCalls u :=
  rfl

@[simp] theorem vecCalls_nil {Γ : List (Kind B)} (u : OVec P Γ []) : P.vecCalls u = [] :=
  rfl

theorem mem_vecCalls {Γ : List (Kind B)} {t' : OTerm P Γ P.msgTy} :
    ∀ {τs : List (Ty B)} {u : OVec P Γ τs},
      t' ∈ P.vecCalls u ↔ ∃ τ, ∃ x : ScopedVar τs τ, t' ∈ P.calls (u τ x)
  | [], _ => ⟨fun h => absurd h List.not_mem_nil, fun ⟨_, x, _⟩ => nomatch x⟩
  | _ :: _, u => by
    rw [vecCalls, List.mem_append, mem_vecCalls]
    constructor
    · rintro (h | ⟨τ, x, h⟩)
      · exact ⟨_, .zero, h⟩
      · exact ⟨τ, .succ x, h⟩
    · rintro ⟨τ, x, h⟩
      cases x with
      | zero => exact .inl h
      | succ x => exact .inr ⟨τ, x, h⟩

/-- A closed term with calls, closed up, means at `(η, ρ)` its reading with the key of `ρ`. -/
theorem denote_close_apply (C : AdvClass M) {τ : Ty B} (t : OTerm P [] τ)
    (env : Env (Kind.Value M) []) (ρ : M.Tape η) :
    (P.close t).denote (fullInterp M C) env η ρ =
      t.denote (P.ointerp M η ρ (P.keyVal M η ρ.2)) Env.empty := by
  have h := eval_denote_fullInterp M C η ρ (P.close t) env
  rw [Env.eq_empty (evalEnv M η ρ env), denote_close] at h
  exact h

variable (P) in
/-- **ψ_msg at `(η, ρ)`**: no call argument of `u⃗` or `m` has the value of `m`, each read with
the key of `ρ`. -/
theorem psiMsg_eq_true_iff (C : AdvClass M) {τs : List (Ty B)} (u : OVec P [] τs)
    (m : OTerm P [] P.msgTy) (env : Env (Kind.Value M) []) (ρ : M.Tape η) :
    (P.psiMsg u m).denote (fullInterp M C) env η ρ = true ↔
      ∀ t' ∈ P.vecCalls u ++ P.calls m,
        t'.denote (P.ointerp M η ρ (P.keyVal M η ρ.2)) Env.empty ≠
          m.denote (P.ointerp M η ρ (P.keyVal M η ρ.2)) Env.empty := by
  rw [psiMsg, FTerm.denote_conj_eq_true, List.forall_mem_map]
  refine forall₂_congr fun t' _ => ?_
  simp only [FTerm.not, FTerm.denote_ite, FTerm.denote_eq, FTerm.denote_ff, FTerm.denote_tt]
  rw [denote_close_apply, denote_close_apply]
  by_cases h : t'.denote (P.ointerp M η ρ (P.keyVal M η ρ.2)) Env.empty =
    m.denote (P.ointerp M η ρ (P.keyVal M η ρ.2)) Env.empty <;> simp [h]

end Semantics

end PRFSymbols

end Interop.Squirrel
