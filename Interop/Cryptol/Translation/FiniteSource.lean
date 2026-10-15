/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Translation.Finite.Relation
public import Interop.Cryptol.Model.Resolved
public import Interop.Cryptol.Model.SequenceAppend
public import Interop.Cryptol.Model.NativeLaws

/-!
# Compact source export for the total fragment

This translation preserves native primitive heads, array literals and lexical
let bindings. Its direct source semantics is related to the independent native
interpreter; composition with source lowering gives the canonical verified route
to the core without expanding the text sent to Cryptol.
-/

public section

open OmegaCompletePartialOrder

namespace Interop.Cryptol.Finite

/-- Translate one native constructor while retaining its binding contexts. -/
@[expose] def sourceOp (Γ : List Ty) : {a : Ty} → (op : Op a) →
    ((p : Fin op.arity) → Resolved.Term (((op.child p).1 ++ Γ).map Ty.core) ((op.child p).2).core) →
      Resolved.Term (Γ.map Ty.core) a.core
  | _, .bit b, _ => .bit b
  | _, .word x, _ => .word x
  | _, .pair, next => .pair (next 0) (next 1)
  | _, .fst, next => .fst (next 0)
  | _, .snd, next => .snd (next 0)
  | _, @Op.sequence a n, next => .sequence n (fun i => (next i))
  | _, @Op.snoc a n, next =>
      .app (.app (.primitive (.append n (.finite 1) a.core)) (next 0))
        (.sequence 1 (fun _ => next 1))
  | _, .index i, next => .index (next 0) (.integer i.val)
  | _, .arithmetic op, next => .wordArithmetic op.core (next 0) (next 1)
  | _, .lam, next => .lam (next 0)
  | _, .app, next => .app (next 0) (next 1)
  | _, .letE, next => .letE (next 0) (next 1)
  | _, .bitNot, next => .bitNot (next 0)
  | _, .bitOp op, next => .bitOp op (next 0) (next 1)
  | _, .wordNot, next => .app (.primitive (.wordNot _)) (next 0)
  | _, .wordOp op, next => .wordLogic op (next 0) (next 1)
  | _, .wordEq _, next => .app (.app (.primitive (.wordEq _)) (next 0)) (next 1)
  | _, .shiftLeft k, next => .app (.primitive (.shiftFixed _ .left k)) (next 0)
  | _, .shiftRight k, next => .app (.primitive (.shiftFixed _ .right k)) (next 0)
  | _, .rotateLeft k, next => .app (.primitive (.shiftFixed _ .rotateLeft k)) (next 0)
  | _, .rotateRight k, next => .app (.primitive (.shiftFixed _ .rotateRight k)) (next 0)

/-- Translate native syntax using the generic indexed fold. -/
@[expose] def Term.source {Γ : List Ty} {a : Ty} (t : Term Γ a) :
    Resolved.Term (Γ.map Ty.core) a.core :=
  t.fold (D := fun j : IPFunctor.ScopedSignature.Judgment Ty =>
      Resolved.Term (j.1.map Ty.core) j.2.core)
    (fun _ v => .var (lowerVar v)) (fun j op next => sourceOp j.1 op next)

/-- Compact source translation preserves every accepted native meaning. -/
theorem Term.source_correct {Γ : List Ty} {a : Ty} (e : Term Γ a) (ρ : Env Γ)
    (η : Environment (Γ.map Ty.core)) (h : EnvRepresents ρ η) :
    Represents a (e.denote ρ) (Resolved.denote e.source η) := by
  induction e using IPFunctor.ScopedSignature.Term.inductionOn with
  | hvar Γ a v => exact h _ v
  | hnode Γ a op args ih =>
    cases op with
    | bit b =>
      rfl
    | word x =>
      rfl
    | pair =>
      let x : Term _ _ := args 0
      let y : Term _ _ := args 1
      have ihx := ih 0
      have ihy := ih 1
      exact ⟨_, _, rfl, ihx ρ η h, ihy ρ η h⟩
    | fst =>
      let x : Term _ _ := args 0
      have ih := ih 0
      obtain ⟨dx, dy, hd, hx, _⟩ := ih ρ η h
      change Represents _ _ (DomainResult.bind _ (Resolved.denote x.source η))
      rw [hd]
      exact hx
    | snd =>
      let x : Term _ _ := args 0
      have ih := ih 0
      obtain ⟨dx, dy, hd, _, hy⟩ := ih ρ η h
      change Represents _ _ (DomainResult.bind _ (Resolved.denote x.source η))
      rw [hd]
      exact hy
    | sequence n =>
      let items := args
      have ih := ih
      exact ⟨_, rfl, fun i => ih i ρ η h⟩
    | @snoc a n =>
      obtain ⟨ds, hd, hs⟩ := ih 0 ρ η h
      change Represents (.seq (n + 1) a) _
        (Semantics.append n (Length.finite 1) (Resolved.denote (Term.source (args 0)) η)
        (.value (fun _ => Resolved.denote (Term.source (args 1)) η)))
      rw [hd]
      erw [Semantics.append_value_snoc]
      exact Represents.snoc hs (ih 1 ρ η h)
    | index i =>
      let xs : Term _ _ := args 0
      have ih := ih 0
      obtain ⟨ds, hd, hs⟩ := ih ρ η h
      change Represents _ (Term.denote (args 0) ρ i)
        (Semantics.index (Resolved.denote xs.source η) (.value ⟨(i.val : Int)⟩))
      rw [hd, Semantics.index_values]
      simpa [Length.checkIndex, i.isLt] using hs i
    | lam =>
      let body : Term _ _ := args 0
      have ih := ih 0
      refine ⟨(ContinuousHom.curry
        ((Resolved.denote body.source).comp Environment.extendContinuous)) η, rfl, ?_⟩
      intro x dx hx
      exact ih (ρ.extend x) (η.extend dx) (h.extend hx)
    | app =>
      let f : Term _ _ := args 0
      let x : Term _ _ := args 1
      have ihf := ih 0
      have ihx := ih 1
      obtain ⟨g, hg, hfun⟩ := ihf ρ η h
      change Represents _ _ (DomainResult.applyContinuous (Resolved.denote f.source η) _)
      rw [hg]
      exact hfun _ _ (ihx ρ η h)
    | letE =>
      let x : Term _ _ := args 0
      let body : Term _ _ := args 1
      have ihx := ih 0
      have ihbody := ih 1
      exact ihbody _ _ (h.extend (ihx ρ η h))
    | bitNot =>
      let x : Term _ _ := args 0
      have ih := ih 0
      change DomainResult.bind _ (Resolved.denote x.source η) = _
      rw [ih ρ η h]
      rfl
    | bitOp op =>
      let x : Term _ _ := args 0
      let y : Term _ _ := args 1
      have ihx := ih 0
      have ihy := ih 1
      change Semantics.binary _ (Resolved.denote x.source η) (Resolved.denote y.source η) = _
      rw [ihx ρ η h, ihy ρ η h]
      rfl
    | wordNot =>
      let x : Term _ _ := args 0
      have ih := ih 0
      change Semantics.wordNot _ (Resolved.denote x.source η) = _
      rw [ih ρ η h]
      exact Semantics.wordNot_value _
    | wordOp op =>
      let x : Term _ _ := args 0
      let y : Term _ _ := args 1
      have ihx := ih 0
      have ihy := ih 1
      change Semantics.wordLogic _ op (Resolved.denote x.source η) (Resolved.denote y.source η) = _
      rw [ihx ρ η h, ihy ρ η h]
      cases op <;> exact Semantics.wordLogic_values _ _ _
    | wordEq n =>
      let x : Term _ _ := args 0
      let y : Term _ _ := args 1
      have ihx := ih 0
      have ihy := ih 1
      change Semantics.wordEq _ (Resolved.denote x.source η) (Resolved.denote y.source η) = _
      rw [ihx ρ η h, ihy ρ η h]
      exact Semantics.wordEq_values _ _
    | arithmetic op =>
      let x : Term _ _ := args 0
      let y : Term _ _ := args 1
      have ihx := ih 0
      have ihy := ih 1
      change Semantics.wordArithmetic _ op.core
        (Resolved.denote x.source η) (Resolved.denote y.source η) = _
      rw [ihx ρ η h, ihy ρ η h]
      cases op with
      | add => exact Semantics.wordAdd_values _ _
      | sub => exact Semantics.wordSub_values _ _
      | mul => exact Semantics.wordMul_values _ _
    | shiftLeft k =>
      let x : Term _ _ := args 0
      have ih := ih 0
      change Semantics.shiftFixed .left _ k (Resolved.denote x.source η) = _
      rw [ih ρ η h]
      exact Semantics.shiftFixed_value .left _ _
    | shiftRight k =>
      let x : Term _ _ := args 0
      have ih := ih 0
      change Semantics.shiftFixed .right _ k (Resolved.denote x.source η) = _
      rw [ih ρ η h]
      exact Semantics.shiftFixed_value .right _ _
    | rotateLeft k =>
      let x : Term _ _ := args 0
      have ih := ih 0
      change Semantics.shiftFixed .rotateLeft _ k (Resolved.denote x.source η) = _
      rw [ih ρ η h]
      exact Semantics.shiftFixed_value .rotateLeft _ _
    | rotateRight k =>
      let x : Term _ _ := args 0
      have ih := ih 0
      change Semantics.shiftFixed .rotateRight _ k (Resolved.denote x.source η) = _
      rw [ih ρ η h]
      exact Semantics.shiftFixed_value .rotateRight _ _

/-- Lower native descriptions through their retained resolved source. -/
@[expose] def Term.lower {Γ : List Ty} {a : Ty} (e : Term Γ a) :
    Expr (Γ.map Ty.core) a.core := Resolved.lower e.source

@[simp] theorem Term.lower_app {Γ : List Ty} {a b : Ty}
    (f : Term Γ (.arrow a b)) (x : Term Γ a) :
    (Term.app f x).lower = Expr.app f.lower x.lower := rfl

@[simp] theorem Term.lower_word {Γ : List Ty} {n : Nat} (x : BitVec n) :
    (Term.word (Γ := Γ) x).lower = Expr.word x := rfl

/-- Source preservation followed by resolved lowering preserves the native result. -/
theorem Term.lower_correct {Γ : List Ty} {a : Ty} (e : Term Γ a) (ρ : Env Γ)
    (η : Environment (Γ.map Ty.core)) (h : EnvRepresents ρ η) :
    Represents a (e.denote ρ) (e.lower.denote η) := by
  rw [Term.lower, Resolved.lower_correct]
  exact e.source_correct ρ η h

/-- Execute a closed native word function with an explicit bitvector result type. -/
@[expose] def Term.evalWord {n m : Nat} (f : Term [] (.arrow (.word n) (.word m)))
    (x : BitVec n) : BitVec m := f.denote Env.empty x

/-- Execute a closed native Boolean property with an explicit Boolean result type. -/
@[expose] def Term.evalProperty {n : Nat} (p : Term [] (.arrow (.word n) .bit))
    (x : BitVec n) : Bool := p.denote Env.empty x

/-- Closed word functions return every bit of their native result. -/
theorem Term.denote_apply_word {n m : Nat} (f : Term [] (.arrow (.word n) (.word m)))
    (x : BitVec n) :
    (Expr.app f.lower (.word x)).denote Environment.empty =
      .value (wordValue (f.denote Env.empty x)) :=
  (Term.app f (.word x)).lower_correct Env.empty Environment.empty envRepresents_empty

/-- Closed Boolean properties have the same meaning after lowering. -/
theorem Term.denote_apply_bit {n : Nat} (p : Term [] (.arrow (.word n) .bit))
    (x : BitVec n) :
    (Expr.app p.lower (.word x)).denote Environment.empty =
      .value ⟨p.denote Env.empty x⟩ :=
  (Term.app p (.word x)).lower_correct Env.empty Environment.empty envRepresents_empty
/-- The compact source route also preserves the native result after core lowering. -/
theorem Term.source_lower_correct {Γ : List Ty} {a : Ty} (e : Term Γ a) (ρ : Env Γ)
    (η : Environment (Γ.map Ty.core)) (h : EnvRepresents ρ η) :
    Represents a (e.denote ρ) ((Resolved.lower e.source).denote η) := by
  rw [Resolved.lower_correct]
  exact e.source_correct ρ η h

end Interop.Cryptol.Finite
