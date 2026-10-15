/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Model.SequenceLaws

/-!
# Lazy heterogeneous records and tuples

After label resolution, a record is a spine of typed fields. Updates construct
a new spine without demanding the original record; selecting the updated field
does not demand any original field. This is the demand behavior of `ESet` in
Cryptol's reference evaluator, including an erroneous original record.
-/

public section

namespace Interop.Cryptol.Record

/-- The core product spine associated with a checked field ordering. -/
@[expose] def type : List ClosedTy → ClosedTy
  | [] => .unit
  | a :: fields => .prod a (type fields)

/-- A suspended expression for every field in a heterogeneous record. -/
abbrev Fields (Γ fields : List ClosedTy) := (a : ClosedTy) → Var fields a → Expr Γ a

/-- Construct a record without forcing any field. -/
@[expose] def literal {Γ : List ClosedTy} : (fields : List ClosedTy) →
    Fields Γ fields → Expr Γ (type fields)
  | [], _ => .unit
  | a :: fields, values => .pair (values a .zero)
      (literal fields (fun b i => values b (.succ i)))

/-- Select a field using evidence of its type and position. -/
@[expose] def select {Γ : List ClosedTy} {a : ClosedTy} :
    {fields : List ClosedTy} → Var fields a → Expr Γ (type fields) → Expr Γ a
  | _ :: _, .zero, record => .fst record
  | _ :: _, .succ index, record => select index (.snd record)

/-- Rebuild the complete spine with suspended projections of the old record.
Synthetic tail constructors stay available even when the old record is erroneous. -/
@[expose] def update {Γ : List ClosedTy} {a : ClosedTy} :
    {fields : List ClosedTy} → Var fields a → Expr Γ (type fields) → Expr Γ a →
      Expr Γ (type fields)
  | _ :: fields, .zero, record, value => .pair value
      (literal fields (fun _ index => select index (.snd record)))
  | _ :: _, .succ index, record, value => .pair (.fst record)
      (update index (.snd record) value)

/-- Record selection respects semantic equality of suspended operands. -/
theorem denote_select_congr {Γ fields : List ClosedTy} {a : ClosedTy}
    (index : Var fields a) (left right : Expr Γ (type fields)) (ρ : Environment Γ)
    (h : left.denote ρ = right.denote ρ) :
    (select index left).denote ρ = (select index right).denote ρ := by
  induction index with
  | zero => change DomainResult.bind _ (left.denote ρ) = DomainResult.bind _ (right.denote ρ)
            rw [h]
  | succ index ih =>
      apply ih (.snd left) (.snd right)
      change DomainResult.bind _ (left.denote ρ) = DomainResult.bind _ (right.denote ρ)
      rw [h]

/-- Selection from a literal demands exactly the chosen field. -/
theorem denote_select_literal {Γ fields : List ClosedTy} {a : ClosedTy}
    (index : Var fields a) (values : Fields Γ fields) (ρ : Environment Γ) :
    (select index (literal fields values)).denote ρ = (values a index).denote ρ := by
  induction index with
  | zero => rfl
  | succ index ih =>
      exact (denote_select_congr index (.snd (literal _ values))
        (literal _ (fun b i => values b (.succ i))) ρ rfl).trans
        (ih (fun b i => values b (.succ i)))

/-- Rebuilding a record tail leaves every unmodified field's demand unchanged. -/
theorem denote_select_update_zero_succ {Γ fields : List ClosedTy} {a b : ClosedTy}
    (index : Var fields b) (record : Expr Γ (type (a :: fields))) (value : Expr Γ a)
    (ρ : Environment Γ) :
    (select (.succ index) (update .zero record value)).denote ρ =
      (select (.succ index) record).denote ρ := by
  exact (denote_select_congr index (.snd (update .zero record value))
    (literal fields (fun _ i => select i (.snd record))) ρ rfl).trans
      (denote_select_literal index (fun _ i => select i (.snd record)) ρ)

/-- The selected update bypasses errors or divergence in the original record. -/
theorem denote_select_update {Γ fields : List ClosedTy} {a : ClosedTy}
    (index : Var fields a) (record : Expr Γ (type fields)) (value : Expr Γ a)
    (ρ : Environment Γ) :
    (select index (update index record value)).denote ρ = value.denote ρ := by
  induction index with
  | zero => rfl
  | succ index ih =>
      exact (denote_select_congr index (.snd (update (.succ index) record value))
        (update index (.snd record) value) ρ rfl).trans
        (ih (.snd record) value)

end Interop.Cryptol.Record
